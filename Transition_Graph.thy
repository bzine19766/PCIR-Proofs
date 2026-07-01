theory Transition_Graph
  imports Invariant_Preservation
begin

(* ========================================================================= *)
(* Section 1 : Vertices                                                      *)
(* ========================================================================= *)

definition TG_vertices ::
  "graph \<Rightarrow> config set"
where
  "TG_vertices G =
     {cfg. wf_config cfg}"

(* ========================================================================= *)
(* Section 2 : Edges                                                         *)
(* ========================================================================= *)

definition TG_edge ::
  "graph \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
where
  "TG_edge G c1 c2 \<longleftrightarrow>
      (\<exists>a. transition G c1 a c2)"

definition TG_edges ::
  "graph \<Rightarrow> (config \<times> config) set"
where
  "TG_edges G =
     {(c1,c2). TG_edge G c1 c2}"

(* ========================================================================= *)
(* Section 3 : Root Configuration                                            *)
(* ========================================================================= *)

definition TG_root ::
  "graph \<Rightarrow> config"
where
  "TG_root G = init_config G"

(* ========================================================================= *)
(* Section 4 : Successors and Predecessors                                   *)
(* ========================================================================= *)

definition successors ::
  "graph \<Rightarrow> config \<Rightarrow> config set"
where
  "successors G cfg =
     {cfg'. TG_edge G cfg cfg'}"

definition predecessors ::
  "graph \<Rightarrow> config \<Rightarrow> config set"
where
  "predecessors G cfg =
     {cfg'. TG_edge G cfg' cfg}"

(* ========================================================================= *)
(* Section 5 : Parent Relation                                               *)
(* ========================================================================= *)

definition parent ::
  "graph \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
where
  "parent G p c \<longleftrightarrow> TG_edge G p c"

(* ========================================================================= *)
(* Section 6 : Leaves                                                        *)
(* ========================================================================= *)

definition leaf ::
  "graph \<Rightarrow> config \<Rightarrow> bool"
where
  "leaf G cfg \<longleftrightarrow> successors G cfg = {}"

definition internal ::
  "graph \<Rightarrow> config \<Rightarrow> bool"
where
  "internal G cfg \<longleftrightarrow> successors G cfg \<noteq> {}"

(* ========================================================================= *)
(* Section 7 : Reachability                                                  *)
(* ========================================================================= *)

inductive reachable ::
  "graph \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
where
  refl:
    "reachable G cfg cfg"
|
  step:
    "\<lbrakk> TG_edge G c1 c2;
       reachable G c2 c3 \<rbrakk>
     \<Longrightarrow> reachable G c1 c3"

(* ========================================================================= *)
(* Section 8 : Basic Characterisations                                       *)
(* ========================================================================= *)

lemma TG_edgeI:
  assumes
    "transition G c1 a c2"
  shows
    "TG_edge G c1 c2"
  using assms
  unfolding TG_edge_def
  by auto

lemma TG_edgeE:
  assumes
    "TG_edge G c1 c2"
  obtains a
  where
    "transition G c1 a c2"
  using assms
  unfolding TG_edge_def
  by auto

lemma TG_edgesI:
  assumes
    "transition G c1 a c2"
  shows
    "(c1,c2) \<in> TG_edges G"
  using assms
  unfolding TG_edges_def TG_edge_def
  by auto

lemma TG_edgesE:
  assumes
    "(c1,c2) \<in> TG_edges G"
  obtains a
  where
    "transition G c1 a c2"
  using assms
  unfolding TG_edges_def TG_edge_def
  by auto

(* ========================================================================= *)
(* Section 9 : Successors                                                    *)
(* ========================================================================= *)

lemma successorI:
  assumes
    "transition G cfg a cfg'"
  shows
    "cfg' \<in> successors G cfg"
  using assms
  unfolding successors_def TG_edge_def
  by auto

lemma successorE:
  assumes
    "cfg' \<in> successors G cfg"
  obtains a
  where
    "transition G cfg a cfg'"
  using assms
  unfolding successors_def TG_edge_def
  by auto

lemma successor_characterization:
  "cfg' \<in> successors G cfg
      \<longleftrightarrow>
   TG_edge G cfg cfg'"
  unfolding successors_def
  by auto

(* ========================================================================= *)
(* Section 10 : Predecessors                                                 *)
(* ========================================================================= *)

lemma predecessorI:
  assumes
    "transition G cfg a cfg'"
  shows
    "cfg \<in> predecessors G cfg'"
  using assms
  unfolding predecessors_def TG_edge_def
  by auto

lemma predecessorE:
  assumes
    "cfg \<in> predecessors G cfg'"
  obtains a
  where
    "transition G cfg a cfg'"
  using assms
  unfolding predecessors_def TG_edge_def
  by auto

lemma predecessor_characterization:
  "cfg' \<in> predecessors G cfg
      \<longleftrightarrow>
   TG_edge G cfg' cfg"
  unfolding predecessors_def
  by auto

lemma parent_predecessor:
  "parent G p c
      \<longleftrightarrow>
   p \<in> predecessors G c"
  unfolding
      parent_def
      predecessors_def
      TG_edge_def
  by auto

(* ========================================================================= *)
(* Section 11 : Root                                                         *)
(* ========================================================================= *)

lemma TG_vertices_root:
  "TG_root G \<in> TG_vertices G"
  unfolding
      TG_root_def
      TG_vertices_def
  using init_configuration_wf
  by simp

lemma root_is_vertex:
  "TG_root G \<in> TG_vertices G"
  using TG_vertices_root .

(* ========================================================================= *)
(* Section 12 : Well-formedness of Vertices                                  *)
(* ========================================================================= *)

lemma transition_source_vertex:
  assumes
    "transition G cfg a cfg'"
    "wf_config cfg"
  shows
    "cfg \<in> TG_vertices G"
  using assms
  unfolding TG_vertices_def
  by auto

lemma transition_target_vertex:
  assumes
    "transition G cfg a cfg'"
    "wf_config cfg"
  shows
    "cfg' \<in> TG_vertices G"
  using
      transition_preserves_wf
      assms
  unfolding TG_vertices_def
  by auto

(* ========================================================================= *)
(* Section 13 : Reachability Facts                                           *)
(* ========================================================================= *)

lemma reachable_refl:
  "reachable G cfg cfg"
  by (rule reachable.refl)

lemma reachable_step:
  assumes
    "TG_edge G c1 c2"
    "reachable G c2 c3"
  shows
    "reachable G c1 c3"
  using assms
  by (rule reachable.step)

(* ========================================================================= *)
(* Section 14 : Leaves                                                       *)
(* ========================================================================= *)

lemma leaf_not_internal:
  "leaf G cfg \<longleftrightarrow> \<not> internal G cfg"
  unfolding
      leaf_def
      internal_def
  by auto

text \<open>

This theory introduces the transition graph induced by the
operational semantics.

The following theory proves its structural properties:

  • every transition strictly decreases the ranking function,

  • the transition graph is acyclic,

  • every non-root configuration has a unique predecessor,

  • therefore the transition graph is a rooted tree.

\<close>

end