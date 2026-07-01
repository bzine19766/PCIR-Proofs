theory Graph_Basics
  imports Main
begin

(* ========================================================================= *)
(* Section 1 : Basic Mathematical Objects                                    *)
(* ========================================================================= *)

type_synonym vertex = nat

type_synonym edge = "vertex \<times> vertex"

record graph =
  V :: "vertex set"
  E :: "edge set"

(* ========================================================================= *)
(* Section 2 : Adjacency                                                     *)
(* ========================================================================= *)

definition adjacent ::
  "graph \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> bool"
where
  "adjacent G u v \<longleftrightarrow>
      (u,v) \<in> E G \<or> (v,u) \<in> E G"

lemma adjacent_iff[simp]:
  "adjacent G u v \<longleftrightarrow> adjacent G v u"
  unfolding adjacent_def
  by auto

(* ========================================================================= *)
(* Section 3 : Induced Subgraphs                                             *)
(* ========================================================================= *)

definition induced_subgraph ::
  "graph \<Rightarrow> vertex set \<Rightarrow> graph"
where
  "induced_subgraph G U =
     \<lparr>
       V = U,
       E = {(u,v) \<in> E G. u \<in> U \<and> v \<in> U}
     \<rparr>"

text \<open>
The notation residual G P corresponds to the induced
subgraph G[P] used throughout the paper.
\<close>

abbreviation residual ::
  "graph \<Rightarrow> vertex set \<Rightarrow> graph"
where
  "residual G P \<equiv> induced_subgraph G P"

lemma induced_subgraph_vertices[simp]:
  "V (induced_subgraph G U) = U"
  unfolding induced_subgraph_def
  by simp

lemma induced_subgraph_edges[simp]:
  "E (induced_subgraph G U) =
      {(u,v) \<in> E G. u \<in> U \<and> v \<in> U}"
  unfolding induced_subgraph_def
  by simp

(* ========================================================================= *)
(* Section 4 : Independent Sets                                              *)
(* ========================================================================= *)

definition independent ::
  "graph \<Rightarrow> vertex set \<Rightarrow> bool"
where
  "independent G S \<longleftrightarrow>
      (\<forall>u\<in>S.
        \<forall>v\<in>S.
          u \<noteq> v \<longrightarrow> \<not> adjacent G u v)"

lemma independent_empty[simp]:
  "independent G {}"
  unfolding independent_def
  by auto

lemma independent_singleton[simp]:
  "independent G {v}"
  unfolding independent_def
  by auto

lemma independent_mono:
  assumes
    "independent G B"
    "A \<subseteq> B"
  shows
    "independent G A"
  using assms
  unfolding independent_def
  by blast

(* ========================================================================= *)
(* Section 5 : Maximal Independent Sets                                      *)
(* ========================================================================= *)

definition maximal_independent ::
  "graph \<Rightarrow> vertex set \<Rightarrow> vertex set \<Rightarrow> bool"
where
  "maximal_independent G U S \<longleftrightarrow>
      independent G S \<and>
      S \<subseteq> U \<and>
      (\<forall>v\<in>U - S.
          \<exists>u\<in>S. adjacent G u v)"

lemma maximal_independent_subset:
  assumes
    "maximal_independent G U S"
  shows
    "S \<subseteq> U"
  using assms
  unfolding maximal_independent_def
  by simp

lemma maximal_independent_independent:
  assumes
    "maximal_independent G U S"
  shows
    "independent G S"
  using assms
  unfolding maximal_independent_def
  by simp

lemma maximal_independent_domination:
  assumes
    "maximal_independent G U S"
    "v \<in> U - S"
  shows
    "\<exists>u\<in>S. adjacent G u v"
  using assms
  unfolding maximal_independent_def
  by blast

end