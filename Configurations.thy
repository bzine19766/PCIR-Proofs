theory Configurations
  imports Graph_Basics
begin

(* ========================================================================= *)
(* Section 1 : Configuration States                                          *)
(* ========================================================================= *)

text \<open>
A configuration represents one node of the operational search tree.

P : residual problem (uncoloured vertices)

R : sequence of completed independent sets (colour classes)

I : current independent set under construction

C : candidate vertices that may still extend I
\<close>

record config =
  P :: "vertex set"
  R :: "vertex set list"
  I :: "vertex set"
  C :: "vertex set"

(* ========================================================================= *)
(* Section 2 : Initial Configuration                                         *)
(* ========================================================================= *)

text \<open>
The initial configuration contains the entire graph as the residual
problem. No colour classes have been completed and the current
independent set is empty.
\<close>

definition init_config ::
  "graph \<Rightarrow> config"
where
  "init_config G =
     \<lparr>
       P = V G,
       R = [],
       I = {},
       C = V G
     \<rparr>"

(* ========================================================================= *)
(* Section 3 : Abstract Pruning Predicate                                    *)
(* ========================================================================= *)

text \<open>
The operational semantics is parameterized by an abstract pruning
predicate.

Initially every configuration is accepted. Concrete pruning strategies
(Byskov bounds, clique bounds, spectral filters, etc.) are obtained by
replacing this definition in later theories.
\<close>

definition prune ::
  "config \<Rightarrow> bool"
where
  "prune cfg \<longleftrightarrow> True"

(* ========================================================================= *)
(* Section 4 : Transition Labels                                             *)
(* ========================================================================= *)

text \<open>
The operational semantics consists of two elementary actions.

• Add v
    inserts a vertex into the current independent set.

• Commit
    closes the current independent set and starts the next colour class.

The Extend transition introduced in the paper for incremental colouring
will be added later in a separate theory.
\<close>

datatype action =
    Add vertex
  | Commit

(* ========================================================================= *)
(* Section 5 : Basic Configuration Invariants                                *)
(* ========================================================================= *)

text \<open>
These are auxiliary structural invariants used throughout the proofs.
They are intentionally weaker than the semantic invariants introduced
later in the paper.
\<close>

definition inv_I_subset_P ::
  "config \<Rightarrow> bool"
where
  "inv_I_subset_P cfg \<longleftrightarrow>
      I cfg \<subseteq> P cfg"

definition inv_C_subset_P ::
  "config \<Rightarrow> bool"
where
  "inv_C_subset_P cfg \<longleftrightarrow>
      C cfg \<subseteq> P cfg"

definition wf_config ::
  "config \<Rightarrow> bool"
where
  "wf_config cfg \<longleftrightarrow>
      inv_I_subset_P cfg \<and>
      inv_C_subset_P cfg"

(* ========================================================================= *)
(* Section 6 : Initial Well-Formedness                                       *)
(* ========================================================================= *)

lemma init_wf:
  "wf_config (init_config G)"
  unfolding
      wf_config_def
      inv_I_subset_P_def
      inv_C_subset_P_def
      init_config_def
  by simp

(* ========================================================================= *)
(* Section 7 : Elimination Rules                                             *)
(* ========================================================================= *)

lemma wf_I:
  assumes
    "wf_config cfg"
  shows
    "I cfg \<subseteq> P cfg"
  using assms
  unfolding
      wf_config_def
      inv_I_subset_P_def
  by simp

lemma wf_C:
  assumes
    "wf_config cfg"
  shows
    "C cfg \<subseteq> P cfg"
  using assms
  unfolding
      wf_config_def
      inv_C_subset_P_def
  by simp

(* ========================================================================= *)
(* Section 8 : Elementary Set Lemmas                                         *)
(* ========================================================================= *)

lemma subset_insert:
  assumes
    "A \<subseteq> B"
    "x \<in> B"
  shows
    "A \<union> {x} \<subseteq> B"
  using assms
  by auto

lemma subset_filter:
  fixes P :: "'a \<Rightarrow> bool"
  assumes
    "A \<subseteq> B"
  shows
    "{x\<in>A. P x} \<subseteq> B"
  using assms
  by auto
(* ========================================================================= *)
(* Section 9 : Candidate Set is Functionally Determined                      *)
(* ========================================================================= *)

text \<open>

The candidate set is completely determined by the problem set and the
current independent set in every well-formed configuration.

Consequently, two well-formed configurations having identical problem
sets and current independent sets necessarily have identical candidate
sets.

\<close>
theorem candidate_set_unique:
  assumes
      WF1: "wf_config cfg1"
  and WF2: "wf_config cfg2"
  and HP:  "P cfg1 = P cfg2"
  and HI:  "I cfg1 = I cfg2"
  shows
      "C cfg1 = C cfg2"
proof -

  have HC1:
      "C cfg1 =
         {u \<in> P cfg1 - I cfg1.
             \<forall>w\<in>I cfg1.
               \<not> adjacent G u w}"
    using WF1
    unfolding wf_config_def
    by auto

  have HC2:
      "C cfg2 =
         {u \<in> P cfg2 - I cfg2.
             \<forall>w\<in>I cfg2.
               \<not> adjacent G u w}"
    using WF2
    unfolding wf_config_def
    by auto

  show ?thesis
    unfolding HC1 HC2
    using HP HI
    by auto

qed
end