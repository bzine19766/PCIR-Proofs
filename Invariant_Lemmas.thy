theory Invariant_Lemmas
  imports Configurations
begin

(* ========================================================================= *)
(* Section 1 : Well-formed configurations                                    *)
(* ========================================================================= *)

lemma init_configuration_wf:
  "wf_config (init_config G)"
  using init_wf .

lemma wf_has_I_subset:
  assumes "wf_config cfg"
  shows "I cfg \<subseteq> P cfg"
  using assms
  by (rule wf_I)

lemma wf_has_C_subset:
  assumes "wf_config cfg"
  shows "C cfg \<subseteq> P cfg"
  using assms
  by (rule wf_C)

(* ========================================================================= *)
(* Section 2 : Elementary Set Lemmas                                         *)
(* ========================================================================= *)

lemma subset_insert':
  assumes
    "A \<subseteq> B"
    "x \<in> B"
  shows
    "insert x A \<subseteq> B"
  using assms
  by auto

lemma subset_filter':
  fixes Q :: "'a \<Rightarrow> bool"
  assumes
    "A \<subseteq> B"
  shows
    "{x \<in> A. Q x} \<subseteq> B"
  using assms
  by auto

lemma subset_difference:
  "A - B \<subseteq> A"
  by auto

lemma empty_subset':
  "{} \<subseteq> A"
  by auto

(* ========================================================================= *)
(* Section 3 : Useful Set Facts                                              *)
(* ========================================================================= *)

lemma union_singleton_subset:
  assumes
    "A \<subseteq> B"
    "x \<in> B"
  shows
    "A \<union> {x} \<subseteq> B"
  using assms
  by auto

lemma filter_subset:
  fixes Q :: "'a \<Rightarrow> bool"
  shows
    "{x \<in> A. Q x} \<subseteq> A"
  by auto

lemma difference_subset':
  "A - B \<subseteq> A"
  by auto

lemma insert_subset:
  assumes
    "insert x A \<subseteq> B"
  shows
    "A \<subseteq> B"
  using assms
  by auto

(* ========================================================================= *)
(* Section 4 : Candidate and Current Sets                                    *)
(* ========================================================================= *)

lemma candidate_subset_problem:
  assumes
    "wf_config cfg"
  shows
    "C cfg \<subseteq> P cfg"
  using assms
  unfolding
    wf_config_def
    inv_C_subset_P_def
  by auto

lemma current_subset_problem:
  assumes
    "wf_config cfg"
  shows
    "I cfg \<subseteq> P cfg"
  using assms
  unfolding
    wf_config_def
    inv_I_subset_P_def
  by auto

end