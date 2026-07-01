theory Configuration_Updates
  imports Configurations
begin

(* ========================================================================= *)
(* Section 1 : Add Update                                                    *)
(* ========================================================================= *)

definition add_update ::
  "graph \<Rightarrow> config \<Rightarrow> vertex \<Rightarrow> config"
where
  "add_update G cfg v =
     cfg\<lparr>
       I := I cfg \<union> {v},
       C := {u \<in> C cfg.
               u > v \<and>
               \<not> adjacent G u v}
     \<rparr>"

(* ========================================================================= *)
(* Section 2 : Commit Update                                                 *)
(* ========================================================================= *)

definition commit_update ::
  "config \<Rightarrow> config"
where
  "commit_update cfg =
     cfg\<lparr>
       P := P cfg - I cfg,
       R := R cfg @ [I cfg],
       I := {},
       C := P cfg - I cfg
     \<rparr>"

(* ========================================================================= *)
(* Section 3 : Basic Equations                                               *)
(* ========================================================================= *)

lemma add_update_P[simp]:
  "P (add_update G cfg v) = P cfg"
  unfolding add_update_def
  by simp

lemma add_update_R[simp]:
  "R (add_update G cfg v) = R cfg"
  unfolding add_update_def
  by simp

lemma add_update_I[simp]:
  "I (add_update G cfg v) =
      I cfg \<union> {v}"
  unfolding add_update_def
  by simp

lemma add_update_C[simp]:
  "C (add_update G cfg v) =
      {u\<in>C cfg.
          u > v \<and>
          \<not> adjacent G u v}"
  unfolding add_update_def
  by simp

lemma commit_update_P[simp]:
  "P (commit_update cfg) =
      P cfg - I cfg"
  unfolding commit_update_def
  by simp

lemma commit_update_R[simp]:
  "R (commit_update cfg) =
      R cfg @ [I cfg]"
  unfolding commit_update_def
  by simp

lemma commit_update_I[simp]:
  "I (commit_update cfg) = {}"
  unfolding commit_update_def
  by simp

lemma commit_update_C[simp]:
  "C (commit_update cfg) =
      P cfg - I cfg"
  unfolding commit_update_def
  by simp

(* ========================================================================= *)
(* Section 4 : Add Update preserves invariants                               *)
(* ========================================================================= *)

lemma add_update_preserves_I_subset:
  assumes
    "wf_config cfg"
    "v \<in> C cfg"
  shows
    "inv_I_subset_P (add_update G cfg v)"
proof -

  have HI:
    "I cfg \<subseteq> P cfg"
    using wf_I[OF assms(1)] .

  have HC:
    "C cfg \<subseteq> P cfg"
    using wf_C[OF assms(1)] .

  have Hv:
    "v \<in> P cfg"
    using HC assms(2)
    by auto

  have
    "I cfg \<union> {v} \<subseteq> P cfg"
    using subset_insert[OF HI Hv]
    .

  thus ?thesis
    unfolding
      inv_I_subset_P_def
      add_update_def
    by simp

qed

lemma add_update_preserves_C_subset:
  assumes
    "wf_config cfg"
  shows
    "inv_C_subset_P (add_update G cfg v)"
proof -

  have
    "C cfg \<subseteq> P cfg"
    using wf_C[OF assms]
    .

  hence
    "{u\<in>C cfg.
        u > v \<and>
        \<not> adjacent G u v}
      \<subseteq>
     P cfg"
    using subset_filter
    by blast

  thus ?thesis
    unfolding
      inv_C_subset_P_def
      add_update_def
    by simp

qed

lemma add_update_preserves_wf:
  assumes
    "wf_config cfg"
    "v \<in> C cfg"
  shows
    "wf_config (add_update G cfg v)"
proof -

  have
    "inv_I_subset_P (add_update G cfg v)"
    using
      add_update_preserves_I_subset
      assms
    .

  moreover

  have
    "inv_C_subset_P (add_update G cfg v)"
    using
      add_update_preserves_C_subset
      assms(1)
    .

  ultimately
  show ?thesis
    unfolding wf_config_def
    by blast

qed

(* ========================================================================= *)
(* Section 5 : Commit Update preserves invariants                            *)
(* ========================================================================= *)

lemma commit_update_preserves_I_subset:
  "inv_I_subset_P (commit_update cfg)"
  unfolding
    inv_I_subset_P_def
    commit_update_def
  by simp

lemma commit_update_preserves_C_subset:
  "inv_C_subset_P (commit_update cfg)"
  unfolding
    inv_C_subset_P_def
    commit_update_def
  by simp

lemma commit_update_preserves_wf:
  "wf_config (commit_update cfg)"
proof -

  have
    "inv_I_subset_P (commit_update cfg)"
    by (rule commit_update_preserves_I_subset)

  moreover

  have
    "inv_C_subset_P (commit_update cfg)"
    by (rule commit_update_preserves_C_subset)

  ultimately
  show ?thesis
    unfolding wf_config_def
    by blast

qed

end