theory Cardinality_Lemmas
  imports Invariant_Lemmas
begin

(* ========================================================================= *)
(* Section 1 : Finiteness                                                    *)
(* ========================================================================= *)

lemma finite_subset':
  assumes
    "finite B"
    "A \<subseteq> B"
  shows
    "finite A"
  using assms
  by (meson finite_subset)

lemma finite_difference:
  assumes
    "finite A"
  shows
    "finite (A - B)"
  using assms
  by simp

lemma finite_insert':
  assumes
    "finite A"
  shows
    "finite (insert x A)"
  using assms
  by simp

(* ========================================================================= *)
(* Section 2 : Cardinality of Insert                                         *)
(* ========================================================================= *)

lemma card_insert_notin:
  assumes
    "finite A"
    "x \<notin> A"
  shows
    "card (insert x A) = card A + 1"
  using assms
  by simp

lemma card_insert_in:
  assumes
    "finite A"
    "x \<in> A"
  shows
    "card (insert x A) = card A"
  using assms
  by (simp add: insert_absorb)
(* ========================================================================= *)
(* Section 3 : Cardinality of Subsets                                        *)
(* ========================================================================= *)

lemma card_subset_le:
  assumes
    "finite B"
    "A \<subseteq> B"
  shows
    "card A \<le> card B"
  using assms
  by (simp add: card_mono)

lemma card_proper_subset:
  assumes
    "finite B"
    "A \<subset> B"
  shows
    "card A < card B"
  using assms
  by (simp add: psubset_card_mono)

(* ========================================================================= *)
(* Section 4 : Difference                                                    *)
(* ========================================================================= *)

lemma diff_subset:
  "A - B \<subseteq> A"
  by auto

lemma diff_proper_subset:
  assumes
    "B \<subseteq> A"
    "B \<noteq> {}"
  shows
    "A - B \<subset> A"
proof
  show
    "A - B \<subseteq> A"
    by auto

  obtain x
    where
      "x \<in> B"
    using assms(2)
    by auto

  hence
    "x \<in> A"
    using assms(1)
    by auto

  moreover

  have
    "x \<notin> A - B"
    using `x \<in> B`
    by auto

  ultimately
  show
    "A - B \<noteq> A"
    by auto
qed

lemma card_difference_less:
  assumes
    "finite A"
    "B \<subseteq> A"
    "B \<noteq> {}"
  shows
    "card (A - B) < card A"
proof -

  have
    "A - B \<subset> A"
    using diff_proper_subset assms(2-3)
    by blast

  thus ?thesis
    using assms(1)
    by (simp add: psubset_card_mono)

qed

(* ========================================================================= *)
(* Section 5 : Useful Arithmetic                                             *)
(* ========================================================================= *)

lemma card_subset_difference:
  assumes
    "finite B"
    "A \<subseteq> B"
  shows
    "card B - card A \<ge> 0"
  by simp

lemma card_insert_difference:
  assumes
    "finite A"
    "x \<notin> A"
  shows
    "card (insert x A) - card A = 1"
  using assms
  by simp

lemma card_difference_positive:
  assumes
    "finite A"
    "A \<noteq> {}"
  shows
    "0 < card A"
  using assms
  by (simp add: card_gt_0_iff)
(* ========================================================================= *)
(* Section 6 : Consequences of Well-formedness                               *)
(* ========================================================================= *)

lemma wf_card_I_le_P:
  assumes
    "finite (P cfg)"
    "wf_config cfg"
  shows
    "card (I cfg) \<le> card (P cfg)"
proof -

  have
    "I cfg \<subseteq> P cfg"
    using wf_has_I_subset[OF assms(2)] .

  thus ?thesis
    using assms(1)
    by (simp add: card_mono)

qed

lemma wf_card_C_le_P:
  assumes
    "finite (P cfg)"
    "wf_config cfg"
  shows
    "card (C cfg) \<le> card (P cfg)"
proof -

  have
    "C cfg \<subseteq> P cfg"
    using wf_has_C_subset[OF assms(2)] .

  thus ?thesis
    using assms(1)
    by (simp add: card_mono)

qed

end