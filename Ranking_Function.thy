theory Ranking_Function
  imports Cardinality_Lemmas
          Configuration_Updates
begin

(* ========================================================================= *)
(* Section 1 : Structural Ranking Function                                   *)
(* ========================================================================= *)

definition rho ::
  "config \<Rightarrow> nat \<times> nat"
where
  "rho cfg =
     (card (P cfg),
      card (P cfg) - card (I cfg))"

(* ========================================================================= *)
(* Section 2 : Basic Simplification Rules                                    *)
(* ========================================================================= *)

lemma rho_first[simp]:
  "fst (rho cfg) = card (P cfg)"
  by (simp add: rho_def)

lemma rho_second[simp]:
  "snd (rho cfg) =
     card (P cfg) - card (I cfg)"
  by (simp add: rho_def)

lemma rho_expand:
  "rho cfg =
     (card (P cfg),
      card (P cfg) - card (I cfg))"
  by (simp add: rho_def)

lemma rho_commit_expand:
  "rho (commit_update cfg) =
     (card (P cfg - I cfg),
      card (P cfg - I cfg))"
  by (simp add: rho_def)

lemma rho_add_expand:
  "rho (add_update G cfg v) =
     (card (P cfg),
      card (P cfg) - card (I cfg \<union> {v}))"
  by (simp add: rho_def)

(* ========================================================================= *)
(* Section 3 : Behaviour under Add Update                                    *)
(* ========================================================================= *)

lemma rho_add_first:
  "fst (rho (add_update G cfg v))
      =
   fst (rho cfg)"
  by (simp add: rho_def)

lemma rho_add_second:
  "snd (rho (add_update G cfg v))
      =
   card (P cfg) -
   card (I cfg \<union> {v})"
  by (simp add: rho_def)

lemma rho_add_notin:
  assumes
    "finite (I cfg)"
    "v \<notin> I cfg"
  shows
    "snd (rho (add_update G cfg v))
      =
     snd (rho cfg) - 1"
proof -

  have
    "card (I cfg \<union> {v})
      =
     card (I cfg) + 1"
    using assms
    by simp

  thus ?thesis
    by (simp add: rho_def)

qed

lemma rho_add_second_le:
  assumes
    "finite (I cfg)"
  shows
    "snd (rho (add_update G cfg v))
      \<le>
     snd (rho cfg)"
proof (cases "v \<in> I cfg")

  case True
  then show ?thesis
    by (simp add: rho_def)

next

  case False
  then show ?thesis
    using rho_add_notin[OF assms False]
    by simp

qed

(* ========================================================================= *)
(* Section 4 : Behaviour under Commit Update                                 *)
(* ========================================================================= *)

lemma rho_commit_first:
  "fst (rho (commit_update cfg))
      =
   card (P cfg - I cfg)"
  by (simp add: rho_def)

lemma rho_commit_second:
  "snd (rho (commit_update cfg))
      =
   card (P cfg - I cfg)"
  by (simp add: rho_def)

lemma rho_commit_components_equal:
  "fst (rho (commit_update cfg))
      =
   snd (rho (commit_update cfg))"
  by (simp add: rho_def)

lemma rho_commit_problem_smaller:
  assumes
    "finite (P cfg)"
    "I cfg \<subseteq> P cfg"
    "I cfg \<noteq> {}"
  shows
    "card (P (commit_update cfg))
      <
     card (P cfg)"
proof -

  have
    "card (P cfg - I cfg)
      <
     card (P cfg)"
    using
      card_difference_less
      assms
    by blast

  thus ?thesis
    by simp

qed

lemma rho_commit_first_less:
  assumes
    "finite (P cfg)"
    "I cfg \<subseteq> P cfg"
    "I cfg \<noteq> {}"
  shows
    "fst (rho (commit_update cfg))
      <
     fst (rho cfg)"
  using
    rho_commit_problem_smaller
    assms
  by (simp add: rho_def)

(* ========================================================================= *)
(* Section 5 : General Properties                                            *)
(* ========================================================================= *)

lemma rho_second_le_first:
  "snd (rho cfg)
      \<le>
   fst (rho cfg)"
  by (simp add: rho_def)

lemma rho_nonnegative:
  "0 \<le> snd (rho cfg)"
  by (simp add: rho_def)

lemma rho_finite_components:
  assumes
    "finite (P cfg)"
  shows
    "fst (rho cfg) < Suc (card (P cfg))
     \<and>
     snd (rho cfg) < Suc (card (P cfg))"
proof

  show
    "fst (rho cfg)
      <
     Suc (card (P cfg))"
    by simp

  have
    "snd (rho cfg)
      \<le>
     card (P cfg)"
    by (simp add: rho_def)

  thus
    "snd (rho cfg)
      <
     Suc (card (P cfg))"
    by simp

qed

(* ========================================================================= *)
(* Section 6 : Interpretation                                                *)
(* ========================================================================= *)

text \<open>

The structural ranking function

      \<rho>(\<Gamma>) = (|P|, |P| - |I|)

is compared lexicographically.

The second component decreases during Add transitions,
provided the inserted vertex is new.

The first component decreases during Commit transitions,
because the current independent set is removed from the
remaining problem set.

The transition-based decrease theorem is proved later,
after the operational semantics has been introduced.

\<close>

end