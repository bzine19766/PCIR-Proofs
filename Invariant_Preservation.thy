theory Invariant_Preservation
  imports Transition_Inversion
          Ranking_Function
begin

(* ========================================================================= *)
(* Section 1 : Add Transition preserves Well-Formedness                      *)
(* ========================================================================= *)

theorem add_transition_preserves_wf:
  assumes
    "transition G cfg (Add v) cfg'"
    "wf_config cfg"
  shows
    "wf_config cfg'"
proof -

  have
    "cfg' = add_update G cfg v"
    using add_transition_update[OF assms(1)] .

  moreover have
    "wf_config (add_update G cfg v)"
    using
      assms
      add_transition_vertex
      add_update_preserves_wf
    by blast

  ultimately
  show ?thesis
    by simp

qed


(* ========================================================================= *)
(* Section 2 : Commit Transition preserves Well-Formedness                   *)
(* ========================================================================= *)

theorem commit_transition_preserves_wf:
  assumes
    "transition G cfg Commit cfg'"
    "wf_config cfg"
  shows
    "wf_config cfg'"
proof -

  have
    "cfg' = commit_update cfg"
    using commit_transition_update[OF assms(1)] .

  moreover have
    "wf_config (commit_update cfg)"
    by (rule commit_update_preserves_wf)

  ultimately
  show ?thesis
    by simp

qed


(* ========================================================================= *)
(* Section 3 : Every Transition preserves Well-Formedness                    *)
(* ========================================================================= *)

theorem transition_preserves_wf:
  assumes
    "transition G cfg a cfg'"
    "wf_config cfg"
  shows
    "wf_config cfg'"
using assms
proof (induction rule: transition.induct)

  case (Add v cfg G)

  then show ?case
    using add_update_preserves_wf
    by auto

next

  case (Commit cfg G)

  then show ?case
    using commit_update_preserves_wf
    by auto

qed


(* ========================================================================= *)
(* Section 4 : Behaviour of \<rho> under Add                                      *)
(* ========================================================================= *)

theorem add_transition_rho:
  assumes
    "transition G cfg (Add v) cfg'"
    "finite (I cfg)"
    "v \<notin> I cfg"
  shows
    "fst (rho cfg') = fst (rho cfg)"
    "snd (rho cfg') < snd (rho cfg)"
proof -

  have H:
    "cfg' = add_update G cfg v"
    using add_transition_update[OF assms(1)] .

  show
    "fst (rho cfg') = fst (rho cfg)"
    using H
    by simp

  show
    "snd (rho cfg') < snd (rho cfg)"
    using
      H
      rho_add_notin[OF assms(2-3)]
    by simp

qed


(* ========================================================================= *)
(* Section 5 : Behaviour of \<rho> under Commit                                   *)
(* ========================================================================= *)

theorem commit_transition_rho:
  assumes
    "transition G cfg Commit cfg'"
    "finite (P cfg)"
    "I cfg \<subseteq> P cfg"
    "I cfg \<noteq> {}"
  shows
    "fst (rho cfg') < fst (rho cfg)"
proof -

  have H:
    "cfg' = commit_update cfg"
    using commit_transition_update[OF assms(1)] .

  show
    "fst (rho cfg') < fst (rho cfg)"
    using
      H
      rho_commit_first_less[OF assms(2-4)]
    by simp

qed


(* ========================================================================= *)
(* Section 6 : Summary                                                       *)
(* ========================================================================= *)

text \<open>

This theory establishes two preservation properties of the operational
semantics.

\<^item> Every transition preserves well-formed configurations.

\<^item> Every transition makes strict structural progress with respect to
the ranking function \<rho>.

For Add transitions, the first component of \<rho> is unchanged while the
second strictly decreases.

For Commit transitions, the first component strictly decreases.

These results are combined in the next theory to define the
lexicographic order on \<rho> and prove acyclicity, uniqueness of
predecessors, and that the transition graph forms a rooted tree.

\<close>
definition inv_C_characterization ::
  "graph \<Rightarrow> config \<Rightarrow> bool"
where
"inv_C_characterization G cfg \<longleftrightarrow>
   (if I cfg = {} then
        C cfg = P cfg
    else
        C cfg =
        {u \<in> P cfg - I cfg.
            u > Max (I cfg) \<and>
            (\<forall>w\<in>I cfg. \<not> adjacent G u w)})"

definition inv_R_independent ::
  "graph \<Rightarrow> config \<Rightarrow> bool"
where
  "inv_R_independent G cfg \<longleftrightarrow>
      (\<forall>M \<in> set (R cfg).
          independent G M)"

definition inv_R_cover ::
  "graph \<Rightarrow> config \<Rightarrow> bool"
where
  "inv_R_cover G cfg \<longleftrightarrow>
      \<Union> (set (R cfg))
        =
      V G - P cfg"

definition inv_R_disjoint ::
  "config \<Rightarrow> bool"
where
  "inv_R_disjoint cfg \<longleftrightarrow>
      pairwise_disjoint (R cfg)"

lemma Max_insert_new:
  assumes
    "finite S"
    "S \<noteq> {}"
    "\<forall>u\<in>S. u < v"
  shows
    "Max (insert v S) = v"
proof (rule Max_eqI)

  show "v \<in> insert v S"
    by simp

next

  fix x
  assume "x \<in> insert v S"

  then show "x \<le> v"
  proof
    assume "x = v"
    then show ?thesis
      by simp
  next
    assume "x \<in> S"
    with assms(3)
    show ?thesis
      by auto
  qed

qed (use assms in auto)

lemma add_candidate_characterization:
  assumes
      "inv_C_characterization G cfg"
      "finite (I cfg)"
      "I cfg \<noteq> {}"
      "v \<notin> I cfg"
      "\<forall>u\<in>I cfg. u < v"
  shows
      "{u \<in> C cfg.
          u > v \<and>
          \<not> adjacent G u v}
       =
       {u \<in> P cfg - (I cfg \<union> {v}).
          u > Max (I cfg \<union> {v}) \<and>
          (\<forall>w\<in>I cfg \<union> {v}. \<not> adjacent G u w)}"
proof -

  have Hmax:
      "Max (I cfg \<union> {v}) = v"
    using
      Max_insert_new
      assms(2-5)
    by blast

  from assms(1,3)
  have HC:
      "C cfg =
        {u \<in> P cfg - I cfg.
            u > Max (I cfg) \<and>
            (\<forall>w\<in>I cfg. \<not> adjacent G u w)}"
    unfolding inv_C_characterization_def
    by simp

  show ?thesis
    unfolding HC Hmax
    by auto

qed

theorem add_preserves_inv_C:
  assumes
      T:
      "transition G cfg (Add v) cfg'"
  and IC:
      "inv_C_characterization G cfg"
  and Fin:
      "finite (I cfg)"
  and Non:
      "I cfg \<noteq> {}"
  and NotIn:
      "v \<notin> I cfg"
  and Ord:
      "\<forall>u\<in>I cfg. u < v"
  shows
      "inv_C_characterization G cfg'"
proof -

  have U:
      "cfg' = add_update G cfg v"
    using add_transition_update[OF T] .

  have HC':
      "C cfg'
       =
       {u \<in> C cfg.
           u > v \<and>
           \<not> adjacent G u v}"
    using add_transition_candidates[OF T]
    by simp

  have Hchar:
      "{u \<in> C cfg.
           u > v \<and>
           \<not> adjacent G u v}
       =
       {u \<in> P cfg - (I cfg \<union> {v}).
           u > Max (I cfg \<union> {v}) \<and>
           (\<forall>w\<in>I cfg \<union> {v}. \<not> adjacent G u w)}"
    using
      add_candidate_characterization
      IC Fin Non NotIn Ord
    by blast

  show ?thesis
    unfolding U add_update_def inv_C_characterization_def
    using HC' Hchar
    by auto

qed

theorem commit_preserves_inv_C:
  assumes
      "transition G cfg Commit cfg'"
  shows
      "inv_C_characterization G cfg'"
proof -

  have
      "cfg' = commit_update cfg"
    using commit_transition_update[OF assms]
    by simp

  thus ?thesis
    unfolding
      commit_update_def
      inv_C_characterization_def
    by auto

qed

theorem add_preserves_inv_R_independent:
  assumes
      "transition G cfg (Add v) cfg'"
      "inv_R_independent G cfg"
  shows
      "inv_R_independent G cfg'"
proof -

  have
      "R cfg' = R cfg"
    using
      add_transition_result
      assms(1)
    by blast

  thus ?thesis
    using assms(2)
    unfolding inv_R_independent_def
    by simp

qed

theorem commit_preserves_inv_R_independent:
  assumes
      T:
      "transition G cfg Commit cfg'"
  and RI:
      "inv_R_independent G cfg"
  shows
      "inv_R_independent G cfg'"
proof -

  have HR:
      "R cfg' = R cfg @ [I cfg]"
    using
      commit_transition_result
      T
    by blast

  have HM:
      "maximal_independent G (P cfg) (I cfg)"
    using
      commit_transition_maximal
      T
    by blast

  have HI:
      "independent G (I cfg)"
    using
      maximal_independent_independent
      HM
    by blast

  show ?thesis
    unfolding
      inv_R_independent_def
      HR
    using
      RI
      HI
    by auto

qed

theorem add_preserves_inv_R_cover:
  assumes
      "transition G cfg (Add v) cfg'"
      "inv_R_cover G cfg"
  shows
      "inv_R_cover G cfg'"
proof -

  have
      "R cfg' = R cfg"
    using
      add_transition_result
      assms(1)
    by blast

  moreover

  have
      "P cfg' = P cfg"
    using
      add_transition_problem
      assms(1)
    by blast

  ultimately
  show ?thesis
    using assms(2)
    unfolding inv_R_cover_def
    by simp

qed

theorem commit_preserves_inv_R_cover:
  assumes
      T:
      "transition G cfg Commit cfg'"
  and RC:
      "inv_R_cover G cfg"
  shows
      "inv_R_cover G cfg'"
proof -

  have HR:
      "R cfg' = R cfg @ [I cfg]"
    using
      commit_transition_result
      T
    by blast

  have HP:
      "P cfg' = P cfg - I cfg"
    using
      commit_transition_problem
      T
    by blast

  show ?thesis
    unfolding
      inv_R_cover_def
      HR
      HP
    using RC
    by auto

qed

theorem add_preserves_inv_R_disjoint:
  assumes
      "transition G cfg (Add v) cfg'"
      "inv_R_disjoint cfg"
  shows
      "inv_R_disjoint cfg'"
proof -

  have
      "R cfg' = R cfg"
    using
      add_transition_result
      assms(1)
    by blast

  thus ?thesis
    using assms(2)
    unfolding inv_R_disjoint_def
    by simp

qed


end