theory Transition_Inversion
  imports Configuration_Updates
          Operational_Semantics
begin

(* ========================================================================= *)
(* Section 1 : Add Transition                                                *)
(* ========================================================================= *)

lemma add_transition_update:
  assumes T:
    "transition G cfg (Add v) cfg'"
  shows
    "cfg' = add_update G cfg v"
proof -
  from T
  obtain H1 H2
    where
      "v \<in> C cfg"
      "cfg' =
         cfg\<lparr>
           I := I cfg \<union> {v},
           C := {u \<in> C cfg.
                   u > v \<and>
                   \<not> adjacent G u v}
         \<rparr>"
    unfolding add_update_def
    by (cases rule: transition.cases) auto
  thus ?thesis
    unfolding add_update_def
    by simp
qed

lemma add_transition_vertex:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "v \<in> C cfg"
  using assms
  by (cases rule: transition.cases) auto

lemma add_transition_prune:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "prune cfg'"
proof -
  from assms
  obtain H
    where
      "prune
         (cfg\<lparr>
            I := I cfg \<union> {v},
            C := {u \<in> C cfg.
                    u > v \<and>
                    \<not> adjacent G u v}
          \<rparr>)"
    by (cases rule: transition.cases) auto
  thus ?thesis
    using add_transition_update[OF assms]
    unfolding add_update_def
    by simp
qed

lemma add_transition_current:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "I cfg' = I cfg \<union> {v}"
  using assms
  unfolding add_update_def
  by (cases rule: transition.cases) auto

lemma add_transition_candidates:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "C cfg' =
      {u \<in> C cfg.
          u > v \<and>
          \<not> adjacent G u v}"
  using assms
  unfolding add_update_def
  by (cases rule: transition.cases) auto

lemma add_transition_problem:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "P cfg' = P cfg"
  using assms
  unfolding add_update_def
  by (cases rule: transition.cases) auto

lemma add_transition_result:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "R cfg' = R cfg"
  using assms
  unfolding add_update_def
  by (cases rule: transition.cases) auto


(* ========================================================================= *)
(* Section 2 : Commit Transition                                             *)
(* ========================================================================= *)

lemma commit_transition_update:
  assumes T:
    "transition G cfg Commit cfg'"
  shows
    "cfg' = commit_update cfg"
proof -
  from T
  obtain H1 H2 H3 H4
    where
      "C cfg = {}"
      "I cfg \<noteq> {}"
      "maximal_independent G (P cfg) (I cfg)"
      "cfg' =
         cfg\<lparr>
           P := P cfg - I cfg,
           R := R cfg @ [I cfg],
           I := {},
           C := P cfg - I cfg
         \<rparr>"
    unfolding commit_update_def
    by (cases rule: transition.cases) auto
  thus ?thesis
    unfolding commit_update_def
    by simp
qed

lemma commit_transition_empty_candidates:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "C cfg = {}"
  using assms
  by (cases rule: transition.cases) auto

lemma commit_transition_nonempty:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "I cfg \<noteq> {}"
  using assms
  by (cases rule: transition.cases) auto

lemma commit_transition_maximal:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "maximal_independent G (P cfg) (I cfg)"
  using assms
  by (cases rule: transition.cases) auto

lemma commit_transition_prune:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "prune cfg'"
proof -
  from assms
  obtain H
    where
      "prune
         (cfg\<lparr>
            P := P cfg - I cfg,
            R := R cfg @ [I cfg],
            I := {},
            C := P cfg - I cfg
          \<rparr>)"
    by (cases rule: transition.cases) auto
  thus ?thesis
    using commit_transition_update[OF assms]
    unfolding commit_update_def
    by simp
qed

lemma commit_transition_problem:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "P cfg' = P cfg - I cfg"
  using assms
  unfolding commit_update_def
  by (cases rule: transition.cases) auto

lemma commit_transition_result:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "R cfg' = R cfg @ [I cfg]"
  using assms
  unfolding commit_update_def
  by (cases rule: transition.cases) auto

lemma commit_transition_current:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "I cfg' = {}"
  using assms
  unfolding commit_update_def
  by (cases rule: transition.cases) auto

lemma commit_transition_candidates:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "C cfg' = P cfg - I cfg"
  using assms
  unfolding commit_update_def
  by (cases rule: transition.cases) auto

(* ========================================================================= *)
(* Section 3 : Transition Classification                                     *)
(* ========================================================================= *)

lemma transition_cases':
  assumes
    "transition G cfg a cfg'"
  shows
    "(\<exists>v. a = Add v \<and> cfg' = add_update G cfg v)
      \<or>
     (a = Commit \<and> cfg' = commit_update cfg)"
proof (cases rule: transition.cases[OF assms])
  case (Add v)
  then show ?thesis
    by (auto simp:add_update_def)
next
  case Commit
  then show ?thesis
    by (auto simp:commit_update_def)
qed

lemma transition_add_or_commit:
  assumes
    "transition G cfg a cfg'"
  shows
    "(\<exists>v. a = Add v) \<or> a = Commit"
using assms
by (cases rule: transition.cases) auto

(* ========================================================================= *)
(* Section 4 : Exclusiveness                                                 *)
(* ========================================================================= *)

lemma add_not_commit:
  "Add v \<noteq> Commit"
  by simp

lemma commit_not_add:
  "Commit \<noteq> Add v"
  by simp

lemma transition_add_not_commit:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "\<not> transition G cfg Commit cfg''"
proof
  assume
    "transition G cfg Commit cfg''"

  then have
    "C cfg = {}"
    using commit_transition_empty_candidates
    by blast

  moreover

  from assms
  have
    "v \<in> C cfg"
    using add_transition_vertex
    by blast

  ultimately
  show False
    by auto
qed

(* ========================================================================= *)
(* Section 5 : Determinism of Updates                                         *)
(* ========================================================================= *)


lemma add_transition_unique_target:
  assumes
    T1: "transition G cfg (Add v) c1"
    and T2: "transition G cfg (Add v) c2"
  shows
    "c1 = c2"
proof -

  have H1:
    "c1 = add_update G cfg v"
    using T1
    by (rule add_transition_update)

  have H2:
    "c2 = add_update G cfg v"
    using T2
    by (rule add_transition_update)

  from H1 H2
  show ?thesis
    by simp

qed


lemma commit_transition_unique_target:
  assumes
    T1: "transition G cfg Commit c1"
    and T2: "transition G cfg Commit c2"
  shows
    "c1 = c2"
proof -

  have H1:
    "c1 = commit_update cfg"
    using T1
    by (rule commit_transition_update)

  have H2:
    "c2 = commit_update cfg"
    using T2
    by (rule commit_transition_update)

  from H1 H2
  show ?thesis
    by simp

qed
(* ========================================================================= *)
(* Section 6 : Field Inversion                                               *)
(* ========================================================================= *)

lemma add_transition_fields:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "P cfg' = P cfg"
    "R cfg' = R cfg"
    "I cfg' = I cfg \<union> {v}"
    "C cfg'
      =
      {u\<in>C cfg.
          u > v \<and>
          \<not> adjacent G u v}"
using assms
by (auto
      simp:add_update_def
      dest:add_transition_problem
           add_transition_result
           add_transition_current
           add_transition_candidates)

lemma commit_transition_fields:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "P cfg' = P cfg - I cfg"
    "R cfg' = R cfg @ [I cfg]"
    "I cfg' = {}"
    "C cfg' = P cfg - I cfg"
using assms
by (auto
      simp:commit_update_def
      dest:commit_transition_problem
           commit_transition_result
           commit_transition_current
           commit_transition_candidates)


lemma transition_commit_not_add:
  assumes
    "transition G cfg Commit cfg'"
  shows
    "\<not> transition G cfg (Add v) cfg''"
proof
  assume
    "transition G cfg (Add v) cfg''"

  from assms
  have
    "C cfg = {}"
    by (rule commit_transition_empty_candidates)

  moreover

  from \<open>transition G cfg (Add v) cfg''\<close>
  have
    "v \<in> C cfg"
    by (rule add_transition_vertex)

  ultimately
  show False
    by auto
qed


(* ========================================================================= *)
(* Section 7 : Summary                                                       *)
(* ========================================================================= *)

text \<open>
This theory provides inversion principles for every transition.
Later theories use these lemmas to prove ranking decrease,
acyclicity, uniqueness of predecessors, and finally that the
transition graph forms a rooted tree.
\<close>

end