theory Unique_Predecessor
  imports Transition_Graph
          Transition_Inversion
         
begin

(* ========================================================================= *)
(* Section 1 : Lexicographic Order induced by the Ranking Function           *)
(* ========================================================================= *)

definition rho_less ::
  "config \<Rightarrow> config \<Rightarrow> bool"
where
  "rho_less c1 c2 \<longleftrightarrow>
      fst (rho c1) < fst (rho c2)
   \<or> (fst (rho c1) = fst (rho c2)
      \<and> snd (rho c1) < snd (rho c2))"

lemma rho_less_first:
  assumes
    "fst (rho c1) < fst (rho c2)"
  shows
    "rho_less c1 c2"
  using assms
  unfolding rho_less_def
  by auto

lemma rho_less_second:
  assumes
    "fst (rho c1) = fst (rho c2)"
    "snd (rho c1) < snd (rho c2)"
  shows
    "rho_less c1 c2"
  using assms
  unfolding rho_less_def
  by auto

lemma rho_less_irrefl:
  "\<not> rho_less c c"
  unfolding rho_less_def
  by auto

(* ========================================================================= *)
(* Section 2 : Add transitions decrease \<rho>                                   *)
(* ========================================================================= *)

theorem add_transition_decreases_rho:
  assumes
      "transition G cfg (Add v) cfg'"
      "finite (I cfg)"
      "v \<notin> I cfg"
  shows
      "rho_less cfg' cfg"
proof -

  have Hupd:
      "cfg' = add_update G cfg v"
    using
      add_transition_update[OF assms(1)]
    .

  have H1:
      "fst (rho (add_update G cfg v))
       =
       fst (rho cfg)"
    by (rule rho_add_first)

  have H2:
      "snd (rho (add_update G cfg v))
       <
       snd (rho cfg)"
    using
      rho_add_notin[OF assms(2-3)]
    by simp

  show ?thesis
    unfolding Hupd
    using
      rho_less_second[OF H1 H2]
    .

qed

(* ========================================================================= *)
(* Section 3 : Commit transitions decrease \<rho>                                *)
(* ========================================================================= *)

theorem commit_transition_decreases_rho:
  assumes
      "transition G cfg Commit cfg'"
      "finite (P cfg)"
      "I cfg \<subseteq> P cfg"
      "I cfg \<noteq> {}"
  shows
      "rho_less cfg' cfg"
proof -

  have Hupd:
      "cfg' = commit_update cfg"
    using
      commit_transition_update[OF assms(1)]
    .

  have Hfirst:
      "fst (rho (commit_update cfg))
       <
       fst (rho cfg)"
    using
      rho_commit_first_less
      assms(2-4)
    by blast

  show ?thesis
    unfolding Hupd
    using
      rho_less_first[OF Hfirst]
    .

qed

(* ========================================================================= *)
(* Section 4 : Every transition decreases the ranking                       *)
(* ========================================================================= *)

theorem transition_decreases_rho:
  assumes
      "transition G cfg a cfg'"
      "finite (P cfg)"
      "finite (I cfg)"
      "I cfg \<subseteq> P cfg"
      "wf_config cfg"
  shows
      "rho_less cfg' cfg"
proof (cases rule: transition.cases[OF assms(1)])

  case (Add v)

  moreover

  have
    "v \<in> C cfg"
    using Add
    by auto

  hence
    "v \<notin> I cfg"
    using
      wf_I[OF assms(5)]
      wf_C[OF assms(5)]
    unfolding
      inv_I_subset_P_def
      inv_C_subset_P_def
    by auto

  ultimately
  show ?thesis
    using
      add_transition_decreases_rho
      assms
    by blast

next

  case Commit

  moreover

  have
    "I cfg \<noteq> {}"
    using Commit
    by auto

  ultimately
  show ?thesis
    using
      commit_transition_decreases_rho
      assms
    by blast

qed

(* ========================================================================= *)
(* Section 5 : Strict Progress and Acyclicity                                *)
(* ========================================================================= *)

lemma transition_strict_progress:
  assumes
      "transition G c1 a c2"
      "finite (P c1)"
      "finite (I c1)"
      "I c1 \<subseteq> P c1"
      "wf_config c1"
  shows
      "rho_less c2 c1"
using transition_decreases_rho assms
by blast


lemma transition_not_reflexive:
  assumes
      "transition G c a c"
      "finite (P c)"
      "finite (I c)"
      "I c \<subseteq> P c"
      "wf_config c"
  shows False
proof -

  have
      "rho_less c c"
    using
      transition_strict_progress
      assms
    by blast

  thus False
    using rho_less_irrefl
    by blast

qed

text \<open>

This theory establishes the fundamental well-foundedness property of
the operational semantics.

Every transition strictly decreases the ranking function \<rho>.
Consequently,

  • no transition is reflexive;

  • every finite transition path is strictly descending;

  • cycles cannot exist.

The remaining structural properties of the transition graph
(existence and uniqueness of predecessors, and the rooted-tree theorem)
require reasoning about inverse transitions and are proved in the
following theory.

\<close>
(* ========================================================================= *)
(* Section 6 : Predecessor Reconstruction                                    *)
(* ========================================================================= *)

text \<open>
This section studies the inverse direction of the operational
semantics.

While the previous theory showed how a configuration is transformed,
the present section characterizes the predecessor of a transition.
These characterizations are the key ingredients for proving uniqueness
of predecessors and, ultimately, the rooted-tree property.
\<close>

lemma add_predecessor_characterization:
  assumes
      "transition G cfg (Add v) cfg'"
  shows
      "cfg' = add_update G cfg v"
      "v \<in> C cfg"
      "I cfg' = I cfg \<union> {v}"
      "P cfg' = P cfg"
      "R cfg' = R cfg"
      "C cfg'
        =
        {u\<in>C cfg.
            u > v \<and>
            \<not> adjacent G u v}"
using assms
by (auto
      dest:
        add_transition_update
        add_transition_vertex
        add_transition_problem
        add_transition_result
        add_transition_current
        add_transition_candidates)

lemma commit_predecessor_characterization:
  assumes
      "transition G cfg Commit cfg'"
  shows
      "cfg' = commit_update cfg"
      "C cfg = {}"
      "I cfg \<noteq> {}"
      "P cfg' = P cfg - I cfg"
      "R cfg' = R cfg @ [I cfg]"
      "I cfg' = {}"
      "C cfg' = P cfg - I cfg"
using assms
by (auto
      dest:
        commit_transition_update
        commit_transition_empty_candidates
        commit_transition_nonempty
        commit_transition_problem
        commit_transition_result
        commit_transition_current
        commit_transition_candidates)

(* ========================================================================= *)
(* Section 6 : Recovering the Transition Kind                                *)
(* ========================================================================= *)

text \<open>

The shape of a successor configuration determines whether it was
produced by an Add transition or by a Commit transition.

An Add transition always inserts one vertex into the current
independent set, whereas a Commit transition always clears the
current independent set.

These elementary observations are the first step toward proving
uniqueness of predecessors.

\<close>

lemma add_successor_nonempty_current:
  assumes
      "transition G cfg (Add v) cfg'"
      "finite (I cfg)"
      "v \<notin> I cfg"
  shows
      "I cfg' \<noteq> {}"
proof -

  have
      "I cfg' = I cfg \<union> {v}"
    using
      add_transition_current
      assms(1)
    by blast

  moreover

  have
      "v \<notin> I cfg"
    using
      assms(3)
    .

  ultimately
  show ?thesis
    by auto

qed


lemma commit_successor_empty_current:
  assumes
      "transition G cfg Commit cfg'"
  shows
      "I cfg' = {}"
using
    commit_transition_current
    assms
by blast


lemma add_successor_not_commit:
  assumes
      "transition G cfg1 (Add v) s"
      "transition G cfg2 Commit s"
      "finite (I cfg1)"
      "v \<notin> I cfg1"
  shows False
proof -

  have
      "I s \<noteq> {}"
    using
      add_successor_nonempty_current
      assms(1,3,4)
    by blast

  moreover

  have
      "I s = {}"
    using
      commit_successor_empty_current
      assms(2)
    by blast

  ultimately
  show False
    by simp

qed


lemma commit_successor_not_add:
  assumes
      "transition G cfg1 Commit s"
      "transition G cfg2 (Add v) s"
      "finite (I cfg2)"
      "v \<notin> I cfg2"
  shows False
using
    add_successor_not_commit
    assms
by blast


theorem successor_transition_kind_unique:
  assumes
      "transition G c1 a1 s"
      "transition G c2 a2 s"
      "finite (I c1)"
      "finite (I c2)"
      "wf_config c1"
      "wf_config c2"
  shows
      "(\<exists>v w. a1 = Add v \<and> a2 = Add w)
       \<or>
       (a1 = Commit \<and> a2 = Commit)"
proof -

  from assms(1)
  have
      "(\<exists>v. a1 = Add v) \<or> a1 = Commit"
    using transition_add_or_commit
    by blast

  moreover

  from assms(2)
  have
      "(\<exists>v. a2 = Add v) \<or> a2 = Commit"
    using transition_add_or_commit
    by blast

  ultimately
  show ?thesis
  proof auto

    fix v

    assume
        A1: "a1 = Add v"
    assume
        A2: "a2 = Commit"

    have
        "v \<notin> I c1"
      using
        assms(5)
        add_transition_vertex[OF assms(1)[unfolded A1]]
        wf_I
        wf_C
      unfolding
        inv_I_subset_P_def
        inv_C_subset_P_def
      by auto

    thus False
      using
        add_successor_not_commit
        assms
        A1
        A2
      by auto

  next

    fix v

    assume
        A1: "a2 = Add v"
    assume
        A2: "a1 = Commit"

    have
        "v \<notin> I c2"
      using
        assms(6)
        add_transition_vertex[OF assms(2)[unfolded A1]]
        wf_I
        wf_C
      unfolding
        inv_I_subset_P_def
        inv_C_subset_P_def
      by auto

    thus False
      using
        commit_successor_not_add
        assms
        A1
        A2
      by auto

  qed

qed

(* ========================================================================= *)
(* Section 7 : Reconstruction of Add Predecessors                            *)
(* ========================================================================= *)

text \<open>

This section studies the inverse direction of Add transitions.

Most components of the predecessor configuration can be recovered
immediately from the inversion lemmas established previously.

The only component that requires additional reasoning is the
candidate set, whose uniqueness will be proved later.

\<close>

lemma add_predecessor_problem:
  assumes
      "transition G cfg (Add v) cfg'"
  shows
      "P cfg = P cfg'"
using
    add_transition_problem
    assms
by blast


lemma add_predecessor_result:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "R cfg = R cfg'"
using add_transition_result[OF assms]
by simp
lemma add_predecessor_current:
  assumes
      "transition G cfg (Add v) cfg'"
  shows
      "I cfg = I cfg' - {v}"
proof -

  have
      "I cfg' = I cfg \<union> {v}"
    using
      add_transition_current
      assms
    by blast

  thus ?thesis
    by auto

qed


lemma add_predecessor_vertex_not_current:
  assumes
      "transition G cfg (Add v) cfg'"
      "finite (I cfg)"
      "v \<notin> I cfg"
  shows
      "v \<in> I cfg'"
proof -

  have
      "I cfg' = I cfg \<union> {v}"
    using
      add_transition_current
      assms(1)
    by blast

  thus ?thesis
    using assms(3)
    by auto

qed


lemma add_predecessor_candidate_subset:
  assumes
      "transition G cfg (Add v) cfg'"
  shows
      "C cfg' \<subseteq> C cfg"
proof -

  have
      "C cfg'
       =
       {u\<in>C cfg.
            u > v \<and>
            \<not> adjacent G u v}"
    using
      add_transition_candidates
      assms
    by blast

  thus ?thesis
    by auto

qed


lemma add_predecessor_candidate_order:
  assumes
      "transition G cfg (Add v) cfg'"
      "u \<in> C cfg'"
  shows
      "u > v"
proof -

  have
      "C cfg'
       =
       {u\<in>C cfg.
            u > v \<and>
            \<not> adjacent G u v}"
    using
      add_transition_candidates
      assms(1)
    by blast

  with assms(2)
  show ?thesis
    by auto

qed


lemma add_predecessor_candidate_independent:
  assumes
      "transition G cfg (Add v) cfg'"
      "u \<in> C cfg'"
  shows
      "\<not> adjacent G u v"
proof -

  have
      "C cfg'
       =
       {u\<in>C cfg.
            u > v \<and>
            \<not> adjacent G u v}"
    using
      add_transition_candidates
      assms(1)
    by blast

  with assms(2)
  show ?thesis
    by auto

qed

(* ========================================================================= *)
(* Section 8 : Recovering the Inserted Vertex                                *)
(* ========================================================================= *)

text \<open>

For an Add transition, the inserted vertex is the unique element
that belongs to the successor current independent set but not to the
predecessor current independent set.

This observation is the key ingredient for reconstructing the entire
predecessor configuration.

\<close>

lemma add_inserted_vertex_member:
  assumes
      "transition G cfg (Add v) cfg'"
      "finite (I cfg)"
      "v \<notin> I cfg"
  shows
      "v \<in> I cfg'"
proof -

  have
      "I cfg' = I cfg \<union> {v}"
    using
      add_transition_current
      assms(1)
    by blast

  thus ?thesis
    using assms(3)
    by auto

qed

lemma add_inserted_vertex_difference:
  assumes
      "transition G cfg (Add v) cfg'"
      "finite (I cfg)"
      "v \<notin> I cfg"
  shows
      "I cfg' - I cfg = {v}"
proof -

  have
      "I cfg' = I cfg \<union> {v}"
    using
      add_transition_current
      assms(1)
    by blast

  thus ?thesis
    using assms(3)
    by auto

qed

lemma add_inserted_vertex_unique:
  assumes
      "transition G cfg (Add v1) cfg'"
      "transition G cfg (Add v2) cfg'"
      "finite (I cfg)"
      "v1 \<notin> I cfg"
      "v2 \<notin> I cfg"
  shows
      "v1 = v2"
proof -

  have
      "I cfg' - I cfg = {v1}"
    using
      add_inserted_vertex_difference
      assms(1,3,4)
    by blast

  moreover

  have
      "I cfg' - I cfg = {v2}"
    using
      add_inserted_vertex_difference
      assms(2,3,5)
    by blast

  ultimately
  show ?thesis
    by auto

qed

(* ========================================================================= *)
(* Section 9 : Injectivity of Add Updates                                    *)
(* ========================================================================= *)

text \<open>

The inserted vertex together with the successor configuration uniquely
determines the predecessor.

The following lemmas show that two Add transitions reaching the same
successor must originate from the same predecessor.

\<close>
lemma add_predecessor_current_unique:
  assumes
      "transition G cfg1 (Add v) s"
      "transition G cfg2 (Add v) s"
      "finite (I cfg1)"
      "finite (I cfg2)"
      "v \<notin> I cfg1"
      "v \<notin> I cfg2"
  shows
      "I cfg1 = I cfg2"
proof -

  have
      "I cfg1 = I s - {v}"
    using
      add_predecessor_current
      assms(1)
    by blast

  moreover

  have
      "I cfg2 = I s - {v}"
    using
      add_predecessor_current
      assms(2)
    by blast

  ultimately
  show ?thesis
    by simp

qed

lemma add_predecessor_problem_unique:
  assumes
      "transition G cfg1 (Add v) s"
      "transition G cfg2 (Add v) s"
  shows
      "P cfg1 = P cfg2"
proof -

  have
      "P cfg1 = P s"
    using
      add_predecessor_problem
      assms(1)
    by blast

  moreover

  have
      "P cfg2 = P s"
    using
      add_predecessor_problem
      assms(2)
    by blast

  ultimately
  show ?thesis
    by simp

qed

lemma add_predecessor_result_unique:
  assumes
      "transition G cfg1 (Add v) s"
      "transition G cfg2 (Add v) s"
  shows
      "R cfg1 = R cfg2"
proof -

  have
      "R cfg1 = R s"
    using
      add_predecessor_result
      assms(1)
    by blast

  moreover

  have
      "R cfg2 = R s"
    using
      add_predecessor_result
      assms(2)
    by blast

  ultimately
  show ?thesis
    by simp

qed

(* ========================================================================= *)
(* Section 10 : Reconstruction of the Candidate Set                          *)
(* ========================================================================= *)

text \<open>

The only component that is not immediately recoverable from an Add
transition is the candidate set.

This section shows that the predecessor candidate set is nevertheless
uniquely determined once the transition invariants are taken into
account.

\<close>
lemma add_candidate_filter:
  assumes
      "transition G cfg (Add v) cfg'"
  shows
      "C cfg'
       =
       {u \<in> C cfg.
           u > v \<and>
           \<not> adjacent G u v}"
using
    add_transition_candidates
    assms
  by blast

lemma successor_candidate_properties:
  assumes
      "transition G cfg (Add v) cfg'"
      "u \<in> C cfg'"
  shows
      "u \<in> C cfg"
      "u > v"
      "\<not> adjacent G u v"
using
    assms
    add_transition_candidates
  by auto

lemma successor_candidate_iff:
  assumes
      "transition G cfg (Add v) cfg'"
  shows
      "u \<in> C cfg'
       \<longleftrightarrow>
       u \<in> C cfg
       \<and> u > v
       \<and> \<not> adjacent G u v"
using
    assms
    add_transition_candidates
  by auto

(* ========================================================================= *)
(* Section 11 : Uniqueness of Reconstructed Components                       *)
(* ========================================================================= *)

text \<open>

Two Add transitions reaching the same successor and inserting the same
vertex necessarily agree on the three structural components that are
preserved by the transition:

  • the problem set P,
  • the current independent set I,
  • the accumulated result list R.

This theorem will later allow us to reconstruct the complete predecessor
configuration.

\<close>

theorem add_predecessor_components_unique:
  assumes
      T1: "transition G cfg1 (Add v) s"
  and T2: "transition G cfg2 (Add v) s"
  and F1: "finite (I cfg1)"
  and F2: "finite (I cfg2)"
  and N1: "v \<notin> I cfg1"
  and N2: "v \<notin> I cfg2"
  shows
      "P cfg1 = P cfg2"
      "I cfg1 = I cfg2"
      "R cfg1 = R cfg2"
proof -

  show
      "P cfg1 = P cfg2"
    using
      add_predecessor_problem_unique
      T1 T2
    by blast

  show
      "I cfg1 = I cfg2"
    using
      add_predecessor_current_unique
      T1 T2 F1 F2 N1 N2
    by blast

  show
      "R cfg1 = R cfg2"
    using
      add_predecessor_result_unique
      T1 T2
    by blast

qed

(* ========================================================================= *)
(* Section 12 : Uniqueness of the Candidate Set                              *)
(* ========================================================================= *)

text \<open>

The only remaining component of a predecessor configuration is the
candidate set.

Since the problem set and the current independent set are already
uniquely determined, the candidate set is also uniquely determined by
the well-formedness invariant.

This completes reconstruction of Add predecessors.

\<close>
(* ========================================================================= *)
(* Section 13 : Candidate Set is Uniquely Reconstructible                    *)
(* ========================================================================= *)

theorem add_predecessor_candidates_unique:
  assumes
      IC1: "inv_C_characterization G cfg1"
  and IC2: "inv_C_characterization G cfg2"
  and HP:  "P cfg1 = P cfg2"
  and HI:  "I cfg1 = I cfg2"
  shows
      "C cfg1 = C cfg2"
proof (cases "I cfg1 = {}")

  case True

  hence "I cfg2 = {}"
    using HI
    by simp

  from IC1 True
  have
    "C cfg1 = P cfg1"
    unfolding inv_C_characterization_def
    by simp

  moreover

  from IC2 `I cfg2 = {}`
  have
    "C cfg2 = P cfg2"
    unfolding inv_C_characterization_def
    by simp

  ultimately
  show ?thesis
    using HP
    by simp

next

  case False

  hence NZ1:
    "I cfg1 \<noteq> {}"
    by simp

  have NZ2:
    "I cfg2 \<noteq> {}"
    using False HI
    by simp

  from IC1 NZ1
  have H1:
    "C cfg1 =
      {u \<in> P cfg1 - I cfg1.
          u > Max (I cfg1) \<and>
          (\<forall>w\<in>I cfg1. \<not> adjacent G u w)}"
    unfolding inv_C_characterization_def
    by simp

  from IC2 NZ2
  have H2:
    "C cfg2 =
      {u \<in> P cfg2 - I cfg2.
          u > Max (I cfg2) \<and>
          (\<forall>w\<in>I cfg2. \<not> adjacent G u w)}"
    unfolding inv_C_characterization_def
    by simp

  have
      "Max (I cfg1) = Max (I cfg2)"
    using HI IC1
    unfolding inv_C_characterization_def
    by simp

  with HP HI H1 H2
  show ?thesis
    by auto

qed

theorem add_predecessor_unique:
  assumes
      WF1: "inv_C_characterization G cfg1"
  and WF2: "inv_C_characterization G cfg2"
  and T1:  "transition G cfg1 (Add v) s"
  and T2:  "transition G cfg2 (Add v) s"
  and F1:  "finite (I cfg1)"
  and F2:  "finite (I cfg2)"
  and N1:  "v \<notin> I cfg1"
  and N2:  "v \<notin> I cfg2"
  shows
      "cfg1 = cfg2"
proof -

  have HP:
    "P cfg1 = P cfg2"
    using add_predecessor_problem_unique T1 T2 .

  have HI:
    "I cfg1 = I cfg2"
    using
      add_predecessor_current_unique
      T1 T2 F1 F2 N1 N2 .

  have HR:
    "R cfg1 = R cfg2"
    using
      add_predecessor_result_unique
      T1 T2 .

  have HC:
    "C cfg1 = C cfg2"
    using
      add_predecessor_candidates_unique
      WF1 WF2 HP HI .

  show ?thesis
    by (cases cfg1; cases cfg2; simp add: HP HI HR HC)

qed

(* ========================================================================= *)
(* Section : Commit Predecessor Uniqueness                                   *)
(* ========================================================================= *)

theorem commit_predecessor_unique:
  assumes
      T1: "transition G cfg1 Commit s"
  and T2: "transition G cfg2 Commit s"
  shows
      "cfg1 = cfg2"
proof -

  have HC1:
      "C cfg1 = {}"
    using
      commit_transition_empty_candidates[OF T1]
    .

  have HC2:
      "C cfg2 = {}"
    using
      commit_transition_empty_candidates[OF T2]
    .

  have HP1:
      "P s = P cfg1 - I cfg1"
    using
      commit_transition_problem[OF T1]
    .

  have HP2:
      "P s = P cfg2 - I cfg2"
    using
      commit_transition_problem[OF T2]
    .

  have HR1:
      "R s = R cfg1 @ [I cfg1]"
    using
      commit_transition_result[OF T1]
    .

  have HR2:
      "R s = R cfg2 @ [I cfg2]"
    using
      commit_transition_result[OF T2]
    .

  have Happend:
      "R cfg1 @ [I cfg1]
       =
       R cfg2 @ [I cfg2]"
    using HR1 HR2
    by simp

  have HR:
      "R cfg1 = R cfg2"
    and HI:
      "I cfg1 = I cfg2"
    using Happend
    by auto

  have HP:
      "P cfg1 = P cfg2"
    using HP1 HP2 HI
    by auto

  show ?thesis
    by (cases cfg1; cases cfg2;
        simp add: HP HI HR HC1 HC2)

qed

(* ========================================================================= *)
(* Section 14 : Uniqueness of Predecessors                                   *)
(* ========================================================================= *)

text \<open>

Every configuration has at most one predecessor.

The proof proceeds by first identifying the transition kind
(Add or Commit), then invoking the corresponding uniqueness theorem.

\<close>

theorem predecessor_unique:
  assumes
      T1: "transition G cfg1 a1 s"
  and T2: "transition G cfg2 a2 s"
  and F1: "finite (I cfg1)"
  and F2: "finite (I cfg2)"
  and WF1: "wf_config cfg1"
  and WF2: "wf_config cfg2"
  and IC1: "inv_C_characterization G cfg1"
  and IC2: "inv_C_characterization G cfg2"
  shows
      "cfg1 = cfg2"
proof -

  have HK:
      "(\<exists>v w. a1 = Add v \<and> a2 = Add w)
       \<or>
       (a1 = Commit \<and> a2 = Commit)"
    using
      successor_transition_kind_unique
      T1 T2 F1 F2 WF1 WF2
    by blast

  then show ?thesis
  proof

    assume
      "\<exists>v w. a1 = Add v \<and> a2 = Add w"

    then obtain v w
      where
        A1: "a1 = Add v"
        and A2: "a2 = Add w"
      by blast

    have HV:
      "v = w"
    proof -

      have
        "transition G cfg1 (Add v) s"
        using T1 A1
        by simp

      moreover

      have
        "transition G cfg2 (Add w) s"
        using T2 A2
        by simp

      moreover

      have
        "v \<notin> I cfg1"
        using
          WF1
          add_transition_vertex[OF calculation(1)]
          wf_I
          wf_C
        unfolding
          inv_I_subset_P_def
          inv_C_subset_P_def
        by auto

      moreover

      have
        "w \<notin> I cfg2"
        using
          WF2
          add_transition_vertex[OF calculation(2)]
          wf_I
          wf_C
        unfolding
          inv_I_subset_P_def
          inv_C_subset_P_def
        by auto

      ultimately
      show ?thesis
        using
          add_inserted_vertex_unique
          F1 F2
        by blast

    qed

    have
      "transition G cfg1 (Add v) s"
      using T1 A1
      by simp

    moreover

    have
      "transition G cfg2 (Add v) s"
      using T2 A2 HV
      by simp

    moreover

    have
      "v \<notin> I cfg1"
      using
        WF1
        add_transition_vertex[OF calculation(1)]
        wf_I
        wf_C
      unfolding
        inv_I_subset_P_def
        inv_C_subset_P_def
      by auto

    moreover

    have
      "v \<notin> I cfg2"
      using
        WF2
        add_transition_vertex[OF calculation(2)]
        wf_I
        wf_C
      unfolding
        inv_I_subset_P_def
        inv_C_subset_P_def
      by auto

    ultimately
    show ?thesis
      using
        add_predecessor_unique
        IC1 IC2 F1 F2
      by blast

  next

    assume
      "a1 = Commit \<and> a2 = Commit"

    then have
      "transition G cfg1 Commit s"
      using T1
      by simp

    moreover

    have
      "transition G cfg2 Commit s"
      using `a1 = Commit \<and> a2 = Commit` T2
      by simp

    ultimately
    show ?thesis
      using
        commit_predecessor_unique
      by blast

  qed

qed
theorem init_has_no_predecessor:
  shows
    "\<not> (\<exists>cfg a. transition G cfg a (init_config G))"
proof
  assume "\<exists>cfg a. transition G cfg a (init_config G)"

  then obtain cfg a
    where T:
      "transition G cfg a (init_config G)"
    by blast

  from transition_add_or_commit[OF T]
  show False
  proof

    assume "\<exists>v. a = Add v"

    then obtain v
      where A: "a = Add v"
      by blast

    from add_transition_current[OF T[unfolded A]]
    have
      "I (init_config G) = I cfg \<union> {v}"
      by simp

    thus False
      unfolding init_config_def
      by auto

  next

    assume C:
      "a = Commit"

    from commit_transition_result[OF T[unfolded C]]
    have
      "R (init_config G) = R cfg @ [I cfg]"
      by simp

    thus False
      unfolding init_config_def
      by auto
  qed
qed

inductive reachable :: "graph \<Rightarrow> config \<Rightarrow> bool" where
  root:
    "reachable G (init_config G)"
| step:
    "reachable G c \<Longrightarrow>
     transition G c a c' \<Longrightarrow>
     reachable G c'"

theorem reachable_has_predecessor:
  assumes
    "reachable G c"
    "c \<noteq> init_config G"
  shows
    "\<exists>p a.
        reachable G p \<and>
        transition G p a c"
using assms
proof (induction rule: reachable.induct)
  case root
  then show ?case
    by simp
next
  case (step p a c)
  then show ?case
    by blast
qed

theorem rooted_tree:
  shows
      "reachable G (init_config G)"
      "\<not> (\<exists>p a. transition G p a (init_config G))"
      "\<And>c.
          reachable G c \<Longrightarrow>
          c \<noteq> init_config G \<Longrightarrow>
          \<exists>! pa.
              reachable G (fst pa) \<and>
              transition G (fst pa) (snd pa) c"
proof -

  show "reachable G (init_config G)"
    by (rule reachable.root)

  show "\<not> (\<exists>p a. transition G p a (init_config G))"
    by (rule init_has_no_predecessor)

  fix c
  assume Rc: "reachable G c"
  assume Nc: "c \<noteq> init_config G"

  obtain p a
    where
      Rp: "reachable G p"
      and Tp: "transition G p a c"
    using reachable_has_predecessor[OF Rc Nc]
    by blast

  have Unique:
    "\<And>p' a'.
        reachable G p' \<Longrightarrow>
        transition G p' a' c
        \<Longrightarrow> p' = p \<and> a' = a"
  proof -
    fix p' a'
    assume Rp': "reachable G p'"
    assume Tp': "transition G p' a' c"

    have "p' = p"
      using predecessor_unique Tp Tp' Rp Rp'
      by blast

    moreover

    have "a' = a"
      using Tp Tp' calculation
            successor_transition_kind_unique
            add_transition_unique_target
            commit_transition_unique_target
      by blast

    ultimately
    show "p' = p \<and> a' = a"
      by simp
  qed

  show
    "\<exists>! pa.
        reachable G (fst pa) \<and>
        transition G (fst pa) (snd pa) c"
  proof (rule ex1I)

    show
      "reachable G (fst (p,a)) \<and>
       transition G (fst (p,a)) (snd (p,a)) c"
      using Rp Tp
      by simp

  next

    fix pa
    assume
      "reachable G (fst pa) \<and>
       transition G (fst pa) (snd pa) c"

    then obtain p' a'
      where
        Pa: "pa = (p',a')"
        and Rp': "reachable G p'"
        and Tp': "transition G p' a' c"
      by (cases pa) auto

    have "p' = p \<and> a' = a"
      using Unique Rp' Tp'
      by blast

    with Pa
    show "pa = (p,a)"
      by simp

  qed

qed


end