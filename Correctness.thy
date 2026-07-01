theory Correctness
  imports Unique_Predecessor
begin

(* ====================================================================== *)
(* Section 1 : Proper Colorings                                           *)
(* ====================================================================== *)

text \<open>
A terminal configuration should represent a proper coloring of the graph.
The following definitions formalize this notion.
\<close>

definition coloring_covers ::
  "graph \<Rightarrow> vertex set list \<Rightarrow> bool"
where
  "coloring_covers G Cs \<longleftrightarrow>
      \<Union> (set Cs) = V G"

definition pairwise_disjoint ::
  "vertex set list \<Rightarrow> bool"
where
  "pairwise_disjoint Cs \<longleftrightarrow>
      (\<forall>i<length Cs.
         \<forall>j<length Cs.
            i \<noteq> j \<longrightarrow> Cs ! i \<inter> Cs ! j = {})"

definition coloring_independent ::
  "graph \<Rightarrow> vertex set list \<Rightarrow> bool"
where
  "coloring_independent G Cs \<longleftrightarrow>
      (\<forall>C \<in> set Cs.
          independent G C)"

definition proper_coloring ::
  "graph \<Rightarrow> vertex set list \<Rightarrow> bool"
where
  "proper_coloring G Cs \<longleftrightarrow>
      coloring_covers G Cs \<and>
      pairwise_disjoint Cs \<and>
      coloring_independent G Cs"

lemma proper_coloring_independent:
  assumes "proper_coloring G Cs"
  shows "coloring_independent G Cs"
  using assms
  unfolding proper_coloring_def
  by simp

lemma proper_coloring_cover:
  assumes "proper_coloring G Cs"
  shows "coloring_covers G Cs"
  using assms
  unfolding proper_coloring_def
  by simp

lemma proper_coloring_disjoint:
  assumes "proper_coloring G Cs"
  shows "pairwise_disjoint Cs"
  using assms
  unfolding proper_coloring_def
  by simp

theorem terminal_problem_empty:
  assumes T: "terminal cfg"
  shows "P cfg = {}"
proof -
  from T
  have "P cfg = {} \<and> I cfg = {} \<and> C cfg = {}"
    unfolding terminal_def
    by simp
  then show ?thesis
    by simp
qed

lemma terminal_current_empty:
  assumes T: "terminal cfg"
  shows "I cfg = {}"
proof -
  from T
  have "P cfg = {} \<and> I cfg = {} \<and> C cfg = {}"
    unfolding terminal_def
    by simp
  then show ?thesis
    by simp
qed

lemma terminal_candidates_empty:
  assumes T: "terminal cfg"
  shows "C cfg = {}"
proof -
  from T
  have "P cfg = {} \<and> I cfg = {} \<and> C cfg = {}"
    unfolding terminal_def
    by simp
  then show ?thesis
    by simp
qed

inductive follows_path ::
  "graph \<Rightarrow> config \<Rightarrow> action list \<Rightarrow> config \<Rightarrow> bool"
where
  empty:
    "follows_path G c [] c"
|
  step:
    "transition G c a c' \<Longrightarrow>
     follows_path G c' as c'' \<Longrightarrow>
     follows_path G c (a # as) c''"

theorem unique_path:
  assumes
      "reachable G c"
  shows
      "\<exists>! as.
          follows_path G (init_config G) as c"
proof -
  obtain as
    where
      "follows_path G (init_config G) as c"
    using reachable_has_path assms
    by blast

  moreover

  have
      "\<And>bs.
        follows_path G (init_config G) bs c \<Longrightarrow>
        bs = as"
    using follows_path_unique calculation
    by blast

  ultimately
  show ?thesis
    by (rule ex1I)
qed

lemma terminal_coloring_covers:
  assumes
      "reachable G cfg"
      "terminal cfg"
  shows
      "coloring_covers G (R cfg)"
proof -

  have
      "\<Union> (set (R cfg)) = V G - P cfg"
    using reachable_R_cover assms(1)
    by blast

  moreover

  have
      "P cfg = {}"
    using terminal_problem_empty assms(2)
    by blast

  ultimately
  show ?thesis
    unfolding coloring_covers_def
    by simp

qed

lemma terminal_coloring_independent:
  assumes
      "reachable G cfg"
      "terminal cfg"
  shows
      "coloring_independent G (R cfg)"
proof -

  have
      "\<forall>S \<in> set (R cfg).
          independent G S"
    using reachable_R_independent assms(1)
    by blast

  thus ?thesis
    unfolding coloring_independent_def
    by blast

qed

lemma terminal_coloring_disjoint:
  assumes
      "reachable G cfg"
      "terminal cfg"
  shows
      "pairwise_disjoint (R cfg)"
proof -

  show ?thesis
    using reachable_R_disjoint assms(1)
    by blast

qed

theorem soundness:
  assumes
      "reachable G cfg"
      "terminal cfg"
  shows
      "proper_coloring G (R cfg)"
proof -

  have
      "coloring_covers G (R cfg)"
    using terminal_coloring_covers assms
    by blast

  moreover

  have
      "pairwise_disjoint (R cfg)"
    using terminal_coloring_disjoint assms
    by blast

  moreover

  have
      "coloring_independent G (R cfg)"
    using terminal_coloring_independent assms
    by blast

  ultimately
  show ?thesis
    unfolding proper_coloring_def
    by blast

qed

fun RMIS_sequence ::
  "graph \<Rightarrow> vertex set \<Rightarrow> vertex set list \<Rightarrow> bool"
where
  "RMIS_sequence G U [] = (U = {})"
| "RMIS_sequence G U (M # Ms) =
      (maximal_independent G U M \<and>
       RMIS_sequence G (U - M) Ms)"

definition RMIS ::
  "graph \<Rightarrow> vertex set list \<Rightarrow> bool"
where
  "RMIS G Rs \<longleftrightarrow> RMIS_sequence G (V G) Rs"

lemma RMIS_sequence_head:
  assumes
    "RMIS_sequence G U (M # Ms)"
  shows
    "maximal_independent G U M"
using assms
by simp

lemma RMIS_sequence_tail:
  assumes
    "RMIS_sequence G U (M # Ms)"
  shows
    "RMIS_sequence G (U - M) Ms"
using assms
by simp

lemma RMIS_head:
  assumes
    "RMIS G (M # Ms)"
  shows
    "maximal_independent G (V G) M"
using assms
unfolding RMIS_def
by simp

lemma RMIS_tail:
  assumes
    "RMIS G (M # Ms)"
  shows
    "RMIS_sequence G (V G - M) Ms"
using assms
unfolding RMIS_def
  by simp

lemma RMIS_empty:
  assumes "RMIS_sequence G U []"
  shows "U = {}"
using assms
  by simp

lemma RMIS_nonempty_subset:
  assumes
    "RMIS_sequence G U (M # Ms)"
  shows
    "M \<subseteq> U"
proof -
  from assms
  have "maximal_independent G U M"
    by simp
  thus ?thesis
    by (rule maximal_independent_subset)
qed

lemma RMIS_nonempty_independent:
  assumes
      "RMIS_sequence G U (M # Ms)"
  shows
      "independent G M"
proof -
  from assms
  have
      "maximal_independent G U M"
    by simp
  thus ?thesis
    by (rule maximal_independent_independent)
qed

lemma RMIS_residual_subset:
  assumes
      "RMIS_sequence G U (M # Ms)"
  shows
      "U - M \<subseteq> U"
proof
  fix x
  assume
      "x \<in> U - M"
  thus
      "x \<in> U"
    by auto
qed

lemma RMIS_nonempty:
  assumes
      "RMIS_sequence G U (M # Ms)"
  shows
      "M \<noteq> {}"
proof
  assume
      "M = {}"

  from assms
  have
      "maximal_independent G U {}"
    by simp

  moreover
  have
      "U = {}"
  proof (cases "U = {}")
    case True
    then show ?thesis .
  next
    case False
    then obtain v
      where
        "v \<in> U"
      by auto

    from calculation
    have
      "\<forall>v\<in>U - {}. \<exists>u\<in>{}. adjacent G u v"
      unfolding maximal_independent_def
      by blast

    with `v \<in> U`
    show ?thesis
      by auto
  qed

  with assms
  show False
    by simp
qed

lemma empty_current_candidates:
  assumes
      "I cfg = {}"
      "inv_C_characterization G cfg"
  shows
      "C cfg = P cfg"
using assms
unfolding inv_C_characterization_def
  by simp

lemma RMIS_vertex_initial_candidate:
  assumes
      "RMIS_sequence G U (M # Ms)"
      "P cfg = U"
      "I cfg = {}"
      "inv_C_characterization G cfg"
      "v \<in> M"
  shows
      "v \<in> C cfg"
proof -
  from assms(4,3)
  have
      "C cfg = P cfg"
    unfolding inv_C_characterization_def
    by simp

  moreover

  from assms(1)
  have
      "M \<subseteq> U"
    by (rule RMIS_nonempty_subset)

  with assms(2,5)
  have
      "v \<in> P cfg"
    by auto

  ultimately
  show ?thesis
    by simp
qed

lemma subset_of_RMIS_independent:
  assumes
    "RMIS_sequence G U (M # Ms)"
    "S \<subseteq> M"
  shows
    "independent G S"
proof -
  have "independent G M"
    using assms(1)
    by (simp add: maximal_independent_independent)

  thus ?thesis
    using assms(2)
    by (rule independent_mono)
qed

lemma RMIS_previous_nonadjacent:
  assumes
      "RMIS_sequence G U (M # Ms)"
      "I cfg \<subseteq> M"
      "v \<in> M - I cfg"
      "w \<in> I cfg"
  shows
      "\<not> adjacent G w v"
proof -

  have Hind:
      "independent G M"
    using assms(1)
    by (simp add: maximal_independent_independent)

  have
      "w \<in> M"
    using assms(2,4)
    by auto

  moreover

  have
      "v \<in> M"
    using assms(3)
    by auto

  moreover

  have
      "w \<noteq> v"
    using assms(3,4)
    by auto

  ultimately

  show ?thesis
    using Hind
    unfolding independent_def
    by blast

qed

lemma RMIS_next_above_Max:
  assumes
      "finite (I cfg)"
      "I cfg \<noteq> {}"
      "\<forall>u\<in>I cfg. u < v"
  shows
      "Max (I cfg) < v"
using assms Max_in
  by blast

theorem RMIS_next_candidate:
  assumes
      "RMIS_sequence G U (M # Ms)"
      "inv_C_characterization G cfg"
      "P cfg = U"
      "I cfg \<subseteq> M"
      "v \<in> M - I cfg"
      "finite (I cfg)"
      "I cfg \<noteq> {}"
      "\<forall>u\<in>I cfg. u < v"
  shows
      "v \<in> C cfg"
proof -

  have HvP:
      "v \<in> P cfg"
  proof -
    have "M \<subseteq> U"
      using assms(1)
      by (simp add: maximal_independent_subset)
    with assms(3,5)
    show ?thesis
      by auto
  qed

  have HvNotI:
      "v \<notin> I cfg"
    using assms(5)
    by auto

  have HvMax:
      "Max (I cfg) < v"
    using
        RMIS_next_above_Max
        assms(6-8)
    by blast

  have Hnonadj:
      "\<forall>w\<in>I cfg. \<not> adjacent G w v"
  proof
    fix w
    assume "w \<in> I cfg"
    thus "\<not> adjacent G w v"
      using
          RMIS_previous_nonadjacent
          assms(1,4,5)
      by blast
  qed

  show ?thesis
    using
        HvP
        HvNotI
        HvMax
        Hnonadj
        assms(2)
    unfolding inv_C_characterization_def
    by auto

qed

theorem RMIS_add_exists:
  assumes
      RMIS: "RMIS_sequence G U (M # Ms)"
  and Inv: "inv_C_characterization G cfg"
  and P:   "P cfg = U"
  and Sub: "I cfg \<subseteq> M"
  and Vin: "v \<in> M - I cfg"
  and Fin: "finite (I cfg)"
  and Non: "I cfg \<noteq> {}"
  and Ord: "\<forall>u\<in>I cfg. u < v"
  and Pr:  "prune (add_update G cfg v)"
  shows
      "transition G cfg (Add v) (add_update G cfg v)"
proof -

  have
      "v \<in> C cfg"
    using
        RMIS_next_candidate
        RMIS Inv P Sub Vin Fin Non Ord
    by blast

  thus ?thesis
    using Pr
    unfolding add_update_def
    by (rule transition.Add)

qed

theorem RMIS_commit_exists:
  assumes
      RMIS: "RMIS_sequence G U (M # Ms)"
  and P:    "P cfg = U"
  and I:    "I cfg = M"
  and C:    "C cfg = {}"
  and Pr:   "prune (commit_update cfg)"
  shows
      "transition G cfg Commit (commit_update cfg)"
proof -

  have MI:
      "maximal_independent G (P cfg) (I cfg)"
  proof -
    have
        "maximal_independent G U M"
      using RMIS
      by (rule RMIS_sequence_head)

    thus ?thesis
      using P I
      by simp
  qed

  have NE:
      "I cfg \<noteq> {}"
  proof -
    have
        "M \<noteq> {}"
      using RMIS
      by (rule RMIS_nonempty)

    thus ?thesis
      using I
      by simp
  qed

  show ?thesis
    using
        C
        NE
        MI
        Pr
    unfolding commit_update_def
    by (rule transition.Commit)

qed

theorem RMIS_first_add_exists:
  assumes
      RMIS: "RMIS_sequence G U (M # Ms)"
  and Inv:  "inv_C_characterization G cfg"
  and P:    "P cfg = U"
  and I:    "I cfg = {}"
  and Vin:  "v \<in> M"
  and Pr:   "prune (add_update G cfg v)"
  shows
      "transition G cfg (Add v) (add_update G cfg v)"
proof -

  have HC:
      "C cfg = P cfg"
    using Inv I
    unfolding inv_C_characterization_def
    by simp

  have HM:
      "M \<subseteq> U"
    using RMIS_nonempty_subset[OF RMIS] .

  have
      "v \<in> U"
    using HM Vin
    by auto

  hence
      "v \<in> P cfg"
    using P
    by simp

  hence
      "v \<in> C cfg"
    using HC
    by simp

  thus ?thesis
    using Pr
    unfolding add_update_def
    by (rule transition.Add)

qed

lemma build_one_MIS_step:
  assumes
      RMIS: "RMIS_sequence G U (M # Ms)"
  and Reach: "reachable G cfg"
  and P:     "P cfg = U"
  and Inv:   "inv_C_characterization G cfg"
  and Sub:   "I cfg \<subseteq> M"
  and Vin:   "v \<in> M - I cfg"
  and Fin:   "finite (I cfg)"
  and Non:   "I cfg \<noteq> {}"
  and Ord:   "\<forall>u\<in>I cfg. u < v"
  and Pr:    "prune (add_update G cfg v)"
  shows
      "reachable G (add_update G cfg v)"
proof -

  have T:
      "transition G cfg (Add v) (add_update G cfg v)"
    using
        RMIS
        Inv
        P
        Sub
        Vin
        Fin
        Non
        Ord
        Pr
    by (rule RMIS_add_exists)

  have E:
      "TG_edge G cfg (add_update G cfg v)"
    using T
    by (rule TG_edgeI)

  show ?thesis
    using
        Reach
        E
    by (rule reachable.step)

qed

lemma build_one_MIS_commit:
  assumes
      RMIS: "RMIS_sequence G U (M # Ms)"
      and Reach: "reachable G cfg"
      and P: "P cfg = U"
      and I: "I cfg = M"
      and C: "C cfg = {}"
      and Pr: "prune (commit_update cfg)"
  shows
      "reachable G (commit_update cfg)"
proof -

  have
      "transition G cfg Commit (commit_update cfg)"
    using
      RMIS_commit_exists
      RMIS P I C Pr
    by blast

  thus ?thesis
    using Reach
    by (rule reachable_transition)

qed

theorem build_one_MIS:
  assumes RMIS: "RMIS_sequence G U (M # Ms)"
      and Reach: "reachable G cfg"
      and P_eq:  "P cfg = U"
      and I_sub: "I cfg \<subseteq> M"
      and Inv:   "inv_C_characterization G cfg"
  shows "\<exists>cfg1. reachable G cfg1 \<and> P cfg1 = U \<and> I cfg1 = M \<and> C cfg1 = {}"
proof (induction "card (M - I cfg) + length (M # Ms)" arbitrary: cfg U M Ms I_sub Inv Reach P_eq RMIS rule: less_induct)
  case (less m cfg U M Ms I_sub Inv Reach P_eq RMIS)
  show ?case
  proof (cases "I cfg = M")
    case True
    (* Base case: Configuration already satisfies I = M. *)
    (* Since inv_C_characterization holds and I=M, we must show C = {} *)
    have "C cfg = {}" using True Inv unfolding inv_C_characterization_def by auto
    with True show ?thesis using Reach P_eq by blast
  next
    case False
    (* Inductive step: Pick v in M - I cfg *)
    obtain v where v_in: "v \<in> M - I cfg" using False by auto
    let ?cfg' = "add_update G cfg v"
    
    (* 1. Transition Existence *)
    have trans: "transition G cfg (Add v) ?cfg'"
      using RMIS Inv P_eq I_sub v_in RMIS_add_exists by blast
      
    (* 2. Reachability Preservation *)
    have reach': "reachable G ?cfg'"
      using Reach trans by (rule reachable.step)
      
    (* 3. Invariant Preservation for IH *)
    have I_sub': "I ?cfg' \<subseteq> M" 
      unfolding add_update_def using I_sub v_in by auto
      
    (* 4. Measure Reduction *)
    have "card (M - I ?cfg') + length (M # Ms) < card (M - I cfg) + length (M # Ms)"
      using v_in by (simp add: card_psubset)

    (* 5. Application of IH *)
    from less.hyps[OF this RMIS reach' P_eq I_sub' Inv]
    show ?thesis by blast
  qed

theorem completeness:
  assumes "RMIS G Rs"
  shows "\<exists>as cfg_terminal. follows_path G (init_config G) as cfg_terminal \<and> 
               terminal cfg_terminal \<and> R cfg_terminal = Rs"
proof (induction Rs arbitrary: G)
  case Nil
  (* Base case: Rs is [], meaning the problem set is empty. *)
  (* The initial configuration is already terminal for an empty graph. *)
  show ?case
  proof (rule exI[of _ "[]"], rule exI[of _ "init_config G"], rule conjI)
    show "follows_path G (init_config G) [] (init_config G)"
      by (rule follows_path.empty)
  next
    show "terminal (init_config G) \<and> R (init_config G) = []"
      using Nil.prems unfolding RMIS_def RMIS_sequence.simps init_config_def terminal_def
      by auto
  qed
next
  case (Cons M Ms)
  (* Inductive step: Rs = M # Ms *)
  (* 1. Reach configuration cfg_M where I = M using build_one_MIS. *)
  obtain cfg_M where reach_M: "reachable G cfg_M" 
                   and P_M: "P cfg_M = V G" 
                   and I_M: "I cfg_M = M" 
                   and C_M: "C cfg_M = {}"
    using build_one_MIS[OF Cons.prems(1)[unfolded RMIS_def]] by blast

  (* 2. Get the unique path to the MIS configuration. *)
  obtain as_M where path_M: "follows_path G (init_config G) as_M cfg_M"
    using unique_path reach_M by blast

  (* 3. Perform the Commit transition to reach the residual problem state. *)
  let ?cfg_commit = "commit_update cfg_M"
  have trans_commit: "transition G cfg_M Commit ?cfg_commit"
    using RMIS_commit_exists Cons.prems(1)[unfolded RMIS_def] P_M I_M C_M by blast
  
  have path_full: "follows_path G (init_config G) (as_M @ [Commit]) ?cfg_commit"
    using path_M trans_commit by (rule follows_path.step)

  (* 4. Inductive hypothesis on the residual graph. *)
  let ?G_resid = "induced_subgraph G (V G - M)"
  have "RMIS_sequence G (V G - M) Ms" 
    using Cons.prems(1)[unfolded RMIS_def] by (rule RMIS_tail)
  
  from Cons.IH[of ?G_resid] obtain as_Ms cfg_term where 
    "follows_path ?G_resid (init_config ?G_resid) as_Ms cfg_term \<and> 
     terminal cfg_term \<and> R cfg_term = Ms"
    by blast

  (* 5. Combine paths and witness the existentials. *)
  show ?case
    by (rule exI[of _ "as_M @ [Commit] @ as_Ms"], rule exI[of _ "cfg_term"], auto)
qed


end