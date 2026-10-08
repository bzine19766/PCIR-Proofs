theory MIS_Paw
  imports MIS_Structure
begin

text \<open>
  The Paw graph example of Section 7, connected to the mechanised semantics.

  Strategy.  An executable successor function Paw_succs is defined for the Paw graph and
  proved to agree with the relation step on well-formed configurations (Paw_succs_step).
  A bounded depth-first enumeration Paw_reach_list is then proved to be exactly ReachG
  (Paw_ReachG_eq).  The counts reported in the paper (37 reachable configurations, 36 edges,
  6 terminal configurations, 2 dead ends, 15 commit-ready configurations) are obtained by
  evaluation and transferred to statements about ReachG itself.
\<close>

(* ========================================================================= *)
(* Part 1 : The graph                                                        *)
(* ========================================================================= *)

definition Paw_V :: "nat set" where
  "Paw_V = {0, 1, 2, 3}"

definition Paw_E :: "(nat \<times> nat) set" where
  "Paw_E = {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (2, 3), (3, 2)}"

lemma Paw_finite: "finite Paw_V"
  unfolding Paw_V_def by simp

lemma Paw_sym: "sym Paw_E"
  unfolding Paw_E_def sym_def by auto

lemma Paw_irrefl: "irrefl Paw_E"
  unfolding Paw_E_def irrefl_def by auto

interpretation Paw: fixed_graph Paw_V Paw_E
proof
  show "finite Paw_V" by (rule Paw_finite)
  show "sym Paw_E" by (rule Paw_sym)
  show "irrefl Paw_E" by (rule Paw_irrefl)
qed

lemma cfg_obtain:
  obtains P R I C where "(c :: nat config) = (P, R, I, C)"
  by (cases c) auto

(* ========================================================================= *)
(* Part 2 : Executable counterparts of the semantic notions                  *)
(* ========================================================================= *)

text \<open>
  Plain (non-locale) definitions are used so that the code generator can evaluate them.
  Each one is proved equal to the corresponding locale notion.
\<close>

definition Paw_cand :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "Paw_cand P I =
     (if I = {} then P
      else Set.filter (\<lambda>v. Max I < v \<and> (\<forall>u \<in> I. (u, v) \<notin> Paw_E)) (P - I))"

lemma Paw_cand_eq: "Paw_cand P I = Paw.candidate_set P I"
  by (cases "I = {}") (auto simp: Paw_cand_def Paw.candidate_set_def)

definition Paw_max :: "nat set \<Rightarrow> nat set \<Rightarrow> bool" where
  "Paw_max P I = (\<forall>v \<in> P - I. \<exists>u \<in> I. (u, v) \<in> Paw_E)"

lemma Paw_max_eq:
  assumes "I \<subseteq> P" "Paw.is_indep I"
  shows "Paw_max P I = Paw.is_maximal_indep P I"
  using assms unfolding Paw_max_def Paw.is_maximal_indep_def by auto

fun Paw_succs :: "nat config \<Rightarrow> nat config list" where
  "Paw_succs (P, R, I, C) =
     (if C \<noteq> {} then
        map (\<lambda>v. (P, R, I \<union> {v}, Paw_cand P (I \<union> {v}))) (sorted_list_of_set C)
      else if I \<noteq> {} \<and> Paw_max P I then
        [(P - I, R @ [I], {}, P - I)]
      else [])"

text \<open>
  Correctness of Paw_succs: on well-formed configurations, the executable successor list is
  exactly the set of successors in the transition relation.
\<close>

lemma Paw_succs_iff:
  assumes wf: "Paw.well_formed (P, R, I, C)"
  shows "Paw.step (P, R, I, C) c' \<longleftrightarrow> c' \<in> set (Paw_succs (P, R, I, C))"
proof -
  note p = Paw.wf_parts[OF wf]
  have finP: "finite P" by (rule Paw.finite_sub[OF p(1)])
  have CP: "C \<subseteq> P" unfolding p(4) by (rule Paw.candidate_set_subset)
  have finC: "finite C" by (rule finite_subset[OF CP finP])
  have sl: "set (sorted_list_of_set C) = C" by (simp add: finC)
  have mx: "Paw_max P I = Paw.is_maximal_indep P I" by (rule Paw_max_eq[OF p(3) p(2)])
  show ?thesis
  proof (cases "C = {}")
    case True
    have c1: "\<not> (C \<noteq> {})" using True by simp
    show ?thesis
    proof (cases "I \<noteq> {} \<and> Paw.is_maximal_indep P I")
      case T: True
      have c2: "I \<noteq> {} \<and> Paw_max P I" by (metis T mx)
      have eq: "Paw_succs (P, R, I, C) = [(P - I, R @ [I], {}, P - I)]"
        unfolding Paw_succs.simps by (simp only: if_not_P[OF c1] if_P[OF c2])
      show ?thesis unfolding eq Paw.step_unfold using T True by auto
    next
      case F: False
      have c2: "\<not> (I \<noteq> {} \<and> Paw_max P I)" by (metis F mx)
      have eq: "Paw_succs (P, R, I, C) = []"
        unfolding Paw_succs.simps by (simp only: if_not_P[OF c1] if_not_P[OF c2])
      show ?thesis unfolding eq Paw.step_unfold using F True by auto
    qed
  next
    case False
    have rhs: "set (Paw_succs (P, R, I, C)) =
               (\<lambda>v. (P, R, I \<union> {v}, Paw.candidate_set P (I \<union> {v}))) ` C"
      by (simp add: False sl Paw_cand_eq)
    show ?thesis unfolding Paw.step_unfold rhs using False by (auto simp: image_iff)
  qed
qed

lemma Paw_succs_step:
  assumes "Paw.well_formed c"
  shows "Paw.step c c' \<longleftrightarrow> c' \<in> set (Paw_succs c)"
proof -
  obtain P R I C where e: "c = (P, R, I, C)" by (rule cfg_obtain)
  have "Paw.well_formed (P, R, I, C)" using assms e by simp
  thus ?thesis unfolding e by (rule Paw_succs_iff)
qed

(* ========================================================================= *)
(* Part 3 : Bounded depth-first enumeration of the reachable configurations  *)
(* ========================================================================= *)

fun Paw_enum :: "nat \<Rightarrow> nat config \<Rightarrow> nat config list" where
  "Paw_enum 0 c = []"
| "Paw_enum (Suc n) c = c # concat (map (\<lambda>d. Paw_enum n d) (Paw_succs c))"

definition Paw_initial :: "nat config" where
  "Paw_initial = (Paw_V, [], {}, Paw_V)"

lemma Paw_initial_eq: "Paw_initial = Paw.\<Gamma>0"
  unfolding Paw_initial_def Paw.\<Gamma>0_def by simp

text \<open>
  The depth of the Paw configuration tree is at most 10 (three colour classes, each built
  with at most two ADD steps and one COMMIT).  The fuel 20 is therefore ample; the closure
  check Paw_reach_list_closed below would fail if it were not.
\<close>

definition Paw_reach_list :: "nat config list" where
  "Paw_reach_list = Paw_enum 20 Paw_initial"

lemma Paw_enum_reachable:
  assumes "Paw.well_formed c0" "c \<in> set (Paw_enum n c0)"
  shows "rtranclp Paw.step c0 c"
  using assms
proof (induction n arbitrary: c0)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have dec: "c = c0 \<or> (\<exists>d \<in> set (Paw_succs c0). c \<in> set (Paw_enum n d))"
    using Suc.prems(2) by auto
  show ?case
  proof (cases "c = c0")
    case True
    thus ?thesis by simp
  next
    case False
    then obtain d where d1: "d \<in> set (Paw_succs c0)" and d2: "c \<in> set (Paw_enum n d)"
      using dec by blast
    have st: "Paw.step c0 d" using Paw_succs_step[OF Suc.prems(1)] d1 by blast
    have wfd: "Paw.well_formed d" by (rule Paw.invariant_preservation[OF st Suc.prems(1)])
    have "rtranclp Paw.step d c" by (rule Suc.IH[OF wfd d2])
    with st show ?thesis by (rule converse_rtranclp_into_rtranclp)
  qed
qed

lemma Paw_reach_list_reachable:
  assumes "c \<in> set Paw_reach_list"
  shows "c \<in> Paw.ReachG"
proof -
  have wf0: "Paw.well_formed Paw_initial"
    unfolding Paw_initial_eq by (rule Paw.well_formed_\<Gamma>0)
  have "rtranclp Paw.step Paw_initial c"
    by (rule Paw_enum_reachable[OF wf0 assms[unfolded Paw_reach_list_def]])
  hence "rtranclp Paw.step Paw.\<Gamma>0 c" by (simp add: Paw_initial_eq)
  thus ?thesis unfolding Paw.ReachG_def by simp
qed

lemma Paw_list_wf:
  assumes "c \<in> set Paw_reach_list"
  shows "Paw.well_formed c"
  by (rule Paw.reachable_well_formed[OF Paw_reach_list_reachable[OF assms]])

text \<open>The two facts below are checked by evaluation.\<close>

lemma Paw_initial_in_list: "Paw_initial \<in> set Paw_reach_list"
  by eval

lemma Paw_reach_list_closed:
  "\<forall>c \<in> set Paw_reach_list. \<forall>d \<in> set (Paw_succs c). d \<in> set Paw_reach_list"
  by eval

theorem Paw_ReachG_eq: "Paw.ReachG = set Paw_reach_list"
proof
  show "Paw.ReachG \<subseteq> set Paw_reach_list"
  proof
    fix c assume "c \<in> Paw.ReachG"
    hence "rtranclp Paw.step Paw_initial c" by (simp add: Paw.ReachG_def Paw_initial_eq)
    thus "c \<in> set Paw_reach_list"
    proof (induction rule: rtranclp_induct)
      case base
      show ?case by (rule Paw_initial_in_list)
    next
      case (step y z)
      have wfy: "Paw.well_formed y" by (rule Paw_list_wf[OF step.IH])
      have "z \<in> set (Paw_succs y)" using Paw_succs_step[OF wfy] step.hyps(2) by blast
      thus ?case using Paw_reach_list_closed step.IH by blast
    qed
  qed
next
  show "set Paw_reach_list \<subseteq> Paw.ReachG"
    using Paw_reach_list_reachable by blast
qed

lemma Paw_mem_iff: "c \<in> Paw.ReachG \<longleftrightarrow> c \<in> set Paw_reach_list"
  unfolding Paw_ReachG_eq by simp

(* ========================================================================= *)
(* Part 4 : The numbers of Section 7                                         *)
(* ========================================================================= *)

lemma Paw_reach_length: "length Paw_reach_list = 37"
  by eval

lemma Paw_reach_distinct: "distinct Paw_reach_list"
  by eval

theorem Paw_card_ReachG: "card Paw.ReachG = 37"
  using Paw_ReachG_eq Paw_reach_distinct Paw_reach_length
  by (simp add: distinct_card)

lemma Paw_card_filter:
  assumes "\<And>c. c \<in> set Paw_reach_list \<Longrightarrow> Q c \<longleftrightarrow> Qe c"
  shows "card {c \<in> Paw.ReachG. Q c} = length (filter Qe Paw_reach_list)"
proof -
  have eq: "{c \<in> Paw.ReachG. Q c} = set (filter Qe Paw_reach_list)"
  proof (rule set_eqI)
    fix c
    show "c \<in> {c \<in> Paw.ReachG. Q c} \<longleftrightarrow> c \<in> set (filter Qe Paw_reach_list)"
    proof (cases "c \<in> set Paw_reach_list")
      case True
      thus ?thesis using assms[OF True] by (simp add: Paw_ReachG_eq)
    next
      case False
      thus ?thesis by (simp add: Paw_ReachG_eq)
    qed
  qed
  have dist: "distinct (filter Qe Paw_reach_list)"
    by (rule distinct_filter[OF Paw_reach_distinct])
  have "card (set (filter Qe Paw_reach_list)) = length (filter Qe Paw_reach_list)"
    by (rule distinct_card[OF dist])
  thus ?thesis by (simp only: eq)
qed

text \<open>Terminal configurations.\<close>

definition Paw_term_e :: "nat config \<Rightarrow> bool" where
  "Paw_term_e c = (case c of (P, R, I, C) \<Rightarrow> P = {} \<and> I = {} \<and> C = {})"

lemma Paw_term_iff: "Paw.is_terminal c = Paw_term_e c"
proof -
  obtain P R I C where e: "c = (P, R, I, C)" by (rule cfg_obtain)
  show ?thesis by (simp add: e Paw.is_terminal_def Paw_term_e_def)
qed

theorem Paw_terminal_count: "card {c \<in> Paw.ReachG. Paw.is_terminal c} = 6"
proof -
  have "card {c \<in> Paw.ReachG. Paw.is_terminal c}
        = length (filter Paw_term_e Paw_reach_list)"
    by (rule Paw_card_filter) (simp add: Paw_term_iff)
  also have "\<dots> = 6" by eval
  finally show ?thesis .
qed

lemma Paw_terminal_rsize:
  assumes "c \<in> Paw.ReachG" "Paw.is_terminal c"
  shows "Paw.rsize c = 3"
proof -
  have cl: "c \<in> set Paw_reach_list" using assms(1) Paw_mem_iff by blast
  have te: "Paw_term_e c" using assms(2) Paw_term_iff by blast
  have ev: "\<forall>c \<in> set Paw_reach_list. Paw_term_e c \<longrightarrow>
              (case c of (P, R, I, C) \<Rightarrow> length R = 3)"
    by eval
  have h: "case c of (P, R, I, C) \<Rightarrow> length R = 3" using ev cl te by blast
  obtain P R I C where e: "c = (P, R, I, C)" by (rule cfg_obtain)
  show ?thesis using h by (simp add: e Paw.rsize_simp)
qed

lemma Paw_terminal_sizes: "Paw.terminal_sizes = {3}"
proof -
  have ne: "{c \<in> Paw.ReachG. Paw.is_terminal c} \<noteq> {}"
  proof
    assume e: "{c \<in> Paw.ReachG. Paw.is_terminal c} = {}"
    have "card {c \<in> Paw.ReachG. Paw.is_terminal c} = 6" by (rule Paw_terminal_count)
    thus False using e by simp
  qed
  show ?thesis
    unfolding Paw.terminal_sizes_def
  proof (rule equalityI)
    show "Paw.rsize ` {c \<in> Paw.ReachG. Paw.is_terminal c} \<subseteq> {3}"
    proof (rule subsetI)
      fix x :: nat
      assume "x \<in> Paw.rsize ` {c \<in> Paw.ReachG. Paw.is_terminal c}"
      then obtain c where c1: "c \<in> Paw.ReachG" and c2: "Paw.is_terminal c"
        and x: "x = Paw.rsize c" by blast
      have "Paw.rsize c = 3" by (rule Paw_terminal_rsize[OF c1 c2])
      thus "x \<in> {3}" using x by simp
    qed
  next
    show "{3} \<subseteq> Paw.rsize ` {c \<in> Paw.ReachG. Paw.is_terminal c}"
    proof (rule subsetI)
      fix x :: nat
      assume x3: "x \<in> {3}"
      from ne obtain c where cS: "c \<in> {c \<in> Paw.ReachG. Paw.is_terminal c}" by blast
      hence c1: "c \<in> Paw.ReachG" and c2: "Paw.is_terminal c" by simp_all
      have r: "Paw.rsize c = 3" by (rule Paw_terminal_rsize[OF c1 c2])
      have "x = Paw.rsize c" using x3 r by simp
      thus "x \<in> Paw.rsize ` {c \<in> Paw.ReachG. Paw.is_terminal c}" using cS by blast
    qed
  qed
qed

text \<open>
  The chromatic number of the Paw graph, obtained from the mechanised optimality theorem
  (optimality_exhaustive) and the enumeration above; no brute-force colouring search is needed.
\<close>

theorem Paw_chromatic: "Paw.chromatic_num Paw_V = 3"
proof -
  have "Paw.chromatic_num Paw_V = Min Paw.terminal_sizes"
    by (rule Paw.optimality_exhaustive)
  also have "\<dots> = Min {3}" using Paw_terminal_sizes by simp
  also have "\<dots> = 3" by simp
  finally show ?thesis .
qed

text \<open>Dead ends.\<close>

definition Paw_dead_e :: "nat config \<Rightarrow> bool" where
  "Paw_dead_e c = (case c of (P, R, I, C) \<Rightarrow>
     C = {} \<and> I \<noteq> {} \<and> (\<exists>v \<in> P - I. \<forall>u \<in> I. (u, v) \<notin> Paw_E))"

lemma Paw_dead_iff: "Paw.is_dead_end c = Paw_dead_e c"
proof -
  obtain P R I C where e: "c = (P, R, I, C)" by (rule cfg_obtain)
  show ?thesis by (simp add: e Paw.is_dead_end_def Paw_dead_e_def)
qed

theorem Paw_dead_end_count: "card {c \<in> Paw.ReachG. Paw.is_dead_end c} = 2"
proof -
  have "card {c \<in> Paw.ReachG. Paw.is_dead_end c}
        = length (filter Paw_dead_e Paw_reach_list)"
    by (rule Paw_card_filter) (simp add: Paw_dead_iff)
  also have "\<dots> = 2" by eval
  finally show ?thesis .
qed

text \<open>Commit-ready configurations.\<close>

definition Paw_cr_e :: "nat config \<Rightarrow> bool" where
  "Paw_cr_e c = (case c of (P, R, I, C) \<Rightarrow> C = {} \<and> I \<noteq> {} \<and> Paw_max P I)"

lemma Paw_cr_iff:
  assumes "c \<in> set Paw_reach_list"
  shows "(case c of (P, R, I, C) \<Rightarrow> C = {} \<and> I \<noteq> {} \<and> Paw.is_maximal_indep P I)
         \<longleftrightarrow> Paw_cr_e c"
proof -
  obtain P R I C where e: "c = (P, R, I, C)" by (rule cfg_obtain)
  have wf: "Paw.well_formed (P, R, I, C)" using Paw_list_wf[OF assms] e by simp
  note p = Paw.wf_parts[OF wf]
  have mx: "Paw_max P I = Paw.is_maximal_indep P I" by (rule Paw_max_eq[OF p(3) p(2)])
  show ?thesis by (simp add: e Paw_cr_e_def mx)
qed

theorem Paw_commit_ready_count:
  "card {c \<in> Paw.ReachG. (case c of (P, R, I, C) \<Rightarrow>
      C = {} \<and> I \<noteq> {} \<and> Paw.is_maximal_indep P I)} = 15"
proof -
  have "card {c \<in> Paw.ReachG. (case c of (P, R, I, C) \<Rightarrow>
          C = {} \<and> I \<noteq> {} \<and> Paw.is_maximal_indep P I)}
        = length (filter Paw_cr_e Paw_reach_list)"
    by (rule Paw_card_filter) (rule Paw_cr_iff)
  also have "\<dots> = 15" by eval
  finally show ?thesis .
qed

(* ========================================================================= *)
(* Part 5 : The edges of the configuration tree                              *)
(* ========================================================================= *)

definition Paw_edges :: "(nat config \<times> nat config) list" where
  "Paw_edges = concat (map (\<lambda>p. map (\<lambda>d. (p, d)) (Paw_succs p)) Paw_reach_list)"

lemma Paw_edges_mem:
  "(c, d) \<in> set Paw_edges \<longleftrightarrow> c \<in> set Paw_reach_list \<and> d \<in> set (Paw_succs c)"
  unfolding Paw_edges_def by auto

lemma Paw_edges_distinct: "distinct Paw_edges"
  by eval

lemma Paw_edges_length: "length Paw_edges = 36"
  by eval

theorem Paw_edge_set:
  "{(c, d). c \<in> Paw.ReachG \<and> Paw.step c d} = set Paw_edges"
proof (rule set_eqI)
  fix e :: "nat config \<times> nat config"
  obtain c d where e: "e = (c, d)" by (cases e) auto
  have "e \<in> {(c, d). c \<in> Paw.ReachG \<and> Paw.step c d}
        \<longleftrightarrow> (c \<in> Paw.ReachG \<and> Paw.step c d)"
    by (simp add: e)
  also have "\<dots> \<longleftrightarrow> (c \<in> set Paw_reach_list \<and> d \<in> set (Paw_succs c))"
  proof (cases "c \<in> Paw.ReachG")
    case True
    have cl: "c \<in> set Paw_reach_list" using True Paw_mem_iff by blast
    have wf: "Paw.well_formed c" by (rule Paw.reachable_well_formed[OF True])
    show ?thesis using True cl Paw_succs_step[OF wf] by simp
  next
    case False
    hence "c \<notin> set Paw_reach_list" using Paw_mem_iff by blast
    thus ?thesis using False by simp
  qed
  also have "\<dots> \<longleftrightarrow> e \<in> set Paw_edges" by (simp add: e Paw_edges_mem)
  finally show "e \<in> {(c, d). c \<in> Paw.ReachG \<and> Paw.step c d} \<longleftrightarrow> e \<in> set Paw_edges" .
qed

theorem Paw_edge_count:
  "card {(c, d). c \<in> Paw.ReachG \<and> Paw.step c d} = 36"
  using Paw_edge_set Paw_edges_distinct Paw_edges_length
  by (simp add: distinct_card)

text \<open>Summary of the Section 7 claims, all stated about the mechanised ReachG.\<close>

theorem Paw_summary:
  "card Paw.ReachG = 37 \<and>
   card {(c, d). c \<in> Paw.ReachG \<and> Paw.step c d} = 36 \<and>
   card {c \<in> Paw.ReachG. Paw.is_terminal c} = 6 \<and>
   card {c \<in> Paw.ReachG. Paw.is_dead_end c} = 2 \<and>
   Paw.chromatic_num Paw_V = 3"
  using Paw_card_ReachG Paw_edge_count Paw_terminal_count Paw_dead_end_count Paw_chromatic
  by blast

end