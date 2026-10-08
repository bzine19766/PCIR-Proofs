theory MIS_Universal
  imports MIS_Soundness_Completeness
begin

context fixed_graph
begin

text \<open>This theory adds the universal counterparts of the existential completeness theorem:
  (1) universal termination and progress (every stuck configuration is terminal or a dead end),
  (2) finiteness of ReachG,
  (3) universal soundness and optimality of exhaustive search:
      min over reachable terminals of |R_f| = chromatic number,
  (4) completeness for every proper coloring (universal over colorings, existential over runs).
  Per-run optimality is false (see the path graph 0-1-2-3: first class {0,3} forces 3 colors).\<close>

definition rsize :: "'a config \<Rightarrow> nat" where
  "rsize \<Gamma> \<equiv> (case \<Gamma> of (_, R, _, _) \<Rightarrow> length R)"

lemma rsize_simp [simp]: "rsize (P, R, I, C) = length R"
  unfolding rsize_def by simp

definition is_dead_end :: "'a config \<Rightarrow> bool" where
  "is_dead_end \<Gamma> \<equiv> (case \<Gamma> of (P, R, I, C) \<Rightarrow>
      C = {} \<and> I \<noteq> {} \<and> (\<exists>v \<in> P - I. \<forall>u \<in> I. (u, v) \<notin> E))"

text \<open>Part 1: progress and universal termination.\<close>

lemma step_enabled:
  assumes "\<Gamma> \<rightarrow>G \<Gamma>'"
  shows "case \<Gamma> of (P, R, I, C) \<Rightarrow> C \<noteq> {} \<or> (I \<noteq> {} \<and> is_maximal_indep P I)"
  using assms by (induction rule: step.induct) auto

lemma terminal_stuck:
  assumes "is_terminal \<Gamma>"
  shows "\<not> (\<exists>\<Gamma>'. \<Gamma> \<rightarrow>G \<Gamma>')"
proof
  assume "\<exists>\<Gamma>'. \<Gamma> \<rightarrow>G \<Gamma>'"
  then obtain \<Gamma>' where st: "\<Gamma> \<rightarrow>G \<Gamma>'" by blast
  from step_enabled[OF st] assms show False
    by (cases \<Gamma>) (auto simp: is_terminal_def)
qed

lemma dead_end_stuck:
  assumes "is_dead_end \<Gamma>"
  shows "\<not> (\<exists>\<Gamma>'. \<Gamma> \<rightarrow>G \<Gamma>')"
proof
  assume "\<exists>\<Gamma>'. \<Gamma> \<rightarrow>G \<Gamma>'"
  then obtain \<Gamma>' where st: "\<Gamma> \<rightarrow>G \<Gamma>'" by blast
  from step_enabled[OF st] assms show False
    by (cases \<Gamma>) (auto simp: is_dead_end_def is_maximal_indep_def)
qed

lemma stuck_terminal_or_dead_end:
  assumes wf: "well_formed \<Gamma>" and stuck: "\<not> (\<exists>\<Gamma>'. \<Gamma> \<rightarrow>G \<Gamma>')"
  shows "is_terminal \<Gamma> \<or> is_dead_end \<Gamma>"
proof -
  obtain P R I C where \<Gamma>_eq: "\<Gamma> = (P, R, I, C)" by (cases \<Gamma>) auto
  have wf': "well_formed (P, R, I, C)" using wf \<Gamma>_eq by simp
  have stuck': "\<not> (\<exists>\<Gamma>'. (P, R, I, C) \<rightarrow>G \<Gamma>')" using stuck \<Gamma>_eq by simp
  note p = wf_parts[OF wf']
  have C_empty: "C = {}"
  proof (rule ccontr)
    assume "C \<noteq> {}"
    then obtain v where vC: "v \<in> C" by auto
    have "(P, R, I, C) \<rightarrow>G (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))"
      by (rule step.Add[OF vC refl])
    thus False using stuck' by blast
  qed
  have goal_disj: "is_terminal (P, R, I, C) \<or> is_dead_end (P, R, I, C)"
  proof -
    consider (Iempty) "I = {}"
      | (Imax) "I \<noteq> {}" "\<forall>v \<in> P - I. \<exists>u \<in> I. (u, v) \<in> E"
      | (Idead) "I \<noteq> {}" "\<not> (\<forall>v \<in> P - I. \<exists>u \<in> I. (u, v) \<in> E)"
      by blast
    thus ?thesis
    proof cases
      case Iempty
      have cs0: "candidate_set P I = {}" using p(4) C_empty by metis
      have "P = {}" using cs0 Iempty candidate_set_empty by simp
      hence "is_terminal (P, R, I, C)"
        unfolding is_terminal_def using Iempty C_empty by simp
      thus ?thesis by blast
    next
      case Imax
      have mx: "is_maximal_indep P I"
        unfolding is_maximal_indep_def using p(3) p(2) Imax(2) by blast
      have "(P, R, I, C) \<rightarrow>G (P - I, R @ [I], {}, P - I)"
        by (rule step.Commit[OF C_empty Imax(1) mx])
      hence False using stuck' by blast
      thus ?thesis by blast
    next
      case Idead
      have "\<exists>v \<in> P - I. \<forall>u \<in> I. (u, v) \<notin> E" using Idead(2) by blast
      hence "is_dead_end (P, R, I, C)"
        using C_empty Idead(1) by (auto simp: is_dead_end_def)
      thus ?thesis by blast
    qed
  qed
  thus ?thesis using \<Gamma>_eq by simp
qed

lemma \<rho>_lex:
  assumes "\<rho> \<Gamma>' < \<rho> \<Gamma>"
  shows "(\<rho> \<Gamma>', \<rho> \<Gamma>) \<in> less_than <*lex*> less_than"
proof -
  obtain a b where ab: "\<rho> \<Gamma>' = (a, b)" by (metis prod.exhaust)
  obtain c d where cd: "\<rho> \<Gamma> = (c, d)" by (metis prod.exhaust)
  show ?thesis using assms ab cd by (auto simp: in_lex_prod less_than_iff le_less)
qed

lemma wf_step_reverse: "wf {(\<Gamma>', \<Gamma>). \<Gamma> \<rightarrow>G \<Gamma>' \<and> well_formed \<Gamma>}"
proof (rule wf_subset)
  show "wf (inv_image (less_than <*lex*> less_than) \<rho>)"
    by (intro wf_inv_image wf_lex_prod wf_less_than)
next
  show "{(\<Gamma>', \<Gamma>). \<Gamma> \<rightarrow>G \<Gamma>' \<and> well_formed \<Gamma>} \<subseteq> inv_image (less_than <*lex*> less_than) \<rho>"
  proof (rule subsetI)
    fix x assume x: "x \<in> {(\<Gamma>', \<Gamma>). \<Gamma> \<rightarrow>G \<Gamma>' \<and> well_formed \<Gamma>}"
    obtain \<Gamma>' \<Gamma> where xeq: "x = (\<Gamma>', \<Gamma>)" by (metis prod.exhaust)
    from x xeq have st: "\<Gamma> \<rightarrow>G \<Gamma>'" and wfG: "well_formed \<Gamma>" by simp_all
    have "\<rho> \<Gamma>' < \<rho> \<Gamma>" by (rule \<rho>_strict_decrease[OF st wfG])
    hence "(\<rho> \<Gamma>', \<rho> \<Gamma>) \<in> less_than <*lex*> less_than" by (rule \<rho>_lex)
    thus "x \<in> inv_image (less_than <*lex*> less_than) \<rho>"
      using xeq by (simp add: inv_image_def)
  qed
qed

lemma reach_step:
  assumes "\<Gamma> \<in> ReachG" "\<Gamma> \<rightarrow>G \<Gamma>'"
  shows "\<Gamma>' \<in> ReachG"
proof -
  have "\<Gamma>0 \<rightarrow>G* \<Gamma>" using assms(1) unfolding ReachG_def by simp
  hence "\<Gamma>0 \<rightarrow>G* \<Gamma>'" using assms(2) by (rule rtranclp.rtrancl_into_rtrancl)
  thus ?thesis unfolding ReachG_def by simp
qed

theorem universal_termination:
  assumes "f 0 \<in> ReachG"
  shows "\<not> (\<forall>n. f n \<rightarrow>G f (Suc n))"
proof
  assume run: "\<forall>n. f n \<rightarrow>G f (Suc n)"
  have reach: "\<forall>n. f n \<in> ReachG"
  proof
    fix n show "f n \<in> ReachG"
    proof (induction n)
      case 0 show ?case using assms by simp
    next
      case (Suc n) show ?case by (rule reach_step[OF Suc.IH run[rule_format]])
    qed
  qed
  have chain: "\<forall>n. (f (Suc n), f n) \<in> {(\<Gamma>', \<Gamma>). \<Gamma> \<rightarrow>G \<Gamma>' \<and> well_formed \<Gamma>}"
  proof
    fix n
    have s: "f n \<rightarrow>G f (Suc n)" by (rule run[rule_format])
    have w: "well_formed (f n)" by (rule reachable_well_formed[OF reach[rule_format]])
    show "(f (Suc n), f n) \<in> {(\<Gamma>', \<Gamma>). \<Gamma> \<rightarrow>G \<Gamma>' \<and> well_formed \<Gamma>}"
      using s w by simp
  qed
  have nochain: "\<not> (\<exists>g. \<forall>i. (g (Suc i), g i) \<in> {(\<Gamma>', \<Gamma>). \<Gamma> \<rightarrow>G \<Gamma>' \<and> well_formed \<Gamma>})"
    using wf_step_reverse unfolding wf_iff_no_infinite_down_chain .
  have ex: "\<exists>g. \<forall>i. (g (Suc i), g i) \<in> {(\<Gamma>', \<Gamma>). \<Gamma> \<rightarrow>G \<Gamma>' \<and> well_formed \<Gamma>}"
    by (rule exI[of _ f]) (rule chain)
  show False by (rule notE[OF nochain ex])
qed

text \<open>Part 2: ReachG is finite.\<close>

lemma candidate_set_subset: "candidate_set P I \<subseteq> P"
  by (cases "I = {}") (auto simp: candidate_set_def)

definition lenbound :: "'a config \<Rightarrow> bool" where
  "lenbound \<Gamma> \<equiv> (case \<Gamma> of (P, R, I, C) \<Rightarrow> length R + card P \<le> card V)"

lemma lenbound_simp [simp]: "lenbound (P, R, I, C) \<longleftrightarrow> length R + card P \<le> card V"
  unfolding lenbound_def by simp

lemma len_commit:
  assumes wf: "well_formed (P, R, I, C)" and ne: "I \<noteq> {}" and lb: "length R + card P \<le> card V"
  shows "length (R @ [I]) + card (P - I) \<le> card V"
proof -
  note p = wf_parts[OF wf]
  have finP: "finite P" by (rule finite_sub[OF p(1)])
  have "P - I \<subset> P" using p(3) ne by auto
  hence lt: "card (P - I) < card P" by (rule psubset_card_mono[OF finP])
  have "length (R @ [I]) = length R + 1" by simp
  thus ?thesis using lb lt by arith
qed

lemma lenbound_step:
  assumes "\<Gamma> \<rightarrow>G \<Gamma>'" "well_formed \<Gamma>" "lenbound \<Gamma>"
  shows "lenbound \<Gamma>'"
  using assms
proof (induction rule: step.induct)
  case Add
  show ?case using Add.prems by simp
next
  case Commit
  show ?case
    unfolding lenbound_simp
    by (rule len_commit[OF Commit.prems(1) Commit.hyps(2)]) (use Commit.prems(2) in simp)
qed

lemma reach_lenbound:
  assumes "\<Gamma> \<in> ReachG"
  shows "lenbound \<Gamma>"
proof -
  from assms have "\<Gamma>0 \<rightarrow>G* \<Gamma>" unfolding ReachG_def by simp
  thus ?thesis
  proof (induction rule: rtranclp_induct)
    case base
    show ?case unfolding \<Gamma>0_def by simp
  next
    case (step y z)
    have yR: "y \<in> ReachG" using step.hyps(1) unfolding ReachG_def by simp
    show ?case
      by (rule lenbound_step[OF step.hyps(2) reachable_well_formed[OF yR] step.IH])
  qed
qed

theorem finite_ReachG: "finite ReachG"
proof -
  have fPow: "finite (Pow V)" using finite_V by simp
  have fin_Rs: "finite {R. set R \<subseteq> Pow V \<and> length R \<le> card V}"
    by (rule finite_lists_length_le[OF fPow])
  have fin_prod: "finite (Pow V \<times> ({R. set R \<subseteq> Pow V \<and> length R \<le> card V} \<times> (Pow V \<times> Pow V)))"
    by (intro finite_cartesian_product fPow fin_Rs)
  have sub: "ReachG \<subseteq> Pow V \<times> ({R. set R \<subseteq> Pow V \<and> length R \<le> card V} \<times> (Pow V \<times> Pow V))"
  proof (rule subsetI)
    fix \<Gamma> assume \<Gamma>_in: "\<Gamma> \<in> ReachG"
    obtain P R I C where \<Gamma>_eq: "\<Gamma> = (P, R, I, C)" by (cases \<Gamma>) auto
    have wf: "well_formed (P, R, I, C)" using reachable_well_formed[OF \<Gamma>_in] \<Gamma>_eq by simp
    note p = wf_parts[OF wf]
    have lenb: "length R + card P \<le> card V"
      using reach_lenbound[OF \<Gamma>_in] \<Gamma>_eq by simp
    have PV: "P \<in> Pow V" using p(1) by simp
    have IV: "I \<in> Pow V" using p(3) p(1) by auto
    have CP: "C \<subseteq> P" using p(4) candidate_set_subset by simp
    have CV: "C \<in> Pow V" using CP p(1) by auto
    have Rsub: "set R \<subseteq> Pow V" using p(5) unfolding is_indep_def by auto
    have Rlen: "length R \<le> card V" using lenb by arith
    show "\<Gamma> \<in> Pow V \<times> ({R. set R \<subseteq> Pow V \<and> length R \<le> card V} \<times> (Pow V \<times> Pow V))"
      using \<Gamma>_eq PV IV CV Rsub Rlen by auto
  qed
  show ?thesis by (rule finite_subset[OF sub fin_prod])
qed

text \<open>Part 3: universal soundness and optimality of exhaustive search.\<close>

definition terminal_sizes :: "nat set" where
  "terminal_sizes \<equiv> rsize ` {\<Gamma> \<in> ReachG. is_terminal \<Gamma>}"

theorem universal_lower_bound:
  assumes "\<Gamma>_f \<in> ReachG" "is_terminal \<Gamma>_f"
  shows "chromatic_num V \<le> rsize \<Gamma>_f"
proof (rule theorem_8_1_Soundness[OF assms])
  fix R_f assume eq: "\<Gamma>_f = ({}, R_f, {}, {})" and val: "is_valid_coloring V R_f"
  show ?thesis using chromatic_num_le[OF val] unfolding eq by simp
qed

theorem optimality_exhaustive:
  "chromatic_num V = Min terminal_sizes"
proof -
  have fin0: "finite {\<Gamma> \<in> ReachG. is_terminal \<Gamma>}"
    by (rule finite_subset[OF _ finite_ReachG]) auto
  hence fin: "finite terminal_sizes" unfolding terminal_sizes_def by (rule finite_imageI)
  have lb: "\<And>n. n \<in> terminal_sizes \<Longrightarrow> chromatic_num V \<le> n"
  proof -
    fix n assume "n \<in> terminal_sizes"
    then obtain \<Gamma> where \<Gamma>1: "\<Gamma> \<in> ReachG" and \<Gamma>2: "is_terminal \<Gamma>" and \<Gamma>3: "n = rsize \<Gamma>"
      unfolding terminal_sizes_def by auto
    have "chromatic_num V \<le> rsize \<Gamma>" by (rule universal_lower_bound[OF \<Gamma>1 \<Gamma>2])
    thus "chromatic_num V \<le> n" using \<Gamma>3 by simp
  qed
  from corollary_8_1_Global_Completeness show ?thesis
  proof (rule bexE)
    fix \<Gamma>_f
    assume r: "\<Gamma>_f \<in> ReachG"
      and c: "is_terminal \<Gamma>_f \<and>
              (case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = chromatic_num V)"
    have t: "is_terminal \<Gamma>_f" using c by (rule conjunct1)
    have l: "(case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = chromatic_num V)"
      using c by (rule conjunct2)
    have eq: "rsize \<Gamma>_f = chromatic_num V" using l by (cases \<Gamma>_f) simp
    have mem: "chromatic_num V \<in> terminal_sizes"
      unfolding terminal_sizes_def
      by (rule image_eqI[where x = \<Gamma>_f]) (use r t eq in auto)
    show ?thesis by (rule sym[OF Min_eqI[OF fin lb mem]])
  qed
qed

text \<open>Part 4: completeness for every proper coloring.\<close>

lemma commit_phase:
  assumes reach: "(P, R, {}, P) \<in> ReachG" and ne: "P \<noteq> {}" and M_in: "M \<in> MIS_P P"
  shows "reachable (P, R, {}, P) (P - M, R @ [M], {}, P - M) \<and>
         (P - M, R @ [M], {}, P - M) \<in> ReachG \<and> card (P - M) < card P"
proof -
  have wf: "well_formed (P, R, {}, P)" by (rule reachable_well_formed[OF reach])
  have P_sub: "P \<subseteq> V" using wf unfolding well_formed_simp by blast
  have M_is_max: "is_maximal_indep P M" using M_in unfolding MIS_P_def by auto
  have M_sub_P: "M \<subseteq> P" using M_in unfolding MIS_P_def by auto
  have M_ne: "M \<noteq> {}"
  proof
    assume "M = {}"
    from ne obtain v where "v \<in> P" by auto
    hence "v \<in> P - M" using \<open>M = {}\<close> by simp
    hence "\<exists>u \<in> M. (u, v) \<in> E" using M_is_max unfolding is_maximal_indep_def by blast
    thus False using \<open>M = {}\<close> by simp
  qed
  have bij: "bij_betw (\<Phi> P R) (MIS_P P) (commit_ready_states P R)"
    by (rule theorem_6_1_MIS_Commit_Ready_Bijection[OF P_sub ne])
  have "\<Phi> P R M \<in> commit_ready_states P R" by (rule bij_betw_apply[OF bij M_in])
  hence "(P, R, M, {}) \<in> commit_ready_states P R" unfolding \<Phi>_def by simp
  then obtain xs where path: "add_path_seq P R xs M {}"
    unfolding commit_ready_states_def by auto
  have to_commit: "reachable (P, R, {}, P) (P, R, M, {})"
    by (rule add_path_seq_imp_reachable[OF path])
  have step_c: "(P, R, M, {}) \<rightarrow>G (P - M, R @ [M], {}, P - M)"
    by (rule step.Commit[OF refl M_ne M_is_max])
  have reach_next: "reachable (P, R, {}, P) (P - M, R @ [M], {}, P - M)"
    using to_commit step_c by (rule rtranclp.rtrancl_into_rtrancl)
  have next_reach: "(P - M, R @ [M], {}, P - M) \<in> ReachG"
  proof -
    have a: "\<Gamma>0 \<rightarrow>G* (P, R, {}, P)" using reach unfolding ReachG_def by simp
    have "\<Gamma>0 \<rightarrow>G* (P - M, R @ [M], {}, P - M)" using a reach_next by (rule rtranclp_trans)
    thus ?thesis unfolding ReachG_def by simp
  qed
  have fin: "finite P" by (rule finite_sub[OF P_sub])
  have "P - M \<subset> P" using M_ne M_sub_P by auto
  hence lt: "card (P - M) < card P" by (rule psubset_card_mono[OF fin])
  show ?thesis using reach_next next_reach lt by blast
qed

lemma completeness_colorings_aux:
  "\<forall>P R Rs. card P = n \<longrightarrow> (P, R, {}, P) \<in> ReachG \<longrightarrow> is_valid_coloring P Rs \<longrightarrow>
     (\<exists>\<Gamma>_f \<in> ReachG. reachable (P, R, {}, P) \<Gamma>_f \<and> is_terminal \<Gamma>_f \<and>
        rsize \<Gamma>_f \<le> length R + length Rs)"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (intro allI impI)
    fix P R Rs
    assume cardP: "card P = n" and reach: "(P, R, {}, P) \<in> ReachG"
      and val: "is_valid_coloring P Rs"
    have ih: "\<And>P' R' Rs'. card P' < n \<Longrightarrow> (P', R', {}, P') \<in> ReachG \<Longrightarrow>
        is_valid_coloring P' Rs' \<Longrightarrow>
        (\<exists>\<Gamma>_f \<in> ReachG. reachable (P', R', {}, P') \<Gamma>_f \<and> is_terminal \<Gamma>_f \<and>
           rsize \<Gamma>_f \<le> length R' + length Rs')"
    proof -
      fix P' R' Rs' assume lt: "card P' < n" and r: "(P', R', {}, P') \<in> ReachG"
        and v: "is_valid_coloring P' Rs'"
      from less.IH[OF lt]
      have "\<forall>Q S T. card Q = card P' \<longrightarrow> (Q, S, {}, Q) \<in> ReachG \<longrightarrow> is_valid_coloring Q T \<longrightarrow>
              (\<exists>\<Gamma>_f \<in> ReachG. reachable (Q, S, {}, Q) \<Gamma>_f \<and> is_terminal \<Gamma>_f \<and>
                 rsize \<Gamma>_f \<le> length S + length T)" .
      thus "\<exists>\<Gamma>_f \<in> ReachG. reachable (P', R', {}, P') \<Gamma>_f \<and> is_terminal \<Gamma>_f \<and>
              rsize \<Gamma>_f \<le> length R' + length Rs'"
        using r v by blast
    qed
    consider (empty) "P = {}" | (nonempty) "P \<noteq> {}" by blast
    thus "\<exists>\<Gamma>_f \<in> ReachG. reachable (P, R, {}, P) \<Gamma>_f \<and> is_terminal \<Gamma>_f \<and>
            rsize \<Gamma>_f \<le> length R + length Rs"
    proof cases
      case empty
      have is_term: "is_terminal (P, R, {}, P)"
        unfolding is_terminal_def using empty by simp
      have sz: "rsize (P, R, {}, P) \<le> length R + length Rs" by simp
      show ?thesis
        by (rule bexI[of _ "(P, R, {}, P)"])
           (use reach is_term sz in \<open>auto intro: rtranclp.rtrancl_refl\<close>)
    next
      case nonempty
      have wf: "well_formed (P, R, {}, P)" by (rule reachable_well_formed[OF reach])
      have P_sub: "P \<subseteq> V" using wf unfolding well_formed_simp by blast
      have un: "\<Union> (set Rs) = P" using val unfolding is_valid_coloring_def by blast
      have Rs_ne: "Rs \<noteq> []"
      proof
        assume "Rs = []"
        hence "P = {}" using un by auto
        thus False using nonempty by simp
      qed
      obtain Rs' M_last where Rs_eq: "Rs = Rs' @ [M_last]"
      proof (cases Rs rule: rev_cases)
        case Nil
        thus ?thesis using Rs_ne by simp
      next
        case (snoc ys y)
        thus ?thesis by (rule that)
      qed
      have val_snoc: "is_valid_coloring P (Rs' @ [M_last])" using val Rs_eq by simp
      have val': "is_valid_coloring (P - M_last) Rs'"
        by (rule valid_coloring_snoc_split[OF val_snoc])
      have M_last_mem: "M_last \<in> set Rs" using Rs_eq by simp
      have M_last_indep: "is_indep M_last"
        using val M_last_mem unfolding is_valid_coloring_def by blast
      have M_last_sub: "M_last \<subseteq> P"
      proof -
        have "M_last \<subseteq> \<Union> (set Rs)" using M_last_mem by (rule Union_upper)
        thus ?thesis using un by simp
      qed
      obtain M where M_in: "M \<in> MIS_P P" and M_ext: "M_last \<subseteq> M"
        using independent_set_extension[OF P_sub M_last_sub M_last_indep] by blast
      define Rf where "Rf = filter (\<lambda>C. C - M \<noteq> {}) Rs'"
      have v2: "is_valid_coloring ((P - M_last) - M) (map (\<lambda>C. C - M) Rf)"
        by (rule valid_coloring_remove[OF val' Rf_def])
      have eqPM: "(P - M_last) - M = P - M" using M_ext by auto
      have v2': "is_valid_coloring (P - M) (map (\<lambda>C. C - M) Rf)" using v2 eqPM by simp
      have len2: "length (map (\<lambda>C. C - M) Rf) \<le> length Rs'"
        by (simp add: Rf_def length_filter_le)
      have cp: "reachable (P, R, {}, P) (P - M, R @ [M], {}, P - M) \<and>
                (P - M, R @ [M], {}, P - M) \<in> ReachG \<and> card (P - M) < card P"
        by (rule commit_phase[OF reach nonempty M_in])
      have reach_next: "reachable (P, R, {}, P) (P - M, R @ [M], {}, P - M)"
        using cp by blast
      have next_reach: "(P - M, R @ [M], {}, P - M) \<in> ReachG" using cp by blast
      have lt0: "card (P - M) < card P" using cp by blast
      have lt: "card (P - M) < n" using lt0 cardP by simp
      from ih[OF lt next_reach v2'] obtain \<Gamma>_f where
        \<Gamma>_reach: "\<Gamma>_f \<in> ReachG"
        and \<Gamma>_sub: "reachable (P - M, R @ [M], {}, P - M) \<Gamma>_f"
        and \<Gamma>_term: "is_terminal \<Gamma>_f"
        and \<Gamma>_size: "rsize \<Gamma>_f \<le> length (R @ [M]) + length (map (\<lambda>C. C - M) Rf)"
        by blast
      have \<Gamma>_from_P: "reachable (P, R, {}, P) \<Gamma>_f"
        using reach_next \<Gamma>_sub by (rule rtranclp_trans)
      have lenRs: "length Rs = length Rs' + 1" using Rs_eq by simp
      have lenRM: "length (R @ [M]) = length R + 1" by simp
      have final_size: "rsize \<Gamma>_f \<le> length R + length Rs"
        using \<Gamma>_size len2 lenRs lenRM by arith
      show ?thesis
        by (rule bexI[of _ \<Gamma>_f]) (use \<Gamma>_reach \<Gamma>_from_P \<Gamma>_term final_size in auto)
    qed
  qed
qed

theorem completeness_for_colorings:
  assumes "(P, R, {}, P) \<in> ReachG" "is_valid_coloring P Rs"
  shows "\<exists>\<Gamma>_f \<in> ReachG. reachable (P, R, {}, P) \<Gamma>_f \<and> is_terminal \<Gamma>_f \<and>
           rsize \<Gamma>_f \<le> length R + length Rs"
  using completeness_colorings_aux[of "card P"] assms by blast

corollary global_completeness_for_colorings:
  assumes "is_valid_coloring V Rs"
  shows "\<exists>\<Gamma>_f \<in> ReachG. is_terminal \<Gamma>_f \<and> rsize \<Gamma>_f \<le> length Rs"
proof -
  have \<Gamma>0_reach: "(V, [], {}, V) \<in> ReachG"
    using \<Gamma>0_def by (auto simp: ReachG_def intro: rtranclp.rtrancl_refl)
  from completeness_for_colorings[OF \<Gamma>0_reach assms]
  show ?thesis by auto
qed

end
end
