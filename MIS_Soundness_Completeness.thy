theory MIS_Soundness_Completeness
  imports MIS_Commit_Bijection
begin

context fixed_graph
begin

text \<open>Set-based colorings: classes are distinct, non-empty, independent,
  pairwise disjoint, and cover P. No index reasoning is needed for map/filter/append.\<close>

definition is_valid_coloring :: "'a set \<Rightarrow> 'a set list \<Rightarrow> bool" where
  "is_valid_coloring P R \<equiv>
    distinct R \<and>
    (\<forall>m \<in> set R. is_indep m \<and> m \<noteq> {}) \<and>
    \<Union> (set R) = P \<and>
    (\<forall>A \<in> set R. \<forall>B \<in> set R. A \<noteq> B \<longrightarrow> A \<inter> B = {})"

definition chromatic_num :: "'a set \<Rightarrow> nat" where
  "chromatic_num P \<equiv> LEAST n. \<exists>R. is_valid_coloring P R \<and> length R = n"

definition is_terminal :: "'a config \<Rightarrow> bool" where
  "is_terminal \<Gamma> \<equiv> (case \<Gamma> of (P, R, I, C) \<Rightarrow> P = {} \<and> I = {} \<and> C = {})"

lemma disj_notin: "A \<inter> B = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> B"
  by (metis Int_iff equals0D)

text \<open>Bridge from the index-based disjointness in well_formed to the set-based one.\<close>

lemma index_disjoint_distinct:
  assumes ne: "\<forall>m \<in> set R. m \<noteq> {}"
      and disj: "\<forall>i < length R. \<forall>j < length R. i \<noteq> j \<longrightarrow> R ! i \<inter> R ! j = {}"
  shows "distinct R"
  unfolding distinct_conv_nth
proof (intro allI impI)
  fix i j assume i: "i < length R" and j: "j < length R" and ij: "i \<noteq> j"
  have inter: "R ! i \<inter> R ! j = {}" using disj i j ij by blast
  have "R ! i \<in> set R" using i by (rule nth_mem)
  hence ne_i: "R ! i \<noteq> {}" using ne by blast
  show "R ! i \<noteq> R ! j"
  proof
    assume eq: "R ! i = R ! j"
    have "R ! i \<inter> R ! i = {}" using inter eq by metis
    hence "R ! i = {}" by simp
    thus False using ne_i by simp
  qed
qed

lemma index_disjoint_set_disjoint:
  assumes disj: "\<forall>i < length R. \<forall>j < length R. i \<noteq> j \<longrightarrow> R ! i \<inter> R ! j = {}"
  shows "\<forall>A \<in> set R. \<forall>B \<in> set R. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
proof (intro ballI impI)
  fix A B assume "A \<in> set R" "B \<in> set R" "A \<noteq> B"
  from \<open>A \<in> set R\<close> obtain i where i: "i < length R" "R ! i = A"
    by (auto simp: in_set_conv_nth)
  from \<open>B \<in> set R\<close> obtain j where j: "j < length R" "R ! j = B"
    by (auto simp: in_set_conv_nth)
  have "i \<noteq> j" using \<open>A \<noteq> B\<close> i j by auto
  hence "R ! i \<inter> R ! j = {}" using disj i(1) j(1) by blast
  thus "A \<inter> B = {}" using i(2) j(2) by simp
qed

text \<open>Appending / removing the last class.\<close>

lemma valid_coloring_snoc_split:
  assumes "is_valid_coloring P (R @ [M])"
  shows "is_valid_coloring (P - M) R"
proof -
  from assms have dist: "distinct (R @ [M])"
    and cls: "\<forall>m \<in> set (R @ [M]). is_indep m \<and> m \<noteq> {}"
    and un: "\<Union> (set (R @ [M])) = P"
    and dj: "\<forall>A \<in> set (R @ [M]). \<forall>B \<in> set (R @ [M]). A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    unfolding is_valid_coloring_def by auto
  have dR: "distinct R" and M_notin: "M \<notin> set R" using dist by auto
  have disjM: "\<And>A. A \<in> set R \<Longrightarrow> A \<inter> M = {}"
  proof -
    fix A assume A: "A \<in> set R"
    hence "A \<noteq> M" using M_notin by auto
    thus "A \<inter> M = {}" using dj A by auto
  qed
  have cls_R: "\<forall>m \<in> set R. is_indep m \<and> m \<noteq> {}" using cls by auto
  have dj_R: "\<forall>A \<in> set R. \<forall>B \<in> set R. A \<noteq> B \<longrightarrow> A \<inter> B = {}" using dj by auto
  have un_R: "\<Union> (set R) = P - M"
  proof
    show "\<Union> (set R) \<subseteq> P - M"
    proof
      fix x assume "x \<in> \<Union> (set R)"
      then obtain A where A: "A \<in> set R" "x \<in> A" by auto
      have xin: "x \<in> \<Union> (set (R @ [M]))" using A by auto
      have xP: "x \<in> P" by (rule rev_subsetD[OF xin equalityD1[OF un]])
      have "x \<notin> M" using disj_notin[OF disjM[OF A(1)] A(2)] .
      thus "x \<in> P - M" using xP by simp
    qed
  next
    show "P - M \<subseteq> \<Union> (set R)"
    proof
      fix x assume xPM: "x \<in> P - M"
      hence "x \<in> \<Union> (set (R @ [M]))" using un by simp
      then obtain A where A: "A \<in> set (R @ [M])" "x \<in> A" by auto
      have "A \<noteq> M" using A(2) xPM by auto
      hence "A \<in> set R" using A(1) by auto
      thus "x \<in> \<Union> (set R)" using A(2) by auto
    qed
  qed
  show ?thesis
    unfolding is_valid_coloring_def using dR cls_R un_R dj_R by blast
qed

lemma valid_coloring_snoc:
  assumes "is_valid_coloring (P - M) R" "is_indep M" "M \<noteq> {}" "M \<subseteq> P"
  shows "is_valid_coloring P (R @ [M])"
proof -
  from assms(1) have dR: "distinct R"
    and cls: "\<forall>m \<in> set R. is_indep m \<and> m \<noteq> {}"
    and un: "\<Union> (set R) = P - M"
    and dj: "\<forall>A \<in> set R. \<forall>B \<in> set R. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    unfolding is_valid_coloring_def by auto
  have sub: "\<And>A. A \<in> set R \<Longrightarrow> A \<subseteq> P - M"
  proof -
    fix A assume "A \<in> set R"
    hence "A \<subseteq> \<Union> (set R)" by (rule Union_upper)
    thus "A \<subseteq> P - M" using un by simp
  qed
  have disjM: "\<And>A. A \<in> set R \<Longrightarrow> A \<inter> M = {}"
  proof (rule Int_emptyI)
    fix A x assume "A \<in> set R" "x \<in> A" "x \<in> M"
    hence "x \<in> P - M" using sub by auto
    thus False using \<open>x \<in> M\<close> by simp
  qed
  have M_notin: "M \<notin> set R"
  proof
    assume "M \<in> set R"
    hence "M \<inter> M = {}" using disjM by blast
    thus False using assms(3) by simp
  qed
  have dist': "distinct (R @ [M])" using dR M_notin by simp
  have cls': "\<forall>m \<in> set (R @ [M]). is_indep m \<and> m \<noteq> {}" using cls assms(2,3) by auto
  have un': "\<Union> (set (R @ [M])) = P"
  proof -
    have "\<Union> (set (R @ [M])) = \<Union> (set R) \<union> M" by auto
    also have "... = (P - M) \<union> M" using un by simp
    also have "... = P" using assms(4) by auto
    finally show ?thesis .
  qed
  have dj': "\<forall>A \<in> set (R @ [M]). \<forall>B \<in> set (R @ [M]). A \<noteq> B \<longrightarrow> A \<inter> B = {}"
  proof (intro ballI impI)
    fix A B assume A: "A \<in> set (R @ [M])" and B: "B \<in> set (R @ [M])" and AB: "A \<noteq> B"
    show "A \<inter> B = {}"
    proof (cases "A = M")
      case True
      hence "B \<in> set R" using B AB by auto
      hence "B \<inter> M = {}" by (rule disjM)
      thus ?thesis using True by (simp add: Int_commute)
    next
      case False
      hence A_R: "A \<in> set R" using A by auto
      show ?thesis
      proof (cases "B = M")
        case True
        thus ?thesis using disjM[OF A_R] by simp
      next
        case False
        hence "B \<in> set R" using B by auto
        thus ?thesis using dj A_R AB by blast
      qed
    qed
  qed
  show ?thesis unfolding is_valid_coloring_def using dist' cls' un' dj' by blast
qed

text \<open>Removing a vertex set S from a coloring: map (C goes to C - S), drop empties.\<close>

lemma valid_coloring_remove:
  assumes valid: "is_valid_coloring Q Rs"
      and Rf_def: "Rf = filter (\<lambda>C. C - S \<noteq> {}) Rs"
  shows "is_valid_coloring (Q - S) (map (\<lambda>C. C - S) Rf)"
proof -
  from valid have dist: "distinct Rs"
    and cls: "\<forall>m \<in> set Rs. is_indep m \<and> m \<noteq> {}"
    and un: "\<Union> (set Rs) = Q"
    and dj: "\<forall>A \<in> set Rs. \<forall>B \<in> set Rs. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    unfolding is_valid_coloring_def by auto
  have dRf: "distinct Rf" using dist Rf_def by simp
  have setRf: "set Rf = {C \<in> set Rs. C - S \<noteq> {}}" using Rf_def by simp
  have un_sub: "\<And>C. C \<in> set Rs \<Longrightarrow> C \<subseteq> Q"
  proof -
    fix C assume "C \<in> set Rs"
    hence "C \<subseteq> \<Union> (set Rs)" by (rule Union_upper)
    thus "C \<subseteq> Q" using un by simp
  qed
  have inj: "inj_on (\<lambda>C. C - S) (set Rf)"
  proof (rule inj_onI)
    fix A B assume A: "A \<in> set Rf" and B: "B \<in> set Rf" and eq: "A - S = B - S"
    from A setRf have A': "A \<in> set Rs" "A - S \<noteq> {}" by auto
    from B setRf have B': "B \<in> set Rs" by auto
    show "A = B"
    proof (rule ccontr)
      assume "A \<noteq> B"
      hence AB: "A \<inter> B = {}" using dj A'(1) B'(1) by blast
      have "A - S \<subseteq> A" by auto
      moreover have "A - S \<subseteq> B" using eq by auto
      ultimately have "A - S \<subseteq> A \<inter> B" by blast
      hence "A - S = {}" using AB by auto
      thus False using A'(2) by simp
    qed
  qed
  have dist': "distinct (map (\<lambda>C. C - S) Rf)" using dRf inj by (simp add: distinct_map)
  have cls': "\<forall>m \<in> set (map (\<lambda>C. C - S) Rf). is_indep m \<and> m \<noteq> {}"
  proof
    fix m assume "m \<in> set (map (\<lambda>C. C - S) Rf)"
    then obtain C where C: "C \<in> set Rf" and m: "m = C - S" by auto
    from C setRf have C': "C \<in> set Rs" "C - S \<noteq> {}" by auto
    have "is_indep C" using cls C'(1) by blast
    hence "is_indep (C - S)" unfolding is_indep_def by auto
    thus "is_indep m \<and> m \<noteq> {}" using m C'(2) by simp
  qed
  have un': "\<Union> (set (map (\<lambda>C. C - S) Rf)) = Q - S"
  proof
    show "\<Union> (set (map (\<lambda>C. C - S) Rf)) \<subseteq> Q - S"
    proof
      fix x assume "x \<in> \<Union> (set (map (\<lambda>C. C - S) Rf))"
      then obtain C where C: "C \<in> set Rf" and xC: "x \<in> C - S" by auto
      have "C \<in> set Rs" using C setRf by auto
      hence "C \<subseteq> Q" by (rule un_sub)
      thus "x \<in> Q - S" using xC by auto
    qed
  next
    show "Q - S \<subseteq> \<Union> (set (map (\<lambda>C. C - S) Rf))"
    proof
      fix x assume xQ: "x \<in> Q - S"
      hence "x \<in> \<Union> (set Rs)" using un by simp
      then obtain C where C: "C \<in> set Rs" and xC: "x \<in> C" by auto
      have xCS: "x \<in> C - S" using xC xQ by auto
      hence "C - S \<noteq> {}" by auto
      hence "C \<in> set Rf" using C setRf by auto
      thus "x \<in> \<Union> (set (map (\<lambda>C. C - S) Rf))" using xCS by auto
    qed
  qed
  have dj': "\<forall>A \<in> set (map (\<lambda>C. C - S) Rf). \<forall>B \<in> set (map (\<lambda>C. C - S) Rf).
              A \<noteq> B \<longrightarrow> A \<inter> B = {}"
  proof (intro ballI impI)
    fix A B
    assume "A \<in> set (map (\<lambda>C. C - S) Rf)" "B \<in> set (map (\<lambda>C. C - S) Rf)" "A \<noteq> B"
    then obtain C1 C2 where C1: "C1 \<in> set Rf" "A = C1 - S"
      and C2: "C2 \<in> set Rf" "B = C2 - S" by auto
    have ne: "C1 \<noteq> C2" using \<open>A \<noteq> B\<close> C1 C2 by auto
    have "C1 \<in> set Rs" "C2 \<in> set Rs" using C1(1) C2(1) setRf by auto
    hence "C1 \<inter> C2 = {}" using dj ne by blast
    show "A \<inter> B = {}"
      unfolding C1(2) C2(2)
    proof (rule Int_emptyI)
      fix x assume "x \<in> C1 - S" "x \<in> C2 - S"
      hence "x \<in> C1" "x \<in> C2" by auto
      thus False using disj_notin[OF \<open>C1 \<inter> C2 = {}\<close>] by blast
    qed
  qed
  show ?thesis
    unfolding is_valid_coloring_def using dist' cls' un' dj' by blast
qed

lemma valid_coloring_exists:
  assumes "P \<subseteq> V"
  shows "\<exists>R. is_valid_coloring P R"
proof -
  have key: "\<And>Q. finite Q \<Longrightarrow> Q \<subseteq> V \<Longrightarrow> \<exists>R. is_valid_coloring Q R"
  proof -
    fix Q :: "'a set" assume "finite Q"
    thus "Q \<subseteq> V \<Longrightarrow> \<exists>R. is_valid_coloring Q R"
    proof (induction rule: finite_induct)
      case empty
      have "is_valid_coloring {} []" unfolding is_valid_coloring_def by simp
      thus ?case by blast
    next
      case (insert x S)
      from insert.prems have xV: "x \<in> V" and SV: "S \<subseteq> V" by auto
      from insert.IH[OF SV] obtain R where R_val: "is_valid_coloring S R" by blast
      have eq: "insert x S - {x} = S" using insert.hyps(2) by auto
      have R_val': "is_valid_coloring (insert x S - {x}) R" using R_val eq by simp
      have indep_x: "is_indep {x}" using xV unfolding is_indep_def by auto
      have "is_valid_coloring (insert x S) (R @ [{x}])"
        by (rule valid_coloring_snoc[OF R_val' indep_x]) auto
      thus ?case by blast
    qed
  qed
  show ?thesis using key[OF finite_subset[OF assms finite_V] assms] .
qed

lemma chromatic_num_le:
  assumes "is_valid_coloring P R"
  shows "chromatic_num P \<le> length R"
proof -
  have ex: "\<exists>R'. is_valid_coloring P R' \<and> length R' = length R" using assms by blast
  show ?thesis unfolding chromatic_num_def
    by (rule Least_le[of "\<lambda>n. \<exists>R'. is_valid_coloring P R' \<and> length R' = n" "length R"])
       (rule ex)
qed

lemma chromatic_num_attained:
  assumes "P \<subseteq> V"
  shows "\<exists>R. is_valid_coloring P R \<and> length R = chromatic_num P"
proof -
  obtain R0 where "is_valid_coloring P R0" using valid_coloring_exists[OF assms] by blast
  hence ex: "\<exists>n. \<exists>R. is_valid_coloring P R \<and> length R = n" by blast
  from LeastI_ex[OF ex] show ?thesis unfolding chromatic_num_def by blast
qed

lemma chromatic_num_empty: "chromatic_num {} = 0"
proof -
  have "is_valid_coloring {} []" unfolding is_valid_coloring_def by simp
  from chromatic_num_le[OF this] show ?thesis by simp
qed

lemma chromatic_num_remove_le:
  assumes "is_valid_coloring Q Rs"
  shows "chromatic_num (Q - S) \<le> length Rs"
proof -
  define Rf where "Rf = filter (\<lambda>C. C - S \<noteq> {}) Rs"
  have v: "is_valid_coloring (Q - S) (map (\<lambda>C. C - S) Rf)"
    by (rule valid_coloring_remove[OF assms Rf_def])
  have "chromatic_num (Q - S) \<le> length (map (\<lambda>C. C - S) Rf)" by (rule chromatic_num_le[OF v])
  also have "... = length Rf" by simp
  also have "... \<le> length Rs" unfolding Rf_def by (rule length_filter_le)
  finally show ?thesis .
qed

text \<open>Every independent set extends to a maximal one (in P).\<close>

lemma independent_set_extension:
  assumes "P \<subseteq> V" "I0 \<subseteq> P" "is_indep I0"
  shows "\<exists>M \<in> MIS_P P. I0 \<subseteq> M"
proof -
  have finP: "finite P" using finite_subset[OF assms(1) finite_V] .
  define S_set where "S_set = {S. I0 \<subseteq> S \<and> S \<subseteq> P \<and> is_indep S}"
  have "I0 \<in> S_set" using assms unfolding S_set_def by auto
  hence ne: "S_set \<noteq> {}" by auto
  have "S_set \<subseteq> Pow P" unfolding S_set_def by auto
  moreover have "finite (Pow P)" using finP by simp
  ultimately have fin: "finite S_set" by (rule finite_subset)
  obtain M where M_in: "M \<in> S_set" and M_max: "\<forall>S \<in> S_set. M \<subseteq> S \<longrightarrow> S = M"
    using finite_has_maximal[OF fin ne] by blast
  have M_P: "M \<subseteq> P" and M_ind: "is_indep M" and M_I0: "I0 \<subseteq> M"
    using M_in unfolding S_set_def by auto
  have symm: "\<And>a b. (a, b) \<in> E \<Longrightarrow> (b, a) \<in> E" using sym_E unfolding sym_def by blast
  have nbr: "\<forall>v \<in> P - M. \<exists>u \<in> M. (u, v) \<in> E"
  proof (rule ballI, rule ccontr)
    fix v assume vPM: "v \<in> P - M" and "\<not> (\<exists>u \<in> M. (u, v) \<in> E)"
    hence v_no: "\<forall>u \<in> M. (u, v) \<notin> E" by auto
    have sub: "M \<subseteq> insert v M" by auto
    have indep': "is_indep (insert v M)"
    proof -
      have "M \<subseteq> V" using M_ind unfolding is_indep_def by simp
      moreover have "v \<in> V" using vPM assms(1) by auto
      moreover have "\<forall>u \<in> insert v M. \<forall>w \<in> insert v M. u \<noteq> w \<longrightarrow> (u, w) \<notin> E"
      proof (intro ballI impI)
        fix u w assume uw: "u \<in> insert v M" "w \<in> insert v M" "u \<noteq> w"
        consider (MM) "u \<in> M" "w \<in> M" | (vM) "u = v" "w \<in> M" | (Mv) "u \<in> M" "w = v"
          using uw by auto
        thus "(u, w) \<notin> E"
        proof cases
          case MM
          thus ?thesis using M_ind uw(3) unfolding is_indep_def by auto
        next
          case vM
          thus ?thesis using v_no symm by auto
        next
          case Mv
          thus ?thesis using v_no by auto
        qed
      qed
      ultimately show ?thesis unfolding is_indep_def by auto
    qed
    have "insert v M \<in> S_set"
      unfolding S_set_def using M_I0 M_P vPM indep' by auto
    hence "insert v M = M" using M_max sub by blast
    thus False using vPM by auto
  qed
  have "M \<in> MIS_P P"
    unfolding MIS_P_def is_maximal_indep_def using M_P M_ind nbr by auto
  thus ?thesis using M_I0 by blast
qed

text \<open>Lemma 8.1 (MIS recurrence), existential form.\<close>

lemma lemma_8_1_MIS_chromatic_recurrence:
  assumes "P \<subseteq> V" "P \<noteq> {}"
  shows "\<exists>M \<in> MIS_P P. chromatic_num P = 1 + chromatic_num (P - M)"
proof -
  obtain R_opt where R_opt_val: "is_valid_coloring P R_opt"
    and R_opt_len: "length R_opt = chromatic_num P"
    using chromatic_num_attained[OF assms(1)] by blast
  have cls: "\<forall>m \<in> set R_opt. is_indep m \<and> m \<noteq> {}"
    and un: "\<Union> (set R_opt) = P"
    using R_opt_val unfolding is_valid_coloring_def by auto
  have R_ne: "R_opt \<noteq> []"
  proof
    assume "R_opt = []"
    hence "P = {}" using un by auto
    thus False using assms(2) by simp
  qed
  obtain R_prev M_last where R_split: "R_opt = R_prev @ [M_last]"
  proof (cases R_opt rule: rev_cases)
    case Nil
    thus ?thesis using R_ne by simp
  next
    case (snoc ys y)
    thus ?thesis by (rule that)
  qed
  have M_last_mem: "M_last \<in> set R_opt" using R_split by simp
  have M_last_indep: "is_indep M_last" using cls M_last_mem by blast
  have M_last_ne: "M_last \<noteq> {}" using cls M_last_mem by blast
  have M_last_sub: "M_last \<subseteq> P" using un M_last_mem by auto
  have len_prev: "length R_prev + 1 = chromatic_num P"
    using R_opt_len R_split by simp
  have R_prev_val: "is_valid_coloring (P - M_last) R_prev"
  proof -
    have "is_valid_coloring P (R_prev @ [M_last])" using R_opt_val R_split by simp
    thus ?thesis by (rule valid_coloring_snoc_split)
  qed
  obtain M_max where M_max_in: "M_max \<in> MIS_P P" and M_ext: "M_last \<subseteq> M_max"
    using independent_set_extension[OF assms(1) M_last_sub M_last_indep] by blast
  have M_max_sub: "M_max \<subseteq> P" and M_max_indep: "is_indep M_max"
    using M_max_in unfolding MIS_P_def is_maximal_indep_def by auto
  have M_max_ne: "M_max \<noteq> {}" using M_last_ne M_ext by auto
  text \<open>Lower bound: chi(P - M_max) + 1 <= chi(P).\<close>
  have eq: "(P - M_last) - M_max = P - M_max" using M_ext by auto
  have ineq1: "chromatic_num (P - M_max) \<le> length R_prev"
    using chromatic_num_remove_le[OF R_prev_val, of M_max] eq by simp
  have ge: "chromatic_num (P - M_max) + 1 \<le> chromatic_num P"
    using ineq1 len_prev by arith
  text \<open>Upper bound: chi(P) <= chi(P - M_max) + 1.\<close>
  have PM_sub: "P - M_max \<subseteq> V" using assms(1) by auto
  obtain R_rem where R_rem_val: "is_valid_coloring (P - M_max) R_rem"
    and R_rem_len: "length R_rem = chromatic_num (P - M_max)"
    using chromatic_num_attained[OF PM_sub] by blast
  have R_full_val: "is_valid_coloring P (R_rem @ [M_max])"
    by (rule valid_coloring_snoc[OF R_rem_val M_max_indep M_max_ne M_max_sub])
  have "chromatic_num P \<le> length (R_rem @ [M_max])" by (rule chromatic_num_le[OF R_full_val])
  hence le: "chromatic_num P \<le> chromatic_num (P - M_max) + 1" using R_rem_len by simp
  have "chromatic_num P = 1 + chromatic_num (P - M_max)" using ge le by arith
  thus ?thesis using M_max_in by blast
qed

text \<open>Theorem 8.1 (Soundness).\<close>

theorem theorem_8_1_Soundness:
  assumes "\<Gamma>_f \<in> ReachG" "is_terminal \<Gamma>_f"
  obtains R_f where "\<Gamma>_f = ({}, R_f, {}, {})" "is_valid_coloring V R_f"
proof -
  from assms(1) have wf: "well_formed \<Gamma>_f" by (rule reachable_well_formed)
  obtain P R_f I C where \<Gamma>_eq: "\<Gamma>_f = (P, R_f, I, C)" by (cases \<Gamma>_f) auto
  from assms(2) have is_term: "P = {} \<and> I = {} \<and> C = {}"
    unfolding \<Gamma>_eq is_terminal_def by simp
  hence P_e: "P = {}" and I_e: "I = {}" and C_e: "C = {}" by simp_all
  from wf have wf': "well_formed (P, R_f, I, C)" unfolding \<Gamma>_eq .
  have conj: "(\<forall>m \<in> set R_f. is_indep m \<and> m \<noteq> {}) \<and>
              (\<forall>i < length R_f. \<forall>j < length R_f. i \<noteq> j \<longrightarrow> R_f ! i \<inter> R_f ! j = {}) \<and>
              P = V - \<Union> (set R_f)"
    using wf' unfolding well_formed_simp by blast
  from conj have R_cls: "\<forall>m \<in> set R_f. is_indep m \<and> m \<noteq> {}" by blast
  from conj have R_disj: "\<forall>i < length R_f. \<forall>j < length R_f. i \<noteq> j \<longrightarrow> R_f ! i \<inter> R_f ! j = {}"
    by blast
  from conj have cover: "P = V - \<Union> (set R_f)" by blast
  have ne: "\<forall>m \<in> set R_f. m \<noteq> {}" using R_cls by blast
  have dist: "distinct R_f" by (rule index_disjoint_distinct[OF ne R_disj])
  have setdj: "\<forall>A \<in> set R_f. \<forall>B \<in> set R_f. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    by (rule index_disjoint_set_disjoint[OF R_disj])
  have cover0: "V - \<Union> (set R_f) = {}" by (rule trans[OF cover[symmetric] P_e])
  have V_eq: "\<Union> (set R_f) = V"
  proof
    show "\<Union> (set R_f) \<subseteq> V" using R_cls unfolding is_indep_def by auto
    show "V \<subseteq> \<Union> (set R_f)" using cover0 by auto
  qed
  have valid: "is_valid_coloring V R_f"
    unfolding is_valid_coloring_def using dist R_cls V_eq setdj by blast
  have "\<Gamma>_f = ({}, R_f, {}, {})" using \<Gamma>_eq P_e I_e C_e by simp
  thus ?thesis using valid that by blast
qed

text \<open>Theorem 8.2 (Residual-state completeness).\<close>

definition completes :: "'a set \<Rightarrow> 'a set list \<Rightarrow> bool" where
  "completes P R \<equiv> \<exists>\<Gamma>_f \<in> ReachG.
      reachable (P, R, {}, P) \<Gamma>_f \<and> is_terminal \<Gamma>_f \<and>
      (case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = length R + chromatic_num P)"

lemma completeness_aux:
  "\<forall>P R. card P = n \<longrightarrow> (P, R, {}, P) \<in> ReachG \<longrightarrow> completes P R"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (intro allI impI)
    fix P R
    assume cardP: "card P = n" and reach: "(P, R, {}, P) \<in> ReachG"
    have ih: "\<And>P' R'. card P' < n \<Longrightarrow> (P', R', {}, P') \<in> ReachG \<Longrightarrow> completes P' R'"
    proof -
      fix P' R' assume lt: "card P' < n" and r: "(P', R', {}, P') \<in> ReachG"
      from less.IH[OF lt]
      have "\<forall>Q S. card Q = card P' \<longrightarrow> (Q, S, {}, Q) \<in> ReachG \<longrightarrow> completes Q S" .
      thus "completes P' R'" using r by blast
    qed
    have wf: "well_formed (P, R, {}, P)" by (rule reachable_well_formed[OF reach])
    have P_sub: "P \<subseteq> V" using wf unfolding well_formed_simp by blast
    consider (empty) "P = {}" | (nonempty) "P \<noteq> {}" by blast
    thus "completes P R"
    proof cases
      case empty
      have is_term: "is_terminal (P, R, {}, P)"
        unfolding is_terminal_def using empty by simp
      have chrom0: "chromatic_num P = 0" using empty chromatic_num_empty by simp
      have "(P, R, {}, P) \<in> ReachG" by (rule reach)
      moreover have "reachable (P, R, {}, P) (P, R, {}, P)" by (rule rtranclp.rtrancl_refl)
      moreover have "(case (P, R, {}, P) of (_, R_f, _, _) \<Rightarrow>
                        length R_f = length R + chromatic_num P)"
        using chrom0 by simp
      ultimately show ?thesis unfolding completes_def using is_term by blast
    next
      case nonempty
      obtain M where M_in: "M \<in> MIS_P P"
        and chi_eq: "chromatic_num P = 1 + chromatic_num (P - M)"
        using lemma_8_1_MIS_chromatic_recurrence[OF P_sub nonempty] by blast
      have M_is_max: "is_maximal_indep P M" using M_in unfolding MIS_P_def by auto
      have M_sub_P: "M \<subseteq> P" using M_in unfolding MIS_P_def by auto
      have M_ne: "M \<noteq> {}"
      proof
        assume "M = {}"
        from nonempty obtain v where "v \<in> P" by auto
        hence "v \<in> P - M" using \<open>M = {}\<close> by simp
        hence "\<exists>u \<in> M. (u, v) \<in> E" using M_is_max unfolding is_maximal_indep_def by blast
        thus False using \<open>M = {}\<close> by simp
      qed
      have bij: "bij_betw (\<Phi> P R) (MIS_P P) (commit_ready_states P R)"
        by (rule theorem_6_1_MIS_Commit_Ready_Bijection[OF P_sub nonempty])
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
      have fin: "finite P" using finite_subset[OF P_sub finite_V] .
      have lt: "card (P - M) < n"
      proof -
        have "P - M \<subset> P" using M_ne M_sub_P by auto
        hence "card (P - M) < card P" by (rule psubset_card_mono[OF fin])
        thus ?thesis using cardP by simp
      qed
      from ih[OF lt next_reach] obtain \<Gamma>_f where
        \<Gamma>_f_reach: "\<Gamma>_f \<in> ReachG"
        and \<Gamma>_f_sub: "reachable (P - M, R @ [M], {}, P - M) \<Gamma>_f"
        and \<Gamma>_f_term: "is_terminal \<Gamma>_f"
        and \<Gamma>_f_len: "(case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow>
                         length R_f = length (R @ [M]) + chromatic_num (P - M))"
        unfolding completes_def by blast
      have \<Gamma>_f_from_P: "reachable (P, R, {}, P) \<Gamma>_f"
        using reach_next \<Gamma>_f_sub by (rule rtranclp_trans)
      obtain a R_f c d where \<Gamma>_f_eq: "\<Gamma>_f = (a, R_f, c, d)" by (cases \<Gamma>_f) auto
      have len: "length R_f = length R + 1 + chromatic_num (P - M)"
        using \<Gamma>_f_len unfolding \<Gamma>_f_eq by simp
      have len': "length R_f = length R + chromatic_num P" using len chi_eq by arith
      have final_len: "(case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = length R + chromatic_num P)"
        using len' unfolding \<Gamma>_f_eq by simp
      show ?thesis
        unfolding completes_def using \<Gamma>_f_reach \<Gamma>_f_from_P \<Gamma>_f_term final_len by blast
    qed
  qed
qed

theorem theorem_8_2_Residual_Completeness:
  assumes "\<Gamma> \<in> ReachG" "\<Gamma> = (P, R, {}, P)"
  shows "\<exists>\<Gamma>_f \<in> ReachG. reachable \<Gamma> \<Gamma>_f \<and> is_terminal \<Gamma>_f \<and>
          (case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = length R + chromatic_num P)"
proof -
  from assms have reach: "(P, R, {}, P) \<in> ReachG" by simp
  have "completes P R" using completeness_aux[of "card P"] reach by blast
  thus ?thesis unfolding completes_def assms(2) by blast
qed

corollary corollary_8_1_Global_Completeness:
  shows "\<exists>\<Gamma>_f \<in> ReachG. is_terminal \<Gamma>_f \<and>
          (case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = chromatic_num V)"
proof -
  have \<Gamma>0_reach: "\<Gamma>0 \<in> ReachG" unfolding ReachG_def by (auto intro: rtranclp.rtrancl_refl)
  have \<Gamma>0_eq: "\<Gamma>0 = (V, [], {}, V)" unfolding \<Gamma>0_def by simp
  from theorem_8_2_Residual_Completeness[OF \<Gamma>0_reach \<Gamma>0_eq] show ?thesis
  proof (rule bexE)
    fix \<Gamma>_f
    assume m: "\<Gamma>_f \<in> ReachG"
      and c: "reachable \<Gamma>0 \<Gamma>_f \<and> is_terminal \<Gamma>_f \<and>
              (case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = length ([] :: 'a set list) + chromatic_num V)"
    have t: "is_terminal \<Gamma>_f" using c by (rule conjunct2[THEN conjunct1])
    have l: "(case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = length ([] :: 'a set list) + chromatic_num V)"
      using c by (rule conjunct2[THEN conjunct2])
    have l': "(case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = chromatic_num V)"
      using l by (cases \<Gamma>_f) simp
    show ?thesis
    proof (rule bexI[OF _ m])
      show "is_terminal \<Gamma>_f \<and>
            (case \<Gamma>_f of (_, R_f, _, _) \<Rightarrow> length R_f = chromatic_num V)"
        using t l' by (rule conjI)
    qed
  qed
qed

end
end
