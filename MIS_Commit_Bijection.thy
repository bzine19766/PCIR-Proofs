theory MIS_Commit_Bijection
  imports MIS_Cover_Semantics
begin

context fixed_graph
begin

inductive add_path_seq :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  for P :: "'a set" and R :: "'a set list" where
  Nil: "add_path_seq P R [] {} P"
| Cons: "\<lbrakk> add_path_seq P R xs I C; v \<in> C; C' = candidate_set P (I \<union> {v}) \<rbrakk>
          \<Longrightarrow> add_path_seq P R (xs @ [v]) (I \<union> {v}) C'"

lemma add_path_seq_candidate:
  assumes "add_path_seq P R xs I C"
  shows "C = candidate_set P I"
  using assms
proof (induction rule: add_path_seq.induct)
  case Nil
  show ?case by (simp add: candidate_set_empty)
next
  case (Cons xs I C v C')
  show ?case using Cons.hyps by blast
qed

lemma add_path_seq_imp_reachable:
  assumes "add_path_seq P R xs I C"
  shows "(P, R, {}, P) \<rightarrow>G* (P, R, I, C)"
  using assms
proof (induction rule: add_path_seq.induct)
  case Nil
  show ?case by (rule rtranclp.rtrancl_refl)
next
  case (Cons xs I C v C')
  have s: "(P, R, I, C) \<rightarrow>G (P, R, I \<union> {v}, C')"
    using Cons.hyps by (blast intro: step.Add)
  from Cons.IH s show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

definition MIS_P :: "'a set \<Rightarrow> 'a set set" where
  "MIS_P P \<equiv> {M. M \<subseteq> P \<and> is_maximal_indep P M}"

definition commit_ready_states :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a config set" where
  "commit_ready_states P R \<equiv>
    {(P, R, I, {}) | I. (\<exists>xs. add_path_seq P R xs I {}) \<and> is_maximal_indep P I \<and> I \<noteq> {}}"

lemma set_of_add_path_seq:
  assumes "add_path_seq P R xs I C"
  shows "set xs = I"
  using assms
proof (induction rule: add_path_seq.induct)
  case Nil
  show ?case by simp
next
  case (Cons xs I C v C')
  show ?case using Cons.IH by simp
qed

lemma sorted_add_path_seq:
  assumes "add_path_seq P R xs I C"
  shows "sorted_wrt (<) xs \<and> distinct xs"
  using assms
proof (induction rule: add_path_seq.induct)
  case Nil
  show ?case by simp
next
  case (Cons xs I C v C')
  have h1: "add_path_seq P R xs I C" using Cons.hyps by blast
  have h2: "v \<in> C" using Cons.hyps by blast
  have cand: "C = candidate_set P I" by (rule add_path_seq_candidate[OF h1])
  have setxs: "set xs = I" by (rule set_of_add_path_seq[OF h1])
  have finI: "finite I" using setxs by (metis finite_set)
  have "v \<in> candidate_set P I" using h2 cand by simp
  hence vI: "v \<notin> I" and vlt: "\<forall>u \<in> I. u < v"
    using candidate_set_mem_iff[OF finI] by auto
  have sorted_xs: "sorted_wrt (<) xs" using Cons.IH by blast
  have dist_xs: "distinct xs" using Cons.IH by blast
  have "sorted_wrt (<) (xs @ [v])"
    using sorted_xs vlt setxs by (simp add: sorted_wrt_append)
  moreover have "distinct (xs @ [v])"
    using dist_xs vI setxs by simp
  ultimately show ?case by blast
qed

text \<open>Two strictly sorted lists with the same underlying set are equal.\<close>

lemma strict_sorted_set_unique:
  fixes xs ys :: "'a list"
  assumes "sorted_wrt (<) xs" "sorted_wrt (<) ys" "set xs = set ys"
  shows "xs = ys"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  thus ?case by (cases ys) auto
next
  case (Cons x xs)
  obtain y ys' where ys_eq: "ys = y # ys'"
    using Cons.prems(3) by (cases ys) auto
  have sx: "\<forall>z \<in> set xs. x < z" and sxs: "sorted_wrt (<) xs"
    using Cons.prems(1) by simp_all
  have sy: "\<forall>z \<in> set ys'. y < z" and sys': "sorted_wrt (<) ys'"
    using Cons.prems(2) ys_eq by simp_all
  have seteq: "set (x # xs) = set (y # ys')" using Cons.prems(3) ys_eq by simp
  have x_in: "x \<in> set (y # ys')" using seteq by auto
  have y_in: "y \<in> set (x # xs)" using seteq by auto
  have xy: "x = y"
  proof (rule ccontr)
    assume ne: "x \<noteq> y"
    have "x \<in> set ys'" using x_in ne by simp
    hence "y < x" using sy by blast
    have "y \<in> set xs" using y_in ne by auto
    hence "x < y" using sx by blast
    from less_trans[OF \<open>x < y\<close> \<open>y < x\<close>] show False by simp
  qed
  have x_notin_xs: "x \<notin> set xs" using sx by auto
  have x_notin_ys': "x \<notin> set ys'" using sy xy by auto
  have "set xs = set ys'"
  proof
    show "set xs \<subseteq> set ys'"
    proof
      fix z assume z: "z \<in> set xs"
      hence "z \<in> set (y # ys')" using seteq by auto
      moreover have "z \<noteq> y" using z x_notin_xs xy by auto
      ultimately show "z \<in> set ys'" by simp
    qed
  next
    show "set ys' \<subseteq> set xs"
    proof
      fix z assume z: "z \<in> set ys'"
      hence "z \<in> set (x # xs)" using seteq by auto
      moreover have "z \<noteq> x" using z x_notin_ys' by auto
      ultimately show "z \<in> set xs" by simp
    qed
  qed
  hence "xs = ys'" using Cons.IH[OF sxs sys'] by blast
  thus ?case using xy ys_eq by simp
qed

lemma add_path_seq_unique:
  assumes "add_path_seq P R xs I C" "add_path_seq P R ys I C'"
  shows "xs = ys"
proof -
  have sx: "sorted_wrt (<) xs" using sorted_add_path_seq[OF assms(1)] by blast
  have sy: "sorted_wrt (<) ys" using sorted_add_path_seq[OF assms(2)] by blast
  have "set xs = set ys"
    using set_of_add_path_seq[OF assms(1)] set_of_add_path_seq[OF assms(2)] by simp
  from strict_sorted_set_unique[OF sx sy this] show ?thesis .
qed

text \<open>Every finite set of a linear order has a strictly sorted enumeration.\<close>

lemma exists_sorted_enum:
  fixes S :: "'a set"
  assumes "finite S"
  shows "\<exists>xs. set xs = S \<and> sorted_wrt (<) xs \<and> distinct xs"
proof -
  have s1: "set (sorted_list_of_set S) = S" using assms by simp
  have s2: "sorted_wrt (<) (sorted_list_of_set S)"
    by (simp add: strict_sorted_iff)
  have s3: "distinct (sorted_list_of_set S)" by simp
  from s1 s2 s3 show ?thesis by blast
qed

text \<open>A strictly sorted enumeration of an independent set (inside P) is a canonical ADD path.\<close>

lemma list_to_add_path_seq:
  assumes "sorted_wrt (<) xs" "distinct xs" "set xs \<subseteq> P" "is_indep (set xs)"
  shows "add_path_seq P R xs (set xs) (candidate_set P (set xs))"
  using assms
proof (induction xs rule: rev_induct)
  case Nil
  show ?case using add_path_seq.Nil by (simp add: candidate_set_empty)
next
  case (snoc x xs)
  have sorted_xs: "sorted_wrt (<) xs" and lt: "\<forall>u \<in> set xs. u < x"
    using snoc.prems(1) by (simp_all add: sorted_wrt_append)
  have dist_xs: "distinct xs" using snoc.prems(2) by simp
  have x_notin: "x \<notin> set xs" using lt by auto
  have sub_xs: "set xs \<subseteq> P" and xP: "x \<in> P" using snoc.prems(3) by auto
  have ind_x: "is_indep (set xs \<union> {x})" using snoc.prems(4) by simp
  have ind_xs: "is_indep (set xs)" using ind_x unfolding is_indep_def by auto
  have nE: "\<forall>u \<in> set xs. (u, x) \<notin> E"
  proof
    fix u assume u: "u \<in> set xs"
    hence "u < x" using lt by blast
    hence "u \<noteq> x" by (rule less_imp_neq)
    thus "(u, x) \<notin> E" using ind_x u unfolding is_indep_def by auto
  qed
  have ih: "add_path_seq P R xs (set xs) (candidate_set P (set xs))"
    by (rule snoc.IH[OF sorted_xs dist_xs sub_xs ind_xs])
  have key: "x \<in> candidate_set P (set xs) \<longleftrightarrow>
      (x \<in> P \<and> x \<notin> set xs \<and> (\<forall>u \<in> set xs. u < x) \<and> (\<forall>u \<in> set xs. (u, x) \<notin> E))"
    by (rule candidate_set_mem_iff[OF finite_set])
  have x_cand: "x \<in> candidate_set P (set xs)" using key xP x_notin lt nE by blast
  have "add_path_seq P R (xs @ [x]) (set xs \<union> {x}) (candidate_set P (set xs \<union> {x}))"
    by (rule add_path_seq.Cons[OF ih x_cand refl])
  thus ?case by simp
qed

definition \<Phi> :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set \<Rightarrow> 'a config" where
  "\<Phi> P R M = (P, R, M, {})"

text \<open>Theorem 6.1: MIS(G[P]) is in bijection with the commit-ready configurations
  reached by canonical ADD paths. Path uniqueness is add_path_seq_unique.\<close>

theorem theorem_6_1_MIS_Commit_Ready_Bijection:
  assumes "P \<subseteq> V" "P \<noteq> {}"
  shows "bij_betw (\<Phi> P R) (MIS_P P) (commit_ready_states P R)"
proof (unfold bij_betw_def, intro conjI)
  show "inj_on (\<Phi> P R) (MIS_P P)"
    unfolding inj_on_def \<Phi>_def by auto
next
  have finP: "finite P" by (rule finite_sub[OF assms(1)])
  show "\<Phi> P R ` MIS_P P = commit_ready_states P R"
  proof (rule set_eqI)
    fix \<Gamma>
    show "\<Gamma> \<in> \<Phi> P R ` MIS_P P \<longleftrightarrow> \<Gamma> \<in> commit_ready_states P R"
    proof
      assume "\<Gamma> \<in> \<Phi> P R ` MIS_P P"
      then obtain M where M_in: "M \<in> MIS_P P" and \<Gamma>_eq: "\<Gamma> = \<Phi> P R M"
        by (auto simp: image_iff)
      have M_max: "is_maximal_indep P M" and M_sub: "M \<subseteq> P"
        using M_in unfolding MIS_P_def by auto
      have M_fin: "finite M" by (rule finite_subset[OF M_sub finP])
      have M_ind: "is_indep M" using M_max unfolding is_maximal_indep_def by blast
      have M_ne: "M \<noteq> {}"
      proof
        assume "M = {}"
        from assms(2) obtain v where "v \<in> P" by auto
        hence "v \<in> P - M" using \<open>M = {}\<close> by simp
        hence "\<exists>u \<in> M. (u, v) \<in> E" using M_max unfolding is_maximal_indep_def by blast
        thus False using \<open>M = {}\<close> by simp
      qed
      obtain xs where xs: "set xs = M" "sorted_wrt (<) xs" "distinct xs"
        using exists_sorted_enum[OF M_fin] by blast
      have path0: "add_path_seq P R xs (set xs) (candidate_set P (set xs))"
        by (rule list_to_add_path_seq[OF xs(2) xs(3)]) (use xs(1) M_sub M_ind in auto)
      have cs_empty: "candidate_set P M = {}"
      proof (rule equals0I)
        fix x assume "x \<in> candidate_set P M"
        hence xP: "x \<in> P" and xM: "x \<notin> M" and xE: "\<forall>u \<in> M. (u, x) \<notin> E"
          using candidate_set_mem_iff[OF M_fin] by auto
        have "\<exists>u \<in> M. (u, x) \<in> E"
          using M_max xP xM unfolding is_maximal_indep_def by blast
        thus False using xE by blast
      qed
      have path: "add_path_seq P R xs M {}" using path0 xs(1) cs_empty by simp
      show "\<Gamma> \<in> commit_ready_states P R"
        unfolding \<Gamma>_eq \<Phi>_def commit_ready_states_def using path M_max M_ne by blast
    next
      assume "\<Gamma> \<in> commit_ready_states P R"
      then obtain I where \<Gamma>_eq: "\<Gamma> = (P, R, I, {})" and max_I: "is_maximal_indep P I"
        unfolding commit_ready_states_def by auto
      have "I \<in> MIS_P P"
        using max_I unfolding MIS_P_def is_maximal_indep_def by auto
      thus "\<Gamma> \<in> \<Phi> P R ` MIS_P P" using \<Gamma>_eq by (auto simp: \<Phi>_def)
    qed
  qed
qed

end
end
