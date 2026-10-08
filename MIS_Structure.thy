theory MIS_Structure
  imports MIS_Universal
begin

text \<open>
  Mechanisation of the structural results of Section 4 of the paper:

    Theorem 4.1   unique_predecessor
    Theorem 4.2   rooted_tree   (with unique_path, acyclic_reach, root_no_pred)
    Theorem 4.3   partial_order_reach
    Prop.   4.1   self_containment (with step_unfold, enabled_iff, finite_branching)
    Cor.    4.2   disjoint_subtrees
    Cor.    4.3   least_element, unique_minimal, root_minimal

  Everything is proved for the reachable configurations ReachG.
\<close>

context fixed_graph
begin

(* ========================================================================= *)
(* Part 1 : Elementary facts about the transition relation                   *)
(* ========================================================================= *)

text \<open>Explicit characterisation of the transition relation on tuples.\<close>

lemma step_unfold:
  "(P, R, I, C) \<rightarrow>G \<Gamma>' \<longleftrightarrow>
     (\<exists>v. v \<in> C \<and> \<Gamma>' = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))) \<or>
     (C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I \<and>
        \<Gamma>' = (P - I, R @ [I], {}, P - I))"
proof
  assume st: "(P, R, I, C) \<rightarrow>G \<Gamma>'"
  from st show
    "(\<exists>v. v \<in> C \<and> \<Gamma>' = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))) \<or>
     (C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I \<and>
        \<Gamma>' = (P - I, R @ [I], {}, P - I))"
    by (cases rule: step.cases) auto
next
  assume h:
    "(\<exists>v. v \<in> C \<and> \<Gamma>' = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))) \<or>
     (C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I \<and>
        \<Gamma>' = (P - I, R @ [I], {}, P - I))"
  from h show "(P, R, I, C) \<rightarrow>G \<Gamma>'"
  proof
    assume "\<exists>v. v \<in> C \<and> \<Gamma>' = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))"
    then obtain v where vC: "v \<in> C"
      and e: "\<Gamma>' = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))" by blast
    show ?thesis unfolding e by (rule step.Add[OF vC refl])
  next
    assume "C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I \<and>
              \<Gamma>' = (P - I, R @ [I], {}, P - I)"
    hence c: "C = {}" and ne: "I \<noteq> {}" and mx: "is_maximal_indep P I"
      and e: "\<Gamma>' = (P - I, R @ [I], {}, P - I)" by blast+
    show ?thesis unfolding e by (rule step.Commit[OF c ne mx])
  qed
qed

lemma reach_iff: "\<Gamma> \<in> ReachG \<longleftrightarrow> \<Gamma>0 \<rightarrow>G* \<Gamma>"
  unfolding ReachG_def by simp

lemma rtranclp_last_step:
  assumes "a \<rightarrow>G* b"
  shows "b = a \<or> (\<exists>q. a \<rightarrow>G* q \<and> q \<rightarrow>G b)"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  show ?case using step.hyps by blast
qed

lemma wf_of_reach:
  assumes "\<Gamma>0 \<rightarrow>G* x"
  shows "well_formed x"
proof (rule reachable_well_formed)
  show "x \<in> ReachG" using assms by (simp add: reach_iff)
qed

lemma wf_reach_closed:
  assumes "well_formed \<Gamma>" and "\<Gamma> \<rightarrow>G* \<Delta>"
  shows "well_formed \<Delta>"
  using assms(2)
proof (induction rule: rtranclp_induct)
  case base
  show ?case using assms(1) .
next
  case (step y z)
  show ?case using invariant_preservation[OF step.hyps(2) step.IH] .
qed

text \<open>The progress measure decreases along every non-trivial path.\<close>

lemma rho_reach:
  assumes "well_formed \<Gamma>" and "\<Gamma> \<rightarrow>G* \<Delta>"
  shows "\<Delta> = \<Gamma> \<or> \<rho> \<Delta> < \<rho> \<Gamma>"
  using assms(2)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have wfy: "well_formed y" by (rule wf_reach_closed[OF assms(1) step.hyps(1)])
  have lt: "\<rho> z < \<rho> y" by (rule \<rho>_strict_decrease[OF step.hyps(2) wfy])
  show ?case
  proof (cases "y = \<Gamma>")
    case True
    hence "\<rho> z < \<rho> \<Gamma>" using lt by simp
    thus ?thesis by (rule disjI2)
  next
    case False
    hence "\<rho> y < \<rho> \<Gamma>" using step.IH by blast
    hence "\<rho> z < \<rho> \<Gamma>" by (rule less_trans[OF lt])
    thus ?thesis by (rule disjI2)
  qed
qed

lemma reach_antisym:
  assumes wf: "well_formed \<Gamma>" and a: "\<Gamma> \<rightarrow>G* \<Delta>" and b: "\<Delta> \<rightarrow>G* \<Gamma>"
  shows "\<Gamma> = \<Delta>"
proof (rule ccontr)
  assume ne: "\<Gamma> \<noteq> \<Delta>"
  have wfD: "well_formed \<Delta>" by (rule wf_reach_closed[OF wf a])
  have h1: "\<rho> \<Delta> < \<rho> \<Gamma>" using rho_reach[OF wf a] ne by blast
  have h2: "\<rho> \<Gamma> < \<rho> \<Delta>" using rho_reach[OF wfD b] ne by blast
  have "\<rho> \<Delta> < \<rho> \<Delta>" by (rule less_trans[OF h1 h2])
  thus False by simp
qed

(* ========================================================================= *)
(* Part 2 : Uniqueness of the predecessor                                    *)
(* ========================================================================= *)

lemma snoc_inject_pair:
  assumes "xs @ [x] = ys @ [y]"
  shows "xs = ys \<and> x = y"
proof -
  have h1: "xs = butlast (xs @ [x])" by simp
  have h2: "butlast (ys @ [y]) = ys" by simp
  have h3: "x = last (xs @ [x])" by simp
  have h4: "last (ys @ [y]) = y" by simp
  have "butlast (xs @ [x]) = butlast (ys @ [y])" using assms by simp
  hence e1: "xs = ys" using h1 h2 by simp
  have "last (xs @ [x]) = last (ys @ [y])" using assms by simp
  hence e2: "x = y" using h3 h4 by simp
  show ?thesis using e1 e2 by simp
qed

text \<open>Two ADD steps with the same successor come from the same configuration.\<close>

lemma add_pred_unique:
  assumes wf1: "well_formed (P1, R1, I1, C1)" and wf2: "well_formed (P2, R2, I2, C2)"
      and hv1: "v1 \<in> C1" and hv2: "v2 \<in> C2"
      and eq: "(P1, R1, I1 \<union> {v1}, candidate_set P1 (I1 \<union> {v1})) =
               (P2, R2, I2 \<union> {v2}, candidate_set P2 (I2 \<union> {v2}))"
  shows "(P1, R1, I1, C1) = (P2, R2, I2, C2)"
proof -
  note q1 = wf_parts[OF wf1]
  note q2 = wf_parts[OF wf2]
  have fin1: "finite I1" by (rule finite_indep[OF q1(2)])
  have fin2: "finite I2" by (rule finite_indep[OF q2(2)])
  have hP: "P1 = P2" using arg_cong[where f = fst, OF eq] by simp
  have hR: "R1 = R2" using arg_cong[where f = "\<lambda>x. fst (snd x)", OF eq] by simp
  have hI: "I1 \<union> {v1} = I2 \<union> {v2}"
    using arg_cong[where f = "\<lambda>x. fst (snd (snd x))", OF eq] by simp
  have c1: "v1 \<in> candidate_set P1 I1" using hv1 q1(4) by simp
  have c2: "v2 \<in> candidate_set P2 I2" using hv2 q2(4) by simp
  have m1: "v1 \<notin> I1" and l1: "\<forall>u \<in> I1. u < v1"
    using c1 candidate_set_mem_iff[OF fin1] by auto
  have m2: "v2 \<notin> I2" and l2: "\<forall>u \<in> I2. u < v2"
    using c2 candidate_set_mem_iff[OF fin2] by auto
  have mem: "\<And>x. x \<in> I1 \<union> {v1} \<longleftrightarrow> x \<in> I2 \<union> {v2}"
    by (simp only: hI)
  have vv: "v1 = v2"
  proof (rule ccontr)
    assume ne: "v1 \<noteq> v2"
    have x1: "v1 \<in> I2 \<union> {v2}" using mem[of v1] by simp
    hence "v1 \<in> I2" using ne by auto
    hence a: "v1 < v2" using l2 by blast
    have x2: "v2 \<in> I1 \<union> {v1}" using mem[of v2] by simp
    hence "v2 \<in> I1" using ne by auto
    hence b: "v2 < v1" using l1 by blast
    have "v1 < v1" by (rule less_trans[OF a b])
    thus False by simp
  qed
  have hI12: "I1 = I2"
  proof (rule set_eqI)
    fix x
    show "x \<in> I1 \<longleftrightarrow> x \<in> I2"
    proof
      assume x: "x \<in> I1"
      have "x \<in> I2 \<union> {v2}" using mem[of x] x by simp
      moreover have "x \<noteq> v2" using x m1 vv by auto
      ultimately show "x \<in> I2" by auto
    next
      assume x: "x \<in> I2"
      have "x \<in> I1 \<union> {v1}" using mem[of x] x by simp
      moreover have "x \<noteq> v1" using x m2 vv by auto
      ultimately show "x \<in> I1" by auto
    qed
  qed
  have hC: "C1 = C2" using q1(4) q2(4) hP hI12 by simp
  show ?thesis using hP hR hI12 hC by simp
qed

text \<open>Two COMMIT steps with the same successor come from the same configuration.\<close>

lemma commit_pred_unique:
  assumes wf1: "well_formed (P1, R1, I1, C1)" and wf2: "well_formed (P2, R2, I2, C2)"
      and c1: "C1 = {}" and c2: "C2 = {}"
      and eq: "(P1 - I1, R1 @ [I1], ({}::'a set), P1 - I1) = (P2 - I2, R2 @ [I2], {}, P2 - I2)"
  shows "(P1, R1, I1, C1) = (P2, R2, I2, C2)"
proof -
  note q1 = wf_parts[OF wf1]
  note q2 = wf_parts[OF wf2]
  have e1: "P1 - I1 = P2 - I2" using arg_cong[where f = fst, OF eq] by simp
  have e2: "R1 @ [I1] = R2 @ [I2]"
    using arg_cong[where f = "\<lambda>x. fst (snd x)", OF eq] by simp
  have hRI: "R1 = R2 \<and> I1 = I2" by (rule snoc_inject_pair[OF e2])
  hence hR: "R1 = R2" and hI: "I1 = I2" by blast+
  have e1': "P1 - I2 = P2 - I2" using e1 hI by simp
  have s1: "I2 \<subseteq> P1" using q1(3) hI by simp
  have s2: "I2 \<subseteq> P2" using q2(3) by simp
  have hP: "P1 = P2"
  proof -
    have "P1 = (P1 - I2) \<union> I2" using s1 by auto
    also have "\<dots> = (P2 - I2) \<union> I2" using e1' by simp
    also have "\<dots> = P2" using s2 by auto
    finally show ?thesis .
  qed
  show ?thesis using hP hR hI c1 c2 by simp
qed

lemma Un_single_ne: "I \<union> {v} \<noteq> {}"
  by simp

lemma snoc_ne_Nil': "R @ [I] \<noteq> []"
  by simp

text \<open>The initial configuration has no predecessor at all.\<close>

lemma root_no_pred: "\<not> (p \<rightarrow>G \<Gamma>0)"
proof
  assume h: "p \<rightarrow>G \<Gamma>0"
  obtain P R I C where hp: "p = (P, R, I, C)" by (cases p) auto
  have h': "(P, R, I, C) \<rightarrow>G (V, [], {}, V)"
    using h hp unfolding \<Gamma>0_def by simp
  from h'[unfolded step_unfold] show False
  proof
    assume "\<exists>v. v \<in> C \<and> (V, [], {}, V) = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))"
    then obtain v where
      e: "(V, [], {}, V) = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))" by blast
    have "{} = I \<union> {v}"
      using arg_cong[where f = "\<lambda>x. fst (snd (snd x))", OF e] by simp
    thus False using Un_single_ne by metis
  next
    assume "C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I \<and>
              (V, [], {}, V) = (P - I, R @ [I], {}, P - I)"
    hence e: "(V, [], {}, V) = (P - I, R @ [I], {}, P - I)" by blast
    have "[] = R @ [I]"
      using arg_cong[where f = "\<lambda>x. fst (snd x)", OF e] by simp
    thus False using snoc_ne_Nil' by metis
  qed
qed

text \<open>Core uniqueness: two well-formed predecessors of the same configuration coincide.\<close>

lemma step_pred_unique:
  assumes wf1: "well_formed p1" and wf2: "well_formed p2"
      and s1: "p1 \<rightarrow>G \<Gamma>" and s2: "p2 \<rightarrow>G \<Gamma>"
  shows "p1 = p2"
proof -
  obtain P1 R1 I1 C1 where hp1: "p1 = (P1, R1, I1, C1)" by (cases p1) auto
  obtain P2 R2 I2 C2 where hp2: "p2 = (P2, R2, I2, C2)" by (cases p2) auto
  have wf1': "well_formed (P1, R1, I1, C1)" using wf1 hp1 by simp
  have wf2': "well_formed (P2, R2, I2, C2)" using wf2 hp2 by simp
  have s1': "(P1, R1, I1, C1) \<rightarrow>G \<Gamma>" using s1 hp1 by simp
  have s2': "(P2, R2, I2, C2) \<rightarrow>G \<Gamma>" using s2 hp2 by simp
  have key: "(P1, R1, I1, C1) = (P2, R2, I2, C2)"
  proof -
    from s1'[unfolded step_unfold] show ?thesis
    proof
      assume "\<exists>v1. v1 \<in> C1 \<and>
                \<Gamma> = (P1, R1, I1 \<union> {v1}, candidate_set P1 (I1 \<union> {v1}))"
      then obtain v1 where hv1: "v1 \<in> C1"
        and g1: "\<Gamma> = (P1, R1, I1 \<union> {v1}, candidate_set P1 (I1 \<union> {v1}))" by blast
      from s2'[unfolded step_unfold] show ?thesis
      proof
        assume "\<exists>v2. v2 \<in> C2 \<and>
                  \<Gamma> = (P2, R2, I2 \<union> {v2}, candidate_set P2 (I2 \<union> {v2}))"
        then obtain v2 where hv2: "v2 \<in> C2"
          and g2: "\<Gamma> = (P2, R2, I2 \<union> {v2}, candidate_set P2 (I2 \<union> {v2}))" by blast
        have eq: "(P1, R1, I1 \<union> {v1}, candidate_set P1 (I1 \<union> {v1})) =
                  (P2, R2, I2 \<union> {v2}, candidate_set P2 (I2 \<union> {v2}))"
          by (rule trans[OF sym[OF g1] g2])
        show ?thesis by (rule add_pred_unique[OF wf1' wf2' hv1 hv2 eq])
      next
        assume "C2 = {} \<and> I2 \<noteq> {} \<and> is_maximal_indep P2 I2 \<and>
                  \<Gamma> = (P2 - I2, R2 @ [I2], {}, P2 - I2)"
        hence g2: "\<Gamma> = (P2 - I2, R2 @ [I2], {}, P2 - I2)" by blast
        have eq: "(P1, R1, I1 \<union> {v1}, candidate_set P1 (I1 \<union> {v1})) =
                  (P2 - I2, R2 @ [I2], {}, P2 - I2)"
          by (rule trans[OF sym[OF g1] g2])
        have "{} = I1 \<union> {v1}" using arg_cong[where f = "\<lambda>x. fst (snd (snd x))", OF eq]
          by simp
        hence False using Un_single_ne by metis
        thus ?thesis by blast
      qed
    next
      assume "C1 = {} \<and> I1 \<noteq> {} \<and> is_maximal_indep P1 I1 \<and>
                \<Gamma> = (P1 - I1, R1 @ [I1], {}, P1 - I1)"
      hence c1: "C1 = {}" and g1: "\<Gamma> = (P1 - I1, R1 @ [I1], {}, P1 - I1)" by blast+
      from s2'[unfolded step_unfold] show ?thesis
      proof
        assume "\<exists>v2. v2 \<in> C2 \<and>
                  \<Gamma> = (P2, R2, I2 \<union> {v2}, candidate_set P2 (I2 \<union> {v2}))"
        then obtain v2 where
          g2: "\<Gamma> = (P2, R2, I2 \<union> {v2}, candidate_set P2 (I2 \<union> {v2}))" by blast
        have eq: "(P1 - I1, R1 @ [I1], ({}::'a set), P1 - I1) =
                  (P2, R2, I2 \<union> {v2}, candidate_set P2 (I2 \<union> {v2}))"
          by (rule trans[OF sym[OF g1] g2])
        have "{} = I2 \<union> {v2}" using arg_cong[where f = "\<lambda>x. fst (snd (snd x))", OF eq]
          by simp
        hence False using Un_single_ne by metis
        thus ?thesis by blast
      next
        assume "C2 = {} \<and> I2 \<noteq> {} \<and> is_maximal_indep P2 I2 \<and>
                  \<Gamma> = (P2 - I2, R2 @ [I2], {}, P2 - I2)"
        hence c2: "C2 = {}" and g2: "\<Gamma> = (P2 - I2, R2 @ [I2], {}, P2 - I2)" by blast+
        have eq: "(P1 - I1, R1 @ [I1], ({}::'a set), P1 - I1) = (P2 - I2, R2 @ [I2], {}, P2 - I2)"
          by (rule trans[OF sym[OF g1] g2])
        show ?thesis by (rule commit_pred_unique[OF wf1' wf2' c1 c2 eq])
      qed
    qed
  qed
  show ?thesis by (rule trans[OF trans[OF hp1 key] sym[OF hp2]])
qed

text \<open>Theorem 4.1 (Unique Predecessor).\<close>

theorem unique_predecessor:
  assumes r: "\<Gamma> \<in> ReachG" and ne: "\<Gamma> \<noteq> \<Gamma>0"
  shows "\<exists>!p. p \<in> ReachG \<and> p \<rightarrow>G \<Gamma>"
proof -
  have a: "\<Gamma>0 \<rightarrow>G* \<Gamma>" using r by (simp add: reach_iff)
  from rtranclp_last_step[OF a] ne obtain q
    where q1: "\<Gamma>0 \<rightarrow>G* q" and q2: "q \<rightarrow>G \<Gamma>" by blast
  have qR: "q \<in> ReachG" using q1 by (simp add: reach_iff)
  show ?thesis
  proof (rule ex1I[of _ q])
    show "q \<in> ReachG \<and> q \<rightarrow>G \<Gamma>" using qR q2 by blast
  next
    fix x assume x: "x \<in> ReachG \<and> x \<rightarrow>G \<Gamma>"
    hence xR: "x \<in> ReachG" and xs: "x \<rightarrow>G \<Gamma>" by blast+
    show "x = q"
      by (rule step_pred_unique[OF reachable_well_formed[OF xR]
                                   reachable_well_formed[OF qR] xs q2])
  qed
qed

(* ========================================================================= *)
(* Part 3 : Paths and the rooted tree                                        *)
(* ========================================================================= *)

text \<open>A path from a is the list of configurations visited after a.\<close>

inductive path :: "'a config \<Rightarrow> 'a config list \<Rightarrow> 'a config \<Rightarrow> bool"
  for a :: "'a config" where
  path_nil: "path a [] a"
| path_snoc: "\<lbrakk> path a xs b; b \<rightarrow>G c \<rbrakk> \<Longrightarrow> path a (xs @ [c]) c"

lemma path_inv:
  assumes "path a ys c"
  shows "(ys = [] \<and> c = a) \<or> (\<exists>ys' b. ys = ys' @ [c] \<and> path a ys' b \<and> b \<rightarrow>G c)"
  using assms by (cases rule: path.cases) auto

lemma path_reach:
  assumes "path a xs b"
  shows "a \<rightarrow>G* b"
  using assms
proof (induction rule: path.induct)
  case path_nil
  show ?case by (rule rtranclp.rtrancl_refl)
next
  case (path_snoc xs b c)
  from path_snoc.IH path_snoc.hyps(2) show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma reach_path:
  assumes "a \<rightarrow>G* b"
  shows "\<exists>xs. path a xs b"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  have "path a [] a" by (rule path.path_nil)
  thus ?case by blast
next
  case (step y z)
  from step.IH obtain xs where hx: "path a xs y" by blast
  have "path a (xs @ [z]) z" by (rule path.path_snoc[OF hx step.hyps(2)])
  thus ?case by blast
qed

lemma path_unique_aux:
  assumes p1: "path \<Gamma>0 xs c"
  shows "\<forall>ys. path \<Gamma>0 ys c \<longrightarrow> xs = ys"
  using p1
proof (induction rule: path.induct)
  case path_nil
  show ?case
  proof (intro allI impI)
    fix ys assume hy: "path \<Gamma>0 ys \<Gamma>0"
    from path_inv[OF hy] show "[] = ys"
    proof
      assume "ys = [] \<and> \<Gamma>0 = \<Gamma>0"
      thus ?thesis by simp
    next
      assume "\<exists>ys' b. ys = ys' @ [\<Gamma>0] \<and> path \<Gamma>0 ys' b \<and> b \<rightarrow>G \<Gamma>0"
      then obtain b where "b \<rightarrow>G \<Gamma>0" by blast
      thus ?thesis using root_no_pred by blast
    qed
  qed
next
  case (path_snoc xs b c)
  show ?case
  proof (intro allI impI)
    fix ys assume hy: "path \<Gamma>0 ys c"
    from path_inv[OF hy] show "xs @ [c] = ys"
    proof
      assume "ys = [] \<and> c = \<Gamma>0"
      hence "c = \<Gamma>0" by blast
      hence "b \<rightarrow>G \<Gamma>0" using path_snoc.hyps(2) by simp
      thus ?thesis using root_no_pred by blast
    next
      assume "\<exists>ys' b'. ys = ys' @ [c] \<and> path \<Gamma>0 ys' b' \<and> b' \<rightarrow>G c"
      then obtain ys' b' where e: "ys = ys' @ [c]"
        and pp: "path \<Gamma>0 ys' b'" and bs: "b' \<rightarrow>G c" by blast
      have rb: "\<Gamma>0 \<rightarrow>G* b" by (rule path_reach[OF path_snoc.hyps(1)])
      have rb': "\<Gamma>0 \<rightarrow>G* b'" by (rule path_reach[OF pp])
      have bb: "b' = b"
        by (rule step_pred_unique[OF wf_of_reach[OF rb'] wf_of_reach[OF rb]
                                     bs path_snoc.hyps(2)])
      have pp': "path \<Gamma>0 ys' b" using pp bb by simp
      have "xs = ys'" by (rule path_snoc.IH[rule_format, OF pp'])
      thus ?thesis using e by simp
    qed
  qed
qed

text \<open>Every reachable configuration has exactly one root-to-node path.\<close>

theorem unique_path:
  assumes "\<Gamma> \<in> ReachG"
  shows "\<exists>!xs. path \<Gamma>0 xs \<Gamma>"
proof -
  have a: "\<Gamma>0 \<rightarrow>G* \<Gamma>" using assms by (simp add: reach_iff)
  from reach_path[OF a] obtain xs where px: "path \<Gamma>0 xs \<Gamma>" by blast
  show ?thesis
  proof (rule ex1I[of _ xs])
    show "path \<Gamma>0 xs \<Gamma>" by (rule px)
  next
    fix ys assume hy: "path \<Gamma>0 ys \<Gamma>"
    show "ys = xs" using path_unique_aux[OF px] hy by blast
  qed
qed

text \<open>No cycles: there is no path back to a configuration from one of its successors.\<close>

theorem acyclic_reach:
  assumes g: "\<Gamma> \<in> ReachG" and s: "\<Gamma> \<rightarrow>G x"
  shows "\<not> (x \<rightarrow>G* \<Gamma>)"
proof
  assume hb: "x \<rightarrow>G* \<Gamma>"
  have wfG: "well_formed \<Gamma>" by (rule reachable_well_formed[OF g])
  have xR: "x \<in> ReachG" by (rule reach_step[OF g s])
  have wfx: "well_formed x" by (rule reachable_well_formed[OF xR])
  have lt: "\<rho> x < \<rho> \<Gamma>" by (rule \<rho>_strict_decrease[OF s wfG])
  from rho_reach[OF wfx hb] show False
  proof
    assume "\<Gamma> = x"
    thus False using lt by simp
  next
    assume h: "\<rho> \<Gamma> < \<rho> x"
    have "\<rho> x < \<rho> x" by (rule less_trans[OF lt h])
    thus False by simp
  qed
qed

text \<open>Theorem 4.2 (Rooted Tree).\<close>

theorem rooted_tree:
  "(\<forall>\<Gamma> \<in> ReachG. \<Gamma>0 \<rightarrow>G* \<Gamma>) \<and>
   (\<forall>p. \<not> (p \<rightarrow>G \<Gamma>0)) \<and>
   (\<forall>\<Gamma> \<in> ReachG. \<Gamma> \<noteq> \<Gamma>0 \<longrightarrow> (\<exists>!p. p \<in> ReachG \<and> p \<rightarrow>G \<Gamma>)) \<and>
   (\<forall>\<Gamma> \<in> ReachG. \<forall>x. \<Gamma> \<rightarrow>G x \<longrightarrow> \<not> (x \<rightarrow>G* \<Gamma>)) \<and>
   (\<forall>\<Gamma> \<in> ReachG. \<exists>!xs. path \<Gamma>0 xs \<Gamma>)"
proof (intro conjI)
  show "\<forall>\<Gamma> \<in> ReachG. \<Gamma>0 \<rightarrow>G* \<Gamma>" by (simp add: reach_iff)
next
  show "\<forall>p. \<not> (p \<rightarrow>G \<Gamma>0)" using root_no_pred by blast
next
  show "\<forall>\<Gamma> \<in> ReachG. \<Gamma> \<noteq> \<Gamma>0 \<longrightarrow> (\<exists>!p. p \<in> ReachG \<and> p \<rightarrow>G \<Gamma>)"
  proof (intro ballI impI)
    fix \<Gamma> assume r: "\<Gamma> \<in> ReachG" and ne: "\<Gamma> \<noteq> \<Gamma>0"
    show "\<exists>!p. p \<in> ReachG \<and> p \<rightarrow>G \<Gamma>" by (rule unique_predecessor[OF r ne])
  qed
next
  show "\<forall>\<Gamma> \<in> ReachG. \<forall>x. \<Gamma> \<rightarrow>G x \<longrightarrow> \<not> (x \<rightarrow>G* \<Gamma>)"
  proof (intro ballI allI impI)
    fix \<Gamma> x assume g: "\<Gamma> \<in> ReachG" and s: "\<Gamma> \<rightarrow>G x"
    show "\<not> (x \<rightarrow>G* \<Gamma>)" by (rule acyclic_reach[OF g s])
  qed
next
  show "\<forall>\<Gamma> \<in> ReachG. \<exists>!xs. path \<Gamma>0 xs \<Gamma>"
  proof (intro ballI)
    fix \<Gamma> assume g: "\<Gamma> \<in> ReachG"
    show "\<exists>!xs. path \<Gamma>0 xs \<Gamma>" by (rule unique_path[OF g])
  qed
qed

(* ========================================================================= *)
(* Part 4 : Reachability as a partial order                                  *)
(* ========================================================================= *)

text \<open>Theorem 4.3 (Partial Order): reflexive, transitive, antisymmetric on ReachG.\<close>

theorem partial_order_reach:
  "(\<forall>\<Gamma> \<in> ReachG. \<Gamma> \<rightarrow>G* \<Gamma>) \<and>
   (\<forall>\<Gamma> \<Delta> \<Theta>. \<Gamma> \<rightarrow>G* \<Delta> \<longrightarrow> \<Delta> \<rightarrow>G* \<Theta> \<longrightarrow> \<Gamma> \<rightarrow>G* \<Theta>) \<and>
   (\<forall>\<Gamma> \<in> ReachG. \<forall>\<Delta>. \<Gamma> \<rightarrow>G* \<Delta> \<longrightarrow> \<Delta> \<rightarrow>G* \<Gamma> \<longrightarrow> \<Gamma> = \<Delta>)"
proof (intro conjI)
  show "\<forall>\<Gamma> \<in> ReachG. \<Gamma> \<rightarrow>G* \<Gamma>" by (auto intro: rtranclp.rtrancl_refl)
next
  show "\<forall>\<Gamma> \<Delta> \<Theta>. \<Gamma> \<rightarrow>G* \<Delta> \<longrightarrow> \<Delta> \<rightarrow>G* \<Theta> \<longrightarrow> \<Gamma> \<rightarrow>G* \<Theta>"
    by (auto intro: rtranclp_trans)
next
  show "\<forall>\<Gamma> \<in> ReachG. \<forall>\<Delta>. \<Gamma> \<rightarrow>G* \<Delta> \<longrightarrow> \<Delta> \<rightarrow>G* \<Gamma> \<longrightarrow> \<Gamma> = \<Delta>"
  proof (intro ballI allI impI)
    fix \<Gamma> \<Delta> assume g: "\<Gamma> \<in> ReachG" and a: "\<Gamma> \<rightarrow>G* \<Delta>" and b: "\<Delta> \<rightarrow>G* \<Gamma>"
    show "\<Gamma> = \<Delta>" by (rule reach_antisym[OF reachable_well_formed[OF g] a b])
  qed
qed

text \<open>Corollary 4.3 (the initial configuration is the least element).\<close>

theorem least_element:
  shows "\<Gamma>0 \<in> ReachG" and "\<And>\<Gamma>. \<Gamma> \<in> ReachG \<Longrightarrow> \<Gamma>0 \<rightarrow>G* \<Gamma>"
proof -
  show "\<Gamma>0 \<in> ReachG" by (simp add: reach_iff)
next
  fix \<Gamma> assume "\<Gamma> \<in> ReachG"
  thus "\<Gamma>0 \<rightarrow>G* \<Gamma>" by (simp add: reach_iff)
qed

theorem root_minimal:
  assumes d: "\<Delta> \<in> ReachG" and b: "\<Delta> \<rightarrow>G* \<Gamma>0"
  shows "\<Delta> = \<Gamma>0"
proof -
  have a: "\<Gamma>0 \<rightarrow>G* \<Delta>" using d by (simp add: reach_iff)
  have "\<Gamma>0 = \<Delta>" by (rule reach_antisym[OF well_formed_\<Gamma>0 a b])
  thus ?thesis by (rule sym)
qed

theorem unique_minimal:
  assumes g: "\<Gamma> \<in> ReachG" and m: "\<forall>\<Delta> \<in> ReachG. \<Delta> \<rightarrow>G* \<Gamma> \<longrightarrow> \<Delta> = \<Gamma>"
  shows "\<Gamma> = \<Gamma>0"
proof -
  have g0: "\<Gamma>0 \<in> ReachG" by (simp add: reach_iff)
  have a: "\<Gamma>0 \<rightarrow>G* \<Gamma>" using g by (simp add: reach_iff)
  have "\<Gamma>0 = \<Gamma>" using m g0 a by blast
  thus ?thesis by (rule sym)
qed

(* ========================================================================= *)
(* Part 5 : Disjoint subtrees                                                *)
(* ========================================================================= *)

lemma ancestors_comparable:
  assumes r2: "\<Gamma>2 \<in> ReachG" and r1: "\<Gamma>1 \<in> ReachG" and a1: "\<Gamma>1 \<rightarrow>G* \<Delta>"
  shows "\<Gamma>2 \<rightarrow>G* \<Delta> \<longrightarrow> \<Gamma>1 \<rightarrow>G* \<Gamma>2 \<or> \<Gamma>2 \<rightarrow>G* \<Gamma>1"
  using a1
proof (induction rule: rtranclp_induct)
  case base
  show ?case by blast
next
  case (step y z)
  show ?case
  proof
    assume h: "\<Gamma>2 \<rightarrow>G* z"
    from rtranclp_last_step[OF h] show "\<Gamma>1 \<rightarrow>G* \<Gamma>2 \<or> \<Gamma>2 \<rightarrow>G* \<Gamma>1"
    proof
      assume hz: "z = \<Gamma>2"
      have "\<Gamma>1 \<rightarrow>G* z"
        by (rule rtranclp.rtrancl_into_rtrancl[OF step.hyps(1) step.hyps(2)])
      hence "\<Gamma>1 \<rightarrow>G* \<Gamma>2" using hz by simp
      thus ?thesis by blast
    next
      assume "\<exists>q. \<Gamma>2 \<rightarrow>G* q \<and> q \<rightarrow>G z"
      then obtain q where q1: "\<Gamma>2 \<rightarrow>G* q" and q2: "q \<rightarrow>G z" by blast
      have g2: "\<Gamma>0 \<rightarrow>G* \<Gamma>2" using r2 by (simp add: reach_iff)
      have g1: "\<Gamma>0 \<rightarrow>G* \<Gamma>1" using r1 by (simp add: reach_iff)
      have rq: "\<Gamma>0 \<rightarrow>G* q" by (rule rtranclp_trans[OF g2 q1])
      have ry: "\<Gamma>0 \<rightarrow>G* y" by (rule rtranclp_trans[OF g1 step.hyps(1)])
      have yq: "y = q"
        by (rule step_pred_unique[OF wf_of_reach[OF ry] wf_of_reach[OF rq]
                                     step.hyps(2) q2])
      have "\<Gamma>2 \<rightarrow>G* y" using q1 yq by simp
      with step.IH show ?thesis by blast
    qed
  qed
qed

lemma sibling_not_below:
  assumes p: "p \<in> ReachG" and s1: "p \<rightarrow>G \<Gamma>1" and s2: "p \<rightarrow>G \<Gamma>2"
      and ne: "\<Gamma>1 \<noteq> \<Gamma>2"
  shows "\<not> (\<Gamma>1 \<rightarrow>G* \<Gamma>2)"
proof
  assume h: "\<Gamma>1 \<rightarrow>G* \<Gamma>2"
  from rtranclp_last_step[OF h] ne obtain q
    where q1: "\<Gamma>1 \<rightarrow>G* q" and q2: "q \<rightarrow>G \<Gamma>2" by blast
  have r1: "\<Gamma>1 \<in> ReachG" by (rule reach_step[OF p s1])
  have g1: "\<Gamma>0 \<rightarrow>G* \<Gamma>1" using r1 by (simp add: reach_iff)
  have rq: "\<Gamma>0 \<rightarrow>G* q" by (rule rtranclp_trans[OF g1 q1])
  have gp: "\<Gamma>0 \<rightarrow>G* p" using p by (simp add: reach_iff)
  have qp: "q = p"
    by (rule step_pred_unique[OF wf_of_reach[OF rq] wf_of_reach[OF gp] q2 s2])
  have "\<Gamma>1 \<rightarrow>G* p" using q1 qp by simp
  moreover have "\<not> (\<Gamma>1 \<rightarrow>G* p)" by (rule acyclic_reach[OF p s1])
  ultimately show False by blast
qed

text \<open>Corollary 4.2 (Disjoint Subtrees): the subtrees below distinct siblings are disjoint.\<close>

theorem disjoint_subtrees:
  assumes p: "p \<in> ReachG" and s1: "p \<rightarrow>G \<Gamma>1" and s2: "p \<rightarrow>G \<Gamma>2"
      and ne: "\<Gamma>1 \<noteq> \<Gamma>2"
  shows "{\<Delta>. \<Gamma>1 \<rightarrow>G* \<Delta>} \<inter> {\<Delta>. \<Gamma>2 \<rightarrow>G* \<Delta>} = {}"
proof (rule equals0I)
  fix \<Delta> assume d: "\<Delta> \<in> {\<Delta>. \<Gamma>1 \<rightarrow>G* \<Delta>} \<inter> {\<Delta>. \<Gamma>2 \<rightarrow>G* \<Delta>}"
  hence d1: "\<Gamma>1 \<rightarrow>G* \<Delta>" and d2: "\<Gamma>2 \<rightarrow>G* \<Delta>" by auto
  have r1: "\<Gamma>1 \<in> ReachG" by (rule reach_step[OF p s1])
  have r2: "\<Gamma>2 \<in> ReachG" by (rule reach_step[OF p s2])
  from ancestors_comparable[OF r2 r1 d1] d2
  have cmp: "\<Gamma>1 \<rightarrow>G* \<Gamma>2 \<or> \<Gamma>2 \<rightarrow>G* \<Gamma>1" by blast
  from cmp show False
  proof
    assume "\<Gamma>1 \<rightarrow>G* \<Gamma>2"
    thus False using sibling_not_below[OF p s1 s2 ne] by blast
  next
    assume "\<Gamma>2 \<rightarrow>G* \<Gamma>1"
    thus False using sibling_not_below[OF p s2 s1 ne[symmetric]] by blast
  qed
qed

(* ========================================================================= *)
(* Part 6 : Semantic self-containment                                        *)
(* ========================================================================= *)

text \<open>
  Whether a configuration has a successor depends only on (P, I, C) and the fixed
  graph; the committed sequence R is never inspected.
\<close>

lemma enabled_iff:
  "(\<exists>\<Gamma>'. (P, R, I, C) \<rightarrow>G \<Gamma>') \<longleftrightarrow>
     (C \<noteq> {} \<or> (C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I))"
proof
  assume "\<exists>\<Gamma>'. (P, R, I, C) \<rightarrow>G \<Gamma>'"
  then obtain \<Gamma>' where st: "(P, R, I, C) \<rightarrow>G \<Gamma>'" by blast
  from st[unfolded step_unfold]
  show "C \<noteq> {} \<or> (C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I)" by blast
next
  assume h: "C \<noteq> {} \<or> (C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I)"
  from h show "\<exists>\<Gamma>'. (P, R, I, C) \<rightarrow>G \<Gamma>'"
  proof
    assume "C \<noteq> {}"
    then obtain v where vC: "v \<in> C" by blast
    have "(P, R, I, C) \<rightarrow>G (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))"
      by (rule step.Add[OF vC refl])
    thus ?thesis by blast
  next
    assume "C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I"
    hence c: "C = {}" and ne: "I \<noteq> {}" and mx: "is_maximal_indep P I" by blast+
    have "(P, R, I, C) \<rightarrow>G (P - I, R @ [I], {}, P - I)"
      by (rule step.Commit[OF c ne mx])
    thus ?thesis by blast
  qed
qed

text \<open>Proposition 4.1 (Self-Containment).\<close>

theorem self_containment:
  shows "(P, R, I, C) \<rightarrow>G \<Gamma>' \<longleftrightarrow>
           (\<exists>v. v \<in> C \<and> \<Gamma>' = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))) \<or>
           (C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I \<and>
              \<Gamma>' = (P - I, R @ [I], {}, P - I))"
    and "(\<exists>\<Gamma>'. (P, R, I, C) \<rightarrow>G \<Gamma>') \<longleftrightarrow> (\<exists>\<Gamma>'. (P, S, I, C) \<rightarrow>G \<Gamma>')"
proof -
  show "(P, R, I, C) \<rightarrow>G \<Gamma>' \<longleftrightarrow>
           (\<exists>v. v \<in> C \<and> \<Gamma>' = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))) \<or>
           (C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I \<and>
              \<Gamma>' = (P - I, R @ [I], {}, P - I))"
    by (rule step_unfold)
next
  show "(\<exists>\<Gamma>'. (P, R, I, C) \<rightarrow>G \<Gamma>') \<longleftrightarrow> (\<exists>\<Gamma>'. (P, S, I, C) \<rightarrow>G \<Gamma>')"
    by (simp only: enabled_iff)
qed

text \<open>Every reachable configuration has finitely many successors (finite branching).\<close>

theorem finite_branching:
  assumes "\<Gamma> \<in> ReachG"
  shows "finite {\<Gamma>'. \<Gamma> \<rightarrow>G \<Gamma>'}"
proof (rule finite_subset[OF _ finite_ReachG])
  show "{\<Gamma>'. \<Gamma> \<rightarrow>G \<Gamma>'} \<subseteq> ReachG"
    by (auto intro: reach_step[OF assms])
qed

end
end
