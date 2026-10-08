theory MIS_Cover_Semantics
  imports Main "HOL-Library.Product_Lexorder"
begin

type_synonym 'b config = "'b set \<times> ('b set) list \<times> 'b set \<times> 'b set"

locale fixed_graph =
  fixes V :: "'a::linorder set"
  and E :: "('a \<times> 'a) set"
  assumes finite_V: "finite V"
  and sym_E: "sym E"
  and irrefl_E: "irrefl E"
begin

definition is_indep :: "'a set \<Rightarrow> bool" where
  "is_indep S \<equiv> S \<subseteq> V \<and> (\<forall>u\<in>S. \<forall>v\<in>S. u \<noteq> v \<longrightarrow> (u, v) \<notin> E)"

definition is_maximal_indep :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_maximal_indep P S \<equiv> S \<subseteq> P \<and> is_indep S \<and> (\<forall>v \<in> P - S. \<exists>u \<in> S. (u, v) \<in> E)"

definition candidate_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "candidate_set P I =
    (if I = {} then P
     else {v \<in> P - I. v > Max I \<and> (\<forall>u \<in> I. (u, v) \<notin> E)})"

definition well_formed :: "'a config \<Rightarrow> bool" where
  "well_formed \<Gamma> \<equiv> case \<Gamma> of (P, R, I, C) \<Rightarrow>
    P \<subseteq> V \<and>
    is_indep I \<and>
    I \<subseteq> P \<and>
    C = candidate_set P I \<and>
    (\<forall>m \<in> set R. is_indep m \<and> m \<noteq> {}) \<and>
    (\<forall>i < length R. \<forall>j < length R. i \<noteq> j \<longrightarrow> R ! i \<inter> R ! j = {}) \<and>
    P = V - (\<Union> (set R))"

definition \<Gamma>0 :: "'a config" where
  "\<Gamma>0 = (V, [], {}, V)"

inductive step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix "\<rightarrow>G" 50) where
  Add: "\<lbrakk> v \<in> C; C' = candidate_set P (I \<union> {v}) \<rbrakk>
        \<Longrightarrow> (P, R, I, C) \<rightarrow>G (P, R, I \<union> {v}, C')"
| Commit: "\<lbrakk> C = {}; I \<noteq> {}; is_maximal_indep P I \<rbrakk>
        \<Longrightarrow> (P, R, I, C) \<rightarrow>G (P - I, R @ [I], {}, P - I)"

abbreviation reachable :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix "\<rightarrow>G*" 50) where
  "reachable \<equiv> rtranclp step"

definition ReachG :: "'a config set" where
  "ReachG = {\<Gamma>. \<Gamma>0 \<rightarrow>G* \<Gamma>}"

definition \<rho> :: "'a config \<Rightarrow> (nat \<times> nat)" where
  "\<rho> \<Gamma> = (case \<Gamma> of (P, R, I, C) \<Rightarrow> (card P, card P - card I))"

text \<open>Basic facts about the graph and candidate sets.\<close>

lemma edge_sym: "(a, b) \<in> E \<Longrightarrow> (b, a) \<in> E"
  using sym_E unfolding sym_def by blast

lemma finite_sub: 
  assumes "P \<subseteq> V"
  shows "finite P"
  using assms finite_V by (rule finite_subset)

lemma finite_indep:
  assumes "is_indep S"
  shows "finite S"
proof -
  have "S \<subseteq> V" using assms unfolding is_indep_def by simp
  thus ?thesis by (rule finite_sub)
qed

lemma candidate_set_empty: "candidate_set P {} = P"
  unfolding candidate_set_def by simp

lemma candidate_set_mem_iff:
  assumes "finite I"
  shows "x \<in> candidate_set P I \<longleftrightarrow>
    (x \<in> P \<and> x \<notin> I \<and> (\<forall>u \<in> I. u < x) \<and> (\<forall>u \<in> I. (u, x) \<notin> E))"
proof (cases "I = {}")
  case True
  thus ?thesis unfolding candidate_set_def by simp
next
  case False
  have iff: "Max I < x \<longleftrightarrow> (\<forall>u \<in> I. u < x)" 
    by (rule Max_less_iff[OF assms False])
  show ?thesis unfolding candidate_set_def using False iff by auto
qed

lemma indep_add:
  assumes "is_indep I" "v \<in> V" "\<forall>u \<in> I. (u, v) \<notin> E"
  shows "is_indep (I \<union> {v})"
proof -
  have IV: "I \<subseteq> V" using assms(1) unfolding is_indep_def by simp
  have inner: "\<forall>u \<in> I. \<forall>w \<in> I. u \<noteq> w \<longrightarrow> (u, w) \<notin> E"
    using assms(1) unfolding is_indep_def by simp
  have "\<forall>u \<in> I \<union> {v}. \<forall>w \<in> I \<union> {v}. u \<noteq> w \<longrightarrow> (u, w) \<notin> E"
  proof (intro ballI impI)
    fix u w assume uw: "u \<in> I \<union> {v}" "w \<in> I \<union> {v}" "u \<noteq> w"
    consider (II) "u \<in> I" "w \<in> I" | (vI) "u = v" "w \<in> I" | (Iv) "u \<in> I" "w = v"
      using uw by auto
    thus "(u, w) \<notin> E"
    proof cases
      case II
      thus ?thesis using inner uw(3) by blast
    next
      case vI
      show ?thesis
      proof
        assume "(u, w) \<in> E"
        hence "(w, u) \<in> E" by (rule edge_sym)
        thus False using assms(3) vI by auto
      qed
    next
      case Iv
      thus ?thesis using assms(3) by auto
    qed
  qed
  moreover have "I \<union> {v} \<subseteq> V" using IV assms(2) by auto
  ultimately show ?thesis unfolding is_indep_def by blast
qed

text \<open>Unfolding lemmas for well_formed.\<close>

lemma well_formed_simp:
  "well_formed (P, R, I, C) \<longleftrightarrow>
    (P \<subseteq> V \<and> is_indep I \<and> I \<subseteq> P \<and> C = candidate_set P I \<and>
     (\<forall>m \<in> set R. is_indep m \<and> m \<noteq> {}) \<and>
     (\<forall>i < length R. \<forall>j < length R. i \<noteq> j \<longrightarrow> R ! i \<inter> R ! j = {}) \<and>
     P = V - (\<Union> (set R)))"
  unfolding well_formed_def by simp

lemma wf_parts:
  assumes "well_formed (P, R, I, C)"
  shows "P \<subseteq> V" "is_indep I" "I \<subseteq> P" "C = candidate_set P I"
    "\<forall>m \<in> set R. is_indep m \<and> m \<noteq> {}"
    "\<forall>i < length R. \<forall>j < length R. i \<noteq> j \<longrightarrow> R ! i \<inter> R ! j = {}"
    "P = V - (\<Union> (set R))"
  using assms unfolding well_formed_simp by auto

text \<open>Tie to Definition 3.4 of the paper: under well-formedness, the ADD update
  C' = {u \<in> C | u > v \<and> (u,v) \<notin> E} coincides with the candidate-set definition.\<close>

lemma add_candidate_set_eq:
  assumes wf: "well_formed (P, R, I, C)" and vC: "v \<in> C"
  shows "{u \<in> C. u > v \<and> (u, v) \<notin> E} = candidate_set P (I \<union> {v})"
proof -
  note p = wf_parts[OF wf]
  have finI: "finite I" by (rule finite_indep[OF p(2)])
  have finI': "finite (I \<union> {v})" using finI by simp
  have "v \<in> candidate_set P I" using vC p(4) by simp
  hence v1: "v \<in> P" and v2: "v \<notin> I" and v3: "\<forall>u \<in> I. u < v" and v4: "\<forall>u \<in> I. (u, v) \<notin> E"
    using candidate_set_mem_iff[OF finI] by auto
  show ?thesis
  proof (rule set_eqI)
    fix u
    have cs1: "u \<in> candidate_set P (I \<union> {v}) \<longleftrightarrow>
        (u \<in> P \<and> u \<notin> I \<union> {v} \<and> (\<forall>w \<in> I \<union> {v}. w < u) \<and> (\<forall>w \<in> I \<union> {v}. (w, u) \<notin> E))"
      by (rule candidate_set_mem_iff[OF finI'])
    have cs2: "u \<in> C \<longleftrightarrow> (u \<in> P \<and> u \<notin> I \<and> (\<forall>w \<in> I. w < u) \<and> (\<forall>w \<in> I. (w, u) \<notin> E))"
      using p(4) candidate_set_mem_iff[OF finI] by simp
    show "u \<in> {u \<in> C. v < u \<and> (u, v) \<notin> E} \<longleftrightarrow> u \<in> candidate_set P (I \<union> {v})"
      unfolding mem_Collect_eq cs1 cs2
    proof (intro iffI)
      assume h: "(u \<in> P \<and> u \<notin> I \<and> (\<forall>w \<in> I. w < u) \<and> (\<forall>w \<in> I. (w, u) \<notin> E)) \<and>
                 v < u \<and> (u, v) \<notin> E"
      have vu: "(v, u) \<notin> E"
      proof
        assume "(v, u) \<in> E"
        hence "(u, v) \<in> E" by (rule edge_sym)
        thus False using h by simp
      qed
      show "u \<in> P \<and> u \<notin> I \<union> {v} \<and> (\<forall>w \<in> I \<union> {v}. w < u) \<and> (\<forall>w \<in> I \<union> {v}. (w, u) \<notin> E)"
        using h vu by auto
    next
      assume h: "u \<in> P \<and> u \<notin> I \<union> {v} \<and> (\<forall>w \<in> I \<union> {v}. w < u) \<and> (\<forall>w \<in> I \<union> {v}. (w, u) \<notin> E)"
      have vu: "(v, u) \<notin> E" using h by auto
      have uv: "(u, v) \<notin> E"
      proof
        assume "(u, v) \<in> E"
        hence "(v, u) \<in> E" by (rule edge_sym)
        thus False using vu by simp
      qed
      have "v < u" using h by auto
      thus "(u \<in> P \<and> u \<notin> I \<and> (\<forall>w \<in> I. w < u) \<and> (\<forall>w \<in> I. (w, u) \<notin> E)) \<and>
            v < u \<and> (u, v) \<notin> E"
        using h uv by auto
    qed
  qed
qed

text \<open>Per-rule lemmas on tuples (no dependence on induction case naming).\<close>

lemma wf_add:
  assumes wf: "well_formed (P, R, I, C)" and vC: "v \<in> C"
      and C': "C' = candidate_set P (I \<union> {v})"
  shows "well_formed (P, R, I \<union> {v}, C')"
proof -
  note p = wf_parts[OF wf]
  have finI: "finite I" by (rule finite_indep[OF p(2)])
  have "v \<in> candidate_set P I" using vC p(4) by simp
  hence v1: "v \<in> P" and v4: "\<forall>u \<in> I. (u, v) \<notin> E"
    using candidate_set_mem_iff[OF finI] by auto
  have vV: "v \<in> V" using v1 p(1) by auto
  have ind': "is_indep (I \<union> {v})" by (rule indep_add[OF p(2) vV v4])
  have sub': "I \<union> {v} \<subseteq> P" using p(3) v1 by auto
  show ?thesis
    unfolding well_formed_simp using p(1) ind' sub' C' p(5) p(6) p(7) by blast
qed

lemma wf_commit:
  assumes wf: "well_formed (P, R, I, C)" and ne: "I \<noteq> {}"
  shows "well_formed (P - I, R @ [I], {}, P - I)"
proof -
  note p = wf_parts[OF wf]
  have R'cls: "\<forall>m \<in> set (R @ [I]). is_indep m \<and> m \<noteq> {}"
    using p(5) p(2) ne by auto
  have disj_new: "\<And>A. A \<in> set R \<Longrightarrow> A \<inter> I = {}"
  proof -
    fix A assume A: "A \<in> set R"
    show "A \<inter> I = {}"
    proof (rule Int_emptyI)
      fix x assume xA: "x \<in> A" and xI: "x \<in> I"
      have "x \<in> \<Union> (set R)" using A xA by auto
      moreover have "x \<in> P" using p(3) xI by auto
      ultimately show False using p(7) by auto
    qed
  qed
  have disj': "\<forall>i < length (R @ [I]). \<forall>j < length (R @ [I]). i \<noteq> j \<longrightarrow>
                 (R @ [I]) ! i \<inter> (R @ [I]) ! j = {}"
  proof (intro allI impI)
    fix i j
    assume i: "i < length (R @ [I])" and j: "j < length (R @ [I])" and ij: "i \<noteq> j"
    have len: "length (R @ [I]) = length R + 1" by simp
    show "(R @ [I]) ! i \<inter> (R @ [I]) ! j = {}"
    proof (cases "i < length R")
      case iR: True
      show ?thesis
      proof (cases "j < length R")
        case jR: True
        have e1: "(R @ [I]) ! i = R ! i" using iR by (simp add: nth_append)
        have e2: "(R @ [I]) ! j = R ! j" using jR by (simp add: nth_append)
        have "R ! i \<inter> R ! j = {}" using p(6) iR jR ij by blast
        thus ?thesis using e1 e2 by simp
      next
        case jR: False
        have jeq: "j = length R" using j jR len by arith
        have e1: "(R @ [I]) ! i = R ! i" using iR by (simp add: nth_append)
        have e2: "(R @ [I]) ! j = I" using jeq by simp
        have "R ! i \<inter> I = {}" by (rule disj_new[OF nth_mem[OF iR]])
        thus ?thesis using e1 e2 by simp
      qed
    next
      case iR: False
      have ieq: "i = length R" using i iR len by arith
      have jR: "j < length R" using j ij ieq len by arith
      have e1: "(R @ [I]) ! i = I" using ieq by simp
      have e2: "(R @ [I]) ! j = R ! j" using jR by (simp add: nth_append)
      have "R ! j \<inter> I = {}" by (rule disj_new[OF nth_mem[OF jR]])
      thus ?thesis using e1 e2 by (simp add: Int_commute)
    qed
  qed
  have P'_eq: "P - I = V - \<Union> (set (R @ [I]))" using p(7) by auto
  have P'V: "P - I \<subseteq> V" using p(1) by auto
  have ind_empty: "is_indep {}" unfolding is_indep_def by simp
  show ?thesis
    unfolding well_formed_simp
    using P'V ind_empty candidate_set_empty R'cls disj' P'_eq by auto
qed

lemma rho_add:
  assumes wf: "well_formed (P, R, I, C)" and vC: "v \<in> C"
  shows "\<rho> (P, R, I \<union> {v}, C') < \<rho> (P, R, I, C)"
proof -
  note p = wf_parts[OF wf]
  have finP: "finite P" by (rule finite_sub[OF p(1)])
  have finI: "finite I" by (rule finite_indep[OF p(2)])
  have "v \<in> candidate_set P I" using vC p(4) by simp
  hence vP: "v \<in> P" and vI: "v \<notin> I"
    using candidate_set_mem_iff[OF finI] by auto
  have c1: "card (I \<union> {v}) = card I + 1" using finI vI by simp
  have "I \<subset> P" using p(3) vP vI by auto
  hence c2: "card I < card P" by (rule psubset_card_mono[OF finP])
  have lt: "card P - card (I \<union> {v}) < card P - card I" using c1 c2 by arith
  show ?thesis unfolding \<rho>_def using lt by simp
qed

lemma rho_commit:
  assumes wf: "well_formed (P, R, I, C)" and ne: "I \<noteq> {}"
  shows "\<rho> (P - I, R @ [I], {}, P - I) < \<rho> (P, R, I, C)"
proof -
  note p = wf_parts[OF wf]
  have finP: "finite P" by (rule finite_sub[OF p(1)])
  have "P - I \<subset> P" using p(3) ne by auto
  hence "card (P - I) < card P" by (rule psubset_card_mono[OF finP])
  thus ?thesis unfolding \<rho>_def by simp
qed

lemma \<rho>_strict_decrease:
  assumes "\<Gamma> \<rightarrow>G \<Gamma>'" "well_formed \<Gamma>"
  shows "\<rho> \<Gamma>' < \<rho> \<Gamma>"
  using assms
proof (induction rule: step.induct)
  case Add
  show ?case using Add.prems Add.hyps by (blast intro: rho_add)
next
  case Commit
  show ?case using Commit.prems Commit.hyps by (blast intro: rho_commit)
qed

lemma invariant_preservation:
  assumes "\<Gamma> \<rightarrow>G \<Gamma>'" "well_formed \<Gamma>"
  shows "well_formed \<Gamma>'"
  using assms
proof (induction rule: step.induct)
  case Add
  show ?case using Add.prems Add.hyps by (blast intro: wf_add)
next
  case Commit
  show ?case using Commit.prems Commit.hyps by (blast intro: wf_commit)
qed

lemma well_formed_\<Gamma>0: "well_formed \<Gamma>0"
  unfolding \<Gamma>0_def well_formed_simp is_indep_def candidate_set_def by simp

theorem reachable_well_formed:
  assumes "\<Gamma> \<in> ReachG"
  shows "well_formed \<Gamma>"
proof -
  from assms have "\<Gamma>0 \<rightarrow>G* \<Gamma>" unfolding ReachG_def by simp
  thus ?thesis
  proof (induction rule: rtranclp_induct)
    case base
    show ?case by (rule well_formed_\<Gamma>0)
  next
    case (step y z)
    thus ?case using invariant_preservation by blast
  qed
qed

end
end
