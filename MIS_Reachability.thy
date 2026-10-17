theory MIS_Reachability
  imports MIS_Structure
begin

context fixed_graph
begin

text \<open>
  P2: structural characterisation of the reachable configurations.

  An RMIS history records successive non-empty maximal independent sets, each maximal
  in the residual pool left by its predecessors.  The pool after a history R is V minus
  the vertices already committed.  Theorem reachable_characterisation shows
  ReachG = reach_form, and exact_cardinality counts it.
\<close>

definition pool :: "'a set list \<Rightarrow> 'a set" where
  "pool R = V - \<Union> (set R)"

inductive rmis :: "'a set list \<Rightarrow> bool" where
  rmis_nil: "rmis []"
| rmis_snoc:
    "\<lbrakk> rmis R; pool R \<noteq> {}; is_maximal_indep (pool R) M \<rbrakk>
     \<Longrightarrow> rmis (R @ [M])"

definition reach_form :: "'a config set" where
  "reach_form =
    {(pool R, R, I, candidate_set (pool R) I) | R I.
       rmis R \<and> I \<subseteq> pool R \<and> is_indep I}"

lemma pool_subset_V: "pool R \<subseteq> V"
  unfolding pool_def by auto

lemma pool_nil: "pool [] = V"
  unfolding pool_def by simp

lemma pool_snoc: "pool (R @ [M]) = pool R - M"
  unfolding pool_def by auto

lemma reach_form_intro:
  assumes "rmis R" "I \<subseteq> pool R" "is_indep I"
  shows "(pool R, R, I, candidate_set (pool R) I) \<in> reach_form"
  unfolding reach_form_def using assms by blast

lemma maximal_indep_nonempty:
  assumes "P \<noteq> {}" "is_maximal_indep P M"
  shows "M \<noteq> {}"
proof
  assume M0: "M = {}"
  obtain v where vP: "v \<in> P" using assms(1) by blast
  hence "v \<in> P - M" using M0 by simp
  hence "\<exists>u \<in> M. (u, v) \<in> E"
    using assms(2) unfolding is_maximal_indep_def by blast
  thus False using M0 by simp
qed

lemma candidate_set_empty_of_maximal:
  assumes Psub: "P \<subseteq> V" and mx: "is_maximal_indep P M"
  shows "candidate_set P M = {}"
proof (rule equals0I)
  fix x assume xC: "x \<in> candidate_set P M"
  have Msub: "M \<subseteq> P" and Mind: "is_indep M"
    using mx unfolding is_maximal_indep_def by auto
  have finM: "finite M" by (rule finite_indep[OF Mind])
  have xP: "x \<in> P" and xnot: "x \<notin> M"
    and noE: "\<forall>u \<in> M. (u, x) \<notin> E"
    using candidate_set_mem_iff[OF finM] xC by auto
  have xPM: "x \<in> P - M" using xP xnot by simp
  have "\<exists>u \<in> M. (u, x) \<in> E"
    using mx xPM unfolding is_maximal_indep_def by blast
  thus False using noE by blast
qed

text \<open>Every independent subset of a pool is reached from the phase root by its canonical ADD path.\<close>

lemma add_path_to_indep:
  assumes Isub: "I \<subseteq> P" and Iind: "is_indep I"
  shows "reachable (P, R, {}, P) (P, R, I, candidate_set P I)"
proof -
  have finI: "finite I" by (rule finite_indep[OF Iind])
  obtain xs where xs_set: "set xs = I" and xs_sorted: "sorted_wrt (<) xs"
    and xs_distinct: "distinct xs"
    using exists_sorted_enum[OF finI] by blast
  have xs_sub: "set xs \<subseteq> P" using xs_set Isub by simp
  have xs_ind: "is_indep (set xs)" using xs_set Iind by simp
  have p0: "add_path_seq P R xs (set xs) (candidate_set P (set xs))"
    by (rule list_to_add_path_seq[OF xs_sorted xs_distinct xs_sub xs_ind])
  have p1: "add_path_seq P R xs I (candidate_set P I)"
    using p0[unfolded xs_set] .
  show ?thesis by (rule add_path_seq_imp_reachable[OF p1])
qed

text \<open>The phase-root configuration is reachable for every RMIS history.\<close>

lemma phase_root_reachable:
  assumes "rmis R"
  shows "reachable \<Gamma>0 (pool R, R, {}, pool R)"
  using assms
proof (induction rule: rmis.induct)
  case rmis_nil
  have e: "(pool [], ([] :: 'a set list), ({} :: 'a set), pool []) = \<Gamma>0"
    by (simp add: pool_nil \<Gamma>0_def)
  show ?case by (subst e) (rule rtranclp.rtrancl_refl)
next
  case (rmis_snoc R M)
  have prev: "reachable \<Gamma>0 (pool R, R, {}, pool R)" by (rule rmis_snoc.IH)
  have Pne: "pool R \<noteq> {}" by (rule rmis_snoc.hyps(2))
  have mx: "is_maximal_indep (pool R) M" by (rule rmis_snoc.hyps(3))
  have Msub: "M \<subseteq> pool R" and Mind: "is_indep M"
    using mx unfolding is_maximal_indep_def by auto
  have finM: "finite M" by (rule finite_indep[OF Mind])
  obtain xs where xs_set: "set xs = M" and xs_sorted: "sorted_wrt (<) xs"
    and xs_distinct: "distinct xs"
    using exists_sorted_enum[OF finM] by blast
  have xs_sub: "set xs \<subseteq> pool R" using xs_set Msub by simp
  have xs_ind: "is_indep (set xs)" using xs_set Mind by simp
  have p0: "add_path_seq (pool R) R xs (set xs) (candidate_set (pool R) (set xs))"
    by (rule list_to_add_path_seq[OF xs_sorted xs_distinct xs_sub xs_ind])
  have p1: "add_path_seq (pool R) R xs M (candidate_set (pool R) M)"
    using p0[unfolded xs_set] .
  have add_reach: "reachable (pool R, R, {}, pool R) (pool R, R, M, candidate_set (pool R) M)"
    by (rule add_path_seq_imp_reachable[OF p1])
  have cand0: "candidate_set (pool R) M = {}"
    by (rule candidate_set_empty_of_maximal[OF pool_subset_V mx])
  have add_reach': "reachable (pool R, R, {}, pool R) (pool R, R, M, {})"
    using add_reach cand0 by simp
  have Mne: "M \<noteq> {}" by (rule maximal_indep_nonempty[OF Pne mx])
  have commit: "(pool R, R, M, {}) \<rightarrow>G (pool R - M, R @ [M], {}, pool R - M)"
    by (rule step.Commit[OF refl Mne mx])
  have add_commit: "reachable (pool R, R, {}, pool R) (pool R - M, R @ [M], {}, pool R - M)"
    by (rule rtranclp.rtrancl_into_rtrancl[OF add_reach' commit])
  have total: "reachable \<Gamma>0 (pool R - M, R @ [M], {}, pool R - M)"
    by (rule rtranclp_trans[OF prev add_commit])
  show ?case using total by (simp add: pool_snoc)
qed

text \<open>A transition preserves the RMIS property of the committed history.\<close>

lemma rmis_preserved_step:
  assumes r: "rmis R" and wf: "well_formed (P, R, I, C)"
      and st: "(P, R, I, C) \<rightarrow>G (P', R', I', C')"
  shows "rmis R'"
proof -
  note parts = wf_parts[OF wf]
  from st[unfolded step_unfold] show ?thesis
  proof
    assume "\<exists>v. v \<in> C \<and> (P', R', I', C') = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))"
    then obtain v where
      e: "(P', R', I', C') = (P, R, I \<union> {v}, candidate_set P (I \<union> {v}))" by blast
    hence "R' = R" by simp
    thus ?thesis using r by simp
  next
    assume h: "C = {} \<and> I \<noteq> {} \<and> is_maximal_indep P I \<and>
               (P', R', I', C') = (P - I, R @ [I], {}, P - I)"
    hence ne: "I \<noteq> {}" and mx: "is_maximal_indep P I"
      and e: "(P', R', I', C') = (P - I, R @ [I], {}, P - I)" by blast+
    have R'eq: "R' = R @ [I]" using e by simp
    have pool_eq: "pool R = P" using parts(7) unfolding pool_def by simp
    have Pne: "P \<noteq> {}" using parts(3) ne by auto
    have a: "pool R \<noteq> {}" using pool_eq Pne by simp
    have b: "is_maximal_indep (pool R) I" using mx pool_eq by simp
    from rmis.rmis_snoc[OF r a b] show ?thesis using R'eq by simp
  qed
qed

lemma rmis_invariant:
  assumes "\<Gamma>0 \<rightarrow>G* \<Gamma>"
  shows "well_formed \<Gamma> \<and> rmis (fst (snd \<Gamma>))"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case unfolding \<Gamma>0_def using well_formed_\<Gamma>0[unfolded \<Gamma>0_def] rmis.rmis_nil by simp
next
  case (step y z)
  obtain P R I C where y: "y = (P, R, I, C)" by (cases y) auto
  obtain P' R' I' C' where z: "z = (P', R', I', C')" by (cases z) auto
  have ih: "well_formed (P, R, I, C) \<and> rmis R" using step.IH y by simp
  hence wfy: "well_formed (P, R, I, C)" and ry: "rmis R" by blast+
  have st: "(P, R, I, C) \<rightarrow>G (P', R', I', C')" using step.hyps(2) y z by simp
  have wfz: "well_formed (P', R', I', C')"
    by (rule invariant_preservation[OF st wfy])
  have rz: "rmis R'" by (rule rmis_preserved_step[OF ry wfy st])
  show ?case using wfz rz z by simp
qed

lemma reachable_has_rmis:
  assumes "(P, R, I, C) \<in> ReachG"
  shows "rmis R"
proof -
  have "\<Gamma>0 \<rightarrow>G* (P, R, I, C)" using assms unfolding ReachG_def by simp
  from rmis_invariant[OF this] show ?thesis by simp
qed

lemma ReachG_subset_reach_form: "ReachG \<subseteq> reach_form"
proof
  fix \<Gamma> assume g: "\<Gamma> \<in> ReachG"
  obtain P R I C where geq: "\<Gamma> = (P, R, I, C)" by (cases \<Gamma>) auto
  have gR: "(P, R, I, C) \<in> ReachG" using g geq by simp
  have wf: "well_formed (P, R, I, C)" by (rule reachable_well_formed[OF gR])
  have rm: "rmis R" by (rule reachable_has_rmis[OF gR])
  note parts = wf_parts[OF wf]
  have pool_eq: "pool R = P" using parts(7) unfolding pool_def by simp
  have Isub: "I \<subseteq> pool R" using parts(3) pool_eq by simp
  have mem: "(pool R, R, I, candidate_set (pool R) I) \<in> reach_form"
    by (rule reach_form_intro[OF rm Isub parts(2)])
  have e: "(pool R, R, I, candidate_set (pool R) I) = (P, R, I, C)"
    using parts(4) pool_eq by simp
  have "(P, R, I, C) \<in> reach_form" by (metis e mem)
  thus "\<Gamma> \<in> reach_form" using geq by simp
qed

lemma reach_form_subset_ReachG: "reach_form \<subseteq> ReachG"
proof
  fix \<Gamma> assume g: "\<Gamma> \<in> reach_form"
  then obtain R I where geq: "\<Gamma> = (pool R, R, I, candidate_set (pool R) I)"
    and rm: "rmis R" and Isub: "I \<subseteq> pool R" and Iind: "is_indep I"
    unfolding reach_form_def by blast
  have root: "reachable \<Gamma>0 (pool R, R, {}, pool R)"
    by (rule phase_root_reachable[OF rm])
  have add: "reachable (pool R, R, {}, pool R) (pool R, R, I, candidate_set (pool R) I)"
    by (rule add_path_to_indep[OF Isub Iind])
  have p: "\<Gamma>0 \<rightarrow>G* (pool R, R, I, candidate_set (pool R) I)"
    by (rule rtranclp_trans[OF root add])
  show "\<Gamma> \<in> ReachG" unfolding ReachG_def using p geq by simp
qed

theorem reachable_characterisation: "ReachG = reach_form"
  using ReachG_subset_reach_form reach_form_subset_ReachG by blast

corollary reachable_iff_rmis:
  assumes wf: "well_formed (P, R, I, C)"
  shows "(P, R, I, C) \<in> ReachG \<longleftrightarrow> rmis R"
proof
  assume "(P, R, I, C) \<in> ReachG"
  thus "rmis R" by (rule reachable_has_rmis)
next
  assume rm: "rmis R"
  note parts = wf_parts[OF wf]
  have pool_eq: "pool R = P" using parts(7) unfolding pool_def by simp
  have Isub: "I \<subseteq> pool R" using parts(3) pool_eq by simp
  have mem: "(pool R, R, I, candidate_set (pool R) I) \<in> reach_form"
    by (rule reach_form_intro[OF rm Isub parts(2)])
  have e: "(pool R, R, I, candidate_set (pool R) I) = (P, R, I, C)"
    using parts(4) pool_eq by simp
  have "(P, R, I, C) \<in> reach_form" by (metis e mem)
  thus "(P, R, I, C) \<in> ReachG" using reachable_characterisation by simp
qed

text \<open>
  Exact state count: every RMIS history contributes one configuration for each
  independent subset of its residual pool.
\<close>

definition rmis_sequences :: "'a set list set" where
  "rmis_sequences = {R. rmis R}"

definition independent_subsets :: "'a set \<Rightarrow> 'a set set" where
  "independent_subsets P = {I. I \<subseteq> P \<and> is_indep I}"

definition pair_space :: "('a set list \<times> 'a set) set" where
  "pair_space = (SIGMA R:rmis_sequences. independent_subsets (pool R))"

definition decode_pair :: "'a set list \<times> 'a set \<Rightarrow> 'a config" where
  "decode_pair q = (pool (fst q), fst q, snd q, candidate_set (pool (fst q)) (snd q))"

lemma finite_rmis_sequences: "finite rmis_sequences"
proof -
  have eq: "rmis_sequences = (\<lambda>\<Gamma>. fst (snd \<Gamma>)) ` ReachG"
  proof (rule set_eqI)
    fix R
    show "R \<in> rmis_sequences \<longleftrightarrow> R \<in> (\<lambda>\<Gamma>. fst (snd \<Gamma>)) ` ReachG"
    proof
      assume "R \<in> rmis_sequences"
      hence rm: "rmis R" unfolding rmis_sequences_def by simp
      have root: "reachable \<Gamma>0 (pool R, R, {}, pool R)"
        by (rule phase_root_reachable[OF rm])
      have mem: "(pool R, R, {}, pool R) \<in> ReachG"
        using root unfolding ReachG_def by simp
      show "R \<in> (\<lambda>\<Gamma>. fst (snd \<Gamma>)) ` ReachG"
        by (rule image_eqI[OF _ mem]) simp
    next
      assume "R \<in> (\<lambda>\<Gamma>. fst (snd \<Gamma>)) ` ReachG"
      then obtain \<Gamma> where g: "\<Gamma> \<in> ReachG" and h: "R = fst (snd \<Gamma>)" by blast
      obtain P R0 I C where geq: "\<Gamma> = (P, R0, I, C)" by (cases \<Gamma>) auto
      have "rmis R0" by (rule reachable_has_rmis[of P R0 I C]) (use g geq in simp)
      thus "R \<in> rmis_sequences" using h geq unfolding rmis_sequences_def by simp
    qed
  qed
  have "finite ((\<lambda>\<Gamma>. fst (snd \<Gamma>)) ` ReachG)"
    by (rule finite_imageI[OF finite_ReachG])
  thus ?thesis using eq by simp
qed

lemma finite_independent_subsets:
  assumes "R \<in> rmis_sequences"
  shows "finite (independent_subsets (pool R))"
proof -
  have fin_pool: "finite (pool R)" by (rule finite_sub[OF pool_subset_V])
  have sub: "independent_subsets (pool R) \<subseteq> Pow (pool R)"
    unfolding independent_subsets_def by auto
  show ?thesis by (rule finite_subset[OF sub]) (use fin_pool in simp)
qed

lemma decode_pair_inj: "inj_on decode_pair pair_space"
  unfolding inj_on_def decode_pair_def by auto

lemma decode_pair_image: "decode_pair ` pair_space = reach_form"
proof (rule set_eqI)
  fix \<Gamma>
  show "\<Gamma> \<in> decode_pair ` pair_space \<longleftrightarrow> \<Gamma> \<in> reach_form"
  proof
    assume "\<Gamma> \<in> decode_pair ` pair_space"
    then obtain q where q1: "q \<in> pair_space" and q2: "\<Gamma> = decode_pair q" by blast
    obtain R I where qe: "q = (R, I)" by (cases q) auto
    have "R \<in> rmis_sequences" and "I \<in> independent_subsets (pool R)"
      using q1 qe unfolding pair_space_def by simp_all
    hence h: "rmis R" "I \<subseteq> pool R" "is_indep I"
      unfolding rmis_sequences_def independent_subsets_def by simp_all
    have "(pool R, R, I, candidate_set (pool R) I) \<in> reach_form"
      by (rule reach_form_intro[OF h])
    thus "\<Gamma> \<in> reach_form" using q2 qe by (simp add: decode_pair_def)
  next
    assume "\<Gamma> \<in> reach_form"
    then obtain R I where geq: "\<Gamma> = (pool R, R, I, candidate_set (pool R) I)"
      and rm: "rmis R" and Isub: "I \<subseteq> pool R" and Iind: "is_indep I"
      unfolding reach_form_def by blast
    have "(R, I) \<in> pair_space"
      unfolding pair_space_def rmis_sequences_def independent_subsets_def
      using rm Isub Iind by simp
    thus "\<Gamma> \<in> decode_pair ` pair_space"
      by (rule image_eqI[rotated]) (simp add: decode_pair_def geq)
  qed
qed

lemma finite_pair_space: "finite pair_space"
  unfolding pair_space_def
  by (rule finite_SigmaI[OF finite_rmis_sequences finite_independent_subsets])

theorem exact_cardinality:
  "card ReachG = (\<Sum>R\<in>rmis_sequences. card (independent_subsets (pool R)))"
proof -
  have finR: "finite rmis_sequences" by (rule finite_rmis_sequences)
  have finFib: "\<forall>R \<in> rmis_sequences. finite (independent_subsets (pool R))"
    using finite_independent_subsets by blast
  have cardSigma:
    "card pair_space = (\<Sum>R\<in>rmis_sequences. card (independent_subsets (pool R)))"
    unfolding pair_space_def by (rule card_SigmaI[OF finR finFib])
  have cardImage: "card (decode_pair ` pair_space) = card pair_space"
    by (rule card_image[OF decode_pair_inj])
  have "card reach_form = card pair_space"
    using decode_pair_image cardImage by simp
  thus ?thesis using reachable_characterisation cardSigma by simp
qed

end
end
