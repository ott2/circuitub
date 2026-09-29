theory Construction
  imports Count Cover Moduli ExpBound "HOL-Library.FuncSet"
begin

section \<open>Helpers\<close>

text \<open>The test on block weights, independent of the assignment.\<close>

definition passesW :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "passesW k ws ss = distinct (map (\<lambda>p. (fst p + snd p) mod k) (zip ws ss))"

lemma passes_passesW: "passes k \<sigma> Bs ss = passesW k (map (cnt \<sigma>) Bs) ss"
  by (simp add: passes_def passesW_def shifted_def zip_map1 comp_def split_def)

lemma distinct_conv_nth_less:
  "distinct xs \<longleftrightarrow> (\<forall>i j. i < j \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<noteq> xs ! j)"
proof
  assume "distinct xs"
  then show "\<forall>i j. i < j \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<noteq> xs ! j"
    by (auto simp: distinct_conv_nth)
next
  assume h: "\<forall>i j. i < j \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<noteq> xs ! j"
  show "distinct xs"
  proof (subst distinct_conv_nth, intro allI impI)
    fix i j assume i: "i < length xs" and j: "j < length xs" and ij: "i \<noteq> j"
    show "xs ! i \<noteq> xs ! j"
    proof (cases "i < j")
      case True
      then show ?thesis using h j by blast
    next
      case False
      with ij have "j < i" by simp
      then have "xs ! j \<noteq> xs ! i" using h i by blast
      then show ?thesis by simp
    qed
  qed
qed

lemma collide_iff:
  fixes wi wj si sj lj q :: nat
  assumes q: "q > 0" and wj: "wj \<le> lj"
  shows "((wi + (lj - wj) + si) mod q = (lj + sj) mod q) \<longleftrightarrow> ((wi + si) mod q = (wj + sj) mod q)"
proof -
  let ?x = "lj - wj"
  have e1: "wi + (lj - wj) + si = (wi + si) + ?x" by simp
  have e2: "lj + sj = (wj + sj) + ?x" using wj by simp
  have "((wi + si) + ?x) mod q = ((wj + sj) + ?x) mod q \<longleftrightarrow> (wi + si) mod q = (wj + sj) mod q"
  proof
    assume "((wi + si) + ?x) mod q = ((wj + sj) + ?x) mod q"
    then show "(wi + si) mod q = (wj + sj) mod q" using q by (rule mod_add_cancel_nat[rotated])
  next
    assume h: "(wi + si) mod q = (wj + sj) mod q"
    have "(?x + (wi + si)) mod q = (?x + (wj + sj)) mod q" using h by (rule mod_add_right_cong)
    then show "((wi + si) + ?x) mod q = ((wj + sj) + ?x) mod q" by (simp add: add.commute)
  qed
  then show ?thesis by (simp only: e1 e2)
qed

lemma in_concat_map: "x \<in> set (f y) \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<in> set (concat (map f ys))"
  by auto

lemma length_le_concat: "xs \<in> set xss \<Longrightarrow> length xs \<le> length (concat xss)"
  by (induction xss) auto

lemma length_concat_le:
  assumes "\<forall>xs\<in>set xss. length xs \<le> c" shows "length (concat xss) \<le> length xss * c"
  using assms by (induction xss) auto

lemma bsize_le:
  assumes q: "q > 0" and m: "m \<le> q * b" shows "bsize q m \<le> b"
proof -
  obtain q2 where q2: "q = Suc q2" using q by (cases q) auto
  have "m + q2 < (b + 1) * q" using m q2 by (simp add: algebra_simps)
  then have "(m + q2) div q < b + 1" by (rule less_mult_imp_div_less)
  then show ?thesis using q2 by (simp add: bsize_def)
qed

definition Econst :: "nat \<Rightarrow> nat" where
  "Econst D = D * fact D + 1"

section \<open>One induction step: depth \<open>D\<close> to depth \<open>D+1\<close>\<close>

text \<open>
  \<open>F\<close> is the inductive hypothesis: \<open>\<Sigma>\<^sub>D\<close> formulas of size \<open>2\<^sup>C\<^sup>(\<^sup>k\<^sup>'\<^sup>+\<^sup>1\<^sup>)\<close> for every symmetric
  function of at most \<open>k'\<^sup>D\<^sup>-\<^sup>1\<close> literals.  We build \<open>\<Sigma>\<^sub>D\<^sub>+\<^sub>1\<close> formulas for symmetric functions
  of at most \<open>k\<^sup>D\<close> literals, following Section 4 of the paper with \<open>D = d - 1\<close> moduli.
\<close>

locale step =
  fixes D :: nat and k :: nat and C :: nat
    and L :: "'v lit list"
    and F :: "nat \<Rightarrow> 'v lit list \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'v form"
  assumes D2: "2 \<le> D"
    and Lk: "length L \<le> k ^ D"
    and F: "\<And>k' L' g'. length L' \<le> k' ^ (D - 1) \<Longrightarrow>
              SIG D (F k' L' g') \<and> gates (F k' L' g') \<le> 2 ^ (C * (k' + 1)) \<and>
              (\<forall>\<sigma>. eval \<sigma> (F k' L' g') = g' (cnt \<sigma> L'))"
begin

subsection \<open>Moduli and blocks\<close>

definition modl :: "nat \<Rightarrow> nat" where "modl l = modq D k l"
definition blks :: "nat \<Rightarrow> 'v lit list list" where "blks l = blocks (modl l) L"
definition Qb :: nat where "Qb = Econst D * (k + 1)"

lemma modl_pos: "0 < modl l"
  by (simp add: modl_def modq_pos)

lemma modl_gt: "k < modl l"
  using modq_ge[of k D l] by (simp add: modl_def)

lemma modl_le: "l < D \<Longrightarrow> modl l \<le> Qb"
  using modq_le[of l D k] by (simp add: modl_def Qb_def Econst_def)

lemma length_blks [simp]: "length (blks l) = modl l"
  by (simp add: blks_def length_blocks modl_pos)

lemma concat_blks [simp]: "concat (blks l) = L"
  by (simp add: blks_def concat_blocks modl_pos)

lemma blk_len:
  assumes "i < modl l" shows "length (blks l ! i) \<le> k ^ (D - 1)"
proof -
  have D1: "D = Suc (D - 1)" using D2 by simp
  have "length L \<le> k * k ^ (D - 1)" using Lk D1 by (metis power_Suc)
  also have "\<dots> \<le> modl l * k ^ (D - 1)"
    using modl_gt[of l] by (intro mult_right_mono) simp_all
  finally have "bsize (modl l) (length L) \<le> k ^ (D - 1)"
    using modl_pos by (intro bsize_le) simp_all
  moreover have "blks l ! i \<in> set (blocks (modl l) L)"
    using assms by (simp add: blks_def[symmetric])
  ultimately show ?thesis using blocks_lengths[of "modl l" L] by fastforce
qed

lemma cnt_blk_le: "i < modl l \<Longrightarrow> cnt \<sigma> (blks l ! i) \<le> length L"
proof -
  assume i: "i < modl l"
  have "cnt \<sigma> (blks l ! i) \<le> length (blks l ! i)" by (rule cnt_le_length)
  also have "\<dots> \<le> length (concat (blks l))"
    using i by (intro length_le_concat) simp
  finally show ?thesis by simp
qed

subsection \<open>Pair formulas\<close>

definition pairL :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v lit list" where
  "pairL l i j = blks l ! i @ map neg (blks l ! j)"

definition collide :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "collide l j si sj c = ((c + si) mod modl l = (length (blks l ! j) + sj) mod modl l)"

definition pairF :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v form" where
  "pairF l i j si sj = dual (F (2 * k) (pairL l i j) (collide l j si sj))"

lemma pairL_len:
  assumes "i < modl l" "j < modl l"
  shows "length (pairL l i j) \<le> (2 * k) ^ (D - 1)"
proof -
  have "length (pairL l i j) \<le> k ^ (D - 1) + k ^ (D - 1)"
    using blk_len[OF assms(1)] blk_len[OF assms(2)] by (simp add: pairL_def)
  also have "\<dots> = 2 * k ^ (D - 1)" by simp
  also have "\<dots> \<le> 2 ^ (D - 1) * k ^ (D - 1)"
  proof (intro mult_right_mono)
    have "2 ^ 1 \<le> (2::nat) ^ (D - 1)" using D2 by (intro power_increasing) simp_all
    then show "2 \<le> (2::nat) ^ (D - 1)" by simp
  qed simp
  also have "\<dots> = (2 * k) ^ (D - 1)" by (simp add: power_mult_distrib)
  finally show ?thesis .
qed

lemma pairF_facts:
  assumes "i < modl l" "j < modl l"
  shows "PI D (pairF l i j si sj)"
    and "gates (pairF l i j si sj) \<le> 2 ^ (C * (2 * k + 1))"
    and "eval \<sigma> (pairF l i j si sj) \<longleftrightarrow>
           (cnt \<sigma> (blks l ! i) + si) mod modl l \<noteq> (cnt \<sigma> (blks l ! j) + sj) mod modl l"
proof -
  note Fp = F[OF pairL_len[OF assms], of "collide l j si sj"]
  show "PI D (pairF l i j si sj)" using Fp by (simp add: pairF_def pi_dual)
  show "gates (pairF l i j si sj) \<le> 2 ^ (C * (2 * k + 1))" using Fp by (simp add: pairF_def)
  have c: "cnt \<sigma> (pairL l i j) = cnt \<sigma> (blks l ! i) + (length (blks l ! j) - cnt \<sigma> (blks l ! j))"
    by (simp add: pairL_def cnt_map_neg)
  have "eval \<sigma> (pairF l i j si sj) \<longleftrightarrow> \<not> collide l j si sj (cnt \<sigma> (pairL l i j))"
    using Fp by (simp add: pairF_def)
  also have "\<dots> \<longleftrightarrow> \<not> ((cnt \<sigma> (blks l ! i) + si) mod modl l = (cnt \<sigma> (blks l ! j) + sj) mod modl l)"
    unfolding collide_def c
    by (subst collide_iff) (simp_all add: modl_pos cnt_le_length)
  finally show "eval \<sigma> (pairF l i j si sj) \<longleftrightarrow>
           (cnt \<sigma> (blks l ! i) + si) mod modl l \<noteq> (cnt \<sigma> (blks l ! j) + sj) mod modl l" by simp
qed

subsection \<open>Tests\<close>

definition idx :: "(nat \<times> nat \<times> nat) list" where
  "idx = concat (map (\<lambda>l. concat (map (\<lambda>i. map (\<lambda>j. (l, i, j)) [Suc i..<modl l]) [0..<modl l])) [0..<D])"

lemma set_idx: "(l, i, j) \<in> set idx \<longleftrightarrow> l < D \<and> i < j \<and> j < modl l"
proof
  assume "(l, i, j) \<in> set idx"
  then show "l < D \<and> i < j \<and> j < modl l" by (auto simp: idx_def)
next
  assume h: "l < D \<and> i < j \<and> j < modl l"
  have "(l, i, j) \<in> set (map (\<lambda>j. (l, i, j)) [Suc i..<modl l])" using h by simp
  then have "(l, i, j) \<in> set (concat (map (\<lambda>i. map (\<lambda>j. (l, i, j)) [Suc i..<modl l]) [0..<modl l]))"
    by (rule in_concat_map) (use h in simp)
  then show "(l, i, j) \<in> set idx"
    unfolding idx_def by (rule in_concat_map) (use h in simp)
qed

lemma length_idx: "length idx \<le> D * (Qb * Qb)"
proof -
  have inner: "length (concat (map (\<lambda>i. map (\<lambda>j. (l, i, j)) [Suc i..<modl l]) [0..<modl l])) \<le> Qb * Qb"
    if l: "l < D" for l
  proof -
    have "length (concat (map (\<lambda>i. map (\<lambda>j. (l, i, j)) [Suc i..<modl l]) [0..<modl l]))
        \<le> length (map (\<lambda>i. map (\<lambda>j. (l, i, j)) [Suc i..<modl l]) [0..<modl l]) * Qb"
      using modl_le[OF l] by (intro length_concat_le) auto
    also have "\<dots> \<le> Qb * Qb" using modl_le[OF l] by simp
    finally show ?thesis .
  qed
  have "length idx \<le> length (map (\<lambda>l. concat (map (\<lambda>i. map (\<lambda>j. (l, i, j)) [Suc i..<modl l]) [0..<modl l])) [0..<D]) * (Qb * Qb)"
    unfolding idx_def using inner by (intro length_concat_le) auto
  then show ?thesis by simp
qed

definition testF :: "(nat \<Rightarrow> nat list) \<Rightarrow> 'v form" where
  "testF \<theta> = andflat (map (\<lambda>(l, i, j). pairF l i j (\<theta> l ! i) (\<theta> l ! j)) idx)"

lemma testF_parts:
  assumes "f \<in> set (map (\<lambda>(l, i, j). pairF l i j (\<theta> l ! i) (\<theta> l ! j)) idx)"
  shows "PI D f \<and> gates f \<le> 2 ^ (C * (2 * k + 1))"
proof -
  obtain l i j where lij: "(l, i, j) \<in> set idx" and f: "f = pairF l i j (\<theta> l ! i) (\<theta> l ! j)"
    using assms by auto
  then have "i < modl l" "j < modl l" by (auto simp: set_idx)
  then show ?thesis using f pairF_facts by simp
qed

lemma testF_pi: "PI D (testF \<theta>)"
  unfolding testF_def by (rule andflat_PI') (use D2 testF_parts in auto)

lemma testF_gates: "gates (testF \<theta>) \<le> Suc (D * (Qb * Qb) * 2 ^ (C * (2 * k + 1)))"
proof -
  let ?fs = "map (\<lambda>(l, i, j). pairF l i j (\<theta> l ! i) (\<theta> l ! j)) idx"
  have "gates (testF \<theta>) \<le> Suc (sum_list (map gates ?fs))"
    unfolding testF_def by (rule gates_andflat)
  also have "sum_list (map gates ?fs) \<le> length ?fs * 2 ^ (C * (2 * k + 1))"
    using testF_parts by (intro sum_list_le_const) blast
  also have "length ?fs * 2 ^ (C * (2 * k + 1)) \<le> D * (Qb * Qb) * 2 ^ (C * (2 * k + 1))"
    using length_idx by simp
  finally show ?thesis by simp
qed

lemma testF_eval:
  assumes len: "\<And>l. l < D \<Longrightarrow> length (\<theta> l) = modl l"
  shows "eval \<sigma> (testF \<theta>) \<longleftrightarrow> (\<forall>l<D. passes (modl l) \<sigma> (blks l) (\<theta> l))"
proof -
  let ?fs = "map (\<lambda>(l, i, j). pairF l i j (\<theta> l ! i) (\<theta> l ! j)) idx"
  have ands: "\<forall>f\<in>set ?fs. \<exists>gs. f = And gs"
  proof
    fix f assume "f \<in> set ?fs"
    then have "PI D f" using testF_parts by blast
    then show "\<exists>gs. f = And gs" using D2 by (intro PI_And) simp_all
  qed
  have "eval \<sigma> (testF \<theta>) \<longleftrightarrow> (\<forall>f\<in>set ?fs. eval \<sigma> f)"
    unfolding testF_def using ands by (rule eval_andflat)
  also have "\<dots> \<longleftrightarrow> (\<forall>(l, i, j)\<in>set idx. eval \<sigma> (pairF l i j (\<theta> l ! i) (\<theta> l ! j)))"
    by auto
  also have "\<dots> \<longleftrightarrow> (\<forall>l<D. \<forall>i j. i < j \<longrightarrow> j < modl l \<longrightarrow>
        (cnt \<sigma> (blks l ! i) + \<theta> l ! i) mod modl l \<noteq> (cnt \<sigma> (blks l ! j) + \<theta> l ! j) mod modl l)"
  proof
    assume A: "\<forall>(l, i, j)\<in>set idx. eval \<sigma> (pairF l i j (\<theta> l ! i) (\<theta> l ! j))"
    show "\<forall>l<D. \<forall>i j. i < j \<longrightarrow> j < modl l \<longrightarrow>
        (cnt \<sigma> (blks l ! i) + \<theta> l ! i) mod modl l \<noteq> (cnt \<sigma> (blks l ! j) + \<theta> l ! j) mod modl l"
    proof (intro allI impI)
      fix l i j assume l: "l < D" and ij: "i < j" and j: "j < modl l"
      have "(l, i, j) \<in> set idx" using l ij j by (simp add: set_idx)
      with A have ev: "eval \<sigma> (pairF l i j (\<theta> l ! i) (\<theta> l ! j))" by fastforce
      have i: "i < modl l" using ij j by simp
      show "(cnt \<sigma> (blks l ! i) + \<theta> l ! i) mod modl l \<noteq> (cnt \<sigma> (blks l ! j) + \<theta> l ! j) mod modl l"
        using ev pairF_facts(3)[OF i j] by simp
    qed
  next
    assume B: "\<forall>l<D. \<forall>i j. i < j \<longrightarrow> j < modl l \<longrightarrow>
        (cnt \<sigma> (blks l ! i) + \<theta> l ! i) mod modl l \<noteq> (cnt \<sigma> (blks l ! j) + \<theta> l ! j) mod modl l"
    show "\<forall>(l, i, j)\<in>set idx. eval \<sigma> (pairF l i j (\<theta> l ! i) (\<theta> l ! j))"
    proof
      fix x assume x: "x \<in> set idx"
      obtain l i j where xe: "x = (l, i, j)" by (cases x) auto
      with x have l: "l < D" and ij: "i < j" and j: "j < modl l" by (simp_all add: set_idx)
      have i: "i < modl l" using ij j by simp
      have "(cnt \<sigma> (blks l ! i) + \<theta> l ! i) mod modl l \<noteq> (cnt \<sigma> (blks l ! j) + \<theta> l ! j) mod modl l"
        using B l ij j by blast
      then have "eval \<sigma> (pairF l i j (\<theta> l ! i) (\<theta> l ! j))" using pairF_facts(3)[OF i j] by simp
      then show "case x of (l, i, j) \<Rightarrow> eval \<sigma> (pairF l i j (\<theta> l ! i) (\<theta> l ! j))" using xe by simp
    qed
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>l<D. passes (modl l) \<sigma> (blks l) (\<theta> l))"
    using len by (auto simp: passes_def distinct_conv_nth_less shifted_def)
  finally show ?thesis .
qed

end

end
