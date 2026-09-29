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

subsection \<open>The family of tests, and covering every input of weight \<open>t\<close>\<close>

text \<open>
  A test is a tuple of shift vectors, one per modulus, each admissible for the target
  weight \<open>t\<close>.  Whether a test accepts an input depends only on the block weights, so the
  universe to be covered is the finite set of weight tuples of inputs of weight \<open>t\<close>.
\<close>

definition Th :: "nat \<Rightarrow> (nat \<Rightarrow> nat list) set" where
  "Th t = {\<theta> \<in> PiE {..<D} (\<lambda>l. shifts (modl l)). \<forall>l<D. adm (modl l) t (\<theta> l)}"

definition wv :: "('v \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat list" where
  "wv \<sigma> = restrict (\<lambda>l. map (cnt \<sigma>) (blks l)) {..<D}"

definition Univ :: "nat \<Rightarrow> (nat \<Rightarrow> nat list) set" where
  "Univ t = wv ` {\<sigma>. cnt \<sigma> L = t}"

definition Rel :: "(nat \<Rightarrow> nat list) \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow> bool" where
  "Rel \<theta> u = (\<forall>l<D. passesW (modl l) (u l) (\<theta> l))"

definition aa :: nat where "aa = (\<Prod>l<D. fact (modl l))"
definition rr :: nat where "rr = 3 ^ (D * Qb)"
definition hh :: nat where "hh = D * (D * (k + 1) * Qb) + 1"

lemma Rel_wv: "Rel \<theta> (wv \<sigma>) \<longleftrightarrow> (\<forall>l<D. passes (modl l) \<sigma> (blks l) (\<theta> l))"
  by (simp add: Rel_def wv_def passes_passesW)

lemma finite_Th: "finite (Th t)"
proof -
  have "Th t \<subseteq> PiE {..<D} (\<lambda>l. shifts (modl l))" by (auto simp: Th_def)
  moreover have "finite (PiE {..<D} (\<lambda>l. shifts (modl l)))"
    by (intro finite_PiE) (simp_all add: finite_shifts)
  ultimately show ?thesis by (rule finite_subset)
qed

lemma aa_pos: "0 < aa"
  by (simp add: aa_def)

lemma card_Th: "card (Th t) \<le> rr * aa"
proof -
  have "card (Th t) \<le> card (PiE {..<D} (\<lambda>l. shifts (modl l)))"
    by (intro card_mono) (auto simp: Th_def intro: finite_PiE simp: finite_shifts)
  also have "\<dots> = (\<Prod>l<D. modl l ^ modl l)" by (simp add: card_PiE card_shifts)
  also have "\<dots> \<le> (\<Prod>l<D. 3 ^ modl l * fact (modl l))"
    by (intro prod_mono conjI) (simp_all add: pow_le_3pow_fact)
  also have "\<dots> = (\<Prod>l<D. 3 ^ modl l) * aa" by (simp add: prod.distrib aa_def)
  also have "(\<Prod>l<D. (3::nat) ^ modl l) \<le> (\<Prod>l<D. 3 ^ Qb)"
    by (intro prod_mono conjI) (simp_all add: modl_le power_increasing)
  also have "(\<Prod>l<D. (3::nat) ^ Qb) = rr"
  proof -
    have "(\<Prod>l<D. (3::nat) ^ Qb) = (3 ^ Qb) ^ D" by simp
    also have "\<dots> = 3 ^ (Qb * D)" by (rule power_mult[symmetric])
    also have "\<dots> = rr" by (simp add: rr_def mult.commute)
    finally show ?thesis .
  qed
  finally show ?thesis by simp
qed

lemma wit:
  assumes "u \<in> Univ t" shows "aa \<le> card {\<theta> \<in> Th t. Rel \<theta> u}"
proof -
  obtain \<sigma> where u: "u = wv \<sigma>" and w: "cnt \<sigma> L = t" using assms by (auto simp: Univ_def)
  let ?G = "\<lambda>l. {ss \<in> shifts (modl l). passes (modl l) \<sigma> (blks l) ss}"
  have sub: "PiE {..<D} ?G \<subseteq> {\<theta> \<in> Th t. Rel \<theta> u}"
  proof
    fix \<theta> assume th: "\<theta> \<in> PiE {..<D} ?G"
    have sh: "\<theta> \<in> PiE {..<D} (\<lambda>l. shifts (modl l))" using th by (auto simp: PiE_iff)
    have ps: "\<And>l. l < D \<Longrightarrow> passes (modl l) \<sigma> (blks l) (\<theta> l)" using th by (auto simp: PiE_iff)
    have adm: "adm (modl l) t (\<theta> l)" if l: "l < D" for l
    proof (rule passes_imp_adm)
      show "length (blks l) = modl l" by simp
      show "length (\<theta> l) = modl l" using sh l by (auto simp: PiE_iff shifts_def)
      show "0 < modl l" by (rule modl_pos)
      show "cnt \<sigma> (concat (blks l)) mod modl l = t mod modl l" using w by simp
      show "passes (modl l) \<sigma> (blks l) (\<theta> l)" using ps l by blast
    qed
    have "\<theta> \<in> Th t" using sh adm by (simp add: Th_def)
    moreover have "Rel \<theta> u" using ps u by (simp add: Rel_wv)
    ultimately show "\<theta> \<in> {\<theta> \<in> Th t. Rel \<theta> u}" by simp
  qed
  have fin: "finite {\<theta> \<in> Th t. Rel \<theta> u}" using finite_Th by simp
  have "aa \<le> (\<Prod>l<D. card (?G l))"
    unfolding aa_def by (intro prod_mono conjI) (simp_all add: card_accepting_shifts modl_pos)
  also have "\<dots> = card (PiE {..<D} ?G)" by (simp add: card_PiE)
  also have "\<dots> \<le> card {\<theta> \<in> Th t. Rel \<theta> u}" using fin sub by (rule card_mono)
  finally show ?thesis .
qed

definition Wset :: "(nat \<Rightarrow> nat list) set" where
  "Wset = PiE {..<D} (\<lambda>l. {ws. set ws \<subseteq> {..length L} \<and> length ws = modl l})"

lemma finite_Wset: "finite Wset"
  unfolding Wset_def by (intro finite_PiE) (simp_all add: finite_lists_length_eq)

lemma Univ_sub: "Univ t \<subseteq> Wset"
proof
  fix u assume "u \<in> Univ t"
  then obtain \<sigma> where u: "u = wv \<sigma>" by (auto simp: Univ_def)
  have "cnt \<sigma> B \<le> length L" if "B \<in> set (blks l)" for B l
  proof -
    have "cnt \<sigma> B \<le> length B" by (rule cnt_le_length)
    also have "\<dots> \<le> length (concat (blks l))" using that by (rule length_le_concat)
    finally show ?thesis by simp
  qed
  then show "u \<in> Wset" using u by (auto simp: Wset_def wv_def PiE_iff)
qed

lemma finite_Univ: "finite (Univ t)"
  using finite_Wset Univ_sub by (rule finite_subset[rotated])

lemma card_Univ: "card (Univ t) < 2 ^ hh"
proof -
  let ?K = "k + 1"
  have "card (Univ t) \<le> card Wset" using finite_Wset Univ_sub by (intro card_mono)
  also have "\<dots> = (\<Prod>l<D. Suc (length L) ^ modl l)"
    by (simp add: Wset_def card_PiE card_lists_length_eq)
  also have "\<dots> \<le> (\<Prod>l<D. 2 ^ (?K * D * Qb))"
  proof (intro prod_mono conjI)
    fix l assume l: "l \<in> {..<D}"
    have D0: "0 < D" using D2 by simp
    have "k ^ D < ?K ^ D" using D0 by (intro power_strict_mono) simp_all
    with Lk have "length L < ?K ^ D" by (rule le_less_trans)
    then have a: "Suc (length L) \<le> ?K ^ D" by simp
    have Kle: "?K \<le> 2 ^ ?K" by (rule less_imp_le, rule less_exp)
    have i1: "?K ^ D \<le> (2 ^ ?K) ^ D" using Kle by (rule power_mono) simp
    have "Suc (length L) ^ modl l \<le> (?K ^ D) ^ modl l" using a by (rule power_mono) simp
    also have "\<dots> \<le> (?K ^ D) ^ Qb"
      using l modl_le by (intro power_increasing) simp_all
    also have "\<dots> \<le> ((2 ^ ?K) ^ D) ^ Qb" using i1 by (rule power_mono) simp
    also have "\<dots> = 2 ^ (?K * D * Qb)" by (simp only: power_mult)
    finally show "Suc (length L) ^ modl l \<le> 2 ^ (?K * D * Qb)" .
  qed simp
  also have "\<dots> = 2 ^ (D * (?K * D * Qb))"
  proof -
    have "(\<Prod>l<D. (2::nat) ^ (?K * D * Qb)) = (2 ^ (?K * D * Qb)) ^ D" by simp
    also have "\<dots> = 2 ^ (?K * D * Qb * D)" by (rule power_mult[symmetric])
    also have "?K * D * Qb * D = D * (?K * D * Qb)" by (rule mult.commute)
    finally show ?thesis .
  qed
  also have "\<dots> < 2 ^ hh" by (simp add: hh_def algebra_simps)
  finally show ?thesis .
qed

lemma cover_exists: "\<exists>S\<subseteq>Th t. card S \<le> rr * hh \<and> (\<forall>u\<in>Univ t. \<exists>\<theta>\<in>S. Rel \<theta> u)"
  by (rule cover) (rule finite_Univ, rule finite_Th, rule aa_pos, erule wit, rule card_Th, rule card_Univ)

definition Sc :: "nat \<Rightarrow> (nat \<Rightarrow> nat list) set" where
  "Sc t = (SOME S. S \<subseteq> Th t \<and> card S \<le> rr * hh \<and> (\<forall>u\<in>Univ t. \<exists>\<theta>\<in>S. Rel \<theta> u))"

lemma Sc: "Sc t \<subseteq> Th t" "card (Sc t) \<le> rr * hh" "\<forall>u\<in>Univ t. \<exists>\<theta>\<in>Sc t. Rel \<theta> u"
  using someI_ex[OF cover_exists[of t]] unfolding Sc_def by blast+

lemma finite_Sc: "finite (Sc t)"
  using Sc(1) finite_Th by (rule finite_subset)

definition scl :: "nat \<Rightarrow> (nat \<Rightarrow> nat list) list" where
  "scl t = (SOME xs. set xs = Sc t \<and> distinct xs)"

lemma scl: "set (scl t) = Sc t" "distinct (scl t)"
  using someI_ex[OF finite_distinct_list[OF finite_Sc[of t]]] unfolding scl_def by blast+

lemma length_scl: "length (scl t) \<le> rr * hh"
  using scl Sc(2)[of t] by (simp add: distinct_card[symmetric])

subsection \<open>\<open>EXACT\<^sub>t\<close> and arbitrary symmetric functions\<close>

definition exactF :: "nat \<Rightarrow> 'v form" where
  "exactF t = Or (map testF (scl t))"

lemma exactF_SIG: "SIG (Suc D) (exactF t)"
  by (simp add: exactF_def testF_pi)

lemma exactF_gates: "gates (exactF t) \<le> Suc (rr * hh * Suc (D * (Qb * Qb) * 2 ^ (C * (2 * k + 1))))"
proof -
  have "sum_list (map gates (map testF (scl t))) \<le> length (map testF (scl t)) * Suc (D * (Qb * Qb) * 2 ^ (C * (2 * k + 1)))"
    by (intro sum_list_le_const ballI) (use testF_gates in auto)
  also have "\<dots> \<le> rr * hh * Suc (D * (Qb * Qb) * 2 ^ (C * (2 * k + 1)))"
    by (rule mult_right_mono) (simp_all add: length_scl)
  finally show ?thesis by (simp add: exactF_def comp_def)
qed

lemma exactF_eval:
  assumes t: "t \<le> length L"
  shows "eval \<sigma> (exactF t) \<longleftrightarrow> cnt \<sigma> L = t"
proof
  assume "eval \<sigma> (exactF t)"
  then obtain \<theta> where th: "\<theta> \<in> Sc t" and ev: "eval \<sigma> (testF \<theta>)"
    by (auto simp: exactF_def scl)
  have thT: "\<theta> \<in> Th t" using th Sc(1) by blast
  have len: "\<And>l. l < D \<Longrightarrow> length (\<theta> l) = modl l"
    using thT by (auto simp: Th_def PiE_iff shifts_def)
  have ps: "\<forall>l<D. passes (modl l) \<sigma> (blks l) (\<theta> l)" using ev len by (simp add: testF_eval)
  have cong: "cnt \<sigma> L mod modq D k l = t mod modq D k l" if l: "l < D" for l
  proof -
    have "cnt \<sigma> (concat (blks l)) mod modl l = t mod modl l"
    proof (rule test_sound)
      show "length (blks l) = modl l" by simp
      show "length (\<theta> l) = modl l" using len l by blast
      show "0 < modl l" by (rule modl_pos)
      show "adm (modl l) t (\<theta> l)" using thT l by (simp add: Th_def)
      show "passes (modl l) \<sigma> (blks l) (\<theta> l)" using ps l by blast
    qed
    then show ?thesis by (simp add: modl_def)
  qed
  have D0: "0 < D" using D2 by simp
  have c1: "cnt \<sigma> L < (\<Prod>i<D. modq D k i)"
    using D0 cnt_le_length[of \<sigma> L] Lk by (intro modq_prod_gt) simp_all
  have c2: "t < (\<Prod>i<D. modq D k i)"
    using D0 t Lk by (intro modq_prod_gt) simp_all
  show "cnt \<sigma> L = t"
    by (rule crt_eq[of D "modq D k"]) (simp_all add: modq_coprime cong c1 c2)
next
  assume w: "cnt \<sigma> L = t"
  then have "wv \<sigma> \<in> Univ t" by (auto simp: Univ_def)
  then obtain \<theta> where th: "\<theta> \<in> Sc t" and R: "Rel \<theta> (wv \<sigma>)" using Sc(3) by blast
  have thT: "\<theta> \<in> Th t" using th Sc(1) by blast
  have len: "\<And>l. l < D \<Longrightarrow> length (\<theta> l) = modl l"
    using thT by (auto simp: Th_def PiE_iff shifts_def)
  have "eval \<sigma> (testF \<theta>)" using R len by (simp add: testF_eval Rel_wv)
  then show "eval \<sigma> (exactF t)" using th by (auto simp: exactF_def scl)
qed

definition symF :: "(nat \<Rightarrow> bool) \<Rightarrow> 'v form" where
  "symF g = orflat (map exactF (filter g [0..<Suc (length L)]))"

lemma symF_SIG: "SIG (Suc D) (symF g)"
  unfolding symF_def by (rule orflat_SIG') (auto simp del: SIG.simps simp: exactF_SIG)

lemma symF_eval: "eval \<sigma> (symF g) \<longleftrightarrow> g (cnt \<sigma> L)"
proof -
  have ors: "\<forall>f\<in>set (map exactF (filter g [0..<Suc (length L)])). \<exists>gs. f = Or gs"
    by (auto simp: exactF_def)
  have "eval \<sigma> (symF g) \<longleftrightarrow> (\<exists>t\<in>set (filter g [0..<Suc (length L)]). eval \<sigma> (exactF t))"
    unfolding symF_def using ors by (simp add: eval_orflat)
  also have "\<dots> \<longleftrightarrow> g (cnt \<sigma> L)"
  proof
    assume "\<exists>t\<in>set (filter g [0..<Suc (length L)]). eval \<sigma> (exactF t)"
    then obtain t where t: "t < Suc (length L)" "g t" "eval \<sigma> (exactF t)"
      by (auto simp del: upt_Suc)
    then have "cnt \<sigma> L = t" using exactF_eval[of t \<sigma>] by simp
    with t(2) show "g (cnt \<sigma> L)" by simp
  next
    assume g: "g (cnt \<sigma> L)"
    have c: "cnt \<sigma> L \<le> length L" by (rule cnt_le_length)
    then have "eval \<sigma> (exactF (cnt \<sigma> L))" using exactF_eval by simp
    then show "\<exists>t\<in>set (filter g [0..<Suc (length L)]). eval \<sigma> (exactF t)"
      using g c by (intro bexI[of _ "cnt \<sigma> L"]) (auto simp del: upt_Suc)
  qed
  finally show ?thesis .
qed

lemma symF_gates:
  "gates (symF g) \<le> Suc (Suc (length L) * Suc (rr * hh * Suc (D * (Qb * Qb) * 2 ^ (C * (2 * k + 1)))))"
proof -
  let ?b = "Suc (rr * hh * Suc (D * (Qb * Qb) * 2 ^ (C * (2 * k + 1))))"
  have "gates (symF g) \<le> Suc (sum_list (map gates (map exactF (filter g [0..<Suc (length L)]))))"
    unfolding symF_def by (rule gates_orflat)
  also have "sum_list (map gates (map exactF (filter g [0..<Suc (length L)])))
      \<le> length (map exactF (filter g [0..<Suc (length L)])) * ?b"
    by (intro sum_list_le_const ballI) (use exactF_gates in auto)
  also have "\<dots> \<le> Suc (length L) * ?b"
  proof (rule mult_right_mono)
    have "length (filter g [0..<Suc (length L)]) \<le> length [0..<Suc (length L)]"
      by (rule length_filter_le)
    then show "length (map exactF (filter g [0..<Suc (length L)])) \<le> Suc (length L)"
      by (simp del: upt_Suc)
  qed simp
  finally show ?thesis by simp
qed

end

end
