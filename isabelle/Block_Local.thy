theory Block_Local
  imports Bounded_Width
begin

section \<open>Block locality of the construction, and a lower bound for one-block tests\<close>

text \<open>
  The depth-3 construction is an OR of tests, each an AND of clauses, and every clause
  reads the variables of at most two blocks of one of two fixed partitions of
  \<open>x\<^sub>0 \<dots> x\<^sub>n\<^sub>-\<^sub>1\<close> into consecutive blocks of size at most \<open>\<lceil>n/k\<rceil>\<close>
  (\<open>symmetric_or_of_cnfs_local\<close>).  Two blocks are necessary: if every conjunct of every
  test reads a single block of one fixed partition, a formula for Majority needs at least as
  many tests as there are block-weight vectors of weight \<open>n/2\<close> (\<open>one_block_tests\<close>).  For
  \<open>m\<close> blocks of size \<open>b\<close> that is at least \<open>(b+1)\<^sup>m\<^sup>/\<^sup>2\<close> (\<open>one_block_tests_equal\<close>), which for
  \<open>b = m = \<surd>n\<close> is \<open>2\<^sup>\<Omega>\<^sup>(\<^sup>\<surd>\<^sup>n \<^sup>l\<^sup>o\<^sup>g \<^sup>n\<^sup>)\<close>, against \<open>2\<^sup>O\<^sup>(\<^sup>\<surd>\<^sup>n\<^sup>)\<close> with two blocks.
\<close>

fun fvars :: "'v form \<Rightarrow> 'v set" where
  "fvars (Lit v b) = {v}"
| "fvars (And fs) = (\<Union>f\<in>set fs. fvars f)"
| "fvars (Or fs) = (\<Union>f\<in>set fs. fvars f)"

lemma eval_cong: "\<forall>v\<in>fvars f. \<sigma> v = \<tau> v \<Longrightarrow> eval \<sigma> f = eval \<tau> f"
  by (induction f) auto

lemma fvars_dual [simp]: "fvars (dual f) = fvars f"
  by (induction f) auto

lemma fvars_kids: "c \<in> set (kids f) \<Longrightarrow> fvars c \<subseteq> fvars f"
  by (cases f) auto

lemma fst_set_zip: "p \<in> set (zip xs ys) \<Longrightarrow> fst p \<in> set xs"
  by (cases p) (auto dest: set_zip_leftD)

lemma fvars_dnf: "fvars (dnf L g) \<subseteq> fst ` set L"
  unfolding dnf_def minterm_def by (auto simp: split_def dest!: fst_set_zip)

subsection \<open>Blocks of consecutive variables\<close>

lemma chop_map: "chop c (map f xs) = map (map f) (chop c xs)"
proof (induction c xs rule: chop.induct)
  case (1 c xs)
  show ?case
  proof (cases "c = 0 \<or> xs = []")
    case False
    then have "chop c (map f xs) = take c (map f xs) # chop c (drop c (map f xs))"
      by (simp add: chop_Cons)
    with False 1 show ?thesis by (simp add: chop_Cons take_map drop_map)
  qed auto
qed

lemma chop_upt_mem:
  "0 < c \<Longrightarrow> i < length (chop c [a..<b]) \<Longrightarrow> x \<in> set (chop c [a..<b] ! i) \<Longrightarrow>
     a + i * c \<le> x \<and> x < a + Suc i * c"
proof (induction i arbitrary: a)
  case 0
  then have "[a..<b] \<noteq> []" by (cases "[a..<b] = []") auto
  then have "chop c [a..<b] ! 0 = take c [a..<b]" using "0.prems"(1) by (simp add: chop_Cons)
  with "0.prems" have "x \<in> set (take c [a..<b])" by simp
  then show ?case by (auto simp: in_set_conv_nth)
next
  case (Suc i)
  then have "[a..<b] \<noteq> []" by (cases "[a..<b] = []") auto
  then have ch: "chop c [a..<b] = take c [a..<b] # chop c [a + c..<b]"
    using Suc.prems(1) by (simp add: chop_Cons)
  have "a + c + i * c \<le> x \<and> x < a + c + Suc i * c"
    using Suc.prems ch by (intro Suc.IH) auto
  then show ?case by simp
qed

lemma blocks_vars_div:
  assumes i: "i < q" and v: "v \<in> fst ` set (blocks q (vars n) ! i)"
  shows "v div bsize q n = i"
proof -
  let ?c = "bsize q n"
  let ?ch = "chop ?c [0..<n]"
  have bl: "blocks q (vars n) = map (map (\<lambda>i. (i, True))) ?ch @ replicate (q - length ?ch) []"
    by (simp add: blocks_def vars_def chop_map)
  show ?thesis
  proof (cases "i < length ?ch")
    case True
    then have vi: "v \<in> set (?ch ! i)" using v bl by (auto simp: nth_append image_image)
    have c0: "0 < ?c" using True by (cases "?c = 0") auto
    have "0 + i * ?c \<le> v \<and> v < 0 + Suc i * ?c" by (rule chop_upt_mem[OF c0 True vi])
    then show ?thesis by (intro div_nat_eqI) (simp_all add: mult.commute)
  next
    case False
    then show ?thesis using v i bl by (simp add: nth_append)
  qed
qed

context step3
begin

lemma bsize_modl: "bsize (modl l) (length L) \<le> bsize k (length L)"
proof -
  have "length L \<le> k * bsize k (length L)" using k0 by (rule bsize_bound)
  also have "\<dots> \<le> modl l * bsize k (length L)"
    using modl_gt[of l] by (intro mult_right_mono) simp_all
  finally show ?thesis using modl_pos by (intro bsize_le) simp_all
qed

lemma fst_pairL: "fst ` set (pairL l i j) = fst ` set (blks l ! i) \<union> fst ` set (blks l ! j)"
  by (simp add: pairL_def neg_def image_Un image_image)

lemma testF_clause_local:
  assumes "c \<in> set (kids (testF \<theta>))"
  shows "\<exists>l i j. (l, i, j) \<in> set idx \<and> fvars c \<subseteq> fst ` set (pairL l i j)"
proof -
  obtain l i j where lij: "(l, i, j) \<in> set idx"
    and c: "c \<in> set (kids (pairF l i j (\<theta> l ! i) (\<theta> l ! j)))"
    using assms by (auto simp: testF_def andflat_def)
  have "fvars c \<subseteq> fvars (pairF l i j (\<theta> l ! i) (\<theta> l ! j))" using c by (rule fvars_kids)
  also have "\<dots> \<subseteq> fst ` set (pairL l i j)" by (simp add: pairF_def fvars_dnf)
  finally show ?thesis using lij by blast
qed

lemma cnfs_kids_local:
  assumes "f \<in> set (cnfs g)" "c \<in> set (kids f)"
  shows "\<exists>l i j. (l, i, j) \<in> set idx \<and> fvars c \<subseteq> fst ` set (pairL l i j)"
proof -
  obtain \<theta> where "f = testF \<theta>" using assms(1) by (auto simp: cnfs_def)
  then show ?thesis using assms(2) by (simp add: testF_clause_local)
qed

end

theorem symmetric_or_of_cnfs_local:
  "\<exists>C. \<forall>n k g. 0 < k \<longrightarrow> n \<le> k * k \<longrightarrow>
     (\<exists>fs (s :: nat \<Rightarrow> nat). length fs \<le> 2 ^ (C * k) \<and> (\<forall>f\<in>set fs. CNF (width n k) f) \<and>
          (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)) \<and>
          (\<forall>l. s l \<le> (n + k - 1) div k \<and> (0 < n \<longrightarrow> 0 < s l)) \<and>
          (\<forall>f\<in>set fs. \<forall>c\<in>set (kids f). \<exists>l<2. \<exists>i j. \<forall>v\<in>fvars c. v div s l = i \<or> v div s l = j))"
proof -
  obtain c where c: "\<And>K. 1 \<le> K \<Longrightarrow> nb K \<le> 2 ^ (c * K)"
    using EB_nb by (auto simp: EB_def)
  show ?thesis
  proof (intro exI[of _ "2 * c"] allI impI)
    fix n k :: nat and g :: "nat \<Rightarrow> bool" assume k: "0 < k" and nk: "n \<le> k * k"
    interpret st: step3 k "vars n"
      by (rule step3I) (use k nk in \<open>simp_all add: power2_eq_square\<close>)
    have wd: "st.wd = width n k" by (simp add: st.wd_def width_def bsize_def)
    define s where "s l = bsize (st.modl l) n" for l
    show "\<exists>fs (s :: nat \<Rightarrow> nat). length fs \<le> 2 ^ (2 * c * k) \<and> (\<forall>f\<in>set fs. CNF (width n k) f) \<and>
          (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)) \<and>
          (\<forall>l. s l \<le> (n + k - 1) div k \<and> (0 < n \<longrightarrow> 0 < s l)) \<and>
          (\<forall>f\<in>set fs. \<forall>c\<in>set (kids f). \<exists>l<2. \<exists>i j. \<forall>v\<in>fvars c. v div s l = i \<or> v div s l = j)"
    proof -
      have ck: "c * (k + 1) \<le> 2 * c * k"
      proof -
        have "c \<le> c * k" using k by simp
        then show ?thesis by (simp add: algebra_simps)
      qed
      have "length (st.cnfs g) \<le> nb (k + 1)" by (rule st.length_cnfs)
      also have "\<dots> \<le> 2 ^ (c * (k + 1))" by (rule c) simp
      also have "\<dots> \<le> 2 ^ (2 * c * k)" using ck by (intro power_increasing) simp_all
      finally have len: "length (st.cnfs g) \<le> 2 ^ (2 * c * k)" .
      have cnf: "\<forall>f\<in>set (st.cnfs g). CNF (width n k) f"
        using st.cnfs_CNF wd by simp
      have ev: "\<forall>\<sigma>. (\<exists>f\<in>set (st.cnfs g). eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)"
        using st.cnfs_eval[of g] by (simp add: cnt_vars)
      have sz: "\<forall>l. s l \<le> (n + k - 1) div k \<and> (0 < n \<longrightarrow> 0 < s l)"
      proof (intro allI conjI impI)
        fix l
        show "s l \<le> (n + k - 1) div k"
          using st.bsize_modl[of l] by (simp add: s_def bsize_def)
        show "0 < s l" if "0 < n"
          using that st.modl_pos[of l] by (simp add: s_def bsize_def div_greater_zero_iff)
      qed
      have loc: "\<exists>l<2. \<exists>i j. \<forall>v\<in>fvars cl. v div s l = i \<or> v div s l = j"
        if f: "f \<in> set (st.cnfs g)" and cl: "cl \<in> set (kids f)" for f cl
      proof -
        obtain l i j where lij: "(l, i, j) \<in> set st.idx"
          and sub: "fvars cl \<subseteq> fst ` set (st.pairL l i j)"
          using st.cnfs_kids_local[OF f cl] by blast
        have l: "l < 2" and i: "i < st.modl l" and j: "j < st.modl l"
          using lij by (auto simp: st.set_idx)
        have "\<forall>v\<in>fvars cl. v div s l = i \<or> v div s l = j"
        proof
          fix v assume "v \<in> fvars cl"
          then have "v \<in> fst ` set (st.blks l ! i) \<or> v \<in> fst ` set (st.blks l ! j)"
            using sub st.fst_pairL by blast
          then show "v div s l = i \<or> v div s l = j"
          proof
            assume "v \<in> fst ` set (st.blks l ! i)"
            then have "v div bsize (st.modl l) n = i"
              by (intro blocks_vars_div[OF i]) (simp add: st.blks_def)
            then show ?thesis by (simp add: s_def)
          next
            assume "v \<in> fst ` set (st.blks l ! j)"
            then have "v div bsize (st.modl l) n = j"
              by (intro blocks_vars_div[OF j]) (simp add: st.blks_def)
            then show ?thesis by (simp add: s_def)
          qed
        qed
        with l show ?thesis by blast
      qed
      show ?thesis
        by (rule exI[of _ "st.cnfs g"], rule exI[of _ s]) (use len cnf ev sz loc in blast)
    qed
  qed
qed

subsection \<open>Tests whose conjuncts each read one block\<close>

text \<open>\<open>bw blk n \<sigma> p\<close>: the weight of \<open>\<sigma>\<close> on block \<open>p\<close> of the partition \<open>blk\<close>.\<close>

definition bw :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
  "bw blk n \<sigma> p = card {i. i < n \<and> blk i = p \<and> \<sigma> i}"

lemma weight_bw: "weight n \<sigma> = (\<Sum>p\<in>blk ` {..<n}. bw blk n \<sigma> p)"
proof -
  have "{i. i < n \<and> \<sigma> i} = (\<Union>p\<in>blk ` {..<n}. {i. i < n \<and> blk i = p \<and> \<sigma> i})" by auto
  then have "weight n \<sigma> = card (\<Union>p\<in>blk ` {..<n}. {i. i < n \<and> blk i = p \<and> \<sigma> i})"
    by (simp add: weight_def)
  also have "\<dots> = (\<Sum>p\<in>blk ` {..<n}. card {i. i < n \<and> blk i = p \<and> \<sigma> i})"
    by (rule card_UN_disjoint) auto
  finally show ?thesis by (simp add: bw_def)
qed

lemma finite_bw: "finite (bw blk n ` A)"
proof (rule finite_subset)
  let ?P = "blk ` {..<n}"
  show "bw blk n ` A \<subseteq> (\<lambda>f p. if p \<in> ?P then f p else 0) ` (?P \<rightarrow>\<^sub>E {..n})"
  proof
    fix u assume "u \<in> bw blk n ` A"
    then obtain \<sigma> where u: "u = bw blk n \<sigma>" by blast
    have le: "u p \<le> n" for p
    proof -
      have "u p \<le> card {..<n}" unfolding u bw_def by (rule card_mono) auto
      then show ?thesis by simp
    qed
    have z: "u p = 0" if "p \<notin> ?P" for p
    proof -
      have "{i. i < n \<and> blk i = p \<and> \<sigma> i} = {}" using that by auto
      then show ?thesis by (simp add: u bw_def)
    qed
    show "u \<in> (\<lambda>f p. if p \<in> ?P then f p else 0) ` (?P \<rightarrow>\<^sub>E {..n})"
      by (rule image_eqI[of _ _ "restrict u ?P"]) (auto simp: fun_eq_iff z le)
  qed
  show "finite ((\<lambda>f p. if p \<in> ?P then f p else 0) ` (?P \<rightarrow>\<^sub>E {..n}))"
    by (intro finite_imageI finite_PiE) auto
qed

text \<open>
  The key step: if a one-block test accepts two inputs of weight \<open>n/2\<close>, mixing them block by
  block (taking the lighter one on each block) gives an input the test still accepts, of
  weight \<open>\<Sum>\<^sub>p min(a\<^sub>p, a'\<^sub>p)\<close>.  Majority forces this to be \<open>n/2\<close>, so the block weights agree.
\<close>

lemma mix:
  assumes loc: "\<exists>gs. t = And gs \<and> (\<forall>g\<in>set gs. \<exists>p. \<forall>v\<in>fvars g. blk v = p)"
    and maj: "\<forall>\<sigma>. eval \<sigma> (Or ts) = majority n \<sigma>" and t: "t \<in> set ts" and ev: "even n"
    and s1: "eval \<sigma> t" "weight n \<sigma> = n div 2"
    and s2: "eval \<sigma>' t" "weight n \<sigma>' = n div 2"
  shows "bw blk n \<sigma> = bw blk n \<sigma>'"
proof -
  define a where "a = bw blk n \<sigma>"
  define a' where "a' = bw blk n \<sigma>'"
  define \<tau> where "\<tau> v = (if a (blk v) \<le> a' (blk v) then \<sigma> v else \<sigma>' v)" for v
  obtain gs where gs: "t = And gs" "\<forall>g\<in>set gs. \<exists>p. \<forall>v\<in>fvars g. blk v = p"
    using loc by blast
  have "eval \<tau> g" if g: "g \<in> set gs" for g
  proof -
    obtain p where p: "\<forall>v\<in>fvars g. blk v = p" using gs(2) g by blast
    show ?thesis
    proof (cases "a p \<le> a' p")
      case True
      then have "\<forall>v\<in>fvars g. \<tau> v = \<sigma> v" using p by (simp add: \<tau>_def)
      then have "eval \<tau> g = eval \<sigma> g" by (rule eval_cong)
      moreover have "eval \<sigma> g" using s1(1) gs(1) g by simp
      ultimately show ?thesis by simp
    next
      case False
      then have "\<forall>v\<in>fvars g. \<tau> v = \<sigma>' v" using p by (simp add: \<tau>_def)
      then have "eval \<tau> g = eval \<sigma>' g" by (rule eval_cong)
      moreover have "eval \<sigma>' g" using s2(1) gs(1) g by simp
      ultimately show ?thesis by simp
    qed
  qed
  then have "eval \<tau> t" using gs(1) by simp
  then have "majority n \<tau>" using maj t by auto
  then have m: "n \<le> 2 * weight n \<tau>" by (simp add: majority_def)
  define P where "P = blk ` {..<n}"
  have finP: "finite P" by (simp add: P_def)
  have bw\<tau>: "bw blk n \<tau> p = min (a p) (a' p)" for p
  proof (cases "a p \<le> a' p")
    case True
    then have "{i. i < n \<and> blk i = p \<and> \<tau> i} = {i. i < n \<and> blk i = p \<and> \<sigma> i}"
      by (auto simp: \<tau>_def)
    then show ?thesis using True by (simp add: bw_def a_def min_def)
  next
    case False
    then have "{i. i < n \<and> blk i = p \<and> \<tau> i} = {i. i < n \<and> blk i = p \<and> \<sigma>' i}"
      by (auto simp: \<tau>_def)
    then show ?thesis using False by (simp add: bw_def a'_def min_def)
  qed
  have w\<tau>: "weight n \<tau> = (\<Sum>p\<in>P. min (a p) (a' p))"
    using weight_bw[of n \<tau> blk] bw\<tau> by (simp add: P_def)
  have wa: "(\<Sum>p\<in>P. a p) = n div 2"
    using weight_bw[of n \<sigma> blk] s1(2) by (simp add: P_def a_def)
  have wa': "(\<Sum>p\<in>P. a' p) = n div 2"
    using weight_bw[of n \<sigma>' blk] s2(2) by (simp add: P_def a'_def)
  have n2: "2 * (n div 2) = n" using ev by simp
  have eqa: "min (a p) (a' p) = a p" if "p \<in> P" for p
  proof (rule ccontr)
    assume "min (a p) (a' p) \<noteq> a p"
    then have "min (a p) (a' p) < a p" by simp
    then have "(\<Sum>p\<in>P. min (a p) (a' p)) < (\<Sum>p\<in>P. a p)"
      using that by (intro sum_strict_mono_ex1[OF finP]) auto
    then show False using m w\<tau> wa n2 by linarith
  qed
  have eqa': "min (a p) (a' p) = a' p" if "p \<in> P" for p
  proof (rule ccontr)
    assume "min (a p) (a' p) \<noteq> a' p"
    then have "min (a p) (a' p) < a' p" by simp
    then have "(\<Sum>p\<in>P. min (a p) (a' p)) < (\<Sum>p\<in>P. a' p)"
      using that by (intro sum_strict_mono_ex1[OF finP]) auto
    then show False using m w\<tau> wa' n2 by linarith
  qed
  have all: "a p = a' p" for p
  proof (cases "p \<in> P")
    case True
    then show ?thesis using eqa[OF True] eqa'[OF True] by simp
  next
    case False
    have e1: "{i. i < n \<and> blk i = p \<and> \<sigma> i} = {}" using False by (auto simp: P_def)
    have e2: "{i. i < n \<and> blk i = p \<and> \<sigma>' i} = {}" using False by (auto simp: P_def)
    show ?thesis unfolding a_def a'_def bw_def e1 e2 by simp
  qed
  then have "a = a'" by (simp add: fun_eq_iff)
  then show ?thesis by (simp add: a_def a'_def)
qed

theorem one_block_tests:
  assumes ev: "even n"
    and maj: "\<forall>\<sigma>. eval \<sigma> (Or ts) = majority n \<sigma>"
    and loc: "\<forall>t\<in>set ts. \<exists>gs. t = And gs \<and> (\<forall>g\<in>set gs. \<exists>p. \<forall>v\<in>fvars g. blk v = p)"
  shows "card (bw blk n ` {\<sigma>. weight n \<sigma> = n div 2}) \<le> length ts"
proof -
  define S where "S = {\<sigma>. weight n \<sigma> = n div 2}"
  define V where "V t = bw blk n ` {\<sigma> \<in> S. eval \<sigma> t}" for t
  have n2: "2 * (n div 2) = n" using ev by simp
  have cover: "bw blk n ` S \<subseteq> (\<Union>t\<in>set ts. V t)"
  proof
    fix u assume "u \<in> bw blk n ` S"
    then obtain \<sigma> where \<sigma>: "\<sigma> \<in> S" "u = bw blk n \<sigma>" by blast
    then have "majority n \<sigma>" using n2 by (simp add: S_def majority_def)
    then obtain t where "t \<in> set ts" "eval \<sigma> t" using maj by auto
    with \<sigma> show "u \<in> (\<Union>t\<in>set ts. V t)" by (auto simp: V_def)
  qed
  have V1: "finite (V t) \<and> card (V t) \<le> 1" if t: "t \<in> set ts" for t
  proof (cases "V t = {}")
    case False
    then obtain \<sigma>0 where \<sigma>0: "\<sigma>0 \<in> S" "eval \<sigma>0 t" by (auto simp: V_def)
    have sub: "V t \<subseteq> {bw blk n \<sigma>0}"
    proof
      fix u assume "u \<in> V t"
      then obtain \<sigma> where \<sigma>: "\<sigma> \<in> S" "eval \<sigma> t" "u = bw blk n \<sigma>" by (auto simp: V_def)
      have "bw blk n \<sigma> = bw blk n \<sigma>0"
        by (rule mix[of t blk ts n]) (use loc t ev maj \<sigma> \<sigma>0 in \<open>auto simp: S_def\<close>)
      then show "u \<in> {bw blk n \<sigma>0}" using \<sigma> by simp
    qed
    then have "finite (V t)" by (rule finite_subset) simp
    moreover have "card (V t) \<le> card {bw blk n \<sigma>0}" using sub by (intro card_mono) simp_all
    ultimately show ?thesis by simp
  qed simp
  have "card (bw blk n ` S) \<le> card (\<Union>t\<in>set ts. V t)"
    using cover V1 by (intro card_mono) auto
  also have "\<dots> \<le> (\<Sum>t\<in>set ts. card (V t))" by (rule card_UN_le) simp
  also have "\<dots> \<le> (\<Sum>t\<in>set ts. 1)" using V1 by (intro sum_mono) auto
  also have "\<dots> = card (set ts)" by simp
  also have "\<dots> \<le> length ts" by (rule card_length)
  finally show ?thesis by (simp add: S_def)
qed

subsection \<open>Equal blocks: at least \<open>(b+1)\<^sup>m\<^sup>/\<^sup>2\<close> tests\<close>

lemma card_block_prefix:
  assumes b: "0 < b" and p: "p < m" and x: "x \<le> b"
  shows "card {i. i < m * b \<and> i div b = p \<and> i mod b < x} = x"
proof -
  have "{i. i < m * b \<and> i div b = p \<and> i mod b < x} = (\<lambda>r. p * b + r) ` {..<x}"
  proof (rule set_eqI, rule iffI)
    fix i assume "i \<in> {i. i < m * b \<and> i div b = p \<and> i mod b < x}"
    then have "i = p * b + i mod b" "i mod b < x" using div_mult_mod_eq[of i b] by auto
    then show "i \<in> (\<lambda>r. p * b + r) ` {..<x}" by (intro image_eqI[of i _ "i mod b"]) simp_all
  next
    fix i assume "i \<in> (\<lambda>r. p * b + r) ` {..<x}"
    then obtain r where r: "r < x" "i = p * b + r" by auto
    have rb: "r < b" using r x by simp
    have "p * b + r < Suc p * b" using rb by simp
    also have "\<dots> \<le> m * b" using p by (intro mult_right_mono) simp_all
    finally have "i < m * b" using r by simp
    moreover have "i div b = p" "i mod b = r" using r rb by simp_all
    ultimately show "i \<in> {i. i < m * b \<and> i div b = p \<and> i mod b < x}" using r by simp
  qed
  moreover have "inj_on (\<lambda>r. p * b + r) {..<x}" by (rule inj_onI) simp
  ultimately show ?thesis by (simp add: card_image)
qed

text \<open>Block \<open>2q\<close> gets weight \<open>c q\<close> and block \<open>2q+1\<close> gets \<open>b - c q\<close>.\<close>

definition pick :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "pick b c i = (if even (i div b) then i mod b < c (i div b div 2) else i mod b < b - c (i div b div 2))"

definition pw :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "pw b c p = (if even p then c (p div 2) else b - c (p div 2))"

lemma bw_pick:
  assumes b: "0 < b" and p: "p < m" and c: "c (p div 2) \<le> b"
  shows "bw (\<lambda>v. v div b) (m * b) (pick b c) p = pw b c p"
proof -
  have "{i. i < m * b \<and> i div b = p \<and> pick b c i} = {i. i < m * b \<and> i div b = p \<and> i mod b < pw b c p}"
    by (auto simp: pick_def pw_def)
  moreover have "pw b c p \<le> b" using c by (simp add: pw_def)
  ultimately show ?thesis using card_block_prefix[OF b p] by (simp add: bw_def)
qed

lemma blk_image: "0 < (b::nat) \<Longrightarrow> (\<lambda>v. v div b) ` {..<m * b} = {..<m}"
proof (rule set_eqI, rule iffI)
  fix p assume b: "0 < b" and "p \<in> (\<lambda>v. v div b) ` {..<m * b}"
  then obtain v where "v < m * b" "p = v div b" by auto
  then show "p \<in> {..<m}" using less_mult_imp_div_less[of v m b] by simp
next
  fix p assume b: "0 < b" and "p \<in> {..<m}"
  then have "p * b < m * b" "p = p * b div b" by simp_all
  then show "p \<in> (\<lambda>v. v div b) ` {..<m * b}" by blast
qed

lemma sum_pw: "\<forall>q<h. c q \<le> b \<Longrightarrow> (\<Sum>p<2 * h. pw b c p) = h * b"
proof (induction h)
  case (Suc h)
  have "(\<Sum>p<2 * Suc h. pw b c p) = (\<Sum>p<2 * h. pw b c p) + pw b c (2 * h) + pw b c (Suc (2 * h))"
    by simp
  also have "\<dots> = h * b + c h + (b - c h)" using Suc by (simp add: pw_def)
  also have "\<dots> = Suc h * b" using Suc.prems by simp
  finally show ?case .
qed simp

corollary one_block_tests_equal:
  assumes b: "0 < b" and m: "even m"
    and maj: "\<forall>\<sigma>. eval \<sigma> (Or ts) = majority (m * b) \<sigma>"
    and loc: "\<forall>t\<in>set ts. \<exists>gs. t = And gs \<and> (\<forall>g\<in>set gs. \<exists>p. \<forall>v\<in>fvars g. v div b = p)"
  shows "(b + 1) ^ (m div 2) \<le> length ts"
proof -
  define h where "h = m div 2"
  define n where "n = m * b"
  define C where "C = {..<h} \<rightarrow>\<^sub>E {..b}"
  define blk :: "nat \<Rightarrow> nat" where "blk = (\<lambda>v. v div b)"
  have mh: "m = 2 * h" using m by (simp add: h_def)
  have ev: "even n" using m by (simp add: n_def)
  have bw_c: "bw blk n (pick b c) p = pw b c p" if c: "c \<in> C" and p: "p < m" for c p
  proof -
    have "p div 2 < h" using p mh by simp
    then have "c (p div 2) \<le> b" using c by (auto simp: C_def)
    then show ?thesis using bw_pick[OF b p] by (simp add: blk_def n_def)
  qed
  have slice: "weight n (pick b c) = n div 2" if c: "c \<in> C" for c
  proof -
    have "weight n (pick b c) = (\<Sum>p\<in>{..<m}. bw blk n (pick b c) p)"
      using weight_bw[of n "pick b c" blk] blk_image[OF b, of m] by (simp add: blk_def n_def)
    also have "\<dots> = (\<Sum>p<2 * h. pw b c p)" using bw_c[OF c] mh by simp
    also have "\<dots> = h * b" using c by (intro sum_pw) (auto simp: C_def)
    also have "\<dots> = n div 2" using mh by (simp add: n_def)
    finally show ?thesis .
  qed
  have inj: "inj_on (\<lambda>c. bw blk n (pick b c)) C"
  proof (rule inj_onI)
    fix c c' assume c: "c \<in> C" and c': "c' \<in> C" and eq: "bw blk n (pick b c) = bw blk n (pick b c')"
    show "c = c'"
    proof (rule PiE_ext[OF c[unfolded C_def] c'[unfolded C_def]])
      fix q assume q: "q \<in> {..<h}"
      then have q2: "2 * q < m" using mh by simp
      have "pw b c (2 * q) = pw b c' (2 * q)" using eq bw_c[OF c q2] bw_c[OF c' q2] by metis
      then show "c q = c' q" by (simp add: pw_def)
    qed
  qed
  have "(b + 1) ^ h = card C" by (simp add: C_def card_PiE)
  also have "\<dots> = card ((\<lambda>c. bw blk n (pick b c)) ` C)" using inj by (simp add: card_image)
  also have "\<dots> \<le> card (bw blk n ` {\<sigma>. weight n \<sigma> = n div 2})"
    using slice by (intro card_mono finite_bw) auto
  also have "\<dots> \<le> length ts"
    by (rule one_block_tests[OF ev]) (use maj loc in \<open>simp_all add: n_def blk_def\<close>)
  finally show ?thesis by (simp add: h_def)
qed

end
