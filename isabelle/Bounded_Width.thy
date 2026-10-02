theory Bounded_Width
  imports Majority_Circuits
begin

section \<open>Symmetric functions as an OR of few narrow CNFs (Remark 1 of arXiv:2609.34029v2)\<close>

text \<open>
  Remark 1 of the paper: with moduli above \<open>k \<ge> \<surd>n\<close>, the depth-3 construction writes
  Majority as an OR of \<open>2\<^sup>O\<^sup>(\<^sup>k\<^sup>)\<close> CNFs of clause width \<open>k' = 2\<lceil>n/k\<rceil>\<close>, i.e.\ of
  \<open>2\<^sup>O\<^sup>(\<^sup>n\<^sup>/\<^sup>k\<^sup>'\<^sup>)\<close> many \<open>k'\<close>-CNFs.  This refutes the \<open>\<Sigma>\<^sub>3\<^sup>k\<close> lower bound
  \<open>2\<^sup>\<Omega>\<^sup>(\<^sup>n \<^sup>l\<^sup>o\<^sup>g \<^sup>k\<^sup>/\<^sup>k\<^sup>)\<close> that Gurumukhani, Paturi, Pudl\'ak, Saks and Talebanfard (CCC 2024)
  derive from a hypothetical local enumeration algorithm.  By pigeonhole it also gives
  \<open>k'\<close>-CNFs with no solution of weight below \<open>t\<close> and \<open>\<binom>n t / 2\<^sup>O\<^sup>(\<^sup>n\<^sup>/\<^sup>k\<^sup>'\<^sup>)\<close> solutions of weight
  exactly \<open>t\<close>, a lower bound on the output size of their problem \<open>Enum(k', t)\<close>.
\<close>

text \<open>\<open>CNF w f\<close>: \<open>f\<close> is an AND of clauses, each an OR of at most \<open>w\<close> literals.\<close>

definition CNF :: "nat \<Rightarrow> 'v form \<Rightarrow> bool" where
  "CNF w f \<longleftrightarrow> (\<exists>cs. f = And cs \<and>
     (\<forall>c\<in>set cs. \<exists>ls. c = Or ls \<and> length ls \<le> w \<and> (\<forall>l\<in>set ls. \<exists>v b. l = Lit v b)))"

text \<open>The clause width of the paper's Remark 1, \<open>k' = 2\<lceil>n/k\<rceil>\<close>.\<close>

definition width :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "width n k = 2 * ((n + k - 1) div k)"

lemma CNF_mono: "CNF w f \<Longrightarrow> w \<le> w' \<Longrightarrow> CNF w' f"
  unfolding CNF_def by fastforce

lemma CNF_dual_dnf: "CNF (length L) (dual (dnf L g))"
  unfolding CNF_def dnf_def minterm_def by (auto simp: split_def)

lemma CNF_andflat: "\<forall>f\<in>set fs. CNF w f \<Longrightarrow> CNF w (andflat fs)"
proof (induction fs)
  case (Cons f fs)
  then obtain cs where "f = And cs"
    "\<forall>c\<in>set cs. \<exists>ls. c = Or ls \<and> length ls \<le> w \<and> (\<forall>l\<in>set ls. \<exists>v b. l = Lit v b)"
    by (auto simp: CNF_def)
  with Cons show ?case by (auto simp: CNF_def andflat_def)
qed (simp add: CNF_def andflat_def)

lemma gates_dnf_le: "length L \<le> k \<Longrightarrow> gates (dnf L g) \<le> 2 * 2 ^ k"
proof -
  assume "length L \<le> k"
  then have a: "(2::nat) ^ length L \<le> 2 ^ k" by simp
  have b: "(1::nat) \<le> 2 ^ k" by simp
  have "Suc (2 ^ length L) \<le> 2 * 2 ^ k" using a b by linarith
  then show ?thesis using gates_dnf[of L g] by simp
qed

definition nb :: "nat \<Rightarrow> nat" where
  "nb K = K ^ 2 * (3 ^ ((2 * Econst 2) * K) * (2 * (2 * K * (Econst 2 * K)) + 1))"

lemma EB_nb: "EB nb"
  unfolding nb_def[abs_def] by (intro EB_intros)

text \<open>The depth-3 instance of the construction, with the base case fixed to the DNF.\<close>

locale step3 = step 2 k 1 L "\<lambda>_ L' g'. dnf L' g'"
  for k :: nat and L :: "'v lit list" +
  assumes k0: "0 < k"
begin

definition wd :: nat where "wd = 2 * bsize k (length L)"

lemma blk_len3: "i < modl l \<Longrightarrow> length (blks l ! i) \<le> bsize k (length L)"
proof -
  assume i: "i < modl l"
  have "length L \<le> k * bsize k (length L)" using k0 by (rule bsize_bound)
  also have "\<dots> \<le> modl l * bsize k (length L)"
    using modl_gt[of l] by (intro mult_right_mono) simp_all
  finally have "bsize (modl l) (length L) \<le> bsize k (length L)"
    using modl_pos by (intro bsize_le) simp_all
  moreover have "blks l ! i \<in> set (blocks (modl l) L)"
    using i by (simp add: blks_def[symmetric])
  ultimately show ?thesis using blocks_lengths[of "modl l" L] by fastforce
qed

lemma pairF_CNF:
  assumes "i < modl l" "j < modl l" shows "CNF wd (pairF l i j si sj)"
proof -
  have len: "length (pairL l i j) \<le> wd"
    using blk_len3[OF assms(1)] blk_len3[OF assms(2)] by (simp add: pairL_def wd_def)
  have "pairF l i j si sj = dual (dnf (pairL l i j) (collide l j si sj))"
    by (simp add: pairF_def)
  with CNF_mono[OF CNF_dual_dnf len] show ?thesis by simp
qed

lemma testF_CNF: "CNF wd (testF \<theta>)"
  unfolding testF_def
proof (rule CNF_andflat, intro ballI)
  fix f assume "f \<in> set (map (\<lambda>(l, i, j). pairF l i j (\<theta> l ! i) (\<theta> l ! j)) idx)"
  then obtain l i j where lij: "(l, i, j) \<in> set idx" and f: "f = pairF l i j (\<theta> l ! i) (\<theta> l ! j)"
    by auto
  then have "i < modl l" "j < modl l" by (auto simp: set_idx)
  then show "CNF wd f" using f pairF_CNF by simp
qed

definition cnfs :: "(nat \<Rightarrow> bool) \<Rightarrow> 'v form list" where
  "cnfs g = concat (map (\<lambda>t. map testF (scl t)) (filter g [0..<Suc (length L)]))"

lemma symF_cnfs: "symF g = Or (cnfs g)"
  by (simp add: symF_def orflat_def exactF_def cnfs_def comp_def)

lemma cnfs_eval: "(\<exists>f\<in>set (cnfs g). eval \<sigma> f) \<longleftrightarrow> g (cnt \<sigma> L)"
  using symF_eval[of \<sigma> g] by (simp add: symF_cnfs)

lemma cnfs_CNF: "f \<in> set (cnfs g) \<Longrightarrow> CNF wd f"
  by (auto simp: cnfs_def testF_CNF)

lemma length_cnfs: "length (cnfs g) \<le> nb (k + 1)"
proof -
  have "length (cnfs g) \<le> length (map (\<lambda>t. map testF (scl t)) (filter g [0..<Suc (length L)])) * (rr * hh)"
    unfolding cnfs_def by (intro length_concat_le) (auto simp: length_scl)
  also have "\<dots> \<le> Suc (length L) * (rr * hh)"
  proof (rule mult_right_mono)
    have "length (filter g [0..<Suc (length L)]) \<le> length [0..<Suc (length L)]"
      by (rule length_filter_le)
    then show "length (map (\<lambda>t. map testF (scl t)) (filter g [0..<Suc (length L)])) \<le> Suc (length L)"
      by (simp del: upt_Suc)
  qed simp
  also have "\<dots> \<le> (k + 1) ^ 2 * (rr * hh)"
  proof (rule mult_right_mono)
    show "Suc (length L) \<le> (k + 1) ^ 2" using Lk by (simp add: power2_eq_square algebra_simps)
  qed simp
  also have "\<dots> = nb (k + 1)"
    by (simp add: nb_def rr_def hh_def Qb_def algebra_simps)
  finally show ?thesis .
qed

end

lemma step3I: "0 < k \<Longrightarrow> length L \<le> k ^ 2 \<Longrightarrow> step3 k L"
  by unfold_locales (simp_all add: sig2_dnf eval_dnf gates_dnf_le)

theorem symmetric_or_of_cnfs:
  "\<exists>C. \<forall>n k g. 0 < k \<longrightarrow> n \<le> k * k \<longrightarrow>
     (\<exists>fs. length fs \<le> 2 ^ (C * k) \<and> (\<forall>f\<in>set fs. CNF (width n k) f) \<and>
          (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)))"
proof -
  obtain c where c: "\<And>K. 1 \<le> K \<Longrightarrow> nb K \<le> 2 ^ (c * K)"
    using EB_nb by (auto simp: EB_def)
  show ?thesis
  proof (intro exI[of _ "2 * c"] allI impI)
    fix n k :: nat and g :: "nat \<Rightarrow> bool" assume k: "0 < k" and nk: "n \<le> k * k"
    interpret st: step3 k "vars n"
      by (rule step3I) (use k nk in \<open>simp_all add: power2_eq_square\<close>)
    have wd: "st.wd = width n k" by (simp add: st.wd_def width_def bsize_def)
    show "\<exists>fs. length fs \<le> 2 ^ (2 * c * k) \<and> (\<forall>f\<in>set fs. CNF (width n k) f) \<and>
            (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>))"
    proof (intro exI[of _ "st.cnfs g"] conjI ballI allI)
      have ck: "c * (k + 1) \<le> 2 * c * k"
      proof -
        have "c \<le> c * k" using k by simp
        then show ?thesis by (simp add: algebra_simps)
      qed
      have "length (st.cnfs g) \<le> nb (k + 1)" by (rule st.length_cnfs)
      also have "\<dots> \<le> 2 ^ (c * (k + 1))" by (rule c) simp
      also have "\<dots> \<le> 2 ^ (2 * c * k)" using ck by (intro power_increasing) simp_all
      finally show "length (st.cnfs g) \<le> 2 ^ (2 * c * k)" .
      show "CNF (width n k) f" if "f \<in> set (st.cnfs g)" for f
        using st.cnfs_CNF[OF that] wd by simp
      show "(\<exists>f\<in>set (st.cnfs g). eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)" for \<sigma>
        using st.cnfs_eval[of g \<sigma>] by (simp add: cnt_vars)
    qed
  qed
qed

section \<open>In terms of the clause width: \<open>2\<^sup>O\<^sup>(\<^sup>n\<^sup>/\<^sup>k\<^sup>'\<^sup>)\<close> many \<open>k'\<close>-CNFs\<close>

lemma k_width:
  assumes k: "0 < k" "k \<le> n" shows "0 < width n k" "real k \<le> 4 * real n / real (width n k)"
proof -
  have "k \<le> n + k - 1" using k by simp
  then have "0 < (n + k - 1) div k" using k by (simp add: div_greater_zero_iff)
  then show w0: "0 < width n k" by (simp add: width_def)
  have a: "k * ((n + k - 1) div k) \<le> n + k - 1" by (rule times_div_less_eq_dividend)
  have b: "n + k - 1 \<le> 2 * n" using k by simp
  have "k * width n k = 2 * (k * ((n + k - 1) div k))" by (simp add: width_def)
  then have "k * width n k \<le> 4 * n" using a b by linarith
  then have "real k * real (width n k) \<le> 4 * real n" by (simp flip: of_nat_mult)
  then show "real k \<le> 4 * real n / real (width n k)" using w0 by (simp add: pos_le_divide_eq)
qed

theorem symmetric_or_of_cnfs_width:
  "\<exists>C. \<forall>n k g. 0 < k \<longrightarrow> n \<le> k * k \<longrightarrow> k \<le> n \<longrightarrow>
     (\<exists>fs. real (length fs) \<le> 2 powr (C * real n / real (width n k)) \<and>
          (\<forall>f\<in>set fs. CNF (width n k) f) \<and>
          (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)))"
proof -
  obtain C where C: "\<forall>n k g. 0 < k \<longrightarrow> n \<le> k * k \<longrightarrow>
     (\<exists>fs. length fs \<le> 2 ^ (C * k) \<and> (\<forall>f\<in>set fs. CNF (width n k) f) \<and>
          (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)))"
    using symmetric_or_of_cnfs by blast
  show ?thesis
  proof (intro exI[of _ "4 * real C"] allI impI)
    fix n k :: nat and g :: "nat \<Rightarrow> bool" assume k: "0 < k" and nk: "n \<le> k * k" and kn: "k \<le> n"
    obtain fs where fs: "length fs \<le> 2 ^ (C * k)" "\<forall>f\<in>set fs. CNF (width n k) f"
      "\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)"
      using C k nk by blast
    show "\<exists>fs. real (length fs) \<le> 2 powr (4 * real C * real n / real (width n k)) \<and>
            (\<forall>f\<in>set fs. CNF (width n k) f) \<and> (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>))"
    proof (intro exI[of _ fs] conjI)
      have "real (length fs) \<le> real ((2::nat) ^ (C * k))" using fs(1) by (simp only: of_nat_le_iff)
      also have "\<dots> = 2 powr (real C * real k)" by (simp add: powr_realpow[symmetric])
      also have "\<dots> \<le> 2 powr (4 * real C * real n / real (width n k))"
      proof (rule powr_mono)
        have "real C * real k \<le> real C * (4 * real n / real (width n k))"
          using k_width(2)[OF k kn] by (rule mult_left_mono) simp
        then show "real C * real k \<le> 4 * real C * real n / real (width n k)" by (simp add: ac_simps)
      qed simp
      finally show "real (length fs) \<le> 2 powr (4 * real C * real n / real (width n k))" .
    qed (use fs in auto)
  qed
qed

corollary majority_or_of_cnfs:
  "\<exists>C. \<forall>n k. 0 < k \<longrightarrow> n \<le> k * k \<longrightarrow> k \<le> n \<longrightarrow>
     (\<exists>fs. real (length fs) \<le> 2 powr (C * real n / real (width n k)) \<and>
          (\<forall>f\<in>set fs. CNF (width n k) f) \<and>
          (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma>))"
proof -
  obtain C where C: "\<forall>n k g. 0 < k \<longrightarrow> n \<le> k * k \<longrightarrow> k \<le> n \<longrightarrow>
     (\<exists>fs. real (length fs) \<le> 2 powr (C * real n / real (width n k)) \<and>
          (\<forall>f\<in>set fs. CNF (width n k) f) \<and>
          (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)))"
    using symmetric_or_of_cnfs_width by blast
  show ?thesis
  proof (intro exI[of _ C] allI impI)
    fix n k :: nat assume k: "0 < k" and nk: "n \<le> k * k" and kn: "k \<le> n"
    show "\<exists>fs. real (length fs) \<le> 2 powr (C * real n / real (width n k)) \<and>
            (\<forall>f\<in>set fs. CNF (width n k) f) \<and> (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma>)"
      using spec[OF spec[OF spec[OF C, of n], of k], of "\<lambda>w. n \<le> 2 * w"] k nk kn
      by (simp add: majority_def)
  qed
qed

section \<open>Consequence for local enumeration\<close>

text \<open>
  Some \<open>k'\<close>-CNF \<open>F\<close> in the cover of \<open>EXACT\<^sub>t\<close> has no satisfying assignment of weight other
  than \<open>t\<close> (so none at distance \<open>< t\<close> from \<open>0\<^sup>n\<close>), yet at least \<open>\<binom>n t / 2\<^sup>O\<^sup>(\<^sup>n\<^sup>/\<^sup>k\<^sup>'\<^sup>)\<close>
  satisfying assignments at distance exactly \<open>t\<close>.  Any algorithm for \<open>Enum(k', t)\<close> must
  list them all.  For \<open>t = \<lceil>n/2\<rceil>\<close> this is \<open>2\<^sup>(\<^sup>1\<^sup>-\<^sup>O\<^sup>(\<^sup>1\<^sup>/\<^sup>k\<^sup>'\<^sup>)\<^sup>)\<^sup>n\<close> up to a polynomial factor.
\<close>

lemma weight_set: "S \<subseteq> {..<n} \<Longrightarrow> weight n (\<lambda>i. i \<in> S) = card S"
proof -
  assume "S \<subseteq> {..<n}"
  then have "{i. i < n \<and> i \<in> S} = S" by auto
  then show ?thesis by (simp add: weight_def)
qed

theorem enum_output_lower_bound:
  "\<exists>C. \<forall>n k t. 0 < k \<longrightarrow> n \<le> k * k \<longrightarrow> k \<le> n \<longrightarrow> t \<le> n \<longrightarrow>
     (\<exists>F. CNF (width n k) F \<and> (\<forall>\<sigma>. eval \<sigma> F \<longrightarrow> weight n \<sigma> = t) \<and>
          real (n choose t) \<le> 2 powr (C * real n / real (width n k))
             * real (card {S. S \<subseteq> {..<n} \<and> card S = t \<and> eval (\<lambda>i. i \<in> S) F}))"
proof -
  obtain C where C: "\<forall>n k g. 0 < k \<longrightarrow> n \<le> k * k \<longrightarrow> k \<le> n \<longrightarrow>
     (\<exists>fs. real (length fs) \<le> 2 powr (C * real n / real (width n k)) \<and>
          (\<forall>f\<in>set fs. CNF (width n k) f) \<and>
          (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> g (weight n \<sigma>)))"
    using symmetric_or_of_cnfs_width by blast
  show ?thesis
  proof (intro exI[of _ C] allI impI)
    fix n k t :: nat assume k: "0 < k" and nk: "n \<le> k * k" and kn: "k \<le> n" and t: "t \<le> n"
    obtain fs where fs: "real (length fs) \<le> 2 powr (C * real n / real (width n k))"
      "\<forall>f\<in>set fs. CNF (width n k) f" "\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> weight n \<sigma> = t"
      using spec[OF spec[OF spec[OF C, of n], of k], of "\<lambda>w. w = t"] k nk kn by blast
    define A where "A = {S. S \<subseteq> {..<n} \<and> card S = t}"
    define X where "X F = {S \<in> A. eval (\<lambda>i. i \<in> S) F}" for F
    have finA: "finite A"
      by (rule finite_subset[of _ "Pow {..<n}"]) (auto simp: A_def)
    have cardA: "card A = n choose t"
      using n_subsets[of "{..<n}" t] by (simp add: A_def)
    have tA: "{..<t} \<in> A" using t by (auto simp: A_def)
    have cover: "A \<subseteq> (\<Union>F\<in>set fs. X F)"
    proof
      fix S assume S: "S \<in> A"
      then have "weight n (\<lambda>i. i \<in> S) = t" by (simp add: A_def weight_set)
      then obtain F where "F \<in> set fs" "eval (\<lambda>i. i \<in> S) F" using fs(3) by blast
      with S show "S \<in> (\<Union>F\<in>set fs. X F)" by (auto simp: X_def)
    qed
    have ne: "set fs \<noteq> {}"
    proof
      assume "set fs = {}"
      then have "A = {}" using cover by simp
      with tA show False by simp
    qed
    define m where "m = Max ((\<lambda>F. card (X F)) ` set fs)"
    have "m \<in> (\<lambda>F. card (X F)) ` set fs"
      unfolding m_def using ne by (intro Max_in) simp_all
    then obtain F where F: "F \<in> set fs" "card (X F) = m" by auto
    have le_m: "card (X G) \<le> m" if "G \<in> set fs" for G
      using that by (auto simp: m_def intro: Max_ge)
    have "n choose t = card A" by (simp add: cardA)
    also have "\<dots> \<le> card (\<Union>F\<in>set fs. X F)"
      using cover by (rule card_mono[rotated]) (auto simp: X_def finA)
    also have "\<dots> \<le> (\<Sum>G\<in>set fs. card (X G))" by (rule card_UN_le) simp
    also have "\<dots> \<le> card (set fs) * m"
      using sum_bounded_above[of "set fs" "\<lambda>G. card (X G)" m] le_m by simp
    also have "\<dots> \<le> length fs * m" by (intro mult_right_mono card_length) simp
    finally have nt: "real (n choose t) \<le> real (length fs) * real m" by (simp flip: of_nat_mult)
    have XF: "X F = {S. S \<subseteq> {..<n} \<and> card S = t \<and> eval (\<lambda>i. i \<in> S) F}"
      by (auto simp: X_def A_def)
    show "\<exists>F. CNF (width n k) F \<and> (\<forall>\<sigma>. eval \<sigma> F \<longrightarrow> weight n \<sigma> = t) \<and>
            real (n choose t) \<le> 2 powr (C * real n / real (width n k))
              * real (card {S. S \<subseteq> {..<n} \<and> card S = t \<and> eval (\<lambda>i. i \<in> S) F})"
    proof (intro exI[of _ F] conjI allI impI)
      show "CNF (width n k) F" using fs(2) F(1) by blast
      show "weight n \<sigma> = t" if "eval \<sigma> F" for \<sigma> using fs(3) F(1) that by blast
      have "real (n choose t) \<le> real (length fs) * real m" by (rule nt)
      also have "\<dots> \<le> 2 powr (C * real n / real (width n k)) * real m"
        using fs(1) by (rule mult_right_mono) simp
      finally show "real (n choose t) \<le> 2 powr (C * real n / real (width n k))
              * real (card {S. S \<subseteq> {..<n} \<and> card S = t \<and> eval (\<lambda>i. i \<in> S) F})"
        using F(2) XF by simp
    qed
  qed
qed

end
