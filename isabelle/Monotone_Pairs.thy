theory Monotone_Pairs
  imports "HOL-Library.FuncSet" "HOL.Binomial_Plus"
begin

section \<open>Monotone pairwise tests: an extremal problem\<close>

text \<open>
  Fix a partition into \<open>k\<close> blocks of size \<open>b\<close>.  A \<^emph>\<open>monotone, block-symmetric, pairwise\<close> test is
  an AND of monotone functions, each depending only on the weights \<open>(w\<^sub>i, w\<^sub>j)\<close> of two blocks.
  On block-weight vectors \<open>w : {..<k} \<rightarrow> {..b}\<close> it is given by up-closed relations \<open>P i j\<close>, and
  it is sound for Majority iff every accepted \<open>w\<close> has \<open>\<Sum>w \<ge> N\<close>.  It covers the weight vectors
  \<open>H\<close> with \<open>\<Sum>w = N\<close> that it accepts.  \<open>valid k N H\<close> characterises the sets \<open>H\<close> that arise this
  way (\<open>test_valid\<close>, \<open>valid_test\<close>): every \<open>z\<close> that is dominated on every pair of coordinates by
  some element of \<open>H\<close> has \<open>\<Sum>z \<ge> N\<close>.

  Main results: every point of a valid \<open>H\<close> has, for each coordinate \<open>l\<close>, a witness coordinate
  \<open>i\<close> (\<open>exchange\<close>) which determines \<open>p l\<close> from \<open>p i\<close> (\<open>determination\<close>), and hence
  \<open>|H| \<le> (k-1)\<^sup>k (b+1)\<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2\<close> (\<open>pairwise_count\<close>, Theorem A), with \<open>|H| \<le> 2(b+1)\<close> for
  \<open>k = 3\<close> (\<open>three_blocks\<close>).  Decoding in a fixed order removes the need to record witnesses:
  \<open>|H| \<le> 2\<^sup>k\<^sup>+\<^sup>1 (b+1)\<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2\<close>, and likewise for the number of inputs (\<open>sharp_bounds\<close>, Theorem B).  The matching test (pair up blocks, require complementary weights) is valid
  with \<open>|H| \<ge> (b+1)\<^sup>k\<^sup>/\<^sup>2\<close> (\<open>matching_valid\<close>, \<open>matching_card\<close>), so the exponent \<open>k/2\<close> is optimal.
\<close>

definition dom2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat) set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "dom2 k H z \<longleftrightarrow> (\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> (\<exists>h\<in>H. h i \<le> z i \<and> h j \<le> z j))"

definition valid :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set \<Rightarrow> bool" where
  "valid k N H \<longleftrightarrow> (\<forall>h\<in>H. (\<Sum>i<k. h i) = N) \<and> (\<forall>z. dom2 k H z \<longrightarrow> N \<le> (\<Sum>i<k. z i))"

subsection \<open>Lemma 1: valid sets are exactly the slices covered by sound pairwise tests\<close>

definition upclosed :: "(nat \<times> nat) set \<Rightarrow> bool" where
  "upclosed P \<longleftrightarrow> (\<forall>x y x' y'. (x, y) \<in> P \<longrightarrow> x \<le> x' \<longrightarrow> y \<le> y' \<longrightarrow> (x', y') \<in> P)"

definition accepts :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "accepts k P z \<longleftrightarrow> (\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> (z i, z j) \<in> P i j)"

lemma test_valid:
  assumes up: "\<forall>i j. upclosed (P i j)"
    and sound: "\<forall>z. accepts k P z \<longrightarrow> N \<le> (\<Sum>i<k. z i)"
    and H: "\<forall>h\<in>H. accepts k P h \<and> (\<Sum>i<k. h i) = N"
  shows "valid k N H"
  unfolding valid_def
proof (intro conjI allI impI ballI)
  show "(\<Sum>i<k. h i) = N" if "h \<in> H" for h using H that by blast
  fix z assume d: "dom2 k H z"
  have "accepts k P z"
    unfolding accepts_def
  proof (intro allI impI)
    fix i j assume ij: "i < k" "j < k" "i \<noteq> j"
    then obtain h where h: "h \<in> H" "h i \<le> z i" "h j \<le> z j" using d by (auto simp: dom2_def)
    then have "(h i, h j) \<in> P i j" using H ij by (auto simp: accepts_def)
    then show "(z i, z j) \<in> P i j" using up h by (auto simp: upclosed_def)
  qed
  then show "N \<le> (\<Sum>i<k. z i)" using sound by blast
qed

lemma valid_test:
  assumes v: "valid k N H"
  defines "P \<equiv> \<lambda>i j. {(x, y). \<exists>h\<in>H. h i \<le> x \<and> h j \<le> y}"
  shows "\<forall>i j. upclosed (P i j)"
    and "\<forall>z. accepts k P z \<longrightarrow> N \<le> (\<Sum>i<k. z i)"
    and "\<forall>h\<in>H. accepts k P h \<and> (\<Sum>i<k. h i) = N"
proof -
  show "\<forall>i j. upclosed (P i j)"
    by (auto simp: upclosed_def P_def intro: order_trans)
  show "\<forall>z. accepts k P z \<longrightarrow> N \<le> (\<Sum>i<k. z i)"
  proof (intro allI impI)
    fix z assume "accepts k P z"
    then have "dom2 k H z" by (auto simp: accepts_def dom2_def P_def)
    then show "N \<le> (\<Sum>i<k. z i)" using v by (simp add: valid_def)
  qed
  show "\<forall>h\<in>H. accepts k P h \<and> (\<Sum>i<k. h i) = N"
    using v by (auto simp: accepts_def P_def valid_def)
qed

subsection \<open>Lemma 2: exchange\<close>

lemma exchange:
  assumes v: "valid k N H" and k: "2 \<le> k" and p: "p \<in> H" and l: "l < k"
  shows "\<exists>i<k. i \<noteq> l \<and> (\<forall>h\<in>H. h l < p l \<longrightarrow> p i < h i)"
proof (rule ccontr)
  assume neg: "\<not> (\<exists>i<k. i \<noteq> l \<and> (\<forall>h\<in>H. h l < p l \<longrightarrow> p i < h i))"
  define A where "A = {..<k} - {l}"
  have "\<forall>i\<in>A. \<exists>h. h \<in> H \<and> h l < p l \<and> h i \<le> p i"
  proof
    fix i assume "i \<in> A"
    then have "i < k" "i \<noteq> l" by (auto simp: A_def)
    then have "\<not> (\<forall>h\<in>H. h l < p l \<longrightarrow> p i < h i)" using neg by blast
    then show "\<exists>h. h \<in> H \<and> h l < p l \<and> h i \<le> p i" by (auto simp: not_less)
  qed
  from bchoice[OF this] obtain g where g: "\<forall>i\<in>A. g i \<in> H \<and> g i l < p l \<and> g i i \<le> p i"
    by blast
  have finA: "finite A" by (simp add: A_def)
  have "(if l = 0 then 1 else 0) \<in> A" using k by (auto simp: A_def)
  then have neA: "A \<noteq> {}" by blast
  define m where "m = Max ((\<lambda>i. g i l) ` A)"
  have m_lt: "m < p l" using g finA neA by (simp add: m_def)
  have m_ge: "g i l \<le> m" if "i \<in> A" for i
    unfolding m_def using finA that by (intro Max_ge) simp_all
  define z where "z = p(l := m)"
  have "dom2 k H z"
    unfolding dom2_def
  proof (intro allI impI)
    fix i j assume ij: "i < k" "j < k" "i \<noteq> j"
    show "\<exists>h\<in>H. h i \<le> z i \<and> h j \<le> z j"
    proof (cases "i = l")
      case True
      then have j: "j \<in> A" using ij by (auto simp: A_def)
      then have "g j \<in> H" "g j i \<le> z i" "g j j \<le> z j"
        using g m_ge[OF j] True ij(3) by (auto simp: z_def)
      then show ?thesis by blast
    next
      case False
      show ?thesis
      proof (cases "j = l")
        case True
        then have i: "i \<in> A" using ij False by (auto simp: A_def)
        then have "g i \<in> H" "g i i \<le> z i" "g i j \<le> z j"
          using g m_ge[OF i] True False by (auto simp: z_def)
        then show ?thesis by blast
      next
        assume jl: "j \<noteq> l"
        have "p i \<le> z i" "p j \<le> z j" using False jl by (simp_all add: z_def)
        then show ?thesis using p by blast
      qed
    qed
  qed
  then have "N \<le> (\<Sum>i<k. z i)" using v by (simp add: valid_def)
  moreover have "(\<Sum>i<k. z i) < (\<Sum>i<k. p i)"
    using l m_lt by (intro sum_strict_mono_ex1) (auto simp: z_def)
  moreover have "(\<Sum>i<k. p i) = N" using v p by (simp add: valid_def)
  ultimately show False by simp
qed

subsection \<open>Lemma 3: determination\<close>

definition mu :: "(nat \<Rightarrow> nat) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mu H i l x = (LEAST y. \<exists>h\<in>H. h i \<le> x \<and> h l = y)"

lemma determination:
  assumes p: "p \<in> H" and w: "\<forall>h\<in>H. h l < p l \<longrightarrow> p i < h i"
  shows "p l = mu H i l (p i)"
  unfolding mu_def
proof (rule Least_equality[symmetric])
  show "\<exists>h\<in>H. h i \<le> p i \<and> h l = p l" using p by blast
  fix y assume "\<exists>h\<in>H. h i \<le> p i \<and> h l = y"
  then obtain h where "h \<in> H" "h i \<le> p i" "h l = y" by blast
  then show "p l \<le> y" using w by (metis not_less)
qed

subsection \<open>Theorem A: \<open>|H| \<le> (k-1)\<^sup>k (b+1)\<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2\<close>\<close>

text \<open>Fixed-point-free maps on \<open>{..<k}\<close>, and the witness property for a whole map.\<close>

definition fpf :: "nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "fpf k = (\<Pi>\<^sub>E l\<in>{..<k}. {..<k} - {l})"

definition witf :: "(nat \<Rightarrow> nat) set \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "witf H k f p \<longleftrightarrow> (\<forall>l<k. \<forall>h\<in>H. h l < p l \<longrightarrow> p (f l) < h (f l))"

lemma fpf_mem: "f \<in> fpf k \<Longrightarrow> l < k \<Longrightarrow> f l < k \<and> f l \<noteq> l"
  by (auto simp: fpf_def dest: PiE_mem)

lemma witf_exists:
  assumes v: "valid k N H" and k: "2 \<le> k" and p: "p \<in> H"
  shows "\<exists>f\<in>fpf k. witf H k f p"
proof -
  have "\<forall>l\<in>{..<k}. \<exists>i. i \<in> {..<k} - {l} \<and> (\<forall>h\<in>H. h l < p l \<longrightarrow> p i < h i)"
    using exchange[OF v k p] by blast
  from bchoice[OF this] obtain f
    where f: "\<forall>l\<in>{..<k}. f l \<in> {..<k} - {l} \<and> (\<forall>h\<in>H. h l < p l \<longrightarrow> p (f l) < h (f l))"
    by blast
  show ?thesis
    by (rule bexI[of _ "restrict f {..<k}"]) (use f in \<open>auto simp: fpf_def witf_def\<close>)
qed

lemma desc_meets:
  assumes "finite (D :: nat set)" "D \<noteq> {}" "\<forall>l\<in>D. f l \<in> D \<and> f l \<noteq> l"
  shows "\<exists>l\<in>D. f l < l"
proof -
  have m: "Max D \<in> D" using assms by simp
  then have "f (Max D) \<in> D" "f (Max D) \<noteq> Max D" using assms(3) by auto
  then have "f (Max D) < Max D" using assms(1) by (simp add: order_neq_le_trans)
  with m show ?thesis by blast
qed

lemma asc_meets:
  assumes "finite (D :: nat set)" "D \<noteq> {}" "\<forall>l\<in>D. f l \<in> D \<and> f l \<noteq> l"
  shows "\<exists>l\<in>D. l < f l"
proof -
  have m: "Min D \<in> D" using assms by simp
  then have "f (Min D) \<in> D" "f (Min D) \<noteq> Min D" using assms(3) by auto
  then have "Min D < f (Min D)" using assms(1) by (simp add: order_neq_le_trans)
  with m show ?thesis by blast
qed

text \<open>
  The smaller of the descent set \<open>{l. f l < l}\<close> and the ascent set \<open>{l. l < f l}\<close>; it meets
  every cycle of \<open>f\<close>.
\<close>

definition Rs :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "Rs k f = (if card {l. l < k \<and> f l < l} \<le> card {l. l < k \<and> l < f l}
             then {l. l < k \<and> f l < l} else {l. l < k \<and> l < f l})"

lemma Rs_sub: "Rs k f \<subseteq> {..<k}"
  by (auto simp: Rs_def)

lemma Rs_card:
  assumes f: "f \<in> fpf k" shows "card (Rs k f) \<le> k div 2"
proof -
  let ?A = "{l. l < k \<and> f l < l}" and ?B = "{l. l < k \<and> l < f l}"
  have "?A \<union> ?B = {..<k}" using fpf_mem[OF f] by (auto simp: nat_neq_iff)
  moreover have "?A \<inter> ?B = {}" by auto
  ultimately have AB: "card ?A + card ?B = k"
    using card_Un_disjoint[of ?A ?B] by simp
  have "2 * card (Rs k f) \<le> k" using AB by (simp add: Rs_def)
  then show ?thesis using div_le_mono[of "2 * card (Rs k f)" k 2] by simp
qed

lemma Rs_meets:
  assumes f: "f \<in> fpf k" and D: "D \<subseteq> {..<k}" "D \<noteq> {}" and cl: "\<forall>l\<in>D. f l \<in> D"
  shows "D \<inter> Rs k f \<noteq> {}"
proof -
  have finD: "finite D" using D(1) finite_subset by blast
  have ne: "\<forall>l\<in>D. f l \<in> D \<and> f l \<noteq> l" using cl fpf_mem[OF f] D(1) by blast
  obtain a where a: "a \<in> D" "f a < a" using desc_meets[OF finD D(2) ne] by blast
  obtain c where c: "c \<in> D" "c < f c" using asc_meets[OF finD D(2) ne] by blast
  show ?thesis using a c D(1) by (auto simp: Rs_def)
qed

lemma determined:
  assumes f: "f \<in> fpf k" and p: "p \<in> H" "witf H k f p" and q: "q \<in> H" "witf H k f q"
    and box: "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" "q \<in> {..<k} \<rightarrow>\<^sub>E {..b}"
    and agree: "\<forall>l\<in>Rs k f. p l = q l"
  shows "p = q"
proof -
  define D where "D = {l. l < k \<and> p l \<noteq> q l}"
  have cl: "\<forall>l\<in>D. f l \<in> D"
  proof
    fix l assume "l \<in> D"
    then have l: "l < k" "p l \<noteq> q l" by (auto simp: D_def)
    have fl: "f l < k" using fpf_mem[OF f l(1)] by simp
    have "p l = mu H (f l) l (p (f l))"
      using p(2) l(1) by (intro determination[OF p(1)]) (simp add: witf_def)
    moreover have "q l = mu H (f l) l (q (f l))"
      using q(2) l(1) by (intro determination[OF q(1)]) (simp add: witf_def)
    ultimately have "p (f l) \<noteq> q (f l)" using l(2) by metis
    then show "f l \<in> D" using fl by (simp add: D_def)
  qed
  have "D = {}"
  proof (rule ccontr)
    assume "D \<noteq> {}"
    then have "D \<inter> Rs k f \<noteq> {}" using Rs_meets[OF f _ _ cl] by (auto simp: D_def)
    then obtain l where "l \<in> D" "l \<in> Rs k f" by blast
    then show False using agree by (simp add: D_def)
  qed
  then show "p = q" using box by (intro PiE_ext[of p "{..<k}" "\<lambda>_. {..b}" q]) (auto simp: D_def)
qed

lemma card_fpf: "card (fpf k) = (k - 1) ^ k"
proof -
  have "card (fpf k) = (\<Prod>l<k. card ({..<k} - {l}))" by (simp add: fpf_def card_PiE)
  also have "\<dots> = (\<Prod>l<k. k - 1)" by (rule prod.cong) simp_all
  also have "\<dots> = (k - 1) ^ k" by simp
  finally show ?thesis .
qed

text \<open>
  Counting by classes.  If \<open>H\<close> is covered by the classes \<open>Cl a\<close>, \<open>a \<in> I\<close>, and each class is
  determined by its values on a set \<open>R a\<close> of at most \<open>k div 2\<close> coordinates, then
  \<open>|H| \<le> |I| (b+1)\<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2\<close>, and similarly for the number of inputs.  Theorem A takes the classes
  to be the witness maps; Theorem B below needs only \<open>2\<^sup>k\<^sup>+\<^sup>1\<close> classes.
\<close>

lemma class_bounds:
  fixes k :: nat
  assumes box: "S \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" and R: "R \<subseteq> {..<k}"
    and inj: "inj_on (\<lambda>p. restrict p R) S"
  shows "card S \<le> (b + 1) ^ card R"
    and "(\<Sum>p\<in>S. \<Prod>i\<in>R. b choose p i) \<le> (2 ^ b) ^ card R"
proof -
  let ?r = "\<lambda>p. restrict p R"
  have finR: "finite R" using R by (rule finite_subset) simp
  have img: "?r ` S \<subseteq> R \<rightarrow>\<^sub>E {..b}"
  proof
    fix r assume "r \<in> ?r ` S"
    then obtain p where p: "p \<in> S" "r = ?r p" by blast
    then have "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" using box by blast
    then show "r \<in> R \<rightarrow>\<^sub>E {..b}" using p(2) R by (auto simp: restrict_PiE_iff)
  qed
  have "card S = card (?r ` S)" using inj by (simp add: card_image)
  also have "\<dots> \<le> card (R \<rightarrow>\<^sub>E {..b})" using img finR by (intro card_mono finite_PiE) auto
  also have "\<dots> = (b + 1) ^ card R" using finR by (simp add: card_PiE)
  finally show "card S \<le> (b + 1) ^ card R" .
  have rr: "(\<Prod>i\<in>R. b choose ?r p i) = (\<Prod>i\<in>R. b choose p i)" for p
    by (rule prod.cong) simp_all
  have "(\<Sum>p\<in>S. \<Prod>i\<in>R. b choose p i) = (\<Sum>r\<in>?r ` S. \<Prod>i\<in>R. b choose r i)"
    using inj by (simp add: sum.reindex rr)
  also have "\<dots> \<le> (\<Sum>r\<in>R \<rightarrow>\<^sub>E {..b}. \<Prod>i\<in>R. b choose r i)"
    using img finR by (intro sum_mono2 finite_PiE) auto
  also have "\<dots> = (\<Prod>i\<in>R. \<Sum>x\<le>b. b choose x)"
    using finR by (subst prod_sum_PiE) simp_all
  also have "\<dots> = (2 ^ b) ^ card R" by (simp add: choose_row_sum)
  finally show "(\<Sum>p\<in>S. \<Prod>i\<in>R. b choose p i) \<le> (2 ^ b) ^ card R" .
qed

lemma trade:
  fixes M B :: nat
  assumes a: "M \<le> B" "r \<le> r'" "r' \<le> k"
  shows "M ^ (k - r) * B ^ r \<le> B ^ r' * M ^ (k - r')"
proof -
  have e: "k - r = (k - r') + (r' - r)" using a by simp
  have "M ^ (k - r) * B ^ r = M ^ (k - r') * (M ^ (r' - r) * B ^ r)"
    by (simp add: e power_add mult_ac)
  also have "\<dots> \<le> M ^ (k - r') * (B ^ (r' - r) * B ^ r)"
    by (intro mult_left_mono mult_right_mono power_mono) (simp_all add: a)
  also have "B ^ (r' - r) * B ^ r = B ^ r'"
    using a by (simp add: power_add[symmetric])
  finally show ?thesis by (simp add: mult_ac)
qed

text \<open>
  The weighted count, for classes determined by their values on at most \<open>m\<close> coordinates.
\<close>

lemma classes_gen:
  assumes box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" and I: "finite I"
    and cover: "H \<subseteq> (\<Union>a\<in>I. Cl a)" and sub: "\<forall>a\<in>I. Cl a \<subseteq> H"
    and R: "\<forall>a\<in>I. R a \<subseteq> {..<k} \<and> card (R a) \<le> m" and m: "m \<le> k"
    and inj: "\<forall>a\<in>I. inj_on (\<lambda>p. restrict p (R a)) (Cl a)"
  shows "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i) \<le> card I * ((2 ^ b) ^ m * (b choose (b div 2)) ^ (k - m))"
proof -
  define M where "M = b choose (b div 2)"
  define wt where "wt p = (\<Prod>i<k. b choose p i)" for p :: "nat \<Rightarrow> nat"
  have finH: "finite H" using box by (rule finite_subset) (intro finite_PiE; simp)
  have boxa: "Cl a \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" if "a \<in> I" for a using sub box that by blast
  have Ra: "R a \<subseteq> {..<k}" "card (R a) \<le> m" if "a \<in> I" for a using R that by auto
  have injs: "inj_on (\<lambda>p. restrict p (R a)) (Cl a)" if "a \<in> I" for a using inj that by blast
  have M2: "M \<le> 2 ^ b"
  proof -
    have "b choose (b div 2) \<le> (\<Sum>x\<le>b. b choose x)" by (rule member_le_sum) simp_all
    then show ?thesis by (simp add: M_def choose_row_sum)
  qed
  have each: "(\<Sum>p\<in>Cl a. wt p) \<le> (2 ^ b) ^ m * M ^ (k - m)" if a: "a \<in> I" for a
  proof -
    have finR: "finite (R a)" using Ra(1)[OF a] by (rule finite_subset) simp
    have split: "wt p \<le> (\<Prod>i\<in>R a. b choose p i) * M ^ (k - card (R a))" for p
    proof -
      have eq: "wt p = (\<Prod>i\<in>R a. b choose p i) * (\<Prod>i\<in>{..<k} - R a. b choose p i)"
        unfolding wt_def using Ra(1)[OF a] prod.subset_diff[of "R a" "{..<k}" "\<lambda>i. b choose p i"]
        by (simp add: mult.commute)
      have "(\<Prod>i\<in>{..<k} - R a. b choose p i) \<le> (\<Prod>i\<in>{..<k} - R a. M)"
        by (rule prod_mono) (simp add: M_def binomial_maximum)
      also have "\<dots> = M ^ (k - card (R a))"
        using Ra(1)[OF a] finR by (simp add: card_Diff_subset)
      finally show ?thesis using eq by (simp add: mult_left_mono)
    qed
    have S: "(\<Sum>p\<in>Cl a. \<Prod>i\<in>R a. b choose p i) \<le> (2 ^ b) ^ card (R a)"
      by (rule class_bounds(2)[OF boxa[OF a] Ra(1)[OF a] injs[OF a]])
    have "(\<Sum>p\<in>Cl a. wt p) \<le> (\<Sum>p\<in>Cl a. (\<Prod>i\<in>R a. b choose p i) * M ^ (k - card (R a)))"
      by (rule sum_mono) (rule split)
    also have "\<dots> = M ^ (k - card (R a)) * (\<Sum>p\<in>Cl a. \<Prod>i\<in>R a. b choose p i)"
      by (simp add: sum_distrib_left mult.commute)
    also have "\<dots> \<le> M ^ (k - card (R a)) * (2 ^ b) ^ card (R a)" using S by (rule mult_left_mono) simp
    also have "\<dots> \<le> (2 ^ b) ^ m * M ^ (k - m)"
      using M2 Ra(2)[OF a] m by (intro trade) simp_all
    finally show ?thesis .
  qed
  have "(\<Sum>p\<in>H. wt p) \<le> (\<Sum>p\<in>H. \<Sum>a\<in>I. if p \<in> Cl a then wt p else 0)"
  proof (rule sum_mono)
    fix p assume "p \<in> H"
    then obtain a where a: "a \<in> I" "p \<in> Cl a" using cover by blast
    have "wt p = (if p \<in> Cl a then wt p else 0)" using a by simp
    also have "\<dots> \<le> (\<Sum>a\<in>I. if p \<in> Cl a then wt p else 0)"
      by (rule member_le_sum) (use a I in auto)
    finally show "wt p \<le> (\<Sum>a\<in>I. if p \<in> Cl a then wt p else 0)" .
  qed
  also have "\<dots> = (\<Sum>a\<in>I. \<Sum>p\<in>H. if p \<in> Cl a then wt p else 0)" by (rule sum.swap)
  also have "\<dots> = (\<Sum>a\<in>I. \<Sum>p\<in>Cl a. wt p)"
  proof (rule sum.cong[OF refl])
    fix a assume a: "a \<in> I"
    have "(\<Sum>p\<in>H. if p \<in> Cl a then wt p else 0) = sum wt (H \<inter> Cl a)"
      by (rule sum.inter_restrict[OF finH, symmetric])
    also have "H \<inter> Cl a = Cl a" using sub a by blast
    finally show "(\<Sum>p\<in>H. if p \<in> Cl a then wt p else 0) = (\<Sum>p\<in>Cl a. wt p)" .
  qed
  also have "\<dots> \<le> (\<Sum>a\<in>I. (2 ^ b) ^ m * M ^ (k - m))"
    using each by (intro sum_mono) blast
  also have "\<dots> = card I * ((2 ^ b) ^ m * M ^ (k - m))" by simp
  finally show "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> card I * ((2 ^ b) ^ m * (b choose (b div 2)) ^ (k - m))"
    by (simp add: wt_def M_def)
qed

lemma classes:
  assumes box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" and I: "finite I"
    and cover: "H \<subseteq> (\<Union>a\<in>I. Cl a)" and sub: "\<forall>a\<in>I. Cl a \<subseteq> H"
    and R: "\<forall>a\<in>I. R a \<subseteq> {..<k} \<and> card (R a) \<le> k div 2"
    and inj: "\<forall>a\<in>I. inj_on (\<lambda>p. restrict p (R a)) (Cl a)"
  shows "card H \<le> card I * (b + 1) ^ (k div 2)"
    and "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> card I * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
proof -
  have finH: "finite H" using box by (rule finite_subset) (intro finite_PiE; simp)
  have boxa: "Cl a \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" if "a \<in> I" for a using sub box that by blast
  have Ra: "R a \<subseteq> {..<k}" "card (R a) \<le> k div 2" if "a \<in> I" for a using R that by auto
  have injs: "inj_on (\<lambda>p. restrict p (R a)) (Cl a)" if "a \<in> I" for a using inj that by blast
  have finU: "finite (\<Union>a\<in>I. Cl a)" using sub by (intro finite_subset[OF _ finH]) blast
  have "card H \<le> card (\<Union>a\<in>I. Cl a)" using cover finU by (rule card_mono[rotated])
  also have "\<dots> \<le> (\<Sum>a\<in>I. card (Cl a))" by (rule card_UN_le[OF I])
  also have "\<dots> \<le> (\<Sum>a\<in>I. (b + 1) ^ (k div 2))"
  proof (rule sum_mono)
    fix a assume a: "a \<in> I"
    have "card (Cl a) \<le> (b + 1) ^ card (R a)"
      by (rule class_bounds(1)[OF boxa[OF a] Ra(1)[OF a] injs[OF a]])
    also have "\<dots> \<le> (b + 1) ^ (k div 2)" using Ra(2)[OF a] by (intro power_increasing) simp_all
    finally show "card (Cl a) \<le> (b + 1) ^ (k div 2)" .
  qed
  also have "\<dots> = card I * (b + 1) ^ (k div 2)" by simp
  finally show "card H \<le> card I * (b + 1) ^ (k div 2)" .
  show "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> card I * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
    by (rule classes_gen[OF box I cover sub R _ inj]) simp
qed

text \<open>
  Theorem A only uses the witness maps: if every point has a witness map in a family \<open>F\<close>,
  then \<open>|H| \<le> |F| (b+1)\<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2\<close>, and similarly for the number of inputs.
\<close>

lemma witness_classes:
  assumes box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" and F: "F \<subseteq> fpf k" "finite F"
    and wit: "\<forall>p\<in>H. \<exists>f\<in>F. witf H k f p"
  shows "card H \<le> card F * (b + 1) ^ (k div 2)"
    and "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> card F * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
proof -
  define Hf where "Hf f = {p \<in> H. witf H k f p}" for f
  have cover: "H \<subseteq> (\<Union>f\<in>F. Hf f)" using wit by (auto simp: Hf_def)
  have sub: "\<forall>f\<in>F. Hf f \<subseteq> H" by (auto simp: Hf_def)
  have R: "\<forall>f\<in>F. Rs k f \<subseteq> {..<k} \<and> card (Rs k f) \<le> k div 2"
    using F(1) Rs_sub Rs_card by blast
  have inj: "\<forall>f\<in>F. inj_on (\<lambda>p. restrict p (Rs k f)) (Hf f)"
  proof
    fix f assume "f \<in> F"
    then have f: "f \<in> fpf k" using F(1) by blast
    show "inj_on (\<lambda>p. restrict p (Rs k f)) (Hf f)"
    proof (rule inj_onI)
      fix p q assume pq: "p \<in> Hf f" "q \<in> Hf f"
        and eq: "restrict p (Rs k f) = restrict q (Rs k f)"
      have "\<forall>l\<in>Rs k f. p l = q l" using eq by (metis restrict_apply')
      then show "p = q" using pq box by (intro determined[OF f]) (auto simp: Hf_def)
    qed
  qed
  show "card H \<le> card F * (b + 1) ^ (k div 2)"
    by (rule classes(1)[OF box F(2) cover sub R inj])
  show "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> card F * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
    by (rule classes(2)[OF box F(2) cover sub R inj])
qed

lemmas count_via = witness_classes(1)
lemmas weight_via = witness_classes(2)

theorem pairwise_count:
  assumes v: "valid k N H" and k: "2 \<le> k" and box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}"
  shows "card H \<le> (k - 1) ^ k * (b + 1) ^ (k div 2)"
proof -
  have wit: "\<forall>p\<in>H. \<exists>f\<in>fpf k. witf H k f p" using witf_exists[OF v k] by blast
  have fin: "finite (fpf k)" by (simp add: fpf_def finite_PiE)
  show ?thesis using count_via[OF box subset_refl fin wit] by (simp add: card_fpf)
qed

subsection \<open>Theorem A, weighted by the number of inputs per weight vector\<close>

text \<open>
  A weight vector \<open>p\<close> stands for \<open>\<Prod>\<^sub>i C(b, p\<^sub>i)\<close> inputs.  The weighted bound below, divided by
  \<open>C(kb, kb/2)\<close>, bounds the fraction of the Majority slice that one test covers; the central
  binomial estimates turn it into \<open>(k-1)\<^sup>k (\<pi>b/2)\<^sup>-\<^sup>k\<^sup>/\<^sup>4 \<surd>(2kb)\<close>.
\<close>

theorem pairwise_weight:
  assumes v: "valid k N H" and k: "2 \<le> k" and box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}"
  shows "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> (k - 1) ^ k * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
proof -
  have wit: "\<forall>p\<in>H. \<exists>f\<in>fpf k. witf H k f p" using witf_exists[OF v k] by blast
  have fin: "finite (fpf k)" by (simp add: fpf_def finite_PiE)
  show ?thesis using weight_via[OF box subset_refl fin wit] by (simp add: card_fpf)
qed

subsection \<open>Theorem B: \<open>|H| \<le> 2\<^sup>k\<^sup>+\<^sup>1 (b+1)\<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2\<close>\<close>

text \<open>
  The witness map need not be recorded.  Decode the coordinates of \<open>p\<close> in a fixed order \<open>r\<close>,
  and call \<open>l\<close> \<^emph>\<open>free\<close> if every witness for \<open>(p, l)\<close> comes after \<open>l\<close>.  If some witness \<open>i\<close>
  comes before \<open>l\<close>, then \<open>p l = mu H i l (p i)\<close>, while \<open>mu H j l (p j) \<le> p l\<close> for every \<open>j\<close>;
  so \<open>p l\<close> is the largest value \<open>mu H j l (p j)\<close> over earlier \<open>j\<close>.  Hence \<open>p\<close> is determined
  by its free set and its values there (\<open>free_determined\<close>).  No coordinate is free both in an
  order and in its reverse, so one of the two free sets has at most \<open>k div 2\<close> elements
  (\<open>free_small\<close>).  This replaces the \<open>(k-1)\<^sup>k\<close> witness maps of Theorem A by \<open>2\<^sup>k\<^sup>+\<^sup>1\<close> classes.
\<close>

definition wit :: "(nat \<Rightarrow> nat) set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wit H p i l \<longleftrightarrow> (\<forall>h\<in>H. h l < p l \<longrightarrow> p i < h i)"

definition free :: "(nat \<Rightarrow> nat) set \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "free H k r p = {l. l < k \<and> (\<forall>i<k. i \<noteq> l \<longrightarrow> wit H p i l \<longrightarrow> r l < r i)}"

lemma mu_le: "q \<in> H \<Longrightarrow> mu H i l (q i) \<le> q l"
  unfolding mu_def by (rule Least_le) blast

lemma free_determined:
  assumes r: "inj_on r {..<k}" and p: "p \<in> H" and q: "q \<in> H"
    and box: "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" "q \<in> {..<k} \<rightarrow>\<^sub>E {..b}"
    and F: "free H k r p = free H k r q" and agree: "\<forall>l\<in>free H k r p. p l = q l"
  shows "p = q"
proof -
  have earlier: "\<exists>i<k. r i < r l \<and> wit H s i l"
    if s: "s = p \<or> s = q" and l: "l < k" "l \<notin> free H k r p" for s l
  proof -
    have "l \<notin> free H k r s" using s l F by auto
    then obtain i where i: "i < k" "i \<noteq> l" "wit H s i l" "\<not> r l < r i"
      using l(1) by (auto simp: free_def)
    have "r i \<noteq> r l" using r i(1,2) l(1) by (auto dest: inj_onD)
    then show ?thesis using i by auto
  qed
  have all: "\<forall>l<k. r l = m \<longrightarrow> p l = q l" for m
  proof (induction m rule: less_induct)
    case (less m)
    show ?case
    proof (intro allI impI)
      fix l assume l: "l < k" "r l = m"
      show "p l = q l"
      proof (cases "l \<in> free H k r p")
        case True
        then show ?thesis using agree by blast
      next
        case False
        obtain i where i: "i < k" "r i < r l" "wit H p i l" using earlier[of p l] l False by blast
        obtain j where j: "j < k" "r j < r l" "wit H q j l" using earlier[of q l] l False by blast
        have pi: "p i = q i" using less.IH[of "r i"] i l by simp
        have pj: "p j = q j" using less.IH[of "r j"] j l by simp
        have "p l = mu H i l (p i)"
          by (rule determination[OF p]) (use i(3) in \<open>simp add: wit_def\<close>)
        also have "\<dots> = mu H i l (q i)" using pi by simp
        also have "\<dots> \<le> q l" by (rule mu_le[OF q])
        finally have le1: "p l \<le> q l" .
        have "q l = mu H j l (q j)"
          by (rule determination[OF q]) (use j(3) in \<open>simp add: wit_def\<close>)
        also have "\<dots> = mu H j l (p j)" using pj by simp
        also have "\<dots> \<le> p l" by (rule mu_le[OF p])
        finally have "q l \<le> p l" .
        with le1 show ?thesis by simp
      qed
    qed
  qed
  have "p l = q l" if "l \<in> {..<k}" for l using all[of "r l"] that by blast
  then show "p = q" using box by (intro PiE_ext[of p "{..<k}" "\<lambda>_. {..b}" q]) auto
qed

lemma free_small:
  assumes v: "valid k N H" and k: "2 \<le> k" and p: "p \<in> H"
  shows "card (free H k (\<lambda>i. i) p) \<le> k div 2 \<or> card (free H k (\<lambda>i. k - i) p) \<le> k div 2"
proof -
  let ?A = "free H k (\<lambda>i. i) p" and ?B = "free H k (\<lambda>i. k - i) p"
  have disj: "?A \<inter> ?B = {}"
  proof (rule ccontr)
    assume "?A \<inter> ?B \<noteq> {}"
    then obtain l where l: "l \<in> ?A" "l \<in> ?B" by blast
    then have lk: "l < k" by (simp add: free_def)
    obtain i where i: "i < k" "i \<noteq> l" "\<forall>h\<in>H. h l < p l \<longrightarrow> p i < h i"
      using exchange[OF v k p lk] by blast
    have w: "wit H p i l" using i(3) by (simp add: wit_def)
    have "l < i" using l(1) i(1,2) w by (simp add: free_def)
    moreover have "k - l < k - i" using l(2) i(1,2) w by (simp add: free_def)
    ultimately show False by simp
  qed
  have finA: "finite ?A" by (rule finite_subset[of _ "{..<k}"]) (auto simp: free_def)
  have finB: "finite ?B" by (rule finite_subset[of _ "{..<k}"]) (auto simp: free_def)
  have "card (?A \<union> ?B) \<le> card {..<k}" by (rule card_mono) (auto simp: free_def)
  then have "card ?A + card ?B \<le> k" using card_Un_disjoint[OF finA finB disj] by simp
  moreover have "k = 2 * (k div 2) + k mod 2" "k mod 2 < 2" by simp_all
  ultimately show ?thesis by linarith
qed

theorem sharp_bounds:
  assumes v: "valid k N H" and k: "2 \<le> k" and box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}"
  shows "card H \<le> 2 ^ (k + 1) * (b + 1) ^ (k div 2)"
    and "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> 2 ^ (k + 1) * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
proof -
  define r where "r d = (if d then (\<lambda>i. i) else (\<lambda>i. k - i))" for d :: bool
  define I where "I = (UNIV :: bool set) \<times> {S. S \<subseteq> {..<k} \<and> card S \<le> k div 2}"
  define Cl where "Cl a = {p \<in> H. free H k (r (fst a)) p = snd a}" for a :: "bool \<times> nat set"
  have rinj: "inj_on (r d) {..<k}" for d by (cases d) (auto simp: r_def inj_on_def)
  have I_sub: "I \<subseteq> UNIV \<times> Pow {..<k}" by (auto simp: I_def)
  have finI: "finite I" using I_sub by (rule finite_subset) simp
  have cardI: "card I \<le> 2 ^ (k + 1)"
  proof -
    have "card I \<le> card ((UNIV :: bool set) \<times> Pow {..<k})" by (rule card_mono[OF _ I_sub]) simp
    also have "\<dots> = 2 ^ (k + 1)" by (simp add: card_cartesian_product card_Pow)
    finally show ?thesis .
  qed
  have cover: "H \<subseteq> (\<Union>a\<in>I. Cl a)"
  proof
    fix p assume p: "p \<in> H"
    have "card (free H k (r True) p) \<le> k div 2 \<or> card (free H k (r False) p) \<le> k div 2"
      using free_small[OF v k p] by (simp add: r_def)
    then obtain d where d: "card (free H k (r d) p) \<le> k div 2" by blast
    have "free H k (r d) p \<subseteq> {..<k}" by (auto simp: free_def)
    then have "(d, free H k (r d) p) \<in> I" using d by (simp add: I_def)
    moreover have "p \<in> Cl (d, free H k (r d) p)" using p by (simp add: Cl_def)
    ultimately show "p \<in> (\<Union>a\<in>I. Cl a)" by blast
  qed
  have sub: "\<forall>a\<in>I. Cl a \<subseteq> H" by (auto simp: Cl_def)
  have R: "\<forall>a\<in>I. snd a \<subseteq> {..<k} \<and> card (snd a) \<le> k div 2" by (auto simp: I_def)
  have inj: "\<forall>a\<in>I. inj_on (\<lambda>p. restrict p (snd a)) (Cl a)"
  proof
    fix a assume "a \<in> I"
    show "inj_on (\<lambda>p. restrict p (snd a)) (Cl a)"
    proof (rule inj_onI)
      fix p q assume p: "p \<in> Cl a" and q: "q \<in> Cl a"
        and eq: "restrict p (snd a) = restrict q (snd a)"
      have pH: "p \<in> H" and qH: "q \<in> H" using p q by (auto simp: Cl_def)
      have Sp: "free H k (r (fst a)) p = snd a" and Sq: "free H k (r (fst a)) q = snd a"
        using p q by (simp_all add: Cl_def)
      have "\<forall>l\<in>snd a. p l = q l" using eq by (metis restrict_apply')
      then have ag: "\<forall>l\<in>free H k (r (fst a)) p. p l = q l" using Sp by simp
      have bp: "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and bq: "q \<in> {..<k} \<rightarrow>\<^sub>E {..b}" using pH qH box by blast+
      show "p = q" by (rule free_determined[OF rinj pH qH bp bq _ ag]) (simp add: Sp Sq)
    qed
  qed
  have "card H \<le> card I * (b + 1) ^ (k div 2)" by (rule classes(1)[OF box finI cover sub R inj])
  also have "\<dots> \<le> 2 ^ (k + 1) * (b + 1) ^ (k div 2)" using cardI by (rule mult_right_mono) simp
  finally show "card H \<le> 2 ^ (k + 1) * (b + 1) ^ (k div 2)" .
  have "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> card I * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
    by (rule classes(2)[OF box finI cover sub R inj])
  also have "\<dots> \<le> 2 ^ (k + 1) * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
    using cardI by (rule mult_right_mono) simp
  finally show "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> 2 ^ (k + 1) * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))" .
qed

subsection \<open>Three blocks: \<open>|H| \<le> 2(b+1)\<close>\<close>

lemma sum3: "(\<Sum>i<3. (p :: nat \<Rightarrow> nat) i) = p 0 + p 1 + p 2"
  by (simp add: numeral_3_eq_3 numeral_2_eq_2)

theorem three_blocks:
  assumes v: "valid 3 N H" and box: "H \<subseteq> {..<3} \<rightarrow>\<^sub>E {..b}"
  shows "card H \<le> 2 * (b + 1)"
proof -
  define Hi where "Hi i = {p \<in> H. \<forall>h\<in>H. h 2 < p 2 \<longrightarrow> p i < h i}" for i :: nat
  have finH: "finite H" using box by (rule finite_subset) (intro finite_PiE; simp)
  have cover: "H \<subseteq> Hi 0 \<union> Hi 1"
  proof
    fix p assume p: "p \<in> H"
    obtain i where "i < 3" "i \<noteq> 2" "\<forall>h\<in>H. h 2 < p 2 \<longrightarrow> p i < h i"
      using exchange[OF v _ p, of 2] by auto
    then have "i = 0 \<or> i = 1" by auto
    then show "p \<in> Hi 0 \<union> Hi 1" using p \<open>\<forall>h\<in>H. h 2 < p 2 \<longrightarrow> p i < h i\<close> by (auto simp: Hi_def)
  qed
  have each: "card (Hi i) \<le> b + 1" if i: "i = 0 \<or> i = 1" for i
  proof -
    have inj: "inj_on (\<lambda>p. p i) (Hi i)"
    proof (rule inj_onI)
      fix p q assume p: "p \<in> Hi i" and q: "q \<in> Hi i" and eq: "p i = q i"
      have pH: "p \<in> H" and qH: "q \<in> H" using p q by (auto simp: Hi_def)
      have "p 2 = mu H i 2 (p i)" using p by (intro determination) (auto simp: Hi_def)
      moreover have "q 2 = mu H i 2 (q i)" using q by (intro determination) (auto simp: Hi_def)
      ultimately have e2: "p 2 = q 2" using eq by simp
      have "p 0 + p 1 + p 2 = q 0 + q 1 + q 2"
        using v pH qH by (simp add: valid_def sum3)
      then have e01: "p 0 = q 0 \<and> p 1 = q 1" using i eq e2 by auto
      have "p \<in> {..<3} \<rightarrow>\<^sub>E {..b}" "q \<in> {..<3} \<rightarrow>\<^sub>E {..b}" using pH qH box by auto
      then show "p = q"
      proof (rule PiE_ext)
        fix j assume "j \<in> {..<3::nat}"
        then have "j = 0 \<or> j = 1 \<or> j = 2" by auto
        then show "p j = q j" using e01 e2 by auto
      qed
    qed
    have "(\<lambda>p. p i) ` Hi i \<subseteq> {..b}"
    proof
      fix x assume "x \<in> (\<lambda>p. p i) ` Hi i"
      then obtain p where p: "p \<in> H" "x = p i" by (auto simp: Hi_def)
      then have pb: "p \<in> {..<3} \<rightarrow>\<^sub>E {..b}" using box by blast
      have "i \<in> {..<3}" using i by auto
      then have "p i \<in> {..b}" by (rule PiE_mem[OF pb])
      then show "x \<in> {..b}" using p(2) by simp
    qed
    then have "card ((\<lambda>p. p i) ` Hi i) \<le> card {..b}" by (intro card_mono) simp_all
    then show ?thesis using inj by (simp add: card_image)
  qed
  have "card H \<le> card (Hi 0 \<union> Hi 1)"
    using cover finH by (intro card_mono) (auto simp: Hi_def intro: finite_subset)
  also have "\<dots> \<le> card (Hi 0) + card (Hi 1)" by (rule card_Un_le)
  also have "\<dots> \<le> 2 * (b + 1)" using each[of 0] each[of 1] by simp
  finally show ?thesis .
qed

subsection \<open>The matching test: \<open>|H| \<ge> (b+1)\<^sup>k\<^sup>/\<^sup>2\<close>\<close>

definition matchH :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "matchH h b = {p \<in> {..<2 * h} \<rightarrow>\<^sub>E {..b}. \<forall>q<h. p (2 * q) + p (Suc (2 * q)) = b}"

lemma sum_pairs: "(\<Sum>i<2 * h. z i) = (\<Sum>q<h. z (2 * q) + z (Suc (2 * q)))"
  by (induction h) (simp_all add: add.assoc)

theorem matching_valid: "valid (2 * h) (h * b) (matchH h b)"
  unfolding valid_def
proof (intro conjI allI impI ballI)
  fix p assume "p \<in> matchH h b"
  then have "\<forall>q<h. p (2 * q) + p (Suc (2 * q)) = b" by (simp add: matchH_def)
  then show "(\<Sum>i<2 * h. p i) = h * b" by (simp add: sum_pairs)
next
  fix z assume d: "dom2 (2 * h) (matchH h b) z"
  have pair: "b \<le> z (2 * q) + z (Suc (2 * q))" if q: "q < h" for q
  proof -
    have ij: "2 * q < 2 * h" "Suc (2 * q) < 2 * h" "2 * q \<noteq> Suc (2 * q)" using q by simp_all
    have "\<forall>i<2 * h. \<forall>j<2 * h. i \<noteq> j \<longrightarrow> (\<exists>p\<in>matchH h b. p i \<le> z i \<and> p j \<le> z j)"
      using d by (simp add: dom2_def)
    then obtain p where p: "p \<in> matchH h b" "p (2 * q) \<le> z (2 * q)" "p (Suc (2 * q)) \<le> z (Suc (2 * q))"
      using ij by blast
    have "p (2 * q) + p (Suc (2 * q)) = b" using p(1) q by (simp add: matchH_def)
    with p(2,3) show ?thesis by linarith
  qed
  have "h * b = (\<Sum>q<h. b)" by simp
  also have "\<dots> \<le> (\<Sum>q<h. z (2 * q) + z (Suc (2 * q)))" using pair by (intro sum_mono) simp
  also have "\<dots> = (\<Sum>i<2 * h. z i)" by (simp add: sum_pairs)
  finally show "h * b \<le> (\<Sum>i<2 * h. z i)" .
qed

definition mk :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "mk h b c i = (if i < 2 * h then (if even i then c (i div 2) else b - c (i div 2)) else undefined)"

theorem matching_card: "(b + 1) ^ h \<le> card (matchH h b)"
proof -
  let ?C = "{..<h} \<rightarrow>\<^sub>E {..b}"
  have mem: "mk h b c \<in> matchH h b" if c: "c \<in> ?C" for c
  proof -
    have cb: "c q \<le> b" if "q < h" for q using c that by (auto dest: PiE_mem)
    have "i div 2 < h" if "i < 2 * h" for i using that by simp
    then have "mk h b c \<in> {..<2 * h} \<rightarrow>\<^sub>E {..b}"
      using cb by (auto simp: mk_def PiE_def extensional_def)
    moreover have "mk h b c (2 * q) + mk h b c (Suc (2 * q)) = b" if "q < h" for q
      using cb[OF that] that by (simp add: mk_def)
    ultimately show ?thesis by (simp add: matchH_def)
  qed
  have inj: "inj_on (mk h b) ?C"
  proof (rule inj_onI)
    fix c c' assume c: "c \<in> ?C" and c': "c' \<in> ?C" and eq: "mk h b c = mk h b c'"
    show "c = c'"
    proof (rule PiE_ext[OF c c'])
      fix q assume "q \<in> {..<h}"
      then have "mk h b c (2 * q) = c q" "mk h b c' (2 * q) = c' q" by (simp_all add: mk_def)
      then show "c q = c' q" using eq by metis
    qed
  qed
  have fin: "finite (matchH h b)"
    by (rule finite_subset[of _ "{..<2 * h} \<rightarrow>\<^sub>E {..b}"]) (auto simp: matchH_def intro: finite_PiE)
  have "(b + 1) ^ h = card ?C" by (simp add: card_PiE)
  also have "\<dots> = card (mk h b ` ?C)" using inj by (simp add: card_image)
  also have "\<dots> \<le> card (matchH h b)" using mem fin by (intro card_mono) auto
  finally show ?thesis .
qed

text \<open>
  Weighted: the matching test covers \<open>C(2b,b)\<^sup>h\<close> inputs, against the weighted Theorem A bound
  \<open>(k-1)\<^sup>k (2\<^sup>b C(b,b/2))\<^sup>h\<close> for \<open>k = 2h\<close>; the ratio is at most \<open>(k-1)\<^sup>k\<close> times \<open>O(1)\<^sup>k\<close>.
\<close>

lemma prod_pairs: "(\<Prod>i<2 * h. z i) = (\<Prod>q<h. z (2 * q) * z (Suc (2 * q)))"
  for z :: "nat \<Rightarrow> nat"
  by (induction h) (simp_all add: mult.assoc)

theorem matching_weight:
  "((2 * b) choose b) ^ h \<le> (\<Sum>p\<in>matchH h b. \<Prod>i<2 * h. b choose p i)"
proof -
  let ?C = "{..<h} \<rightarrow>\<^sub>E {..b}"
  have cb: "c q \<le> b" if "c \<in> ?C" "q < h" for c q using that by (auto dest: PiE_mem)
  have mem: "mk h b c \<in> matchH h b" if c: "c \<in> ?C" for c
  proof -
    have "i div 2 < h" if "i < 2 * h" for i using that by simp
    then have "mk h b c \<in> {..<2 * h} \<rightarrow>\<^sub>E {..b}"
      using cb[OF c] by (auto simp: mk_def PiE_def extensional_def)
    moreover have "mk h b c (2 * q) + mk h b c (Suc (2 * q)) = b" if "q < h" for q
      using cb[OF c that] that by (simp add: mk_def)
    ultimately show ?thesis by (simp add: matchH_def)
  qed
  have inj: "inj_on (mk h b) ?C"
  proof (rule inj_onI)
    fix c c' assume c: "c \<in> ?C" and c': "c' \<in> ?C" and eq: "mk h b c = mk h b c'"
    show "c = c'"
    proof (rule PiE_ext[OF c c'])
      fix q assume "q \<in> {..<h}"
      then have "mk h b c (2 * q) = c q" "mk h b c' (2 * q) = c' q" by (simp_all add: mk_def)
      then show "c q = c' q" using eq by metis
    qed
  qed
  have fin: "finite (matchH h b)"
    by (rule finite_subset[of _ "{..<2 * h} \<rightarrow>\<^sub>E {..b}"]) (auto simp: matchH_def intro: finite_PiE)
  have wmk: "(\<Prod>i<2 * h. b choose mk h b c i) = (\<Prod>q<h. (b choose c q) ^ 2)" if c: "c \<in> ?C" for c
  proof -
    have "(\<Prod>i<2 * h. b choose mk h b c i)
            = (\<Prod>q<h. (b choose mk h b c (2 * q)) * (b choose mk h b c (Suc (2 * q))))"
      by (rule prod_pairs)
    also have "\<dots> = (\<Prod>q<h. (b choose c q) ^ 2)"
    proof (rule prod.cong[OF refl])
      fix q assume "q \<in> {..<h}"
      then have q: "q < h" by simp
      have "b choose (b - c q) = b choose c q" using binomial_symmetric[OF cb[OF c q]] by simp
      then show "(b choose mk h b c (2 * q)) * (b choose mk h b c (Suc (2 * q))) = (b choose c q) ^ 2"
        using q by (simp add: mk_def power2_eq_square)
    qed
    finally show ?thesis .
  qed
  have "((2 * b) choose b) ^ h = (\<Prod>q<h. \<Sum>x\<le>b. (b choose x) ^ 2)" by (simp add: choose_square_sum)
  also have "\<dots> = (\<Sum>c\<in>?C. \<Prod>q<h. (b choose c q) ^ 2)" by (subst prod_sum_PiE) simp_all
  also have "\<dots> = (\<Sum>c\<in>?C. \<Prod>i<2 * h. b choose mk h b c i)" using wmk by (intro sum.cong) simp_all
  also have "\<dots> = (\<Sum>p\<in>mk h b ` ?C. \<Prod>i<2 * h. b choose p i)" using inj by (simp add: sum.reindex)
  also have "\<dots> \<le> (\<Sum>p\<in>matchH h b. \<Prod>i<2 * h. b choose p i)"
    using mem fin by (intro sum_mono2) auto
  finally show ?thesis .
qed

end
