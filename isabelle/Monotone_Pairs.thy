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
  \<open>|H| \<le> (k-1)\<^sup>k (b+1)\<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2\<close> (\<open>pairwise_count\<close>), with \<open>|H| \<le> 2(b+1)\<close> for \<open>k = 3\<close>
  (\<open>three_blocks\<close>).  The matching test (pair up blocks, require complementary weights) is valid
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
  The counting only uses the witness maps: if every point has a witness map in a family \<open>F\<close>,
  then \<open>|H| \<le> |F| (b+1)\<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2\<close>.
\<close>

lemma count_via:
  assumes box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" and F: "F \<subseteq> fpf k" "finite F"
    and wit: "\<forall>p\<in>H. \<exists>f\<in>F. witf H k f p"
  shows "card H \<le> card F * (b + 1) ^ (k div 2)"
proof -
  define Hf where "Hf f = {p \<in> H. witf H k f p}" for f
  have finH: "finite H" using box by (rule finite_subset) (intro finite_PiE; simp)
  have cover: "H \<subseteq> (\<Union>f\<in>F. Hf f)" using wit by (auto simp: Hf_def)
  have each: "card (Hf f) \<le> (b + 1) ^ (k div 2)" if f: "f \<in> fpf k" for f
  proof -
    let ?r = "\<lambda>p. restrict p (Rs k f)"
    have inj: "inj_on ?r (Hf f)"
    proof (rule inj_onI)
      fix p q assume pq: "p \<in> Hf f" "q \<in> Hf f" and eq: "?r p = ?r q"
      have "\<forall>l\<in>Rs k f. p l = q l" using eq by (metis restrict_apply')
      then show "p = q" using pq box by (intro determined[OF f]) (auto simp: Hf_def)
    qed
    have finR: "finite (Rs k f)" using Rs_sub finite_subset by blast
    have img: "?r ` Hf f \<subseteq> Rs k f \<rightarrow>\<^sub>E {..b}"
    proof
      fix r assume "r \<in> ?r ` Hf f"
      then obtain p where p: "p \<in> H" "r = ?r p" by (auto simp: Hf_def)
      then have "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" using box by blast
      then show "r \<in> Rs k f \<rightarrow>\<^sub>E {..b}" using p(2) Rs_sub by (auto simp: restrict_PiE_iff)
    qed
    have "card (Hf f) = card (?r ` Hf f)" using inj by (simp add: card_image)
    also have "\<dots> \<le> card (Rs k f \<rightarrow>\<^sub>E {..b})" using img finR by (intro card_mono finite_PiE) auto
    also have "\<dots> = (b + 1) ^ card (Rs k f)" using finR by (simp add: card_PiE)
    also have "\<dots> \<le> (b + 1) ^ (k div 2)" using Rs_card[OF f] by (intro power_increasing) simp_all
    finally show ?thesis .
  qed
  have "card H \<le> card (\<Union>f\<in>F. Hf f)"
    using cover finH by (intro card_mono) (auto simp: Hf_def intro: finite_subset)
  also have "\<dots> \<le> (\<Sum>f\<in>F. card (Hf f))" by (rule card_UN_le[OF F(2)])
  also have "\<dots> \<le> (\<Sum>f\<in>F. (b + 1) ^ (k div 2))" using each F(1) by (intro sum_mono) blast
  also have "\<dots> = card F * (b + 1) ^ (k div 2)" by simp
  finally show ?thesis .
qed

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

lemma weight_via:
  assumes box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" and F: "F \<subseteq> fpf k" "finite F"
    and wit: "\<forall>p\<in>H. \<exists>f\<in>F. witf H k f p"
  shows "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> card F * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
proof -
  define M where "M = b choose (b div 2)"
  define wt where "wt p = (\<Prod>i<k. b choose p i)" for p :: "nat \<Rightarrow> nat"
  define Hf where "Hf f = {p \<in> H. witf H k f p}" for f
  have finH: "finite H" using box by (rule finite_subset) (intro finite_PiE; simp)
  have finF: "finite F" by (rule F(2))
  have cover: "H \<subseteq> (\<Union>f\<in>F. Hf f)" using wit by (auto simp: Hf_def)
  have sub: "Hf f \<subseteq> H" for f by (auto simp: Hf_def)
  have M2: "M \<le> 2 ^ b"
  proof -
    have "b choose (b div 2) \<le> (\<Sum>x\<le>b. b choose x)" by (rule member_le_sum) simp_all
    then show ?thesis by (simp add: M_def choose_row_sum)
  qed
  have each: "(\<Sum>p\<in>Hf f. wt p) \<le> (2 ^ b) ^ (k div 2) * M ^ (k - k div 2)" if f: "f \<in> fpf k" for f
  proof -
    let ?R = "Rs k f"
    let ?r = "\<lambda>p. restrict p ?R"
    have finR: "finite ?R" using Rs_sub finite_subset by blast
    have split: "wt p \<le> (\<Prod>i\<in>?R. b choose p i) * M ^ (k - card ?R)" for p
    proof -
      have eq: "wt p = (\<Prod>i\<in>?R. b choose p i) * (\<Prod>i\<in>{..<k} - ?R. b choose p i)"
        unfolding wt_def using Rs_sub prod.subset_diff[of ?R "{..<k}" "\<lambda>i. b choose p i"]
        by (simp add: mult.commute)
      have "(\<Prod>i\<in>{..<k} - ?R. b choose p i) \<le> (\<Prod>i\<in>{..<k} - ?R. M)"
        by (rule prod_mono) (simp add: M_def binomial_maximum)
      also have "\<dots> = M ^ (k - card ?R)"
        using Rs_sub finR by (simp add: card_Diff_subset)
      finally show ?thesis using eq by (simp add: mult_left_mono)
    qed
    have inj: "inj_on ?r (Hf f)"
    proof (rule inj_onI)
      fix p q assume pq: "p \<in> Hf f" "q \<in> Hf f" and eq: "?r p = ?r q"
      have "\<forall>l\<in>?R. p l = q l" using eq by (metis restrict_apply')
      then show "p = q" using pq box by (intro determined[OF f]) (auto simp: Hf_def)
    qed
    have img: "?r ` Hf f \<subseteq> ?R \<rightarrow>\<^sub>E {..b}"
    proof
      fix r assume "r \<in> ?r ` Hf f"
      then obtain p where p: "p \<in> H" "r = ?r p" by (auto simp: Hf_def)
      then have "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" using box by blast
      then show "r \<in> ?R \<rightarrow>\<^sub>E {..b}" using p(2) Rs_sub by (auto simp: restrict_PiE_iff)
    qed
    have rr: "(\<Prod>i\<in>?R. b choose ?r p i) = (\<Prod>i\<in>?R. b choose p i)" for p
      by (rule prod.cong) simp_all
    have S: "(\<Sum>p\<in>Hf f. \<Prod>i\<in>?R. b choose p i) \<le> (2 ^ b) ^ card ?R"
    proof -
      have "(\<Sum>p\<in>Hf f. \<Prod>i\<in>?R. b choose p i) = (\<Sum>r\<in>?r ` Hf f. \<Prod>i\<in>?R. b choose r i)"
        using inj by (simp add: sum.reindex rr)
      also have "\<dots> \<le> (\<Sum>r\<in>?R \<rightarrow>\<^sub>E {..b}. \<Prod>i\<in>?R. b choose r i)"
        using img finR by (intro sum_mono2 finite_PiE) auto
      also have "\<dots> = (\<Prod>i\<in>?R. \<Sum>x\<le>b. b choose x)"
        using finR by (subst prod_sum_PiE) simp_all
      also have "\<dots> = (2 ^ b) ^ card ?R" by (simp add: choose_row_sum)
      finally show ?thesis .
    qed
    have "(\<Sum>p\<in>Hf f. wt p) \<le> (\<Sum>p\<in>Hf f. (\<Prod>i\<in>?R. b choose p i) * M ^ (k - card ?R))"
      by (rule sum_mono) (rule split)
    also have "\<dots> = M ^ (k - card ?R) * (\<Sum>p\<in>Hf f. \<Prod>i\<in>?R. b choose p i)"
      by (simp add: sum_distrib_left mult.commute)
    also have "\<dots> \<le> M ^ (k - card ?R) * (2 ^ b) ^ card ?R" using S by (rule mult_left_mono) simp
    also have "\<dots> \<le> (2 ^ b) ^ (k div 2) * M ^ (k - k div 2)"
      using M2 Rs_card[OF f] by (intro trade) simp_all
    finally show ?thesis .
  qed
  have "(\<Sum>p\<in>H. wt p) \<le> (\<Sum>p\<in>H. \<Sum>f\<in>F. if p \<in> Hf f then wt p else 0)"
  proof (rule sum_mono)
    fix p assume "p \<in> H"
    then obtain f where f: "f \<in> F" "p \<in> Hf f" using cover by blast
    have "wt p = (if p \<in> Hf f then wt p else 0)" using f by simp
    also have "\<dots> \<le> (\<Sum>f\<in>F. if p \<in> Hf f then wt p else 0)"
      by (rule member_le_sum) (use f finF in auto)
    finally show "wt p \<le> (\<Sum>f\<in>F. if p \<in> Hf f then wt p else 0)" .
  qed
  also have "\<dots> = (\<Sum>f\<in>F. \<Sum>p\<in>H. if p \<in> Hf f then wt p else 0)" by (rule sum.swap)
  also have "\<dots> = (\<Sum>f\<in>F. \<Sum>p\<in>Hf f. wt p)"
  proof (rule sum.cong[OF refl])
    fix f
    have "(\<Sum>p\<in>H. if p \<in> Hf f then wt p else 0) = sum wt (H \<inter> Hf f)"
      by (rule sum.inter_restrict[OF finH, symmetric])
    also have "H \<inter> Hf f = Hf f" using sub by blast
    finally show "(\<Sum>p\<in>H. if p \<in> Hf f then wt p else 0) = (\<Sum>p\<in>Hf f. wt p)" .
  qed
  also have "\<dots> \<le> (\<Sum>f\<in>F. (2 ^ b) ^ (k div 2) * M ^ (k - k div 2))"
    using each F(1) by (intro sum_mono) blast
  also have "\<dots> = card F * ((2 ^ b) ^ (k div 2) * M ^ (k - k div 2))" by simp
  finally show ?thesis by (simp add: wt_def M_def)
qed

theorem pairwise_weight:
  assumes v: "valid k N H" and k: "2 \<le> k" and box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}"
  shows "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> (k - 1) ^ k * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
proof -
  have wit: "\<forall>p\<in>H. \<exists>f\<in>fpf k. witf H k f p" using witf_exists[OF v k] by blast
  have fin: "finite (fpf k)" by (simp add: fpf_def finite_PiE)
  show ?thesis using weight_via[OF box subset_refl fin wit] by (simp add: card_fpf)
qed

subsection \<open>Witness graphs of bounded degree\<close>

text \<open>
  If the witnesses can always be chosen along the edges of a fixed digraph \<open>G\<close> with out-degree
  at most \<open>D\<close>, the factor \<open>(k-1)\<^sup>k\<close> drops to \<open>D\<^sup>k\<close>.  This is where Conjecture Q would need a
  structural argument: the remaining loss is only the choice of witnesses.
\<close>

lemma card_PiE_le:
  assumes "\<forall>l<k. card (G l) \<le> D"
  shows "card (\<Pi>\<^sub>E l\<in>{..<k}. G l) \<le> D ^ k"
proof -
  have "card (\<Pi>\<^sub>E l\<in>{..<k}. G l) = (\<Prod>l<k. card (G l))" by (simp add: card_PiE)
  also have "\<dots> \<le> (\<Prod>l<k. D)" using assms by (intro prod_mono) simp
  also have "\<dots> = D ^ k" by simp
  finally show ?thesis .
qed

theorem graph_weight:
  assumes box: "H \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}"
    and G: "\<forall>l<k. G l \<subseteq> {..<k} - {l} \<and> card (G l) \<le> D"
    and wit: "\<forall>p\<in>H. \<exists>f\<in>(\<Pi>\<^sub>E l\<in>{..<k}. G l). witf H k f p"
  shows "card H \<le> D ^ k * (b + 1) ^ (k div 2)"
    and "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> D ^ k * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
proof -
  let ?F = "\<Pi>\<^sub>E l\<in>{..<k}. G l"
  have F: "?F \<subseteq> fpf k" using G unfolding fpf_def by (intro PiE_mono) auto
  have finG: "finite (G l)" if "l < k" for l using G that finite_subset by blast
  have finF: "finite ?F" using finG by (intro finite_PiE) auto
  have cF: "card ?F \<le> D ^ k" using G by (intro card_PiE_le) simp
  have "card H \<le> card ?F * (b + 1) ^ (k div 2)" by (rule count_via[OF box F finF wit])
  also have "\<dots> \<le> D ^ k * (b + 1) ^ (k div 2)" using cF by (rule mult_right_mono) simp
  finally show "card H \<le> D ^ k * (b + 1) ^ (k div 2)" .
  have "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> card ?F * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
    by (rule weight_via[OF box F finF wit])
  also have "\<dots> \<le> D ^ k * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
    using cF by (rule mult_right_mono) simp
  finally show "(\<Sum>p\<in>H. \<Prod>i<k. b choose p i)
           \<le> D ^ k * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))" .
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
