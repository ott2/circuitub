theory Monotone_Kraft
  imports Complex_Main Monotone_Wide
begin

section \<open>Averaging the order instead of choosing it\<close>

text \<open>
  \<open>wide_compress\<close> chooses, for each accepted vector, a colouring with few free coordinates and
  records it, which costs a factor \<open>(2w)\<^sup>k\<close>.  Here no choice is recorded.  For a fixed
  colouring \<open>c\<close>, the encoding \<open>u \<mapsto> (decoded or u i)\<^sub>i\<close> is injective (\<open>wfree_determined\<close>),
  so a Kraft inequality (\<open>kraft_partial\<close>) holds with weight \<open>\<delta>\<close> for a decoded coordinate
  and \<open>(1 - \<delta>) C(b, x) / 2\<^sup>b\<close> for a free coordinate of value \<open>x\<close>.  Summing over all colourings
  and applying Jensen's inequality to \<open>\<lambda>\<^sup>D\<close> (\<open>power_average\<close>, proved from \<open>exp x \<ge> 1 + x\<close>)
  turns the average number \<open>D\<close> of decoded coordinates into an exponent.

  The result (\<open>wide_kraft\<close>): the inputs covered with \<open>t\<close> tight coordinates satisfy
  \<open>#S \<cdot> \<lambda>\<^sup>y \<le> (2\<^sup>b / (1 - \<delta>))\<^sup>k\<close> with \<open>\<lambda> = \<delta> 2\<^sup>b / ((1 - \<delta>) C(b, b/2)) \<approx> \<delta> \<surd>(\<pi>b/2) / (1 - \<delta>)\<close>
  and \<open>y = t (w-1)\<^sup>w\<^sup>-\<^sup>1 / w\<^sup>w \<approx> t / (e w)\<close>.  With \<open>\<delta> = 1/(w+1)\<close> the overhead is \<open>e\<^sup>k\<^sup>/\<^sup>w\<close> instead
  of \<open>(2w)\<^sup>k\<close>, and a decoded coordinate gains \<open>log(\<surd>b / w)\<close> instead of needing
  \<open>log \<surd>b > log(2w) \<cdot> e w\<close>.
\<close>

subsection \<open>A Kraft inequality for partial encodings\<close>

lemma kraft_partial:
  fixes enc :: "'p \<Rightarrow> nat \<Rightarrow> 'v" and wo :: "'v \<Rightarrow> real"
  assumes P: "finite P" and inj: "inj_on enc P"
    and enc: "\<forall>p\<in>P. enc p \<in> {..<k} \<rightarrow>\<^sub>E Opt" and Opt: "finite Opt"
    and wo: "\<forall>z\<in>Opt. 0 \<le> wo z" and tot: "(\<Sum>z\<in>Opt. wo z) \<le> 1"
  shows "(\<Sum>p\<in>P. \<Prod>i<k. wo (enc p i)) \<le> 1"
proof -
  have "(\<Sum>p\<in>P. \<Prod>i<k. wo (enc p i)) = (\<Sum>h\<in>enc ` P. \<Prod>i<k. wo (h i))"
    using inj by (simp add: sum.reindex)
  also have "\<dots> \<le> (\<Sum>h\<in>{..<k} \<rightarrow>\<^sub>E Opt. \<Prod>i<k. wo (h i))"
  proof (rule sum_mono2)
    show "finite ({..<k} \<rightarrow>\<^sub>E Opt)" using Opt by (simp add: finite_PiE)
    show "enc ` P \<subseteq> {..<k} \<rightarrow>\<^sub>E Opt" using enc by blast
  next
    fix h assume h: "h \<in> ({..<k} \<rightarrow>\<^sub>E Opt) - enc ` P"
    have "\<forall>i\<in>{..<k}. 0 \<le> wo (h i)" using h wo by (auto simp: PiE_iff)
    then show "0 \<le> (\<Prod>i<k. wo (h i))" by (intro prod_nonneg) blast
  qed
  also have "\<dots> = (\<Prod>i<k. \<Sum>z\<in>Opt. wo z)"
    using prod_sum_PiE[of "{..<k}" "\<lambda>_. Opt" "\<lambda>_ z. wo z"] Opt by simp
  also have "\<dots> \<le> 1"
  proof (rule prod_le_1)
    fix i assume "i \<in> {..<k}"
    show "0 \<le> (\<Sum>z\<in>Opt. wo z) \<and> (\<Sum>z\<in>Opt. wo z) \<le> 1" using wo tot by (simp add: sum_nonneg)
  qed
  finally show ?thesis .
qed

subsection \<open>Jensen's inequality for powers\<close>

lemma exp_average:
  fixes x :: "'c \<Rightarrow> real"
  assumes C: "finite C" "C \<noteq> {}"
  shows "real (card C) * exp ((\<Sum>c\<in>C. x c) / card C) \<le> (\<Sum>c\<in>C. exp (x c))"
proof -
  define m where "m = (\<Sum>c\<in>C. x c) / card C"
  have R: "0 < real (card C)" using C by (simp add: card_gt_0_iff)
  have Rm: "real (card C) * m = (\<Sum>c\<in>C. x c)" using R by (simp add: m_def)
  have each: "exp m * (1 + (x c - m)) \<le> exp (x c)" for c
  proof -
    have "1 + (x c - m) \<le> exp (x c - m)" by (rule exp_ge_add_one_self)
    then have "exp m * (1 + (x c - m)) \<le> exp m * exp (x c - m)" by (rule mult_left_mono) simp
    also have "\<dots> = exp (x c)" by (simp add: exp_add[symmetric])
    finally show ?thesis .
  qed
  have "(\<Sum>c\<in>C. 1 + (x c - m)) = real (card C) + (\<Sum>c\<in>C. x c) - real (card C) * m"
    by (simp add: sum.distrib sum_subtractf)
  also have "\<dots> = real (card C)" using Rm by simp
  finally have s: "(\<Sum>c\<in>C. 1 + (x c - m)) = real (card C)" .
  have "real (card C) * exp m = exp m * (\<Sum>c\<in>C. 1 + (x c - m))" using s by simp
  also have "\<dots> = (\<Sum>c\<in>C. exp m * (1 + (x c - m)))" by (rule sum_distrib_left)
  also have "\<dots> \<le> (\<Sum>c\<in>C. exp (x c))" using each by (rule sum_mono)
  finally show ?thesis by (simp add: m_def)
qed

lemma power_average:
  fixes D :: "'c \<Rightarrow> nat" and lam y :: real
  assumes C: "finite C" "C \<noteq> {}" and lam: "1 \<le> lam"
    and avg: "real (card C) * y \<le> (\<Sum>c\<in>C. real (D c))"
  shows "real (card C) * lam powr y \<le> (\<Sum>c\<in>C. lam ^ D c)"
proof -
  have R: "0 < real (card C)" using C by (simp add: card_gt_0_iff)
  have l0: "0 < lam" using lam by simp
  have ln0: "0 \<le> ln lam" using lam by simp
  have yle: "y \<le> (\<Sum>c\<in>C. real (D c)) / card C" using avg R by (simp add: le_divide_eq mult.commute)
  have "y * ln lam \<le> (\<Sum>c\<in>C. real (D c)) / card C * ln lam" using yle ln0 by (rule mult_right_mono)
  also have "\<dots> = (\<Sum>c\<in>C. real (D c) * ln lam) / card C" by (simp add: sum_distrib_right)
  finally have e: "y * ln lam \<le> (\<Sum>c\<in>C. real (D c) * ln lam) / card C" .
  have "real (card C) * lam powr y = real (card C) * exp (y * ln lam)" using l0 by (simp add: powr_def)
  also have "\<dots> \<le> real (card C) * exp ((\<Sum>c\<in>C. real (D c) * ln lam) / card C)"
    using e R by simp
  also have "\<dots> \<le> (\<Sum>c\<in>C. exp (real (D c) * ln lam))" by (rule exp_average[OF C])
  also have "\<dots> = (\<Sum>c\<in>C. lam ^ D c)"
  proof (rule sum.cong[OF refl])
    fix c
    have "exp (real (D c) * ln lam) = lam powr real (D c)" using l0 by (simp add: powr_def mult.commute)
    also have "\<dots> = lam ^ D c" using l0 by (rule powr_realpow)
    finally show "exp (real (D c) * ln lam) = lam ^ D c" .
  qed
  finally show ?thesis .
qed

subsection \<open>The weighted count\<close>

theorem wide_kraft:
  fixes k :: nat and blk :: "nat \<Rightarrow> 'a set" and G :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" and \<delta> :: real
  assumes mono: "wmono k G" and w: "1 \<le> w" and beta: "1 < \<beta>"
    and range: "\<forall>x. lo - 1 \<le> x \<longrightarrow> x < hi \<longrightarrow> \<beta> \<le> b choose x"
    and cost: "\<forall>v\<in>{..<k} \<rightarrow>\<^sub>E {..b}. \<not> G v \<longrightarrow> (\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i))))
                 \<longrightarrow> (\<Prod>i<k. b choose v i) < \<beta> ^ (w + 1)"
    and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b" and V: "V = (\<Union>i<k. blk i)"
    and \<delta>: "0 < \<delta>" "\<delta> < 1" and lam: "(1 - \<delta>) * (b choose (b div 2)) \<le> \<delta> * 2 ^ b"
  shows "real (card {X. X \<subseteq> V \<and> G (bw blk k X) \<and> t \<le> card (wtight k G lo hi (bw blk k X))})
           * (\<delta> * 2 ^ b / ((1 - \<delta>) * (b choose (b div 2))))
               powr (real t * (w - 1) ^ (w - 1) / w ^ w)
         \<le> (2 ^ b / (1 - \<delta>)) ^ k"
proof -
  define M :: real where "M = real (b choose (b div 2))"
  define lam :: real where "lam = \<delta> * 2 ^ b / ((1 - \<delta>) * M)"
  define K :: real where "K = 2 ^ b / (1 - \<delta>)"
  define q :: nat where "q = (w - 1) ^ (w - 1)"
  define P :: nat where "P = w ^ w"
  define y :: real where "y = real t * q / P"
  define C where "C = {..<k} \<rightarrow>\<^sub>E {..<w}"
  define U where "U = {u \<in> {..<k} \<rightarrow>\<^sub>E {..b}. G u \<and> t \<le> card (wtight k G lo hi u)}"
  define F where "F c u = wfree k G lo hi (cord k c) u" for c u
  define D where "D c u = k - card (F c u)" for c u
  define wo :: "nat option \<Rightarrow> real"
    where "wo z = (case z of None \<Rightarrow> \<delta> | Some x \<Rightarrow> (1 - \<delta>) * (b choose x) / 2 ^ b)" for z
  define enc where "enc c u = restrict (\<lambda>i. if i \<in> F c u then Some (u i) else None) {..<k}" for c u
  define Opt where "Opt = insert None (Some ` {..b})"
  define cw :: "(nat \<Rightarrow> nat) \<Rightarrow> real" where "cw u = (\<Prod>i<k. real (b choose u i))" for u
  have Mpos: "0 < M" by (simp add: M_def)
  have d1: "0 < 1 - \<delta>" using \<delta> by simp
  have lam1: "1 \<le> lam"
  proof -
    have "(1 - \<delta>) * M \<le> \<delta> * 2 ^ b" using lam by (simp add: M_def)
    moreover have "0 < (1 - \<delta>) * M" using d1 Mpos by simp
    ultimately show ?thesis by (simp add: lam_def le_divide_eq)
  qed
  have Ppos: "0 < P" using w by (simp add: P_def)
  have finC: "finite C" by (simp add: C_def finite_PiE)
  have Cne: "C \<noteq> {}"
  proof -
    have "(\<lambda>i\<in>{..<k}. 0) \<in> C" using w by (auto simp: C_def)
    then show ?thesis by blast
  qed
  have box: "U \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" by (auto simp: U_def)
  have finU: "finite U" using box by (rule finite_subset) (intro finite_PiE; simp)
  have Fsub: "F c u \<subseteq> {..<k}" for c u by (auto simp: F_def wfree_def)
  have finF: "finite (F c u)" for c u using Fsub by (rule finite_subset) simp
  text \<open>Kraft, for each colouring.\<close>
  have kraft: "(\<Sum>u\<in>U. \<Prod>i<k. wo (enc c u i)) \<le> 1" for c
  proof (rule kraft_partial[where enc = "enc c" and Opt = Opt and wo = wo, OF finU])
    show "inj_on (enc c) U"
    proof (rule inj_onI)
      fix u v assume u: "u \<in> U" and v: "v \<in> U" and eq: "enc c u = enc c v"
      have e: "(if i \<in> F c u then Some (u i) else None) = (if i \<in> F c v then Some (v i) else None)"
        if "i < k" for i using fun_cong[OF eq, of i] that by (simp add: enc_def)
      have FF: "F c u = F c v"
      proof
        show "F c u \<subseteq> F c v"
        proof
          fix i assume i: "i \<in> F c u"
          then have "i < k" using Fsub by blast
          then show "i \<in> F c v" using e[of i] i by (cases "i \<in> F c v") auto
        qed
        show "F c v \<subseteq> F c u"
        proof
          fix i assume i: "i \<in> F c v"
          then have "i < k" using Fsub by blast
          then show "i \<in> F c u" using e[of i] i by (cases "i \<in> F c u") auto
        qed
      qed
      have ag: "\<forall>l\<in>wfree k G lo hi (cord k c) u. u l = v l"
      proof
        fix l assume l: "l \<in> wfree k G lo hi (cord k c) u"
        then have l': "l \<in> F c u" "l \<in> F c v" using FF by (simp_all add: F_def)
        then have "l < k" using Fsub by blast
        then show "u l = v l" using e[of l] l' by simp
      qed
      have bu: "u \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and gu: "G u" using u by (simp_all add: U_def)
      have bv: "v \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and gv: "G v" using v by (simp_all add: U_def)
      show "u = v" by (rule wfree_determined[OF mono gu gv bu bv _ ag]) (use FF in \<open>simp add: F_def\<close>)
    qed
    show "\<forall>u\<in>U. enc c u \<in> {..<k} \<rightarrow>\<^sub>E Opt"
    proof
      fix u assume u: "u \<in> U"
      have "u i \<le> b" if "i < k" for i using PiE_mem[OF subsetD[OF box u], of i] that by simp
      then show "enc c u \<in> {..<k} \<rightarrow>\<^sub>E Opt" by (auto simp: enc_def Opt_def)
    qed
    show "finite Opt" by (simp add: Opt_def)
    show "\<forall>z\<in>Opt. 0 \<le> wo z" using \<delta> d1 by (auto simp: Opt_def wo_def)
    have row: "(\<Sum>x\<le>b. real (b choose x)) = 2 ^ b"
    proof -
      have "(\<Sum>x\<le>b. real (b choose x)) = real (\<Sum>x\<le>b. b choose x)" by (rule of_nat_sum[symmetric])
      also have "\<dots> = 2 ^ b" by (simp only: choose_row_sum) simp
      finally show ?thesis .
    qed
    have "(\<Sum>z\<in>Opt. wo z) = \<delta> + (\<Sum>z\<in>Some ` {..b}. wo z)" by (simp add: Opt_def wo_def)
    also have "\<dots> = \<delta> + (\<Sum>x\<le>b. (1 - \<delta>) * (b choose x) / 2 ^ b)"
      by (simp add: sum.reindex wo_def)
    also have "\<dots> = \<delta> + (1 - \<delta>) * (\<Sum>x\<le>b. real (b choose x)) / 2 ^ b"
      by (simp add: sum_distrib_left sum_divide_distrib)
    also have "\<dots> = 1" using row by simp
    finally show "(\<Sum>z\<in>Opt. wo z) \<le> 1" by simp
  qed
  text \<open>Each coordinate: a decoded one gains \<open>lam\<close>.\<close>
  have point: "cw u * lam ^ D c u \<le> (\<Prod>i<k. wo (enc c u i)) * K ^ k" if u: "u \<in> U" for c u
  proof -
    define g where "g i = (if i \<in> F c u then 1 else lam)" for i
    have ub: "u i \<le> b" if "i < k" for i using PiE_mem[OF subsetD[OF box u], of i] that by simp
    have each: "real (b choose u i) * g i \<le> wo (enc c u i) * K" if i: "i \<in> {..<k}" for i
    proof (cases "i \<in> F c u")
      case True
      then show ?thesis using i d1 by (simp add: g_def enc_def wo_def K_def)
    next
      case False
      have cm: "real (b choose u i) \<le> M" by (simp add: M_def binomial_maximum)
      have "real (b choose u i) * lam \<le> M * lam" using cm lam1 by (simp add: mult_right_mono)
      also have "\<dots> = \<delta> * K" using Mpos d1 by (simp add: lam_def K_def)
      finally show ?thesis using False i by (simp add: g_def enc_def wo_def)
    qed
    have "cw u * (\<Prod>i<k. g i) = (\<Prod>i<k. real (b choose u i) * g i)"
      by (simp add: cw_def prod.distrib)
    also have "\<dots> \<le> (\<Prod>i<k. wo (enc c u i) * K)"
    proof (rule prod_mono)
      fix i assume i: "i \<in> {..<k}"
      have "0 \<le> g i" using lam1 by (simp add: g_def)
      then show "0 \<le> real (b choose u i) * g i \<and> real (b choose u i) * g i \<le> wo (enc c u i) * K"
        using each[OF i] by simp
    qed
    also have "\<dots> = (\<Prod>i<k. wo (enc c u i)) * K ^ k" by (simp add: prod.distrib)
    finally have le: "cw u * (\<Prod>i<k. g i) \<le> (\<Prod>i<k. wo (enc c u i)) * K ^ k" .
    have "(\<Prod>i<k. g i) = (\<Prod>i\<in>{..<k} \<inter> {i. i \<in> F c u}. 1) * (\<Prod>i\<in>{..<k} \<inter> - {i. i \<in> F c u}. lam)"
      unfolding g_def by (rule prod.If_cases) simp
    also have "\<dots> = lam ^ card ({..<k} - F c u)" by (simp add: Diff_eq)
    also have "card ({..<k} - F c u) = D c u" using Fsub finF by (simp add: D_def card_Diff_subset)
    finally show ?thesis using le by simp
  qed
  text \<open>Averaging: decoded coordinates are frequent.\<close>
  have avg: "real (card C) * lam powr y \<le> (\<Sum>c\<in>C. lam ^ D c u)" if u: "u \<in> U" for u
  proof (rule power_average[OF finC Cne lam1])
    have tu: "t \<le> card (wtight k G lo hi u)" using u by (simp add: U_def)
    have ub: "u \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and Gu: "G u" using u by (simp_all add: U_def)
    have goodl: "\<forall>l\<in>wtight k G lo hi u. w ^ k * (w - 1) ^ (w - 1) \<le> w ^ w * card {c \<in> C. l \<notin> F c u}"
      using wide_good[OF mono w beta range cost ub Gu _ C_def] by (simp add: F_def)
    have Fs: "\<forall>c\<in>C. F c u \<subseteq> {..<k}" using Fsub by blast
    have ns: "(\<Sum>c\<in>C. card (F c u)) * P + t * (card C * q) \<le> k * (card C * P)"
      using free_sum[OF C_def w Fs wtight_sub tu goodl] by (simp add: P_def q_def)
    have r: "real (\<Sum>c\<in>C. card (F c u)) * P + real t * (real (card C) * q) \<le> real k * (real (card C) * P)"
      using of_nat_mono[OF ns] by simp
    have sD: "(\<Sum>c\<in>C. real (D c u)) = real k * card C - real (\<Sum>c\<in>C. card (F c u))"
    proof -
      have "card (F c u) \<le> k" for c using card_mono[OF _ Fsub[of c u]] by simp
      then have "(\<Sum>c\<in>C. real (D c u)) = (\<Sum>c\<in>C. real k - real (card (F c u)))"
        by (simp add: D_def of_nat_diff)
      also have "\<dots> = real k * card C - real (\<Sum>c\<in>C. card (F c u))"
        by (simp add: sum_subtractf of_nat_sum)
      finally show ?thesis .
    qed
    have "real (card C) * real t * real q \<le> (real k * card C - real (\<Sum>c\<in>C. card (F c u))) * P"
      using r by (simp add: algebra_simps)
    then show "real (card C) * y \<le> (\<Sum>c\<in>C. real (D c u))"
      using Ppos by (simp add: sD y_def pos_divide_le_eq mult.assoc)
  qed
  text \<open>Summing.\<close>
  have Rpos: "0 < real (card C)" using finC Cne by (simp add: card_gt_0_iff)
  have cw0: "0 \<le> cw u" for u by (simp add: cw_def prod_nonneg)
  have "(\<Sum>u\<in>U. cw u) * (real (card C) * lam powr y) = (\<Sum>u\<in>U. cw u * (real (card C) * lam powr y))"
    by (simp add: sum_distrib_right)
  also have "\<dots> \<le> (\<Sum>u\<in>U. cw u * (\<Sum>c\<in>C. lam ^ D c u))"
    using avg cw0 by (intro sum_mono mult_left_mono) simp_all
  also have "\<dots> = (\<Sum>c\<in>C. \<Sum>u\<in>U. cw u * lam ^ D c u)"
    by (simp add: sum_distrib_left sum.swap[of _ C U])
  also have "\<dots> \<le> (\<Sum>c\<in>C. \<Sum>u\<in>U. (\<Prod>i<k. wo (enc c u i)) * K ^ k)"
    using point by (intro sum_mono) simp
  also have "\<dots> = (\<Sum>c\<in>C. K ^ k * (\<Sum>u\<in>U. \<Prod>i<k. wo (enc c u i)))"
    by (simp add: sum_distrib_left mult.commute)
  also have "\<dots> \<le> (\<Sum>c\<in>C. K ^ k)"
  proof (rule sum_mono)
    fix c
    have "0 \<le> K" using d1 by (simp add: K_def)
    then show "K ^ k * (\<Sum>u\<in>U. \<Prod>i<k. wo (enc c u i)) \<le> K ^ k"
      using kraft[of c] by (simp add: mult_left_le)
  qed
  also have "\<dots> = real (card C) * K ^ k" by simp
  finally have "(\<Sum>u\<in>U. cw u) * (real (card C) * lam powr y) \<le> real (card C) * K ^ k" .
  then have main: "(\<Sum>u\<in>U. cw u) * lam powr y \<le> K ^ k" using Rpos by (simp add: mult.left_commute)
  let ?S = "{X. X \<subseteq> V \<and> G (bw blk k X) \<and> t \<le> card (wtight k G lo hi (bw blk k X))}"
  have sub2: "?S \<subseteq> {X. X \<subseteq> V \<and> bw blk k X \<in> U}"
  proof
    fix X assume X: "X \<in> ?S"
    have "card (X \<inter> blk i) \<le> b" if "i < k" for i
      using blk that card_mono[of "blk i" "X \<inter> blk i"] by auto
    then have "bw blk k X \<in> {..<k} \<rightarrow>\<^sub>E {..b}" by (auto simp: bw_def)
    then show "X \<in> {X. X \<subseteq> V \<and> bw blk k X \<in> U}" using X by (simp add: U_def)
  qed
  have finV: "finite V" using blk by (simp add: V)
  have fin2: "finite {X. X \<subseteq> V \<and> bw blk k X \<in> U}"
    using finV by (auto intro: finite_subset[of _ "Pow V"])
  have "card ?S \<le> card {X. X \<subseteq> V \<and> bw blk k X \<in> U}" using sub2 fin2 by (rule card_mono[rotated])
  also have "\<dots> \<le> (\<Sum>u\<in>U. \<Prod>i<k. b choose u i)" by (rule inputs_count[OF blk V finU])
  finally have cS: "card ?S \<le> (\<Sum>u\<in>U. \<Prod>i<k. b choose u i)" .
  have "real (card ?S) \<le> (\<Sum>u\<in>U. cw u)" using of_nat_mono[OF cS] by (simp add: cw_def)
  then have "real (card ?S) * lam powr y \<le> (\<Sum>u\<in>U. cw u) * lam powr y" by (rule mult_right_mono) simp
  also have "\<dots> \<le> K ^ k" by (rule main)
  finally show ?thesis by (simp add: lam_def M_def K_def y_def q_def P_def)
qed

text \<open>For a sound test given by a CNF with fewer than \<open>\<beta>\<^sup>w\<^sup>+\<^sup>1\<close> clauses, as in \<open>wide_cover\<close>.\<close>

theorem wide_cover_kraft:
  fixes k :: nat and blk :: "nat \<Rightarrow> 'a set" and G :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" and \<delta> :: real
  assumes mono: "wmono k G" and sound: "\<forall>u. G u \<longrightarrow> N \<le> (\<Sum>i<k. u i)"
    and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and cs: "finite cs" "\<forall>X\<subseteq>V. G (bw blk k X) = cnf_val cs X"
    and size: "card cs < \<beta> ^ (w + 1)" and w: "1 \<le> w" and beta: "1 < \<beta>"
    and lo: "1 \<le> lo" and range: "\<forall>x. lo - 1 \<le> x \<longrightarrow> x < hi \<longrightarrow> \<beta> \<le> b choose x"
    and \<delta>: "0 < \<delta>" "\<delta> < 1" and lam: "(1 - \<delta>) * (b choose (b div 2)) \<le> \<delta> * 2 ^ b"
  shows "real (card {X. X \<subseteq> V \<and> G (bw blk k X) \<and> (\<Sum>i<k. bw blk k X i) = N
                        \<and> card (atyp k lo hi (bw blk k X)) \<le> a})
           * (\<delta> * 2 ^ b / ((1 - \<delta>) * (b choose (b div 2))))
               powr (real (k - a) * (w - 1) ^ (w - 1) / w ^ w)
         \<le> (2 ^ b / (1 - \<delta>)) ^ k"
proof -
  note cost = wide_cnf_cost[OF mono blk disj V cs size]
  let ?S = "{X. X \<subseteq> V \<and> G (bw blk k X) \<and> (\<Sum>i<k. bw blk k X i) = N
                 \<and> card (atyp k lo hi (bw blk k X)) \<le> a}"
  let ?T = "{X. X \<subseteq> V \<and> G (bw blk k X) \<and> k - a \<le> card (wtight k G lo hi (bw blk k X))}"
  let ?p = "(\<delta> * 2 ^ b / ((1 - \<delta>) * (b choose (b div 2)))) powr (real (k - a) * (w - 1) ^ (w - 1) / w ^ w)"
  have sub: "?S \<subseteq> ?T"
  proof
    fix X assume X: "X \<in> ?S"
    have su: "(\<Sum>i<k. bw blk k X i) = N" and ca: "card (atyp k lo hi (bw blk k X)) \<le> a"
      using X by simp_all
    have "k - a \<le> card (wtight k G lo hi (bw blk k X))" by (rule wide_sound_tight[OF sound lo su ca])
    then show "X \<in> ?T" using X by simp
  qed
  have finV: "finite V" using blk by (simp add: V)
  have finT: "finite ?T" using finV by (auto intro: finite_subset[of _ "Pow V"])
  have "card ?S \<le> card ?T" using sub finT by (rule card_mono[rotated])
  then have "real (card ?S) * ?p \<le> real (card ?T) * ?p" by (intro mult_right_mono) simp_all
  also have "\<dots> \<le> (2 ^ b / (1 - \<delta>)) ^ k" by (rule wide_kraft[OF mono w beta range cost blk V \<delta> lam])
  finally show ?thesis .
qed

end
