theory Binomial_Estimates
  imports Complex_Main
begin

section \<open>Binomial estimates for the monotone lower bounds\<close>

text \<open>
  The analytic inputs of Theorems E and E\<Zprime> (\<open>extensions/locality-and-monotonicity.md\<close>, \<section>2.9),
  in elementary form:
  \<^item> \<open>central_binomial\<close>: \<open>C(b, b/2)\<^sup>2 (3b + 2) \<le> 2 \<cdot> 4\<^sup>b\<close>, so a decoded block saves
    \<open>\<frac>12 log((3b+2)/2)\<close> bits (in place of \<open>\<frac>12 log(\<pi>b/2)\<close>);
  \<^item> \<open>slice_lower\<close>: \<open>2\<^sup>n \<le> (n + 1) C(n, n/2)\<close>;
  \<^item> \<open>binomial_moment\<close> and \<open>chebyshev_window\<close>: at most a \<open>b / (4d\<^sup>2)\<close> fraction of the inputs
    of a block have weight more than \<open>d\<close> away from \<open>b/2\<close> (Chebyshev instead of Hoeffding);
  \<^item> \<open>window_range\<close> and \<open>window_lower\<close>: every weight in the window has at least
    \<open>C(b, b/2) exp(-2j(j+1)/m)\<close> inputs, where \<open>j\<close> is the half-width and \<open>m = b/2\<close>;
  \<^item> \<open>decoded_fraction\<close>: \<open>(w-1)\<^sup>w\<^sup>-\<^sup>1 / w\<^sup>w \<ge> 1/(ew)\<close>, and \<open>one_plus_power\<close>: \<open>(1 + 1/w)\<^sup>k \<le> e\<^sup>k\<^sup>/\<^sup>w\<close>.
\<close>

subsection \<open>The central binomial coefficient\<close>

lemma central_binomial_even: "((2 * m) choose m)\<^sup>2 * (3 * m + 1) \<le> 16 ^ m"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  define c where "c = (2 * m) choose m"
  define c1 where "c1 = Suc (2 * m) choose m"
  have IH: "c\<^sup>2 * (3 * m + 1) \<le> 16 ^ m" using Suc.IH by (simp add: c_def)
  have e1: "Suc m * c1 = Suc (2 * m) * c"
    using binomial_absorb_comp[of "Suc (2 * m)" m] by (simp add: c_def c1_def Suc_diff_le)
  have e2: "Suc m * (Suc (Suc (2 * m)) choose Suc m) = Suc (Suc (2 * m)) * c1"
    using Suc_times_binomial[of m "Suc (2 * m)"] by (simp add: c1_def)
  have e3: "(2 * Suc m) choose (Suc m) = 2 * c1"
  proof -
    have s: "2 * Suc m = Suc (Suc (2 * m))" by simp
    have "Suc m * ((2 * Suc m) choose Suc m) = Suc (Suc (2 * m)) * c1" by (simp only: s e2)
    also have "\<dots> = Suc m * (2 * c1)" by simp
    finally have "Suc m * ((2 * Suc m) choose Suc m) = Suc m * (2 * c1)" .
    then show ?thesis by (metis mult_left_cancel Zero_not_Suc)
  qed
  have poly: "(2 * m + 1)\<^sup>2 * (3 * m + 4) \<le> 4 * (m + 1)\<^sup>2 * (3 * m + 1)"
    by (simp add: power2_eq_square algebra_simps)
  define P where "P = (m + 1)\<^sup>2 * (3 * m + 1)"
  have Ppos: "0 < P" by (simp add: P_def)
  have sq: "(Suc m * c1)\<^sup>2 = (m + 1)\<^sup>2 * c1\<^sup>2" by (simp only: power_mult_distrib Suc_eq_plus1)
  have "4 * c1\<^sup>2 * (3 * m + 4) * P = 4 * (Suc m * c1)\<^sup>2 * (3 * m + 4) * (3 * m + 1)"
    unfolding sq P_def by (simp only: ac_simps)
  also have "\<dots> = 4 * (2 * m + 1)\<^sup>2 * (3 * m + 4) * (c\<^sup>2 * (3 * m + 1))"
  proof -
    have sq2: "(Suc m * c1)\<^sup>2 = (2 * m + 1)\<^sup>2 * c\<^sup>2"
      unfolding e1 by (simp only: power_mult_distrib Suc_eq_plus1)
    show ?thesis unfolding sq2 by (simp only: ac_simps)
  qed
  also have "\<dots> \<le> 4 * (2 * m + 1)\<^sup>2 * (3 * m + 4) * 16 ^ m" using IH by (rule mult_left_mono) simp
  also have "\<dots> \<le> 4 * (4 * (m + 1)\<^sup>2 * (3 * m + 1)) * 16 ^ m"
    using poly by (intro mult_right_mono mult_left_mono) simp_all
  also have "\<dots> = 16 * 16 ^ m * P" by (simp add: P_def algebra_simps)
  finally have "4 * c1\<^sup>2 * (3 * m + 4) * P \<le> 16 * 16 ^ m * P" .
  then have "4 * c1\<^sup>2 * (3 * m + 4) \<le> 16 * 16 ^ m" using Ppos by simp
  then show ?case unfolding e3 by (simp add: power_mult_distrib algebra_simps)
qed

lemma central_binomial: "(b choose (b div 2))\<^sup>2 * (3 * b + 2) \<le> 2 * 4 ^ b"
proof (cases "even b")
  case True
  then obtain m where b: "b = 2 * m" by blast
  have "((2 * m) choose m)\<^sup>2 * (3 * m + 1) \<le> 16 ^ m" by (rule central_binomial_even)
  moreover have "(4::nat) ^ (2 * m) = 16 ^ m" by (simp add: power_mult)
  ultimately show ?thesis by (simp add: b algebra_simps)
next
  case False
  define m where "m = b div 2"
  have b: "b = Suc (2 * m)" using False by (simp add: m_def)
  define c where "c = (2 * m) choose m"
  define c1 where "c1 = Suc (2 * m) choose m"
  have IH: "c\<^sup>2 * (3 * m + 1) \<le> 16 ^ m" unfolding c_def by (rule central_binomial_even)
  have e1: "Suc m * c1 = Suc (2 * m) * c"
    using binomial_absorb_comp[of "Suc (2 * m)" m] by (simp add: c_def c1_def Suc_diff_le)
  have poly: "(2 * m + 1)\<^sup>2 * (6 * m + 5) \<le> 8 * (m + 1)\<^sup>2 * (3 * m + 1)"
    by (simp add: power2_eq_square algebra_simps)
  define P where "P = (m + 1)\<^sup>2 * (3 * m + 1)"
  have Ppos: "0 < P" by (simp add: P_def)
  have sq: "(Suc m * c1)\<^sup>2 = (m + 1)\<^sup>2 * c1\<^sup>2" by (simp only: power_mult_distrib Suc_eq_plus1)
  have "c1\<^sup>2 * (6 * m + 5) * P = (Suc m * c1)\<^sup>2 * (6 * m + 5) * (3 * m + 1)"
    unfolding sq P_def by (simp only: ac_simps)
  also have "\<dots> = (2 * m + 1)\<^sup>2 * (6 * m + 5) * (c\<^sup>2 * (3 * m + 1))"
  proof -
    have sq2: "(Suc m * c1)\<^sup>2 = (2 * m + 1)\<^sup>2 * c\<^sup>2"
      unfolding e1 by (simp only: power_mult_distrib Suc_eq_plus1)
    show ?thesis unfolding sq2 by (simp only: ac_simps)
  qed
  also have "\<dots> \<le> (2 * m + 1)\<^sup>2 * (6 * m + 5) * 16 ^ m" using IH by (rule mult_left_mono) simp
  also have "\<dots> \<le> 8 * (m + 1)\<^sup>2 * (3 * m + 1) * 16 ^ m" using poly by (rule mult_right_mono) simp
  also have "\<dots> = 8 * 16 ^ m * P" by (simp add: P_def algebra_simps)
  finally have "c1\<^sup>2 * (6 * m + 5) \<le> 8 * 16 ^ m" using Ppos by simp
  moreover have "(4::nat) ^ Suc (2 * m) = 4 * 16 ^ m" by (simp add: power_mult)
  moreover have "b div 2 = m" using b by simp
  ultimately show ?thesis by (simp add: b c1_def algebra_simps)
qed

text \<open>So the gain \<open>2\<^sup>b / C(b, b/2)\<close> of a decoded block is at least \<open>\<surd>((3b+2)/2)\<close>.\<close>

lemma central_ratio: "(3 * real b + 2) / 2 \<le> (2 ^ b / real (b choose (b div 2)))\<^sup>2"
proof -
  define c where "c = real (b choose (b div 2))"
  have cpos: "0 < c" by (simp add: c_def)
  have "real ((b choose (b div 2))\<^sup>2 * (3 * b + 2)) \<le> real (2 * 4 ^ b)"
    by (rule of_nat_mono[OF central_binomial])
  then have le: "c\<^sup>2 * (3 * real b + 2) \<le> 2 * 4 ^ b" by (simp add: c_def algebra_simps)
  have f: "(4::real) ^ b = (2 ^ b)\<^sup>2"
  proof -
    have "(4::real) ^ b = (2 ^ 2) ^ b" by simp
    also have "\<dots> = (2 ^ b)\<^sup>2" by (simp only: power_mult[symmetric] mult.commute)
    finally show ?thesis .
  qed
  have "c\<^sup>2 * (3 * real b + 2) \<le> 2 * (2 ^ b)\<^sup>2" using le by (simp only: f)
  then show ?thesis using cpos by (simp add: c_def[symmetric] power_divide field_simps)
qed

lemma slice_lower: "2 ^ n \<le> (n + 1) * (n choose (n div 2))"
proof -
  have "2 ^ n = (\<Sum>j\<le>n. n choose j)" by (simp add: choose_row_sum)
  also have "\<dots> \<le> (\<Sum>j\<le>n. n choose (n div 2))" by (intro sum_mono binomial_maximum)
  also have "\<dots> = (n + 1) * (n choose (n div 2))" by simp
  finally show ?thesis .
qed

subsection \<open>The second moment and Chebyshev's inequality\<close>

lemma choose_quadratic_sum: "(\<Sum>x\<le>b. x * (x - 1) * (b choose x)) = b * (b - 1) * 2 ^ (b - 2)"
proof (cases b)
  case 0
  then show ?thesis by simp
next
  case (Suc n)
  have "(\<Sum>x\<le>Suc n. x * (x - 1) * (Suc n choose x))
          = (\<Sum>y\<le>n. Suc y * (Suc y - 1) * (Suc n choose Suc y))"
    by (simp only: sum.atMost_Suc_shift mult_0 add_0)
  also have "\<dots> = (\<Sum>y\<le>n. Suc n * (y * (n choose y)))"
  proof (rule sum.cong[OF refl])
    fix y
    have "Suc y * (Suc y - 1) * (Suc n choose Suc y) = y * (Suc y * (Suc n choose Suc y))"
      by (simp only: diff_Suc_1 ac_simps)
    also have "\<dots> = y * (Suc n * (n choose y))" by (simp only: Suc_times_binomial)
    also have "\<dots> = Suc n * (y * (n choose y))" by (simp only: ac_simps)
    finally show "Suc y * (Suc y - 1) * (Suc n choose Suc y) = Suc n * (y * (n choose y))" .
  qed
  also have "\<dots> = Suc n * (n * 2 ^ (n - 1))" by (simp only: sum_distrib_left[symmetric] choose_linear_sum)
  finally have calc: "(\<Sum>x\<le>Suc n. x * (x - 1) * (Suc n choose x)) = Suc n * (n * 2 ^ (n - 1))" .
  have h1: "Suc n - 1 = n" and h2: "Suc n - 2 = n - 1" by simp_all
  show ?thesis unfolding Suc h1 h2 calc by (simp only: mult.assoc)
qed

lemma binomial_moment: "(\<Sum>x\<le>b. int (b choose x) * (2 * int x - int b)\<^sup>2) = int b * 2 ^ b"
proof -
  define A1 where "A1 = (\<Sum>x\<le>b. x * (b choose x))"
  define A2 where "A2 = (\<Sum>x\<le>b. x * (x - 1) * (b choose x))"
  have pt: "int (b choose x) * (2 * int x - int b)\<^sup>2
              = 4 * int (x * (x - 1) * (b choose x)) + (4 - 4 * int b) * int (x * (b choose x))
                + (int b)\<^sup>2 * int (b choose x)" for x
  proof -
    have "int (x * (x - 1)) = int x * int x - int x" by (cases x) (simp_all add: algebra_simps)
    then have "int (x * (x - 1) * (b choose x)) = (int x * int x - int x) * int (b choose x)"
      by (metis of_nat_mult)
    then show ?thesis by (simp add: power2_eq_square algebra_simps)
  qed
  have "(\<Sum>x\<le>b. int (b choose x) * (2 * int x - int b)\<^sup>2)
          = 4 * int A2 + (4 - 4 * int b) * int A1 + (int b)\<^sup>2 * int (\<Sum>x\<le>b. b choose x)"
    by (simp add: pt sum.distrib sum_distrib_left A1_def A2_def)
  also have "\<dots> = 4 * int (b * (b - 1) * 2 ^ (b - 2)) + (4 - 4 * int b) * int (b * 2 ^ (b - 1))
                  + (int b)\<^sup>2 * int (2 ^ b)"
  proof -
    have A1v: "A1 = b * 2 ^ (b - 1)" unfolding A1_def by (rule choose_linear_sum)
    have A2v: "A2 = b * (b - 1) * 2 ^ (b - 2)" unfolding A2_def by (rule choose_quadratic_sum)
    show ?thesis by (simp only: A1v A2v choose_row_sum)
  qed
  also have "\<dots> = int b * 2 ^ b"
  proof (cases "b < 2")
    case True
    then consider "b = 0" | "b = 1" by linarith
    then show ?thesis by cases simp_all
  next
    case False
    then obtain c where c: "b = c + 2" by (metis add.commute le_Suc_ex not_less)
    have "(2::int) ^ b = 4 * 2 ^ c" "(2::int) ^ (b - 1) = 2 * 2 ^ c" "b - 2 = c"
      by (simp_all add: c)
    then show ?thesis by (simp add: c power2_eq_square algebra_simps)
  qed
  finally show ?thesis .
qed

text \<open>The window \<open>[m - d, m + d]\<close> around \<open>m = b/2\<close>; outside it, \<open>|2x - b| \<ge> 2d\<close>.\<close>

lemma window_far:
  assumes m: "m = b div 2" and x: "x < m - d \<or> m + d < x"
  shows "(2 * int d)\<^sup>2 \<le> (2 * int x - int b)\<^sup>2"
proof -
  have "\<bar>2 * int d\<bar> \<le> \<bar>2 * int x - int b\<bar>" using x m by linarith
  then show ?thesis by (simp only: abs_le_square_iff[symmetric])
qed

lemma chebyshev_window:
  assumes m: "m = b div 2"
  shows "4 * d\<^sup>2 * (\<Sum>x\<in>{x. x \<le> b \<and> (x < m - d \<or> m + d < x)}. b choose x) \<le> b * 2 ^ b"
proof -
  let ?A = "{x. x \<le> b \<and> (x < m - d \<or> m + d < x)}"
  have sub: "?A \<subseteq> {..b}" by auto
  have "int (4 * d\<^sup>2 * (\<Sum>x\<in>?A. b choose x)) = (\<Sum>x\<in>?A. int (b choose x) * (2 * int d)\<^sup>2)"
    by (simp add: sum_distrib_left sum_distrib_right of_nat_sum power_mult_distrib algebra_simps)
  also have "\<dots> \<le> (\<Sum>x\<in>?A. int (b choose x) * (2 * int x - int b)\<^sup>2)"
    using window_far[OF m] by (intro sum_mono mult_left_mono) auto
  also have "\<dots> \<le> (\<Sum>x\<le>b. int (b choose x) * (2 * int x - int b)\<^sup>2)"
    using sub by (intro sum_mono2) auto
  also have "\<dots> = int (b * 2 ^ b)" by (simp add: binomial_moment)
  finally show ?thesis by linarith
qed

subsection \<open>Binomial coefficients in the window\<close>

lemma window_range:
  assumes m: "m = b div 2" and d: "d + 1 \<le> m"
  shows "\<forall>x. m - d - 1 \<le> x \<longrightarrow> x < m + d \<longrightarrow> b choose (m - d - 1) \<le> b choose x"
proof (intro allI impI)
  fix x assume x1: "m - d - 1 \<le> x" and x2: "x < m + d"
  show "b choose (m - d - 1) \<le> b choose x"
  proof (cases "x \<le> m")
    case True
    then show ?thesis using x1 m by (intro binomial_mono) linarith+
  next
    case False
    have xb: "x \<le> b" using x2 d m by linarith
    have "b choose (m - d - 1) \<le> b choose (b - x)" using False x2 m by (intro binomial_mono) linarith+
    also have "\<dots> = b choose x" using binomial_symmetric[OF xb] by simp
    finally show ?thesis .
  qed
qed

lemma one_minus_exp:
  fixes e :: real
  assumes "0 \<le> e" "e \<le> 1/2"
  shows "exp (- 2 * e) \<le> 1 - e"
proof -
  have "- e - 2 * e\<^sup>2 \<le> ln (1 - e)" by (rule ln_one_minus_pos_lower_bound[OF assms])
  moreover have "2 * e\<^sup>2 \<le> e"
  proof -
    have "e * (2 * e) \<le> e * 1" using assms by (intro mult_left_mono) simp_all
    then show ?thesis by (simp add: power2_eq_square algebra_simps)
  qed
  ultimately have "- 2 * e \<le> ln (1 - e)" by linarith
  then have "exp (- 2 * e) \<le> exp (ln (1 - e))" by simp
  also have "\<dots> = 1 - e" using assms by simp
  finally show ?thesis .
qed

lemma window_lower:
  assumes m: "m = b div 2" and j: "4 * j \<le> m"
  shows "real (b choose m) * exp (- 2 * real j * (real j + 1) / real m) \<le> real (b choose (m - j))"
  using j
proof (induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have m4: "4 * j + 4 \<le> m" using Suc.prems by simp
  have IH: "real (b choose m) * exp (- 2 * real j * (real j + 1) / real m) \<le> real (b choose (m - j))"
    using Suc.IH m4 by simp
  define e :: real where "e = (2 * real j + 2) / real m"
  have mpos: "0 < real m" using m4 by simp
  have e0: "0 \<le> e" and e1: "e \<le> 1/2" using m4 mpos by (simp_all add: e_def field_simps)
  text \<open>The ratio of consecutive coefficients.\<close>
  define k where "k = m - Suc j"
  have kS: "Suc k = m - j" using m4 by (simp add: k_def)
  have bm: "b - m \<le> m + 1" "m \<le> b" using m by simp_all
  have rat: "real (Suc k) * real (b choose Suc k) = real (b - k) * real (b choose k)"
  proof -
    have "Suc k * (b choose Suc k) = b * ((b - 1) choose k)" by (rule binomial_absorption)
    also have "\<dots> = (b - k) * (b choose k)" by (rule binomial_absorb_comp[symmetric])
    finally show ?thesis by (metis of_nat_mult)
  qed
  have bk: "real (b - k) \<le> real m + real j + 2" "0 < real (b - k)" using bm m4 by (simp_all add: k_def)
  have mj: "real (Suc k) = real m - real j" using kS m4 by simp
  have fac: "1 - e \<le> (real m - real j) / real (b - k)"
  proof -
    have "(1 - e) * real (b - k) \<le> (1 - e) * (real m + real j + 2)"
      using bk e1 by (intro mult_left_mono) simp_all
    also have "\<dots> = real m - real j - (2 * real j + 2) * (real j + 2) / real m"
      using mpos by (simp add: e_def field_simps)
    also have "\<dots> \<le> real m - real j" using mpos by simp
    finally show ?thesis using bk by (simp add: le_divide_eq)
  qed
  have ex: "- 2 * real (Suc j) * (real (Suc j) + 1) / real m
              = - 2 * real j * (real j + 1) / real m + - 2 * e"
    using mpos by (simp add: e_def field_simps)
  have "real (b choose m) * exp (- 2 * real (Suc j) * (real (Suc j) + 1) / real m)
          = real (b choose m) * exp (- 2 * real j * (real j + 1) / real m) * exp (- 2 * e)"
    unfolding ex exp_add by (simp only: mult.assoc)
  also have "\<dots> \<le> real (b choose (m - j)) * (1 - e)"
    using IH one_minus_exp[OF e0 e1] by (intro mult_mono) simp_all
  also have "\<dots> \<le> real (b choose (m - j)) * ((real m - real j) / real (b - k))"
    using fac by (intro mult_left_mono) simp_all
  also have "\<dots> = real (b choose (m - Suc j))"
    using rat bk(2) by (simp add: kS[symmetric] mj[symmetric] k_def field_simps)
  finally show ?case .
qed

text \<open>
  So the smallest coefficient \<open>\<beta> = C(b, m - d - 1)\<close> of a window of half-width \<open>d\<close> is at least
  \<open>2\<^sup>b e\<^sup>-\<^sup>2\<^sup>(\<^sup>d\<^sup>+\<^sup>1\<^sup>)\<^sup>(\<^sup>d\<^sup>+\<^sup>2\<^sup>)\<^sup>/\<^sup>m / (b + 1)\<close>.  With \<open>d \<approx> 2\<surd>b\<close> this is \<open>2\<^sup>b e\<^sup>-\<^sup>1\<^sup>6\<^sup>-\<^sup>o\<^sup>(\<^sup>1\<^sup>) / (b + 1)\<close>.
\<close>

lemma window_beta:
  assumes m: "m = b div 2" and j: "4 * j \<le> m"
  shows "2 ^ b / (real b + 1) * exp (- 2 * real j * (real j + 1) / real m) \<le> real (b choose (m - j))"
proof -
  have "real (2 ^ b) \<le> real ((b + 1) * (b choose (b div 2)))" by (rule of_nat_mono[OF slice_lower])
  then have c: "2 ^ b / (real b + 1) \<le> real (b choose m)" using m by (simp add: field_simps)
  have "2 ^ b / (real b + 1) * exp (- 2 * real j * (real j + 1) / real m)
          \<le> real (b choose m) * exp (- 2 * real j * (real j + 1) / real m)"
    using c by (rule mult_right_mono) simp
  also have "\<dots> \<le> real (b choose (m - j))" by (rule window_lower[OF m j])
  finally show ?thesis .
qed

subsection \<open>Two elementary inequalities\<close>

lemma decoded_fraction:
  assumes w: "1 \<le> w"
  shows "1 / (exp 1 * real w) \<le> real ((w - 1) ^ (w - 1)) / real (w ^ w)"
proof (cases "w = 1")
  case True
  have "1 \<le> exp (1::real)" by simp
  then show ?thesis using True by (simp add: divide_le_eq)
next
  case False
  then obtain v where v: "w = Suc v" "1 \<le> v" using w by (metis Suc_le_D le_neq_implies_less less_Suc_eq_le not_less)
  have vpos: "0 < real v" using v by simp
  have "(1 + 1 / real v) ^ v \<le> exp (1 / real v) ^ v"
    by (intro power_mono) (simp_all add: exp_ge_add_one_self add_increasing)
  also have "\<dots> = exp 1" using vpos by (simp add: exp_of_nat_mult[symmetric])
  finally have e: "(1 + 1 / real v) ^ v \<le> exp 1" .
  have "(real v + 1) ^ v = real v ^ v * (1 + 1 / real v) ^ v"
    using vpos by (simp add: power_mult_distrib[symmetric] field_simps)
  also have "\<dots> \<le> real v ^ v * exp 1" using e by (intro mult_left_mono) simp_all
  finally have le: "(real v + 1) ^ v \<le> real v ^ v * exp 1" .
  have "real (w ^ w) = (real v + 1) * (real v + 1) ^ v" using v by (simp add: algebra_simps)
  also have "\<dots> \<le> (real v + 1) * (real v ^ v * exp 1)" using le by (intro mult_left_mono) simp_all
  finally have W: "real (w ^ w) \<le> exp 1 * real w * real ((w - 1) ^ (w - 1))" using v by (simp add: algebra_simps)
  define A where "A = real ((w - 1) ^ (w - 1))"
  have B: "0 < real (w ^ w)" using w by simp
  have pos: "0 < exp 1 * real w" using w by simp
  have "1 / (exp 1 * real w) = real (w ^ w) / (exp 1 * real w) / real (w ^ w)" using B by simp
  also have "\<dots> \<le> (exp 1 * real w * A) / (exp 1 * real w) / real (w ^ w)"
    using W pos B by (intro divide_right_mono) (simp_all add: A_def)
  also have "\<dots> = A / real (w ^ w)" using pos w by simp
  finally show ?thesis by (simp add: A_def)
qed

lemma one_plus_power:
  assumes w: "1 \<le> w"
  shows "(1 + 1 / real w) ^ k \<le> exp (real k / real w)"
proof -
  have "(1 + 1 / real w) ^ k \<le> exp (1 / real w) ^ k"
    by (intro power_mono) (simp_all add: exp_ge_add_one_self add_increasing)
  also have "\<dots> = exp (real k / real w)" by (simp add: exp_of_nat_mult[symmetric])
  finally show ?thesis .
qed

end
