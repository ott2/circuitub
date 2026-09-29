theory Majority_Circuits
  imports Construction
begin

section \<open>Theorem 1 of arXiv:2609.34029, in the paper's form\<close>

text \<open>
  Inputs are \<open>n\<close> Boolean variables \<open>x\<^sub>0, \<dots>, x\<^sub>n\<^sub>-\<^sub>1\<close>, i.e. \<open>\<sigma> :: nat \<Rightarrow> bool\<close> restricted to
  \<open>{..<n}\<close>.  A symmetric function is given by its value \<open>g w\<close> on inputs of Hamming weight \<open>w\<close>.
\<close>

definition weight :: "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "weight n \<sigma> = card {i. i < n \<and> \<sigma> i}"

definition vars :: "nat \<Rightarrow> nat lit list" where
  "vars n = map (\<lambda>i. (i, True)) [0..<n]"

lemma cnt_vars: "cnt \<sigma> (vars n) = weight n \<sigma>"
proof -
  have "cnt \<sigma> (vars n) = length (filter \<sigma> [0..<n])"
    by (simp add: cnt_def vars_def filter_map comp_def litval_def)
  also have "\<dots> = card (set (filter \<sigma> [0..<n]))"
    by (rule distinct_card[symmetric]) simp
  also have "set (filter \<sigma> [0..<n]) = {i. i < n \<and> \<sigma> i}" by auto
  finally show ?thesis by (simp add: weight_def)
qed

lemma length_vars [simp]: "length (vars n) = n"
  by (simp add: vars_def)

lemma ceil_step: "(r::real) \<le> y + 1 \<Longrightarrow> 0 \<le> y \<Longrightarrow> r + 1 \<le> 2 * (y + 1)"
  by (simp add: algebra_simps)

text \<open>Theorem 1 with the additive \<open>+1\<close> covering \<open>n = 0\<close>:
  every symmetric function has depth-\<open>d\<close> formulas of size \<open>2\<^sup>O\<^sup>(\<^sup>n\<^sup>1\<^sup>/\<^sup>(\<^sup>d\<^sup>-\<^sup>1\<^sup>)\<^sup>+\<^sup>1\<^sup>)\<close>.\<close>

theorem symmetric_functions:
  assumes d: "2 \<le> d"
  shows "\<exists>C. \<forall>n g. \<exists>f. SIG d f
           \<and> real (gates f) \<le> 2 powr (C * (real n powr (1 / real (d - 1)) + 1))
           \<and> (\<forall>\<sigma>. eval \<sigma> f = g (weight n \<sigma>))"
proof -
  obtain C where C: "\<forall>k (L::nat lit list) g. length L \<le> k ^ (d - 1) \<longrightarrow>
      (\<exists>f. SIG d f \<and> gates f \<le> 2 ^ (C * (k + 1)) \<and> (\<forall>\<sigma>. eval \<sigma> f = g (cnt \<sigma> L)))"
    using symmetric_upper_bound[OF d] by blast
  show ?thesis
  proof (intro exI[of _ "2 * real C"] allI)
    fix n g
    define x where "x = real n powr (1 / real (d - 1))"
    define k where "k = nat \<lceil>x\<rceil>"
    have d1: "0 < d - 1" using d by simp
    have x0: "0 \<le> x" by (simp add: x_def)
    have kx: "x \<le> real k" by (simp add: k_def real_nat_ceiling_ge)
    have kx1: "real k \<le> x + 1"
    proof -
      have c0: "0 \<le> \<lceil>x\<rceil>" using x0 by simp
      have "real k = of_int \<lceil>x\<rceil>" using c0 by (simp add: k_def)
      also have "\<dots> \<le> x + 1" by (rule of_int_ceiling_le_add_one)
      finally show ?thesis .
    qed
    have nk: "n \<le> k ^ (d - 1)"
    proof (cases "n = 0")
      case False
      have "real n = x ^ (d - 1)"
      proof -
        have "x ^ (d - 1) = x powr real (d - 1)"
          using False by (simp add: x_def powr_realpow)
        also have "\<dots> = real n powr (1 / real (d - 1) * real (d - 1))"
          by (simp add: x_def powr_powr)
        also have "\<dots> = real n" using d1 by simp
        finally show ?thesis by simp
      qed
      also have "\<dots> \<le> real k ^ (d - 1)" using x0 kx by (intro power_mono)
      finally show ?thesis by (simp flip: of_nat_power)
    qed simp
    have "length (vars n) \<le> k ^ (d - 1)" using nk by simp
    then have "\<exists>f. SIG d f \<and> gates f \<le> 2 ^ (C * (k + 1)) \<and> (\<forall>\<sigma>. eval \<sigma> f = g (cnt \<sigma> (vars n)))"
      using C by blast
    then obtain f where f: "SIG d f" "gates f \<le> 2 ^ (C * (k + 1))"
      "\<forall>\<sigma>. eval \<sigma> f = g (cnt \<sigma> (vars n))" by blast
    show "\<exists>f. SIG d f \<and> real (gates f) \<le> 2 powr (2 * real C * (real n powr (1 / real (d - 1)) + 1))
              \<and> (\<forall>\<sigma>. eval \<sigma> f = g (weight n \<sigma>))"
    proof (intro exI[of _ f] conjI allI)
      show "SIG d f" by (rule f(1))
      show "eval \<sigma> f = g (weight n \<sigma>)" for \<sigma> using f(3) by (simp add: cnt_vars)
      have "real (gates f) \<le> real (2 ^ (C * (k + 1)))" using f(2) by (simp only: of_nat_le_iff)
      also have "\<dots> = 2 powr (real C * (real k + 1))"
      proof -
        have "real ((2::nat) ^ (C * (k + 1))) = (2::real) ^ (C * (k + 1))" by simp
        also have "\<dots> = 2 powr real (C * (k + 1))" by (rule powr_realpow[symmetric]) simp
        also have "real (C * (k + 1)) = real C * (real k + 1)" by (simp add: algebra_simps)
        finally show ?thesis .
      qed
      also have "\<dots> \<le> 2 powr (2 * real C * (x + 1))"
      proof (intro powr_mono)
        have "real k + 1 \<le> 2 * (x + 1)" using kx1 x0 by (rule ceil_step)
        then show "real C * (real k + 1) \<le> 2 * real C * (x + 1)"
          using mult_left_mono[of "real k + 1" "2 * (x + 1)" "real C"] by (simp add: algebra_simps)
      qed simp
      finally show "real (gates f) \<le> 2 powr (2 * real C * (real n powr (1 / real (d - 1)) + 1))"
        by (simp add: x_def)
    qed
  qed
qed

text \<open>The same, in the literal \<open>2\<^sup>O\<^sup>(\<^sup>n\<^sup>1\<^sup>/\<^sup>(\<^sup>d\<^sup>-\<^sup>1\<^sup>)\<^sup>)\<close> form for \<open>n \<ge> 1\<close>.\<close>

theorem symmetric_functions_big_O:
  assumes d: "2 \<le> d"
  shows "\<exists>C. \<forall>n \<ge> 1. \<forall>g. \<exists>f. SIG d f
           \<and> real (gates f) \<le> 2 powr (C * real n powr (1 / real (d - 1)))
           \<and> (\<forall>\<sigma>. eval \<sigma> f = g (weight n \<sigma>))"
proof -
  obtain C where C: "\<forall>n g. \<exists>f. SIG d f
      \<and> real (gates f) \<le> 2 powr (C * (real n powr (1 / real (d - 1)) + 1))
      \<and> (\<forall>\<sigma>. eval \<sigma> f = g (weight n \<sigma>))"
    using symmetric_functions[OF d] by blast
  show ?thesis
  proof (intro exI[of _ "2 * C"] allI impI)
    fix n :: nat and g assume n: "1 \<le> n"
    have "\<exists>f. SIG d f \<and> real (gates f) \<le> 2 powr (C * (real n powr (1 / real (d - 1)) + 1))
            \<and> (\<forall>\<sigma>. eval \<sigma> f = g (weight n \<sigma>))" using C by blast
    then obtain f where f: "SIG d f" "real (gates f) \<le> 2 powr (C * (real n powr (1 / real (d - 1)) + 1))"
      "\<forall>\<sigma>. eval \<sigma> f = g (weight n \<sigma>)" by blast
    have y1: "1 \<le> real n powr (1 / real (d - 1))" using n by (simp add: ge_one_powr_ge_zero)
    have g1: "1 \<le> real (gates f)"
    proof -
      have "\<exists>fs. f = Or fs" using d f(1) by (intro SIG_Or) simp_all
      then show ?thesis by auto
    qed
    have C0: "0 \<le> C"
    proof (rule ccontr)
      assume "\<not> 0 \<le> C"
      then have "C * (real n powr (1 / real (d - 1)) + 1) < 0"
        using y1 by (simp add: mult_neg_pos)
      then have "(2::real) powr (C * (real n powr (1 / real (d - 1)) + 1)) < 1"
        by (intro powr_less_one) simp_all
      with g1 f(2) show False by simp
    qed
    show "\<exists>f. SIG d f \<and> real (gates f) \<le> 2 powr (2 * C * real n powr (1 / real (d - 1)))
              \<and> (\<forall>\<sigma>. eval \<sigma> f = g (weight n \<sigma>))"
    proof (intro exI[of _ f] conjI)
      have "C * (real n powr (1 / real (d - 1)) + 1) \<le> 2 * C * real n powr (1 / real (d - 1))"
        using y1 C0 mult_left_mono[of "real n powr (1 / real (d - 1)) + 1"
                                     "2 * real n powr (1 / real (d - 1))" C] by simp
      then have "(2::real) powr (C * (real n powr (1 / real (d - 1)) + 1))
                 \<le> 2 powr (2 * C * real n powr (1 / real (d - 1)))"
        by (rule powr_mono) simp
      with f(2) show "real (gates f) \<le> 2 powr (2 * C * real n powr (1 / real (d - 1)))"
        by (rule order.trans)
    qed (use f in auto)
  qed
qed

section \<open>Majority\<close>

definition majority :: "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "majority n \<sigma> \<longleftrightarrow> n \<le> 2 * weight n \<sigma>"

corollary majority_circuits:
  assumes "2 \<le> d"
  shows "\<exists>C. \<forall>n \<ge> 1. \<exists>f. SIG d f
           \<and> real (gates f) \<le> 2 powr (C * real n powr (1 / real (d - 1)))
           \<and> (\<forall>\<sigma>. eval \<sigma> f = majority n \<sigma>)"
proof -
  obtain C where C: "\<forall>n \<ge> 1. \<forall>g. \<exists>f. SIG d f
      \<and> real (gates f) \<le> 2 powr (C * real n powr (1 / real (d - 1)))
      \<and> (\<forall>\<sigma>. eval \<sigma> f = g (weight n \<sigma>))"
    using symmetric_functions_big_O[OF assms] by blast
  show ?thesis
  proof (intro exI[of _ C] allI impI)
    fix n :: nat assume n: "1 \<le> n"
    have Cn: "\<forall>g. \<exists>f. SIG d f \<and> real (gates f) \<le> 2 powr (C * real n powr (1 / real (d - 1)))
            \<and> (\<forall>\<sigma>. eval \<sigma> f = g (weight n \<sigma>))" using C n by blast
    note inst = spec[OF Cn, of "\<lambda>w. n \<le> 2 * w"]
    from inst show "\<exists>f. SIG d f \<and> real (gates f) \<le> 2 powr (C * real n powr (1 / real (d - 1)))
                \<and> (\<forall>\<sigma>. eval \<sigma> f = majority n \<sigma>)"
      by (simp add: majority_def)
  qed
qed

text \<open>Depth 3 (\<open>\<Sigma>\<^sub>3\<close>, an OR of CNFs): Majority in size \<open>2\<^sup>O\<^sup>(\<^sup>\<surd>\<^sup>n\<^sup>)\<close>.\<close>

corollary majority_depth3:
  "\<exists>C. \<forall>n \<ge> 1. \<exists>f. SIG 3 f \<and> real (gates f) \<le> 2 powr (C * sqrt (real n))
                 \<and> (\<forall>\<sigma>. eval \<sigma> f = majority n \<sigma>)"
  using majority_circuits[of 3] by (simp add: powr_half_sqrt)

end
