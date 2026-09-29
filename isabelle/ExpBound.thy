theory ExpBound
  imports Main
begin

section \<open>Functions bounded by \<open>2\<^sup>O\<^sup>(\<^sup>K\<^sup>)\<close>\<close>

text \<open>
  \<open>EB f\<close>: there is a constant \<open>c\<close> with \<open>f K \<le> 2\<^sup>c\<^sup>\<cdot>\<^sup>K\<close> for all \<open>K \<ge> 1\<close>.  The closure rules
  below let us discharge the final size bound by following the syntax of the expression.
\<close>

definition EB :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "EB f \<longleftrightarrow> (\<exists>c. \<forall>K\<ge>1. f K \<le> 2 ^ (c * K))"

lemma EB_const: "EB (\<lambda>K. c)"
  unfolding EB_def
proof (intro exI allI impI)
  fix K :: nat assume K: "1 \<le> K"
  have "c < 2 ^ c" by (rule less_exp)
  also have "(2::nat) ^ c \<le> 2 ^ (c * K)" using K by (intro power_increasing) simp_all
  finally show "c \<le> 2 ^ (c * K)" by simp
qed

lemma EB_id: "EB (\<lambda>K. K)"
  unfolding EB_def
proof (intro exI[of _ 1] allI impI)
  fix K :: nat
  show "K \<le> 2 ^ (1 * K)" using less_exp[of K] by simp
qed

lemma EB_add:
  assumes "EB f" "EB g" shows "EB (\<lambda>K. f K + g K)"
proof -
  obtain a where a: "\<And>K. 1 \<le> K \<Longrightarrow> f K \<le> 2 ^ (a * K)" using assms(1) by (auto simp: EB_def)
  obtain b where b: "\<And>K. 1 \<le> K \<Longrightarrow> g K \<le> 2 ^ (b * K)" using assms(2) by (auto simp: EB_def)
  show ?thesis unfolding EB_def
  proof (intro exI[of _ "a + b + 1"] allI impI)
    fix K :: nat assume K: "1 \<le> K"
    have "f K \<le> 2 ^ ((a + b) * K)"
      using a[OF K] by (rule order.trans) (intro power_increasing, simp_all)
    moreover have "g K \<le> 2 ^ ((a + b) * K)"
      using b[OF K] by (rule order.trans) (intro power_increasing, simp_all)
    ultimately have "f K + g K \<le> 2 ^ Suc ((a + b) * K)" by simp
    also have "(2::nat) ^ Suc ((a + b) * K) \<le> 2 ^ ((a + b + 1) * K)"
      using K by (intro power_increasing) (simp_all add: algebra_simps)
    finally show "f K + g K \<le> 2 ^ ((a + b + 1) * K)" .
  qed
qed

lemma EB_mult:
  assumes "EB f" "EB g" shows "EB (\<lambda>K. f K * g K)"
proof -
  obtain a where a: "\<And>K. 1 \<le> K \<Longrightarrow> f K \<le> 2 ^ (a * K)" using assms(1) by (auto simp: EB_def)
  obtain b where b: "\<And>K. 1 \<le> K \<Longrightarrow> g K \<le> 2 ^ (b * K)" using assms(2) by (auto simp: EB_def)
  show ?thesis unfolding EB_def
  proof (intro exI[of _ "a + b"] allI impI)
    fix K :: nat assume K: "1 \<le> K"
    have "f K * g K \<le> 2 ^ (a * K) * 2 ^ (b * K)" using a[OF K] b[OF K] by (rule mult_le_mono)
    also have "\<dots> = 2 ^ ((a + b) * K)" by (simp add: power_add algebra_simps)
    finally show "f K * g K \<le> 2 ^ ((a + b) * K)" .
  qed
qed

lemma EB_pow:
  assumes "EB f" shows "EB (\<lambda>K. f K ^ n)"
proof -
  obtain a where a: "\<And>K. 1 \<le> K \<Longrightarrow> f K \<le> 2 ^ (a * K)" using assms by (auto simp: EB_def)
  show ?thesis unfolding EB_def
  proof (intro exI[of _ "a * n"] allI impI)
    fix K :: nat assume K: "1 \<le> K"
    have "f K ^ n \<le> (2 ^ (a * K)) ^ n" using a[OF K] by (rule power_mono) simp
    also have "\<dots> = 2 ^ (a * n * K)" by (simp add: power_mult[symmetric] algebra_simps)
    finally show "f K ^ n \<le> 2 ^ (a * n * K)" .
  qed
qed

lemma EB_exp: "EB (\<lambda>K. b ^ (c * K))"
  unfolding EB_def
proof (intro exI[of _ "b * c"] allI impI)
  fix K :: nat
  have "b \<le> 2 ^ b" using less_exp[of b] by simp
  then have "b ^ (c * K) \<le> (2 ^ b) ^ (c * K)" by (rule power_mono) simp
  also have "\<dots> = 2 ^ (b * c * K)" by (simp add: power_mult[symmetric] algebra_simps)
  finally show "b ^ (c * K) \<le> 2 ^ (b * c * K)" .
qed

lemma EB_mono:
  assumes "\<And>K. 1 \<le> K \<Longrightarrow> g K \<le> f K" "EB f" shows "EB g"
  using assms unfolding EB_def by (meson order.trans)

lemmas EB_intros = EB_add EB_mult EB_pow EB_exp EB_const EB_id

end
