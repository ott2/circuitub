theory Moduli
  imports Main
begin

section \<open>Pairwise coprime moduli of size \<open>\<Theta>(k)\<close>, and the Chinese remainder step\<close>

text \<open>
  The paper takes \<open>k\<^sub>i\<close> = the smallest power of the \<open>i\<close>-th prime exceeding \<open>n\<^sup>1\<^sup>/\<^sup>(\<^sup>d\<^sup>-\<^sup>1\<^sup>)\<close>.
  Any \<open>d-1\<close> pairwise coprime moduli in \<open>[k+1, O(k)]\<close> serve equally well; we use Gödel's
  \<open>\<beta>\<close>-function moduli \<open>1 + (i+1) \<cdot> D! \<cdot> (k+1)\<close>, \<open>i < D\<close>.
\<close>

definition modq :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "modq D k i = 1 + Suc i * fact D * (k + 1)"

lemma modq_ge: "k + 1 < modq D k i"
proof -
  have "1 * 1 \<le> Suc i * fact D" by (rule mult_le_mono) (simp_all add: fact_ge_1)
  then have P: "1 \<le> Suc i * fact D" by simp
  have "1 * (k + 1) \<le> Suc i * fact D * (k + 1)" using P by (rule mult_right_mono) simp
  then have "k + 1 \<le> Suc i * fact D * (k + 1)" by simp
  then show ?thesis by (simp add: modq_def)
qed

lemma modq_pos: "0 < modq D k i"
  by (simp add: modq_def)

lemma modq_le:
  assumes "i < D" shows "modq D k i \<le> (D * fact D + 1) * (k + 1)"
proof -
  have "Suc i * fact D * (k + 1) \<le> D * fact D * (k + 1)"
    using assms by (intro mult_right_mono) simp_all
  then show ?thesis by (simp add: modq_def algebra_simps)
qed

lemma modq_coprime:
  assumes "i < j" "j < D"
  shows "coprime (modq D k i) (modq D k j)"
proof (rule coprimeI)
  fix c assume ci: "c dvd modq D k i" and cj: "c dvd modq D k j"
  obtain d where j: "j = i + d" and d0: "0 < d" using assms(1) by (metis less_imp_add_positive)
  let ?F = "fact D * (k + 1)"
  have e: "Suc j * modq D k i = Suc i * modq D k j + d"
    unfolding modq_def j by (simp add: algebra_simps)
  have "c dvd Suc j * modq D k i" using ci by simp
  moreover have "c dvd Suc i * modq D k j" using cj by simp
  ultimately have cd: "c dvd d" using e by (simp add: dvd_add_right_iff)
  have "d dvd fact D" using d0 assms j by (intro dvd_fact) simp_all
  with cd have "c dvd fact D" by (rule dvd_trans)
  then have X: "c dvd Suc i * fact D * (k + 1)" by simp
  have ci': "c dvd Suc i * fact D * (k + 1) + 1"
    using ci unfolding modq_def by (simp only: add.commute)
  show "c dvd 1" using ci' by (simp only: dvd_add_right_iff[OF X])
qed

lemma modq_prod_gt:
  assumes "0 < D" "m \<le> k ^ D"
  shows "m < (\<Prod>i<D. modq D k i)"
proof -
  have "m \<le> k ^ D" by (rule assms(2))
  also have "\<dots> < (k + 1) ^ D" using assms(1) by (intro power_strict_mono) simp_all
  also have "\<dots> = (\<Prod>i<D. k + 1)" by simp
  also have "\<dots> \<le> (\<Prod>i<D. modq D k i)"
  proof (intro prod_mono conjI)
    fix i show "0 \<le> k + 1" by simp
    show "k + 1 \<le> modq D k i" using modq_ge[of k D i] by simp
  qed
  finally show ?thesis .
qed

subsection \<open>Chinese remainder: congruences modulo all \<open>q\<^sub>i\<close> pin down a small number\<close>

lemma pairwise_coprime_prod_dvd:
  fixes q :: "nat \<Rightarrow> nat"
  assumes "\<And>i j. i < j \<Longrightarrow> j < D \<Longrightarrow> coprime (q i) (q j)"
    and "\<And>i. i < D \<Longrightarrow> q i dvd n"
  shows "(\<Prod>i<D. q i) dvd n"
  using assms
proof (induction D)
  case (Suc D)
  have IH: "(\<Prod>i<D. q i) dvd n" using Suc by simp
  have co: "coprime (\<Prod>i<D. q i) (q D)"
    by (rule prod_coprime_left) (use Suc.prems(1) in simp)
  have "(\<Prod>i<D. q i) * q D dvd n" using co IH Suc.prems(2)[of D] by (simp add: divides_mult)
  then show ?case by (simp add: lessThan_Suc mult.commute)
qed simp

theorem crt_eq:
  fixes q :: "nat \<Rightarrow> nat"
  assumes co: "\<And>i j. i < j \<Longrightarrow> j < D \<Longrightarrow> coprime (q i) (q j)"
    and cong: "\<And>i. i < D \<Longrightarrow> a mod q i = b mod q i"
    and a: "a < (\<Prod>i<D. q i)" and b: "b < (\<Prod>i<D. q i)"
  shows "a = b"
proof -
  have main: "x = y" if le: "y \<le> x" and xb: "x < (\<Prod>i<D. q i)"
    and cg: "\<And>i. i < D \<Longrightarrow> x mod q i = y mod q i" for x y
  proof -
    have "\<And>i. i < D \<Longrightarrow> q i dvd x - y" using le cg by (simp add: mod_eq_dvd_iff_nat)
    then have dv: "(\<Prod>i<D. q i) dvd x - y" using co by (intro pairwise_coprime_prod_dvd) simp_all
    have lt: "x - y < (\<Prod>i<D. q i)" using xb by simp
    have "x - y = 0"
    proof (rule ccontr)
      assume "x - y \<noteq> 0"
      then have "(\<Prod>i<D. q i) \<le> x - y" using dv by (intro dvd_imp_le) simp_all
      with lt show False by simp
    qed
    with le show ?thesis by simp
  qed
  show ?thesis
  proof (cases "b \<le> a")
    case True
    then show ?thesis by (rule main[OF _ a cong])
  next
    case False
    then have le: "a \<le> b" by simp
    have cg: "b mod q i = a mod q i" if "i < D" for i using cong[OF that] by simp
    have "b = a" by (rule main[OF le b cg])
    then show ?thesis by simp
  qed
qed

end
