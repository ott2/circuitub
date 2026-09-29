theory Count
  imports Test Complex_Main
begin

section \<open>At least \<open>k!\<close> of the \<open>k\<^sup>k\<close> shift vectors accept a given input\<close>

text \<open>
  The paper's coverage step: for a fixed input, the shift vectors that make the shifted
  block weights pairwise distinct mod \<open>k\<close> correspond to the \<open>k!\<close> arrangements of the
  residues \<open>0, \<dots>, k-1\<close>.  We prove the direction needed: an injection from arrangements
  (distinct lists of length \<open>k\<close> over \<open>{..<k}\<close>) into accepting shift vectors.
\<close>

definition shifts :: "nat \<Rightarrow> nat list set" where
  "shifts k = {ss. set ss \<subseteq> {..<k} \<and> length ss = k}"

definition arrangements :: "nat \<Rightarrow> nat list set" where
  "arrangements k = {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<k}}"

lemma finite_shifts: "finite (shifts k)"
  unfolding shifts_def by (rule finite_lists_length_eq) simp

lemma card_shifts: "card (shifts k) = k ^ k"
  unfolding shifts_def using card_lists_length_eq[of "{..<k}" k] by simp

lemma card_arrangements: "card (arrangements k) = fact k"
proof -
  have "card (arrangements k) = \<Prod>{card {..<k} - k + 1 .. card {..<k}}"
    unfolding arrangements_def by (rule card_lists_distinct_length_eq) simp_all
  also have "\<dots> = \<Prod>{1..k}" by simp
  finally show ?thesis by (simp add: fact_prod)
qed

text \<open>The inverse map: from a target arrangement back to the shifts that realise it.\<close>

definition unshift :: "nat \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v lit list list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "unshift k \<sigma> Bs xs = map (\<lambda>p. (snd p + k - cnt \<sigma> (fst p) mod k) mod k) (zip Bs xs)"

lemma mod_unshift:
  fixes w x k :: nat
  assumes "x < k"
  shows "(w + (x + k - w mod k) mod k) mod k = x"
proof -
  have k: "k > 0" using assms by simp
  have le: "w mod k \<le> x + k" using k by (simp add: less_imp_le_nat trans_le_add2)
  have "(w + (x + k - w mod k) mod k) mod k = (w + (x + k - w mod k)) mod k"
    by (simp add: mod_add_right_eq)
  also have "\<dots> = (w mod k + (x + k - w mod k)) mod k"
    by (simp add: mod_add_left_eq)
  also have "w mod k + (x + k - w mod k) = x + k" using le by simp
  finally show ?thesis using assms by simp
qed

lemma shifted_unshift:
  assumes "length xs = length Bs" "set xs \<subseteq> {..<k}"
  shows "shifted k \<sigma> Bs (unshift k \<sigma> Bs xs) = xs"
proof (rule nth_equalityI)
  show "length (shifted k \<sigma> Bs (unshift k \<sigma> Bs xs)) = length xs"
    using assms by (simp add: shifted_def unshift_def)
next
  fix i assume i: "i < length (shifted k \<sigma> Bs (unshift k \<sigma> Bs xs))"
  then have il: "i < length xs" "i < length Bs"
    using assms by (simp_all add: shifted_def unshift_def)
  have "xs ! i \<in> set xs" using il(1) by (rule nth_mem)
  then have x: "xs ! i < k" using assms(2) by auto
  have "shifted k \<sigma> Bs (unshift k \<sigma> Bs xs) ! i
      = (cnt \<sigma> (Bs ! i) + (xs ! i + k - cnt \<sigma> (Bs ! i) mod k) mod k) mod k"
    using il assms by (simp add: shifted_def unshift_def)
  also have "\<dots> = xs ! i" using x by (rule mod_unshift)
  finally show "shifted k \<sigma> Bs (unshift k \<sigma> Bs xs) ! i = xs ! i" .
qed

lemma unshift_in_shifts:
  assumes "length xs = k" "length Bs = k" "k > 0"
  shows "unshift k \<sigma> Bs xs \<in> shifts k"
  using assms by (auto simp: shifts_def unshift_def)

theorem card_accepting_shifts:
  assumes "length Bs = k" "k > 0"
  shows "fact k \<le> card {ss \<in> shifts k. passes k \<sigma> Bs ss}"
proof -
  let ?G = "{ss \<in> shifts k. passes k \<sigma> Bs ss}"
  have inj: "inj_on (unshift k \<sigma> Bs) (arrangements k)"
  proof (rule inj_onI)
    fix xs ys assume xs: "xs \<in> arrangements k" and ys: "ys \<in> arrangements k"
      and eq: "unshift k \<sigma> Bs xs = unshift k \<sigma> Bs ys"
    have "xs = shifted k \<sigma> Bs (unshift k \<sigma> Bs xs)"
      using xs assms by (simp add: arrangements_def shifted_unshift)
    also have "\<dots> = shifted k \<sigma> Bs (unshift k \<sigma> Bs ys)" using eq by simp
    also have "\<dots> = ys"
      using ys assms by (simp add: arrangements_def shifted_unshift)
    finally show "xs = ys" .
  qed
  have sub: "unshift k \<sigma> Bs ` arrangements k \<subseteq> ?G"
  proof
    fix ss assume "ss \<in> unshift k \<sigma> Bs ` arrangements k"
    then obtain xs where xs: "xs \<in> arrangements k" and ss: "ss = unshift k \<sigma> Bs xs" by blast
    have "ss \<in> shifts k" using xs assms ss by (simp add: arrangements_def unshift_in_shifts)
    moreover have "shifted k \<sigma> Bs ss = xs"
      using xs assms ss by (simp add: arrangements_def shifted_unshift)
    then have "passes k \<sigma> Bs ss" using xs by (simp add: passes_def arrangements_def)
    ultimately show "ss \<in> ?G" by simp
  qed
  have fin: "finite ?G" using finite_shifts by simp
  have "fact k = card (arrangements k)" by (simp add: card_arrangements)
  also have "\<dots> = card (unshift k \<sigma> Bs ` arrangements k)" using inj by (simp add: card_image)
  also have "\<dots> \<le> card ?G" using fin sub by (rule card_mono)
  finally show ?thesis .
qed

section \<open>\<open>k\<^sup>k \<le> 3\<^sup>k \<cdot> k!\<close>: the acceptance probability \<open>k!/k\<^sup>k\<close> is \<open>2\<^sup>-\<^sup>O\<^sup>(\<^sup>k\<^sup>)\<close>\<close>

text \<open>The paper uses \<open>k!/k\<^sup>k\<^sup>-\<^sup>1 \<ge> e\<^sup>-\<^sup>k\<close>; we use the integer form with base 3 \<open>> e\<close>.\<close>

lemma pow_le_3pow_fact: "k ^ k \<le> 3 ^ k * fact k"
proof (induction k)
  case (Suc k)
  show ?case
  proof (cases "k = 0")
    case False
    have r: "(1 + 1 / real k) ^ k \<le> exp 1"
      by (rule exp_ge_one_plus_x_over_n_power_n) (use False in auto)
    have e3: "exp (1::real) \<le> 3"
      using exp_le by simp
    have "real (Suc k) ^ k = real k ^ k * (1 + 1 / real k) ^ k"
      using False by (simp add: field_simps flip: power_mult_distrib)
    also have "\<dots> \<le> real k ^ k * 3"
      using r e3 by (intro mult_left_mono) simp_all
    finally have a: "real (Suc k) ^ k \<le> 3 * real k ^ k" by simp
    have "real (Suc k ^ Suc k) = real (Suc k) * real (Suc k) ^ k"
      by (simp only: power_Suc of_nat_mult of_nat_power)
    also have "\<dots> \<le> real (Suc k) * (3 * real k ^ k)"
      using a by (intro mult_left_mono) simp_all
    also have "\<dots> \<le> real (Suc k) * (3 * (3 ^ k * fact k))"
    proof -
      have "real (k ^ k) \<le> real (3 ^ k * fact k)" using Suc.IH by (simp only: of_nat_le_iff)
      then have ih: "real k ^ k \<le> 3 ^ k * fact k" by simp
      show ?thesis using ih by (intro mult_left_mono) simp_all
    qed
    also have "\<dots> = real (3 ^ Suc k * fact (Suc k))" by (simp add: algebra_simps)
    finally show ?thesis by (simp only: of_nat_le_iff)
  qed simp
qed simp

end
