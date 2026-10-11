theory Monotone_3CNF
  imports Complex_Main
begin

section \<open>Monotone 3-CNFs with no small transversal\<close>

text \<open>
  Gurumukhani, Kleber, Paturi, Rosin, Saks and Talebanfard (arXiv:2601.04072): a monotone
  3-CNF on \<open>n = 3t - s\<close> variables with no transversal of size below \<open>t\<close> has at most
  \<open>c (2/3)\<^bsup>s/2\<^esup> 3\<^sup>t\<close> transversals of size \<open>t\<close>.

  A CNF over the finite variable set \<open>V\<close> is a set of clauses, each a subset of \<open>V\<close> of size at
  most 3.  A transversal is a set of variables meeting every clause.  Setting the variables
  of \<open>J\<close> to 1 and those of \<open>E\<close> to 0 gives the restricted CNF \<open>restr F J E\<close> over
  \<open>V - J - E\<close>.\<close>

definition cnf :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "cnf V F \<longleftrightarrow> finite V \<and> (\<forall>C\<in>F. C \<subseteq> V \<and> card C \<le> 3)"

definition hits :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "hits F X \<longleftrightarrow> (\<forall>C\<in>F. C \<inter> X \<noteq> {})"

definition trans :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "trans V F t = {X. X \<subseteq> V \<and> hits F X \<and> card X = t}"

definition thr :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "thr V F t \<longleftrightarrow> (\<forall>X. X \<subseteq> V \<longrightarrow> hits F X \<longrightarrow> t \<le> card X)"

definition restr :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "restr F J E = (\<lambda>C. C - E) ` {C\<in>F. C \<inter> J = {}}"

lemma cnf_finite: "cnf V F \<Longrightarrow> finite F"
  by (rule finite_subset[of _ "Pow V"]) (auto simp: cnf_def)

lemma cnf_sub: "cnf V F \<Longrightarrow> C \<in> F \<Longrightarrow> C \<subseteq> V"
  by (simp add: cnf_def)

lemma cnf_clause_finite: "cnf V F \<Longrightarrow> C \<in> F \<Longrightarrow> finite C"
  using finite_subset[of C V] by (simp add: cnf_def)

lemma thrD: "thr V F t \<Longrightarrow> X \<subseteq> V \<Longrightarrow> hits F X \<Longrightarrow> t \<le> card X"
  by (simp add: thr_def)

lemma restr_mem:"C \<in> F \<Longrightarrow> C \<inter> J = {} \<Longrightarrow> C - E \<in> restr F J E"
  unfolding restr_def by blast

lemma restr_cnf:
  assumes "cnf V F"
  shows "cnf (V - J - E) (restr F J E)"
proof -
  have "C - E \<subseteq> V - J - E \<and> card (C - E) \<le> 3" if "C \<in> F" "C \<inter> J = {}" for C
  proof -
    have "card (C - E) \<le> card C"
      using cnf_clause_finite[OF assms that(1)] by (simp add: card_mono)
    then show ?thesis using assms that unfolding cnf_def by auto
  qed
  then show ?thesis using assms unfolding cnf_def restr_def by auto
qed

lemma restr_thr:
  assumes F: "cnf V F" and t: "thr V F t" and J: "J \<subseteq> V"
  shows "thr (V - J - E) (restr F J E) (t - card J)"
  unfolding thr_def
proof (intro allI impI)
  fix Y assume Y: "Y \<subseteq> V - J - E" and h: "hits (restr F J E) Y"
  have hY: "hits F (Y \<union> J)"
    unfolding hits_def
  proof
    fix C assume C: "C \<in> F"
    show "C \<inter> (Y \<union> J) \<noteq> {}"
    proof (cases "C \<inter> J = {}")
      case True
      have "C - E \<in> restr F J E" using restr_mem[OF C True] .
      then have "(C - E) \<inter> Y \<noteq> {}" using h unfolding hits_def by blast
      then show ?thesis by blast
    next
      case False
      then show ?thesis by blast
    qed
  qed
  have "finite V" using F by (simp add: cnf_def)
  have YJ: "Y \<union> J \<subseteq> V" using Y J by blast
  have "t \<le> card (Y \<union> J)" using thrD[OF t YJ hY] .
  also have "card (Y \<union> J) = card Y + card J"
  proof (rule card_Un_disjoint)
    show "finite Y" using finite_subset[of Y V] Y \<open>finite V\<close> by blast
    show "finite J" using \<open>finite V\<close> J by (rule finite_subset[rotated])
    show "Y \<inter> J = {}" using Y by blast
  qed
  finally show "t - card J \<le> card Y" by simp
qed

lemma row_card:
  assumes V: "finite V" and J: "J \<subseteq> V"
  shows "card {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}}
    \<le> card (trans (V - J - E) (restr F J E) (t - card J))"
proof (rule card_inj_on_le[where f = "\<lambda>X. X - J"])
  show "inj_on (\<lambda>X. X - J) {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}}"
    by (rule inj_onI) blast
  show "finite (trans (V - J - E) (restr F J E) (t - card J))"
    by (rule finite_subset[of _ "Pow V"]) (use V in \<open>auto simp: trans_def\<close>)
  show "(\<lambda>X. X - J) ` {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}}
    \<subseteq> trans (V - J - E) (restr F J E) (t - card J)"
  proof
    fix Y assume "Y \<in> (\<lambda>X. X - J) ` {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}}"
    then obtain X where X: "X \<subseteq> V" "hits F X" "card X = t" "J \<subseteq> X" "X \<inter> E = {}"
      and Y: "Y = X - J" by (auto simp: trans_def)
    have "hits (restr F J E) Y"
      unfolding hits_def restr_def using X(2,5) Y unfolding hits_def by blast
    moreover have "card Y = t - card J"
      using X Y finite_subset[OF J V] by (simp add: card_Diff_subset)
    ultimately show "Y \<in> trans (V - J - E) (restr F J E) (t - card J)"
      using X Y unfolding trans_def by blast
  qed
qed

lemma row_empty:
  assumes V: "finite V" and "t < card J"
  shows "{X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}} = {}"
proof (rule equals0I)
  fix X assume "X \<in> {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}}"
  then have X: "X \<subseteq> V" "J \<subseteq> X" "card X = t" by (auto simp: trans_def)
  have "card J \<le> card X" using card_mono[OF finite_subset[OF X(1) V] X(2)] .
  then show False using X(3) assms(2) by simp
qed

text \<open>
  Clauses deleted in a restriction cannot create new co-occurrences: the clauses of
  \<open>restr F J E\<close> containing \<open>x\<close> and \<open>y\<close> are images of clauses of \<open>F\<close> containing them.\<close>

definition twos :: "'a set set \<Rightarrow> 'a set set" where
  "twos F = {C\<in>F. card C = 2}"

definition npair :: "'a set set \<Rightarrow> bool" where
  "npair F \<longleftrightarrow> (\<forall>x y. x \<noteq> y \<longrightarrow> card {C\<in>F. x \<in> C \<and> y \<in> C} \<le> 2)"

lemma npair_restr:
  assumes F: "finite F" and np: "npair F"
  shows "npair (restr F J E)"
  unfolding npair_def
proof (intro allI impI)
  fix x y :: 'a assume xy: "x \<noteq> y"
  have "{C\<in>restr F J E. x \<in> C \<and> y \<in> C} \<subseteq> (\<lambda>C. C - E) ` {C\<in>F. x \<in> C \<and> y \<in> C}"
    unfolding restr_def by blast
  then have "card {C\<in>restr F J E. x \<in> C \<and> y \<in> C} \<le> card ((\<lambda>C. C - E) ` {C\<in>F. x \<in> C \<and> y \<in> C})"
    using F by (intro card_mono) auto
  also have "\<dots> \<le> card {C\<in>F. x \<in> C \<and> y \<in> C}"
    by (rule card_image_le) (use F in simp)
  also have "\<dots> \<le> 2" using np xy unfolding npair_def by blast
  finally show "card {C\<in>restr F J E. x \<in> C \<and> y \<in> C} \<le> 2" .
qed

subsection \<open>The families and their bounds\<close>

text \<open>
  Family 0 is every CNF; 1 has a 2-clause; 2o two 2-clauses meeting in one variable; 2d two
  disjoint 2-clauses; 3 at least three 2-clauses, no three with a common variable; 4 at
  least four 2-clauses.  For 2o, 2d, 3 and 4 no pair of variables lies in three clauses.\<close>

datatype fam = T0 | T1 | T2o | T2d | T3 | T4

fun infam :: "fam \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "infam T0 F = True"
| "infam T1 F = (twos F \<noteq> {})"
| "infam T2o F = ((\<exists>C\<in>twos F. \<exists>D\<in>twos F. C \<noteq> D \<and> C \<inter> D \<noteq> {}) \<and> npair F)"
| "infam T2d F = ((\<exists>C\<in>twos F. \<exists>D\<in>twos F. C \<inter> D = {}) \<and> npair F)"
| "infam T3 F = (3 \<le> card (twos F) \<and> (\<forall>x. card {C\<in>twos F. x \<in> C} \<le> 2) \<and> npair F)"
| "infam T4 F = (4 \<le> card (twos F) \<and> npair F)"

fun coef :: "fam \<Rightarrow> bool \<Rightarrow> real" where
  "coef T0 p = (if p then 1 else 7/9)"
| "coef T1 p = (if p then 5/6 else 2/3)"
| "coef T2o p = (if p then 2/3 else 5/9)"
| "coef T2d p = (if p then 25/36 else 5/9)"
| "coef T3 p = (if p then 7/12 else 1/2)"
| "coef T4 p = (if p then 7/12 else 17/36)"

text \<open>\<open>bound i s t\<close> is \<open>c (2/3)\<^bsup>s/2\<^esup> 3\<^sup>t\<close> for even \<open>s\<close> and \<open>c' (2/3)\<^bsup>(s-1)/2\<^esup> 3\<^sup>t\<close> for odd \<open>s\<close>.\<close>

definition bound :: "fam \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> real" where
  "bound i s t = coef i (even s) * (2/3) powi (s div 2) * 3 ^ t"

lemma coef_pos: "0 < coef i p"
  by (cases i) auto

lemma bound_pos: "0 < bound i s t"
  unfolding bound_def using coef_pos[of i "even s"] by simp

text \<open>
  The ratio of the bound for a row that sets \<open>j\<close> variables to 1 and \<open>e\<close> to 0, with
  restricted family \<open>k\<close>, to the bound for family \<open>i\<close>; \<open>p\<close> is the parity of \<open>s\<close>.\<close>

definition ratio :: "fam \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> fam \<Rightarrow> bool \<Rightarrow> real" where
  "ratio k j e i p = coef k (p = even e) / coef i p
     * (2/3) powi ((int e - 2 * int j + (if p then 0 else 1)) div 2) / 3 ^ j"

lemma ratio_nonneg: "0 \<le> ratio k j e i p"
  unfolding ratio_def using coef_pos[of k "p = even e"] coef_pos[of i p]
  by (intro divide_nonneg_pos mult_nonneg_nonneg) auto

lemma div_shift:
  fixes s d :: int
  shows "(s + d) div 2 = s div 2 + (d + (if even s then 0 else 1)) div 2"
  by (cases "even s") presburger+

lemma bound_shift:
  assumes "j \<le> t"
  shows "bound k (s - 2 * int j + int e) (t - j) = ratio k j e i (even s) * bound i s t"
proof -
  have par: "even (s - 2 * int j + int e) = (even s = even e)" by simp
  have dv: "(s - 2 * int j + int e) div 2
      = s div 2 + (int e - 2 * int j + (if even s then 0 else 1)) div 2"
    using div_shift[of s "int e - 2 * int j"] by (simp add: algebra_simps)
  have p3: "(3::real) ^ (t - j) = 3 ^ t / 3 ^ j" using assms by (simp add: power_diff)
  show ?thesis
    unfolding bound_def ratio_def par dv p3 power_int_add
    using coef_pos[of i "even s"] by (simp add: field_simps power_int_add)
qed

lemma ratio_same: "ratio i 0 1 i p \<le> 1"
  by (cases i; cases p) (simp_all add: ratio_def)

lemma bound_step: "bound i (s + 1) t \<le> bound i s t"
proof -
  have "bound i (s - 2 * int 0 + int 1) (t - 0) = ratio i 0 1 i (even s) * bound i s t"
    by (rule bound_shift) simp
  then have "bound i (s + 1) t = ratio i 0 1 i (even s) * bound i s t" by simp
  also have "\<dots> \<le> bound i s t"
    using ratio_same[of i "even s"] bound_pos[of i s t] by (simp add: mult_left_le_one_le)
  finally show ?thesis .
qed

lemma bound_mono:
  assumes "s \<le> s'"
  shows "bound i s' t \<le> bound i s t"
proof -
  have "bound i (s + int m) t \<le> bound i s t" for m
  proof (induction m)
    case (Suc m)
    have "bound i (s + int (Suc m)) t = bound i ((s + int m) + 1) t" by (simp add: algebra_simps)
    also have "\<dots> \<le> bound i (s + int m) t" by (rule bound_step)
    finally show ?case using Suc by linarith
  qed simp
  from this[of "nat (s' - s)"] show ?thesis using assms by simp
qed

subsection \<open>The induction framework\<close>

text \<open>
  The induction is on the number of variables: every row of every table sets at least one
  variable, so the restricted CNF has fewer.  A CNF with a clause of size at most 1 obeys
  every bound (forcing the variable gives at most half of \<open>bound T0\<close>), so the statement
  allows it in every family.\<close>

definition IH :: "nat \<Rightarrow> bool" where
  "IH m \<longleftrightarrow> (\<forall>(V::nat set) F t i. card V < m \<longrightarrow> cnf V F \<longrightarrow> thr V F t \<longrightarrow>
     (infam i F \<or> (\<exists>C\<in>F. card C \<le> 1)) \<longrightarrow>
     real (card (trans V F t)) \<le> bound i (3 * int t - int (card V)) t)"

text \<open>
  The normalized situation: every clause has two or three variables, no clause contains
  another, every variable occurs, and the bound holds for fewer variables.\<close>

locale core =
  fixes V :: "nat set" and F :: "nat set set" and t :: nat
  assumes cnf: "cnf V F" and thr: "thr V F t" and ih: "IH (card V)"
    and sizes: "\<And>C. C \<in> F \<Longrightarrow> card C = 2 \<or> card C = 3"
    and anti: "\<And>C D. C \<in> F \<Longrightarrow> D \<in> F \<Longrightarrow> C \<subseteq> D \<Longrightarrow> C = D"
    and onto: "\<Union>F = V"
begin

abbreviation s :: int where "s \<equiv> 3 * int t - int (card V)"

lemma finV: "finite V"
  using cnf by (simp add: cnf_def)

lemma finF: "finite F"
  using cnf by (rule cnf_finite)

lemma sub: "C \<in> F \<Longrightarrow> C \<subseteq> V"
  using cnf by (rule cnf_sub)

lemma critical:
  assumes X: "X \<in> trans V F t" and x: "x \<in> X"
  shows "\<exists>C\<in>F. C \<inter> X = {x}"
proof (rule ccontr)
  assume no: "\<not> (\<exists>C\<in>F. C \<inter> X = {x})"
  have XV: "X \<subseteq> V" "hits F X" "card X = t" using X by (auto simp: trans_def)
  have "hits F (X - {x})"
    unfolding hits_def
  proof
    fix C assume C: "C \<in> F"
    have "C \<inter> X \<noteq> {}" "C \<inter> X \<noteq> {x}" using XV(2) C no unfolding hits_def by auto
    then show "C \<inter> (X - {x}) \<noteq> {}" by blast
  qed
  then have "t \<le> card (X - {x})" using thrD[OF thr, of "X - {x}"] XV(1) by blast
  moreover have "finite X" using XV(1) finV by (rule finite_subset)
  moreover have "0 < t" using \<open>finite X\<close> x XV(3) card_gt_0_iff by blast
  ultimately show False using XV(3) x by simp
qed

lemma row:
  assumes J: "J \<subseteq> V" and E: "E \<subseteq> V" and JE: "J \<inter> E = {}" "J \<union> E \<noteq> {}"
    and k: "infam k (restr F J E) \<or> (\<exists>C\<in>restr F J E. card C \<le> 1)"
  shows "real (card {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}})
    \<le> ratio k (card J) (card E) i (even s) * bound i s t"
proof (cases "card J \<le> t")
  case True
  have fJ: "finite J" "finite E" using finite_subset[OF J finV] finite_subset[OF E finV] .
  have cU: "card (J \<union> E) = card J + card E" using fJ JE(1) by (rule card_Un_disjoint)
  have VJE: "V - J - E = V - (J \<union> E)" by blast
  have cV: "card (V - J - E) = card V - card J - card E"
    unfolding VJE using card_Diff_subset[of "J \<union> E" V] fJ J E cU by simp
  have le: "card J + card E \<le> card V"
    using J E finV cU by (metis card_mono le_sup_iff)
  have lt: "card (V - J - E) < card V"
    unfolding VJE using J E JE(2) finV by (intro psubset_card_mono) auto
  have "real (card {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}})
      \<le> real (card (trans (V - J - E) (restr F J E) (t - card J)))"
    using row_card[OF finV J] by simp
  also have "\<dots> \<le> bound k (3 * int (t - card J) - int (card (V - J - E))) (t - card J)"
    using ih lt restr_cnf[OF cnf] restr_thr[OF cnf thr J] k unfolding IH_def by blast
  also have "3 * int (t - card J) - int (card (V - J - E)) = s - 2 * int (card J) + int (card E)"
    using cV le True by simp
  also have "bound k (s - 2 * int (card J) + int (card E)) (t - card J)
      = ratio k (card J) (card E) i (even s) * bound i s t"
    using True by (rule bound_shift)
  finally show ?thesis .
next
  case False
  have e: "{X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}} = {}"
    by (rule row_empty[OF finV]) (use False in simp)
  show ?thesis
    unfolding e using mult_nonneg_nonneg[OF ratio_nonneg less_imp_le[OF bound_pos]] by simp
qed

definition rows_ok :: "(nat set \<times> nat set \<times> fam) list \<Rightarrow> bool" where
  "rows_ok rs \<longleftrightarrow> (\<forall>(J,E,k)\<in>set rs. J \<subseteq> V \<and> E \<subseteq> V \<and> J \<inter> E = {} \<and> J \<union> E \<noteq> {}
     \<and> (infam k (restr F J E) \<or> (\<exists>C\<in>restr F J E. card C \<le> 1)))"

lemma table_sum:
  assumes ok: "rows_ok rs" and S: "S \<subseteq> trans V F t"
    and cov: "\<forall>X\<in>S. \<exists>(J,E,k)\<in>set rs. J \<subseteq> X \<and> X \<inter> E = {}"
  shows "real (card S) \<le> (\<Sum>(J,E,k)\<leftarrow>rs. ratio k (card J) (card E) i (even s)) * bound i s t"
  using ok S cov
proof (induction rs arbitrary: S)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  obtain J E k where r: "r = (J, E, k)" by (cases r) auto
  let ?S1 = "{X\<in>S. J \<subseteq> X \<and> X \<inter> E = {}}"
  let ?S2 = "S - ?S1"
  have fin: "finite (trans V F t)"
    by (rule finite_subset[of _ "Pow V"]) (use finV in \<open>auto simp: trans_def\<close>)
  have okr: "J \<subseteq> V" "E \<subseteq> V" "J \<inter> E = {}" "J \<union> E \<noteq> {}"
      "infam k (restr F J E) \<or> (\<exists>C\<in>restr F J E. card C \<le> 1)"
    using Cons.prems(1) r unfolding rows_ok_def by auto
  have "S = ?S1 \<union> ?S2" by blast
  then have "card S \<le> card ?S1 + card ?S2"
    using card_Un_le[of ?S1 ?S2] by simp
  moreover have "card ?S1 \<le> card {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}}"
    using Cons.prems(2) fin by (intro card_mono) auto
  moreover have "real (card {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}})
      \<le> ratio k (card J) (card E) i (even s) * bound i s t"
    using row[OF okr] .
  moreover have "real (card ?S2) \<le> (\<Sum>(J,E,k)\<leftarrow>rs. ratio k (card J) (card E) i (even s)) * bound i s t"
    using Cons.prems Cons.IH[of ?S2] r unfolding rows_ok_def by fastforce
  ultimately show ?case using r by (simp add: algebra_simps)
qed

lemma table:
  assumes ok: "rows_ok rs"
    and cov: "\<forall>X\<in>trans V F t. \<exists>(J,E,k)\<in>set rs. J \<subseteq> X \<and> X \<inter> E = {}"
    and sum: "(\<Sum>(J,E,k)\<leftarrow>rs. ratio k (card J) (card E) i (even s)) \<le> 1"
  shows "real (card (trans V F t)) \<le> bound i s t"
proof -
  have "real (card (trans V F t))
      \<le> (\<Sum>(J,E,k)\<leftarrow>rs. ratio k (card J) (card E) i (even s)) * bound i s t"
    using table_sum[OF ok order_refl cov] .
  also have "\<dots> \<le> bound i s t"
    using sum bound_pos[of i s t] by (simp add: mult_left_le_one_le)
  finally show ?thesis .
qed

end

subsection \<open>Monotone 3-CNFs with no 2-clause\<close>

locale core0 = core +
  assumes three: "\<And>C. C \<in> F \<Longrightarrow> card C = 3"
begin

lemma hit3:
  assumes "X \<in> trans V F t" "{a,b,c} \<in> F" "a \<notin> X" "b \<notin> X"
  shows "c \<in> X"
proof -
  have "hits F X" using assms(1) by (simp add: trans_def)
  then have "{a,b,c} \<inter> X \<noteq> {}" using assms(2) unfolding hits_def by blast
  then show ?thesis using assms(3,4) by auto
qed

text \<open>\<open>\<P>(0,1)\<close>: a pair \<open>{a,b}\<close> in three clauses.  If \<open>a\<close> always occurs with \<open>b\<close>, setting \<open>a\<close>
  to 1 forces \<open>b\<close> to 0, since otherwise \<open>a\<close> has no critical clause.\<close>

lemma p01_with:
  assumes C: "{a,b,c} \<in> F" "{a,b,d} \<in> F" "{a,b,e} \<in> F" and dist: "distinct [a,b,c,d,e]"
    and aw: "\<And>C. C \<in> F \<Longrightarrow> a \<in> C \<Longrightarrow> b \<in> C"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof (rule table[where rs = "[({a},{b},T0), ({b},{a},T0), ({c,d,e},{a,b},T0)]"])
  show "rows_ok [({a},{b},T0), ({b},{a},T0), ({c,d,e},{a,b},T0)]"
    using sub[OF C(1)] sub[OF C(2)] sub[OF C(3)] dist unfolding rows_ok_def by auto
  show "\<forall>X\<in>trans V F t. \<exists>(J,E,k)\<in>set [({a},{b},T0), ({b},{a},T0), ({c,d,e},{a,b},T0)].
      J \<subseteq> X \<and> X \<inter> E = {}"
  proof
    fix X assume X: "X \<in> trans V F t"
    show "\<exists>(J,E,k)\<in>set [({a},{b},T0), ({b},{a},T0), ({c,d,e},{a,b},T0)]. J \<subseteq> X \<and> X \<inter> E = {}"
    proof (cases "a \<in> X")
      case True
      have "b \<notin> X"
      proof
        assume b: "b \<in> X"
        obtain D where D: "D \<in> F" "D \<inter> X = {a}" using critical[OF X True] by blast
        then have "b \<in> D \<inter> X" using aw b by blast
        then show False using D dist by auto
      qed
      then show ?thesis using True by auto
    next
      case na: False
      show ?thesis
      proof (cases "b \<in> X")
        case True
        then show ?thesis using na by auto
      next
        case False
        have "c \<in> X" "d \<in> X" "e \<in> X" using hit3[OF X _ na False] C by auto
        then show ?thesis using na False by auto
      qed
    qed
  qed
  show "(\<Sum>(J,E,k)\<leftarrow>[({a},{b},T0), ({b},{a},T0), ({c,d,e},{a,b},T0)].
      ratio k (card J) (card E) T0 (even s)) \<le> 1"
    using dist by (cases "even s") (simp_all add: ratio_def power_int_minus inverse_eq_divide power_divide)
qed

end

end
