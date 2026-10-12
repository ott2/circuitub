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
      unfolding hits_def
    proof
      fix C' assume "C' \<in> restr F J E"
      then obtain C where C: "C \<in> F" "C \<inter> J = {}" "C' = C - E" by (auto simp: restr_def)
      then obtain x where "x \<in> C" "x \<in> X" using X(2) unfolding hits_def by blast
      then show "C' \<inter> Y \<noteq> {}" using C X(5) Y by blast
    qed
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

lemmas ratio_simps = ratio_def power_int_minus inverse_eq_divide power_divide

lemma single_out: "C \<inter> X = {x} \<Longrightarrow> y \<in> C \<Longrightarrow> y \<noteq> x \<Longrightarrow> y \<notin> X"
  by blast

lemma excl3: "{x,y,z} \<inter> X = {x} \<Longrightarrow> y \<noteq> x \<Longrightarrow> z \<noteq> x \<Longrightarrow> y \<notin> X \<and> z \<notin> X"
  by blast

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

text \<open>Domination between families: \<open>fam_le k' k\<close> if the bound for \<open>k'\<close> is at most that for \<open>k\<close>.
  The families form a chain \<open>T4 \<le> T3 \<le> T2o \<le> T2d \<le> T1 \<le> T0\<close>.\<close>

definition fam_le :: "fam \<Rightarrow> fam \<Rightarrow> bool" where
  "fam_le k' k \<longleftrightarrow> (\<forall>p. coef k' p \<le> coef k p)"

lemma fam_leI:
  assumes "coef k' True \<le> coef k True" "coef k' False \<le> coef k False"
  shows "fam_le k' k"
  unfolding fam_le_def
proof
  fix p show "coef k' p \<le> coef k p" using assms by (cases p) auto
qed

lemma fam_le_refl: "fam_le k k"
  by (simp add: fam_le_def)

lemma fam_le_2o_2d: "fam_le T2o T2d"
  by (rule fam_leI) simp_all

lemma fam_le_4_3: "fam_le T4 T3"
  by (rule fam_leI) simp_all

lemma bound_le:
  assumes "fam_le k' k"
  shows "bound k' s t \<le> bound k s t"
proof -
  have "coef k' (even s) \<le> coef k (even s)" using assms unfolding fam_le_def by blast
  then show ?thesis unfolding bound_def by (intro mult_right_mono) (auto intro: less_imp_le)
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

text \<open>A row may use family \<open>k\<close> if the restriction is in \<open>k\<close>, has a clause of size at most 1, or
  is in a family dominated by \<open>k\<close>.\<close>

abbreviation fam_ok :: "fam \<Rightarrow> nat set set \<Rightarrow> bool" where
  "fam_ok k G \<equiv> infam k G \<or> (\<exists>C\<in>G. card C \<le> 1) \<or> (\<exists>k'. fam_le k' k \<and> infam k' G)"

lemma ih_fam:
  fixes W :: "nat set"
  assumes ih: "IH m" and lt: "card W < m" and c: "cnf W G" and th: "thr W G t'"
    and k: "fam_ok k G"
  shows "real (card (trans W G t')) \<le> bound k (3 * int t' - int (card W)) t'"
proof -
  have base: "real (card (trans W G t')) \<le> bound j (3 * int t' - int (card W)) t'"
    if "infam j G \<or> (\<exists>C\<in>G. card C \<le> 1)" for j
    using ih lt c th that unfolding IH_def by blast
  show ?thesis using k
  proof (elim disjE)
    assume "infam k G" then show ?thesis using base by blast
  next
    assume "\<exists>C\<in>G. card C \<le> 1" then show ?thesis using base by blast
  next
    assume "\<exists>k'. fam_le k' k \<and> infam k' G"
    then obtain k' where k': "fam_le k' k" "infam k' G" by blast
    show ?thesis
      using base[of k'] k'(2) bound_le[OF k'(1), of "3 * int t' - int (card W)" t'] by linarith
  qed
qed

text \<open>
  The normalized situation: every clause has two or three variables, no clause contains
  another, every variable occurs, and the bound holds for fewer variables.\<close>

locale core =
  fixes V :: "nat set" and F :: "nat set set" and t :: nat
  assumes cnf: "cnf V F" and thr: "thr V F t" and ih: "IH (card V)"
    and sizes: "\<And>C. C \<in> F \<Longrightarrow> card C = 2 \<or> card C = 3"
    and anti: "\<And>C D. C \<in> F \<Longrightarrow> D \<in> F \<Longrightarrow> C \<subseteq> D \<Longrightarrow> C = D"
    and onto: "\<Union>F = V" and t1: "1 \<le> t"
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
    and k: "fam_ok k (restr F J E)"
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
    by (rule ih_fam[OF ih lt restr_cnf[OF cnf] restr_thr[OF cnf thr J] k])
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
     \<and> fam_ok k (restr F J E))"

lemma table_sum:
  assumes ok: "rows_ok rs" and S: "S \<subseteq> trans V F t"
    and cov: "\<forall>X\<in>S. \<exists>r\<in>set rs. fst r \<subseteq> X \<and> X \<inter> fst (snd r) = {}"
  shows "real (card S) \<le> (\<Sum>(J,E,k)\<leftarrow>rs. ratio k (card J) (card E) i (even s)) * bound i s t"
  using ok S cov
proof (induction rs arbitrary: S)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  obtain J E k where r: "r = (J, E, k)" by (cases r) auto
  let ?S1 = "{X\<in>S. J \<subseteq> X \<and> X \<inter> E = {}}"
  let ?S2 = "{X\<in>S. \<exists>r\<in>set rs. fst r \<subseteq> X \<and> X \<inter> fst (snd r) = {}}"
  have fin: "finite (trans V F t)"
    by (rule finite_subset[of _ "Pow V"]) (use finV in \<open>auto simp: trans_def\<close>)
  have okr: "J \<subseteq> V" "E \<subseteq> V" "J \<inter> E = {}" "J \<union> E \<noteq> {}"
      "fam_ok k (restr F J E)"
    using Cons.prems(1) r unfolding rows_ok_def by auto
  have ok2: "rows_ok rs" using Cons.prems(1) unfolding rows_ok_def by simp
  have cov2: "\<forall>X\<in>?S2. \<exists>r\<in>set rs. fst r \<subseteq> X \<and> X \<inter> fst (snd r) = {}" by blast
  have S2: "?S2 \<subseteq> trans V F t" using Cons.prems(2) by blast
  have cS: "S \<subseteq> ?S1 \<union> ?S2" using Cons.prems(3) r by auto
  have "?S1 \<union> ?S2 \<subseteq> trans V F t" using Cons.prems(2) by blast
  then have "finite (?S1 \<union> ?S2)" using fin by (rule finite_subset)
  then have "card S \<le> card (?S1 \<union> ?S2)" using cS by (rule card_mono)
  then have "card S \<le> card ?S1 + card ?S2"
    using card_Un_le[of ?S1 ?S2] by simp
  moreover have "card ?S1 \<le> card {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}}"
    using Cons.prems(2) fin by (intro card_mono) auto
  moreover have "real (card {X\<in>trans V F t. J \<subseteq> X \<and> X \<inter> E = {}})
      \<le> ratio k (card J) (card E) i (even s) * bound i s t"
    using row[OF okr] .
  moreover have "real (card ?S2) \<le> (\<Sum>(J,E,k)\<leftarrow>rs. ratio k (card J) (card E) i (even s)) * bound i s t"
    using Cons.IH[OF ok2 S2 cov2] .
  ultimately show ?case using r by (simp add: algebra_simps)
qed

lemma table:
  assumes ok: "rows_ok rs"
    and cov: "\<forall>X\<in>trans V F t. \<exists>r\<in>set rs. fst r \<subseteq> X \<and> X \<inter> fst (snd r) = {}"
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

text \<open>If every clause containing \<open>a\<close> also contains \<open>b\<close>, a transversal with \<open>a\<close> omits \<open>b\<close>:
  otherwise \<open>a\<close> would have no critical clause.\<close>

lemma forced_out:
  assumes X: "X \<in> trans V F t" and a: "a \<in> X" and ab: "a \<noteq> b"
    and aw: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> b \<in> D"
  shows "b \<notin> X"
proof
  assume b: "b \<in> X"
  obtain D where D: "D \<in> F" "D \<inter> X = {a}" using critical[OF X a] by blast
  then have "b \<in> D \<inter> X" using aw b by blast
  then show False using D ab by auto
qed

lemma hit:
  assumes "X \<in> trans V F t" "C \<in> F"
  shows "C \<inter> X \<noteq> {}"
proof -
  have "hits F X" using assms(1) by (simp add: trans_def)
  then show ?thesis using assms(2) unfolding hits_def by blast
qed

lemma restr_finite: "finite (restr F J E)"
  unfolding restr_def using finF by simp

lemma two_mem:
  assumes "C \<in> F" "C \<inter> J = {}" "C - E = {y,z}" "y \<noteq> z"
  shows "{y,z} \<in> twos (restr F J E)"
  using restr_mem[OF assms(1,2), of E] assms(3,4) by (simp add: twos_def)

lemma two_only:
  assumes deg: "card {C\<in>F. x \<in> C} \<le> 2" and C: "C1 \<in> F" "C2 \<in> F" "x \<in> C1" "x \<in> C2" "C1 \<noteq> C2"
    and D: "D \<in> F" "x \<in> D"
  shows "D = C1 \<or> D = C2"
proof (rule ccontr)
  assume "\<not> (D = C1 \<or> D = C2)"
  then have "C1 \<noteq> D" "C2 \<noteq> D" by auto
  then have "card {C1, C2, D} = 3" using C(5) by simp
  moreover have "card {C1, C2, D} \<le> card {C\<in>F. x \<in> C}"
    using C D finF by (intro card_mono) auto
  ultimately show False using deg by simp
qed

text \<open>If \<open>a \<in> X\<close> lies only in \<open>C1\<close> and \<open>C2\<close>, and \<open>C1\<close> has another variable of \<open>X\<close>, then \<open>C2\<close> is
  the critical clause of \<open>a\<close>.\<close>

lemma crit_other:
  assumes X: "X \<in> trans V F t" and a: "a \<in> X"
    and only: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = C1 \<or> D = C2"
    and y: "y \<in> C1" "y \<in> X" "y \<noteq> a"
  shows "C2 \<inter> X = {a}"
proof -
  obtain D where D: "D \<in> F" "D \<inter> X = {a}" using critical[OF X a] by blast
  have "D \<noteq> C1" using D(2) y by blast
  then show ?thesis using only[OF D(1)] D(2) by blast
qed

lemma crit_other':
  assumes X: "X \<in> trans V F t" and a: "a \<in> X"
    and only: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = C1 \<or> D = C2"
    and y: "y \<in> C2" "y \<in> X" "y \<noteq> a"
  shows "C1 \<inter> X = {a}"
  using crit_other[OF X a _ y, of C1] only by blast

lemma crit_excl:
  assumes X: "X \<in> trans V F t" and a: "a \<in> X"
    and only: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = C1 \<or> D = {a,u,v}"
    and y: "y \<in> C1" "y \<in> X" "y \<noteq> a" and uv: "u \<noteq> a" "v \<noteq> a"
  shows "u \<notin> X \<and> v \<notin> X"
  using crit_other[OF X a only y] uv by blast

lemma only_clause:
  assumes X: "X \<in> trans V F t" and a: "a \<in> X" and only: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = C"
  shows "C \<inter> X = {a}"
  using critical[OF X a] only by blast

subsection \<open>Type 1: a 2-clause \<open>{a,b}\<close>\<close>

text \<open>\<open>\<P>(1,1)\<close>: \<open>a\<close> lies only in \<open>{a,b}\<close>, so \<open>a = 1\<close> forces \<open>b = 0\<close> and \<open>a = 0\<close> forces \<open>b = 1\<close>.\<close>

lemma p11:
  assumes T: "{a,b} \<in> F" and ab: "a \<noteq> b" and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b}"
  shows "real (card (trans V F t)) \<le> bound T1 s t"
proof (rule table[where rs = "[({a},{b},T0), ({b},{a},T0)]"], goal_cases)
  case 1
  then show ?case using sub[OF T] ab unfolding rows_ok_def by auto
next
  case 2
  have "a \<in> X \<and> b \<notin> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
  proof (cases "a \<in> X")
    case True
    have "{a,b} \<inter> X = {a}" using only_clause[OF X True oa] .
    then have "b \<notin> X" using single_out[of "{a,b}" X a b] ab by simp
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis using hit[OF X T] by blast
  qed
  then show ?case by auto
next
  case 3
  then show ?case using ab by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>\<open>\<P>(1,2)\<close>: \<open>a\<close> lies in a further clause \<open>D\<close>, and \<open>b \<notin> D\<close> since no clause contains another.
  The paper writes \<open>D = {a,c,d}\<close>; \<open>D\<close> may also be a 2-clause \<open>{a,c}\<close>, and then \<open>a = 0\<close>, \<open>b = 1\<close>
  leaves the 1-clause \<open>{c}\<close>.  The table is tight: both sums are \<open>1\<close>.\<close>

lemma p12:
  assumes T: "{a,b} \<in> F" and ab: "a \<noteq> b" and D: "D \<in> F" "a \<in> D" "D \<noteq> {a,b}"
  shows "real (card (trans V F t)) \<le> bound T1 s t"
proof (rule table[where rs = "[({a},{},T0), ({b},{a},T1)]"], goal_cases)
  case 1
  have bD: "b \<notin> D"
  proof
    assume "b \<in> D"
    then have "{a,b} \<subseteq> D" using D(2) by blast
    then show False using anti[OF T D(1)] D(3) by blast
  qed
  have m: "D - {a} \<in> restr F {b} {a}" using restr_mem[OF D(1)] bD by blast
  have "card (D - {a}) = card D - 1" using cnf_clause_finite[OF cnf D(1)] D(2) by simp
  then have "card (D - {a}) = 2 \<or> card (D - {a}) \<le> 1" using sizes[OF D(1)] by auto
  then have "infam T1 (restr F {b} {a}) \<or> (\<exists>C\<in>restr F {b} {a}. card C \<le> 1)"
    using m by (auto simp: twos_def)
  then show ?case using sub[OF T] ab unfolding rows_ok_def by auto
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T] by blast
  then show ?case by auto
next
  case 3
  then show ?case by (cases "even s") (simp_all add: ratio_simps)
qed

theorem type1:
  assumes "infam T1 F"
  shows "real (card (trans V F t)) \<le> bound T1 s t"
proof -
  obtain C where C: "C \<in> F" "card C = 2" using assms by (auto simp: twos_def)
  then obtain a b where ab: "C = {a,b}" "a \<noteq> b" unfolding card_2_iff by blast
  have T: "{a,b} \<in> F" using C(1) ab(1) by simp
  show ?thesis
  proof (cases "\<forall>D\<in>F. a \<in> D \<longrightarrow> D = {a,b}")
    case True
    then show ?thesis using p11[OF T ab(2)] by blast
  next
    case na: False
    show ?thesis
    proof (cases "\<forall>D\<in>F. b \<in> D \<longrightarrow> D = {a,b}")
      case True
      have e: "{b,a} = {a,b}" by auto
      have T': "{b,a} \<in> F" using T unfolding e .
      have ob: "D = {b,a}" if "D \<in> F" "b \<in> D" for D using True that unfolding e by blast
      show ?thesis by (rule p11[OF T' ab(2)[symmetric] ob])
    next
      case False
      then obtain D where "D \<in> F" "b \<in> D" "D \<noteq> {a,b}" by blast
      then have "D \<in> F" "b \<in> D" "D \<noteq> {b,a}" by (auto simp: insert_commute)
      moreover have "{b,a} \<in> F" using T by (simp add: insert_commute)
      ultimately show ?thesis using p12[of b a D] ab(2) by blast
    qed
  qed
qed

end

lemma card3_obtain:
  assumes "3 \<le> card A"
  obtains x y z where "x \<in> A" "y \<in> A" "z \<in> A" "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"
proof -
  obtain B where B: "B \<subseteq> A" "card B = 3" using obtain_subset_with_card_n[OF assms] by blast
  then obtain x y z where "B = {x,y,z}" "x \<noteq> y" "y \<noteq> z" "x \<noteq> z"
    using card_3_iff[of B] by blast
  then show ?thesis using that B(1) by blast
qed

lemma card2_obtain:
  assumes "2 \<le> card A"
  obtains x y where "x \<in> A" "y \<in> A" "x \<noteq> y"
proof -
  obtain B where B: "B \<subseteq> A" "card B = 2" using obtain_subset_with_card_n[OF assms] by blast
  then obtain x y where "B = {x,y}" "x \<noteq> y" using card_2_iff[of B] by blast
  then show ?thesis using that B(1) by blast
qed

lemma infam_2d: "C \<in> twos G \<Longrightarrow> D \<in> twos G \<Longrightarrow> npair G \<Longrightarrow> C \<inter> D = {} \<Longrightarrow> infam T2d G"
  by auto

lemma infam_2o:
  "C \<in> twos G \<Longrightarrow> D \<in> twos G \<Longrightarrow> C \<noteq> D \<Longrightarrow> x \<in> C \<Longrightarrow> x \<in> D \<Longrightarrow> npair G \<Longrightarrow> infam T2o G"
  unfolding infam.simps by blast

text \<open>Two distinct 2-clauses give type 2o or 2d, both dominated by 2d.\<close>

lemma infam_2:
  assumes "C \<in> twos G" "D \<in> twos G" "C \<noteq> D" "npair G"
  shows "\<exists>k'. fam_le k' T2d \<and> infam k' G"
proof (cases "C \<inter> D = {}")
  case True
  then have "infam T2d G" using infam_2d[OF assms(1,2,4)] by blast
  then show ?thesis using fam_le_refl by blast
next
  case False
  then obtain x where "x \<in> C" "x \<in> D" by blast
  then have "infam T2o G" using infam_2o[OF assms(1-3) _ _ assms(4)] by blast
  then show ?thesis using fam_le_2o_2d by blast
qed

text \<open>Three distinct 2-clauses with no common variable give type 3, or type 4 if there are
  more 2-clauses.\<close>

lemma t34:
  assumes fin: "finite G" and K: "K1 \<in> twos G" "K2 \<in> twos G" "K3 \<in> twos G"
    and d: "K1 \<noteq> K2" "K1 \<noteq> K3" "K2 \<noteq> K3" and np: "npair G"
    and nc: "\<And>x. x \<in> K1 \<Longrightarrow> x \<in> K2 \<Longrightarrow> x \<in> K3 \<Longrightarrow> False"
  shows "infam T3 G \<or> infam T4 G"
proof -
  have finT: "finite (twos G)" using fin by (simp add: twos_def)
  have sub: "{K1,K2,K3} \<subseteq> twos G" using K by blast
  have c3: "card {K1,K2,K3} = 3" using d by simp
  have ge: "3 \<le> card (twos G)" using card_mono[OF finT sub] c3 by simp
  show ?thesis
  proof (cases "4 \<le> card (twos G)")
    case True
    then have "infam T4 G" using np by simp
    then show ?thesis by blast
  next
    case False
    then have "card (twos G) \<le> card {K1,K2,K3}" using c3 by simp
    then have eq: "{K1,K2,K3} = twos G" by (rule card_seteq[OF finT sub])
    have "card {C\<in>twos G. x \<in> C} \<le> 2" for x
    proof -
      obtain K where K: "K \<in> {K1,K2,K3}" "x \<notin> K" using nc by blast
      have s: "{C\<in>twos G. x \<in> C} \<subseteq> {K1,K2,K3} - {K}"
        unfolding eq[symmetric] using K(2) by blast
      have "card {C\<in>twos G. x \<in> C} \<le> card ({K1,K2,K3} - {K})" by (rule card_mono) (simp_all add: s)
      also have "\<dots> = 2" using K(1) c3 by (simp add: card_Diff_singleton)
      finally show ?thesis .
    qed
    then have "infam T3 G" using ge np by simp
    then show ?thesis by blast
  qed
qed

lemma t3_or_t4:
  assumes "finite G" "K1 \<in> twos G" "K2 \<in> twos G" "K3 \<in> twos G"
    "K1 \<noteq> K2" "K1 \<noteq> K3" "K2 \<noteq> K3" "npair G"
    "\<And>x. x \<in> K1 \<Longrightarrow> x \<in> K2 \<Longrightarrow> x \<in> K3 \<Longrightarrow> False"
  shows "\<exists>k'. fam_le k' T3 \<and> infam k' G"
proof -
  from t34[OF assms] show ?thesis
  proof
    assume "infam T3 G"
    then show ?thesis using fam_le_refl[of T3] by blast
  next
    assume "infam T4 G"
    then show ?thesis using fam_le_4_3 by blast
  qed
qed

lemma t4_of:
  assumes fin: "finite G" and K: "K1 \<in> twos G" "K2 \<in> twos G" "K3 \<in> twos G" "K4 \<in> twos G"
    and d: "distinct [K1,K2,K3,K4]" and np: "npair G"
  shows "infam T4 G"
proof -
  have finT: "finite (twos G)" using fin by (simp add: twos_def)
  have "card {K1,K2,K3,K4} = 4" using d by simp
  moreover have "card {K1,K2,K3,K4} \<le> card (twos G)" using K by (intro card_mono[OF finT]) auto
  ultimately show ?thesis using np by simp
qed

subsection \<open>Type 2d: two disjoint 2-clauses \<open>{a,b}\<close>, \<open>{c,d}\<close>\<close>

text \<open>The 2d proof assumes that no two 2-clauses meet; otherwise the CNF is of type 2o, whose
  bound is smaller and is proved first.  The paper's P2d.5 needs this: with 2-clauses
  \<open>{a,e}\<close>, \<open>{b,e}\<close> (and the same around \<open>{c,d}\<close>) none of P2d.1--P2d.5 holds.\<close>

context core
begin

lemma rows_ok_Nil: "rows_ok []"
  by (simp add: rows_ok_def)

lemma rows_ok_ConsI:
  assumes "J \<subseteq> V" "E \<subseteq> V" "J \<inter> E = {}" "J \<union> E \<noteq> {}" "fam_ok k (restr F J E)" "rows_ok rs"
  shows "rows_ok ((J,E,k) # rs)"
  using assms unfolding rows_ok_def by auto

lemma fam_two: "C \<in> twos G \<Longrightarrow> fam_ok T1 G"
  by auto

lemma fam_in: "infam k G \<Longrightarrow> fam_ok k G"
  by blast

lemma form3:
  assumes C: "C \<in> F" "card C = 3" and xy: "x \<in> C" "y \<in> C" "x \<noteq> y"
  obtains z where "C = {x,y,z}" "z \<noteq> x" "z \<noteq> y"
proof -
  have fC: "finite C" using cnf_clause_finite[OF cnf C(1)] .
  have "card (C - {x,y}) = card C - card {x,y}"
    using xy fC by (intro card_Diff_subset) auto
  then have "card (C - {x,y}) = 1" using C(2) xy(3) by simp
  then obtain z where z: "C - {x,y} = {z}" by (rule card_1_singletonE)
  then have "C = {x,y,z}" using xy by blast
  moreover have "z \<noteq> x" "z \<noteq> y" using z by auto
  ultimately show ?thesis using that by blast
qed

lemma elems3:
  assumes C: "C \<in> F" "card C = 3" "a \<in> C"
  obtains b c where "C = {a,b,c}" "distinct [a,b,c]"
proof -
  have "card (C - {a}) = 2" using C cnf_clause_finite[OF cnf C(1)] by simp
  then obtain b c where bc: "C - {a} = {b,c}" "b \<noteq> c" unfolding card_2_iff by blast
  have e: "C = {a,b,c}" using bc(1) C(3) by blast
  have "a \<noteq> b" "a \<noteq> c" using bc(1) by auto
  then show ?thesis using that[OF e] bc(2) by simp
qed

text \<open>Deleting one variable of a clause leaves a 2-clause or a clause of size at most 1.\<close>

lemma del_cases:
  assumes D: "D \<in> F" "a \<in> D" "D \<inter> J = {}" "D - E = D - {a}"
  shows "D - {a} \<in> twos (restr F J E) \<or> (\<exists>C\<in>restr F J E. card C \<le> 1)"
proof -
  have m: "D - {a} \<in> restr F J E" using restr_mem[OF D(1) D(3), of E] D(4) by simp
  have "card (D - {a}) = card D - 1" using cnf_clause_finite[OF cnf D(1)] D(2) by simp
  then have "card (D - {a}) = 2 \<or> card (D - {a}) \<le> 1" using sizes[OF D(1)] by auto
  then show ?thesis using m by (auto simp: twos_def)
qed

lemma anti_pair:
  assumes "{a,b} \<in> F" "D \<in> F" "a \<in> D" "b \<in> D"
  shows "D = {a,b}"
  using anti[OF assms(1,2)] assms(3,4) by blast

lemma no2o_three:
  assumes no2o: "\<not> infam T2o F" and np: "npair F" and K: "K \<in> twos F"
    and C: "C \<in> F" "x \<in> C" "x \<in> K" "C \<noteq> K"
  shows "card C = 3"
proof (rule ccontr)
  assume "card C \<noteq> 3"
  then have "C \<in> twos F" using sizes[OF C(1)] C(1) by (auto simp: twos_def)
  then have "infam T2o F" by (rule infam_2o[OF _ K C(4) C(2) C(3) np])
  then show False using no2o by blast
qed

text \<open>\<open>\<P>(2d,4)\<close>: \<open>a\<close> lies only in \<open>{a,b}\<close>.\<close>

lemma p2d4:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and dist: "distinct [a,b,c,d]"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b}"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof (rule table[where rs = "[({a},{b},T1), ({b},{a},T1)]"], goal_cases)
  case 1
  have r1: "{c,d} \<in> twos (restr F {a} {b})" by (rule two_mem[OF T(2)]) (use dist in auto)
  have r2: "{c,d} \<in> twos (restr F {b} {a})" by (rule two_mem[OF T(2)]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] fam_two[OF r2]) (use sub[OF T(1)] dist in auto)
next
  case 2
  have "a \<in> X \<and> b \<notin> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
  proof (cases "a \<in> X")
    case True
    have "{a,b} \<inter> X = {a}" using only_clause[OF X True oa] .
    then have "b \<notin> X" using single_out[of "{a,b}" X a b] dist by simp
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis using hit[OF X T(1)] by blast
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>\<open>\<P>(2d,2)\<close>: a clause \<open>D\<close> contains \<open>a\<close> and \<open>c\<close>.  Setting \<open>a = 0\<close>, \<open>b = 1\<close> leaves \<open>D - {a}\<close>
  and \<open>{c,d}\<close>, which meet in \<open>c\<close>; if \<open>D = {a,c}\<close> it leaves the 1-clause \<open>{c}\<close>.\<close>

lemma p2d2:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and dist: "distinct [a,b,c,d]" and np: "npair F"
    and D: "D \<in> F" "a \<in> D" "c \<in> D"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof (rule table[where rs = "[({a},{},T1), ({b},{a},T2o)]"], goal_cases)
  case 1
  have r1: "{c,d} \<in> twos (restr F {a} {})" by (rule two_mem[OF T(2)]) (use dist in auto)
  have bD: "b \<notin> D" using anti_pair[OF T(1) D(1) D(2)] D(3) dist by auto
  have cdm: "{c,d} \<in> twos (restr F {b} {a})" by (rule two_mem[OF T(2)]) (use dist in auto)
  have "D - {a} \<in> twos (restr F {b} {a}) \<or> (\<exists>C\<in>restr F {b} {a}. card C \<le> 1)"
    by (rule del_cases[OF D(1) D(2)]) (use bD in auto)
  moreover have "D - {a} \<noteq> {c,d}"
  proof
    assume e: "D - {a} = {c,d}"
    have "c \<in> D - {a}" "d \<in> D - {a}" unfolding e by simp_all
    then have "D = {c,d}" using anti_pair[OF T(2) D(1)] by blast
    then show False using D(2) dist by auto
  qed
  moreover have "c \<in> D - {a}" using D(3) dist by auto
  ultimately have r2: "fam_ok T2o (restr F {b} {a})"
    using infam_2o[OF _ cdm _ _ _ npair_restr[OF finF np]] by blast
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] r2) (use sub[OF T(1)] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] by blast
  then show ?case by auto
next
  case 3
  then show ?case by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>\<open>\<P>(2d,1)\<close>: \<open>a\<close> lies in two further clauses \<open>D\<^sub>1\<close>, \<open>D\<^sub>2\<close>.  First case: no variable lies in
  \<open>D\<^sub>1\<close>, \<open>D\<^sub>2\<close> and \<open>{c,d}\<close>.  Setting \<open>a = 0\<close>, \<open>b = 1\<close> leaves the 2-clauses \<open>D\<^sub>1 - {a}\<close>, \<open>D\<^sub>2 - {a}\<close>
  and \<open>{c,d}\<close>: type 3, or type 4 if other 2-clauses remain (the paper says type 3).\<close>

lemma p2d1_sep:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and dist: "distinct [a,b,c,d]" and np: "npair F"
    and D: "D1 \<in> F" "D2 \<in> F" "a \<in> D1" "a \<in> D2" "D1 \<noteq> D2" "D1 \<noteq> {a,b}" "D2 \<noteq> {a,b}"
    and nc: "\<And>x. x \<in> D1 \<Longrightarrow> x \<in> D2 \<Longrightarrow> x \<in> {c,d} \<Longrightarrow> False"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof (rule table[where rs = "[({a},{},T1), ({b},{a},T3)]"], goal_cases)
  case 1
  have r1: "{c,d} \<in> twos (restr F {a} {})" by (rule two_mem[OF T(2)]) (use dist in auto)
  have bD: "b \<notin> D1" "b \<notin> D2"
    using anti_pair[OF T(1) D(1) D(3)] anti_pair[OF T(1) D(2) D(4)] D(6,7) by blast+
  have k1: "D1 - {a} \<in> twos (restr F {b} {a}) \<or> (\<exists>C\<in>restr F {b} {a}. card C \<le> 1)"
    by (rule del_cases[OF D(1) D(3)]) (use bD in auto)
  have k2: "D2 - {a} \<in> twos (restr F {b} {a}) \<or> (\<exists>C\<in>restr F {b} {a}. card C \<le> 1)"
    by (rule del_cases[OF D(2) D(4)]) (use bD in auto)
  have k3: "{c,d} \<in> twos (restr F {b} {a})" by (rule two_mem[OF T(2)]) (use dist in auto)
  have n12: "D1 - {a} \<noteq> D2 - {a}"
  proof
    assume "D1 - {a} = D2 - {a}"
    then have "insert a (D1 - {a}) = insert a (D2 - {a})" by simp
    then show False using D(3,4,5) by (simp add: insert_absorb)
  qed
  have ncd: "Di - {a} \<noteq> {c,d}" if "Di \<in> F" "a \<in> Di" for Di
  proof
    assume e: "Di - {a} = {c,d}"
    have "c \<in> Di - {a}" "d \<in> Di - {a}" unfolding e by simp_all
    then have "Di = {c,d}" using anti_pair[OF T(2) that(1)] by blast
    then show False using that(2) dist by auto
  qed
  have r2: "fam_ok T3 (restr F {b} {a})"
  proof (cases "D1 - {a} \<in> twos (restr F {b} {a}) \<and> D2 - {a} \<in> twos (restr F {b} {a})")
    case True
    have "\<exists>k'. fam_le k' T3 \<and> infam k' (restr F {b} {a})"
      by (rule t3_or_t4[OF restr_finite _ _ k3 n12 ncd[OF D(1,3)] ncd[OF D(2,4)] npair_restr[OF finF np]])
        (use True nc in auto)
    then show ?thesis by blast
  next
    case False
    then show ?thesis using k1 k2 by blast
  qed
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] r2) (use sub[OF T(1)] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] by blast
  then show ?case by auto
next
  case 3
  then show ?case by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>Second case: \<open>D\<^sub>1 = {a,d,f}\<close>, \<open>D\<^sub>2 = {a,d,h}\<close>.\<close>

lemma p2d1_com:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and D: "{a,d,f} \<in> F" "{a,d,h} \<in> F"
    and dist: "distinct [a,b,c,d,f,h]"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof (rule table[where rs = "[({a},{},T1), ({b,c,f,h},{a,d},T0), ({b,d},{a},T0)]"], goal_cases)
  case 1
  have r1: "{c,d} \<in> twos (restr F {a} {})" by (rule two_mem[OF T(2)]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF D(1)] sub[OF D(2)] dist in auto)
next
  case 2
  have "a \<in> X \<or> (b \<in> X \<and> c \<in> X \<and> f \<in> X \<and> h \<in> X \<and> a \<notin> X \<and> d \<notin> X) \<or> (b \<in> X \<and> d \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] hit[OF X T(2)] hit[OF X D(1)] hit[OF X D(2)] by auto
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

lemma p2d1:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and dist: "distinct [a,b,c,d]" and np: "npair F"
    and deg: "3 \<le> card {C\<in>F. a \<in> C}"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof -
  have "2 \<le> card ({C\<in>F. a \<in> C} - {{a,b}})"
    using deg by (auto simp: card_Diff_singleton_if)
  then obtain D1 D2 where "D1 \<in> {C\<in>F. a \<in> C} - {{a,b}}" "D2 \<in> {C\<in>F. a \<in> C} - {{a,b}}" "D1 \<noteq> D2"
    by (rule card2_obtain)
  then have D: "D1 \<in> F" "D2 \<in> F" "a \<in> D1" "a \<in> D2" "D1 \<noteq> D2" "D1 \<noteq> {a,b}" "D2 \<noteq> {a,b}"
    by auto
  show ?thesis
  proof (cases "\<exists>x. x \<in> D1 \<and> x \<in> D2 \<and> x \<in> {c,d}")
    case False
    then show ?thesis using p2d1_sep[OF T dist np D] by blast
  next
    case True
    then obtain x where x: "x \<in> D1" "x \<in> D2" "x = c \<or> x = d" by blast
    have ax: "a \<noteq> x" using x(3) dist by auto
    have nc2: "card Di \<noteq> 2" if "Di \<in> F" "Dj \<in> F" "a \<in> Di" "x \<in> Di" "a \<in> Dj" "x \<in> Dj" "Di \<noteq> Dj"
      for Di Dj
    proof
      assume c2: "card Di = 2"
      have s: "{a,x} \<subseteq> Di" using that by blast
      have "card {a,x} = 2" using ax by simp
      then have "{a,x} = Di" using card_seteq[OF cnf_clause_finite[OF cnf that(1)] s] c2 by simp
      then have "Di \<subseteq> Dj" using that by blast
      then show False using anti[OF that(1,2)] that(7) by blast
    qed
    have c3: "card D1 = 3" "card D2 = 3"
      using nc2[of D1 D2] nc2[of D2 D1] sizes[OF D(1)] sizes[OF D(2)] D x by auto
    obtain f where f: "D1 = {a,x,f}" "f \<noteq> a" "f \<noteq> x" using form3[OF D(1) c3(1) D(3) x(1) ax] by blast
    obtain h where h: "D2 = {a,x,h}" "h \<noteq> a" "h \<noteq> x" using form3[OF D(2) c3(2) D(4) x(2) ax] by blast
    have fh: "f \<noteq> h" using f(1) h(1) D(5) by blast
    have bD: "b \<notin> D1" "b \<notin> D2"
      using anti_pair[OF T(1) D(1) D(3)] anti_pair[OF T(1) D(2) D(4)] D(6,7) by blast+
    have cdD: "\<not> (c \<in> D1 \<and> d \<in> D1)" "\<not> (c \<in> D2 \<and> d \<in> D2)"
      using anti_pair[OF T(2) D(1)] anti_pair[OF T(2) D(2)] D(3,4) dist by auto
    from x(3) show ?thesis
    proof
      assume xc: "x = c"
      have "{a,c,f} \<in> F" "{a,c,h} \<in> F" using D(1,2) f(1) h(1) xc by simp_all
      moreover have "distinct [a,b,d,c,f,h]" using dist f h fh bD cdD xc by auto
      moreover have "{d,c} \<in> F" using T(2) by (simp add: insert_commute)
      ultimately show ?thesis using p2d1_com[OF T(1)] by blast
    next
      assume xd: "x = d"
      have "{a,d,f} \<in> F" "{a,d,h} \<in> F" using D(1,2) f(1) h(1) xd by simp_all
      moreover have "distinct [a,b,c,d,f,h]" using dist f h fh bD cdD xd by auto
      ultimately show ?thesis using p2d1_com[OF T] by blast
    qed
  qed
qed

text \<open>\<open>\<P>(2d,3)\<close>: a pair \<open>{e,f}\<close> in two clauses whose third variables lie in \<open>{a,b,c,d}\<close>.  Case 1:
  the clauses are \<open>{e,f,a}\<close>, \<open>{e,f,c}\<close>.\<close>

lemma p2d3_cross:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and K: "{e,f,a} \<in> F" "{e,f,c} \<in> F"
    and dist: "distinct [a,b,c,d,e,f]"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {e,f,a}"
    and oc: "\<And>D. D \<in> F \<Longrightarrow> c \<in> D \<Longrightarrow> D = {c,d} \<or> D = {e,f,c}"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof (rule table[where rs = "[({a,d},{c,b},T1), ({c,b},{a,d},T1), ({b,d},{a,c},T1), ({a,c},{},T0)]"],
    goal_cases)
  case 1
  have r1: "{e,f} \<in> twos (restr F {a,d} {c,b})" by (rule two_mem[OF K(2)]) (use dist in auto)
  have r2: "{e,f} \<in> twos (restr F {c,b} {a,d})" by (rule two_mem[OF K(1)]) (use dist in auto)
  have r3: "{e,f} \<in> twos (restr F {b,d} {a,c})" by (rule two_mem[OF K(1)]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] fam_two[OF r2] fam_two[OF r3] fam_in)
      (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "(a \<in> X \<and> d \<in> X \<and> c \<notin> X \<and> b \<notin> X) \<or> (c \<in> X \<and> b \<in> X \<and> a \<notin> X \<and> d \<notin> X)
      \<or> (b \<in> X \<and> d \<in> X \<and> a \<notin> X \<and> c \<notin> X) \<or> (a \<in> X \<and> c \<in> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "c \<in> X \<or> d \<in> X" "e \<in> X \<or> f \<in> X \<or> a \<in> X" "e \<in> X \<or> f \<in> X \<or> c \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X K(1)] hit[OF X K(2)] by auto
    have ab: "b \<notin> X" if "a \<in> X" "c \<notin> X"
    proof -
      have "{a,b} \<inter> X = {a}"
      proof (cases "e \<in> X")
        case True
        show ?thesis by (rule crit_other'[OF X that(1) oa, of e]) (use True dist in auto)
      next
        case False
        then have "f \<in> X" using h(4) that(2) by blast
        show ?thesis by (rule crit_other'[OF X that(1) oa, of f]) (use \<open>f \<in> X\<close> dist in auto)
      qed
      moreover have "b \<noteq> a" using dist by auto
      ultimately show ?thesis using single_out[of "{a,b}" X a b] by simp
    qed
    have cd: "d \<notin> X" if "c \<in> X" "a \<notin> X"
    proof -
      have "{c,d} \<inter> X = {c}"
      proof (cases "e \<in> X")
        case True
        show ?thesis by (rule crit_other'[OF X that(1) oc, of e]) (use True dist in auto)
      next
        case False
        then have "f \<in> X" using h(3) that(2) by blast
        show ?thesis by (rule crit_other'[OF X that(1) oc, of f]) (use \<open>f \<in> X\<close> dist in auto)
      qed
      moreover have "d \<noteq> c" using dist by auto
      ultimately show ?thesis using single_out[of "{c,d}" X c d] by simp
    qed
    show ?thesis using h ab cd by (cases "a \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  have "c \<noteq> b" using dist by auto
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>Case 2: the clauses are \<open>{e,f,a}\<close>, \<open>{e,f,b}\<close>, and \<open>e\<close> lies in no other clause.  Then \<open>e\<close> and
  \<open>f\<close> are not both in a transversal, since \<open>e\<close> would have no critical clause.\<close>

lemma p2d3_uniq:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and K: "{e,f,a} \<in> F" "{e,f,b} \<in> F"
    and dist: "distinct [a,b,c,d,e,f]"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {e,f,a}"
    and oe: "\<And>D. D \<in> F \<Longrightarrow> e \<in> D \<Longrightarrow> D = {e,f,a} \<or> D = {e,f,b}"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof (rule table[where rs = "[({a,f},{b,e},T1), ({a,e},{b,f},T1), ({b,f},{a,e},T1), ({b,e},{a,f},T1),
    ({a,b},{e,f},T1)]"], goal_cases)
  case 1
  have cd: "{c,d} \<in> twos (restr F J E)" if "{c,d} \<inter> J = {}" "{c,d} \<inter> E = {}" for J E
    by (rule two_mem[OF T(2)]) (use that dist in auto)
  have r: "{c,d} \<in> twos (restr F {a,f} {b,e})" "{c,d} \<in> twos (restr F {a,e} {b,f})"
    "{c,d} \<in> twos (restr F {b,f} {a,e})" "{c,d} \<in> twos (restr F {b,e} {a,f})"
    "{c,d} \<in> twos (restr F {a,b} {e,f})"
    by (rule cd; use dist in auto)+
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r(1)] fam_two[OF r(2)] fam_two[OF r(3)]
        fam_two[OF r(4)] fam_two[OF r(5)])
      (use sub[OF K(1)] sub[OF K(2)] dist in auto)
next
  case 2
  have "(a \<in> X \<and> f \<in> X \<and> b \<notin> X \<and> e \<notin> X) \<or> (a \<in> X \<and> e \<in> X \<and> b \<notin> X \<and> f \<notin> X)
      \<or> (b \<in> X \<and> f \<in> X \<and> a \<notin> X \<and> e \<notin> X) \<or> (b \<in> X \<and> e \<in> X \<and> a \<notin> X \<and> f \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> e \<notin> X \<and> f \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "e \<in> X \<or> f \<in> X \<or> a \<in> X" "e \<in> X \<or> f \<in> X \<or> b \<in> X"
      using hit[OF X T(1)] hit[OF X K(1)] hit[OF X K(2)] by auto
    have nef: "\<not> (e \<in> X \<and> f \<in> X)"
    proof
      assume ef: "e \<in> X \<and> f \<in> X"
      obtain C where C: "C \<in> F" "C \<inter> X = {e}" using critical[OF X, of e] ef by blast
      have "e \<in> C \<inter> X" using C(2) by simp
      then have "f \<in> C" using oe[OF C(1)] by auto
      then have "f \<in> C \<inter> X" using ef by blast
      then show False using C(2) dist by auto
    qed
    have ab: "e \<notin> X \<and> f \<notin> X" if "a \<in> X" "b \<in> X"
    proof -
      have e1: "{e,f,a} \<inter> X = {a}" by (rule crit_other[OF X that(1) oa, of b]) (use that dist in auto)
      have "e \<noteq> a" "f \<noteq> a" using dist by auto
      then show ?thesis using single_out[OF e1, of e] single_out[OF e1, of f] by simp
    qed
    show ?thesis using h nef ab by (cases "a \<in> X"; cases "b \<in> X"; cases "e \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>Case 3: \<open>e\<close> lies in a further clause \<open>C\<^sub>e\<close>.  The rows with \<open>e = 0\<close>, \<open>f = 1\<close> or \<open>a = b = 1\<close>
  leave \<open>C\<^sub>e - {e}\<close> and \<open>{c,d}\<close>: type 2o or 2d.  Only \<open>e\<close>'s further clause is needed; the
  paper also assumes one for \<open>f\<close>.\<close>

lemma p2d3_other:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and K: "{e,f,a} \<in> F" "{e,f,b} \<in> F"
    and dist: "distinct [a,b,c,d,e,f]" and np: "npair F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {e,f,a}"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {a,b} \<or> D = {e,f,b}"
    and Ce: "Ce \<in> F" "e \<in> Ce" "Ce \<noteq> {e,f,a}" "Ce \<noteq> {e,f,b}"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof (rule table[where rs = "[({a,e},{b},T1), ({a,f},{b,e},T2d), ({b,e},{a},T1), ({b,f},{a,e},T2d),
    ({a,b},{e,f},T2d)]"], goal_cases)
  case 1
  have aCe: "a \<notin> Ce"
  proof
    assume "a \<in> Ce"
    then have "Ce = {a,b} \<or> Ce = {e,f,a}" by (rule oa[OF Ce(1)])
    then show False using Ce(2,3) dist by auto
  qed
  have bCe: "b \<notin> Ce"
  proof
    assume "b \<in> Ce"
    then have "Ce = {a,b} \<or> Ce = {e,f,b}" by (rule ob[OF Ce(1)])
    then show False using Ce(2,4) dist by auto
  qed
  have fCe: "f \<notin> Ce"
  proof
    assume fC: "f \<in> Ce"
    have s3: "{{e,f,a},{e,f,b},Ce} \<subseteq> {C\<in>F. e \<in> C \<and> f \<in> C}" using K Ce(1,2) fC by auto
    have ne: "{e,f,a} \<noteq> {e,f,b}" "{e,f,a} \<noteq> Ce" "{e,f,b} \<noteq> Ce" using Ce(3,4) dist by auto
    then have "card {{e,f,a},{e,f,b},Ce} = 3" by simp
    moreover have "card {{e,f,a},{e,f,b},Ce} \<le> card {C\<in>F. e \<in> C \<and> f \<in> C}"
      using finF s3 by (intro card_mono) auto
    moreover have "e \<noteq> f" using dist by simp
    then have "card {C\<in>F. e \<in> C \<and> f \<in> C} \<le> 2" using np unfolding npair_def by blast
    ultimately show False by simp
  qed
  have cdne: "Ce - {e} \<noteq> {c,d}"
  proof
    assume e: "Ce - {e} = {c,d}"
    have "c \<in> Ce - {e}" "d \<in> Ce - {e}" unfolding e by simp_all
    then have "Ce = {c,d}" using anti_pair[OF T(2) Ce(1)] by blast
    then show False using Ce(2) dist by auto
  qed
  have fam2: "fam_ok T2d (restr F J E)"
    if "Ce \<inter> J = {}" "Ce - E = Ce - {e}" "{c,d} \<inter> J = {}" "{c,d} \<inter> E = {}" for J E
  proof -
    have cdm: "{c,d} \<in> twos (restr F J E)" by (rule two_mem[OF T(2)]) (use that(3,4) dist in auto)
    have "Ce - {e} \<in> twos (restr F J E) \<or> (\<exists>C\<in>restr F J E. card C \<le> 1)"
      by (rule del_cases[OF Ce(1) Ce(2) that(1) that(2)])
    then show ?thesis
    proof
      assume "Ce - {e} \<in> twos (restr F J E)"
      then have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F J E)"
        by (rule infam_2[OF _ cdm cdne npair_restr[OF finF np]])
      then show ?thesis by blast
    qed blast
  qed
  have r2: "fam_ok T2d (restr F {a,f} {b,e})" by (rule fam2) (use aCe bCe fCe dist in auto)
  have r4: "fam_ok T2d (restr F {b,f} {a,e})" by (rule fam2) (use aCe bCe fCe dist in auto)
  have r5: "fam_ok T2d (restr F {a,b} {e,f})" by (rule fam2) (use aCe bCe fCe dist in auto)
  have r1: "{c,d} \<in> twos (restr F {a,e} {b})" by (rule two_mem[OF T(2)]) (use dist in auto)
  have r3: "{c,d} \<in> twos (restr F {b,e} {a})" by (rule two_mem[OF T(2)]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] r2 fam_two[OF r3] r4 r5)
      (use sub[OF K(1)] sub[OF K(2)] dist in auto)
next
  case 2
  have "(a \<in> X \<and> e \<in> X \<and> b \<notin> X) \<or> (a \<in> X \<and> f \<in> X \<and> b \<notin> X \<and> e \<notin> X)
      \<or> (b \<in> X \<and> e \<in> X \<and> a \<notin> X) \<or> (b \<in> X \<and> f \<in> X \<and> a \<notin> X \<and> e \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> e \<notin> X \<and> f \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "e \<in> X \<or> f \<in> X \<or> a \<in> X" "e \<in> X \<or> f \<in> X \<or> b \<in> X"
      using hit[OF X T(1)] hit[OF X K(1)] hit[OF X K(2)] by auto
    have ab: "e \<notin> X \<and> f \<notin> X" if "a \<in> X" "b \<in> X"
    proof -
      have e1: "{e,f,a} \<inter> X = {a}" by (rule crit_other[OF X that(1) oa, of b]) (use that dist in auto)
      have "e \<noteq> a" "f \<noteq> a" using dist by auto
      then show ?thesis using single_out[OF e1, of e] single_out[OF e1, of f] by simp
    qed
    show ?thesis using h ab by (cases "a \<in> X"; cases "b \<in> X"; cases "e \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

lemma p2d3_same:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and K: "{e,f,a} \<in> F" "{e,f,b} \<in> F"
    and dist: "distinct [a,b,c,d,e,f]" and np: "npair F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {e,f,a}"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {a,b} \<or> D = {e,f,b}"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof (cases "\<forall>D\<in>F. e \<in> D \<longrightarrow> D = {e,f,a} \<or> D = {e,f,b}")
  case True
  then show ?thesis using p2d3_uniq[OF T K dist oa] by blast
next
  case False
  then obtain Ce where "Ce \<in> F" "e \<in> Ce" "Ce \<noteq> {e,f,a}" "Ce \<noteq> {e,f,b}" by blast
  then show ?thesis using p2d3_other[OF T K dist np oa ob] by blast
qed

text \<open>\<open>\<P>(2d,5)\<close>: \<open>a\<close> and \<open>b\<close> each lie in exactly one further clause, \<open>{a,e,f}\<close> and \<open>{b,g,h}\<close>,
  with \<open>g \<notin> {e,f}\<close>.  Setting \<open>a = b = 1\<close> forces \<open>e = f = g = 0\<close> (and \<open>h = 0\<close>, unused).\<close>

lemma p2d5:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and Da: "{a,e,f} \<in> F" and Db: "{b,g,h} \<in> F"
    and dist: "distinct [a,b,c,d,e,f,g]" and h: "h \<notin> {a,b,c,d}" "h \<noteq> g" and np: "npair F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,e,f}"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {a,b} \<or> D = {b,g,h}"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof (rule table[where rs = "[({a},{b},T2d), ({b},{a},T2d), ({a,b},{e,f,g},T1)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have "{g,h} \<in> twos (restr F {a} {b})" by (rule two_mem[OF Db]) (use dist h in auto)
  moreover have "{c,d} \<in> twos (restr F {a} {b})" by (rule two_mem[OF T(2)]) (use dist in auto)
  ultimately have r1: "infam T2d (restr F {a} {b})" using npr by (rule infam_2d) (use dist h in auto)
  have "{e,f} \<in> twos (restr F {b} {a})" by (rule two_mem[OF Da]) (use dist in auto)
  moreover have "{c,d} \<in> twos (restr F {b} {a})" by (rule two_mem[OF T(2)]) (use dist in auto)
  ultimately have r2: "infam T2d (restr F {b} {a})" using npr by (rule infam_2d) (use dist in auto)
  have r3: "{c,d} \<in> twos (restr F {a,b} {e,f,g})" by (rule two_mem[OF T(2)]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in[OF r1] fam_in[OF r2] fam_two[OF r3])
      (use sub[OF T(1)] sub[OF Da] sub[OF Db] dist in auto)
next
  case 2
  have "(a \<in> X \<and> b \<notin> X) \<or> (b \<in> X \<and> a \<notin> X) \<or> (a \<in> X \<and> b \<in> X \<and> e \<notin> X \<and> f \<notin> X \<and> g \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h1: "a \<in> X \<or> b \<in> X" using hit[OF X T(1)] by auto
    have ab: "e \<notin> X \<and> f \<notin> X \<and> g \<notin> X" if "a \<in> X" "b \<in> X"
    proof -
      have e1: "{a,e,f} \<inter> X = {a}" by (rule crit_other[OF X that(1) oa, of b]) (use that dist in auto)
      have e2: "{b,g,h} \<inter> X = {b}" by (rule crit_other[OF X that(2) ob, of a]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of e] single_out[OF e1, of f] single_out[OF e2, of g] dist
        by auto
    qed
    show ?thesis using h1 ab by (cases "a \<in> X"; cases "b \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

subsubsection \<open>Type 2d: choosing the configuration\<close>

lemma p2d1_any:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and dist: "distinct [a,b,c,d]" and np: "npair F"
    and x: "x \<in> {a,b,c,d}" "3 \<le> card {C\<in>F. x \<in> C}"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof -
  have T': "{b,a} \<in> F" "{d,c} \<in> F" using T by (simp_all add: insert_commute)
  from x(1) consider "x = a" | "x = b" | "x = c" | "x = d" by blast
  then show ?thesis
  proof cases
    case 1
    then have "3 \<le> card {C\<in>F. a \<in> C}" using x(2) by simp
    then show ?thesis by (rule p2d1[OF T dist np])
  next
    case 2
    then have "3 \<le> card {C\<in>F. b \<in> C}" using x(2) by simp
    then show ?thesis by (rule p2d1[OF T'(1) T(2) _ np, rotated]) (use dist in auto)
  next
    case 3
    then have "3 \<le> card {C\<in>F. c \<in> C}" using x(2) by simp
    then show ?thesis by (rule p2d1[OF T(2) T(1) _ np, rotated]) (use dist in auto)
  next
    case 4
    then have "3 \<le> card {C\<in>F. d \<in> C}" using x(2) by simp
    then show ?thesis by (rule p2d1[OF T'(2) T(1) _ np, rotated]) (use dist in auto)
  qed
qed

lemma p2d2_any:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and dist: "distinct [a,b,c,d]" and np: "npair F"
    and D: "D \<in> F" "a \<in> D \<or> b \<in> D" "c \<in> D \<or> d \<in> D"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof -
  have T': "{b,a} \<in> F" "{d,c} \<in> F" using T by (simp_all add: insert_commute)
  have d: "distinct [a,b,d,c]" "distinct [b,a,c,d]" "distinct [b,a,d,c]" using dist by auto
  consider "a \<in> D" "c \<in> D" | "a \<in> D" "d \<in> D" | "b \<in> D" "c \<in> D" | "b \<in> D" "d \<in> D"
    using D(2,3) by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using p2d2[OF T dist np D(1)] by blast
  next
    case 2
    then show ?thesis using p2d2[OF T(1) T'(2) d(1) np D(1)] by blast
  next
    case 3
    then show ?thesis using p2d2[OF T'(1) T(2) d(2) np D(1)] by blast
  next
    case 4
    then show ?thesis using p2d2[OF T'(1) T'(2) d(3) np D(1)] by blast
  qed
qed

lemma p2d3_any:
  assumes T: "{a,b} \<in> F" "{c,d} \<in> F" and dist: "distinct [a,b,c,d]" and np: "npair F"
    and degs: "\<forall>x\<in>{a,b,c,d}. card {C\<in>F. x \<in> C} \<le> 2"
    and nxs: "\<not> (\<exists>D\<in>F. (a \<in> D \<or> b \<in> D) \<and> (c \<in> D \<or> d \<in> D))"
    and ef: "e \<noteq> f" and gh: "g \<noteq> h" "g \<in> {a,b,c,d}" "h \<in> {a,b,c,d}" "g \<notin> {e,f}" "h \<notin> {e,f}"
    and K: "{e,f,g} \<in> F" "{e,f,h} \<in> F"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof -
  have deg: "card {C\<in>F. x \<in> C} \<le> 2" if "x \<in> {a,b,c,d}" for x using degs that by blast
  have nx: False if "D \<in> F" "a \<in> D \<or> b \<in> D" "c \<in> D \<or> d \<in> D" for D using nxs that by blast
  have T': "{b,a} \<in> F" "{d,c} \<in> F" using T by (simp_all add: insert_commute)
  have KK: "{e,f,x} \<in> F" if "x \<in> {g,h}" for x using K that by auto
  have efo: "e \<notin> {a,b,c,d}" "f \<notin> {a,b,c,d}"
    using nx[OF K(1)] nx[OF K(2)] gh by auto
  have only2: "D = P \<or> D = {e,f,x}"
    if "x \<in> {a,b,c,d}" "P \<in> F" "x \<in> P" "e \<notin> P" "{e,f,x} \<in> F" "D \<in> F" "x \<in> D" for x P D
    using two_only[OF deg[OF that(1)] that(2) that(5) that(3) _ _ that(6) that(7)] that(4) by auto
  consider (ab) "a \<in> {g,h}" "b \<in> {g,h}" | (cd) "c \<in> {g,h}" "d \<in> {g,h}"
    | (ac) "a \<in> {g,h}" "c \<in> {g,h}" | (ad) "a \<in> {g,h}" "d \<in> {g,h}"
    | (bc) "b \<in> {g,h}" "c \<in> {g,h}" | (bd) "b \<in> {g,h}" "d \<in> {g,h}"
    using gh(1-3) by auto
  then show ?thesis
  proof cases
    case ab
    have Kx: "{e,f,a} \<in> F" "{e,f,b} \<in> F" using KK ab by auto
    have oa: "D = {a,b} \<or> D = {e,f,a}" if "D \<in> F" "a \<in> D" for D
      by (rule only2[OF _ T(1) _ _ Kx(1) that]) (use efo in auto)
    have ob: "D = {a,b} \<or> D = {e,f,b}" if "D \<in> F" "b \<in> D" for D
      by (rule only2[OF _ T(1) _ _ Kx(2) that]) (use efo in auto)
    have "distinct [a,b,c,d,e,f]" using dist efo ef by auto
    then show ?thesis using p2d3_same[OF T Kx _ np oa ob] by blast
  next
    case cd
    have Kx: "{e,f,c} \<in> F" "{e,f,d} \<in> F" using KK cd by auto
    have oc: "D = {c,d} \<or> D = {e,f,c}" if "D \<in> F" "c \<in> D" for D
      by (rule only2[OF _ T(2) _ _ Kx(1) that]) (use efo in auto)
    have od: "D = {c,d} \<or> D = {e,f,d}" if "D \<in> F" "d \<in> D" for D
      by (rule only2[OF _ T(2) _ _ Kx(2) that]) (use efo in auto)
    have "distinct [c,d,a,b,e,f]" using dist efo ef by auto
    then show ?thesis using p2d3_same[OF T(2) T(1) Kx _ np oc od] by blast
  next
    case ac
    have Kx: "{e,f,a} \<in> F" "{e,f,c} \<in> F" using KK ac by auto
    have oa: "D = {a,b} \<or> D = {e,f,a}" if "D \<in> F" "a \<in> D" for D
      by (rule only2[OF _ T(1) _ _ Kx(1) that]) (use efo in auto)
    have oc: "D = {c,d} \<or> D = {e,f,c}" if "D \<in> F" "c \<in> D" for D
      by (rule only2[OF _ T(2) _ _ Kx(2) that]) (use efo in auto)
    have "distinct [a,b,c,d,e,f]" using dist efo ef by auto
    then show ?thesis using p2d3_cross[OF T Kx _ oa oc] by blast
  next
    case ad
    have Kx: "{e,f,a} \<in> F" "{e,f,d} \<in> F" using KK ad by auto
    have oa: "D = {a,b} \<or> D = {e,f,a}" if "D \<in> F" "a \<in> D" for D
      by (rule only2[OF _ T(1) _ _ Kx(1) that]) (use efo in auto)
    have od: "D = {d,c} \<or> D = {e,f,d}" if "D \<in> F" "d \<in> D" for D
      by (rule only2[OF _ T'(2) _ _ Kx(2) that]) (use efo in auto)
    have "distinct [a,b,d,c,e,f]" using dist efo ef by auto
    then show ?thesis using p2d3_cross[OF T(1) T'(2) Kx _ oa od] by blast
  next
    case bc
    have Kx: "{e,f,b} \<in> F" "{e,f,c} \<in> F" using KK bc by auto
    have ob: "D = {b,a} \<or> D = {e,f,b}" if "D \<in> F" "b \<in> D" for D
      by (rule only2[OF _ T'(1) _ _ Kx(1) that]) (use efo in auto)
    have oc: "D = {c,d} \<or> D = {e,f,c}" if "D \<in> F" "c \<in> D" for D
      by (rule only2[OF _ T(2) _ _ Kx(2) that]) (use efo in auto)
    have "distinct [b,a,c,d,e,f]" using dist efo ef by auto
    then show ?thesis using p2d3_cross[OF T'(1) T(2) Kx _ ob oc] by blast
  next
    case bd
    have Kx: "{e,f,b} \<in> F" "{e,f,d} \<in> F" using KK bd by auto
    have ob: "D = {b,a} \<or> D = {e,f,b}" if "D \<in> F" "b \<in> D" for D
      by (rule only2[OF _ T'(1) _ _ Kx(1) that]) (use efo in auto)
    have od: "D = {d,c} \<or> D = {e,f,d}" if "D \<in> F" "d \<in> D" for D
      by (rule only2[OF _ T'(2) _ _ Kx(2) that]) (use efo in auto)
    have "distinct [b,a,d,c,e,f]" using dist efo ef by auto
    then show ?thesis using p2d3_cross[OF T'(1) T'(2) Kx _ ob od] by blast
  qed
qed

theorem type2d:
  assumes fam: "infam T2d F" and no2o: "\<not> infam T2o F"
  shows "real (card (trans V F t)) \<le> bound T2d s t"
proof -
  obtain C D where CD: "C \<in> twos F" "D \<in> twos F" "C \<inter> D = {}" and np: "npair F"
    using fam by auto
  have "card C = 2" "card D = 2" using CD(1,2) by (simp_all add: twos_def)
  then obtain a b c d where ab: "C = {a,b}" "a \<noteq> b" and cd: "D = {c,d}" "c \<noteq> d"
    unfolding card_2_iff by blast
  have tw: "{a,b} \<in> twos F" "{c,d} \<in> twos F" using CD(1,2) ab(1) cd(1) by simp_all
  have T: "{a,b} \<in> F" "{c,d} \<in> F" using tw by (simp_all add: twos_def)
  have dist: "distinct [a,b,c,d]" using CD(3) ab cd by auto
  have T': "{b,a} \<in> F" "{d,c} \<in> F" using T by (simp_all add: insert_commute)
  show ?thesis
  proof (cases "\<exists>x\<in>{a,b,c,d}. 3 \<le> card {C\<in>F. x \<in> C}")
    case True
    then show ?thesis using p2d1_any[OF T dist np] by blast
  next
    case False
    have deg: "card {C\<in>F. x \<in> C} \<le> 2" if "x \<in> {a,b,c,d}" for x
    proof -
      have "\<not> 3 \<le> card {C\<in>F. x \<in> C}" using False that by blast
      then show ?thesis by simp
    qed
    have dega: "card {C\<in>F. a \<in> C} \<le> 2" "card {C\<in>F. b \<in> C} \<le> 2" using deg by auto
    have degs: "\<forall>x\<in>{a,b,c,d}. card {C\<in>F. x \<in> C} \<le> 2" using deg by blast
    show ?thesis
    proof (cases "\<exists>D\<in>F. (a \<in> D \<or> b \<in> D) \<and> (c \<in> D \<or> d \<in> D)")
      case True
      then show ?thesis using p2d2_any[OF T dist np] by blast
    next
      case nD: False
      then have nx: "False" if "D \<in> F" "a \<in> D \<or> b \<in> D" "c \<in> D \<or> d \<in> D" for D
        using that by blast
      show ?thesis
      proof (cases "\<exists>e f g h. e \<noteq> f \<and> g \<noteq> h \<and> g \<in> {a,b,c,d} \<and> h \<in> {a,b,c,d} \<and> g \<notin> {e,f}
          \<and> h \<notin> {e,f} \<and> {e,f,g} \<in> F \<and> {e,f,h} \<in> F")
        case True
        then obtain e f g h where "e \<noteq> f" "g \<noteq> h" "g \<in> {a,b,c,d}" "h \<in> {a,b,c,d}" "g \<notin> {e,f}"
            "h \<notin> {e,f}" "{e,f,g} \<in> F" "{e,f,h} \<in> F"
          by blast
        then show ?thesis by (rule p2d3_any[OF T dist np degs nD])
      next
        case False
        then have n3: "False"
          if "e \<noteq> f" "g \<noteq> h" "g \<in> {a,b,c,d}" "h \<in> {a,b,c,d}" "g \<notin> {e,f}" "h \<notin> {e,f}"
            "{e,f,g} \<in> F" "{e,f,h} \<in> F" for e f g h
          using that by blast
        show ?thesis
        proof (cases "(\<forall>D\<in>F. a \<in> D \<longrightarrow> D = {a,b}) \<or> (\<forall>D\<in>F. b \<in> D \<longrightarrow> D = {a,b})
            \<or> (\<forall>D\<in>F. c \<in> D \<longrightarrow> D = {c,d}) \<or> (\<forall>D\<in>F. d \<in> D \<longrightarrow> D = {c,d})")
          case True
          then show ?thesis
          proof (elim disjE)
            assume o: "\<forall>D\<in>F. a \<in> D \<longrightarrow> D = {a,b}"
            show ?thesis by (rule p2d4[OF T dist]) (use o in blast)
          next
            assume o: "\<forall>D\<in>F. b \<in> D \<longrightarrow> D = {a,b}"
            have o': "D = {b,a}" if "D \<in> F" "b \<in> D" for D using o that by (auto simp: insert_commute)
            show ?thesis by (rule p2d4[OF T'(1) T(2) _ o']) (use dist in auto)
          next
            assume o: "\<forall>D\<in>F. c \<in> D \<longrightarrow> D = {c,d}"
            show ?thesis by (rule p2d4[OF T(2) T(1)]) (use o dist in auto)
          next
            assume o: "\<forall>D\<in>F. d \<in> D \<longrightarrow> D = {c,d}"
            have o': "D = {d,c}" if "D \<in> F" "d \<in> D" for D using o that by (auto simp: insert_commute)
            show ?thesis by (rule p2d4[OF T'(2) T(1) _ o']) (use dist in auto)
          qed
        next
          case False
          then obtain Da Db where Da: "Da \<in> F" "a \<in> Da" "Da \<noteq> {a,b}" and Db: "Db \<in> F" "b \<in> Db" "Db \<noteq> {a,b}"
            by blast
          have c3: "card Da = 3" "card Db = 3"
            using no2o_three[OF no2o np tw(1) Da(1) Da(2) _ Da(3)]
              no2o_three[OF no2o np tw(1) Db(1) Db(2) _ Db(3)] by simp_all
          obtain e f where ef: "Da = {a,e,f}" "distinct [a,e,f]" by (rule elems3[OF Da(1) c3(1) Da(2)])
          obtain g h where gh: "Db = {b,g,h}" "distinct [b,g,h]" by (rule elems3[OF Db(1) c3(2) Db(2)])
          have bDa: "b \<notin> Da" using anti_pair[OF T(1) Da(1) Da(2)] Da(3) by blast
          have aDb: "a \<notin> Db" using anti_pair[OF T(1) Db(1) _ Db(2)] Db(3) by blast
          have cdDa: "c \<notin> Da" "d \<notin> Da" using nx[OF Da(1)] Da(2) by blast+
          have cdDb: "c \<notin> Db" "d \<notin> Db" using nx[OF Db(1)] Db(2) by blast+
          have efo: "e \<notin> {a,b,c,d}" "f \<notin> {a,b,c,d}" using ef bDa cdDa by auto
          have gho: "g \<notin> {a,b,c,d}" "h \<notin> {a,b,c,d}" using gh aDb cdDb by auto
          have Da': "{a,e,f} \<in> F" "{e,f,a} \<in> F" using Da(1) ef(1) by (simp_all add: insert_commute)
          have "g \<notin> {e,f} \<or> h \<notin> {e,f}"
          proof (rule ccontr)
            assume "\<not> (g \<notin> {e,f} \<or> h \<notin> {e,f})"
            then have "g \<in> {e,f}" "h \<in> {e,f}" by blast+
            then have "{e,f,b} = Db" using gh ef(2) by auto
            then have "{e,f,b} \<in> F" using Db(1) by simp
            moreover have "a \<noteq> b" "a \<in> {a,b,c,d}" "b \<in> {a,b,c,d}" "a \<notin> {e,f}" "b \<notin> {e,f}"
              using dist efo by auto
            ultimately show False using n3[of e f a b] Da'(2) ef(2) by auto
          qed
          then obtain y z where yz: "{b,y,z} \<in> F" "y \<notin> {e,f}" "z \<noteq> y" "y \<notin> {a,b,c,d}" "z \<notin> {a,b,c,d}"
          proof
            assume "g \<notin> {e,f}"
            then show ?thesis using that[of g h] Db(1) gh gho by auto
          next
            assume "h \<notin> {e,f}"
            moreover have "{b,h,g} \<in> F" using Db(1) gh(1) by (simp add: insert_commute)
            ultimately show ?thesis using that[of h g] gh gho by auto
          qed
          have d7: "distinct [a,b,c,d,e,f,y]" using dist efo ef(2) yz(2,4) by auto
          have oa: "D = {a,b} \<or> D = {a,e,f}" if "D \<in> F" "a \<in> D" for D
            using two_only[OF dega(1) T(1) Da'(1) _ _ _ that] efo by auto
          have ob: "D = {a,b} \<or> D = {b,y,z}" if "D \<in> F" "b \<in> D" for D
            using two_only[OF dega(2) T(1) yz(1) _ _ _ that] yz(4) by auto
          show ?thesis by (rule p2d5[OF T Da'(1) yz(1) d7 yz(5) yz(3) np oa ob])
        qed
      qed
    qed
  qed
qed

end


subsection \<open>Types 3 and 4\<close>

text \<open>Type 3: at least three 2-clauses, no variable in three of them.  Any three such 2-clauses
  form a triangle, a path of length 3, or contain one disjoint from the other two.  Type 4: at
  least four 2-clauses.  Type 3 is proved first (from the induction hypothesis alone); type 4
  uses it for even \<open>s\<close> when no variable lies in three 2-clauses.\<close>

context core
begin
lemma a_excl:
  assumes X: "X \<in> trans V F t" and a: "a \<in> X" and ab: "a \<noteq> b" "a \<noteq> c"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
  shows "b \<notin> X \<or> c \<notin> X"
proof -
  obtain C where C: "C \<in> F" "C \<inter> X = {a}" using critical[OF X a] by blast
  have "a \<in> C \<inter> X" using C(2) by simp
  then have "C = {a,b} \<or> C = {a,c}" using oa[OF C(1)] by blast
  then show ?thesis
  proof
    assume "C = {a,b}"
    then have e: "{a,b} \<inter> X = {a}" using C(2) by simp
    have "b \<noteq> a" using ab(1) by blast
    then show ?thesis using single_out[OF e, of b] by simp
  next
    assume "C = {a,c}"
    then have e: "{a,c} \<inter> X = {a}" using C(2) by simp
    have "c \<noteq> a" using ab(2) by blast
    then show ?thesis using single_out[OF e, of c] by simp
  qed
qed

text \<open>Deleting a variable set \<open>E\<close> that meets a clause leaves a 2-clause or a clause of size at
  most 1.\<close>

lemma del_le:
  assumes C: "C \<in> F" "C \<inter> J = {}" "x \<in> C" "x \<in> E"
  shows "C - E \<in> twos (restr F J E) \<or> (\<exists>C'\<in>restr F J E. card C' \<le> 1)"
proof -
  have m: "C - E \<in> restr F J E" using restr_mem[OF C(1) C(2)] .
  have fC: "finite C" using cnf_clause_finite[OF cnf C(1)] .
  have "card (C - E) \<le> card (C - {x})" using fC C(4) by (intro card_mono) auto
  also have "\<dots> = card C - 1" using fC C(3) by simp
  finally have "card (C - E) \<le> 2" using sizes[OF C(1)] by auto
  then have "card (C - E) = 2 \<or> card (C - E) \<le> 1" by auto
  then show ?thesis using m by (auto simp: twos_def)
qed

text \<open>A clause \<open>{z} \<union> P\<close> with \<open>z\<close> set to 0 leaves \<open>P\<close> if \<open>E\<close> misses \<open>P\<close>, and otherwise a clause of
  size at most 1.\<close>

lemma pair_rest:
  assumes C: "insert z P \<in> F" "insert z P \<inter> J = {}" "z \<in> E" "z \<notin> P" "card P = 2"
  shows "(P \<inter> E = {} \<and> P \<in> twos (restr F J E)) \<or> (\<exists>C\<in>restr F J E. card C \<le> 1)"
proof -
  have m: "insert z P - E \<in> restr F J E" using restr_mem[OF C(1) C(2)] .
  show ?thesis
  proof (cases "P \<inter> E = {}")
    case True
    then have "insert z P - E = P" using C(3) by blast
    then show ?thesis using m True C(5) by (simp add: twos_def)
  next
    case False
    then obtain x where x: "x \<in> P" "x \<in> E" by blast
    have fP: "finite P" using C(5) card.infinite by fastforce
    have "insert z P - E \<subseteq> P - {x}" using C(3) x by blast
    then have "card (insert z P - E) \<le> card (P - {x})" using fP by (intro card_mono) auto
    also have "\<dots> = 1" using x(1) C(5) fP by simp
    finally show ?thesis using m by blast
  qed
qed

lemma np3:
  assumes np: "npair F" and xy: "x \<noteq> y" and C: "C1 \<in> F" "C2 \<in> F" "C3 \<in> F" "distinct [C1,C2,C3]"
    and m: "x \<in> C1" "y \<in> C1" "x \<in> C2" "y \<in> C2" "x \<in> C3" "y \<in> C3"
  shows False
proof -
  have "card {C1,C2,C3} = 3" using C(4) by simp
  moreover have "card {C1,C2,C3} \<le> card {C\<in>F. x \<in> C \<and> y \<in> C}" using finF C m by (intro card_mono) auto
  moreover have "card {C\<in>F. x \<in> C \<and> y \<in> C} \<le> 2" using np xy unfolding npair_def by blast
  ultimately show False by simp
qed


lemma twos_restr:
  assumes "K \<in> twos F" "K \<inter> J = {}" "K \<inter> E = {}"
  shows "K \<in> twos (restr F J E)"
proof -
  have "K - E = K" using assms(3) by blast
  then show ?thesis using restr_mem[of K F J E] assms by (simp add: twos_def)
qed

text \<open>Two further clauses through \<open>x\<close>, with \<open>x\<close> set to 0, leave two 2-clauses (type 2o or 2d)
  or a clause of size at most 1.\<close>

lemma fam_two_dels:
  assumes np: "npair F" and A: "A1 \<in> F" "A2 \<in> F" "x \<in> A1" "x \<in> A2" "A1 \<noteq> A2"
    and J: "A1 \<inter> J = {}" "A2 \<inter> J = {}" and E: "A1 - E = A1 - {x}" "A2 - E = A2 - {x}"
  shows "fam_ok T2d (restr F J E)"
proof -
  have k1: "A1 - {x} \<in> twos (restr F J E) \<or> (\<exists>C\<in>restr F J E. card C \<le> 1)"
    by (rule del_cases[OF A(1) A(3) J(1) E(1)])
  have k2: "A2 - {x} \<in> twos (restr F J E) \<or> (\<exists>C\<in>restr F J E. card C \<le> 1)"
    by (rule del_cases[OF A(2) A(4) J(2) E(2)])
  have ne: "A1 - {x} \<noteq> A2 - {x}"
  proof
    assume "A1 - {x} = A2 - {x}"
    then have "insert x (A1 - {x}) = insert x (A2 - {x})" by simp
    then show False using A(3-5) by (simp add: insert_absorb)
  qed
  show ?thesis
  proof (cases "A1 - {x} \<in> twos (restr F J E) \<and> A2 - {x} \<in> twos (restr F J E)")
    case True
    then have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F J E)"
      using infam_2[OF _ _ ne npair_restr[OF finF np]] by blast
    then show ?thesis by blast
  next
    case False
    then show ?thesis using k1 k2 by blast
  qed
qed

lemma bound_T3_T4: "even s \<Longrightarrow> bound T4 s t = bound T3 s t"
  by (simp add: bound_def)

subsubsection \<open>Type 4\<close>

text \<open>\<open>\<P>(4,1)\<close>, odd \<open>s\<close>: no two 2-clauses meet.\<close>

lemma p4_1:
  assumes T: "{a,b} \<in> F" and ab: "a \<noteq> b" and odd: "odd s" and np: "npair F"
    and K: "K1 \<in> twos F" "K2 \<in> twos F" "K3 \<in> twos F" "K1 \<noteq> K2" "K1 \<noteq> K3" "K2 \<noteq> K3"
    and dj: "K1 \<inter> K2 = {}" "K1 \<inter> K3 = {}" "K2 \<inter> K3 = {}"
      "K1 \<inter> {a,b} = {}" "K2 \<inter> {a,b} = {}" "K3 \<inter> {a,b} = {}"
  shows "real (card (trans V F t)) \<le> bound T4 s t"
proof (rule table[where rs = "[({a},{},T3), ({b},{a},T3)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have o: "K1 \<inter> {a} = {}" "K2 \<inter> {a} = {}" "K3 \<inter> {a} = {}" "K1 \<inter> {b} = {}" "K2 \<inter> {b} = {}"
    "K3 \<inter> {b} = {}" using dj(4-6) by blast+
  have m1: "K1 \<in> twos (restr F {a} {})" "K2 \<in> twos (restr F {a} {})" "K3 \<in> twos (restr F {a} {})"
    using twos_restr[OF K(1) o(1)] twos_restr[OF K(2) o(2)] twos_restr[OF K(3) o(3)] by simp_all
  have m2: "K1 \<in> twos (restr F {b} {a})" "K2 \<in> twos (restr F {b} {a})" "K3 \<in> twos (restr F {b} {a})"
    using twos_restr[OF K(1) o(4) o(1)] twos_restr[OF K(2) o(5) o(2)] twos_restr[OF K(3) o(6) o(3)] .
  have "\<exists>k'. fam_le k' T3 \<and> infam k' (restr F {a} {})"
    by (rule t3_or_t4[OF restr_finite m1 K(4-6) npr]) (use dj(1) in blast)
  then have r1: "fam_ok T3 (restr F {a} {})" by blast
  have "\<exists>k'. fam_le k' T3 \<and> infam k' (restr F {b} {a})"
    by (rule t3_or_t4[OF restr_finite m2 K(4-6) npr]) (use dj(1) in blast)
  then have r2: "fam_ok T3 (restr F {b} {a})" by blast
  show ?case by (intro rows_ok_ConsI rows_ok_Nil r1 r2) (use sub[OF T] ab in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X using hit[OF X T] by blast
  then show ?case by auto
next
  case 3
  show ?case using odd ab by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(4,2)\<close>, odd \<open>s\<close>: \<open>a\<close> lies in exactly two 2-clauses \<open>{a,b}\<close>, \<open>{a,c}\<close>; two further 2-clauses
  avoid \<open>a\<close>.\<close>

lemma p4_2:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]" and odd: "odd s" and np: "npair F"
    and K: "K1 \<in> twos F" "K2 \<in> twos F" "K1 \<noteq> K2" "a \<notin> K1" "a \<notin> K2"
  shows "real (card (trans V F t)) \<le> bound T4 s t"
proof (rule table[where rs = "[({a},{},T2d), ({b,c},{a},T0)]"], goal_cases)
  case 1
  have m1: "K1 \<in> twos (restr F {a} {})" "K2 \<in> twos (restr F {a} {})"
    using twos_restr[OF K(1)] twos_restr[OF K(2)] K(4,5) by auto
  have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F {a} {})"
    by (rule infam_2[OF m1 K(3) npair_restr[OF finF np]])
  then have r1: "fam_ok T2d (restr F {a} {})" by blast
  show ?case by (intro rows_ok_ConsI rows_ok_Nil r1 fam_in) (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> c \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] hit[OF X T(2)] by auto
  then show ?case by auto
next
  case 3
  show ?case using odd dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(4,3)\<close>: \<open>a\<close> lies in three 2-clauses.  For odd \<open>s\<close> this is the paper's table.  For even \<open>s\<close>
  the paper defers to type 3, which does not apply here; two tables cover it: \<open>a\<close> in four
  2-clauses, or in three and a further 2-clause avoids \<open>a\<close>.\<close>

lemma p4_3:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" "{a,d} \<in> F" and dist: "distinct [a,b,c,d]" and odd: "odd s"
  shows "real (card (trans V F t)) \<le> bound T4 s t"
proof (rule table[where rs = "[({a},{},T0), ({b,c,d},{a},T0)]"], goal_cases)
  case 1
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in) (use sub[OF T(1)] sub[OF T(2)] sub[OF T(3)] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> c \<in> X \<and> d \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] hit[OF X T(2)] hit[OF X T(3)] by auto
  then show ?case by auto
next
  case 3
  show ?case using odd dist by (simp add: ratio_simps)
qed

lemma p4_e4:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" "{a,d} \<in> F" "{a,e} \<in> F" and dist: "distinct [a,b,c,d,e]"
    and ev: "even s"
  shows "real (card (trans V F t)) \<le> bound T4 s t"
proof (rule table[where rs = "[({a},{},T0), ({b,c,d,e},{a},T0)]"], goal_cases)
  case 1
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF T(3)] sub[OF T(4)] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> c \<in> X \<and> d \<in> X \<and> e \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] hit[OF X T(2)] hit[OF X T(3)] hit[OF X T(4)] by auto
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

lemma p4_e3:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" "{a,d} \<in> F" and dist: "distinct [a,b,c,d]" and ev: "even s"
    and K: "K \<in> twos F" "a \<notin> K"
  shows "real (card (trans V F t)) \<le> bound T4 s t"
proof (rule table[where rs = "[({a},{},T1), ({b,c,d},{a},T0)]"], goal_cases)
  case 1
  have r1: "K \<in> twos (restr F {a} {})" using twos_restr[OF K(1)] K(2) by auto
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF T(3)] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> c \<in> X \<and> d \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] hit[OF X T(2)] hit[OF X T(3)] by auto
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

subsubsection \<open>Type 3: a triangle \<open>{a,b}\<close>, \<open>{b,c}\<close>, \<open>{a,c}\<close>\<close>

text \<open>\<open>\<P>(3t,1)\<close>: \<open>a\<close> lies in no clause outside the triangle.\<close>

lemma p3t1:
  assumes T: "{a,b} \<in> F" "{b,c} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({b,c},{a},T0), ({a,c},{b},T0), ({a,b},{c},T0)]"], goal_cases)
  case 1
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in) (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "(b \<in> X \<and> c \<in> X \<and> a \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X) \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "b \<in> X \<or> c \<in> X" "a \<in> X \<or> c \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X T(3)] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    show ?thesis using h ex by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>\<open>\<P>(3t,2)\<close>: \<open>a\<close> lies in exactly one clause \<open>{a,d,e}\<close> outside the triangle, and \<open>b\<close>, \<open>c\<close> in
  at least one.\<close>

lemma p3t2:
  assumes T: "{a,b} \<in> F" "{b,c} \<in> F" "{a,c} \<in> F" and Da: "{a,d,e} \<in> F" and dist: "distinct [a,b,c,d,e]"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c} \<or> D = {a,d,e}"
    and Db: "Db \<in> F" "b \<in> Db" "Db \<noteq> {a,b}" "Db \<noteq> {b,c}"
    and Dc: "Dc \<in> F" "c \<in> Dc" "Dc \<noteq> {a,c}" "Dc \<noteq> {b,c}"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({b,c},{a},T1), ({a,c},{b},T1), ({a,b},{c},T1), ({a,b,c},{d,e},T0)]"],
    goal_cases)
  case 1
  have r1: "{d,e} \<in> twos (restr F {b,c} {a})" by (rule two_mem[OF Da]) (use dist in auto)
  have aDb: "a \<notin> Db" using anti_pair[OF T(1) Db(1) _ Db(2)] Db(3) by blast
  have cDb: "c \<notin> Db" using anti_pair[OF T(2) Db(1) Db(2)] Db(4) by blast
  have aDc: "a \<notin> Dc" using anti_pair[OF T(3) Dc(1) _ Dc(2)] Dc(3) by blast
  have bDc: "b \<notin> Dc" using anti_pair[OF T(2) Dc(1) _ Dc(2)] Dc(4) by blast
  have "Db - {b} \<in> twos (restr F {a,c} {b}) \<or> (\<exists>C\<in>restr F {a,c} {b}. card C \<le> 1)"
    by (rule del_cases[OF Db(1) Db(2)]) (use aDb cDb in auto)
  then have r2: "fam_ok T1 (restr F {a,c} {b})" using fam_two by blast
  have "Dc - {c} \<in> twos (restr F {a,b} {c}) \<or> (\<exists>C\<in>restr F {a,b} {c}. card C \<le> 1)"
    by (rule del_cases[OF Dc(1) Dc(2)]) (use aDc bDc in auto)
  then have r3: "fam_ok T1 (restr F {a,b} {c})" using fam_two by blast
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] r2 r3 fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF Da] dist in auto)
next
  case 2
  have "(b \<in> X \<and> c \<in> X \<and> a \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X) \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> c \<in> X \<and> d \<notin> X \<and> e \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "b \<in> X \<or> c \<in> X" "a \<in> X \<or> c \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X T(3)] by auto
    have abc: "d \<notin> X \<and> e \<notin> X" if aX: "a \<in> X" and bX: "b \<in> X" and cX: "c \<in> X"
    proof -
      obtain C where C: "C \<in> F" "C \<inter> X = {a}" using critical[OF X aX] by blast
      have "a \<in> C \<inter> X" using C(2) by simp
      then have "C = {a,b} \<or> C = {a,c} \<or> C = {a,d,e}" using oa[OF C(1)] by blast
      moreover have "C \<noteq> {a,b}"
      proof
        assume "C = {a,b}"
        then have "b \<in> C \<inter> X" using bX by simp
        then show False using C(2) dist by auto
      qed
      moreover have "C \<noteq> {a,c}"
      proof
        assume "C = {a,c}"
        then have "c \<in> C \<inter> X" using cX by simp
        then show False using C(2) dist by auto
      qed
      ultimately have e1: "{a,d,e} \<inter> X = {a}" using C(2) by auto
      show ?thesis using single_out[OF e1, of d] single_out[OF e1, of e] dist by auto
    qed
    show ?thesis using h abc by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>\<open>\<P>(3t,3)\<close>: each of \<open>a\<close>, \<open>b\<close>, \<open>c\<close> lies in two clauses outside the triangle.\<close>

lemma p3t3:
  assumes T: "{a,b} \<in> F" "{b,c} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]" and np: "npair F"
    and A: "A1 \<in> F" "A2 \<in> F" "a \<in> A1" "a \<in> A2" "A1 \<noteq> A2" "b \<notin> A1" "b \<notin> A2" "c \<notin> A1" "c \<notin> A2"
    and B: "B1 \<in> F" "B2 \<in> F" "b \<in> B1" "b \<in> B2" "B1 \<noteq> B2" "a \<notin> B1" "a \<notin> B2" "c \<notin> B1" "c \<notin> B2"
    and C: "C1 \<in> F" "C2 \<in> F" "c \<in> C1" "c \<in> C2" "C1 \<noteq> C2" "a \<notin> C1" "a \<notin> C2" "b \<notin> C1" "b \<notin> C2"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({b,c},{a},T2d), ({a,c},{b},T2d), ({a,b},{c},T2d), ({a,b,c},{},T0)]"],
    goal_cases)
  case 1
  have r1: "fam_ok T2d (restr F {b,c} {a})" by (rule fam_two_dels[OF np A(1-5)]) (use A in auto)
  have r2: "fam_ok T2d (restr F {a,c} {b})" by (rule fam_two_dels[OF np B(1-5)]) (use B in auto)
  have r3: "fam_ok T2d (restr F {a,b} {c})" by (rule fam_two_dels[OF np C(1-5)]) (use C in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil r1 r2 r3 fam_in) (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "(b \<in> X \<and> c \<in> X \<and> a \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X) \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> c \<in> X)"
    if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] hit[OF X T(2)] hit[OF X T(3)] by auto
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

subsubsection \<open>Type 3: a path \<open>{a,b}\<close>, \<open>{b,c}\<close>, \<open>{c,d}\<close>\<close>

text \<open>\<open>\<P>(3p,1)\<close>: \<open>b\<close> lies only in \<open>{a,b}\<close> and \<open>{b,c}\<close>.  \<^bold>\<open>The paper's table is wrong\<close>: it claims that
  \<open>a = 1\<close> forces \<open>b = 0\<close>, but \<open>a = b = 1\<close>, \<open>c = 0\<close>, \<open>d = 1\<close> is possible (in
  \<open>{ab, bc, cd, axy, duv}\<close>, \<open>{a,b,d}\<close> is a minimum transversal no row covers).  Splitting on \<open>c\<close>
  instead gives a tight table.\<close>

lemma p3p1:
  assumes T: "{a,b} \<in> F" "{b,c} \<in> F" "{c,d} \<in> F" and dist: "distinct [a,b,c,d]"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {b,a} \<or> D = {b,c}"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({b,d},{c},T0), ({b,c},{a},T0), ({a,c},{b},T0)]"], goal_cases)
  case 1
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in) (use sub[OF T(1)] sub[OF T(2)] sub[OF T(3)] dist in auto)
next
  case 2
  have "(b \<in> X \<and> d \<in> X \<and> c \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "b \<in> X \<or> c \<in> X" "c \<in> X \<or> d \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X T(3)] by auto
    have ba: "b \<noteq> a" "b \<noteq> c" using dist by auto
    have ex: "a \<notin> X \<or> c \<notin> X" if "b \<in> X" using a_excl[OF X that ba ob] .
    show ?thesis using h ex by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>\<open>\<P>(3p,2)\<close>: \<open>b\<close> lies in a further clause.  Only \<open>b\<close>'s clause is used; the paper also
  assumes one for \<open>c\<close>.\<close>

lemma p3p2:
  assumes T: "{a,b} \<in> F" "{b,c} \<in> F" "{c,d} \<in> F" and dist: "distinct [a,b,c,d]"
    and Db: "Db \<in> F" "b \<in> Db" "Db \<noteq> {a,b}" "Db \<noteq> {b,c}"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({b},{},T1), ({a,c},{b},T1)]"], goal_cases)
  case 1
  have r1: "{c,d} \<in> twos (restr F {b} {})" by (rule two_mem[OF T(3)]) (use dist in auto)
  have aDb: "a \<notin> Db" using anti_pair[OF T(1) Db(1) _ Db(2)] Db(3) by blast
  have cDb: "c \<notin> Db" using anti_pair[OF T(2) Db(1) Db(2)] Db(4) by blast
  have "Db - {b} \<in> twos (restr F {a,c} {b}) \<or> (\<exists>C\<in>restr F {a,c} {b}. card C \<le> 1)"
    by (rule del_cases[OF Db(1) Db(2)]) (use aDb cDb in auto)
  then have r2: "fam_ok T1 (restr F {a,c} {b})" using fam_two by blast
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] r2) (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "b \<in> X \<or> a \<in> X \<and> c \<in> X \<and> b \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] hit[OF X T(2)] by auto
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

subsubsection \<open>Type 3: a 2-clause \<open>{a,b}\<close> disjoint from two others \<open>{c,d}\<close>, \<open>{e,f}\<close>\<close>

lemma del_ne_pair:
  assumes "{c,d} \<in> F" "D \<in> F" "a \<in> D" "a \<notin> {c,d}"
  shows "D - {a} \<noteq> {c,d}"
proof
  assume e: "D - {a} = {c,d}"
  have "c \<in> D - {a}" "d \<in> D - {a}" unfolding e by simp_all
  then have "D = {c,d}" using anti_pair[OF assms(1,2)] by blast
  then show False using assms(3,4) by blast
qed

text \<open>\<open>a\<close> lies only in \<open>{a,b}\<close> (P3io.2 and P3ie.1; any parity, and the pairs may meet).\<close>

lemma p3i_uniq:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{e,f} \<in> F" and np: "npair F"
    and dist: "distinct [a,b,c,d]" "distinct [a,b,e,f]" "{c,d} \<noteq> {e,f}"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b}"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({a},{b},T2d), ({b},{a},T2d)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m1: "{c,d} \<in> twos (restr F {a} {b})" "{e,f} \<in> twos (restr F {a} {b})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have m2: "{c,d} \<in> twos (restr F {b} {a})" "{e,f} \<in> twos (restr F {b} {a})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F {a} {b})" by (rule infam_2[OF m1 dist(3) npr])
  then have r1: "fam_ok T2d (restr F {a} {b})" by blast
  have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F {b} {a})" by (rule infam_2[OF m2 dist(3) npr])
  then have r2: "fam_ok T2d (restr F {b} {a})" by blast
  show ?case by (intro rows_ok_ConsI rows_ok_Nil r1 r2) (use sub[OF T] dist in auto)
next
  case 2
  have "a \<in> X \<and> b \<notin> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
  proof (cases "a \<in> X")
    case True
    have "{a,b} \<inter> X = {a}" using only_clause[OF X True oa] .
    then have "b \<notin> X" using single_out[of "{a,b}" X a b] dist by auto
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis using hit[OF X T] by blast
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>P3io.1: odd \<open>s\<close>, and the two other 2-clauses meet: \<open>{c,d}\<close>, \<open>{d,f}\<close>.\<close>

lemma p3i_o1:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{d,f} \<in> F" and dist: "distinct [a,b,c,d,f]"
    and np: "npair F" and odd: "odd s"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({a},{},T2o), ({b},{a},T2o)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have ne: "{c,d} \<noteq> {d,f}" using dist by auto
  have m1: "{c,d} \<in> twos (restr F {a} {})" "{d,f} \<in> twos (restr F {a} {})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have m2: "{c,d} \<in> twos (restr F {b} {a})" "{d,f} \<in> twos (restr F {b} {a})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have r1: "infam T2o (restr F {a} {})" by (rule infam_2o[where x = d, OF m1 ne _ _ npr]) simp_all
  have r2: "infam T2o (restr F {b} {a})" by (rule infam_2o[where x = d, OF m2 ne _ _ npr]) simp_all
  show ?case by (intro rows_ok_ConsI rows_ok_Nil fam_in[OF r1] fam_in[OF r2]) (use sub[OF T] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X using hit[OF X T] by blast
  then show ?case by auto
next
  case 3
  show ?case using odd dist by (simp add: ratio_simps)
qed

text \<open>P3io.3: odd \<open>s\<close>, the other two are disjoint, and \<open>a\<close> lies in a further clause \<open>D\<^sub>a\<close>
  (possibly a 2-clause).\<close>

lemma p3i_o3:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{e,f} \<in> F" and dist: "distinct [a,b,c,d,e,f]"
    and np: "npair F" and odd: "odd s" and Da: "Da \<in> F" "a \<in> Da" "Da \<noteq> {a,b}"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({a},{},T2d), ({b},{a},T3)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m1: "{c,d} \<in> twos (restr F {a} {})" "{e,f} \<in> twos (restr F {a} {})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have r1: "infam T2d (restr F {a} {})" by (rule infam_2d[OF m1 npr]) (use dist in auto)
  have m2: "{c,d} \<in> twos (restr F {b} {a})" "{e,f} \<in> twos (restr F {b} {a})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have bDa: "b \<notin> Da" using anti_pair[OF T Da(1) Da(2)] Da(3) by blast
  have kd: "Da - {a} \<in> twos (restr F {b} {a}) \<or> (\<exists>C\<in>restr F {b} {a}. card C \<le> 1)"
    by (rule del_cases[OF Da(1) Da(2)]) (use bDa in auto)
  have n1: "{c,d} \<noteq> {e,f}" using dist by auto
  have n2: "{c,d} \<noteq> Da - {a}" using del_ne_pair[OF K(1) Da(1) Da(2)] dist by auto
  have n3: "{e,f} \<noteq> Da - {a}" using del_ne_pair[OF K(2) Da(1) Da(2)] dist by auto
  have r2: "fam_ok T3 (restr F {b} {a})"
  proof (cases "Da - {a} \<in> twos (restr F {b} {a})")
    case True
    have "\<exists>k'. fam_le k' T3 \<and> infam k' (restr F {b} {a})"
      by (rule t3_or_t4[OF restr_finite m2 True n1 n2 n3 npr]) (use dist in auto)
    then show ?thesis by blast
  next
    case False
    then show ?thesis using kd by blast
  qed
  show ?case by (intro rows_ok_ConsI rows_ok_Nil fam_in[OF r1] r2) (use sub[OF T] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X using hit[OF X T] by blast
  then show ?case by auto
next
  case 3
  show ?case using odd dist by (simp add: ratio_simps)
qed

text \<open>Even \<open>s\<close>, \<open>a\<close> in two further clauses: the row \<open>a = 0\<close>, \<open>b = 1\<close> leaves four 2-clauses (type
  4), whatever they meet.  This generalizes the paper's P3ie.6.\<close>

lemma p3i_e2:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{e,f} \<in> F" and np: "npair F" and ev: "even s"
    and dist: "distinct [a,b,c,d]" "distinct [a,b,e,f]" "{c,d} \<noteq> {e,f}"
    and A: "A1 \<in> F" "A2 \<in> F" "a \<in> A1" "a \<in> A2" "A1 \<noteq> A2" "A1 \<noteq> {a,b}" "A2 \<noteq> {a,b}"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({a},{},T2d), ({b},{a},T4)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m1: "{c,d} \<in> twos (restr F {a} {})" "{e,f} \<in> twos (restr F {a} {})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F {a} {})" by (rule infam_2[OF m1 dist(3) npr])
  then have r1: "fam_ok T2d (restr F {a} {})" by blast
  have m2: "{c,d} \<in> twos (restr F {b} {a})" "{e,f} \<in> twos (restr F {b} {a})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have bA: "b \<notin> A1" "b \<notin> A2"
    using anti_pair[OF T A(1) A(3)] anti_pair[OF T A(2) A(4)] A(6,7) by blast+
  have k1: "A1 - {a} \<in> twos (restr F {b} {a}) \<or> (\<exists>C\<in>restr F {b} {a}. card C \<le> 1)"
    by (rule del_cases[OF A(1) A(3)]) (use bA in auto)
  have k2: "A2 - {a} \<in> twos (restr F {b} {a}) \<or> (\<exists>C\<in>restr F {b} {a}. card C \<le> 1)"
    by (rule del_cases[OF A(2) A(4)]) (use bA in auto)
  have n12: "A1 - {a} \<noteq> A2 - {a}"
  proof
    assume "A1 - {a} = A2 - {a}"
    then have "insert a (A1 - {a}) = insert a (A2 - {a})" by simp
    then show False using A(3-5) by (simp add: insert_absorb)
  qed
  have nK: "{c,d} \<noteq> A1 - {a}" "{c,d} \<noteq> A2 - {a}" "{e,f} \<noteq> A1 - {a}" "{e,f} \<noteq> A2 - {a}"
    using del_ne_pair[OF K(1) A(1) A(3)] del_ne_pair[OF K(1) A(2) A(4)]
      del_ne_pair[OF K(2) A(1) A(3)] del_ne_pair[OF K(2) A(2) A(4)] dist by auto
  have r2: "fam_ok T4 (restr F {b} {a})"
  proof (cases "A1 - {a} \<in> twos (restr F {b} {a}) \<and> A2 - {a} \<in> twos (restr F {b} {a})")
    case True
    have "infam T4 (restr F {b} {a})"
      by (rule t4_of[OF restr_finite m2 _ _ _ npr]) (use True dist(3) nK n12 in auto)
    then show ?thesis by blast
  next
    case False
    then show ?thesis using k1 k2 by blast
  qed
  show ?case by (intro rows_ok_ConsI rows_ok_Nil r1 r2) (use sub[OF T] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X using hit[OF X T] by blast
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>Even \<open>s\<close>, the other two meet in \<open>d\<close>, and a further clause of \<open>a\<close> avoids \<open>d\<close> (the paper's
  P3ie.4, which also asks for it to avoid \<open>c\<close> and \<open>f\<close>).\<close>

lemma p3i_e3a:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{d,f} \<in> F" and dist: "distinct [a,b,c,d,f]"
    and np: "npair F" and ev: "even s" and Da: "Da \<in> F" "a \<in> Da" "Da \<noteq> {a,b}" "d \<notin> Da"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({a},{},T2o), ({b},{a},T3)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have ne: "{c,d} \<noteq> {d,f}" using dist by auto
  have m1: "{c,d} \<in> twos (restr F {a} {})" "{d,f} \<in> twos (restr F {a} {})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have r1: "infam T2o (restr F {a} {})" by (rule infam_2o[where x = d, OF m1 ne _ _ npr]) simp_all
  have m2: "{c,d} \<in> twos (restr F {b} {a})" "{d,f} \<in> twos (restr F {b} {a})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have bDa: "b \<notin> Da" using anti_pair[OF T Da(1) Da(2)] Da(3) by blast
  have kd: "Da - {a} \<in> twos (restr F {b} {a}) \<or> (\<exists>C\<in>restr F {b} {a}. card C \<le> 1)"
    by (rule del_cases[OF Da(1) Da(2)]) (use bDa in auto)
  have n2: "{c,d} \<noteq> Da - {a}" using del_ne_pair[OF K(1) Da(1) Da(2)] dist by auto
  have n3: "{d,f} \<noteq> Da - {a}" using del_ne_pair[OF K(2) Da(1) Da(2)] dist by auto
  have r2: "fam_ok T3 (restr F {b} {a})"
  proof (cases "Da - {a} \<in> twos (restr F {b} {a})")
    case True
    have "\<exists>k'. fam_le k' T3 \<and> infam k' (restr F {b} {a})"
      by (rule t3_or_t4[OF restr_finite m2 True ne n2 n3 npr]) (use dist Da(4) in auto)
    then show ?thesis by blast
  next
    case False
    then show ?thesis using kd by blast
  qed
  show ?case by (intro rows_ok_ConsI rows_ok_Nil fam_in[OF r1] r2) (use sub[OF T] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X using hit[OF X T] by blast
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>Even \<open>s\<close>, the other two meet in \<open>d\<close>, and \<open>a\<close> lies in \<open>{a,d,x}\<close> (the paper's P3ie.3; with the
  type-2o row the sum is \<open>41/42\<close>).\<close>

lemma p3i_e3b:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{d,f} \<in> F" and Da: "{a,d,x} \<in> F"
    and dist: "distinct [a,b,c,d,f,x]" and np: "npair F" and ev: "even s"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({a},{},T2o), ({b,d},{a},T0), ({b,c,f,x},{a,d},T0)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have ne: "{c,d} \<noteq> {d,f}" using dist by auto
  have m1: "{c,d} \<in> twos (restr F {a} {})" "{d,f} \<in> twos (restr F {a} {})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have r1: "infam T2o (restr F {a} {})" by (rule infam_2o[where x = d, OF m1 ne _ _ npr]) simp_all
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in[OF r1] fam_in)
      (use sub[OF T] sub[OF K(1)] sub[OF K(2)] sub[OF Da] dist in auto)
next
  case 2
  have "a \<in> X \<or> (b \<in> X \<and> d \<in> X \<and> a \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> f \<in> X \<and> x \<in> X \<and> a \<notin> X \<and> d \<notin> X)"
    if X: "X \<in> trans V F t" for X
    using hit[OF X T] hit[OF X K(1)] hit[OF X K(2)] hit[OF X Da] by auto
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>Even \<open>s\<close>, the other two disjoint, and \<open>a\<close> in the 2-clause \<open>{a,c}\<close>.\<close>

lemma p3i_e4:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{e,f} \<in> F" and Da: "{a,c} \<in> F"
    and dist: "distinct [a,b,c,d,e,f]" and np: "npair F" and ev: "even s"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({a},{},T2d), ({b,c},{a},T1)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m1: "{c,d} \<in> twos (restr F {a} {})" "{e,f} \<in> twos (restr F {a} {})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have r1: "infam T2d (restr F {a} {})" by (rule infam_2d[OF m1 npr]) (use dist in auto)
  have r2: "{e,f} \<in> twos (restr F {b,c} {a})" by (rule two_mem[OF K(2)]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in[OF r1] fam_two[OF r2]) (use sub[OF T] sub[OF Da] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> c \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T] hit[OF X Da] by auto
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>Even \<open>s\<close>, the other two disjoint, and \<open>a\<close>'s only further clause is \<open>{a,c,e}\<close>, meeting both.
  The paper's P3ie.2 table claims a type-1 row here that is only of type 0 (sum \<open>43/42\<close>); this
  table, which also uses a further clause of \<open>b\<close>, sums to \<open>39/42\<close>.\<close>

lemma p3i_eG:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{e,f} \<in> F" and Da: "{a,c,e} \<in> F"
    and dist: "distinct [a,b,c,d,e,f]" and np: "npair F" and ev: "even s"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c,e}"
    and Db: "Db \<in> F" "b \<in> Db" "Db \<noteq> {a,b}"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({b,c},{a},T1), ({b,d,e},{a,c},T0), ({a},{b},T3), ({a,b,d,f},{c,e},T0)]"],
    goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have r1: "{e,f} \<in> twos (restr F {b,c} {a})" by (rule two_mem[OF K(2)]) (use dist in auto)
  have m3: "{c,d} \<in> twos (restr F {a} {b})" "{e,f} \<in> twos (restr F {a} {b})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have aDb: "a \<notin> Db" using anti_pair[OF T Db(1) _ Db(2)] Db(3) by blast
  have kd: "Db - {b} \<in> twos (restr F {a} {b}) \<or> (\<exists>C\<in>restr F {a} {b}. card C \<le> 1)"
    by (rule del_cases[OF Db(1) Db(2)]) (use aDb in auto)
  have n1: "{c,d} \<noteq> {e,f}" using dist by auto
  have n2: "{c,d} \<noteq> Db - {b}" using del_ne_pair[OF K(1) Db(1) Db(2)] dist by auto
  have n3: "{e,f} \<noteq> Db - {b}" using del_ne_pair[OF K(2) Db(1) Db(2)] dist by auto
  have r3: "fam_ok T3 (restr F {a} {b})"
  proof (cases "Db - {b} \<in> twos (restr F {a} {b})")
    case True
    have "\<exists>k'. fam_le k' T3 \<and> infam k' (restr F {a} {b})"
      by (rule t3_or_t4[OF restr_finite m3 True n1 n2 n3 npr]) (use dist in auto)
    then show ?thesis by blast
  next
    case False
    then show ?thesis using kd by blast
  qed
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] r3 fam_in)
      (use sub[OF T] sub[OF K(1)] sub[OF K(2)] dist in auto)
next
  case 2
  have "(b \<in> X \<and> c \<in> X \<and> a \<notin> X) \<or> (b \<in> X \<and> d \<in> X \<and> e \<in> X \<and> a \<notin> X \<and> c \<notin> X) \<or> (a \<in> X \<and> b \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> d \<in> X \<and> f \<in> X \<and> c \<notin> X \<and> e \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "c \<in> X \<or> d \<in> X" "e \<in> X \<or> f \<in> X" "a \<in> X \<or> c \<in> X \<or> e \<in> X"
      using hit[OF X T] hit[OF X K(1)] hit[OF X K(2)] hit[OF X Da] by auto
    have ab: "c \<notin> X \<and> e \<notin> X" if "a \<in> X" "b \<in> X"
    proof -
      have e1: "{a,c,e} \<inter> X = {a}" by (rule crit_other[OF X that(1) oa, of b]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of c] single_out[OF e1, of e] dist by auto
    qed
    show ?thesis using h ab by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") auto
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>Even \<open>s\<close>, the other two disjoint, and \<open>a\<close> lies in \<open>{a,c,v}\<close> with \<open>v\<close> outside both pairs (the
  paper's P3ie.2).\<close>

lemma p3i_e5:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{e,f} \<in> F" and Da: "{a,c,v} \<in> F"
    and dist: "distinct [a,b,c,d,e,f,v]" and np: "npair F" and ev: "even s"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({a},{},T2d), ({b,c},{a},T1), ({b,d,v},{a,c},T1)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m1: "{c,d} \<in> twos (restr F {a} {})" "{e,f} \<in> twos (restr F {a} {})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have r1: "infam T2d (restr F {a} {})" by (rule infam_2d[OF m1 npr]) (use dist in auto)
  have r2: "{e,f} \<in> twos (restr F {b,c} {a})" by (rule two_mem[OF K(2)]) (use dist in auto)
  have r3: "{e,f} \<in> twos (restr F {b,d,v} {a,c})" by (rule two_mem[OF K(2)]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in[OF r1] fam_two[OF r2] fam_two[OF r3])
      (use sub[OF T] sub[OF K(1)] sub[OF Da] dist in auto)
next
  case 2
  have "a \<in> X \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X) \<or> (b \<in> X \<and> d \<in> X \<and> v \<in> X \<and> a \<notin> X \<and> c \<notin> X)"
    if X: "X \<in> trans V F t" for X
    using hit[OF X T] hit[OF X K(1)] hit[OF X Da] by auto
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>Even \<open>s\<close>, the other two disjoint, \<open>a\<close>'s further clause \<open>D\<^sub>a\<close> avoids them, and \<open>c\<close> lies in a
  further clause \<open>D\<^sub>c\<close> with \<open>D\<^sub>c - {c} \<noteq> D\<^sub>a - {a}\<close> (the paper's P3ie.5, without its conditions
  on the remaining variables).\<close>

lemma p3i_e6:
  assumes T: "{a,b} \<in> F" and K: "{c,d} \<in> F" "{e,f} \<in> F" and dist: "distinct [a,b,c,d,e,f]"
    and np: "npair F" and ev: "even s"
    and Da: "Da \<in> F" "a \<in> Da" "Da \<noteq> {a,b}" "Da \<inter> {b,c,d,e,f} = {}"
    and Dc: "Dc \<in> F" "c \<in> Dc" "Dc \<noteq> {c,d}" "Dc - {c} \<noteq> Da - {a}" "a \<notin> Dc" "b \<notin> Dc"
  shows "real (card (trans V F t)) \<le> bound T3 s t"
proof (rule table[where rs = "[({a},{},T2d), ({b,c},{a},T2d), ({b,d},{a,c},T3)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m1: "{c,d} \<in> twos (restr F {a} {})" "{e,f} \<in> twos (restr F {a} {})"
    subgoal by (rule two_mem[OF K(1)]) (use dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dist in auto)
    done
  have r1: "infam T2d (restr F {a} {})" by (rule infam_2d[OF m1 npr]) (use dist in auto)
  have Dab: "b \<notin> Da" "c \<notin> Da" "d \<notin> Da" "e \<notin> Da" "f \<notin> Da" using Da(4) by blast+
  have ef2: "{e,f} \<in> twos (restr F {b,c} {a})" by (rule two_mem[OF K(2)]) (use dist in auto)
  have ka2: "Da - {a} \<in> twos (restr F {b,c} {a}) \<or> (\<exists>C\<in>restr F {b,c} {a}. card C \<le> 1)"
    by (rule del_cases[OF Da(1) Da(2)]) (use Dab in auto)
  have nea: "{e,f} \<noteq> Da - {a}" using Dab(4) by blast
  have r2: "fam_ok T2d (restr F {b,c} {a})"
  proof (cases "Da - {a} \<in> twos (restr F {b,c} {a})")
    case True
    have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F {b,c} {a})"
      by (rule infam_2[OF ef2 True nea npr])
    then show ?thesis by blast
  next
    case False
    then show ?thesis using ka2 by blast
  qed
  have ef3: "{e,f} \<in> twos (restr F {b,d} {a,c})" by (rule two_mem[OF K(2)]) (use dist in auto)
  have ka3: "Da - {a} \<in> twos (restr F {b,d} {a,c}) \<or> (\<exists>C\<in>restr F {b,d} {a,c}. card C \<le> 1)"
    by (rule del_cases[OF Da(1) Da(2)]) (use Dab in auto)
  have dDc: "d \<notin> Dc" using anti_pair[OF K(1) Dc(1) Dc(2)] Dc(3) by blast
  have kc3: "Dc - {c} \<in> twos (restr F {b,d} {a,c}) \<or> (\<exists>C\<in>restr F {b,d} {a,c}. card C \<le> 1)"
    by (rule del_cases[OF Dc(1) Dc(2)]) (use dDc Dc(5,6) in auto)
  have nec: "{e,f} \<noteq> Dc - {c}" using del_ne_pair[OF K(2) Dc(1) Dc(2)] dist by auto
  have r3: "fam_ok T3 (restr F {b,d} {a,c})"
  proof (cases "Da - {a} \<in> twos (restr F {b,d} {a,c}) \<and> Dc - {c} \<in> twos (restr F {b,d} {a,c})")
    case True
    have "\<exists>k'. fam_le k' T3 \<and> infam k' (restr F {b,d} {a,c})"
      by (rule t3_or_t4[OF restr_finite ef3 _ _ nea nec Dc(4)[symmetric] npr]) (use True Dab in auto)
    then show ?thesis by blast
  next
    case False
    then show ?thesis using ka3 kc3 by blast
  qed
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in[OF r1] r2 r3) (use sub[OF T] sub[OF K(1)] dist in auto)
next
  case 2
  have "a \<in> X \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X) \<or> (b \<in> X \<and> d \<in> X \<and> a \<notin> X \<and> c \<notin> X)"
    if X: "X \<in> trans V F t" for X
    using hit[OF X T] hit[OF X K(1)] by auto
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

end

subsection \<open>Type 2o: two 2-clauses \<open>{a,b}\<close>, \<open>{a,c}\<close>\<close>

text \<open>The 2o proof assumes that the CNF is not of type 3 or 4 (proved first); then every
  further clause through \<open>b\<close> or \<open>c\<close> is a 3-clause.\<close>

context core
begin

lemma no34_three:
  assumes n3: "\<not> infam T3 F" and n4: "\<not> infam T4 F" and np: "npair F"
    and T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]"
    and C: "C \<in> F" "x \<in> C" "x = b \<or> x = c" "C \<noteq> {a,b}" "C \<noteq> {a,c}"
  shows "card C = 3"
proof (rule ccontr)
  assume "card C \<noteq> 3"
  then have tC: "C \<in> twos F" using sizes[OF C(1)] C(1) by (auto simp: twos_def)
  have tw: "{a,b} \<in> twos F" "{a,c} \<in> twos F" using T dist by (auto simp: twos_def)
  have aC: "a \<notin> C"
  proof
    assume aC: "a \<in> C"
    from C(3) show False
    proof
      assume "x = b"
      then have "C = {a,b}" using anti_pair[OF T(1) C(1) aC] C(2) by simp
      then show False using C(4) by blast
    next
      assume "x = c"
      then have "C = {a,c}" using anti_pair[OF T(2) C(1) aC] C(2) by simp
      then show False using C(5) by blast
    qed
  qed
  have "infam T3 F \<or> infam T4 F"
  proof (rule t34[OF finF tw(1) tw(2) tC])
    show "{a,b} \<noteq> {a,c}" using dist by auto
    show "{a,b} \<noteq> C" using C(4) by blast
    show "{a,c} \<noteq> C" using C(5) by blast
    show "npair F" by (rule np)
  next
    fix y assume "y \<in> {a,b}" "y \<in> {a,c}" "y \<in> C"
    then show False using aC dist by auto
  qed
  then show False using n3 n4 by blast
qed

text \<open>Odd \<open>s\<close>: \<open>a = 1\<close>, or \<open>a = 0\<close> and \<open>b = c = 1\<close>.\<close>

lemma p2o_odd:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]" and odd: "odd s"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a},{},T0), ({b,c},{a},T0)]"], goal_cases)
  case 1
  show ?case by (intro rows_ok_ConsI rows_ok_Nil fam_in) (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> c \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] hit[OF X T(2)] by auto
  then show ?case by auto
next
  case 3
  show ?case using odd dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,1)\<close>: \<open>a\<close> lies in a further clause \<open>D\<close> (a 3-clause, or a third 2-clause \<open>{a,x}\<close>).\<close>

lemma p2o1:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]" and ev: "even s"
    and D: "D \<in> F" "a \<in> D" "D \<noteq> {a,b}" "D \<noteq> {a,c}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a},{},T0), ({b,c},{a},T1)]"], goal_cases)
  case 1
  have bD: "b \<notin> D" "c \<notin> D"
    using anti_pair[OF T(1) D(1) D(2)] anti_pair[OF T(2) D(1) D(2)] D(3,4) by blast+
  have "D - {a} \<in> twos (restr F {b,c} {a}) \<or> (\<exists>C\<in>restr F {b,c} {a}. card C \<le> 1)"
    by (rule del_cases[OF D(1) D(2)]) (use bD in auto)
  then have r2: "fam_ok T1 (restr F {b,c} {a})" using fam_two by blast
  show ?case by (intro rows_ok_ConsI rows_ok_Nil r2 fam_in) (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> c \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] hit[OF X T(2)] by auto
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,2)\<close>: \<open>b\<close> lies in three further clauses.  They share no further variable (that pair
  would lie in three clauses), so the paper's Case 2 cannot occur.\<close>

lemma p2o2:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]" and ev: "even s" and np: "npair F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and D: "D1 \<in> F" "D2 \<in> F" "D3 \<in> F" "b \<in> D1" "b \<in> D2" "b \<in> D3" "distinct [D1,D2,D3]"
      "D1 \<noteq> {a,b}" "D2 \<noteq> {a,b}" "D3 \<noteq> {a,b}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({b},{},T1), ({a},{b},T3)]"], goal_cases)
  case 1
  have r1: "{a,c} \<in> twos (restr F {b} {})" by (rule two_mem[OF T(2)]) (use dist in auto)
  have aD: "a \<notin> Di" if "Di \<in> F" "b \<in> Di" "Di \<noteq> {a,b}" for Di
  proof
    assume "a \<in> Di"
    then have "Di = {a,b} \<or> Di = {a,c}" by (rule oa[OF that(1)])
    then show False using that(2,3) dist by auto
  qed
  have kk: "Di - {b} \<in> twos (restr F {a} {b}) \<or> (\<exists>C\<in>restr F {a} {b}. card C \<le> 1)"
    if "Di \<in> F" "b \<in> Di" "Di \<noteq> {a,b}" for Di
    by (rule del_cases[OF that(1) that(2)]) (use aD[OF that] in auto)
  have ne: "Di - {b} \<noteq> Dj - {b}" if "b \<in> Di" "b \<in> Dj" "Di \<noteq> Dj" for Di Dj
  proof
    assume "Di - {b} = Dj - {b}"
    then have "insert b (Di - {b}) = insert b (Dj - {b})" by simp
    then show False using that by (simp add: insert_absorb)
  qed
  have dd: "D1 \<noteq> D2" "D1 \<noteq> D3" "D2 \<noteq> D3" using D(7) by auto
  have r2: "fam_ok T3 (restr F {a} {b})"
  proof (cases "D1 - {b} \<in> twos (restr F {a} {b}) \<and> D2 - {b} \<in> twos (restr F {a} {b})
      \<and> D3 - {b} \<in> twos (restr F {a} {b})")
    case True
    have "\<exists>k'. fam_le k' T3 \<and> infam k' (restr F {a} {b})"
    proof (rule t3_or_t4[OF restr_finite _ _ _ ne[OF D(4,5) dd(1)] ne[OF D(4,6) dd(2)]
          ne[OF D(5,6) dd(3)] npair_restr[OF finF np]])
      fix x assume x: "x \<in> D1 - {b}" "x \<in> D2 - {b}" "x \<in> D3 - {b}"
      show False by (rule np3[OF np, of b x D1 D2 D3]) (use x D in auto)
    qed (use True in auto)
    then show ?thesis by blast
  next
    case False
    then show ?thesis using kk[OF D(1,4,8)] kk[OF D(2,5,9)] kk[OF D(3,6,10)] by blast
  qed
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] r2) (use sub[OF T(1)] dist in auto)
next
  case 2
  have "b \<in> X \<or> a \<in> X \<and> b \<notin> X" if X: "X \<in> trans V F t" for X
    using hit[OF X T(1)] by auto
  then show ?case by auto
next
  case 3
  show ?case using ev by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,3)\<close>: \<open>b\<close> lies only in \<open>{a,b}\<close>.\<close>

lemma p2o3:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]" and ev: "even s"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {a,b}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a},{b},T0), ({b,c},{a},T0)]"], goal_cases)
  case 1
  show ?case by (intro rows_ok_ConsI rows_ok_Nil fam_in) (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "a \<in> X \<and> b \<notin> X \<or> b \<in> X \<and> c \<in> X \<and> a \<notin> X" if X: "X \<in> trans V F t" for X
  proof (cases "a \<in> X")
    case True
    have "b \<notin> X"
    proof
      assume b: "b \<in> X"
      have e: "{a,b} \<inter> X = {b}" using only_clause[OF X b ob] .
      have "a \<noteq> b" using dist by simp
      then show False using single_out[OF e, of a] True by simp
    qed
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis using hit[OF X T(1)] hit[OF X T(2)] by auto
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,4)\<close>: two clauses \<open>{b,c,d}\<close>, \<open>{b,c,e}\<close>.\<close>

lemma p2o4:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c,d,e]" and ev: "even s"
    and K: "{b,c,d} \<in> F" "{b,c,e} \<in> F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a,d,e},{b,c},T0), ({a,c},{b},T0), ({a,b},{c},T0), ({b,c},{a},T0)]"],
    goal_cases)
  case 1
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in) (use sub[OF T(1)] sub[OF T(2)] sub[OF K(1)] sub[OF K(2)] dist in auto)
next
  case 2
  have "(a \<in> X \<and> d \<in> X \<and> e \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X" "b \<in> X \<or> c \<in> X \<or> d \<in> X" "b \<in> X \<or> c \<in> X \<or> e \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X K(1)] hit[OF X K(2)] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    show ?thesis using h ex by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,5)\<close>: one clause \<open>{b,c,d}\<close> and further clauses \<open>{b,e,f}\<close>, \<open>{c,g,h}\<close>, with
  \<open>d \<notin> {e,f}\<close>.\<close>

lemma p2o5_sep:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,c,d} \<in> F" and Db: "{b,e,f} \<in> F" and Dc: "{c,g,h} \<in> F"
    and dist: "distinct [a,b,c,d,e,f]" and gh: "distinct [a,b,c,g,h]"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a,b},{c},T1), ({a,c},{b},T1), ({a,d},{b,c},T1), ({b,c},{a},T0)]"],
    goal_cases)
  case 1
  have r1: "{g,h} \<in> twos (restr F {a,b} {c})" by (rule two_mem[OF Dc]) (use gh in auto)
  have r2: "{e,f} \<in> twos (restr F {a,c} {b})" by (rule two_mem[OF Db]) (use dist in auto)
  have r3: "{e,f} \<in> twos (restr F {a,d} {b,c})" by (rule two_mem[OF Db]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] fam_two[OF r2] fam_two[OF r3] fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF K] dist in auto)
next
  case 2
  have "(a \<in> X \<and> b \<in> X \<and> c \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X) \<or> (a \<in> X \<and> d \<in> X \<and> b \<notin> X \<and> c \<notin> X)
      \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X" "b \<in> X \<or> c \<in> X \<or> d \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X K] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    show ?thesis using h ex by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>A case the paper's P2o.1--P2o.10 miss: one clause \<open>{b,c,d}\<close>, a further clause \<open>{b,e,f}\<close>,
  and \<open>c\<close> in no clause besides \<open>{a,c}\<close> and \<open>{b,c,d}\<close>.  First \<open>d \<notin> {e,f}\<close>; then \<open>c = 1\<close>,
  \<open>b = 0\<close> forces \<open>d = 0\<close>.  The table is tight.\<close>

lemma p2o5_gap:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,c,d} \<in> F" and Db: "{b,e,f} \<in> F" and dist: "distinct [a,b,c,d,e,f]"
    and oc: "\<And>D. D \<in> F \<Longrightarrow> c \<in> D \<Longrightarrow> D = {a,c} \<or> D = {b,c,d}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a,b},{c},T0), ({a,c},{b,d},T1), ({a,d},{b,c},T1), ({b,c},{a},T0)]"],
    goal_cases)
  case 1
  have r2: "{e,f} \<in> twos (restr F {a,c} {b,d})" by (rule two_mem[OF Db]) (use dist in auto)
  have r3: "{e,f} \<in> twos (restr F {a,d} {b,c})" by (rule two_mem[OF Db]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r2] fam_two[OF r3] fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF K] dist in auto)
next
  case 2
  have "(a \<in> X \<and> b \<in> X \<and> c \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X \<and> d \<notin> X)
      \<or> (a \<in> X \<and> d \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X" "b \<in> X \<or> c \<in> X \<or> d \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X K] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    have cd: "d \<notin> X" if "c \<in> X" "a \<in> X"
    proof -
      have e1: "{b,c,d} \<inter> X = {c}" by (rule crit_other[OF X that(1) oc, of a]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of d] dist by auto
    qed
    show ?thesis using h ex cd by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>Second case, for P2o.5 and the missed case alike: \<open>d \<in> {e,f}\<close>, so \<open>b\<close>'s clauses are
  \<open>{a,b}\<close>, \<open>{b,c,d}\<close>, \<open>{b,d,f}\<close>.  Then \<open>b = 1\<close>, \<open>c = 0\<close> forces \<open>d = 0\<close>.\<close>

lemma p2o5_shared:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s" and np: "npair F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,c,d} \<in> F" "{b,d,f} \<in> F" and dist: "distinct [a,b,c,d,f]"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {a,b} \<or> D = {b,c,d} \<or> D = {b,d,f}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a,b},{c,d},T0), ({b,c},{a},T0), ({a},{b},T2o)]"], goal_cases)
  case 1
  have m1: "{c,d} \<in> twos (restr F {a} {b})" by (rule two_mem[OF K(1)]) (use dist in auto)
  have m2: "{d,f} \<in> twos (restr F {a} {b})" by (rule two_mem[OF K(2)]) (use dist in auto)
  have ne: "{c,d} \<noteq> {d,f}" using dist by auto
  have r3: "infam T2o (restr F {a} {b})"
    by (rule infam_2o[where x = d, OF m1 m2 ne _ _ npair_restr[OF finF np]]) simp_all
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in[OF r3] fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF K(1)] dist in auto)
next
  case 2
  have "(a \<in> X \<and> b \<in> X \<and> c \<notin> X \<and> d \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X) \<or> (a \<in> X \<and> b \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    have bd: "d \<notin> X" if bX: "b \<in> X" and aX: "a \<in> X"
    proof
      assume dX: "d \<in> X"
      obtain C where C: "C \<in> F" "C \<inter> X = {b}" using critical[OF X bX] by blast
      have "b \<in> C \<inter> X" using C(2) by simp
      then have bC: "b \<in> C" by blast
      from ob[OF C(1) bC] consider "C = {a,b}" | "C = {b,c,d}" | "C = {b,d,f}" by blast
      then show False
      proof cases
        case 1
        then have "a \<in> C \<inter> X" using aX by simp
        then show False using C(2) dist by auto
      next
        case 2
        then have "d \<in> C \<inter> X" using dX by simp
        then show False using C(2) dist by auto
      next
        case 3
        then have "d \<in> C \<inter> X" using dX by simp
        then show False using C(2) dist by auto
      qed
    qed
    show ?thesis using h ex bd by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,6)\<close>: clauses \<open>{b,d,e}\<close>, \<open>{c,d,e}\<close> and a further clause \<open>{b,f,g}\<close>.\<close>

lemma p2o6:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s" and np: "npair F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,d,e} \<in> F" "{c,d,e} \<in> F" "{b,f,g} \<in> F"
    and dist: "distinct [a,b,c,d,e]" and fg: "distinct [b,f,g]" "a \<notin> {f,g}" "{f,g} \<noteq> {d,e}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a},{b},T2d), ({a,b},{c},T1), ({b,c},{a},T0)]"], goal_cases)
  case 1
  have m1: "{d,e} \<in> twos (restr F {a} {b})" by (rule two_mem[OF K(1)]) (use dist in auto)
  have m2: "{f,g} \<in> twos (restr F {a} {b})" by (rule two_mem[OF K(3)]) (use fg dist in auto)
  have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F {a} {b})"
    by (rule infam_2[OF m2 m1 fg(3) npair_restr[OF finF np]])
  then have r1: "fam_ok T2d (restr F {a} {b})" by blast
  have r2: "{d,e} \<in> twos (restr F {a,b} {c})" by (rule two_mem[OF K(2)]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil r1 fam_two[OF r2] fam_in)
      (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "(a \<in> X \<and> b \<notin> X) \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    show ?thesis using h ex by (cases "a \<in> X"; cases "b \<in> X") auto
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,7)\<close>: \<open>b\<close> and \<open>c\<close> each lie in two further clauses, giving four distinct pairs.  The
  row \<open>a = 1\<close>, \<open>b = c = 0\<close> leaves four 2-clauses, so it is of type 4 however they overlap: the
  paper's Cases 2 and 3 are not needed.\<close>

lemma p2o7:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s" and np: "npair F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,d,e} \<in> F" "{b,f,g} \<in> F" "{c,h,i} \<in> F" "{c,j,k} \<in> F" and dist: "distinct [a,b,c]"
    and dd: "distinct [b,d,e]" "distinct [b,f,g]" "distinct [c,h,i]" "distinct [c,j,k]"
    and abc: "{d,e,f,g} \<inter> {a,c} = {}" "{h,i,j,k} \<inter> {a,b} = {}"
    and pd: "{d,e} \<noteq> {f,g}" "{d,e} \<noteq> {h,i}" "{d,e} \<noteq> {j,k}" "{f,g} \<noteq> {h,i}" "{f,g} \<noteq> {j,k}"
      "{h,i} \<noteq> {j,k}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a},{b,c},T3), ({a,c},{b},T2d), ({a,b},{c},T2d), ({b,c},{a},T0)]"],
    goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m1: "{d,e} \<in> twos (restr F {a} {b,c})" "{f,g} \<in> twos (restr F {a} {b,c})"
    "{h,i} \<in> twos (restr F {a} {b,c})" "{j,k} \<in> twos (restr F {a} {b,c})"
    subgoal by (rule two_mem[OF K(1)]) (use dd abc dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dd abc dist in auto)
    subgoal by (rule two_mem[OF K(3)]) (use dd abc dist in auto)
    subgoal by (rule two_mem[OF K(4)]) (use dd abc dist in auto)
    done
  have "infam T4 (restr F {a} {b,c})" by (rule t4_of[OF restr_finite m1 _ npr]) (use pd in simp)
  then have r1: "fam_ok T3 (restr F {a} {b,c})" using fam_le_4_3 by blast
  have m2: "{d,e} \<in> twos (restr F {a,c} {b})" "{f,g} \<in> twos (restr F {a,c} {b})"
    subgoal by (rule two_mem[OF K(1)]) (use dd abc dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dd abc dist in auto)
    done
  have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F {a,c} {b})" by (rule infam_2[OF m2 pd(1) npr])
  then have r2: "fam_ok T2d (restr F {a,c} {b})" by blast
  have m3: "{h,i} \<in> twos (restr F {a,b} {c})" "{j,k} \<in> twos (restr F {a,b} {c})"
    subgoal by (rule two_mem[OF K(3)]) (use dd abc dist in auto)
    subgoal by (rule two_mem[OF K(4)]) (use dd abc dist in auto)
    done
  have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F {a,b} {c})" by (rule infam_2[OF m3 pd(6) npr])
  then have r3: "fam_ok T2d (restr F {a,b} {c})" by blast
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil r1 r2 r3 fam_in) (use sub[OF T(1)] sub[OF T(2)] dist in auto)
next
  case 2
  have "(a \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X) \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X)
      \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    show ?thesis using h ex by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,8)\<close>: \<open>b\<close> lies in two further clauses and \<open>c\<close> in one, with distinct pairs.  Case 1:
  no variable in all three pairs.\<close>

lemma p2o8_sep:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s" and np: "npair F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,d,e} \<in> F" "{b,f,g} \<in> F" "{c,h,i} \<in> F" and dist: "distinct [a,b,c]"
    and dd: "distinct [b,d,e]" "distinct [b,f,g]" "distinct [c,h,i]"
    and abc: "{d,e,f,g} \<inter> {a,c} = {}" "{h,i} \<inter> {a,b} = {}"
    and pd: "{d,e} \<noteq> {f,g}" "{d,e} \<noteq> {h,i}" "{f,g} \<noteq> {h,i}"
    and nc: "\<not> (\<exists>x. x \<in> {d,e} \<and> x \<in> {f,g} \<and> x \<in> {h,i})"
    and oc: "\<And>D. D \<in> F \<Longrightarrow> c \<in> D \<Longrightarrow> D = {a,c} \<or> D = {c,h,i}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a},{b,c},T3), ({a,c},{b,h,i},T2d), ({a,b},{c},T1), ({b,c},{a},T0)]"],
    goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m1: "{d,e} \<in> twos (restr F {a} {b,c})" "{f,g} \<in> twos (restr F {a} {b,c})"
    "{h,i} \<in> twos (restr F {a} {b,c})"
    subgoal by (rule two_mem[OF K(1)]) (use dd abc dist in auto)
    subgoal by (rule two_mem[OF K(2)]) (use dd abc dist in auto)
    subgoal by (rule two_mem[OF K(3)]) (use dd abc dist in auto)
    done
  have "\<exists>k'. fam_le k' T3 \<and> infam k' (restr F {a} {b,c})"
    by (rule t3_or_t4[OF restr_finite m1 pd npr]) (use nc in blast)
  then have r1: "fam_ok T3 (restr F {a} {b,c})" by blast
  have p1: "({d,e} \<inter> {b,h,i} = {} \<and> {d,e} \<in> twos (restr F {a,c} {b,h,i}))
      \<or> (\<exists>C\<in>restr F {a,c} {b,h,i}. card C \<le> 1)"
    by (rule pair_rest) (use K(1) dd abc dist in auto)
  have p2: "({f,g} \<inter> {b,h,i} = {} \<and> {f,g} \<in> twos (restr F {a,c} {b,h,i}))
      \<or> (\<exists>C\<in>restr F {a,c} {b,h,i}. card C \<le> 1)"
    by (rule pair_rest) (use K(2) dd abc dist in auto)
  have r2: "fam_ok T2d (restr F {a,c} {b,h,i})"
  proof (cases "{d,e} \<in> twos (restr F {a,c} {b,h,i}) \<and> {f,g} \<in> twos (restr F {a,c} {b,h,i})")
    case True
    then have "\<exists>k'. fam_le k' T2d \<and> infam k' (restr F {a,c} {b,h,i})"
      using infam_2[OF _ _ pd(1) npr] by blast
    then show ?thesis by blast
  next
    case False
    then show ?thesis using p1 p2 by blast
  qed
  have r3: "{h,i} \<in> twos (restr F {a,b} {c})" by (rule two_mem[OF K(3)]) (use dd abc dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil r1 r2 fam_two[OF r3] fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF K(3)] dist dd abc in auto)
next
  case 2
  have "(a \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X \<and> h \<notin> X \<and> i \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    have ch: "h \<notin> X \<and> i \<notin> X" if "c \<in> X" "a \<in> X"
    proof -
      have e1: "{c,h,i} \<inter> X = {c}" by (rule crit_other[OF X that(1) oc, of a]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of h] single_out[OF e1, of i] dd by auto
    qed
    show ?thesis using h ex ch by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist dd abc by (simp add: ratio_simps)
qed

text \<open>Case 2: a variable \<open>d\<close> in all three pairs: \<open>{b,d,e}\<close>, \<open>{b,d,g}\<close>, \<open>{c,d,h}\<close>.\<close>

lemma p2o8_com:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,d,e} \<in> F" "{b,d,g} \<in> F" "{c,d,h} \<in> F" and dist: "distinct [a,b,c,d,e,g,h]"
    and oc: "\<And>D. D \<in> F \<Longrightarrow> c \<in> D \<Longrightarrow> D = {a,c} \<or> D = {c,d,h}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a,e,g,h},{b,c,d},T0), ({a,d},{b,c},T0), ({a,c},{b,d,h},T2d),
    ({a,b},{c},T1), ({b,c},{a},T0)]"], goal_cases)
  case 1
  have "{b,d,e} - {b,d,h} \<in> restr F {a,c} {b,d,h}" by (rule restr_mem[OF K(1)]) (use dist in auto)
  moreover have "{b,d,e} - {b,d,h} = {e}" using dist by auto
  ultimately have r3: "fam_ok T2d (restr F {a,c} {b,d,h})" by (metis card.empty card_insert_disjoint
      empty_iff finite.emptyI le_numeral_extra(4) One_nat_def)
  have r4: "{d,h} \<in> twos (restr F {a,b} {c})" by (rule two_mem[OF K(3)]) (use dist in auto)
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil r3 fam_two[OF r4] fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF K(1)] sub[OF K(2)] sub[OF K(3)] dist in auto)
next
  case 2
  have "(a \<in> X \<and> e \<in> X \<and> g \<in> X \<and> h \<in> X \<and> b \<notin> X \<and> c \<notin> X \<and> d \<notin> X) \<or> (a \<in> X \<and> d \<in> X \<and> b \<notin> X \<and> c \<notin> X)
      \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X \<and> d \<notin> X \<and> h \<notin> X) \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X)
      \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X" "b \<in> X \<or> d \<in> X \<or> e \<in> X" "b \<in> X \<or> d \<in> X \<or> g \<in> X"
      "c \<in> X \<or> d \<in> X \<or> h \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X K(1)] hit[OF X K(2)] hit[OF X K(3)] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    have cdh: "d \<notin> X \<and> h \<notin> X" if "c \<in> X" "a \<in> X"
    proof -
      have e1: "{c,d,h} \<inter> X = {c}" by (rule crit_other[OF X that(1) oc, of a]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of d] single_out[OF e1, of h] dist by auto
    qed
    show ?thesis using h ex cdh by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X"; cases "d \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,9)\<close>: \<open>b\<close> and \<open>c\<close> lie only in \<open>{a,b}\<close>, \<open>{a,c}\<close>, \<open>{b,c,d}\<close>.  Case 1: \<open>d\<close> lies in no
  other clause.\<close>

lemma p2o9_uniq:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,c,d} \<in> F" and dist: "distinct [a,b,c,d]"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {a,b} \<or> D = {b,c,d}"
    and oc: "\<And>D. D \<in> F \<Longrightarrow> c \<in> D \<Longrightarrow> D = {a,c} \<or> D = {b,c,d}"
    and od: "\<And>D. D \<in> F \<Longrightarrow> d \<in> D \<Longrightarrow> D = {b,c,d}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a,d},{b,c},T0), ({a,c},{b,d},T0), ({a,b},{c,d},T0), ({b,c},{a,d},T0)]"],
    goal_cases)
  case 1
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_in) (use sub[OF T(1)] sub[OF T(2)] sub[OF K] dist in auto)
next
  case 2
  have "(a \<in> X \<and> d \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X \<and> d \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X \<and> d \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X \<and> d \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X" "b \<in> X \<or> c \<in> X \<or> d \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X K] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    have cX: "d \<notin> X" if "c \<in> X" "a \<in> X"
    proof -
      have e1: "{b,c,d} \<inter> X = {c}" by (rule crit_other[OF X that(1) oc, of a]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of d] dist by auto
    qed
    have bX: "c \<notin> X \<and> d \<notin> X" if "b \<in> X" "a \<in> X"
    proof -
      have e1: "{b,c,d} \<inter> X = {b}" by (rule crit_other[OF X that(1) ob, of a]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of c] single_out[OF e1, of d] dist by auto
    qed
    have dX: "d \<notin> X" if "b \<in> X"
    proof
      assume d: "d \<in> X"
      have e1: "{b,c,d} \<inter> X = {d}" using only_clause[OF X d od] .
      show False using single_out[OF e1, of b] that dist by auto
    qed
    show ?thesis using h ex cX bX dX by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>Case 2: \<open>d\<close> lies in a further clause \<open>D\<^sub>d\<close>.\<close>

lemma p2o9_other:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,c,d} \<in> F" and dist: "distinct [a,b,c,d]"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {a,b} \<or> D = {b,c,d}"
    and oc: "\<And>D. D \<in> F \<Longrightarrow> c \<in> D \<Longrightarrow> D = {a,c} \<or> D = {b,c,d}"
    and Dd: "Dd \<in> F" "d \<in> Dd" "Dd \<noteq> {b,c,d}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a,d},{b,c},T0), ({a,c},{b,d},T1), ({a,b},{c,d},T1), ({b,c},{a},T0)]"],
    goal_cases)
  case 1
  have aD: "a \<notin> Dd"
  proof
    assume "a \<in> Dd"
    then have "Dd = {a,b} \<or> Dd = {a,c}" by (rule oa[OF Dd(1)])
    then show False using Dd(2) dist by auto
  qed
  have bD: "b \<notin> Dd"
  proof
    assume "b \<in> Dd"
    then have "Dd = {a,b} \<or> Dd = {b,c,d}" by (rule ob[OF Dd(1)])
    then show False using Dd(2,3) dist by auto
  qed
  have cD: "c \<notin> Dd"
  proof
    assume "c \<in> Dd"
    then have "Dd = {a,c} \<or> Dd = {b,c,d}" by (rule oc[OF Dd(1)])
    then show False using Dd(2,3) dist by auto
  qed
  have "Dd - {d} \<in> twos (restr F {a,c} {b,d}) \<or> (\<exists>C\<in>restr F {a,c} {b,d}. card C \<le> 1)"
    by (rule del_cases[OF Dd(1) Dd(2)]) (use aD bD cD in auto)
  then have r2: "fam_ok T1 (restr F {a,c} {b,d})" using fam_two by blast
  have "Dd - {d} \<in> twos (restr F {a,b} {c,d}) \<or> (\<exists>C\<in>restr F {a,b} {c,d}. card C \<le> 1)"
    by (rule del_cases[OF Dd(1) Dd(2)]) (use aD bD cD in auto)
  then have r3: "fam_ok T1 (restr F {a,b} {c,d})" using fam_two by blast
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil r2 r3 fam_in) (use sub[OF T(1)] sub[OF T(2)] sub[OF K] dist in auto)
next
  case 2
  have "(a \<in> X \<and> d \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X \<and> d \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X \<and> d \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X" "b \<in> X \<or> c \<in> X \<or> d \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X K] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    have cX: "d \<notin> X" if "c \<in> X" "a \<in> X"
    proof -
      have e1: "{b,c,d} \<inter> X = {c}" by (rule crit_other[OF X that(1) oc, of a]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of d] dist by auto
    qed
    have bX: "c \<notin> X \<and> d \<notin> X" if "b \<in> X" "a \<in> X"
    proof -
      have e1: "{b,c,d} \<inter> X = {b}" by (rule crit_other[OF X that(1) ob, of a]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of c] single_out[OF e1, of d] dist by auto
    qed
    show ?thesis using h ex cX bX by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

text \<open>\<open>\<P>(2o,10)\<close>: \<open>b\<close> and \<open>c\<close> each lie in one further clause, \<open>{b,d,e}\<close> and \<open>{c,f,g}\<close>, and in no
  common clause.  The pairs may meet or coincide.\<close>

lemma p2o10:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and ev: "even s"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,d,e} \<in> F" "{c,f,g} \<in> F" and dist: "distinct [a,b,c,d,e]" and fg: "a \<notin> {f,g}" "b \<notin> {f,g}"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {a,b} \<or> D = {b,d,e}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof (rule table[where rs = "[({a},{b},T1), ({a,b},{c,d,e},T1), ({b,c},{a},T0)]"], goal_cases)
  case 1
  have r1: "{d,e} \<in> twos (restr F {a} {b})" by (rule two_mem[OF K(1)]) (use dist in auto)
  have "{c,f,g} - {c,d,e} \<in> twos (restr F {a,b} {c,d,e}) \<or> (\<exists>C\<in>restr F {a,b} {c,d,e}. card C \<le> 1)"
    by (rule del_le[OF K(2), of _ c]) (use fg dist in auto)
  then have r2: "fam_ok T1 (restr F {a,b} {c,d,e})" using fam_two by blast
  show ?case
    by (intro rows_ok_ConsI rows_ok_Nil fam_two[OF r1] r2 fam_in)
      (use sub[OF T(1)] sub[OF T(2)] sub[OF K(1)] dist in auto)
next
  case 2
  have "(a \<in> X \<and> b \<notin> X) \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X \<and> d \<notin> X \<and> e \<notin> X) \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X" "a \<in> X \<or> c \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] by auto
    have ab: "a \<noteq> b" "a \<noteq> c" using dist by auto
    have ex: "b \<notin> X \<or> c \<notin> X" if "a \<in> X" using a_excl[OF X that ab oa] .
    have bde: "d \<notin> X \<and> e \<notin> X" if "b \<in> X" "a \<in> X"
    proof -
      have e1: "{b,d,e} \<inter> X = {b}" by (rule crit_other[OF X that(1) ob, of a]) (use that dist in auto)
      show ?thesis using single_out[OF e1, of d] single_out[OF e1, of e] dist by auto
    qed
    show ?thesis using h ex bde by (cases "a \<in> X"; cases "b \<in> X") auto
  qed
  then show ?case by auto
next
  case 3
  show ?case using ev dist by (simp add: ratio_simps)
qed

subsubsection \<open>Type 2o: choosing the configuration\<close>

lemma side3:
  assumes n3: "\<not> infam T3 F" and n4: "\<not> infam T4 F" and np: "npair F"
    and T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and C: "C \<in> F" "b \<in> C" "C \<noteq> {a,b}"
  shows "card C = 3 \<and> a \<notin> C"
proof -
  have nac: "C \<noteq> {a,c}" using C(2) dist by auto
  have "card C = 3" using no34_three[OF n3 n4 np T dist C(1) C(2) _ C(3) nac] by simp
  moreover have "a \<notin> C"
  proof
    assume "a \<in> C"
    then have "C = {a,b} \<or> C = {a,c}" by (rule oa[OF C(1)])
    then show False using C(3) nac by blast
  qed
  ultimately show ?thesis by blast
qed

text \<open>One clause \<open>{b,c,d}\<close> through both, and a further clause through \<open>b\<close>: P2o.5 and the case the
  paper misses.\<close>

lemma p2o_E5:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]" and ev: "even s" and np: "npair F"
    and n3: "\<not> infam T3 F" and n4: "\<not> infam T4 F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and K: "{b,c,d} \<in> F" "distinct [a,b,c,d]"
    and bc1: "\<And>C. C \<in> F \<Longrightarrow> b \<in> C \<Longrightarrow> c \<in> C \<Longrightarrow> C = {b,c,d}"
    and Db: "Db \<in> F" "b \<in> Db" "Db \<noteq> {a,b}" "Db \<noteq> {b,c,d}"
    and nb: "card {C\<in>F. b \<in> C \<and> C \<noteq> {a,b}} \<le> 2"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof -
  have sD: "card Db = 3 \<and> a \<notin> Db" by (rule side3[OF n3 n4 np T dist oa Db(1-3)])
  have cDb: "c \<notin> Db" using bc1[OF Db(1) Db(2)] Db(4) by blast
  obtain e f where ef: "Db = {b,e,f}" "distinct [b,e,f]"
    by (rule elems3[OF Db(1) conjunct1[OF sD] Db(2)])
  have efo: "e \<notin> {a,b,c}" "f \<notin> {a,b,c}" using ef sD cDb by auto
  have Kab: "{b,c,d} \<noteq> {a,b}"
  proof
    assume e: "{b,c,d} = {a,b}"
    have "c \<in> {b,c,d}" by simp
    then have "c \<in> {a,b}" unfolding e .
    then show False using dist by auto
  qed
  have KD: "{b,c,d} \<noteq> Db" using Db(4) by blast
  have S: "{{b,c,d}, Db} = {C\<in>F. b \<in> C \<and> C \<noteq> {a,b}}"
  proof (rule card_seteq)
    show "finite {C\<in>F. b \<in> C \<and> C \<noteq> {a,b}}" using finF by simp
    show "{{b,c,d}, Db} \<subseteq> {C\<in>F. b \<in> C \<and> C \<noteq> {a,b}}" using K(1) Kab Db by auto
    have "card {{b,c,d}, Db} = 2" using KD by simp
    then show "card {C\<in>F. b \<in> C \<and> C \<noteq> {a,b}} \<le> card {{b,c,d}, Db}" using nb by simp
  qed
  have ob: "D = {a,b} \<or> D = {b,c,d} \<or> D = Db" if "D \<in> F" "b \<in> D" for D
  proof (cases "D = {a,b}")
    case False
    then have "D \<in> {{b,c,d}, Db}" unfolding S using that by blast
    then show ?thesis by blast
  qed blast
  show ?thesis
  proof (cases "d \<in> {e,f}")
    case True
    obtain f' where f': "Db = {b,d,f'}" "f' \<notin> {a,b,c,d}"
    proof (cases "d = e")
      case True
      then show ?thesis using that[of f] ef efo K(2) by auto
    next
      case False
      then have "d = f" using \<open>d \<in> {e,f}\<close> by blast
      then show ?thesis using that[of e] ef efo K(2) by (auto simp: insert_commute)
    qed
    have d5: "distinct [a,b,c,d,f']" using K(2) f'(2) by auto
    have ob': "D = {a,b} \<or> D = {b,c,d} \<or> D = {b,d,f'}" if "D \<in> F" "b \<in> D" for D
      using ob[OF that] f'(1) by simp
    have Df: "{b,d,f'} \<in> F" using Db(1) f'(1) by simp
    show ?thesis by (rule p2o5_shared[OF T ev np oa K(1) Df d5 ob'])
  next
    case False
    have d6: "distinct [a,b,c,d,e,f]" using K(2) efo ef(2) False by auto
    have Db': "{b,e,f} \<in> F" using Db(1) ef(1) by simp
    show ?thesis
    proof (cases "\<exists>Dc\<in>F. c \<in> Dc \<and> Dc \<noteq> {a,c} \<and> Dc \<noteq> {b,c,d}")
      case True
      then obtain Dc where Dc: "Dc \<in> F" "c \<in> Dc" "Dc \<noteq> {a,c}" "Dc \<noteq> {b,c,d}" by blast
      have dist': "distinct [a,c,b]" using dist by auto
      have oa': "D = {a,c} \<or> D = {a,b}" if "D \<in> F" "a \<in> D" for D using oa[OF that] by blast
      have sC: "card Dc = 3 \<and> a \<notin> Dc" by (rule side3[OF n3 n4 np T(2) T(1) dist' oa' Dc(1-3)])
      have bDc: "b \<notin> Dc" using bc1[OF Dc(1) _ Dc(2)] Dc(4) by blast
      obtain g h where gh: "Dc = {c,g,h}" "distinct [c,g,h]"
        by (rule elems3[OF Dc(1) conjunct1[OF sC] Dc(2)])
      have gh5: "distinct [a,b,c,g,h]" using gh sC bDc dist by auto
      have Dc': "{c,g,h} \<in> F" using Dc(1) gh(1) by simp
      show ?thesis by (rule p2o5_sep[OF T ev oa K(1) Db' Dc' d6 gh5])
    next
      case False
      have oc: "D = {a,c} \<or> D = {b,c,d}" if "D \<in> F" "c \<in> D" for D using False that by blast
      show ?thesis by (rule p2o5_gap[OF T ev oa K(1) Db' d6 oc])
    qed
  qed
qed

text \<open>No clause through both, and two further clauses through \<open>b\<close>: P2o.6, P2o.7, P2o.8.\<close>

lemma p2o_E6:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]" and ev: "even s" and np: "npair F"
    and n3: "\<not> infam T3 F" and n4: "\<not> infam T4 F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
    and nbc: "\<And>C. C \<in> F \<Longrightarrow> b \<in> C \<Longrightarrow> c \<notin> C"
    and B2: "D1 \<in> F" "D2 \<in> F" "b \<in> D1" "b \<in> D2" "D1 \<noteq> D2" "D1 \<noteq> {a,b}" "D2 \<noteq> {a,b}"
    and Dc: "Dc \<in> F" "c \<in> Dc" "Dc \<noteq> {a,c}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof -
  have dist': "distinct [a,c,b]" using dist by auto
  have oa': "D = {a,c} \<or> D = {a,b}" if "D \<in> F" "a \<in> D" for D using oa[OF that] by blast
  have s1: "card D1 = 3 \<and> a \<notin> D1" by (rule side3[OF n3 n4 np T dist oa B2(1) B2(3) B2(6)])
  have s2: "card D2 = 3 \<and> a \<notin> D2" by (rule side3[OF n3 n4 np T dist oa B2(2) B2(4) B2(7)])
  have sC: "card Dc = 3 \<and> a \<notin> Dc" by (rule side3[OF n3 n4 np T(2) T(1) dist' oa' Dc])
  obtain d e where de: "D1 = {b,d,e}" "distinct [b,d,e]" by (rule elems3[OF B2(1) conjunct1[OF s1] B2(3)])
  obtain f g where fg: "D2 = {b,f,g}" "distinct [b,f,g]" by (rule elems3[OF B2(2) conjunct1[OF s2] B2(4)])
  obtain h i where hi: "Dc = {c,h,i}" "distinct [c,h,i]" by (rule elems3[OF Dc(1) conjunct1[OF sC] Dc(2)])
  have c1: "c \<notin> D1" "c \<notin> D2" using nbc B2 by blast+
  have bDc: "b \<notin> Dc" using nbc[OF Dc(1)] Dc(2) by blast
  have abc: "{d,e,f,g} \<inter> {a,c} = {}" using de fg s1 s2 c1 by auto
  have abc2: "{h,i} \<inter> {a,b} = {}" using hi sC bDc by auto
  have K: "{b,d,e} \<in> F" "{b,f,g} \<in> F" "{c,h,i} \<in> F" using B2(1,2) Dc(1) de(1) fg(1) hi(1) by simp_all
  have p12: "{d,e} \<noteq> {f,g}"
  proof
    assume "{d,e} = {f,g}"
    then have "D1 = D2" using de(1) fg(1) by simp
    then show False using B2(5) by blast
  qed
  show ?thesis
  proof (cases "{c,d,e} \<in> F \<or> {c,f,g} \<in> F")
    case True
    then show ?thesis
    proof
      assume E: "{c,d,e} \<in> F"
      have d5: "distinct [a,b,c,d,e]" using de(2) abc dist by auto
      have fgd: "distinct [b,f,g]" "a \<notin> {f,g}" "{f,g} \<noteq> {d,e}" using fg(2) abc p12 by auto
      show ?thesis by (rule p2o6[OF T ev np oa K(1) E K(2) d5 fgd])
    next
      assume E: "{c,f,g} \<in> F"
      have d5: "distinct [a,b,c,f,g]" using fg(2) abc dist by auto
      have fgd: "distinct [b,d,e]" "a \<notin> {d,e}" "{d,e} \<noteq> {f,g}" using de(2) abc p12 by auto
      show ?thesis by (rule p2o6[OF T ev np oa K(2) E K(1) d5 fgd])
    qed
  next
    case n6: False
    have hne: "{d,e} \<noteq> {h,i}" "{f,g} \<noteq> {h,i}"
    proof -
      show "{d,e} \<noteq> {h,i}"
      proof
        assume "{d,e} = {h,i}"
        then have "{c,d,e} = Dc" using hi(1) by simp
        then show False using n6 Dc(1) by blast
      qed
      show "{f,g} \<noteq> {h,i}"
      proof
        assume "{f,g} = {h,i}"
        then have "{c,f,g} = Dc" using hi(1) by simp
        then show False using n6 Dc(1) by blast
      qed
    qed
    show ?thesis
    proof (cases "\<exists>Dc'\<in>F. c \<in> Dc' \<and> Dc' \<noteq> {a,c} \<and> Dc' \<noteq> Dc")
      case True
      then obtain Dc' where Dc': "Dc' \<in> F" "c \<in> Dc'" "Dc' \<noteq> {a,c}" "Dc' \<noteq> Dc" by blast
      have sC': "card Dc' = 3 \<and> a \<notin> Dc'" by (rule side3[OF n3 n4 np T(2) T(1) dist' oa' Dc'(1-3)])
      obtain j k where jk: "Dc' = {c,j,k}" "distinct [c,j,k]"
        by (rule elems3[OF Dc'(1) conjunct1[OF sC'] Dc'(2)])
      have bDc': "b \<notin> Dc'" using nbc[OF Dc'(1)] Dc'(2) by blast
      have abc': "{h,i,j,k} \<inter> {a,b} = {}" using hi jk sC sC' bDc bDc' by auto
      have hne2: "{d,e} \<noteq> {j,k}" "{f,g} \<noteq> {j,k}" "{h,i} \<noteq> {j,k}"
      proof -
        show "{d,e} \<noteq> {j,k}"
        proof
          assume "{d,e} = {j,k}"
          then have "{c,d,e} = Dc'" using jk(1) by simp
          then show False using n6 Dc'(1) by blast
        qed
        show "{f,g} \<noteq> {j,k}"
        proof
          assume "{f,g} = {j,k}"
          then have "{c,f,g} = Dc'" using jk(1) by simp
          then show False using n6 Dc'(1) by blast
        qed
        show "{h,i} \<noteq> {j,k}"
        proof
          assume "{h,i} = {j,k}"
          then have "Dc = Dc'" using hi(1) jk(1) by simp
          then show False using Dc'(4) by blast
        qed
      qed
      have K4: "{c,j,k} \<in> F" using Dc'(1) jk(1) by simp
      show ?thesis
        by (rule p2o7[OF T ev np oa K K4 dist de(2) fg(2) hi(2) jk(2) abc abc' p12 hne(1) hne2(1)
              hne(2) hne2(2) hne2(3)])
    next
      case False
      have oc: "D = {a,c} \<or> D = {c,h,i}" if "D \<in> F" "c \<in> D" for D using False that hi(1) by blast
      show ?thesis
      proof (cases "\<exists>x. x \<in> {d,e} \<and> x \<in> {f,g} \<and> x \<in> {h,i}")
        case True
        then obtain x where x: "x \<in> {d,e}" "x \<in> {f,g}" "x \<in> {h,i}" by blast
        have xD: "x \<in> D1" "x \<in> D2" "x \<in> Dc" using x de(1) fg(1) hi(1) by auto
        have xb: "b \<noteq> x" "c \<noteq> x" using x de(2) fg(2) hi(2) by auto
        obtain e' where e': "D1 = {b,x,e'}" "e' \<noteq> b" "e' \<noteq> x"
          using form3[OF B2(1) conjunct1[OF s1] B2(3) xD(1) xb(1)] by blast
        obtain g' where g': "D2 = {b,x,g'}" "g' \<noteq> b" "g' \<noteq> x"
          using form3[OF B2(2) conjunct1[OF s2] B2(4) xD(2) xb(1)] by blast
        obtain h' where h': "Dc = {c,x,h'}" "h' \<noteq> c" "h' \<noteq> x"
          using form3[OF Dc(1) conjunct1[OF sC] Dc(2) xD(3) xb(2)] by blast
        have r1: "{d,e} = D1 - {b}" "{x,e'} = D1 - {b}"
          subgoal using de by auto
          subgoal using e' xb by auto
          done
        have r2: "{f,g} = D2 - {b}" "{x,g'} = D2 - {b}"
          subgoal using fg by auto
          subgoal using g' xb by auto
          done
        have r3: "{h,i} = Dc - {c}" "{x,h'} = Dc - {c}"
          subgoal using hi by auto
          subgoal using h' xb by auto
          done
        have ee: "e' \<noteq> g'" using e'(1) g'(1) B2(5) by blast
        have eh: "e' \<noteq> h'"
        proof
          assume "e' = h'"
          then have "{d,e} = {h,i}" using r1 r3 by simp
          then show False using hne(1) by blast
        qed
        have gh: "g' \<noteq> h'"
        proof
          assume "g' = h'"
          then have "{f,g} = {h,i}" using r2 r3 by simp
          then show False using hne(2) by blast
        qed
        have d7: "distinct [a,b,c,x,e',g',h']"
          using dist xb e' g' h' ee eh gh s1 s2 sC c1 bDc xD by auto
        have Kx: "{b,x,e'} \<in> F" "{b,x,g'} \<in> F" "{c,x,h'} \<in> F" using B2(1,2) Dc(1) e'(1) g'(1) h'(1) by simp_all
        have oc': "D = {a,c} \<or> D = {c,x,h'}" if "D \<in> F" "c \<in> D" for D using oc[OF that] hi(1) h'(1) by simp
        show ?thesis by (rule p2o8_com[OF T ev oa Kx d7 oc'])
      next
        case False
        show ?thesis
          by (rule p2o8_sep[OF T ev np oa K dist de(2) fg(2) hi(2) abc abc2 p12 hne False oc])
      qed
    qed
  qed
qed

lemma p2o_even:
  assumes T: "{a,b} \<in> F" "{a,c} \<in> F" and dist: "distinct [a,b,c]" and ev: "even s" and np: "npair F"
    and n3: "\<not> infam T3 F" and n4: "\<not> infam T4 F"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b} \<or> D = {a,c}"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof -
  have dist': "distinct [a,c,b]" using dist by auto
  have oa': "D = {a,c} \<or> D = {a,b}" if "D \<in> F" "a \<in> D" for D using oa[OF that] by blast
  define B where "B = {C\<in>F. b \<in> C \<and> C \<noteq> {a,b}}"
  define Cc where "Cc = {C\<in>F. c \<in> C \<and> C \<noteq> {a,c}}"
  show ?thesis
  proof (cases "3 \<le> card B")
    case True
    obtain D1 D2 D3 where D: "D1 \<in> B" "D2 \<in> B" "D3 \<in> B" "D1 \<noteq> D2" "D1 \<noteq> D3" "D2 \<noteq> D3"
      using card3_obtain[OF True] by blast
    show ?thesis by (rule p2o2[OF T dist ev np oa]) (use D in \<open>auto simp: B_def\<close>)
  next
    case nB3: False
    show ?thesis
    proof (cases "3 \<le> card Cc")
      case True
      obtain D1 D2 D3 where D: "D1 \<in> Cc" "D2 \<in> Cc" "D3 \<in> Cc" "D1 \<noteq> D2" "D1 \<noteq> D3" "D2 \<noteq> D3"
        using card3_obtain[OF True] by blast
      show ?thesis by (rule p2o2[OF T(2) T(1) dist' ev np oa']) (use D in \<open>auto simp: Cc_def\<close>)
    next
      case nC3: False
      have nb: "card {C\<in>F. b \<in> C \<and> C \<noteq> {a,b}} \<le> 2" using nB3 unfolding B_def by simp
      have nc: "card {C\<in>F. c \<in> C \<and> C \<noteq> {a,c}} \<le> 2" using nC3 unfolding Cc_def by simp
      show ?thesis
      proof (cases "B = {}")
        case True
        have ob: "D = {a,b}" if "D \<in> F" "b \<in> D" for D using True that unfolding B_def by blast
        show ?thesis by (rule p2o3[OF T dist ev ob])
      next
        case nB0: False
        show ?thesis
        proof (cases "Cc = {}")
          case True
          have oc: "D = {a,c}" if "D \<in> F" "c \<in> D" for D using True that unfolding Cc_def by blast
          show ?thesis by (rule p2o3[OF T(2) T(1) dist' ev oc])
        next
          case nC0: False
          show ?thesis
          proof (cases "\<exists>K\<in>F. b \<in> K \<and> c \<in> K")
            case True
            then obtain K where K: "K \<in> F" "b \<in> K" "c \<in> K" by blast
            have Kab: "K \<noteq> {a,b}" using K(3) dist by auto
            have sK: "card K = 3 \<and> a \<notin> K" by (rule side3[OF n3 n4 np T dist oa K(1) K(2) Kab])
            have bc: "b \<noteq> c" using dist by simp
            obtain d where d: "K = {b,c,d}" "d \<noteq> b" "d \<noteq> c"
              using form3[OF K(1) conjunct1[OF sK] K(2) K(3) bc] by blast
            have K4: "distinct [a,b,c,d]" using dist d sK by auto
            have Kd: "{b,c,d} \<in> F" using K(1) d(1) by simp
            show ?thesis
            proof (cases "\<exists>K'\<in>F. b \<in> K' \<and> c \<in> K' \<and> K' \<noteq> {b,c,d}")
              case True
              then obtain K' where K': "K' \<in> F" "b \<in> K'" "c \<in> K'" "K' \<noteq> {b,c,d}" by blast
              have K'ab: "K' \<noteq> {a,b}" using K'(3) dist by auto
              have sK': "card K' = 3 \<and> a \<notin> K'" by (rule side3[OF n3 n4 np T dist oa K'(1) K'(2) K'ab])
              obtain e where e: "K' = {b,c,e}" "e \<noteq> b" "e \<noteq> c"
                using form3[OF K'(1) conjunct1[OF sK'] K'(2) K'(3) bc] by blast
              have "d \<noteq> e" using d(1) e(1) K'(4) by blast
              then have d5: "distinct [a,b,c,d,e]" using K4 e sK' by auto
              have Ke: "{b,c,e} \<in> F" using K'(1) e(1) by simp
              show ?thesis by (rule p2o4[OF T d5 ev Kd Ke oa])
            next
              case False
              have bc1: "C = {b,c,d}" if "C \<in> F" "b \<in> C" "c \<in> C" for C using False that by blast
              show ?thesis
              proof (cases "\<exists>Db\<in>F. b \<in> Db \<and> Db \<noteq> {a,b} \<and> Db \<noteq> {b,c,d}")
                case True
                then obtain Db where Db: "Db \<in> F" "b \<in> Db" "Db \<noteq> {a,b}" "Db \<noteq> {b,c,d}" by blast
                show ?thesis by (rule p2o_E5[OF T dist ev np n3 n4 oa Kd K4 bc1 Db nb])
              next
                case nDb: False
                show ?thesis
                proof (cases "\<exists>Dc\<in>F. c \<in> Dc \<and> Dc \<noteq> {a,c} \<and> Dc \<noteq> {b,c,d}")
                  case True
                  then obtain Dc where Dc: "Dc \<in> F" "c \<in> Dc" "Dc \<noteq> {a,c}" "Dc \<noteq> {c,b,d}"
                    by (auto simp: insert_commute)
                  have Kd': "{c,b,d} \<in> F" using Kd by (simp add: insert_commute)
                  have K4': "distinct [a,c,b,d]" using K4 by auto
                  have bc1': "C = {c,b,d}" if "C \<in> F" "c \<in> C" "b \<in> C" for C
                    using bc1[OF that(1,3,2)] by (simp add: insert_commute)
                  show ?thesis by (rule p2o_E5[OF T(2) T(1) dist' ev np n3 n4 oa' Kd' K4' bc1' Dc nc])
                next
                  case nDc: False
                  have ob: "D = {a,b} \<or> D = {b,c,d}" if "D \<in> F" "b \<in> D" for D using nDb that by blast
                  have oc: "D = {a,c} \<or> D = {b,c,d}" if "D \<in> F" "c \<in> D" for D using nDc that by blast
                  show ?thesis
                  proof (cases "\<forall>D\<in>F. d \<in> D \<longrightarrow> D = {b,c,d}")
                    case True
                    have od: "D = {b,c,d}" if "D \<in> F" "d \<in> D" for D using True that by blast
                    show ?thesis by (rule p2o9_uniq[OF T ev oa Kd K4 ob oc od])
                  next
                    case False
                    then obtain Dd where Dd: "Dd \<in> F" "d \<in> Dd" "Dd \<noteq> {b,c,d}" by blast
                    show ?thesis by (rule p2o9_other[OF T ev oa Kd K4 ob oc Dd])
                  qed
                qed
              qed
            qed
          next
            case False
            have nbc: "c \<notin> C" if "C \<in> F" "b \<in> C" for C using False that by blast
            have ncb: "b \<notin> C" if "C \<in> F" "c \<in> C" for C using False that by blast
            obtain Db where Db: "Db \<in> B" using nB0 by blast
            obtain Dc where Dc: "Dc \<in> Cc" using nC0 by blast
            show ?thesis
            proof (cases "\<exists>D1 D2. D1 \<in> B \<and> D2 \<in> B \<and> D1 \<noteq> D2")
              case True
              then obtain D1 D2 where D: "D1 \<in> B" "D2 \<in> B" "D1 \<noteq> D2" by blast
              have D': "D1 \<in> F" "D2 \<in> F" "b \<in> D1" "b \<in> D2" "D1 \<noteq> D2" "D1 \<noteq> {a,b}" "D2 \<noteq> {a,b}"
                using D unfolding B_def by auto
              have Dc': "Dc \<in> F" "c \<in> Dc" "Dc \<noteq> {a,c}" using Dc unfolding Cc_def by auto
              show ?thesis by (rule p2o_E6[OF T dist ev np n3 n4 oa nbc D' Dc'])
            next
              case nB2: False
              show ?thesis
              proof (cases "\<exists>D1 D2. D1 \<in> Cc \<and> D2 \<in> Cc \<and> D1 \<noteq> D2")
                case True
                then obtain D1 D2 where D: "D1 \<in> Cc" "D2 \<in> Cc" "D1 \<noteq> D2" by blast
                have D': "D1 \<in> F" "D2 \<in> F" "c \<in> D1" "c \<in> D2" "D1 \<noteq> D2" "D1 \<noteq> {a,c}" "D2 \<noteq> {a,c}"
                  using D unfolding Cc_def by auto
                have Db': "Db \<in> F" "b \<in> Db" "Db \<noteq> {a,b}" using Db unfolding B_def by auto
                show ?thesis by (rule p2o_E6[OF T(2) T(1) dist' ev np n3 n4 oa' ncb D' Db'])
              next
                case nC2: False
                have Db': "Db \<in> F" "b \<in> Db" "Db \<noteq> {a,b}" using Db unfolding B_def by auto
                have Dc': "Dc \<in> F" "c \<in> Dc" "Dc \<noteq> {a,c}" using Dc unfolding Cc_def by auto
                have ob: "D = {a,b} \<or> D = Db" if "D \<in> F" "b \<in> D" for D
                  using nB2 Db that unfolding B_def by blast
                have sB: "card Db = 3 \<and> a \<notin> Db" by (rule side3[OF n3 n4 np T dist oa Db'])
                have sC: "card Dc = 3 \<and> a \<notin> Dc" by (rule side3[OF n3 n4 np T(2) T(1) dist' oa' Dc'])
                obtain d e where de: "Db = {b,d,e}" "distinct [b,d,e]"
                  by (rule elems3[OF Db'(1) conjunct1[OF sB] Db'(2)])
                obtain f g where fg: "Dc = {c,f,g}" "distinct [c,f,g]"
                  by (rule elems3[OF Dc'(1) conjunct1[OF sC] Dc'(2)])
                have d5: "distinct [a,b,c,d,e]" using dist de sB nbc[OF Db'(1,2)] by auto
                have fgo: "a \<notin> {f,g}" "b \<notin> {f,g}" using fg sC ncb[OF Dc'(1,2)] by auto
                have K: "{b,d,e} \<in> F" "{c,f,g} \<in> F" using Db'(1) Dc'(1) de(1) fg(1) by simp_all
                have ob': "D = {a,b} \<or> D = {b,d,e}" if "D \<in> F" "b \<in> D" for D using ob[OF that] de(1) by simp
                show ?thesis by (rule p2o10[OF T ev oa K d5 fgo ob'])
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

theorem type2o:
  assumes fam: "infam T2o F" and n3: "\<not> infam T3 F" and n4: "\<not> infam T4 F"
  shows "real (card (trans V F t)) \<le> bound T2o s t"
proof -
  obtain C D where CD: "C \<in> twos F" "D \<in> twos F" "C \<noteq> D" "C \<inter> D \<noteq> {}" and np: "npair F"
    using fam by auto
  obtain a where a: "a \<in> C" "a \<in> D" using CD(4) by blast
  have c2: "card C = 2" "card D = 2" using CD(1,2) by (simp_all add: twos_def)
  have fin: "finite C" "finite D" using c2 card.infinite by fastforce+
  have "card (C - {a}) = 1" using c2(1) a(1) fin(1) by simp
  then obtain b where b: "C - {a} = {b}" by (rule card_1_singletonE)
  have "card (D - {a}) = 1" using c2(2) a(2) fin(2) by simp
  then obtain c where c: "D - {a} = {c}" by (rule card_1_singletonE)
  have Cab: "C = {a,b}" using b a(1) by blast
  have Dac: "D = {a,c}" using c a(2) by blast
  have dist: "distinct [a,b,c]" using b c Cab Dac CD(3) by auto
  have T: "{a,b} \<in> F" "{a,c} \<in> F" using CD(1,2) Cab Dac by (simp_all add: twos_def)
  show ?thesis
  proof (cases "even s")
    case False
    then show ?thesis by (rule p2o_odd[OF T dist])
  next
    case ev: True
    show ?thesis
    proof (cases "\<exists>D\<in>F. a \<in> D \<and> D \<noteq> {a,b} \<and> D \<noteq> {a,c}")
      case True
      then obtain D where "D \<in> F" "a \<in> D" "D \<noteq> {a,b}" "D \<noteq> {a,c}" by blast
      then show ?thesis by (rule p2o1[OF T dist ev])
    next
      case False
      have oa: "D = {a,b} \<or> D = {a,c}" if "D \<in> F" "a \<in> D" for D using False that by blast
      show ?thesis by (rule p2o_even[OF T dist ev np n3 n4 oa])
    qed
  qed
qed

end

subsection \<open>Monotone 3-CNFs with no 2-clause\<close>

locale core0 = core +
  assumes three: "\<And>C. C \<in> F \<Longrightarrow> card C = 3"
begin

lemma three_form:
  assumes C: "C \<in> F" and xy: "x \<in> C" "y \<in> C" "x \<noteq> y"
  obtains z where "C = {x,y,z}" "z \<noteq> x" "z \<noteq> y"
proof -
  have fC: "finite C" using cnf_clause_finite[OF cnf C] .
  have "card (C - {x,y}) = card C - card {x,y}"
    using xy fC by (intro card_Diff_subset) auto
  then have "card (C - {x,y}) = 1" using three[OF C] xy(3) by simp
  then obtain z where z: "C - {x,y} = {z}" by (rule card_1_singletonE)
  then have "C = {x,y,z}" using xy by blast
  moreover have "z \<noteq> x" "z \<noteq> y" using z by auto
  ultimately show ?thesis using that by blast
qed

lemma del_two:
  assumes C: "C \<in> F" "a \<in> C" "C \<inter> J = {}"
  shows "C - {a} \<in> twos (restr F J {a})"
proof -
  have "card (C - {a}) = 2"
    using three[OF C(1)] C(2) cnf_clause_finite[OF cnf C(1)] by simp
  then show ?thesis using restr_mem[OF C(1) C(3)] by (simp add: twos_def)
qed

text \<open>\<open>\<P>(0,1)\<close>: a pair \<open>{a,b}\<close> lies in three clauses \<open>{a,b,c}\<close>, \<open>{a,b,d}\<close>, \<open>{a,b,e}\<close>.
  If \<open>a\<close> always occurs with \<open>b\<close>, setting \<open>a\<close> to 1 forces \<open>b\<close> to 0.\<close>

lemma p01_with:
  assumes C: "{a,b,c} \<in> F" "{a,b,d} \<in> F" "{a,b,e} \<in> F" and dist: "distinct [a,b,c,d,e]"
    and aw: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> b \<in> D"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof (rule table[where rs = "[({a},{b},T0), ({b},{a},T0), ({c,d,e},{a,b},T0)]"], goal_cases)
  case 1
  then show ?case using sub[OF C(1)] sub[OF C(2)] sub[OF C(3)] dist unfolding rows_ok_def by auto
next
  case 2
  have "a \<in> X \<and> b \<notin> X \<or> b \<in> X \<and> a \<notin> X \<or> {c,d,e} \<subseteq> X \<and> a \<notin> X \<and> b \<notin> X"
    if X: "X \<in> trans V F t" for X
  proof (cases "a \<in> X")
    case True
    then show ?thesis using forced_out[OF X True _ aw] dist by auto
  next
    case False
    then show ?thesis using hit[OF X C(1)] hit[OF X C(2)] hit[OF X C(3)] by auto
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>Otherwise some clause contains \<open>a\<close> but not \<open>b\<close>, and setting \<open>a = 0\<close>, \<open>b = 1\<close> leaves a
  2-clause.  The paper also assumes a clause with \<open>b\<close> but not \<open>a\<close>; it is not needed.\<close>

lemma p01_sep:
  assumes C: "{a,b,c} \<in> F" "{a,b,d} \<in> F" "{a,b,e} \<in> F" and dist: "distinct [a,b,c,d,e]"
    and D: "D \<in> F" "a \<in> D" "b \<notin> D"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof (rule table[where rs = "[({a},{},T0), ({b},{a},T1), ({c,d,e},{a,b},T0)]"], goal_cases)
  case 1
  have "D - {a} \<in> twos (restr F {b} {a})" using D by (intro del_two) auto
  then have "infam T1 (restr F {b} {a})" by auto
  then show ?case using sub[OF C(1)] sub[OF C(2)] sub[OF C(3)] dist unfolding rows_ok_def by auto
next
  case 2
  have "a \<in> X \<or> b \<in> X \<and> a \<notin> X \<or> {c,d,e} \<subseteq> X \<and> a \<notin> X \<and> b \<notin> X"
    if X: "X \<in> trans V F t" for X
    using hit[OF X C(1)] hit[OF X C(2)] hit[OF X C(3)] by auto
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

lemma p01:
  assumes "\<not> npair F"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof -
  obtain a b where ab: "a \<noteq> b" "\<not> card {C\<in>F. a \<in> C \<and> b \<in> C} \<le> 2"
    using assms unfolding npair_def by blast
  have "3 \<le> card {C\<in>F. a \<in> C \<and> b \<in> C}" using ab(2) by simp
  then obtain C1 C2 C3 where Cs: "C1 \<in> {C\<in>F. a \<in> C \<and> b \<in> C}" "C2 \<in> {C\<in>F. a \<in> C \<and> b \<in> C}"
      "C3 \<in> {C\<in>F. a \<in> C \<and> b \<in> C}" "C1 \<noteq> C2" "C1 \<noteq> C3" "C2 \<noteq> C3"
    by (rule card3_obtain)
  obtain c where c: "C1 = {a,b,c}" "c \<noteq> a" "c \<noteq> b" using three_form[of "C1" a b] Cs(1) ab(1) by blast
  obtain d where d: "C2 = {a,b,d}" "d \<noteq> a" "d \<noteq> b" using three_form[of "C2" a b] Cs(2) ab(1) by blast
  obtain e where e: "C3 = {a,b,e}" "e \<noteq> a" "e \<noteq> b" using three_form[of "C3" a b] Cs(3) ab(1) by blast
  have dist: "distinct [a,b,c,d,e]" using ab(1) c d e Cs(4-6) by auto
  have C: "{a,b,c} \<in> F" "{a,b,d} \<in> F" "{a,b,e} \<in> F" using Cs c d e by auto
  show ?thesis
  proof (cases "\<forall>D\<in>F. a \<in> D \<longrightarrow> b \<in> D")
    case True
    then show ?thesis using p01_with[OF C dist] by blast
  next
    case False
    then obtain D where "D \<in> F" "a \<in> D" "b \<notin> D" by blast
    then show ?thesis using p01_sep[OF C dist] by blast
  qed
qed

text \<open>\<open>\<P>(0,2)\<close>: a variable \<open>a\<close> in three clauses.  Setting \<open>a = 0\<close> turns its clauses into
  2-clauses; no three share a variable, since that variable would lie in three clauses with
  \<open>a\<close>.  If \<open>a\<close> is in four or more clauses the restriction has four or more 2-clauses, and it is
  still of type 3 in the paper's restricted sense.\<close>

lemma del_type3:
  assumes np: "npair F" and deg: "3 \<le> card {C\<in>F. a \<in> C}"
  shows "infam T3 (restr F {} {a})"
proof -
  let ?G = "restr F {} {a}"
  have finT: "finite (twos ?G)" using restr_finite by (simp add: twos_def)
  have img: "(\<lambda>C. C - {a}) ` {C\<in>F. a \<in> C} \<subseteq> twos ?G"
    using del_two by auto
  have inj: "inj_on (\<lambda>C. C - {a}) {C\<in>F. a \<in> C}"
  proof (rule inj_onI)
    fix C D assume "C \<in> {C\<in>F. a \<in> C}" "D \<in> {C\<in>F. a \<in> C}" "C - {a} = D - {a}"
    then have "insert a (C - {a}) = insert a (D - {a})" "a \<in> C" "a \<in> D" by auto
    then show "C = D" by (simp add: insert_absorb)
  qed
  have "3 \<le> card ((\<lambda>C. C - {a}) ` {C\<in>F. a \<in> C})" using deg card_image[OF inj] by simp
  also have "\<dots> \<le> card (twos ?G)" using card_mono[OF finT img] .
  finally have c3: "3 \<le> card (twos ?G)" .
  have deg2: "card {D\<in>twos ?G. x \<in> D} \<le> 2" for x
  proof (cases "x = a")
    case True
    then have e: "{D\<in>twos ?G. x \<in> D} = {}" by (auto simp: twos_def restr_def)
    show ?thesis unfolding e by simp
  next
    case False
    have "{D\<in>twos ?G. x \<in> D} \<subseteq> (\<lambda>C. C - {a}) ` {C\<in>F. a \<in> C \<and> x \<in> C}"
    proof
      fix D assume D: "D \<in> {D\<in>twos ?G. x \<in> D}"
      then obtain C where C: "C \<in> F" "D = C - {a}" "card D = 2" "x \<in> D"
        by (auto simp: twos_def restr_def)
      have "a \<in> C"
      proof (rule ccontr)
        assume "a \<notin> C"
        then have "D = C" using C(2) by simp
        then show False using C three by simp
      qed
      then show "D \<in> (\<lambda>C. C - {a}) ` {C\<in>F. a \<in> C \<and> x \<in> C}" using C by blast
    qed
    then have "card {D\<in>twos ?G. x \<in> D} \<le> card ((\<lambda>C. C - {a}) ` {C\<in>F. a \<in> C \<and> x \<in> C})"
      using finF by (intro card_mono) auto
    also have "\<dots> \<le> card {C\<in>F. a \<in> C \<and> x \<in> C}" using finF by (intro card_image_le) simp
    also have "\<dots> \<le> 2" using np False unfolding npair_def by (metis (no_types, lifting))
    finally show ?thesis .
  qed
  show ?thesis using c3 deg2 npair_restr[OF finF np] by simp
qed

lemma p02:
  assumes np: "npair F" and deg: "3 \<le> card {C\<in>F. a \<in> C}"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof (rule table[where rs = "[({a},{},T0), ({},{a},T3)]"], goal_cases)
  case 1
  obtain C where "C \<in> F" "a \<in> C" using deg by (metis (no_types, lifting) card.empty empty_Collect_eq not_numeral_le_zero)
  then have "a \<in> V" using sub by blast
  then show ?case using del_type3[OF np deg] unfolding rows_ok_def by auto
next
  case 2
  show ?case by auto
next
  case 3
  then show ?case by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>\<open>\<P>(0,3)\<close>: a pair \<open>{a,b}\<close> in exactly two clauses \<open>{a,b,c}\<close>, \<open>{a,b,d}\<close>; since \<open>\<P>(0,2)\<close>
  fails, \<open>a\<close> is in no other clause, so \<open>a = 1\<close> forces \<open>b = 0\<close>.\<close>

lemma p03:
  assumes np: "npair F" and deg: "\<And>x. card {C\<in>F. x \<in> C} \<le> 2"
    and C: "{a,b,c} \<in> F" "{a,b,d} \<in> F" and dist: "distinct [a,b,c,d]"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof (rule table[where rs = "[({a},{b},T0), ({},{a},T2o)]"], goal_cases)
  case 1
  have "{b,c} \<in> twos (restr F {} {a})" "{b,d} \<in> twos (restr F {} {a})"
    using del_two[OF C(1), of a "{}"] del_two[OF C(2), of a "{}"] dist
    by (simp_all add: insert_Diff_if)
  moreover have "{b,c} \<noteq> {b,d}" using dist by (auto simp: doubleton_eq_iff)
  ultimately have "infam T2o (restr F {} {a})" using npair_restr[OF finF np] by fastforce
  then show ?case using sub[OF C(1)] dist unfolding rows_ok_def by auto
next
  case 2
  have aC: "{{a,b,c},{a,b,d}} = {C\<in>F. a \<in> C}"
  proof (rule card_seteq)
    show "finite {C\<in>F. a \<in> C}" using finF by simp
    show "{{a,b,c},{a,b,d}} \<subseteq> {C\<in>F. a \<in> C}" using C by auto
    have "{a,b,c} \<noteq> {a,b,d}" using dist by auto
    then show "card {C\<in>F. a \<in> C} \<le> card {{a,b,c},{a,b,d}}" using deg[of a] by simp
  qed
  have aw: "b \<in> D" if "D \<in> F" "a \<in> D" for D
  proof -
    have "D \<in> {{a,b,c},{a,b,d}}" using aC that by blast
    then show ?thesis by auto
  qed
  have "a \<in> X \<and> b \<notin> X \<or> a \<notin> X" if X: "X \<in> trans V F t" for X
    using forced_out[OF X _ _ aw] dist by auto
  then show ?case by auto
next
  case 3
  then show ?case by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>
  \<open>\<P>(0,4)\<close>: a triangle \<open>{a,b,d}\<close>, \<open>{b,c,e}\<close>, \<open>{a,c,f}\<close>, each of \<open>a\<close>, \<open>b\<close>, \<open>c\<close> in no other
  clause.  Since \<open>\<P>(0,3)\<close> fails, \<open>d\<close>, \<open>e\<close>, \<open>f\<close> are distinct (\<open>d = e\<close> would put \<open>{b,d}\<close> in two
  clauses), so the rows with two of \<open>a\<close>, \<open>b\<close>, \<open>c\<close> set five variables, not four.

  \<^bold>\<open>Gap in the paper.\<close> Its table has no row for \<open>a = b = c = 0\<close>, which forces \<open>d = e = f = 1\<close>.
  Such transversals exist: in the prism (two triangles \<open>a b c\<close> and \<open>a' b' c'\<close> joined by
  \<open>d\<close>, \<open>e\<close>, \<open>f\<close>), \<open>{d,e,f}\<close> is a minimum transversal.  With the exact parameters the
  missing row fits: the sums are \<open>103/108\<close> and \<open>1\<close>.\<close>

lemma p04:
  assumes deg: "\<And>x. card {C\<in>F. x \<in> C} \<le> 2"
    and T: "{a,b,d} \<in> F" "{b,c,e} \<in> F" "{a,c,f} \<in> F" and dist: "distinct [a,b,c,d,e,f]"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof (rule table[where rs = "[({a,e},{b,c},T0), ({b,f},{a,c},T0), ({c,d},{a,b},T0),
    ({a,b},{c,e,f},T0), ({b,c},{a,d,f},T0), ({a,c},{b,d,e},T0), ({d,e,f},{a,b,c},T0)]"], goal_cases)
  case 1
  then show ?case using sub[OF T(1)] sub[OF T(2)] sub[OF T(3)] dist unfolding rows_ok_def by auto
next
  case 2
  have ne: "{a,b,d} \<noteq> {b,c,e}" "{a,b,d} \<noteq> {a,c,f}" "{b,c,e} \<noteq> {a,c,f}" using dist by auto
  have oa: "D = {a,b,d} \<or> D = {a,c,f}" if "D \<in> F" "a \<in> D" for D
    using two_only[OF deg T(1) T(3) _ _ ne(2) that] by simp
  have ob: "D = {a,b,d} \<or> D = {b,c,e}" if "D \<in> F" "b \<in> D" for D
    using two_only[OF deg T(1) T(2) _ _ ne(1) that] by simp
  have oc: "D = {b,c,e} \<or> D = {a,c,f}" if "D \<in> F" "c \<in> D" for D
    using two_only[OF deg T(2) T(3) _ _ ne(3) that] by simp
  have "(a \<in> X \<and> e \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (b \<in> X \<and> f \<in> X \<and> a \<notin> X \<and> c \<notin> X)
      \<or> (c \<in> X \<and> d \<in> X \<and> a \<notin> X \<and> b \<notin> X) \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X \<and> e \<notin> X \<and> f \<notin> X)
      \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X \<and> d \<notin> X \<and> f \<notin> X) \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X \<and> d \<notin> X \<and> e \<notin> X)
      \<or> (d \<in> X \<and> e \<in> X \<and> f \<in> X \<and> a \<notin> X \<and> b \<notin> X \<and> c \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X \<or> d \<in> X" "b \<in> X \<or> c \<in> X \<or> e \<in> X" "a \<in> X \<or> c \<in> X \<or> f \<in> X"
      using hit[OF X T(1)] hit[OF X T(2)] hit[OF X T(3)] by auto
    have ab: "c \<notin> X \<and> f \<notin> X \<and> e \<notin> X" if "a \<in> X" "b \<in> X"
    proof -
      have e1: "{a,c,f} \<inter> X = {a}" by (rule crit_other[OF X that(1) oa, of b]) (use dist that in auto)
      have e2: "{b,c,e} \<inter> X = {b}" by (rule crit_other[OF X that(2) ob, of a]) (use dist that in auto)
      show ?thesis using single_out[OF e1, of c] single_out[OF e1, of f] single_out[OF e2, of e] dist
        by auto
    qed
    have bc: "a \<notin> X \<and> d \<notin> X \<and> f \<notin> X" if "b \<in> X" "c \<in> X"
    proof -
      have e1: "{a,b,d} \<inter> X = {b}" by (rule crit_other'[OF X that(1) ob, of c]) (use dist that in auto)
      have e2: "{a,c,f} \<inter> X = {c}" by (rule crit_other[OF X that(2) oc, of b]) (use dist that in auto)
      show ?thesis using single_out[OF e1, of a] single_out[OF e1, of d] single_out[OF e2, of f] dist
        by auto
    qed
    have ac: "b \<notin> X \<and> d \<notin> X \<and> e \<notin> X" if "a \<in> X" "c \<in> X"
    proof -
      have e1: "{a,b,d} \<inter> X = {a}" by (rule crit_other'[OF X that(1) oa, of c]) (use dist that in auto)
      have e2: "{b,c,e} \<inter> X = {c}" by (rule crit_other'[OF X that(2) oc, of a]) (use dist that in auto)
      show ?thesis using single_out[OF e1, of b] single_out[OF e1, of d] single_out[OF e2, of e] dist
        by auto
    qed
    show ?thesis
      using h ab ac bc by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>\<open>\<P>(0,5)\<close>: an E configuration, spine \<open>{a,b,c}\<close> and pairwise disjoint arms \<open>{a,d,e}\<close>,
  \<open>{b,f,g}\<close>, \<open>{c,h,i}\<close>, with \<open>a\<close>, \<open>b\<close>, \<open>c\<close> in no other clause.\<close>

lemma p05:
  assumes deg: "\<And>x. card {C\<in>F. x \<in> C} \<le> 2" and np: "npair F"
    and T: "{a,b,c} \<in> F" "{a,d,e} \<in> F" "{b,f,g} \<in> F" "{c,h,i} \<in> F"
    and dist: "distinct [a,b,c,d,e,f,g,h,i]"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof (rule table[where rs = "[({a},{b,c},T2d), ({b},{a,c},T2d), ({c},{a,b},T2d),
    ({b,c},{a,f,g,h,i},T1), ({a,c},{b,d,e,h,i},T1), ({a,b},{c,d,e,f,g},T1),
    ({a,b,c},{d,e,f,g,h,i},T0)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m: "C - E \<in> twos (restr F J E)" if "C \<in> F" "C \<inter> J = {}" "card (C - E) = 2" for C J E
    using restr_mem[OF that(1,2)] that(3) by (simp add: twos_def)
  have "{f,g} \<in> twos (restr F {a} {b,c})"
    by (rule two_mem[OF T(3), of "{a}" "{b,c}"]) (use dist in auto)
  moreover have "{h,i} \<in> twos (restr F {a} {b,c})"
    by (rule two_mem[OF T(4), of "{a}" "{b,c}"]) (use dist in auto)
  ultimately have 1: "infam T2d (restr F {a} {b,c})" using npr by (rule infam_2d) (use dist in auto)
  have "{d,e} \<in> twos (restr F {b} {a,c})"
    by (rule two_mem[OF T(2), of "{b}" "{a,c}"]) (use dist in auto)
  moreover have "{h,i} \<in> twos (restr F {b} {a,c})"
    by (rule two_mem[OF T(4), of "{b}" "{a,c}"]) (use dist in auto)
  ultimately have 2: "infam T2d (restr F {b} {a,c})" using npr by (rule infam_2d) (use dist in auto)
  have "{d,e} \<in> twos (restr F {c} {a,b})"
    by (rule two_mem[OF T(2), of "{c}" "{a,b}"]) (use dist in auto)
  moreover have "{f,g} \<in> twos (restr F {c} {a,b})"
    by (rule two_mem[OF T(3), of "{c}" "{a,b}"]) (use dist in auto)
  ultimately have 3: "infam T2d (restr F {c} {a,b})" using npr by (rule infam_2d) (use dist in auto)
  have "{d,e} \<in> twos (restr F {b,c} {a,f,g,h,i})"
    by (rule two_mem[OF T(2), of "{b,c}" "{a,f,g,h,i}"]) (use dist in auto)
  then have 4: "infam T1 (restr F {b,c} {a,f,g,h,i})" by auto
  have "{f,g} \<in> twos (restr F {a,c} {b,d,e,h,i})"
    by (rule two_mem[OF T(3), of "{a,c}" "{b,d,e,h,i}"]) (use dist in auto)
  then have 5: "infam T1 (restr F {a,c} {b,d,e,h,i})" by auto
  have "{h,i} \<in> twos (restr F {a,b} {c,d,e,f,g})"
    by (rule two_mem[OF T(4), of "{a,b}" "{c,d,e,f,g}"]) (use dist in auto)
  then have 6: "infam T1 (restr F {a,b} {c,d,e,f,g})" by auto
  show ?case using 1 2 3 4 5 6 sub[OF T(1)] sub[OF T(2)] sub[OF T(3)] sub[OF T(4)] dist
    unfolding rows_ok_def by auto
next
  case 2
  have ne: "{a,b,c} \<noteq> {a,d,e}" "{a,b,c} \<noteq> {b,f,g}" "{a,b,c} \<noteq> {c,h,i}" using dist by auto
  have oa: "D = {a,b,c} \<or> D = {a,d,e}" if "D \<in> F" "a \<in> D" for D
    using two_only[OF deg T(1) T(2) _ _ ne(1) that] by simp
  have ob: "D = {a,b,c} \<or> D = {b,f,g}" if "D \<in> F" "b \<in> D" for D
    using two_only[OF deg T(1) T(3) _ _ ne(2) that] by simp
  have oc: "D = {a,b,c} \<or> D = {c,h,i}" if "D \<in> F" "c \<in> D" for D
    using two_only[OF deg T(1) T(4) _ _ ne(3) that] by simp
  have "(a \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (b \<in> X \<and> a \<notin> X \<and> c \<notin> X) \<or> (c \<in> X \<and> a \<notin> X \<and> b \<notin> X)
      \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X \<and> f \<notin> X \<and> g \<notin> X \<and> h \<notin> X \<and> i \<notin> X)
      \<or> (a \<in> X \<and> c \<in> X \<and> b \<notin> X \<and> d \<notin> X \<and> e \<notin> X \<and> h \<notin> X \<and> i \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> c \<notin> X \<and> d \<notin> X \<and> e \<notin> X \<and> f \<notin> X \<and> g \<notin> X)
      \<or> (a \<in> X \<and> b \<in> X \<and> c \<in> X \<and> d \<notin> X \<and> e \<notin> X \<and> f \<notin> X \<and> g \<notin> X \<and> h \<notin> X \<and> i \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X \<or> c \<in> X" using hit[OF X T(1)] by auto
    have ca: "d \<notin> X \<and> e \<notin> X" if "a \<in> X" "b \<in> X \<or> c \<in> X"
    proof -
      show ?thesis using that(2)
      proof
        assume "b \<in> X"
        show ?thesis by (rule crit_excl[OF X that(1) oa, of b]) (use dist \<open>b \<in> X\<close> in auto)
      next
        assume "c \<in> X"
        show ?thesis by (rule crit_excl[OF X that(1) oa, of c]) (use dist \<open>c \<in> X\<close> in auto)
      qed
    qed
    have cb: "f \<notin> X \<and> g \<notin> X" if "b \<in> X" "a \<in> X \<or> c \<in> X"
    proof -
      show ?thesis using that(2)
      proof
        assume "a \<in> X"
        show ?thesis by (rule crit_excl[OF X that(1) ob, of a]) (use dist \<open>a \<in> X\<close> in auto)
      next
        assume "c \<in> X"
        show ?thesis by (rule crit_excl[OF X that(1) ob, of c]) (use dist \<open>c \<in> X\<close> in auto)
      qed
    qed
    have cc: "h \<notin> X \<and> i \<notin> X" if "c \<in> X" "a \<in> X \<or> b \<in> X"
    proof -
      show ?thesis using that(2)
      proof
        assume "a \<in> X"
        show ?thesis by (rule crit_excl[OF X that(1) oc, of a]) (use dist \<open>a \<in> X\<close> in auto)
      next
        assume "b \<in> X"
        show ?thesis by (rule crit_excl[OF X that(1) oc, of b]) (use dist \<open>b \<in> X\<close> in auto)
      qed
    qed
    show ?thesis
      using h ca cb cc by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>\<open>\<P>(0,6)\<close>: \<open>a\<close> lies only in \<open>{a,b,c}\<close>, so \<open>a = 1\<close> forces \<open>b = c = 0\<close>.  First case: \<open>b\<close>
  and \<open>c\<close> lie in further clauses \<open>{b,d,e}\<close> and \<open>{c,f,g}\<close>, disjoint since there is no
  triangle.\<close>

lemma p06_both:
  assumes deg: "\<And>x. card {C\<in>F. x \<in> C} \<le> 2" and np: "npair F"
    and T: "{a,b,c} \<in> F" "{b,d,e} \<in> F" "{c,f,g} \<in> F" and dist: "distinct [a,b,c,d,e,f,g]"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b,c}"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof (rule table[where rs = "[({a},{b,c},T2d), ({b},{a,c},T1), ({c},{a,b},T1),
    ({b,c},{a,d,e,f,g},T0)]"], goal_cases)
  case 1
  have npr: "npair (restr F J E)" for J E using npair_restr[OF finF np] .
  have m: "C - E \<in> twos (restr F J E)" if "C \<in> F" "C \<inter> J = {}" "card (C - E) = 2" for C J E
    using restr_mem[OF that(1,2)] that(3) by (simp add: twos_def)
  have "{d,e} \<in> twos (restr F {a} {b,c})"
    by (rule two_mem[OF T(2), of "{a}" "{b,c}"]) (use dist in auto)
  moreover have "{f,g} \<in> twos (restr F {a} {b,c})"
    by (rule two_mem[OF T(3), of "{a}" "{b,c}"]) (use dist in auto)
  ultimately have 1: "infam T2d (restr F {a} {b,c})" using npr by (rule infam_2d) (use dist in auto)
  have "{f,g} \<in> twos (restr F {b} {a,c})"
    by (rule two_mem[OF T(3), of "{b}" "{a,c}"]) (use dist in auto)
  then have 2: "infam T1 (restr F {b} {a,c})" by auto
  have "{d,e} \<in> twos (restr F {c} {a,b})"
    by (rule two_mem[OF T(2), of "{c}" "{a,b}"]) (use dist in auto)
  then have 3: "infam T1 (restr F {c} {a,b})" by auto
  show ?case using 1 2 3 sub[OF T(1)] sub[OF T(2)] sub[OF T(3)] dist unfolding rows_ok_def by auto
next
  case 2
  have ne: "{a,b,c} \<noteq> {b,d,e}" "{a,b,c} \<noteq> {c,f,g}" using dist by auto
  have ob: "D = {a,b,c} \<or> D = {b,d,e}" if "D \<in> F" "b \<in> D" for D
    using two_only[OF deg T(1) T(2) _ _ ne(1) that] by simp
  have oc: "D = {a,b,c} \<or> D = {c,f,g}" if "D \<in> F" "c \<in> D" for D
    using two_only[OF deg T(1) T(3) _ _ ne(2) that] by simp
  have "(a \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (b \<in> X \<and> a \<notin> X \<and> c \<notin> X) \<or> (c \<in> X \<and> a \<notin> X \<and> b \<notin> X)
      \<or> (b \<in> X \<and> c \<in> X \<and> a \<notin> X \<and> d \<notin> X \<and> e \<notin> X \<and> f \<notin> X \<and> g \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "a \<in> X \<or> b \<in> X \<or> c \<in> X" using hit[OF X T(1)] by auto
    have ca: "b \<notin> X \<and> c \<notin> X" if "a \<in> X"
      by (rule excl3[OF only_clause[OF X that oa]]) (use dist in auto)
    have cb: "d \<notin> X \<and> e \<notin> X" if "b \<in> X" "c \<in> X"
      by (rule crit_excl[OF X that(1) ob, of c]) (use dist that in auto)
    have cc: "f \<notin> X \<and> g \<notin> X" if "c \<in> X" "b \<in> X"
      by (rule crit_excl[OF X that(1) oc, of b]) (use dist that in auto)
    show ?thesis
      using h ca cb cc by (cases "a \<in> X"; cases "b \<in> X"; cases "c \<in> X") simp_all
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

text \<open>Second case: \<open>a\<close> and \<open>b\<close> lie only in \<open>{a,b,c}\<close>.  The paper also treats \<open>c\<close> lying in
  another clause, by domination; here the type-0 bound covers both at once.\<close>

lemma p06_one:
  assumes T: "{a,b,c} \<in> F" and dist: "distinct [a,b,c]"
    and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = {a,b,c}"
    and ob: "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = {a,b,c}"
  shows "real (card (trans V F t)) \<le> bound T0 s t"
proof (rule table[where rs = "[({c},{a,b},T0), ({a},{b,c},T0), ({b},{a,c},T0)]"], goal_cases)
  case 1
  then show ?case using sub[OF T] dist unfolding rows_ok_def by auto
next
  case 2
  have "(c \<in> X \<and> a \<notin> X \<and> b \<notin> X) \<or> (a \<in> X \<and> b \<notin> X \<and> c \<notin> X) \<or> (b \<in> X \<and> a \<notin> X \<and> c \<notin> X)"
    if X: "X \<in> trans V F t" for X
  proof -
    have h: "{a,b,c} \<inter> X \<noteq> {}" using hit[OF X T] .
    show ?thesis
    proof (cases "a \<in> X")
      case True
      have "{a,b,c} \<inter> X = {a}" using only_clause[OF X True oa] .
      then have "b \<notin> X" "c \<notin> X"
        using single_out[of "{a,b,c}" X a b] single_out[of "{a,b,c}" X a c] dist by simp_all
      then show ?thesis using True by simp
    next
      case na: False
      show ?thesis
      proof (cases "b \<in> X")
        case True
        have "{a,b,c} \<inter> X = {b}" using only_clause[OF X True ob] .
        then have "c \<notin> X" using single_out[of "{a,b,c}" X b c] dist by simp
        then show ?thesis using True na by simp
      next
        case False
        then have "c \<in> X" using h na by auto
        then show ?thesis using False na by simp
      qed
    qed
  qed
  then show ?case by auto
next
  case 3
  then show ?case using dist by (cases "even s") (simp_all add: ratio_simps)
qed

subsection \<open>Type 0: choosing the configuration\<close>

lemma three_elems:
  assumes C: "C \<in> F" "a \<in> C"
  obtains b c where "C = {a,b,c}" "distinct [a,b,c]"
proof -
  have "card (C - {a}) = 2"
    using three[OF C(1)] C(2) cnf_clause_finite[OF cnf C(1)] by simp
  then obtain b c where bc: "C - {a} = {b,c}" "b \<noteq> c" unfolding card_2_iff by blast
  have e: "C = {a,b,c}" using bc(1) C(2) by blast
  have "a \<noteq> b" "a \<noteq> c" using bc(1) by auto
  then show ?thesis using that[OF e] bc(2) by simp
qed

definition tri :: bool where
  "tri \<longleftrightarrow> (\<exists>a b c d e f. {a,b,d} \<in> F \<and> {b,c,e} \<in> F \<and> {a,c,f} \<in> F \<and> distinct [a,b,c,d,e,f])"

text \<open>If no pair lies in two clauses and there is no triangle, then the further clauses of two
  variables of a clause are disjoint: a common variable \<open>x\<close> of \<open>D\<^sub>1 = {b,x,u}\<close> and
  \<open>D\<^sub>2 = {c,x,v}\<close> gives the triangle \<open>{b,x,u}\<close>, \<open>{x,c,v}\<close>, \<open>{b,c,a}\<close>.\<close>

lemma meet_tri:
  assumes p1: "\<And>x y C D. x \<noteq> y \<Longrightarrow> C \<in> F \<Longrightarrow> D \<in> F \<Longrightarrow> x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> C = D"
    and notri: "\<not> tri"
    and C: "C \<in> F" "b \<in> C" "c \<in> C" "b \<noteq> c"
    and D: "D1 \<in> F" "b \<in> D1" "D1 \<noteq> C" "D2 \<in> F" "c \<in> D2" "D2 \<noteq> C"
  shows "D1 \<inter> D2 = {}"
proof (rule ccontr)
  assume "D1 \<inter> D2 \<noteq> {}"
  then obtain x where x: "x \<in> D1" "x \<in> D2" by blast
  obtain a where a: "C = {b,c,a}" "a \<noteq> b" "a \<noteq> c" using three_form[OF C] by blast
  have aC: "a \<in> C" using a(1) by simp
  have cD1: "c \<notin> D1" using p1[of b c D1 C] C D by blast
  have bD2: "b \<notin> D2" using p1[of b c D2 C] C D by blast
  have aD1: "a \<notin> D1" using p1[of a b D1 C] a(2) aC C D by blast
  have aD2: "a \<notin> D2" using p1[of a c D2 C] a(3) aC C D by blast
  have bx: "b \<noteq> x" using bD2 x(2) by blast
  have cx: "c \<noteq> x" using cD1 x(1) by blast
  obtain u where u: "D1 = {b,x,u}" "u \<noteq> b" "u \<noteq> x" using three_form[OF D(1) D(2) x(1) bx] by blast
  obtain v where v: "D2 = {c,x,v}" "v \<noteq> c" "v \<noteq> x" using three_form[OF D(4) D(5) x(2) cx] by blast
  have "D1 \<noteq> D2" using bD2 D(2) by blast
  then have uv: "u \<noteq> v" using p1[of x u D1 D2] u v D(1,4) by auto
  have F3: "{b,x,u} \<in> F" "{x,c,v} \<in> F" "{b,c,a} \<in> F"
    using D(1,4) C(1) u(1) v(1) a(1) by (auto simp: insert_commute)
  have "distinct [b,x,c,u,v,a]"
    using a(2,3) bx cx u v uv aD1 aD2 cD1 bD2 C(4) by auto
  then have tri unfolding tri_def using F3 by blast
  then show False using notri by blast
qed

theorem type0: "real (card (trans V F t)) \<le> bound T0 s t"
proof (cases "npair F")
  case False
  then show ?thesis by (rule p01)
next
  case np: True
  show ?thesis
  proof (cases "\<exists>a. 3 \<le> card {C\<in>F. a \<in> C}")
    case True
    then obtain a where "3 \<le> card {C\<in>F. a \<in> C}" by blast
    then show ?thesis by (rule p02[OF np])
  next
    case False
    have deg: "card {C\<in>F. x \<in> C} \<le> 2" for x
    proof -
      have "\<not> 3 \<le> card {C\<in>F. x \<in> C}" using False by blast
      then show ?thesis by simp
    qed
    show ?thesis
    proof (cases "\<exists>a b C D. a \<noteq> b \<and> C \<in> F \<and> D \<in> F \<and> C \<noteq> D \<and> a \<in> C \<and> b \<in> C \<and> a \<in> D \<and> b \<in> D")
      case True
      then obtain a b C D where ab: "a \<noteq> b" "C \<in> F" "D \<in> F" "C \<noteq> D" "a \<in> C" "b \<in> C" "a \<in> D" "b \<in> D"
        by blast
      obtain c where c: "C = {a,b,c}" "c \<noteq> a" "c \<noteq> b" using three_form[OF ab(2) ab(5) ab(6) ab(1)] by blast
      obtain d where d: "D = {a,b,d}" "d \<noteq> a" "d \<noteq> b" using three_form[OF ab(3) ab(7) ab(8) ab(1)] by blast
      have "c \<noteq> d" using c(1) d(1) ab(4) by blast
      then have dist: "distinct [a,b,c,d]" using ab(1) c(2,3) d(2,3) by auto
      have "{a,b,c} \<in> F" "{a,b,d} \<in> F" using ab(2,3) c(1) d(1) by simp_all
      then show ?thesis by (rule p03[OF np deg _ _ dist])
    next
      case False
      have p1: "C = D" if "x \<noteq> y" "C \<in> F" "D \<in> F" "x \<in> C" "y \<in> C" "x \<in> D" "y \<in> D" for x y C D
        using False that by blast
      show ?thesis
      proof (cases tri)
        case True
        then obtain a b c d e f where "{a,b,d} \<in> F" "{b,c,e} \<in> F" "{a,c,f} \<in> F" "distinct [a,b,c,d,e,f]"
          unfolding tri_def by blast
        then show ?thesis by (rule p04[OF deg])
      next
        case notri: False
        have mt: "D1 \<inter> D2 = {}"
          if "C \<in> F" "b \<in> C" "c \<in> C" "b \<noteq> c" "D1 \<in> F" "b \<in> D1" "D1 \<noteq> C" "D2 \<in> F" "c \<in> D2" "D2 \<noteq> C"
          for C b c D1 D2
          by (rule meet_tri[OF p1 notri that])
        show ?thesis
        proof (cases "\<exists>a C. C \<in> F \<and> a \<in> C \<and> (\<forall>D\<in>F. a \<in> D \<longrightarrow> D = C)")
          case True
          then obtain a C where aC: "C \<in> F" "a \<in> C" and oa: "\<And>D. D \<in> F \<Longrightarrow> a \<in> D \<Longrightarrow> D = C"
            by blast
          obtain b c where bc: "C = {a,b,c}" "distinct [a,b,c]" by (rule three_elems[OF aC])
          have T: "{a,b,c} \<in> F" using aC(1) bc(1) by simp
          have bC: "b \<in> C" "c \<in> C" "b \<noteq> c" using bc by auto
          have oa': "D = {a,b,c}" if "D \<in> F" "a \<in> D" for D using oa[OF that] bc(1) by simp
          show ?thesis
          proof (cases "(\<exists>D1\<in>F. b \<in> D1 \<and> D1 \<noteq> C) \<and> (\<exists>D2\<in>F. c \<in> D2 \<and> D2 \<noteq> C)")
            case True
            then obtain D1 D2 where D: "D1 \<in> F" "b \<in> D1" "D1 \<noteq> C" "D2 \<in> F" "c \<in> D2" "D2 \<noteq> C"
              by blast
            have disj: "D1 \<inter> D2 = {}" by (rule mt[OF aC(1) bC D])
            have aD: "a \<notin> D1" "a \<notin> D2" using oa D(1,3,4,6) by blast+
            have cD1: "c \<notin> D1" using p1[of b c D1 C] D(1,2,3) bC aC(1) by blast
            have bD2: "b \<notin> D2" using p1[of b c D2 C] D(4,5,6) bC aC(1) by blast
            obtain d e where de: "D1 = {b,d,e}" "distinct [b,d,e]" by (rule three_elems[OF D(1) D(2)])
            obtain f g where fg: "D2 = {c,f,g}" "distinct [c,f,g]" by (rule three_elems[OF D(4) D(5)])
            have T2: "{b,d,e} \<in> F" "{c,f,g} \<in> F" using D(1,4) de(1) fg(1) by simp_all
            have "distinct [a,b,c,d,e,f,g]"
              using bc(2) de fg disj aD cD1 bD2 by auto
            then show ?thesis by (rule p06_both[OF deg np T T2 _ oa'])
          next
            case False
            then consider (b) "\<And>D. D \<in> F \<Longrightarrow> b \<in> D \<Longrightarrow> D = C" | (c) "\<And>D. D \<in> F \<Longrightarrow> c \<in> D \<Longrightarrow> D = C"
              by blast
            then show ?thesis
            proof cases
              case b
              have ob: "D = {a,b,c}" if "D \<in> F" "b \<in> D" for D using b[OF that] bc(1) by simp
              show ?thesis by (rule p06_one[OF T bc(2) oa' ob])
            next
              case c
              have e: "{a,c,b} = {a,b,c}" by auto
              have T': "{a,c,b} \<in> F" using T unfolding e .
              have d': "distinct [a,c,b]" using bc(2) by auto
              have oa'': "D = {a,c,b}" if "D \<in> F" "a \<in> D" for D using oa'[OF that] unfolding e .
              have oc: "D = {a,c,b}" if "D \<in> F" "c \<in> D" for D using c[OF that] bc(1) unfolding e by simp
              show ?thesis by (rule p06_one[OF T' d' oa'' oc])
            qed
          qed
        next
          case False
          then have two: "\<exists>D\<in>F. x \<in> D \<and> D \<noteq> C" if "C \<in> F" "x \<in> C" for x C
            using that by blast
          have "F \<noteq> {}"
          proof
            assume "F = {}"
            then have "hits F {}" by (simp add: hits_def)
            then have "t \<le> card ({}::nat set)" using thrD[OF thr] by blast
            then show False using t1 by simp
          qed
          then obtain C where C: "C \<in> F" by blast
          have "C \<noteq> {}" using three[OF C] by auto
          then obtain a where a: "a \<in> C" by blast
          obtain b c where bc: "C = {a,b,c}" "distinct [a,b,c]" by (rule three_elems[OF C a])
          have abc: "b \<in> C" "c \<in> C" "a \<noteq> b" "a \<noteq> c" "b \<noteq> c" using bc by auto
          obtain Da where Da: "Da \<in> F" "a \<in> Da" "Da \<noteq> C" using two[OF C a] by blast
          obtain Db where Db: "Db \<in> F" "b \<in> Db" "Db \<noteq> C" using two[OF C abc(1)] by blast
          obtain Dc where Dc: "Dc \<in> F" "c \<in> Dc" "Dc \<noteq> C" using two[OF C abc(2)] by blast
          have disj: "Da \<inter> Db = {}" "Da \<inter> Dc = {}" "Db \<inter> Dc = {}"
            by (rule mt[OF C a abc(1) abc(3) Da Db], rule mt[OF C a abc(2) abc(4) Da Dc],
                rule mt[OF C abc(1) abc(2) abc(5) Db Dc])
          have out: "b \<notin> Da" "c \<notin> Da" "a \<notin> Db" "c \<notin> Db" "a \<notin> Dc" "b \<notin> Dc"
            using p1[of a b Da C] p1[of a c Da C] p1[of a b Db C] p1[of b c Db C]
              p1[of a c Dc C] p1[of b c Dc C] C a abc Da Db Dc by blast+
          obtain d e where de: "Da = {a,d,e}" "distinct [a,d,e]" by (rule three_elems[OF Da(1) Da(2)])
          obtain f g where fg: "Db = {b,f,g}" "distinct [b,f,g]" by (rule three_elems[OF Db(1) Db(2)])
          obtain h i where hi: "Dc = {c,h,i}" "distinct [c,h,i]" by (rule three_elems[OF Dc(1) Dc(2)])
          have T: "{a,b,c} \<in> F" "{a,d,e} \<in> F" "{b,f,g} \<in> F" "{c,h,i} \<in> F"
            using C Da(1) Db(1) Dc(1) bc(1) de(1) fg(1) hi(1) by simp_all
          have "distinct [a,b,c,d,e,f,g,h,i]"
            using bc(2) de fg hi disj out by auto
          then show ?thesis by (rule p05[OF deg np T])
        qed
      qed
    qed
  qed
qed

end


end
