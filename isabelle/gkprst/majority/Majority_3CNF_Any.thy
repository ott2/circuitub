theory Majority_3CNF_Any
  imports Majority_3CNF Majority_3CNF_Upper
begin

text \<open>The matching upper bound for every \<open>n\<close>.  Write \<open>n = 4m + r\<close> with \<open>r < 4\<close>.  The extremal CNF is
  \<open>m\<close> disjoint 4-cliques (\<open>K4\<close>) together with one small clique on the last \<open>r\<close> variables: all
  \<open>k\<close>-subsets of an \<open>r\<close>-set, with \<open>k = 1\<close> for \<open>r \<le> 1\<close> and \<open>k = 2\<close> otherwise.  A set hits every clause
  of the small clique iff it misses fewer than \<open>k\<close> of its variables, so the threshold is
  \<open>r + 1 - k = \<lceil>r/2\<rceil>\<close> and there are \<open>r choose \<lceil>r/2\<rceil>\<close> = 1, 1, 2, 3 minimum transversals.  Thresholds
  add over disjoint unions and minimum transversals multiply, so the CNF has threshold
  \<open>\<lceil>n/2\<rceil>\<close> and at least \<open>6\<^bsup>(n-1)/4\<^esup>\<close> minimum transversals.\<close>

subsection \<open>Disjoint unions of CNFs\<close>

lemma hits_Int: "cnf V F \<Longrightarrow> hits F (X \<inter> V) \<longleftrightarrow> hits F X"
  unfolding hits_def cnf_def by blast

lemma hits_Un: "hits (F \<union> G) X \<longleftrightarrow> hits F X \<and> hits G X"
  unfolding hits_def by blast

context
  fixes V W :: "'a set" and F G :: "'a set set"
  assumes F: "cnf V F" and G: "cnf W G" and D: "V \<inter> W = {}"
begin

lemma union_cnf: "cnf (V \<union> W) (F \<union> G)"
  using F G by (auto simp: cnf_def)

lemma card_split:
  assumes X: "X \<subseteq> V \<union> W"
  shows "card X = card (X \<inter> V) + card (X \<inter> W)"
proof -
  have f: "finite V" "finite W" using F G by (auto simp: cnf_def)
  have "card ((X \<inter> V) \<union> (X \<inter> W)) = card (X \<inter> V) + card (X \<inter> W)"
    by (rule card_Un_disjoint) (use f D in auto)
  moreover have "(X \<inter> V) \<union> (X \<inter> W) = X" using X by blast
  ultimately show ?thesis by simp
qed

lemma union_thr:
  assumes s: "thr V F s" and u: "thr W G u"
  shows "thr (V \<union> W) (F \<union> G) (s + u)"
  unfolding thr_def
proof (intro allI impI)
  fix X assume X: "X \<subseteq> V \<union> W" and h: "hits (F \<union> G) X"
  have h1: "hits F (X \<inter> V)" using h by (simp add: hits_Un hits_Int[OF F])
  have h2: "hits G (X \<inter> W)" using h by (simp add: hits_Un hits_Int[OF G])
  have "s \<le> card (X \<inter> V)" using s h1 by (simp add: thr_def)
  moreover have "u \<le> card (X \<inter> W)" using u h2 by (simp add: thr_def)
  ultimately show "s + u \<le> card X" using card_split[OF X] by linarith
qed

lemma union_trans:
  assumes s: "thr V F s" and u: "thr W G u"
  shows "trans (V \<union> W) (F \<union> G) (s + u) = (\<lambda>(X, Y). X \<union> Y) ` (trans V F s \<times> trans W G u)"
proof (rule set_eqI)
  fix Z
  show "Z \<in> trans (V \<union> W) (F \<union> G) (s + u) \<longleftrightarrow> Z \<in> (\<lambda>(X, Y). X \<union> Y) ` (trans V F s \<times> trans W G u)"
  proof
    assume "Z \<in> trans (V \<union> W) (F \<union> G) (s + u)"
    then have Z: "Z \<subseteq> V \<union> W" "hits (F \<union> G) Z" "card Z = s + u" by (auto simp: trans_def)
    have h1: "hits F (Z \<inter> V)" using Z(2) by (simp add: hits_Un hits_Int[OF F])
    have h2: "hits G (Z \<inter> W)" using Z(2) by (simp add: hits_Un hits_Int[OF G])
    have a: "s \<le> card (Z \<inter> V)" using s h1 by (simp add: thr_def)
    have b: "u \<le> card (Z \<inter> W)" using u h2 by (simp add: thr_def)
    have c: "card Z = card (Z \<inter> V) + card (Z \<inter> W)" by (rule card_split[OF Z(1)])
    have "card (Z \<inter> V) = s" "card (Z \<inter> W) = u" using a b c Z(3) by linarith+
    then have mem: "(Z \<inter> V, Z \<inter> W) \<in> trans V F s \<times> trans W G u"
      using h1 h2 by (auto simp: trans_def)
    show "Z \<in> (\<lambda>(X, Y). X \<union> Y) ` (trans V F s \<times> trans W G u)"
    proof (rule image_eqI[where x = "(Z \<inter> V, Z \<inter> W)"])
      show "Z = (\<lambda>(X, Y). X \<union> Y) (Z \<inter> V, Z \<inter> W)" using Z(1) by auto
    qed (rule mem)
  next
    assume "Z \<in> (\<lambda>(X, Y). X \<union> Y) ` (trans V F s \<times> trans W G u)"
    then obtain X Y where X: "X \<in> trans V F s" and Y: "Y \<in> trans W G u" and Z: "Z = X \<union> Y" by blast
    have XV: "X \<subseteq> V" "hits F X" "card X = s" using X by (auto simp: trans_def)
    have YW: "Y \<subseteq> W" "hits G Y" "card Y = u" using Y by (auto simp: trans_def)
    have f: "finite V" "finite W" using F G by (auto simp: cnf_def)
    have hF: "hits F Z" by (rule hits_mono[OF XV(2)]) (simp add: Z)
    have hG: "hits G Z" by (rule hits_mono[OF YW(2)]) (simp add: Z)
    have "X \<inter> Y = {}" using XV(1) YW(1) D by blast
    then have "card (X \<union> Y) = card X + card Y"
      using finite_subset[OF XV(1) f(1)] finite_subset[OF YW(1) f(2)] by (simp add: card_Un_disjoint)
    then show "Z \<in> trans (V \<union> W) (F \<union> G) (s + u)"
      using XV YW hF hG by (auto simp: trans_def hits_Un Z)
  qed
qed

lemma union_trans_card:
  assumes s: "thr V F s" and u: "thr W G u"
  shows "card (trans (V \<union> W) (F \<union> G) (s + u)) = card (trans V F s) * card (trans W G u)"
proof -
  have inj: "inj_on (\<lambda>(X, Y). X \<union> Y) (trans V F s \<times> trans W G u)"
  proof (rule inj_onI, clarify)
    fix X Y X' Y' assume X: "X \<in> trans V F s" "X' \<in> trans V F s"
      and Y: "Y \<in> trans W G u" "Y' \<in> trans W G u" and e: "X \<union> Y = X' \<union> Y'"
    have L: "X \<subseteq> V" "X' \<subseteq> V" "Y \<subseteq> W" "Y' \<subseteq> W" using X Y by (auto simp: trans_def)
    have "X = (X \<union> Y) \<inter> V" using L D by blast
    also have "\<dots> = (X' \<union> Y') \<inter> V" by (simp only: e)
    also have "\<dots> = X'" using L D by blast
    finally have xx: "X = X'" .
    have "Y = (X \<union> Y) \<inter> W" using L D by blast
    also have "\<dots> = (X' \<union> Y') \<inter> W" by (simp only: e)
    also have "\<dots> = Y'" using L D by blast
    finally show "X = X' \<and> Y = Y'" using xx by simp
  qed
  show ?thesis by (simp add: union_trans[OF s u] card_image[OF inj] card_cartesian_product)
qed

end

subsection \<open>Cliques: all \<open>k\<close>-subsets of a finite set\<close>

definition KC :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "KC B k = {C. C \<subseteq> B \<and> card C = k}"

lemma KC_cnf: "finite B \<Longrightarrow> k \<le> 3 \<Longrightarrow> cnf B (KC B k)"
  by (auto simp: cnf_def KC_def)

lemma hits_KC:
  assumes B: "finite B"
  shows "hits (KC B k) X \<longleftrightarrow> card (B - X) < k"
proof
  assume h: "hits (KC B k) X"
  show "card (B - X) < k"
  proof (rule ccontr)
    assume "\<not> card (B - X) < k"
    then have "k \<le> card (B - X)" by simp
    then obtain C where C: "C \<subseteq> B - X" "card C = k" by (rule obtain_subset_with_card_n)
    then have "C \<in> KC B k" "C \<inter> X = {}" by (auto simp: KC_def)
    then show False using h by (auto simp: hits_def)
  qed
next
  assume c: "card (B - X) < k"
  show "hits (KC B k) X" unfolding hits_def
  proof
    fix C assume "C \<in> KC B k"
    then have C: "C \<subseteq> B" "card C = k" by (auto simp: KC_def)
    show "C \<inter> X \<noteq> {}"
    proof
      assume "C \<inter> X = {}"
      then have "C \<subseteq> B - X" using C(1) by blast
      then have "card C \<le> card (B - X)" by (rule card_mono[rotated]) (simp add: B)
      then show False using c C(2) by simp
    qed
  qed
qed

lemma hits_KC_sub:
  assumes B: "finite B" and X: "X \<subseteq> B" and tk: "t + k = card B + 1"
  shows "hits (KC B k) X \<longleftrightarrow> t \<le> card X"
proof -
  have d: "card (B - X) = card B - card X"
    by (rule card_Diff_subset[OF finite_subset[OF X B] X])
  have le: "card X \<le> card B" by (rule card_mono[OF B X])
  have h: "hits (KC B k) X \<longleftrightarrow> card B - card X < k" using hits_KC[OF B] d by simp
  have "card B - card X < k \<longleftrightarrow> t \<le> card X" using le tk by arith
  then show ?thesis using h by simp
qed

lemma KC_thr:
  assumes B: "finite B" and tk: "t + k = card B + 1"
  shows "thr B (KC B k) t"
  unfolding thr_def using hits_KC_sub[OF B _ tk] by blast

lemma KC_trans_card:
  assumes B: "finite B" and tk: "t + k = card B + 1"
  shows "card (trans B (KC B k) t) = card B choose t"
proof -
  have "trans B (KC B k) t = {X. X \<subseteq> B \<and> card X = t}"
    unfolding trans_def using hits_KC_sub[OF B _ tk] by auto
  then show ?thesis using B by (simp add: n_subsets)
qed

subsection \<open>The extremal CNF for every \<open>n\<close>\<close>

definition kg :: "nat \<Rightarrow> nat" where
  "kg r = (if r \<le> 1 then 1 else 2)"

definition tg :: "nat \<Rightarrow> nat" where
  "tg r = (r + 1) div 2"

lemma tg_kg:
  assumes "r < 4"
  shows "tg r + kg r = r + 1"
proof -
  have "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3" using assms by arith
  then show ?thesis by (auto simp: tg_def kg_def)
qed

lemma choose_kg:
  assumes "r < 4"
  shows "r choose kg r \<le> r"
proof -
  have "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3" using assms by arith
  then show ?thesis by (auto simp: kg_def numeral_eq_Suc)
qed

definition XF :: "nat \<Rightarrow> nat \<Rightarrow> nat set set" where
  "XF m r = K4 m \<union> KC {4 * m..<4 * m + r} (kg r)"

lemma XF:
  assumes r: "r < 4"
  shows "cnf {..<4 * m + r} (XF m r)" "thr {..<4 * m + r} (XF m r) (2 * m + tg r)"
    "card (trans {..<4 * m + r} (XF m r) (2 * m + tg r)) = 6 ^ m * (r choose tg r)"
    "card (XF m r) \<le> 4 * m + r"
proof -
  define W where "W = {4 * m..<4 * m + r}"
  have U: "{..<4 * m} \<union> W = {..<4 * m + r}" by (auto simp: W_def)
  have D: "{..<4 * m} \<inter> W = {}" by (auto simp: W_def)
  have cW: "card W = r" "finite W" by (simp_all add: W_def)
  have kg3: "kg r \<le> 3" by (simp add: kg_def)
  have G: "cnf W (KC W (kg r))" by (rule KC_cnf[OF cW(2) kg3])
  have tk: "tg r + kg r = card W + 1" using tg_kg[OF r] cW(1) by simp
  have Gt: "thr W (KC W (kg r)) (tg r)" by (rule KC_thr[OF cW(2) tk])
  have GT: "card (trans W (KC W (kg r)) (tg r)) = r choose tg r"
    using KC_trans_card[OF cW(2) tk] cW(1) by simp
  have X: "XF m r = K4 m \<union> KC W (kg r)" by (simp add: XF_def W_def)
  show "cnf {..<4 * m + r} (XF m r)" using union_cnf[OF K4_cnf G D] U X by simp
  show "thr {..<4 * m + r} (XF m r) (2 * m + tg r)" using union_thr[OF K4_cnf G D K4_thr Gt] U X by simp
  show "card (trans {..<4 * m + r} (XF m r) (2 * m + tg r)) = 6 ^ m * (r choose tg r)"
    using union_trans_card[OF K4_cnf G D K4_thr Gt] U X K4_trans Q4_card GT by simp
  have "card (XF m r) \<le> card (K4 m) + card (KC W (kg r))" unfolding X by (rule card_Un_le)
  moreover have "card (KC W (kg r)) = r choose kg r" using cW by (simp add: KC_def n_subsets)
  ultimately show "card (XF m r) \<le> 4 * m + r" using K4_card[of m] choose_kg[OF r] by linarith
qed

text \<open>The count: with \<open>q = 6\<^bsup>1/4\<^esup>\<close>, \<open>q\<^sup>r \<le> q (r choose \<lceil>r/2\<rceil>)\<close> for \<open>r < 4\<close>, because \<open>1 \<le> q\<close>, \<open>q \<le> 2\<close>
  (\<open>6 \<le> 16\<close>) and \<open>q\<^sup>2 \<le> 3\<close> (\<open>6 \<le> 9\<close>).\<close>

lemma quarter_bound:
  "6 powr (real n / 4) \<le> 6 powr (1 / 4) * real (6 ^ (n div 4) * (n mod 4 choose tg (n mod 4)))"
proof -
  define q :: real where "q = 6 powr (1 / 4)"
  define m where "m = n div 4"
  define r where "r = n mod 4"
  have n: "n = 4 * m + r" by (simp add: m_def r_def)
  have r4: "r < 4" by (simp add: r_def)
  have q0: "0 < q" by (simp add: q_def)
  have qp: "q ^ k = 6 powr (real k / 4)" for k
  proof -
    have "q ^ k = q powr real k" using q0 by (simp add: powr_realpow)
    also have "\<dots> = 6 powr (real k / 4)" by (simp add: q_def powr_powr)
    finally show ?thesis .
  qed
  have q4: "q ^ 4 = 6" using qp[of 4] by simp
  have q1: "1 \<le> q" unfolding q_def by (rule ge_one_powr_ge_zero) simp_all
  have q2: "q \<le> 2"
  proof (rule power_le_imp_le_base)
    show "q ^ Suc 3 \<le> 2 ^ Suc 3" using q4 by simp
  qed simp
  have q3: "q ^ 2 \<le> 3"
  proof (rule power_le_imp_le_base)
    have "(q ^ 2) ^ Suc 1 = q ^ 4" by (simp only: power_mult[symmetric]) simp
    then show "(q ^ 2) ^ Suc 1 \<le> 3 ^ Suc 1" using q4 by simp
  qed simp
  have c3: "(3::nat) choose 2 = 3" by (simp add: numeral_eq_Suc)
  have qr: "q ^ r \<le> q * real (r choose tg r)"
  proof -
    have "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3" using r4 by arith
    then show ?thesis
    proof (elim disjE)
      assume "r = 0"
      then show ?thesis using q1 by (simp add: tg_def)
    next
      assume "r = 1"
      then show ?thesis by (simp add: tg_def)
    next
      assume r: "r = 2"
      have "q ^ 2 = q * q" by (simp add: power2_eq_square)
      also have "\<dots> \<le> q * 2" by (rule mult_left_mono[OF q2]) (use q0 in simp)
      finally show ?thesis using r by (simp add: tg_def)
    next
      assume r: "r = 3"
      have "q ^ 3 = q * q ^ 2" by (simp add: power3_eq_cube power2_eq_square)
      also have "\<dots> \<le> q * 3" by (rule mult_left_mono[OF q3]) (use q0 in simp)
      finally show ?thesis using r c3 by (simp add: tg_def)
    qed
  qed
  have "6 powr (real n / 4) = q ^ n" by (simp add: qp)
  also have "q ^ n = (q ^ 4) ^ m * q ^ r" by (simp add: n power_add power_mult)
  also have "\<dots> = 6 ^ m * q ^ r" by (simp add: q4)
  also have "\<dots> \<le> 6 ^ m * (q * real (r choose tg r))" by (rule mult_left_mono[OF qr]) simp
  also have "\<dots> = q * real (6 ^ m * (r choose tg r))" by simp
  finally show ?thesis by (simp only: q_def m_def r_def)
qed

subsection \<open>Majority: the tight bound for every \<open>n\<close>\<close>

theorem majority_mcnfs_upper_any:
  obtains gs where "\<forall>g\<in>set gs. MCNF 3 g" "\<forall>\<sigma>. eval \<sigma> (Or gs) \<longleftrightarrow> majority n \<sigma>"
    "real (length gs) \<le> 6 powr (1 / 4) * real (n + 1) * real (n choose (n div 2)) / 6 powr (real n / 4) + 1"
    "\<forall>g\<in>set gs. gates g \<le> n + 1"
proof -
  define m where "m = n div 4"
  define r where "r = n mod 4"
  have n: "4 * m + r = n" by (simp add: m_def r_def)
  have r4: "r < 4" by (simp add: r_def)
  define F where "F = XF m r"
  define t where "t = 2 * m + tg r"
  have F: "cnf {..<n} F" "thr {..<n} F t" using XF(1,2)[OF r4, of m] n by (simp_all add: F_def t_def)
  have T: "card (trans {..<n} F t) = 6 ^ m * (r choose tg r)"
    using XF(3)[OF r4, of m] n by (simp add: F_def t_def)
  have tr: "tg r \<le> r" unfolding tg_def by presburger
  have T0: "0 < card (trans {..<n} F t)" using T zero_less_binomial[OF tr] by simp
  have tn: "t = (n + 1) div 2" using n unfolding t_def tg_def by presburger
  have maj: "majority n \<sigma> \<longleftrightarrow> t \<le> weight n \<sigma>" for \<sigma> unfolding majority_def tn by presburger
  have tle: "t \<le> n" using tn by presburger
  have nt: "n - t = n div 2" using tn by presburger
  have bin: "n choose t = n choose (n div 2)" using binomial_symmetric[OF tle] nt by simp
  obtain gs where g: "\<forall>g\<in>set gs. MCNF 3 g" and ev: "\<forall>\<sigma>. eval \<sigma> (Or gs) \<longleftrightarrow> t \<le> weight n \<sigma>"
    and len: "real (length gs) \<le> real (n + 1) * real (n choose t) / real (card (trans {..<n} F t)) + 1"
    and gt: "\<forall>g\<in>set gs. gates g = card F + 1"
    by (rule threshold_cover[OF F T0])
  define q :: real where "q = 6 powr (1 / 4)"
  define a where "a = real (n + 1) * real (n choose t)"
  define T where "T = real (card (trans {..<n} F t))"
  have P: "6 powr (real n / 4) \<le> q * T"
    using quarter_bound[of n] T by (simp add: q_def T_def m_def r_def)
  have q0: "0 < q" by (simp add: q_def)
  have Tp: "0 < T" using T0 by (simp add: T_def)
  have a0: "0 \<le> a" by (simp add: a_def)
  have "a / T = (q * a) / (q * T)" using q0 by simp
  also have "\<dots> \<le> (q * a) / 6 powr (real n / 4)"
    by (rule frac_le) (use a0 q0 P in simp_all)
  finally have aT: "a / T \<le> q * a / 6 powr (real n / 4)" .
  have e1: "real (n + 1) * real (n choose t) / real (card (trans {..<n} F t)) = a / T"
    by (simp add: a_def T_def)
  have e2: "6 powr (1 / 4) * real (n + 1) * real (n choose (n div 2)) / 6 powr (real n / 4)
      = q * a / 6 powr (real n / 4)" by (simp add: a_def q_def bin mult.assoc)
  have "\<forall>\<sigma>. eval \<sigma> (Or gs) \<longleftrightarrow> majority n \<sigma>" using ev maj by simp
  moreover have "real (length gs) \<le> 6 powr (1 / 4) * real (n + 1) * real (n choose (n div 2))
      / 6 powr (real n / 4) + 1"
    using len e1 e2 aT by linarith
  moreover have "\<forall>g\<in>set gs. gates g \<le> n + 1" using gt XF(4)[OF r4, of m] n by (simp add: F_def)
  ultimately show ?thesis using that g by blast
qed

text \<open>Both directions for every \<open>n\<close>: the least number of monotone 3-CNFs whose OR is Majority lies
  between \<open>(n choose \<lfloor>n/2\<rfloor>)/6\<^bsup>(n+1)/4\<^esup>\<close> and \<open>6\<^bsup>1/4\<^esup>(n+1) (n choose \<lfloor>n/2\<rfloor>)/6\<^bsup>n/4\<^esup> + 1\<close>, a ratio of
  \<open>\<surd>6 (n+1)\<close>.\<close>

corollary majority_mcnfs_tight_any:
  shows "\<And>fs. \<forall>f\<in>set fs. MCNF 3 f \<Longrightarrow> \<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma> \<Longrightarrow>
           real (n choose (n div 2)) / 6 powr ((real n + 1) / 4) \<le> real (length fs)"
    and "\<exists>fs. (\<forall>f\<in>set fs. MCNF 3 f) \<and> (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma>) \<and>
           real (length fs) \<le> 6 powr (1 / 4) * real (n + 1) * (real (n choose (n div 2)) / 6 powr (real n / 4)) + 1"
proof -
  fix fs :: "nat form list"
  assume "\<forall>f\<in>set fs. MCNF 3 f" "\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma>"
  then have "real (n choose (n div 2)) \<le> real (length fs) * 6 powr ((real n + 1) / 4)"
    by (rule majority_mcnfs_any)
  then show "real (n choose (n div 2)) / 6 powr ((real n + 1) / 4) \<le> real (length fs)"
    by (simp add: divide_le_eq)
next
  obtain gs where "\<forall>g\<in>set gs. MCNF 3 g" "\<forall>\<sigma>. eval \<sigma> (Or gs) \<longleftrightarrow> majority n \<sigma>"
    "real (length gs) \<le> 6 powr (1 / 4) * real (n + 1) * real (n choose (n div 2)) / 6 powr (real n / 4) + 1"
    by (rule majority_mcnfs_upper_any)
  then show "\<exists>fs. (\<forall>f\<in>set fs. MCNF 3 f) \<and> (\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma>) \<and>
      real (length fs) \<le> 6 powr (1 / 4) * real (n + 1) * (real (n choose (n div 2)) / 6 powr (real n / 4)) + 1"
    by (intro exI[of _ gs]) simp
qed

end
