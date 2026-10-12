theory Majority_3CNF
  imports "Monotone_Sigma3.Monotone_3CNF" "Majority_AC0.Depth3_Lower"
begin

section \<open>Monotone depth-3 formulas with bottom fan-in 3 for Majority\<close>

text \<open>
  The consequence of \<open>gkprst_half\<close> stated in the paper: a monotone OR of 3-CNFs computing
  Majority on \<open>n\<close> (even) variables needs at least \<open>(n choose n/2) / 6\<^bsup>n/4\<^esup>\<close> CNFs, hence size
  \<open>\<ge> (2/6\<^bsup>1/4\<^esup>)\<^sup>n / (n+1) \<approx> 1.278\<^sup>n / (n+1)\<close>.  Each CNF rejects every input of weight below
  \<open>n/2\<close>, so viewed as a set system on \<open>{..<n}\<close> it has no transversal of size below \<open>n/2\<close>, and
  its accepted inputs of weight \<open>n/2\<close> are exactly its transversals of size \<open>n/2\<close>.\<close>

text \<open>\<open>MCNF w f\<close>: \<open>f\<close> is an AND of clauses, each an OR of at most \<open>w\<close> positive literals.\<close>

definition MCNF :: "nat \<Rightarrow> 'v form \<Rightarrow> bool" where
  "MCNF w f \<longleftrightarrow> (\<exists>cs. f = And cs \<and>
     (\<forall>c\<in>set cs. \<exists>ls. c = Or ls \<and> length ls \<le> w \<and> (\<forall>l\<in>set ls. \<exists>v. l = Lit v True)))"

lemma MCNF_CNF: "MCNF w f \<Longrightarrow> CNF w f"
  unfolding MCNF_def CNF_def by fastforce

text \<open>The clause sets of a monotone CNF, restricted to the variables below \<open>n\<close>.\<close>

fun pclause :: "nat \<Rightarrow> nat form \<Rightarrow> nat set" where
  "pclause n (Or ls) = {v. v < n \<and> Lit v True \<in> set ls}"
| "pclause n _ = {}"

fun pcnf :: "nat \<Rightarrow> nat form \<Rightarrow> nat set set" where
  "pcnf n (And cs) = pclause n ` set cs"
| "pcnf n _ = {}"

lemma pclause_card:
  "card (pclause n (Or ls)) \<le> length ls"
proof -
  have "card (pclause n (Or ls)) \<le> card (set ls)"
  proof (rule card_inj_on_le)
    show "inj_on (\<lambda>v. Lit v True) (pclause n (Or ls))" by (auto simp: inj_on_def)
    show "(\<lambda>v. Lit v True) ` pclause n (Or ls) \<subseteq> set ls" by auto
  qed simp
  also have "\<dots> \<le> length ls" by (rule card_length)
  finally show ?thesis .
qed

lemma pcnf_cnf:
  assumes "MCNF 3 f"
  shows "cnf {..<n} (pcnf n f)"
proof -
  obtain cs where f: "f = And cs"
    and cs: "\<forall>c\<in>set cs. \<exists>ls. c = Or ls \<and> length ls \<le> 3 \<and> (\<forall>l\<in>set ls. \<exists>v. l = Lit v True)"
    using assms by (auto simp: MCNF_def)
  have "C \<subseteq> {..<n} \<and> card C \<le> 3" if C: "C \<in> pcnf n f" for C
  proof -
    obtain c where c: "c \<in> set cs" "C = pclause n c" using C by (auto simp: f)
    obtain ls where ls: "c = Or ls" "length ls \<le> 3" using cs c(1) by blast
    have "card C \<le> 3" using pclause_card[of n ls] ls c(2) by simp
    moreover have "C \<subseteq> {..<n}" using c(2) ls(1) by auto
    ultimately show ?thesis by blast
  qed
  then show ?thesis by (simp add: cnf_def)
qed

lemma eval_pcnf:
  assumes f: "MCNF w f" and X: "X \<subseteq> {..<n}"
  shows "eval (\<lambda>v. v \<in> X) f \<longleftrightarrow> hits (pcnf n f) X"
proof -
  obtain cs where fc: "f = And cs"
    and cs: "\<forall>c\<in>set cs. \<exists>ls. c = Or ls \<and> length ls \<le> w \<and> (\<forall>l\<in>set ls. \<exists>v. l = Lit v True)"
    using f by (auto simp: MCNF_def)
  have cl: "eval (\<lambda>v. v \<in> X) c \<longleftrightarrow> pclause n c \<inter> X \<noteq> {}" if c: "c \<in> set cs" for c
  proof -
    obtain ls where ls: "c = Or ls" and pos: "\<forall>l\<in>set ls. \<exists>v. l = Lit v True" using cs c by blast
    show ?thesis
    proof
      assume "eval (\<lambda>v. v \<in> X) c"
      then obtain g where g: "g \<in> set ls" "eval (\<lambda>v. v \<in> X) g" by (auto simp: ls)
      obtain v where v: "g = Lit v True" using pos g(1) by blast
      have "v \<in> X" using g(2) v by simp
      moreover have "v < n" using X \<open>v \<in> X\<close> by blast
      ultimately have "v \<in> pclause n c \<inter> X" using g(1) v by (simp add: ls)
      then show "pclause n c \<inter> X \<noteq> {}" by blast
    next
      assume "pclause n c \<inter> X \<noteq> {}"
      then obtain v where "Lit v True \<in> set ls" "v \<in> X" by (auto simp: ls)
      then show "eval (\<lambda>v. v \<in> X) c" by (force simp: ls)
    qed
  qed
  show ?thesis using cl by (auto simp: fc hits_def)
qed

text \<open>The count: the CNFs cover the slice, and each covers at most \<open>6\<^bsup>n/4\<^esup>\<close> of it.\<close>

theorem majority_mcnfs:
  fixes fs :: "nat form list"
  assumes cnf: "\<forall>f\<in>set fs. MCNF 3 f" and maj: "\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma>"
    and n: "even n"
  shows "real (n choose (n div 2)) \<le> real (length fs) * 6 powr (real n / 4)"
proof -
  define t where "t = n div 2"
  have nt: "n = 2 * t" using n by (simp add: t_def)
  define Sl where "Sl = {X. X \<subseteq> {..<n} \<and> card X = t}"
  have ev: "eval (\<lambda>v. v \<in> X) f \<longleftrightarrow> hits (pcnf n f) X" if "f \<in> set fs" "X \<subseteq> {..<n}" for f X
    using eval_pcnf cnf that by blast
  have thr: "thr {..<n} (pcnf n f) t" if f: "f \<in> set fs" for f
    unfolding thr_def
  proof (intro allI impI)
    fix X assume X: "X \<subseteq> {..<n}" and h: "hits (pcnf n f) X"
    have "eval (\<lambda>v. v \<in> X) f" using ev[OF f X] h by simp
    then have "majority n (\<lambda>v. v \<in> X)" using spec[OF maj, of "\<lambda>v. v \<in> X"] f by blast
    then show "t \<le> card X" using X nt by (simp add: majority_def weight_set)
  qed
  have bnd: "real (card (trans {..<n} (pcnf n f) t)) \<le> 6 powr (real n / 4)" if f: "f \<in> set fs" for f
  proof -
    have "cnf {..<n} (pcnf n f)" using pcnf_cnf cnf f by blast
    moreover have "card {..<n} = 2 * t" using nt by simp
    ultimately show ?thesis using gkprst_half[of "{..<n}" "pcnf n f" t] thr[OF f] by simp
  qed
  have cover: "Sl \<subseteq> (\<Union>f\<in>set fs. trans {..<n} (pcnf n f) t)"
  proof
    fix X assume "X \<in> Sl"
    then have X: "X \<subseteq> {..<n}" "card X = t" by (auto simp: Sl_def)
    have "majority n (\<lambda>v. v \<in> X)" using X nt by (simp add: majority_def weight_set)
    then obtain f where f: "f \<in> set fs" "eval (\<lambda>v. v \<in> X) f"
      using spec[OF maj, of "\<lambda>v. v \<in> X"] by blast
    then have "X \<in> trans {..<n} (pcnf n f) t" using ev[OF f(1) X(1)] X by (simp add: trans_def)
    then show "X \<in> (\<Union>f\<in>set fs. trans {..<n} (pcnf n f) t)" using f(1) by blast
  qed
  have "n choose (n div 2) = card Sl" by (simp add: Sl_def t_def n_subsets)
  also have "\<dots> \<le> card (\<Union>f\<in>set fs. trans {..<n} (pcnf n f) t)"
  proof (rule card_mono[OF _ cover])
    have "(\<Union>f\<in>set fs. trans {..<n} (pcnf n f) t) \<subseteq> Pow {..<n}" by (auto simp: trans_def)
    then show "finite (\<Union>f\<in>set fs. trans {..<n} (pcnf n f) t)" by (rule finite_subset) simp
  qed
  also have "\<dots> \<le> (\<Sum>f\<in>set fs. card (trans {..<n} (pcnf n f) t))" by (rule card_UN_le) simp
  finally have nat: "n choose (n div 2) \<le> (\<Sum>f\<in>set fs. card (trans {..<n} (pcnf n f) t))" .
  have "real (n choose (n div 2)) \<le> (\<Sum>f\<in>set fs. real (card (trans {..<n} (pcnf n f) t)))"
  proof -
    have "real (n choose (n div 2)) \<le> real (\<Sum>f\<in>set fs. card (trans {..<n} (pcnf n f) t))"
      using nat by (simp only: of_nat_le_iff)
    then show ?thesis by simp
  qed
  also have "\<dots> \<le> (\<Sum>f\<in>set fs. 6 powr (real n / 4))" by (rule sum_mono) (rule bnd)
  also have "\<dots> = real (card (set fs)) * 6 powr (real n / 4)" by simp
  also have "\<dots> \<le> real (length fs) * 6 powr (real n / 4)"
    using card_length[of fs] by (intro mult_right_mono) simp_all
  finally show ?thesis .
qed

text \<open>Exponential form: \<open>(2/6\<^bsup>1/4\<^esup>)\<^sup>n \<le> (n+1) \<cdot> #CNFs\<close>, where \<open>2/6\<^bsup>1/4\<^esup> > 1.2779\<close>.\<close>

corollary majority_mcnfs_exp:
  fixes fs :: "nat form list"
  assumes "\<forall>f\<in>set fs. MCNF 3 f" "\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma>" "even n"
  shows "(2 / 6 powr (1 / 4)) powr real n \<le> real (n + 1) * real (length fs)"
proof -
  define a :: real where "a = 6 powr (real n / 4)"
  have a0: "0 < a" by (simp add: a_def)
  have "(2::real) ^ n \<le> real (n + 1) * real (n choose (n div 2))"
  proof -
    have "(2::nat) ^ n \<le> (n + 1) * (n choose (n div 2))" by (rule slice_lower)
    then have "real ((2::nat) ^ n) \<le> real ((n + 1) * (n choose (n div 2)))" by (simp only: of_nat_le_iff)
    then show ?thesis by (simp only: of_nat_mult of_nat_power) simp
  qed
  also have "\<dots> \<le> real (n + 1) * (real (length fs) * a)"
    using majority_mcnfs[OF assms] by (intro mult_left_mono) (simp_all add: a_def)
  finally have "(2::real) ^ n \<le> real (n + 1) * real (length fs) * a" by (simp add: mult.assoc)
  then have le: "(2::real) ^ n / a \<le> real (n + 1) * real (length fs)" using a0 by (simp add: divide_le_eq)
  have "(2 / 6 powr (1 / 4)) powr real n = 2 powr real n / (6 powr (1 / 4)) powr real n"
    by (rule powr_divide)
  also have "\<dots> = (2::real) ^ n / a" by (simp add: a_def powr_powr powr_realpow)
  finally show ?thesis using le by simp
qed

text \<open>As formula size: an OR of monotone 3-CNFs computing Majority.\<close>

corollary majority_mcnf_formula:
  fixes gs :: "nat form list"
  assumes "\<forall>g\<in>set gs. MCNF 3 g" "\<forall>\<sigma>. eval \<sigma> (Or gs) = majority n \<sigma>" "even n"
  shows "real (n choose (n div 2)) \<le> real (gates (Or gs)) * 6 powr (real n / 4)"
    and "(2 / 6 powr (1 / 4)) powr real n \<le> real (n + 1) * real (gates (Or gs))"
proof -
  have g1: "1 \<le> gates g" if g: "g \<in> set gs" for g
  proof -
    obtain cs where "g = And cs" using assms(1) g by (auto simp: MCNF_def)
    then show ?thesis by simp
  qed
  have "length gs = (\<Sum>g\<leftarrow>gs. 1)" by (simp add: sum_list_triv)
  also have "\<dots> \<le> (\<Sum>g\<leftarrow>gs. gates g)" using g1 by (intro sum_list_mono) blast
  finally have L: "real (length gs) \<le> real (gates (Or gs))" by simp
  have maj: "\<forall>\<sigma>. (\<exists>g\<in>set gs. eval \<sigma> g) \<longleftrightarrow> majority n \<sigma>" using assms(2) by simp
  show "real (n choose (n div 2)) \<le> real (gates (Or gs)) * 6 powr (real n / 4)"
    using majority_mcnfs[OF assms(1) maj assms(3)] L by (smt (verit) mult_right_mono powr_ge_zero)
  show "(2 / 6 powr (1 / 4)) powr real n \<le> real (n + 1) * real (gates (Or gs))"
    using majority_mcnfs_exp[OF assms(1) maj assms(3)] L by (smt (verit) mult_left_mono of_nat_0_le_iff)
qed

end
