theory Cover
  imports Complex_Main
begin

section \<open>The covering step (probabilistic method, made deterministic)\<close>

text \<open>
  Abstract setting: a finite universe \<open>U\<close> of things to cover, a finite family \<open>\<Theta>\<close> of tests,
  and a relation \<open>R \<theta> u\<close> (test \<open>\<theta>\<close> covers \<open>u\<close>).  If every \<open>u\<close> is covered by at least \<open>a > 0\<close>
  tests, then few tests cover everything.  This replaces the paper's expectation argument
  (\<open>2\<^sup>n (1-p)\<^sup>T < 1\<close>) by the greedy argument with the same bound.
\<close>

lemma double_count:
  assumes "finite U" "finite \<Theta>"
  shows "(\<Sum>\<theta>\<in>\<Theta>. card {u\<in>U. R \<theta> u}) = (\<Sum>u\<in>U. card {\<theta>\<in>\<Theta>. R \<theta> u})"
proof -
  have c1: "card {u\<in>U. R \<theta> u} = (\<Sum>u\<in>U. if R \<theta> u then 1 else 0)" for \<theta>
    using assms(1) by (simp add: sum.inter_filter[symmetric])
  have c2: "card {\<theta>\<in>\<Theta>. R \<theta> u} = (\<Sum>\<theta>\<in>\<Theta>. if R \<theta> u then 1 else 0)" for u
    using assms(2) by (simp add: sum.inter_filter[symmetric])
  show ?thesis by (simp only: c1 c2 sum.swap[of _ \<Theta> U])
qed

lemma averaging:
  assumes "finite U" "finite \<Theta>" "\<Theta> \<noteq> {}"
    and wit: "\<And>u. u \<in> U \<Longrightarrow> a \<le> card {\<theta>\<in>\<Theta>. R \<theta> u}"
  shows "\<exists>\<theta>\<in>\<Theta>. card U * a \<le> card \<Theta> * card {u\<in>U. R \<theta> u}"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have lt: "\<And>\<theta>. \<theta> \<in> \<Theta> \<Longrightarrow> card \<Theta> * card {u\<in>U. R \<theta> u} < card U * a" by auto
  have "card \<Theta> * (\<Sum>\<theta>\<in>\<Theta>. card {u\<in>U. R \<theta> u}) = (\<Sum>\<theta>\<in>\<Theta>. card \<Theta> * card {u\<in>U. R \<theta> u})"
    by (simp add: sum_distrib_left)
  also have "\<dots> < (\<Sum>\<theta>\<in>\<Theta>. card U * a)"
    using assms(2,3) lt by (rule sum_strict_mono)
  also have "\<dots> = card \<Theta> * (card U * a)" by simp
  finally have A: "(\<Sum>\<theta>\<in>\<Theta>. card {u\<in>U. R \<theta> u}) < card U * a" by simp
  have "card U * a = (\<Sum>u\<in>U. a)" by simp
  also have "\<dots> \<le> (\<Sum>u\<in>U. card {\<theta>\<in>\<Theta>. R \<theta> u})" using wit by (rule sum_mono)
  also have "\<dots> = (\<Sum>\<theta>\<in>\<Theta>. card {u\<in>U. R \<theta> u})"
    using assms(1,2) by (rule double_count[symmetric])
  finally show False using A by simp
qed

lemma greedy_iter:
  assumes "finite U" "finite \<Theta>" "0 < a"
    and wit: "\<And>u. u \<in> U \<Longrightarrow> a \<le> card {\<theta>\<in>\<Theta>. R \<theta> u}"
  shows "\<exists>S\<subseteq>\<Theta>. card S \<le> T \<and>
           real (card {u\<in>U. \<forall>\<theta>\<in>S. \<not> R \<theta> u})
             \<le> real (card U) * (1 - real a / real (card \<Theta>)) ^ T"
  using assms
proof (induction T arbitrary: U)
  case 0
  have "{u\<in>U. \<forall>\<theta>\<in>{}. \<not> R \<theta> u} = U" by simp
  then show ?case by (intro exI[of _ "{}"]) simp
next
  case (Suc T)
  show ?case
  proof (cases "U = {}")
    case True
    then show ?thesis by (intro exI[of _ "{}"]) simp
  next
    case False
    then obtain u0 where u0: "u0 \<in> U" by blast
    have "a \<le> card {\<theta>\<in>\<Theta>. R \<theta> u0}" using Suc.prems(4) u0 by blast
    also have "\<dots> \<le> card \<Theta>" using Suc.prems(2) by (intro card_mono) auto
    finally have aT: "a \<le> card \<Theta>" .
    with Suc.prems(3) have T0: "card \<Theta> > 0" by simp
    then have "\<Theta> \<noteq> {}" by auto
    have "\<exists>\<theta>\<in>\<Theta>. card U * a \<le> card \<Theta> * card {u\<in>U. R \<theta> u}"
      by (rule averaging[OF Suc.prems(1,2) \<open>\<Theta> \<noteq> {}\<close>]) (rule Suc.prems(4))
    then obtain \<theta>0 where \<theta>0: "\<theta>0 \<in> \<Theta>" and big: "card U * a \<le> card \<Theta> * card {u\<in>U. R \<theta>0 u}"
      by blast
    define U' where "U' = {u\<in>U. \<not> R \<theta>0 u}"
    have finU': "finite U'" using Suc.prems(1) by (simp add: U'_def)
    have witU': "\<And>u. u \<in> U' \<Longrightarrow> a \<le> card {\<theta>\<in>\<Theta>. R \<theta> u}"
      using Suc.prems(4) by (simp add: U'_def)
    obtain S' where S': "S' \<subseteq> \<Theta>" "card S' \<le> T"
      and rem': "real (card {u\<in>U'. \<forall>\<theta>\<in>S'. \<not> R \<theta> u})
                   \<le> real (card U') * (1 - real a / real (card \<Theta>)) ^ T"
      using Suc.IH[OF finU' Suc.prems(2,3) witU'] by blast
    define \<rho> where "\<rho> = 1 - real a / real (card \<Theta>)"
    have \<rho>0: "0 \<le> \<rho>" using aT T0 by (simp add: \<rho>_def field_simps)
    have split: "card U = card U' + card {u\<in>U. R \<theta>0 u}"
      using Suc.prems(1) unfolding U'_def
      by (subst card_Un_disjoint[symmetric]) (auto intro: arg_cong[where f = card])
    define c where "c = card {u\<in>U. R \<theta>0 u}"
    have r1: "real (card U) = real (card U') + real c" using split by (simp add: c_def)
    have r2: "real (card U) * real a \<le> real (card \<Theta>) * real c"
      using big by (simp add: c_def flip: of_nat_mult)
    have r3: "real (card U) * real (card \<Theta>) = real (card U') * real (card \<Theta>) + real c * real (card \<Theta>)"
      using r1 by (simp add: algebra_simps)
    have "real (card U') * real (card \<Theta>) \<le> real (card U) * real (card \<Theta>) - real (card U) * real a"
      using r2 r3 by (simp add: algebra_simps)
    then have U'bound: "real (card U') \<le> real (card U) * \<rho>"
      using T0 by (simp add: \<rho>_def field_simps)
    have same: "{u\<in>U. \<forall>\<theta>\<in>insert \<theta>0 S'. \<not> R \<theta> u} = {u\<in>U'. \<forall>\<theta>\<in>S'. \<not> R \<theta> u}"
      by (auto simp: U'_def)
    have finS': "finite S'" using S'(1) Suc.prems(2) by (rule finite_subset)
    have "card (insert \<theta>0 S') \<le> Suc (card S')" using finS' by (simp add: card_insert_if)
    then have "card (insert \<theta>0 S') \<le> Suc T" using S'(2) by simp
    moreover have "insert \<theta>0 S' \<subseteq> \<Theta>" using S' \<theta>0 by simp
    moreover have "real (card {u\<in>U'. \<forall>\<theta>\<in>S'. \<not> R \<theta> u}) \<le> real (card U) * \<rho> ^ Suc T"
    proof -
      have "real (card {u\<in>U'. \<forall>\<theta>\<in>S'. \<not> R \<theta> u}) \<le> real (card U') * \<rho> ^ T"
        using rem' by (simp add: \<rho>_def)
      also have "\<dots> \<le> (real (card U) * \<rho>) * \<rho> ^ T"
        using U'bound \<rho>0 by (intro mult_right_mono) simp_all
      finally show ?thesis by (simp add: algebra_simps)
    qed
    ultimately show ?thesis
      unfolding same[symmetric] \<rho>_def by blast
  qed
qed

theorem cover:
  assumes "finite U" "finite \<Theta>" "0 < a"
    and wit: "\<And>u. u \<in> U \<Longrightarrow> a \<le> card {\<theta>\<in>\<Theta>. R \<theta> u}"
    and ra: "card \<Theta> \<le> r * a" and h: "card U < 2 ^ h"
  shows "\<exists>S\<subseteq>\<Theta>. card S \<le> r * h \<and> (\<forall>u\<in>U. \<exists>\<theta>\<in>S. R \<theta> u)"
proof (cases "U = {}")
  case True
  then show ?thesis by (intro exI[of _ "{}"]) simp
next
  case False
  then obtain u0 where u0: "u0 \<in> U" by blast
  have "a \<le> card {\<theta>\<in>\<Theta>. R \<theta> u0}" using wit u0 by blast
  also have "\<dots> \<le> card \<Theta>" using assms(2) by (intro card_mono) auto
  finally have aT: "a \<le> card \<Theta>" .
  with assms(3) have T0: "card \<Theta> > 0" by simp
  define \<rho> where "\<rho> = 1 - real a / real (card \<Theta>)"
  have \<rho>0: "0 \<le> \<rho>" using aT T0 by (simp add: \<rho>_def field_simps)
  have "\<exists>S\<subseteq>\<Theta>. card S \<le> r * h \<and>
          real (card {u\<in>U. \<forall>\<theta>\<in>S. \<not> R \<theta> u})
            \<le> real (card U) * (1 - real a / real (card \<Theta>)) ^ (r * h)"
    by (rule greedy_iter[OF assms(1-3)]) (rule wit)
  then obtain S where S: "S \<subseteq> \<Theta>" "card S \<le> r * h"
    and rem: "real (card {u\<in>U. \<forall>\<theta>\<in>S. \<not> R \<theta> u}) \<le> real (card U) * \<rho> ^ (r * h)"
    unfolding \<rho>_def by blast
  text \<open>\<open>\<rho>\<^sup>r \<le> e\<^sup>-\<^sup>1 \<le> 1/2\<close>, because \<open>r \<cdot> a \<ge> |\<Theta>|\<close>.\<close>
  have x: "real a / real (card \<Theta>) * real r \<ge> 1"
    using ra T0 by (simp add: field_simps flip: of_nat_mult of_nat_le_iff)
  have "\<rho> \<le> exp (- (real a / real (card \<Theta>)))"
    using exp_ge_add_one_self[of "- (real a / real (card \<Theta>))"] by (simp add: \<rho>_def)
  then have "\<rho> ^ r \<le> exp (- (real a / real (card \<Theta>))) ^ r"
    using \<rho>0 by (rule power_mono)
  also have "\<dots> = exp (- (real a / real (card \<Theta>) * real r))"
    by (simp add: exp_of_nat_mult[symmetric] mult.commute)
  also have "\<dots> \<le> exp (-1)" using x by simp
  also have "\<dots> \<le> 1 / 2"
  proof -
    have "2 \<le> exp (1::real)" using exp_ge_add_one_self[of 1] by simp
    then show ?thesis by (simp add: exp_minus field_simps)
  qed
  finally have \<rho>r: "\<rho> ^ r \<le> 1 / 2" .
  have "\<rho> ^ (r * h) = (\<rho> ^ r) ^ h" by (simp add: power_mult)
  also have "\<dots> \<le> (1 / 2) ^ h" using \<rho>r \<rho>0 by (intro power_mono) simp_all
  finally have "real (card U) * \<rho> ^ (r * h) \<le> real (card U) * (1 / 2) ^ h"
    by (intro mult_left_mono) simp_all
  also have "\<dots> < 1"
  proof -
    have "real (card U) < 2 ^ h" using h by (simp flip: of_nat_less_iff)
    then show ?thesis by (simp add: field_simps)
  qed
  finally have "card {u\<in>U. \<forall>\<theta>\<in>S. \<not> R \<theta> u} = 0" using rem by linarith
  then have empty: "{u\<in>U. \<forall>\<theta>\<in>S. \<not> R \<theta> u} = {}" using assms(1) by simp
  have all: "\<forall>u\<in>U. \<exists>\<theta>\<in>S. R \<theta> u"
  proof
    fix u assume u: "u \<in> U"
    show "\<exists>\<theta>\<in>S. R \<theta> u"
    proof (rule ccontr)
      assume "\<not> (\<exists>\<theta>\<in>S. R \<theta> u)"
      then have "u \<in> {u\<in>U. \<forall>\<theta>\<in>S. \<not> R \<theta> u}" using u by simp
      then show False using empty by simp
    qed
  qed
  show ?thesis by (intro exI[of _ S] conjI S(1) S(2) all)
qed

end
