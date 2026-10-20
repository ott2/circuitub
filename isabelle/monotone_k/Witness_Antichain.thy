theory Witness_Antichain
  imports Shearer_Conditional "HOL-Library.FuncSet"
begin

text \<open>
  Witness parts make sizes irrelevant (log \<section>6h). Label each transversal \<open>X\<close> by a family of
  parts \<open>g X\<close> covering \<open>V\<close> such that every one \<open>v \<in> X \<inter> K\<close> has a critical edge (\<open>e \<inter> X = {v}\<close>)
  inside its part \<open>K\<close> (\<open>wclosed\<close>); the witness components are one such labelling. Then within a
  class the traces \<open>X \<inter> K\<close> form an antichain (\<open>class_antichain\<close>), so by Sperner (\<open>sperner\<close>,
  via the LYM inequality \<open>lym\<close>, proved by induction without permutations) a part \<open>K\<close> carries at
  most \<open>|K| choose |K|/2\<close> traces, whatever their sizes. Hence (\<open>witness_bound\<close>)
  \<open>ln |F| \<le> H(g) + E \<Sum>\<^sub>K ln (|K| choose |K|/2)\<close>, and for partitions (\<open>witness_partition\<close>)
  \<open>ln |F| \<le> H(g) + |V| ln 2 - E \<Sum>\<^sub>K ln ((3|K|+2)/2) / 2\<close>: no concentration of sizes is needed.
\<close>

definition antich :: "'a set set \<Rightarrow> bool" where
  "antich A \<longleftrightarrow> (\<forall>S\<in>A. \<forall>T\<in>A. S \<subseteq> T \<longrightarrow> S = T)"

lemma lym_n:
  assumes A: "antich A"
  shows "finite U \<Longrightarrow> card U = n \<Longrightarrow>
    (\<Sum>T\<in>{T\<in>A. T \<subseteq> U}. fact (card T) * fact (card U - card T)) \<le> (fact (card U) :: nat)"
proof (induct n arbitrary: U)
  case 0
  then have U: "U = {}" by simp
  have "{T\<in>A. T \<subseteq> U} \<subseteq> {{}}" using U by blast
  then have "card {T\<in>A. T \<subseteq> U} \<le> 1" using card_mono[of "{{}}"] by simp
  moreover have "(\<Sum>T\<in>{T\<in>A. T \<subseteq> U}. fact (card T) * fact (card U - card T)) = card {T\<in>A. T \<subseteq> U}"
    using U by (simp add: subset_empty)
  ultimately show ?case using U by simp
next
  case (Suc m)
  note finU = Suc.prems(1) and cU = Suc.prems(2)
  define S where "S = {T\<in>A. T \<subseteq> U}"
  have finS: "finite S" unfolding S_def
    by (rule finite_subset[of _ "Pow U"]) (use finU in auto)
  show ?case
  proof (cases "U \<in> A")
    case True
    have "S = {U}" unfolding S_def using True A unfolding antich_def by blast
    then show ?thesis unfolding S_def[symmetric] by simp
  next
    case False
    define w where "w T = (fact (card T) * fact (m - card T) :: nat)" for T :: "'a set"
    have psub: "T \<subset> U" if "T \<in> S" for T using that False unfolding S_def by blast
    have tm: "fact (card T) * fact (card U - card T) = card {x\<in>U. x \<notin> T} * w T" if T: "T \<in> S" for T
    proof -
      have "card T < card U" using psub[OF T] finU by (simp add: psubset_card_mono)
      then have d: "card U - card T = Suc (m - card T)" using cU by simp
      have TU: "T \<subseteq> U" using psub[OF T] by blast
      have finT: "finite T" by (rule finite_subset[OF TU finU])
      have "{x\<in>U. x \<notin> T} = U - T" by blast
      then have "card {x\<in>U. x \<notin> T} = card U - card T"
        using card_Diff_subset[OF finT TU] by simp
      then show ?thesis unfolding w_def d by (simp add: fact_Suc algebra_simps)
    qed
    have "(\<Sum>T\<in>S. fact (card T) * fact (card U - card T)) = (\<Sum>T\<in>S. card {x\<in>U. x \<notin> T} * w T)"
      by (rule sum.cong) (simp_all add: tm)
    also have "\<dots> = (\<Sum>T\<in>S. \<Sum>x\<in>{x\<in>U. x \<notin> T}. w T)" by simp
    also have "\<dots> = (\<Sum>x\<in>U. \<Sum>T\<in>{T\<in>S. x \<notin> T}. w T)"
      by (rule sum.swap_restrict[OF finS finU])
    also have "\<dots> \<le> (\<Sum>x\<in>U. fact m)"
    proof (rule sum_mono)
      fix x assume x: "x \<in> U"
      have finUx: "finite (U - {x})" using finU by simp
      have cUx: "card (U - {x}) = m" using cU x finU by simp
      have eq: "{T\<in>S. x \<notin> T} = {T\<in>A. T \<subseteq> U - {x}}" unfolding S_def by blast
      have "(\<Sum>T\<in>{T\<in>A. T \<subseteq> U - {x}}. fact (card T) * fact (card (U - {x}) - card T)) \<le> (fact (card (U - {x})) :: nat)"
        by (rule Suc.hyps[OF finUx cUx])
      then show "(\<Sum>T\<in>{T\<in>S. x \<notin> T}. w T) \<le> fact m" unfolding eq w_def cUx .
    qed
    also have "\<dots> = fact (card U)" using cU by (simp add: fact_Suc)
    finally show ?thesis unfolding S_def .
  qed
qed

theorem lym:
  assumes "antich A" and "finite U"
  shows "(\<Sum>T\<in>{T\<in>A. T \<subseteq> U}. fact (card T) * fact (card U - card T)) \<le> (fact (card U) :: nat)"
  by (rule lym_n[OF assms(1) assms(2) refl])

theorem sperner:
  assumes A: "antich A" and finU: "finite U" and AU: "\<forall>T\<in>A. T \<subseteq> U"
  shows "card A \<le> card U choose (card U div 2)"
proof -
  define n where "n = card U"
  define M where "M = n choose (n div 2)"
  have SA: "{T\<in>A. T \<subseteq> U} = A" using AU by blast
  have finA: "finite A" by (rule finite_subset[of _ "Pow U"]) (use AU finU in auto)
  have each: "fact n \<le> M * (fact (card T) * fact (n - card T))" if T: "T \<in> A" for T
  proof -
    have le: "card T \<le> n" unfolding n_def using AU T finU by (simp add: card_mono)
    have "fact n = fact (card T) * fact (n - card T) * (n choose card T)"
      by (rule binomial_fact_lemma[OF le, symmetric])
    also have "\<dots> \<le> fact (card T) * fact (n - card T) * M"
      unfolding M_def by (rule mult_left_mono) (simp_all add: binomial_maximum)
    finally show ?thesis by (simp add: ac_simps)
  qed
  have "card A * fact n = (\<Sum>T\<in>A. fact n)" by simp
  also have "\<dots> \<le> (\<Sum>T\<in>A. M * (fact (card T) * fact (n - card T)))" by (rule sum_mono) (rule each)
  also have "\<dots> = M * (\<Sum>T\<in>A. fact (card T) * fact (n - card T))" by (simp add: sum_distrib_left)
  also have "\<dots> \<le> M * fact n"
    using lym[OF A finU] unfolding SA n_def[symmetric] by (rule mult_left_mono) simp
  finally have "card A * fact n \<le> M * fact n" .
  then show ?thesis unfolding M_def n_def by simp
qed

definition wclosed :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "wclosed H X P \<longleftrightarrow> (\<forall>K\<in>P. \<forall>v\<in>X \<inter> K. \<exists>e\<in>H. e \<subseteq> K \<and> e \<inter> X = {v})"

lemma class_antichain:
  assumes tr: "\<forall>Y\<in>G. \<forall>e\<in>H. e \<inter> Y \<noteq> {}" and cl: "\<forall>Y\<in>G. wclosed H Y P" and K: "K \<in> P"
  shows "antich ((\<lambda>Y. Y \<inter> K) ` G)"
  unfolding antich_def
proof (intro ballI impI)
  fix S T assume S: "S \<in> (\<lambda>Y. Y \<inter> K) ` G" and T: "T \<in> (\<lambda>Y. Y \<inter> K) ` G" and ST: "S \<subseteq> T"
  obtain Y where Y: "Y \<in> G" and SY: "S = Y \<inter> K" using S by blast
  obtain Y' where Y': "Y' \<in> G" and TY: "T = Y' \<inter> K" using T by blast
  have "T \<subseteq> S"
  proof
    fix v assume v: "v \<in> T"
    then have vY': "v \<in> Y' \<inter> K" using TY by simp
    obtain e where e: "e \<in> H" and eK: "e \<subseteq> K" and eY': "e \<inter> Y' = {v}"
      using cl Y' K vY' unfolding wclosed_def by blast
    obtain u where u: "u \<in> e \<inter> Y" using tr Y e by blast
    have "u \<in> S" using u eK SY by blast
    then have "u \<in> Y' \<inter> e" using ST TY u by blast
    then have "u = v" using eY' by blast
    then show "v \<in> S" using \<open>u \<in> S\<close> by simp
  qed
  then show "S = T" using ST by blast
qed

lemma card_traces:
  assumes finG: "finite G" and finP: "finite P" and GP: "\<forall>Y\<in>G. Y \<subseteq> \<Union>P"
  shows "card G \<le> (\<Prod>K\<in>P. card ((\<lambda>Y. Y \<inter> K) ` G))"
proof -
  define f where "f Y = (\<lambda>K\<in>P. Y \<inter> K)" for Y
  have inj: "inj_on f G"
  proof (rule inj_onI)
    fix Y Y' assume Y: "Y \<in> G" and Y': "Y' \<in> G" and eq: "f Y = f Y'"
    have "Y \<inter> K = Y' \<inter> K" if "K \<in> P" for K
      using fun_cong[OF eq, of K] that unfolding f_def by simp
    then have "Y \<inter> \<Union>P = Y' \<inter> \<Union>P" by blast
    then show "Y = Y'" using GP Y Y' by blast
  qed
  have img: "f ` G \<subseteq> PiE P (\<lambda>K. (\<lambda>Y. Y \<inter> K) ` G)" unfolding f_def by auto
  have finPi: "finite (PiE P (\<lambda>K. (\<lambda>Y. Y \<inter> K) ` G))"
    by (rule finite_PiE[OF finP]) (use finG in simp)
  have "card G = card (f ` G)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card (PiE P (\<lambda>K. (\<lambda>Y. Y \<inter> K) ` G))" by (rule card_mono[OF finPi img])
  also have "\<dots> = (\<Prod>K\<in>P. card ((\<lambda>Y. Y \<inter> K) ` G))" by (rule card_PiE[OF finP])
  finally show ?thesis .
qed

theorem witness_bound:
  fixes g :: "'a set \<Rightarrow> 'a set set"
  assumes fin: "finite F" and ne: "F \<noteq> {}" and finV: "finite V" and FV: "\<forall>X\<in>F. X \<subseteq> V"
    and tr: "\<forall>X\<in>F. \<forall>e\<in>H. e \<inter> X \<noteq> {}"
    and parts: "\<forall>X\<in>F. \<Union>(g X) = V"
    and cl: "\<forall>X\<in>F. wclosed H X (g X)"
  shows "ln (real (card F)) \<le> lent F g
           + (\<Sum>X\<in>F. \<Sum>K\<in>g X. ln (real (card K choose (card K div 2)))) / real (card F)"
proof -
  define N where "N = real (card F)"
  have N0: "0 < N" unfolding N_def using fin ne by (simp add: card_gt_0_iff)
  have key: "ln N = lent F g + (\<Sum>X\<in>F. ln (real (lcls F g X))) / N"
    unfolding lent_def N_def by simp
  have each: "ln (real (lcls F g X)) \<le> (\<Sum>K\<in>g X. ln (real (card K choose (card K div 2))))"
    if X: "X \<in> F" for X
  proof -
    define G where "G = {Y\<in>F. g Y = g X}"
    define P where "P = g X"
    have finG: "finite G" unfolding G_def using fin by simp
    have XG: "X \<in> G" unfolding G_def using X by simp
    have UP: "\<Union>P = V" unfolding P_def using parts X by blast
    have finP: "finite P" using finite_UnionD[of P] finV UP by simp
    have finK: "finite K" if "K \<in> P" for K
      by (rule finite_subset[OF _ finV]) (use that UP in blast)
    have GP: "\<forall>Y\<in>G. Y \<subseteq> \<Union>P" using FV UP unfolding G_def by blast
    have trG: "\<forall>Y\<in>G. \<forall>e\<in>H. e \<inter> Y \<noteq> {}" using tr unfolding G_def by blast
    have clG: "\<forall>Y\<in>G. wclosed H Y P" using cl unfolding G_def P_def by force
    have tK: "card ((\<lambda>Y. Y \<inter> K) ` G) \<le> card K choose (card K div 2)" if K: "K \<in> P" for K
      by (rule sperner[OF class_antichain[OF trG clG K] finK[OF K]]) blast
    have "card G \<le> (\<Prod>K\<in>P. card ((\<lambda>Y. Y \<inter> K) ` G))" by (rule card_traces[OF finG finP GP])
    also have "\<dots> \<le> (\<Prod>K\<in>P. card K choose (card K div 2))" by (rule prod_mono) (simp add: tK)
    finally have "real (card G) \<le> real (\<Prod>K\<in>P. card K choose (card K div 2))" by (simp only: of_nat_le_iff)
    then have le: "real (card G) \<le> (\<Prod>K\<in>P. real (card K choose (card K div 2)))" by simp
    have pos: "0 < real (card G)" using finG XG by (auto simp: card_gt_0_iff)
    have "ln (real (card G)) \<le> ln (\<Prod>K\<in>P. real (card K choose (card K div 2)))"
      by (rule ln_mono[OF le pos])
    also have "\<dots> = (\<Sum>K\<in>P. ln (real (card K choose (card K div 2))))"
      by (rule ln_prod[OF finP]) simp
    finally show ?thesis unfolding lcls_def G_def[symmetric] P_def .
  qed
  have "(\<Sum>X\<in>F. ln (real (lcls F g X))) \<le> (\<Sum>X\<in>F. \<Sum>K\<in>g X. ln (real (card K choose (card K div 2))))"
    by (rule sum_mono) (rule each)
  then have "(\<Sum>X\<in>F. ln (real (lcls F g X))) / N
      \<le> (\<Sum>X\<in>F. \<Sum>K\<in>g X. ln (real (card K choose (card K div 2)))) / N"
    by (rule divide_right_mono) (use N0 in simp)
  then show ?thesis using key unfolding N_def by linarith
qed

corollary witness_partition:
  fixes g :: "'a set \<Rightarrow> 'a set set"
  assumes fin: "finite F" and ne: "F \<noteq> {}" and finV: "finite V" and FV: "\<forall>X\<in>F. X \<subseteq> V"
    and tr: "\<forall>X\<in>F. \<forall>e\<in>H. e \<inter> X \<noteq> {}"
    and parts: "\<forall>X\<in>F. \<Union>(g X) = V" and disj: "\<forall>X\<in>F. pairwise disjnt (g X)"
    and cl: "\<forall>X\<in>F. wclosed H X (g X)"
  shows "ln (real (card F)) \<le> lent F g + real (card V) * ln 2
           - (\<Sum>X\<in>F. \<Sum>K\<in>g X. ln ((3 * real (card K) + 2) / 2) / 2) / real (card F)"
proof -
  define N where "N = real (card F)"
  have N0: "0 < N" unfolding N_def using fin ne by (simp add: card_gt_0_iff)
  have each: "(\<Sum>K\<in>g X. ln (real (card K choose (card K div 2))))
      \<le> real (card V) * ln 2 - (\<Sum>K\<in>g X. ln ((3 * real (card K) + 2) / 2) / 2)" if X: "X \<in> F" for X
  proof -
    have UP: "\<Union>(g X) = V" using parts X by blast
    have finP: "finite (g X)" using finite_UnionD[of "g X"] finV UP by simp
    have finK: "\<forall>K\<in>g X. finite K" using UP finV by (metis Union_upper finite_subset)
    have cV: "card V = (\<Sum>K\<in>g X. card K)"
      using card_Union_disjoint[of "g X"] disj X finK UP by simp
    have "(\<Sum>K\<in>g X. ln (real (card K choose (card K div 2))))
        \<le> (\<Sum>K\<in>g X. real (card K) * ln 2 - ln ((3 * real (card K) + 2) / 2) / 2)"
      by (rule sum_mono, rule ln_binom, simp)
    also have "\<dots> = real (card V) * ln 2 - (\<Sum>K\<in>g X. ln ((3 * real (card K) + 2) / 2) / 2)"
      unfolding cV by (simp add: sum_subtractf sum_distrib_right)
    finally show ?thesis .
  qed
  have "(\<Sum>X\<in>F. \<Sum>K\<in>g X. ln (real (card K choose (card K div 2))))
      \<le> (\<Sum>X\<in>F. real (card V) * ln 2 - (\<Sum>K\<in>g X. ln ((3 * real (card K) + 2) / 2) / 2))"
    by (rule sum_mono) (rule each)
  also have "\<dots> = N * (real (card V) * ln 2) - (\<Sum>X\<in>F. \<Sum>K\<in>g X. ln ((3 * real (card K) + 2) / 2) / 2)"
    unfolding N_def by (simp add: sum_subtractf)
  finally have "(\<Sum>X\<in>F. \<Sum>K\<in>g X. ln (real (card K choose (card K div 2)))) / N
      \<le> (N * (real (card V) * ln 2) - (\<Sum>X\<in>F. \<Sum>K\<in>g X. ln ((3 * real (card K) + 2) / 2) / 2)) / N"
    by (rule divide_right_mono) (use N0 in simp)
  also have "\<dots> = real (card V) * ln 2 - (\<Sum>X\<in>F. \<Sum>K\<in>g X. ln ((3 * real (card K) + 2) / 2) / 2) / N"
    using N0 by (simp add: diff_divide_distrib)
  finally show ?thesis
    using witness_bound[OF fin ne finV FV tr parts cl] unfolding N_def by linarith
qed

end
