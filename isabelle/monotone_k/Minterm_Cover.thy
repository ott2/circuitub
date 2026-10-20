theory Minterm_Cover
  imports Witness_Antichain Shadow_Branch Harris_PPZ
begin

text \<open>
  Beyond Majority (log \<section>6j). For any Boolean function \<open>f\<close> on sets and any monotone CNF \<open>H\<close>
  below \<open>f\<close> (every transversal of \<open>H\<close> satisfies \<open>f\<close>), a minterm of \<open>f\<close> that satisfies \<open>H\<close> is a
  minimal transversal of \<open>H\<close> (\<open>minterm_mtr\<close>), and each of its elements has a critical edge
  (\<open>minterm_crit\<close>). So an OR of CNFs \<open>H\<^sub>i\<close>, \<open>i \<in> I\<close>, computing \<open>f\<close> covers the minterms of \<open>f\<close> by
  minimal transversals: \<open>#minterms \<le> \<Sum>\<^sub>i #mtr(H\<^sub>i)\<close> (\<open>minterm_cover\<close>). For Majority the minterms
  are the minimum transversals; in general the relevant count is that of minimal transversals,
  which is what \<open>witness_bound\<close> bounds. No monotonicity of \<open>f\<close> is used: only that transversals
  are closed upwards.
\<close>

definition minterm :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "minterm f X \<longleftrightarrow> f X \<and> (\<forall>v\<in>X. \<not> f (X - {v}))"

lemma tr_mono: "tr H X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> tr H Y"
  unfolding tr_def by blast

lemma minterm_mtr:
  assumes below: "\<forall>Y. tr H Y \<longrightarrow> f Y" and m: "minterm f X" and t: "tr H X"
  shows "mtr H X"
  unfolding mtr_def
proof (intro conjI allI impI)
  show "tr H X" by (rule t)
next
  fix X' assume X': "X' \<subset> X"
  show "\<not> tr H X'"
  proof
    assume tX': "tr H X'"
    obtain v where v: "v \<in> X" and vX': "v \<notin> X'" using X' by blast
    have "X' \<subseteq> X - {v}" using X' vX' by blast
    then have "tr H (X - {v})" by (rule tr_mono[OF tX'])
    then have "f (X - {v})" using below by blast
    then show False using m v unfolding minterm_def by blast
  qed
qed

lemma minterm_crit:
  assumes below: "\<forall>Y. tr H Y \<longrightarrow> f Y" and m: "minterm f X" and t: "tr H X" and v: "v \<in> X"
  shows "\<exists>e\<in>H. e \<inter> X = {v}"
proof -
  have "\<not> f (X - {v})" using m v unfolding minterm_def by blast
  then have "\<not> tr H (X - {v})" using below by blast
  then obtain e where e: "e \<in> H" and e0: "e \<inter> (X - {v}) = {}" unfolding tr_def by blast
  have "e \<inter> X \<noteq> {}" using t e unfolding tr_def by blast
  then have "e \<inter> X = {v}" using e0 by blast
  then show ?thesis using e by blast
qed

theorem minterm_cover:
  fixes Hs :: "'i \<Rightarrow> 'a set set"
  assumes finI: "finite I" and finV: "finite V"
    and below: "\<forall>i\<in>I. \<forall>Y. tr (Hs i) Y \<longrightarrow> f Y"
    and covers: "\<forall>X\<in>M. \<exists>i\<in>I. tr (Hs i) X"
    and mint: "\<forall>X\<in>M. minterm f X" and MV: "\<forall>X\<in>M. X \<subseteq> V"
  shows "card M \<le> (\<Sum>i\<in>I. card {X. X \<subseteq> V \<and> mtr (Hs i) X})"
proof -
  define A where "A i = {X. X \<subseteq> V \<and> mtr (Hs i) X}" for i
  have finA: "finite (A i)" for i unfolding A_def
    by (rule finite_subset[of _ "Pow V"]) (use finV in auto)
  have sub: "M \<subseteq> (\<Union>i\<in>I. A i)"
  proof
    fix X assume X: "X \<in> M"
    obtain i where i: "i \<in> I" and t: "tr (Hs i) X" using covers X by blast
    have "\<forall>Y. tr (Hs i) Y \<longrightarrow> f Y" using below i by blast
    then have "mtr (Hs i) X" using minterm_mtr mint X t by blast
    then show "X \<in> (\<Union>i\<in>I. A i)" using i X MV unfolding A_def by blast
  qed
  have finU: "finite (\<Union>i\<in>I. A i)" using finI finA by blast
  have "card M \<le> card (\<Union>i\<in>I. A i)" by (rule card_mono[OF finU sub])
  also have "\<dots> \<le> (\<Sum>i\<in>I. card (A i))" by (rule card_UN_le[OF finI])
  finally show ?thesis unfolding A_def .
qed

text \<open>
  A fixed partition into parts that each contain whole edges (for instance the connected
  components of \<open>H\<close>) is \<open>wclosed\<close> for every minimal transversal, so the minimal transversals number
  at most \<open>\<Prod>\<^sub>K (|K| choose |K|/2)\<close> (\<open>mtr_parts\<close>): (MT) holds when all parts have \<open>O(k)\<close> vertices.
\<close>

lemma mtr_crit:
  assumes "mtr H X" and "v \<in> X"
  shows "\<exists>e\<in>H. e \<inter> X = {v}"
proof -
  have "X - {v} \<subset> X" using assms(2) by blast
  then have "\<not> tr H (X - {v})" using assms(1) unfolding mtr_def by blast
  then obtain e where e: "e \<in> H" and e0: "e \<inter> (X - {v}) = {}" unfolding tr_def by blast
  have "e \<inter> X \<noteq> {}" using assms(1) e unfolding mtr_def tr_def by blast
  then show ?thesis using e e0 by blast
qed

theorem mtr_parts:
  assumes finV: "finite V" and UP: "\<Union>P = V" and disj: "pairwise disjnt P"
    and inside: "\<forall>e\<in>H. \<exists>K\<in>P. e \<subseteq> K"
  shows "card {X. X \<subseteq> V \<and> mtr H X} \<le> (\<Prod>K\<in>P. card K choose (card K div 2))"
proof -
  define G where "G = {X. X \<subseteq> V \<and> mtr H X}"
  have finG: "finite G" unfolding G_def by (rule finite_subset[of _ "Pow V"]) (use finV in auto)
  have finP: "finite P" using finite_UnionD[of P] finV UP by simp
  have finK: "finite K" if "K \<in> P" for K
    by (rule finite_subset[OF _ finV]) (use that UP in blast)
  have GP: "\<forall>Y\<in>G. Y \<subseteq> \<Union>P" using UP unfolding G_def by blast
  have trG: "\<forall>Y\<in>G. \<forall>e\<in>H. e \<inter> Y \<noteq> {}" unfolding G_def mtr_def tr_def by blast
  have clG: "\<forall>Y\<in>G. wclosed H Y P"
    unfolding wclosed_def
  proof (intro ballI)
    fix Y K v assume Y: "Y \<in> G" and K: "K \<in> P" and v: "v \<in> Y \<inter> K"
    have mY: "mtr H Y" using Y unfolding G_def by blast
    obtain e where e: "e \<in> H" and eY: "e \<inter> Y = {v}" using mtr_crit[OF mY] v by blast
    obtain K' where K': "K' \<in> P" and eK': "e \<subseteq> K'" using inside e by blast
    have "v \<in> K'" using eY eK' by blast
    then have "K' = K" using disj K K' v unfolding pairwise_def disjnt_def by blast
    then show "\<exists>e\<in>H. e \<subseteq> K \<and> e \<inter> Y = {v}" using e eK' eY by blast
  qed
  have tK: "card ((\<lambda>Y. Y \<inter> K) ` G) \<le> card K choose (card K div 2)" if K: "K \<in> P" for K
    by (rule sperner[OF class_antichain[OF trG clG K] finK[OF K]]) blast
  have "card G \<le> (\<Prod>K\<in>P. card ((\<lambda>Y. Y \<inter> K) ` G))" by (rule card_traces[OF finG finP GP])
  also have "\<dots> \<le> (\<Prod>K\<in>P. card K choose (card K div 2))" by (rule prod_mono) (simp add: tK)
  finally show ?thesis unfolding G_def .
qed

text \<open>
  With wide clauses. A minterm all of whose elements have a critical edge of size \<open>\<le> k\<close> is counted
  by \<open>harris_ppz\<close>; any other minterm has a critical edge \<open>e\<close> with \<open>|e| > k\<close>, and at most
  \<open>2^(n - |e|)\<close> sets meet \<open>e\<close> in a given single point (\<open>single_hit\<close>).
\<close>

lemma single_hit:
  assumes e: "e \<subseteq> {..<n}" and v: "v \<in> e"
  shows "card {X. X \<subseteq> {..<n} \<and> e \<inter> X = {v}} \<le> 2 ^ (n - card e)"
proof -
  have sub: "{X. X \<subseteq> {..<n} \<and> e \<inter> X = {v}} \<subseteq> insert v ` Pow ({..<n} - e)"
  proof
    fix X assume X: "X \<in> {X. X \<subseteq> {..<n} \<and> e \<inter> X = {v}}"
    then have "X = insert v (X - e)" "X - e \<in> Pow ({..<n} - e)" by blast+
    then show "X \<in> insert v ` Pow ({..<n} - e)" by (rule image_eqI)
  qed
  have finP: "finite (Pow ({..<n} - e))" by simp
  have "card {X. X \<subseteq> {..<n} \<and> e \<inter> X = {v}} \<le> card (insert v ` Pow ({..<n} - e))"
    by (rule card_mono[OF finite_imageI[OF finP] sub])
  also have "\<dots> \<le> card (Pow ({..<n} - e))" by (rule card_image_le[OF finP])
  also have "\<dots> = 2 ^ card ({..<n} - e)" by (simp add: card_Pow)
  also have "card ({..<n} - e) = n - card e"
    using card_Diff_subset[OF finite_subset[OF e] e] by simp
  finally show ?thesis .
qed

theorem minterm_depth3:
  fixes Hs :: "'i \<Rightarrow> nat set set" and n k t :: nat
  assumes finI: "finite I" and finH: "\<forall>i\<in>I. finite (Hs i)"
    and edges: "\<forall>i\<in>I. \<forall>e\<in>Hs i. e \<subseteq> {..<n}"
    and below: "\<forall>i\<in>I. \<forall>Y. tr (Hs i) Y \<longrightarrow> f Y"
    and covers: "\<forall>X\<in>M. \<exists>i\<in>I. tr (Hs i) X"
    and mint: "\<forall>X\<in>M. minterm f X \<and> X \<subseteq> {..<n} \<and> t \<le> card X"
  shows "real (card M) \<le> real (card I) * 2 ^ n / (1 + 1 / real k) ^ t
           + (\<Sum>i\<in>I. \<Sum>e\<in>{e\<in>Hs i. k < card e}. real (card e) * 2 ^ (n - card e))"
proof -
  define G where "G i = {X\<in>M. tr (Hs i) X \<and> (\<forall>v\<in>X. \<exists>e\<in>Hs i. v \<in> e \<and> e \<inter> X = {v}
                        \<and> e \<subseteq> {..<n} \<and> card e \<le> k)}" for i
  define W where "W i = {e\<in>Hs i. k < card e}" for i
  define S where "S e v = {X. X \<subseteq> {..<n} \<and> e \<inter> X = {v}}" for e :: "nat set" and v
  define B where "B = (\<Union>i\<in>I. \<Union>e\<in>W i. \<Union>v\<in>e. S e v)"
  have finM: "finite M" by (rule finite_subset[of _ "Pow {..<n}"]) (use mint in auto)
  have finG: "finite (G i)" for i unfolding G_def using finM by simp
  have finW: "finite (W i)" if "i \<in> I" for i unfolding W_def using finH that by simp
  have fine: "finite e" if i: "i \<in> I" and e: "e \<in> W i" for i e
  proof -
    have "e \<subseteq> {..<n}" using edges i e unfolding W_def by blast
    then show ?thesis by (rule finite_subset) simp
  qed
  have finS: "finite (S e v)" for e v unfolding S_def
    by (rule finite_subset[of _ "Pow {..<n}"]) auto
  have finB: "finite B" unfolding B_def using finI finW fine finS by blast
  have sub: "M \<subseteq> (\<Union>i\<in>I. G i) \<union> B"
  proof
    fix X assume X: "X \<in> M"
    obtain i where i: "i \<in> I" and t: "tr (Hs i) X" using covers X by blast
    have bi: "\<forall>Y. tr (Hs i) Y \<longrightarrow> f Y" using below i by blast
    have mX: "minterm f X" and XV: "X \<subseteq> {..<n}" using mint X by auto
    show "X \<in> (\<Union>i\<in>I. G i) \<union> B"
    proof (cases "\<forall>v\<in>X. \<exists>e\<in>Hs i. v \<in> e \<and> e \<inter> X = {v} \<and> e \<subseteq> {..<n} \<and> card e \<le> k")
      case True
      then have "X \<in> G i" unfolding G_def using X t by blast
      then show ?thesis using i by blast
    next
      case False
      then obtain v where v: "v \<in> X"
        and nv: "\<not> (\<exists>e\<in>Hs i. v \<in> e \<and> e \<inter> X = {v} \<and> e \<subseteq> {..<n} \<and> card e \<le> k)" by blast
      obtain e where e: "e \<in> Hs i" and eX: "e \<inter> X = {v}" using minterm_crit[OF bi mX t v] by blast
      have ve: "v \<in> e" using eX by blast
      have eV: "e \<subseteq> {..<n}" using edges i e by blast
      have "k < card e" using nv e ve eX eV by force
      then have eW: "e \<in> W i" unfolding W_def using e by blast
      have "X \<in> S e v" unfolding S_def using XV eX by blast
      then show ?thesis unfolding B_def using i eW ve by blast
    qed
  qed
  have cM: "card M \<le> (\<Sum>i\<in>I. card (G i)) + (\<Sum>i\<in>I. \<Sum>e\<in>W i. \<Sum>v\<in>e. card (S e v))"
  proof -
    have "card M \<le> card ((\<Union>i\<in>I. G i) \<union> B)"
      by (rule card_mono[OF _ sub]) (use finI finG finB in blast)
    also have "\<dots> \<le> card (\<Union>i\<in>I. G i) + card B" by (rule card_Un_le)
    also have "card (\<Union>i\<in>I. G i) \<le> (\<Sum>i\<in>I. card (G i))" by (rule card_UN_le[OF finI])
    also have "card B \<le> (\<Sum>i\<in>I. card (\<Union>e\<in>W i. \<Union>v\<in>e. S e v))" unfolding B_def by (rule card_UN_le[OF finI])
    also have "\<dots> \<le> (\<Sum>i\<in>I. \<Sum>e\<in>W i. card (\<Union>v\<in>e. S e v))"
      by (rule sum_mono) (rule card_UN_le[OF finW])
    also have "\<dots> \<le> (\<Sum>i\<in>I. \<Sum>e\<in>W i. \<Sum>v\<in>e. card (S e v))"
      by (rule sum_mono, rule sum_mono, rule card_UN_le[OF fine])
    finally show ?thesis by simp
  qed
  have cG: "real (card (G i)) \<le> 2 ^ n / (1 + 1 / real k) ^ t" for i
  proof -
    have prem: "\<forall>X\<in>G i. X \<subseteq> {..<n} \<and> (\<forall>e\<in>Hs i. e \<inter> X \<noteq> {}) \<and> t \<le> card X
        \<and> (\<forall>v\<in>X. \<exists>e\<in>Hs i. v \<in> e \<and> e \<inter> X = {v} \<and> e \<subseteq> {..<n} \<and> card e \<le> k)"
    proof
      fix X assume X: "X \<in> G i"
      have XM: "X \<in> M" and tX: "tr (Hs i) X"
        and cr: "\<forall>v\<in>X. \<exists>e\<in>Hs i. v \<in> e \<and> e \<inter> X = {v} \<and> e \<subseteq> {..<n} \<and> card e \<le> k"
        using X unfolding G_def by blast+
      have "X \<subseteq> {..<n}" "t \<le> card X" using mint XM by blast+
      moreover have "\<forall>e\<in>Hs i. e \<inter> X \<noteq> {}" using tX unfolding tr_def .
      ultimately show "X \<subseteq> {..<n} \<and> (\<forall>e\<in>Hs i. e \<inter> X \<noteq> {}) \<and> t \<le> card X
          \<and> (\<forall>v\<in>X. \<exists>e\<in>Hs i. v \<in> e \<and> e \<inter> X = {v} \<and> e \<subseteq> {..<n} \<and> card e \<le> k)"
        using cr by blast
    qed
    have "real (card (G i)) * (1 + 1 / real k) ^ t \<le> 2 ^ n" by (rule harris_ppz[OF prem])
    moreover have "0 < (1 + 1 / real k) ^ t" by (simp add: add_pos_nonneg)
    ultimately show ?thesis by (simp add: pos_le_divide_eq)
  qed
  have cS: "card (S e v) \<le> 2 ^ (n - card e)" if "i \<in> I" "e \<in> W i" "v \<in> e" for i e v
    unfolding S_def by (rule single_hit) (use edges that in \<open>auto simp: W_def\<close>)
  have "real (card M) \<le> (\<Sum>i\<in>I. real (card (G i))) + (\<Sum>i\<in>I. \<Sum>e\<in>W i. \<Sum>v\<in>e. real (card (S e v)))"
    using cM by (simp only: of_nat_le_iff of_nat_add of_nat_sum[symmetric])
  also have "\<dots> \<le> (\<Sum>i\<in>I. 2 ^ n / (1 + 1 / real k) ^ t)
      + (\<Sum>i\<in>I. \<Sum>e\<in>W i. \<Sum>v\<in>e. (2::real) ^ (n - card e))"
  proof (rule add_mono)
    show "(\<Sum>i\<in>I. real (card (G i))) \<le> (\<Sum>i\<in>I. 2 ^ n / (1 + 1 / real k) ^ t)"
      by (rule sum_mono) (rule cG)
    show "(\<Sum>i\<in>I. \<Sum>e\<in>W i. \<Sum>v\<in>e. real (card (S e v))) \<le> (\<Sum>i\<in>I. \<Sum>e\<in>W i. \<Sum>v\<in>e. (2::real) ^ (n - card e))"
    proof (rule sum_mono, rule sum_mono, rule sum_mono)
      fix i e v assume "i \<in> I" "e \<in> W i" "v \<in> e"
      then have "card (S e v) \<le> 2 ^ (n - card e)" by (rule cS)
      then show "real (card (S e v)) \<le> (2::real) ^ (n - card e)"
        by (metis of_nat_le_iff of_nat_numeral of_nat_power)
    qed
  qed
  also have "\<dots> = real (card I) * 2 ^ n / (1 + 1 / real k) ^ t
      + (\<Sum>i\<in>I. \<Sum>e\<in>W i. real (card e) * 2 ^ (n - card e))" by simp
  finally show ?thesis unfolding W_def .
qed

end
