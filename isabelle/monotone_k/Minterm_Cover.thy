theory Minterm_Cover
  imports Witness_Antichain Shadow_Branch
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

end
