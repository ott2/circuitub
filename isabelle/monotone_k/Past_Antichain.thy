theory Past_Antichain
  imports Witness_Antichain
begin

text \<open>Adaptive witness antichains. Reveal a minimal transversal part by part, each part
  chosen from what has been revealed so far. Within the family of transversals that agree on
  the revealed set \<open>S\<close>, the traces on the next part \<open>K\<close> form an antichain if every one in
  \<open>K\<close> has a critical edge inside \<open>S \<union> K\<close>. With at most \<open>d\<close> exceptions per
  transversal, comparable traces differ by at most \<open>d\<close> elements, and the residue classes of
  their sizes mod \<open>d+1\<close> are antichains (a weak form of Erd\H{o}s's theorem).\<close>

definition gapped :: "nat \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "gapped d A \<longleftrightarrow> (\<forall>S\<in>A. \<forall>T\<in>A. S \<subset> T \<longrightarrow> card T \<le> card S + d)"

lemma residue_antichain:
  assumes g: "gapped d A" and fin: "\<forall>T\<in>A. finite T"
  shows "antich {T\<in>A. card T mod Suc d = r}"
  unfolding antich_def
proof (intro ballI impI)
  fix S T assume S: "S \<in> {T\<in>A. card T mod Suc d = r}" and T: "T \<in> {T\<in>A. card T mod Suc d = r}"
    and ST: "S \<subseteq> T"
  show "S = T"
  proof (rule ccontr)
    assume "S \<noteq> T"
    then have psub: "S \<subset> T" using ST by blast
    have lt: "card S < card T" using psub fin T by (simp add: psubset_card_mono)
    have le: "card T \<le> card S + d" using g S T psub unfolding gapped_def by blast
    have "card T mod Suc d = card S mod Suc d" using S T by simp
    then have "(card T - card S) mod Suc d = 0" using lt by (simp add: mod_eq_dvd_iff_nat dvd_eq_mod_eq_0)
    moreover have "0 < card T - card S" "card T - card S < Suc d" using lt le by simp_all
    ultimately show False by simp
  qed
qed

theorem gapped_sperner:
  assumes g: "gapped d A" and finU: "finite U" and AU: "\<forall>T\<in>A. T \<subseteq> U"
  shows "card A \<le> Suc d * (card U choose (card U div 2))"
proof -
  have finT: "\<forall>T\<in>A. finite T" using AU finU finite_subset by blast
  have finA: "finite A" by (rule finite_subset[of _ "Pow U"]) (use AU finU in auto)
  have eq: "A = (\<Union>r\<in>{..<Suc d}. {T\<in>A. card T mod Suc d = r})" by auto
  have "card A \<le> (\<Sum>r\<in>{..<Suc d}. card {T\<in>A. card T mod Suc d = r})"
    by (subst eq) (rule card_UN_le, simp)
  also have "\<dots> \<le> (\<Sum>r\<in>{..<Suc d}. card U choose (card U div 2))"
    by (rule sum_mono) (rule sperner[OF residue_antichain[OF g finT] finU], use AU in auto)
  also have "\<dots> = Suc d * (card U choose (card U div 2))" by simp
  finally show ?thesis .
qed

definition loc :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "loc H S K X v \<longleftrightarrow> (\<exists>e\<in>H. e \<subseteq> S \<union> K \<and> e \<inter> X = {v})"

lemma past_local:
  assumes tr: "\<forall>e\<in>H. e \<inter> X \<noteq> {}" and agree: "X \<inter> S = X' \<inter> S"
    and sub: "X \<inter> K \<subseteq> X' \<inter> K" and v: "v \<in> X' \<inter> K" and l: "loc H S K X' v"
  shows "v \<in> X \<inter> K"
proof -
  obtain e where e: "e \<in> H" and eSK: "e \<subseteq> S \<union> K" and eX': "e \<inter> X' = {v}"
    using l unfolding loc_def by blast
  obtain u where u: "u \<in> e \<inter> X" using tr e by blast
  have "u \<in> X'" using u eSK agree sub by blast
  then have "u = v" using u eX' by blast
  then show ?thesis using u v by blast
qed

theorem past_antichain:
  assumes tr: "\<forall>X\<in>G. \<forall>e\<in>H. e \<inter> X \<noteq> {}" and agree: "\<forall>X\<in>G. \<forall>X'\<in>G. X \<inter> S = X' \<inter> S"
    and l: "\<forall>X\<in>G. \<forall>v\<in>X \<inter> K. loc H S K X v"
  shows "antich ((\<lambda>X. X \<inter> K) ` G)"
  unfolding antich_def
proof (intro ballI impI)
  fix A B assume A: "A \<in> (\<lambda>X. X \<inter> K) ` G" and B: "B \<in> (\<lambda>X. X \<inter> K) ` G" and AB: "A \<subseteq> B"
  obtain X where X: "X \<in> G" and AX: "A = X \<inter> K" using A by blast
  obtain X' where X': "X' \<in> G" and BX: "B = X' \<inter> K" using B by blast
  have trX: "\<forall>e\<in>H. e \<inter> X \<noteq> {}" using tr X by blast
  have ag: "X \<inter> S = X' \<inter> S" using agree X X' by blast
  have sub: "X \<inter> K \<subseteq> X' \<inter> K" using AB unfolding AX BX .
  have "v \<in> X \<inter> K" if v: "v \<in> X' \<inter> K" for v
    using past_local[OF trX ag sub v] l X' v by blast
  then have "B \<subseteq> A" unfolding AX BX by blast
  then show "A = B" using AB by blast
qed

theorem past_defect:
  assumes tr: "\<forall>X\<in>G. \<forall>e\<in>H. e \<inter> X \<noteq> {}" and agree: "\<forall>X\<in>G. \<forall>X'\<in>G. X \<inter> S = X' \<inter> S"
    and finK: "finite K"
    and few: "\<forall>X\<in>G. card {v\<in>X \<inter> K. \<not> loc H S K X v} \<le> d"
  shows "card ((\<lambda>X. X \<inter> K) ` G) \<le> Suc d * (card K choose (card K div 2))"
proof (rule gapped_sperner[OF _ finK])
  show "\<forall>T\<in>(\<lambda>X. X \<inter> K) ` G. T \<subseteq> K" by blast
  show "gapped d ((\<lambda>X. X \<inter> K) ` G)"
    unfolding gapped_def
  proof (intro ballI impI)
    fix A B assume A: "A \<in> (\<lambda>X. X \<inter> K) ` G" and B: "B \<in> (\<lambda>X. X \<inter> K) ` G" and AB: "A \<subset> B"
    obtain X where X: "X \<in> G" and AX: "A = X \<inter> K" using A by blast
    obtain X' where X': "X' \<in> G" and BX: "B = X' \<inter> K" using B by blast
    have trX: "\<forall>e\<in>H. e \<inter> X \<noteq> {}" using tr X by blast
    have ag: "X \<inter> S = X' \<inter> S" using agree X X' by blast
    have sub: "X \<inter> K \<subseteq> X' \<inter> K" using AB unfolding AX BX by blast
    have "v \<in> A" if v: "v \<in> X' \<inter> K" and lv: "loc H S K X' v" for v
      using past_local[OF trX ag sub v lv] AX by simp
    then have diff: "B - A \<subseteq> {v\<in>X' \<inter> K. \<not> loc H S K X' v}" unfolding BX by blast
    have finB: "finite B" using finK BX by simp
    have "card B = card A + card (B - A)"
      using AB finB by (metis card_Diff_subset card_mono finite_subset le_add_diff_inverse psubset_imp_subset)
    also have "card (B - A) \<le> d"
    proof -
      have "finite {v\<in>X' \<inter> K. \<not> loc H S K X' v}" using finK by simp
      then have "card (B - A) \<le> card {v\<in>X' \<inter> K. \<not> loc H S K X' v}" by (rule card_mono[OF _ diff])
      then show ?thesis using few X' by (meson order_trans)
    qed
    finally show "card B \<le> card A + d" by simp
  qed
qed

end
