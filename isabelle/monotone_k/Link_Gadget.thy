theory Link_Gadget
  imports Shadow_Branch
begin

text \<open>
  Links of a hypergraph at a helper set \<open>Y\<close> (log \<section>6f). Fixing the helper part
  \<open>S = X \<inter> Y\<close> of a minimum transversal \<open>X\<close> leaves a minimum transversal \<open>X - Y\<close> of the link
  \<open>H\<^sub>S\<close>, a hypergraph of no larger rank on \<open>V - Y\<close>. So helpers multiply the count by at most
  \<open>2^|Y|\<close>: a gadget forcing "exactly half" on a group of size \<open>m\<close> is a \<open>\<Sigma>\<^sub>3\<^sup>k\<close> cover of the
  \<open>m\<close>-slice, with one CNF per helper configuration.
\<close>

definition mint :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "mint H V X \<longleftrightarrow> X \<subseteq> V \<and> tr H X \<and> (\<forall>X'. X' \<subseteq> V \<longrightarrow> tr H X' \<longrightarrow> card X \<le> card X')"

definition link :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "link H Y S = {e - Y | e. e \<in> H \<and> e \<inter> S = {}}"

lemma link_rank:
  assumes "\<forall>e\<in>H. finite e \<and> card e \<le> k" "f \<in> link H Y S"
  shows "card f \<le> k"
proof -
  obtain e where e: "e \<in> H" "f = e - Y" using assms(2) unfolding link_def by blast
  have "card (e - Y) \<le> card e" by (rule card_mono) (use assms(1) e(1) in auto)
  then show ?thesis using assms(1) e by fastforce
qed

lemma link_tr:
  assumes "tr H X"
  shows "tr (link H Y (X \<inter> Y)) (X - Y)"
proof -
  have "f \<inter> (X - Y) \<noteq> {}" if f: "f \<in> link H Y (X \<inter> Y)" for f
  proof -
    obtain e where e: "e \<in> H" "e \<inter> (X \<inter> Y) = {}" "f = e - Y" using f unfolding link_def by blast
    have "e \<inter> X \<noteq> {}" using assms e(1) unfolding tr_def by blast
    then show ?thesis using e(2,3) by blast
  qed
  then show ?thesis unfolding tr_def by blast
qed

lemma link_back:
  assumes "tr (link H Y S) T"
  shows "tr H (S \<union> T)"
proof -
  have False if e: "e \<in> H" "e \<inter> (S \<union> T) = {}" for e
  proof -
    have "e - Y \<in> link H Y S" using e unfolding link_def by blast
    then have "(e - Y) \<inter> T \<noteq> {}" using assms unfolding tr_def by blast
    then show False using e(2) by blast
  qed
  then show ?thesis unfolding tr_def by blast
qed

lemma link_mint:
  assumes fin: "finite V" and X: "mint H V X"
  shows "mint (link H Y (X \<inter> Y)) (V - Y) (X - Y)"
proof -
  have XV: "X \<subseteq> V" "tr H X" and min: "\<forall>X'. X' \<subseteq> V \<longrightarrow> tr H X' \<longrightarrow> card X \<le> card X'"
    using X unfolding mint_def by auto
  have fX: "finite X" using finite_subset[OF XV(1) fin] .
  have split: "card ((X - Y) \<union> (X \<inter> Y)) = card (X - Y) + card (X \<inter> Y)"
    by (rule card_Un_disjoint) (use fX in auto)
  have cX: "card X = card (X - Y) + card (X \<inter> Y)" using split by (simp only: Un_Diff_Int)
  have "card (X - Y) \<le> card T" if T: "T \<subseteq> V - Y" "tr (link H Y (X \<inter> Y)) T" for T
  proof -
    have "tr H ((X \<inter> Y) \<union> T)" by (rule link_back[OF T(2)])
    moreover have "(X \<inter> Y) \<union> T \<subseteq> V" using XV(1) T(1) by blast
    ultimately have "card X \<le> card ((X \<inter> Y) \<union> T)" using min by blast
    also have "\<dots> \<le> card (X \<inter> Y) + card T" by (rule card_Un_le)
    finally show ?thesis using cX by linarith
  qed
  moreover have "X - Y \<subseteq> V - Y" using XV(1) by blast
  moreover have "tr (link H Y (X \<inter> Y)) (X - Y)" by (rule link_tr[OF XV(2)])
  ultimately show ?thesis unfolding mint_def by blast
qed

theorem link_count:
  assumes fin: "finite V" and Y: "Y \<subseteq> V"
    and M: "\<And>S. S \<subseteq> Y \<Longrightarrow> card {T. mint (link H Y S) (V - Y) T \<and> card T = j} \<le> M"
  shows "card {X. mint H V X \<and> card (X - Y) = j} \<le> 2 ^ card Y * M"
proof -
  define A where "A = {X. mint H V X \<and> card (X - Y) = j}"
  define L where "L S = {T. mint (link H Y S) (V - Y) T \<and> card T = j}" for S
  define f where "f X = (X \<inter> Y, X - Y)" for X :: "'a set"
  have fY: "finite Y" using finite_subset[OF Y fin] .
  have inj: "inj_on f A"
  proof (rule inj_onI)
    fix X X' assume "f X = f X'"
    then have "X \<inter> Y = X' \<inter> Y" "X - Y = X' - Y" unfolding f_def by auto
    then show "X = X'" by blast
  qed
  have sub: "f ` A \<subseteq> Sigma (Pow Y) L"
  proof
    fix p assume "p \<in> f ` A"
    then obtain X where X: "mint H V X" "card (X - Y) = j" "p = f X" unfolding A_def by blast
    have "mint (link H Y (X \<inter> Y)) (V - Y) (X - Y)" by (rule link_mint[OF fin X(1)])
    then show "p \<in> Sigma (Pow Y) L" unfolding X(3) f_def L_def using X(2) by auto
  qed
  have finL: "finite (L S)" for S
    by (rule finite_subset[of _ "Pow (V - Y)"]) (use fin in \<open>auto simp: L_def mint_def\<close>)
  have "card A = card (f ` A)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card (Sigma (Pow Y) L)"
    by (rule card_mono[OF _ sub]) (use fY finL in \<open>simp add: finite_SigmaI\<close>)
  also have "\<dots> = (\<Sum>S\<in>Pow Y. card (L S))" by (rule card_SigmaI) (use fY finL in auto)
  also have "\<dots> \<le> (\<Sum>S\<in>Pow Y. M)" by (rule sum_mono) (use M in \<open>auto simp: L_def\<close>)
  also have "\<dots> = 2 ^ card Y * M" using fY by (simp add: card_Pow)
  finally show ?thesis unfolding A_def .
qed

end
