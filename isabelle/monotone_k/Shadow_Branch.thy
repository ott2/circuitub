theory Shadow_Branch
  imports Main
begin

section \<open>Shadows and branching: an elementary bound on minimum transversals\<close>

text \<open>
  Let \<open>H\<close> have edges of size \<open>\<le> k\<close> and no transversal of size \<open>< t\<close>.  Count pairs \<open>(X, Y)\<close>, with
  \<open>X\<close> a transversal of size \<open>t\<close> and \<open>Y \<subseteq> X\<close> of size \<open>t - j\<close>.  For fixed \<open>Y\<close>, the extensions \<open>X\<close>
  are \<open>Y \<union> J\<close> with \<open>J\<close> a minimal transversal of the edges missed by \<open>Y\<close>, and a rank-\<open>k\<close>
  hypergraph has at most \<open>k\<^sup>j\<close> minimal transversals of size \<open>j\<close> (branching).  Hence
  \<open>|X| (t choose j) \<le> (n choose t-j) k\<^sup>j\<close> (\<open>shadow_branch\<close>).  At \<open>n = 2t\<close> and \<open>j \<approx> t/(k-1)\<close> this is
  \<open>(n choose n/2) (1 - 1/k)\<^bsup>n/2\<^esup>\<close> up to a polynomial factor.\<close>

definition tr :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "tr H X \<longleftrightarrow> (\<forall>e\<in>H. e \<inter> X \<noteq> {})"

definition mtr :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "mtr H X \<longleftrightarrow> tr H X \<and> (\<forall>X'. X' \<subset> X \<longrightarrow> \<not> tr H X')"

text \<open>Minimal transversals of size \<open>|P| + j\<close> containing \<open>P\<close>.\<close>

definition ext :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "ext H V P j = {T. T \<subseteq> V \<and> P \<subseteq> T \<and> card T = card P + j \<and> mtr H T}"

lemma ext_finite: "finite V \<Longrightarrow> finite (ext H V P j)"
  by (rule finite_subset[of _ "Pow V"]) (auto simp: ext_def)

lemma minimal_branch:
  fixes H :: "'a set set" and k :: nat
  assumes V: "finite V" and P: "P \<subseteq> V" and E: "\<forall>e\<in>H. finite e \<and> card e \<le> k"
  shows "card (ext H V P j) \<le> k ^ j"
  using P
proof (induction j arbitrary: P)
  case 0
  have "ext H V P 0 \<subseteq> {P}"
  proof
    fix T assume T: "T \<in> ext H V P 0"
    then have "P \<subseteq> T" "card T = card P" "T \<subseteq> V" by (auto simp: ext_def)
    moreover have "finite T" using \<open>T \<subseteq> V\<close> V by (rule finite_subset)
    ultimately have "P = T" by (intro card_subset_eq) simp_all
    then show "T \<in> {P}" by simp
  qed
  then have "card (ext H V P 0) \<le> card {P}" by (rule card_mono[rotated]) simp
  then show ?case by simp
next
  case (Suc j)
  show ?case
  proof (cases "tr H P")
    case True
    have "ext H V P (Suc j) = {}"
    proof (rule equals0I)
      fix T assume T: "T \<in> ext H V P (Suc j)"
      then have PT: "P \<subseteq> T" and cT: "card T = card P + Suc j" and m: "mtr H T" by (auto simp: ext_def)
      have "P \<noteq> T" using cT by auto
      then have "P \<subset> T" using PT by blast
      then show False using m True by (simp add: mtr_def)
    qed
    then show ?thesis by simp
  next
    case False
    then obtain e where e: "e \<in> H" "e \<inter> P = {}" unfolding tr_def by blast
    have fe: "finite e" "card e \<le> k" using E e(1) by blast+
    have sub: "ext H V P (Suc j) \<subseteq> (\<Union>v\<in>e \<inter> V. ext H V (insert v P) j)"
    proof
      fix T assume T: "T \<in> ext H V P (Suc j)"
      then have TV: "T \<subseteq> V" and PT: "P \<subseteq> T" and cT: "card T = card P + Suc j" and m: "mtr H T"
        by (auto simp: ext_def)
      have "e \<inter> T \<noteq> {}" using m e(1) by (simp add: mtr_def tr_def)
      then obtain v where v: "v \<in> e" "v \<in> T" by blast
      have vP: "v \<notin> P" using v(1) e(2) by blast
      have fP: "finite P" using PT TV V by (meson finite_subset)
      have "card (insert v P) + j = card T" using cT vP fP by simp
      moreover have "insert v P \<subseteq> T" using PT v(2) by blast
      ultimately have "T \<in> ext H V (insert v P) j" using TV m by (simp add: ext_def)
      moreover have "v \<in> e \<inter> V" using v TV by blast
      ultimately show "T \<in> (\<Union>v\<in>e \<inter> V. ext H V (insert v P) j)" by blast
    qed
    have "card (ext H V P (Suc j)) \<le> card (\<Union>v\<in>e \<inter> V. ext H V (insert v P) j)"
    proof (rule card_mono[OF _ sub])
      show "finite (\<Union>v\<in>e \<inter> V. ext H V (insert v P) j)"
        using fe(1) ext_finite[OF V] by simp
    qed
    also have "\<dots> \<le> (\<Sum>v\<in>e \<inter> V. card (ext H V (insert v P) j))"
      by (rule card_UN_le) (use fe(1) in simp)
    also have "\<dots> \<le> (\<Sum>v\<in>e \<inter> V. k ^ j)"
    proof (rule sum_mono)
      fix v assume "v \<in> e \<inter> V"
      then have "insert v P \<subseteq> V" using Suc.prems by blast
      then show "card (ext H V (insert v P) j) \<le> k ^ j" by (rule Suc.IH)
    qed
    also have "\<dots> = card (e \<inter> V) * k ^ j" by simp
    also have "\<dots> \<le> k * k ^ j"
    proof (rule mult_right_mono)
      have "card (e \<inter> V) \<le> card e" by (rule card_mono[OF fe(1)]) blast
      then show "card (e \<inter> V) \<le> k" using fe(2) by linarith
    qed simp
    finally show ?thesis by simp
  qed
qed

lemma card_filter_sum:
  "finite A \<Longrightarrow> card {x\<in>A. P x} = (\<Sum>x\<in>A. if P x then 1 else (0::nat))"
  by (simp add: sum.inter_filter[symmetric])

theorem shadow_branch:
  fixes H :: "'a set set" and k t j :: nat
  assumes V: "finite V" and E: "\<forall>e\<in>H. finite e \<and> card e \<le> k"
    and thr: "\<forall>X. X \<subseteq> V \<longrightarrow> tr H X \<longrightarrow> t \<le> card X" and jt: "j \<le> t"
  shows "card {X. X \<subseteq> V \<and> card X = t \<and> tr H X} * (t choose j) \<le> (card V choose (t - j)) * k ^ j"
proof -
  define XS where "XS = {X. X \<subseteq> V \<and> card X = t \<and> tr H X}"
  define YS where "YS = {Y. Y \<subseteq> V \<and> card Y = t - j}"
  have fXS: "finite XS" unfolding XS_def by (rule finite_subset[of _ "Pow V"]) (use V in auto)
  have fYS: "finite YS" unfolding YS_def by (rule finite_subset[of _ "Pow V"]) (use V in auto)
  have cYS: "card YS = card V choose (t - j)" unfolding YS_def using n_subsets[OF V] by simp
  have left: "card {Y\<in>YS. Y \<subseteq> X} = t choose j" if X: "X \<in> XS" for X
  proof -
    have XV: "X \<subseteq> V" and cX: "card X = t" using X by (auto simp: XS_def)
    have fX: "finite X" using XV V by (rule finite_subset)
    have "{Y\<in>YS. Y \<subseteq> X} = {Y. Y \<subseteq> X \<and> card Y = t - j}" using XV by (auto simp: YS_def)
    then have "card {Y\<in>YS. Y \<subseteq> X} = t choose (t - j)" using n_subsets[OF fX] cX by simp
    also have "\<dots> = t choose j" using binomial_symmetric[OF jt] by simp
    finally show ?thesis .
  qed
  have right: "card {X\<in>XS. Y \<subseteq> X} \<le> k ^ j" if Y: "Y \<in> YS" for Y
  proof -
    have YV: "Y \<subseteq> V" and cY: "card Y = t - j" using Y by (auto simp: YS_def)
    have "{X\<in>XS. Y \<subseteq> X} \<subseteq> ext H V Y j"
    proof
      fix X assume "X \<in> {X\<in>XS. Y \<subseteq> X}"
      then have XV: "X \<subseteq> V" and cX: "card X = t" and tX: "tr H X" and YX: "Y \<subseteq> X"
        by (auto simp: XS_def)
      have fX: "finite X" using XV V by (rule finite_subset)
      have "\<not> tr H X'" if X': "X' \<subset> X" for X'
      proof
        assume tX': "tr H X'"
        have "X' \<subseteq> V" using X' XV by blast
        then have "t \<le> card X'" using thr tX' by blast
        moreover have "card X' < card X" by (rule psubset_card_mono[OF fX X'])
        ultimately show False using cX by simp
      qed
      then have "mtr H X" using tX by (simp add: mtr_def)
      moreover have "card X = card Y + j" using cX cY jt by simp
      ultimately show "X \<in> ext H V Y j" using XV YX by (simp add: ext_def)
    qed
    then have "card {X\<in>XS. Y \<subseteq> X} \<le> card (ext H V Y j)" by (rule card_mono[OF ext_finite[OF V]])
    also have "\<dots> \<le> k ^ j" by (rule minimal_branch[OF V YV E])
    finally show ?thesis .
  qed
  have "card XS * (t choose j) = (\<Sum>X\<in>XS. card {Y\<in>YS. Y \<subseteq> X})" using left by simp
  also have "\<dots> = (\<Sum>X\<in>XS. \<Sum>Y\<in>YS. if Y \<subseteq> X then 1 else 0)"
    using fYS by (simp add: card_filter_sum)
  also have "\<dots> = (\<Sum>Y\<in>YS. \<Sum>X\<in>XS. if Y \<subseteq> X then 1 else 0)" by (rule sum.swap)
  also have "\<dots> = (\<Sum>Y\<in>YS. card {X\<in>XS. Y \<subseteq> X})" using fXS by (simp add: card_filter_sum)
  also have "\<dots> \<le> (\<Sum>Y\<in>YS. k ^ j)" by (rule sum_mono) (rule right)
  also have "\<dots> = (card V choose (t - j)) * k ^ j" using cYS by simp
  finally show ?thesis unfolding XS_def .
qed

end
