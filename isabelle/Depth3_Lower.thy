theory Depth3_Lower
  imports Bounded_Width Monotone_Kraft Binomial_Estimates
begin

section \<open>The depth-3 lower bound for Majority, by the PPZ argument\<close>

text \<open>
  The paper's upper bound \<open>2\<^sup>O\<^sup>(\<^sup>\<surd>\<^sup>n\<^sup>)\<close> at depth 3 is optimal by Håstad's lower bound. At depth 3
  that lower bound has an elementary proof (Håstad, Jukna and Pudlák; Paturi, Pudlák and Zane):
  every CNF in a \<open>\<Sigma>\<^sub>3\<close> formula for Majority that accepts a point of the slice has, for every
  one of the point, a critical clause.  Narrow critical clauses make many coordinates forced
  in a random order (PPZ), and wide ones are critical for few points.

  Points are subsets of \<open>{..<n}\<close>; a CNF is a set of clauses, a clause a set of literals.
  Variables outside \<open>{..<n}\<close> are false.
\<close>

definition lv :: "nat set \<Rightarrow> nat lit \<Rightarrow> bool" where
  "lv X l \<longleftrightarrow> ((fst l \<in> X) = snd l)"

definition csat :: "nat lit set set \<Rightarrow> nat set \<Rightarrow> bool" where
  "csat G X \<longleftrightarrow> (\<forall>C\<in>G. \<exists>l\<in>C. lv X l)"

text \<open>
  Coordinate \<open>i\<close> is forced at \<open>X\<close> in the order \<open>p\<close> if some clause contains \<open>i\<close> with one sign
  only, and all its other literals are false at \<open>X\<close> and come earlier.\<close>

definition forced :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat lit set set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "forced n p G X i \<longleftrightarrow> (\<exists>C\<in>G. \<exists>b. (i, b) \<in> C \<and> (i, \<not> b) \<notin> C
      \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> (fst l < n \<longrightarrow> p (fst l) < p i) \<and> \<not> lv X l))"

lemma forced_agree:
  assumes X: "X \<subseteq> {..<n}" "csat G X" and Y: "Y \<subseteq> {..<n}" "csat G Y"
    and agree: "\<forall>v<n. p v < p i \<longrightarrow> (v \<in> X \<longleftrightarrow> v \<in> Y)" and f: "forced n p G X i"
  shows "forced n p G Y i \<and> (i \<in> X \<longleftrightarrow> i \<in> Y)"
proof -
  obtain C b where C: "C \<in> G" "(i, b) \<in> C" "(i, \<not> b) \<notin> C"
    and o: "\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> (fst l < n \<longrightarrow> p (fst l) < p i) \<and> \<not> lv X l"
    using f unfolding forced_def by blast
  have same: "lv Y l = lv X l" if "l \<in> C" "fst l \<noteq> i" for l
  proof (cases "fst l < n")
    case True
    then have "p (fst l) < p i" using o that by blast
    then have "fst l \<in> X \<longleftrightarrow> fst l \<in> Y" using agree True by blast
    then show ?thesis by (simp add: lv_def)
  next
    case False
    then have "fst l \<notin> X" "fst l \<notin> Y" using X(1) Y(1) by auto
    then show ?thesis by (simp add: lv_def)
  qed
  have oY: "\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> (fst l < n \<longrightarrow> p (fst l) < p i) \<and> \<not> lv Y l"
    using o same by blast
  have val: "(i \<in> Z) = b" if Z: "csat G Z" "\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv Z l" for Z
  proof -
    obtain l where l: "l \<in> C" "lv Z l" using Z(1) C(1) unfolding csat_def by blast
    then have li: "fst l = i" using Z(2) by blast
    have "snd l = b"
    proof (rule ccontr)
      assume "snd l \<noteq> b"
      then have "l = (i, \<not> b)" using li by (cases l) auto
      then show False using l(1) C(3) by simp
    qed
    then show ?thesis using l(2) li by (simp add: lv_def)
  qed
  have "(i \<in> X) = b" using val X(2) o by blast
  moreover have "(i \<in> Y) = b" using val Y(2) oY by blast
  moreover have "forced n p G Y i" unfolding forced_def using C oY by blast
  ultimately show ?thesis by simp
qed

text \<open>
  The cylinder of \<open>X\<close>: the points that agree with \<open>X\<close> on the coordinates not forced at \<open>X\<close>.
  It has \<open>2\<^sup>#\<^sup>f\<^sup>o\<^sup>r\<^sup>c\<^sup>e\<^sup>d\<close> elements.\<close>

definition cyl :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat lit set set \<Rightarrow> nat set \<Rightarrow> nat set set" where
  "cyl n p G X = {Z. Z \<subseteq> {..<n} \<and> (\<forall>i<n. \<not> forced n p G X i \<longrightarrow> (i \<in> Z \<longleftrightarrow> i \<in> X))}"

lemma card_cyl:
  assumes X: "X \<subseteq> {..<n}"
  shows "card (cyl n p G X) = 2 ^ card {i. i < n \<and> forced n p G X i}"
proof -
  define Fo where "Fo = {i. i < n \<and> forced n p G X i}"
  have finF: "finite Fo" by (simp add: Fo_def)
  have "bij_betw (\<lambda>Z. Z \<inter> Fo) (cyl n p G X) (Pow Fo)"
  proof (rule bij_betw_byWitness[where f' = "\<lambda>W. W \<union> (X - Fo)"])
    show "\<forall>Z\<in>cyl n p G X. Z \<inter> Fo \<union> (X - Fo) = Z"
    proof
      fix Z assume Z: "Z \<in> cyl n p G X"
      have "z \<in> X - Fo" if "z \<in> Z" "z \<notin> Fo" for z
        using Z that by (auto simp: cyl_def Fo_def)
      moreover have "z \<in> Z" if "z \<in> X - Fo" for z
        using Z that X by (auto simp: cyl_def Fo_def)
      ultimately show "Z \<inter> Fo \<union> (X - Fo) = Z" by blast
    qed
    show "\<forall>W\<in>Pow Fo. (W \<union> (X - Fo)) \<inter> Fo = W" by blast
    show "(\<lambda>Z. Z \<inter> Fo) ` cyl n p G X \<subseteq> Pow Fo" by blast
    show "(\<lambda>W. W \<union> (X - Fo)) ` Pow Fo \<subseteq> cyl n p G X"
      using X by (auto simp: cyl_def Fo_def)
  qed
  then have "card (cyl n p G X) = card (Pow Fo)" by (rule bij_betw_same_card)
  also have "\<dots> = 2 ^ card Fo" using finF by (rule card_Pow)
  finally show ?thesis by (simp add: Fo_def)
qed

text \<open>
  Cylinders of distinct satisfying points are disjoint: at the first coordinate where the
  points differ, a forced coordinate would agree, and an unforced one is fixed by the cylinder.
  This is the Kraft inequality of PPZ, without recording which coordinates are forced.\<close>

lemma cyl_disjoint:
  assumes X: "X \<subseteq> {..<n}" "csat G X" and Y: "Y \<subseteq> {..<n}" "csat G Y" and XY: "X \<noteq> Y"
  shows "cyl n p G X \<inter> cyl n p G Y = {}"
proof (rule ccontr)
  assume "cyl n p G X \<inter> cyl n p G Y \<noteq> {}"
  then obtain Z where ZX: "Z \<in> cyl n p G X" and ZY: "Z \<in> cyl n p G Y" by blast
  define D where "D = {v. v < n \<and> (v \<in> X) \<noteq> (v \<in> Y)}"
  have finD: "finite D" by (simp add: D_def)
  have D0: "D \<noteq> {}"
  proof
    assume "D = {}"
    then have "v \<in> X \<longleftrightarrow> v \<in> Y" for v using X(1) Y(1) by (auto simp: D_def)
    then show False using XY by blast
  qed
  have "Min (p ` D) \<in> p ` D" using finD D0 by (intro Min_in) simp_all
  then obtain i where iD: "i \<in> D" and im: "p i = Min (p ` D)" by (auto simp: image_iff)
  have agree: "\<forall>v<n. p v < p i \<longrightarrow> (v \<in> X \<longleftrightarrow> v \<in> Y)"
  proof (intro allI impI)
    fix v assume v: "v < n" "p v < p i"
    show "v \<in> X \<longleftrightarrow> v \<in> Y"
    proof (rule ccontr)
      assume "\<not> (v \<in> X \<longleftrightarrow> v \<in> Y)"
      then have "v \<in> D" using v by (auto simp: D_def)
      then have "Min (p ` D) \<le> p v" using finD by (intro Min_le) simp_all
      then have "p i \<le> p v" using im by simp
      then show False using v by simp
    qed
  qed
  have agree': "\<forall>v<n. p v < p i \<longrightarrow> (v \<in> Y \<longleftrightarrow> v \<in> X)" using agree by blast
  have iN: "i < n" and ne: "(i \<in> X) \<noteq> (i \<in> Y)" using iD by (auto simp: D_def)
  show False
  proof (cases "forced n p G X i")
    case True
    then show False using forced_agree[OF X Y agree] ne by blast
  next
    case nX: False
    show False
    proof (cases "forced n p G Y i")
      case True
      then show False using forced_agree[OF Y X agree'] ne by blast
    next
      case False
      then show False using nX ZX ZY iN ne by (auto simp: cyl_def)
    qed
  qed
qed

lemma forced_kraft:
  assumes A: "A \<subseteq> {X. X \<subseteq> {..<n} \<and> csat G X}"
  shows "(\<Sum>X\<in>A. (2::nat) ^ card {i. i < n \<and> forced n p G X i}) \<le> 2 ^ n"
proof -
  have "A \<subseteq> Pow {..<n}" using A by blast
  then have finA: "finite A" by (rule finite_subset) simp
  have cylP: "cyl n p G X \<subseteq> Pow {..<n}" for X by (auto simp: cyl_def)
  have "(\<Sum>X\<in>A. (2::nat) ^ card {i. i < n \<and> forced n p G X i}) = (\<Sum>X\<in>A. card (cyl n p G X))"
    using A by (intro sum.cong refl card_cyl[symmetric]) blast
  also have "\<dots> = card (\<Union>X\<in>A. cyl n p G X)"
  proof (rule card_UN_disjoint[symmetric])
    show "finite A" by (rule finA)
    show "\<forall>X\<in>A. finite (cyl n p G X)" using cylP by (blast intro: finite_subset)
    show "\<forall>X\<in>A. \<forall>Y\<in>A. X \<noteq> Y \<longrightarrow> cyl n p G X \<inter> cyl n p G Y = {}"
    proof (intro ballI impI)
      fix X Y assume "X \<in> A" "Y \<in> A" "X \<noteq> Y"
      then have "X \<subseteq> {..<n}" "csat G X" "Y \<subseteq> {..<n}" "csat G Y" using A by auto
      then show "cyl n p G X \<inter> cyl n p G Y = {}" using \<open>X \<noteq> Y\<close> by (rule cyl_disjoint)
    qed
  qed
  also have "\<dots> \<le> card (Pow {..<n})" using cylP by (intro card_mono) blast+
  also have "\<dots> = 2 ^ n" by (simp add: card_Pow)
  finally show ?thesis .
qed

end
