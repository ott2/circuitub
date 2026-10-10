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

text \<open>
  PPZ for one CNF.  Suppose every one \<open>i\<close> of every point of \<open>A\<close> has a critical clause with at most
  \<open>r - 1\<close> other variables.  Under a uniformly random colouring with \<open>r\<close> colours, \<open>i\<close> is forced
  whenever those variables get smaller colours (\<open>good_colorings\<close>).  Averaging \<open>forced_kraft\<close>
  over the colourings, with Jensen (\<open>power_average\<close>), gives the bound.\<close>

lemma ppz_count:
  fixes r :: nat and G :: "nat lit set set"
  assumes A: "A \<subseteq> {X. X \<subseteq> {..<n} \<and> csat G X \<and> t \<le> card X}" and r: "1 \<le> r"
    and narrow: "\<forall>X\<in>A. \<forall>i\<in>X. \<exists>C\<in>G. (i, True) \<in> C \<and> (i, False) \<notin> C
        \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l) \<and> card {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)} \<le> r - 1"
  shows "real (card A) * 2 powr (real t * (r - 1) ^ (r - 1) / r ^ r) \<le> 2 ^ n"
proof -
  define Cs where "Cs = {..<n} \<rightarrow>\<^sub>E {..<r}"
  define q where "q = (r - 1) ^ (r - 1)"
  define P where "P = r ^ r"
  define y :: real where "y = real t * q / P"
  define D where "D c X = card {i. i < n \<and> forced n c G X i}" for c X
  have finCs: "finite Cs" by (simp add: Cs_def finite_PiE)
  have cCs: "card Cs = r ^ n" by (simp add: Cs_def card_PiE)
  have R0: "0 < card Cs" using cCs r by simp
  then have Cs0: "Cs \<noteq> {}" by auto
  have P0: "0 < P" using r by (simp add: P_def)
  have "A \<subseteq> Pow {..<n}" using A by blast
  then have finA: "finite A" by (rule finite_subset) simp
  have each: "real (card Cs) * 2 powr y \<le> (\<Sum>c\<in>Cs. (2::real) ^ D c X)" if X: "X \<in> A" for X
  proof -
    define F where "F c = {i. i < n \<and> \<not> forced n c G X i}" for c
    have XA: "X \<subseteq> {..<n}" "t \<le> card X" using A X by auto
    have good: "\<forall>l\<in>X. r ^ n * (r - 1) ^ (r - 1) \<le> r ^ r * card {c \<in> Cs. l \<notin> F c}"
    proof
      fix i assume i: "i \<in> X"
      obtain C where C: "C \<in> G" "(i, True) \<in> C" "(i, False) \<notin> C"
        and o: "\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l"
        and w: "card {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)} \<le> r - 1"
        using narrow X i by blast
      define E where "E = {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)}"
      have iN: "i < n" using i XA by blast
      have "r ^ n * (r - 1) ^ (r - 1) \<le> r ^ r * card {c \<in> Cs. \<forall>e\<in>E. c e < c i}"
        unfolding Cs_def using iN w r by (intro good_colorings) (auto simp: E_def)
      also have "\<dots> \<le> r ^ r * card {c \<in> Cs. i \<notin> F c}"
      proof (intro mult_left_mono card_mono)
        show "finite {c \<in> Cs. i \<notin> F c}" using finCs by simp
        show "{c \<in> Cs. \<forall>e\<in>E. c e < c i} \<subseteq> {c \<in> Cs. i \<notin> F c}"
        proof safe
          fix c assume c: "c \<in> Cs" "\<forall>e\<in>E. c e < c i" "i \<in> F c"
          have "forced n c G X i" unfolding forced_def
          proof (intro bexI[OF _ C(1)] exI[of _ True] conjI)
            show "(i, True) \<in> C" "(i, \<not> True) \<notin> C" using C by simp_all
            show "\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> (fst l < n \<longrightarrow> c (fst l) < c i) \<and> \<not> lv X l"
            proof (intro ballI impI conjI)
              fix l assume l: "l \<in> C" "fst l \<noteq> i"
              show "\<not> lv X l" using o l by blast
              assume "fst l < n"
              then have "fst l \<in> E" using l unfolding E_def by (cases l) auto
              then show "c (fst l) < c i" using c(2) by blast
            qed
          qed
          then show False using c(3) by (simp add: F_def)
        qed
      qed simp
      finally show "r ^ n * (r - 1) ^ (r - 1) \<le> r ^ r * card {c \<in> Cs. i \<notin> F c}" .
    qed
    have fs: "(\<Sum>c\<in>Cs. card (F c)) * r ^ r + t * (card Cs * (r - 1) ^ (r - 1))
                \<le> n * (card Cs * r ^ r)"
      by (rule free_sum[OF Cs_def r _ XA(1) XA(2) good]) (auto simp: F_def)
    have DF: "D c X + card (F c) = n" for c
    proof -
      have "{i. i < n \<and> forced n c G X i} \<union> F c = {..<n}" by (auto simp: F_def)
      moreover have "{i. i < n \<and> forced n c G X i} \<inter> F c = {}" by (auto simp: F_def)
      ultimately have "card {i. i < n \<and> forced n c G X i} + card (F c) = card {..<n}"
        by (metis card_Un_disjoint finite_Un finite_lessThan)
      then show ?thesis by (simp add: D_def)
    qed
    define SD where "SD = (\<Sum>c\<in>Cs. D c X)"
    define SF where "SF = (\<Sum>c\<in>Cs. card (F c))"
    have "SD + SF = (\<Sum>c\<in>Cs. D c X + card (F c))" by (simp add: SD_def SF_def sum.distrib)
    also have "\<dots> = n * card Cs" using DF by simp
    finally have e: "SD + SF = n * card Cs" .
    have "SD * P + SF * P = n * (card Cs * P)" using e by (metis add_mult_distrib mult.assoc)
    moreover have "SF * P + t * (card Cs * q) \<le> n * (card Cs * P)"
      using fs by (simp add: SF_def P_def q_def)
    ultimately have sd: "t * (card Cs * q) \<le> SD * P" by linarith
    have avg: "real (card Cs) * y \<le> (\<Sum>c\<in>Cs. real (D c X))"
    proof -
      have "real (card Cs) * y = real (t * (card Cs * q)) / real P"
        by (simp add: y_def algebra_simps)
      also have "\<dots> \<le> real (SD * P) / real P"
        using sd by (intro divide_right_mono) (simp only: of_nat_le_iff, simp)
      also have "\<dots> = real SD" using P0 by simp
      finally show ?thesis by (simp add: SD_def)
    qed
    show ?thesis using power_average[OF finCs Cs0 _ avg, of 2] by simp
  qed
  have "real (card A) * (real (card Cs) * 2 powr y) = (\<Sum>X\<in>A. real (card Cs) * 2 powr y)" by simp
  also have "\<dots> \<le> (\<Sum>X\<in>A. \<Sum>c\<in>Cs. (2::real) ^ D c X)" by (rule sum_mono) (rule each)
  also have "\<dots> = (\<Sum>c\<in>Cs. \<Sum>X\<in>A. (2::real) ^ D c X)" by (rule sum.swap)
  also have "\<dots> \<le> (\<Sum>c\<in>Cs. (2::real) ^ n)"
  proof (rule sum_mono)
    fix c
    have "(\<Sum>X\<in>A. (2::nat) ^ D c X) \<le> 2 ^ n" unfolding D_def using A by (intro forced_kraft) blast
    then have "real (\<Sum>X\<in>A. (2::nat) ^ D c X) \<le> real ((2::nat) ^ n)" by (simp only: of_nat_le_iff)
    then show "(\<Sum>X\<in>A. (2::real) ^ D c X) \<le> 2 ^ n" by simp
  qed
  also have "\<dots> = real (card Cs) * 2 ^ n" by simp
  finally have "real (card Cs) * (real (card A) * 2 powr y) \<le> real (card Cs) * 2 ^ n"
    by (simp add: algebra_simps)
  then show ?thesis using R0 by (simp add: y_def q_def P_def)
qed

text \<open>A clause with \<open>w\<close> other variables is critical for \<open>i\<close> at no more than \<open>2\<^sup>n\<^sup>-\<^sup>w\<^sup>-\<^sup>1\<close> points.\<close>

lemma crit_count:
  assumes i: "i < n"
  shows "card {X. X \<subseteq> {..<n} \<and> i \<in> X \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l)}
           \<le> 2 ^ (n - Suc (card {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)}))"
proof -
  define W where "W = {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)}"
  define S where "S = {X. X \<subseteq> {..<n} \<and> i \<in> X \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l)}"
  define R where "R = {..<n} - insert i W"
  have Wn: "insert i W \<subseteq> {..<n}" using i by (auto simp: W_def)
  have finW: "finite W" by (simp add: W_def)
  have iW: "i \<notin> W" by (simp add: W_def)
  have inj: "inj_on (\<lambda>X. X - insert i W) S"
  proof (rule inj_onI)
    fix X Y assume X: "X \<in> S" and Y: "Y \<in> S" and e: "X - insert i W = Y - insert i W"
    have "v \<in> X \<longleftrightarrow> v \<in> Y" if v: "v \<in> insert i W" for v
    proof (cases "v = i")
      case True
      then show ?thesis using X Y by (simp add: S_def)
    next
      case False
      then obtain b where b: "(v, b) \<in> C" using v by (auto simp: W_def)
      have "\<not> lv X (v, b)" "\<not> lv Y (v, b)" using X Y b False by (auto simp: S_def)
      then show ?thesis by (auto simp: lv_def)
    qed
    then show "X = Y" using e by blast
  qed
  have sub: "(\<lambda>X. X - insert i W) ` S \<subseteq> Pow R" by (auto simp: S_def R_def)
  have "card S \<le> card (Pow R)" using inj sub by (rule card_inj_on_le) (simp add: R_def)
  also have "\<dots> = 2 ^ card R" by (simp add: R_def card_Pow)
  also have "card R = n - Suc (card W)"
    using Wn finW iW by (simp add: R_def card_Diff_subset)
  finally show ?thesis by (simp add: S_def W_def)
qed

text \<open>
  An OR of CNFs that accepts the slice of weight \<open>t\<close> and rejects weight \<open>t - 1\<close>.  Each point of
  the slice is accepted by some CNF \<open>G\<close>, and each of its ones has a critical clause in \<open>G\<close>.
  Either all these can be chosen narrow (\<open>ppz_count\<close>), or some point is made critical by a
  wide clause (\<open>crit_count\<close>).\<close>

theorem sigma3_slice:
  fixes Gs :: "nat lit set set set" and r t :: nat
  assumes fin: "finite Gs" "\<forall>G\<in>Gs. finite G" and r: "1 \<le> r" and t: "1 \<le> t"
    and acc: "\<forall>X. X \<subseteq> {..<n} \<longrightarrow> card X = t \<longrightarrow> (\<exists>G\<in>Gs. csat G X)"
    and rej: "\<forall>G\<in>Gs. \<forall>X. X \<subseteq> {..<n} \<longrightarrow> card X + 1 = t \<longrightarrow> \<not> csat G X"
  shows "real (n choose t) \<le> real (card Gs) * 2 ^ n / 2 powr (real t * (r - 1) ^ (r - 1) / r ^ r)
           + real (card (\<Union>Gs)) * (n * 2 ^ (n - Suc r))"
proof -
  define y :: real where "y = real t * (r - 1) ^ (r - 1) / r ^ r"
  define W where "W C i = {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)}" for C :: "nat lit set" and i
  define crit where "crit X i C \<longleftrightarrow> (i, True) \<in> C \<and> (i, False) \<notin> C \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l)"
    for X i C
  define AG where "AG G = {X. X \<subseteq> {..<n} \<and> csat G X \<and> card X = t
                            \<and> (\<forall>i\<in>X. \<exists>C\<in>G. crit X i C \<and> card (W C i) \<le> r - 1)}" for G
  define Bd where "Bd C i = (if r \<le> card (W C i)
      then {X. X \<subseteq> {..<n} \<and> i \<in> X \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l)} else {})" for C i
  define Sl where "Sl = {X. X \<subseteq> {..<n} \<and> card X = t}"
  have finU: "finite (\<Union>Gs)" using fin by blast
  have cover: "Sl \<subseteq> (\<Union>G\<in>Gs. AG G) \<union> (\<Union>C\<in>\<Union>Gs. \<Union>i\<in>{..<n}. Bd C i)"
  proof
    fix X assume "X \<in> Sl"
    then have X: "X \<subseteq> {..<n}" "card X = t" by (auto simp: Sl_def)
    obtain G where G: "G \<in> Gs" "csat G X" using acc X by blast
    show "X \<in> (\<Union>G\<in>Gs. AG G) \<union> (\<Union>C\<in>\<Union>Gs. \<Union>i\<in>{..<n}. Bd C i)"
    proof (cases "\<forall>i\<in>X. \<exists>C\<in>G. crit X i C \<and> card (W C i) \<le> r - 1")
      case True
      then have "X \<in> AG G" using X G by (simp add: AG_def)
      then show ?thesis using G by blast
    next
      case False
      then obtain i where i: "i \<in> X" and nn: "\<forall>C\<in>G. crit X i C \<longrightarrow> \<not> card (W C i) \<le> r - 1"
        by blast
      have finX: "finite X" using X(1) by (rule finite_subset) simp
      have "card (X - {i}) + 1 = t" using X(2) i finX t by (simp add: card_Diff_singleton)
      then have "\<not> csat G (X - {i})" using rej G(1) X(1) by blast
      then obtain C where C: "C \<in> G" and Cf: "\<forall>l\<in>C. \<not> lv (X - {i}) l" by (auto simp: csat_def)
      have other: "\<not> lv X l" if "l \<in> C" "fst l \<noteq> i" for l
        using Cf that by (auto simp: lv_def)
      obtain l where l: "l \<in> C" "lv X l" using G(2) C by (auto simp: csat_def)
      then have li: "fst l = i" using other by blast
      then have "l = (i, True)" using l(2) i by (cases l) (simp add: lv_def)
      then have iT: "(i, True) \<in> C" using l(1) by simp
      have iF: "(i, False) \<notin> C" using Cf by (auto simp: lv_def)
      have cr: "crit X i C" using iT iF other by (simp add: crit_def)
      then have "r \<le> card (W C i)" using nn C r by fastforce
      then have "X \<in> Bd C i" using X(1) i other by (simp add: Bd_def)
      moreover have "i < n" using X(1) i by blast
      ultimately show ?thesis using C G(1) by blast
    qed
  qed
  have AGb: "real (card (AG G)) \<le> 2 ^ n / 2 powr y" for G
  proof -
    have "real (card (AG G)) * 2 powr y \<le> 2 ^ n" unfolding y_def
    proof (rule ppz_count[OF _ r])
      show "AG G \<subseteq> {X. X \<subseteq> {..<n} \<and> csat G X \<and> t \<le> card X}" by (auto simp: AG_def)
      show "\<forall>X\<in>AG G. \<forall>i\<in>X. \<exists>C\<in>G. (i, True) \<in> C \<and> (i, False) \<notin> C
          \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l) \<and> card {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)} \<le> r - 1"
        by (auto simp: AG_def crit_def W_def)
    qed
    then show ?thesis by (simp add: le_divide_eq)
  qed
  have Bdb: "card (Bd C i) \<le> 2 ^ (n - Suc r)" if "i < n" for C i
  proof (cases "r \<le> card (W C i)")
    case True
    then have "card (Bd C i) \<le> 2 ^ (n - Suc (card (W C i)))"
      using crit_count[OF that, of C] by (simp add: Bd_def W_def)
    also have "\<dots> \<le> 2 ^ (n - Suc r)" using True by (intro power_increasing) simp_all
    finally show ?thesis .
  qed (simp add: Bd_def)
  have finSl: "finite Sl" by (simp add: Sl_def)
  have "n choose t = card Sl" by (simp add: Sl_def n_subsets)
  also have "\<dots> \<le> card ((\<Union>G\<in>Gs. AG G) \<union> (\<Union>C\<in>\<Union>Gs. \<Union>i\<in>{..<n}. Bd C i))"
  proof (rule card_mono[OF _ cover])
    have "AG G \<subseteq> Pow {..<n}" for G by (auto simp: AG_def)
    moreover have "Bd C i \<subseteq> Pow {..<n}" for C i by (auto simp: Bd_def)
    ultimately have "(\<Union>G\<in>Gs. AG G) \<union> (\<Union>C\<in>\<Union>Gs. \<Union>i\<in>{..<n}. Bd C i) \<subseteq> Pow {..<n}" by blast
    then show "finite ((\<Union>G\<in>Gs. AG G) \<union> (\<Union>C\<in>\<Union>Gs. \<Union>i\<in>{..<n}. Bd C i))"
      by (rule finite_subset) simp
  qed
  also have "\<dots> \<le> card (\<Union>G\<in>Gs. AG G) + card (\<Union>C\<in>\<Union>Gs. \<Union>i\<in>{..<n}. Bd C i)"
    by (rule card_Un_le)
  also have "card (\<Union>G\<in>Gs. AG G) \<le> (\<Sum>G\<in>Gs. card (AG G))" by (rule card_UN_le[OF fin(1)])
  also have "card (\<Union>C\<in>\<Union>Gs. \<Union>i\<in>{..<n}. Bd C i) \<le> (\<Sum>C\<in>\<Union>Gs. card (\<Union>i\<in>{..<n}. Bd C i))"
    by (rule card_UN_le[OF finU])
  also have "\<dots> \<le> (\<Sum>C\<in>\<Union>Gs. n * 2 ^ (n - Suc r))"
  proof (rule sum_mono)
    fix C
    have "card (\<Union>i\<in>{..<n}. Bd C i) \<le> (\<Sum>i<n. card (Bd C i))" by (rule card_UN_le) simp
    also have "\<dots> \<le> (\<Sum>i<n. 2 ^ (n - Suc r))" by (rule sum_mono) (rule Bdb, simp)
    finally show "card (\<Union>i\<in>{..<n}. Bd C i) \<le> n * 2 ^ (n - Suc r)" by simp
  qed
  finally have nat: "n choose t \<le> (\<Sum>G\<in>Gs. card (AG G)) + card (\<Union>Gs) * (n * 2 ^ (n - Suc r))"
    by simp
  have "real (n choose t) \<le> (\<Sum>G\<in>Gs. real (card (AG G))) + real (card (\<Union>Gs)) * (n * 2 ^ (n - Suc r))"
  proof -
    have "real (n choose t) \<le> real ((\<Sum>G\<in>Gs. card (AG G)) + card (\<Union>Gs) * (n * 2 ^ (n - Suc r)))"
      using nat by (simp only: of_nat_le_iff)
    then show ?thesis by simp
  qed
  also have "(\<Sum>G\<in>Gs. real (card (AG G))) \<le> (\<Sum>G\<in>Gs. 2 ^ n / 2 powr y)"
    by (rule sum_mono) (rule AGb)
  also have "\<dots> = real (card Gs) * 2 ^ n / 2 powr y" by simp
  finally show ?thesis by (simp add: y_def)
qed

section \<open>Formulas\<close>

fun clause_of :: "nat form \<Rightarrow> nat lit set" where
  "clause_of (Or ls) = {(v, b). Lit v b \<in> set ls}"
| "clause_of _ = {}"

fun cnf_of :: "nat form \<Rightarrow> nat lit set set" where
  "cnf_of (And hs) = clause_of ` set hs"
| "cnf_of _ = {}"

lemma pi0_lit: "PI 0 g \<Longrightarrow> \<exists>v b. g = Lit v b"
  by (cases g) auto

lemma eval_clause:
  assumes "SIG (Suc 0) h"
  shows "eval (\<lambda>v. v \<in> X) h \<longleftrightarrow> (\<exists>l\<in>clause_of h. lv X l)"
proof -
  obtain ls where h: "h = Or ls" and ls: "\<forall>g\<in>set ls. PI 0 g" using assms sig_Suc_Or by blast
  have "eval (\<lambda>v. v \<in> X) h \<longleftrightarrow> (\<exists>g\<in>set ls. eval (\<lambda>v. v \<in> X) g)" by (simp add: h)
  also have "\<dots> \<longleftrightarrow> (\<exists>l\<in>clause_of h. lv X l)"
  proof
    assume "\<exists>g\<in>set ls. eval (\<lambda>v. v \<in> X) g"
    then obtain g where g: "g \<in> set ls" "eval (\<lambda>v. v \<in> X) g" by blast
    obtain v b where "g = Lit v b" using pi0_lit ls g(1) by blast
    then show "\<exists>l\<in>clause_of h. lv X l" using g by (auto simp: h lv_def)
  next
    assume "\<exists>l\<in>clause_of h. lv X l"
    then obtain v b where "Lit v b \<in> set ls" "(v \<in> X) = b" by (auto simp: h lv_def)
    then show "\<exists>g\<in>set ls. eval (\<lambda>v. v \<in> X) g" by force
  qed
  finally show ?thesis .
qed

lemma eval_cnf:
  assumes "PI (Suc (Suc 0)) g"
  shows "eval (\<lambda>v. v \<in> X) g \<longleftrightarrow> csat (cnf_of g) X"
proof -
  obtain hs where g: "g = And hs" and hs: "\<forall>h\<in>set hs. SIG (Suc 0) h" using assms pi_Suc_And by blast
  show ?thesis using hs eval_clause by (auto simp: g csat_def)
qed

lemma gates_pos: "PI (Suc d) g \<Longrightarrow> 1 \<le> gates g" "SIG (Suc d) g \<Longrightarrow> 1 \<le> gates g"
  by (cases g; simp)+

lemma card_cnf_of:
  assumes "PI (Suc (Suc 0)) g"
  shows "card (cnf_of g) \<le> gates g"
proof -
  obtain hs where g: "g = And hs" and hs: "\<forall>h\<in>set hs. SIG (Suc 0) h" using assms pi_Suc_And by blast
  have "card (cnf_of g) \<le> card (set hs)" by (simp add: g card_image_le)
  also have "\<dots> \<le> length hs" by (rule card_length)
  also have "\<dots> = (\<Sum>h\<leftarrow>hs. 1)" by (simp add: sum_list_triv)
  also have "\<dots> \<le> (\<Sum>h\<leftarrow>hs. gates h)" using hs gates_pos(2) by (intro sum_list_mono) blast
  also have "\<dots> \<le> gates g" by (simp add: g)
  finally show ?thesis .
qed

lemma sum_set_le_sum_list: "sum f (set xs) \<le> (\<Sum>x\<leftarrow>xs. (f x :: nat))"
proof (induction xs)
  case (Cons a xs)
  have "sum f (set (a # xs)) \<le> f a + sum f (set xs)"
    by (cases "a \<in> set xs") (simp_all add: insert_absorb)
  then show ?case using Cons by simp
qed simp

text \<open>A \<open>\<Sigma>\<^sub>3\<close> formula that accepts weight \<open>t\<close> and rejects weight \<open>t - 1\<close>, for any threshold \<open>t\<close>.\<close>

theorem sigma3_threshold:
  fixes f :: "nat form" and r t :: nat
  assumes f: "SIG 3 f" and t: "1 \<le> t" and r: "1 \<le> r"
    and acc: "\<forall>X. X \<subseteq> {..<n} \<longrightarrow> card X = t \<longrightarrow> eval (\<lambda>v. v \<in> X) f"
    and rej: "\<forall>X. X \<subseteq> {..<n} \<longrightarrow> card X + 1 = t \<longrightarrow> \<not> eval (\<lambda>v. v \<in> X) f"
  shows "real (n choose t) \<le> real (gates f)
           * (2 ^ n / 2 powr (real t * (r - 1) ^ (r - 1) / r ^ r) + real n * 2 ^ (n - Suc r))"
proof -
  have "SIG (Suc (Suc (Suc 0))) f" using f by (simp add: numeral_3_eq_3)
  then obtain gs where fg: "f = Or gs" and gs: "\<forall>g\<in>set gs. PI (Suc (Suc 0)) g"
    using sig_Suc_Or by blast
  define Gs where "Gs = cnf_of ` set gs"
  define y :: real where "y = real t * (r - 1) ^ (r - 1) / r ^ r"
  have evf: "eval (\<lambda>v. v \<in> X) f \<longleftrightarrow> (\<exists>G\<in>Gs. csat G X)" for X
    using gs eval_cnf by (auto simp: fg Gs_def)
  have finG: "\<forall>G\<in>Gs. finite G"
  proof
    fix G assume "G \<in> Gs"
    then obtain g where g: "g \<in> set gs" "G = cnf_of g" by (auto simp: Gs_def)
    then have "PI (Suc (Suc 0)) g" using gs by blast
    then obtain hs where "g = And hs" unfolding pi_Suc_And by blast
    then show "finite G" using g(2) by simp
  qed
  have rejG: "\<forall>G\<in>Gs. \<forall>X. X \<subseteq> {..<n} \<longrightarrow> card X + 1 = t \<longrightarrow> \<not> csat G X"
    using rej evf by blast
  have main: "real (n choose t) \<le> real (card Gs) * 2 ^ n / 2 powr y
                + real (card (\<Union>Gs)) * (n * 2 ^ (n - Suc r))"
    unfolding y_def using evf acc rejG finG r t by (intro sigma3_slice) (auto simp: Gs_def)
  have s1: "1 \<le> gates g" if "g \<in> set gs" for g using gs that gates_pos(1) by blast
  have sum: "(\<Sum>g\<leftarrow>gs. gates g) < gates f" by (simp add: fg)
  have cG: "card Gs \<le> gates f"
  proof -
    have "card Gs \<le> card (set gs)" by (simp add: Gs_def card_image_le)
    also have "\<dots> \<le> length gs" by (rule card_length)
    also have "\<dots> = (\<Sum>g\<leftarrow>gs. 1)" by (simp add: sum_list_triv)
    also have "\<dots> \<le> (\<Sum>g\<leftarrow>gs. gates g)" using s1 by (intro sum_list_mono) blast
    finally show ?thesis using sum by simp
  qed
  have cU: "card (\<Union>Gs) \<le> gates f"
  proof -
    have "card (\<Union>Gs) = card (\<Union>g\<in>set gs. cnf_of g)" by (simp add: Gs_def)
    also have "\<dots> \<le> (\<Sum>g\<in>set gs. card (cnf_of g))" by (rule card_UN_le) simp
    also have "\<dots> \<le> (\<Sum>g\<in>set gs. gates g)" using gs card_cnf_of by (intro sum_mono) blast
    also have "\<dots> \<le> (\<Sum>g\<leftarrow>gs. gates g)" by (rule sum_set_le_sum_list)
    finally show ?thesis using sum by simp
  qed
  have "real (card Gs) * 2 ^ n / 2 powr y \<le> real (gates f) * (2 ^ n / 2 powr y)"
  proof -
    have "real (card Gs) * (2 ^ n / 2 powr y) \<le> real (gates f) * (2 ^ n / 2 powr y)"
      using cG by (intro mult_right_mono) simp_all
    then show ?thesis by simp
  qed
  moreover have "real (card (\<Union>Gs)) * (n * 2 ^ (n - Suc r)) \<le> real (gates f) * (n * 2 ^ (n - Suc r))"
    using cU by (intro mult_right_mono) simp_all
  ultimately have "real (n choose t) \<le> real (gates f) * (2 ^ n / 2 powr y)
                     + real (gates f) * (n * 2 ^ (n - Suc r))" using main by linarith
  then show ?thesis by (simp add: y_def distrib_left)
qed

section \<open>Majority\<close>

text \<open>Complementing the variables below \<open>n\<close>.\<close>

fun cflip :: "nat \<Rightarrow> nat form \<Rightarrow> nat form" where
  "cflip n (Lit v b) = Lit v (if v < n then \<not> b else b)"
| "cflip n (And fs) = And (map (cflip n) fs)"
| "cflip n (Or fs) = Or (map (cflip n) fs)"

lemma eval_cflip: "eval \<sigma> (cflip n f) = eval (\<lambda>v. if v < n then \<not> \<sigma> v else \<sigma> v) f"
  by (induction f) auto

lemma gates_cflip: "gates (cflip n f) = gates f"
proof (induction f)
  case (And fs)
  then show ?case by (simp add: comp_def cong: map_cong)
next
  case (Or fs)
  then show ?case by (simp add: comp_def cong: map_cong)
qed simp

lemma sig_pi_cflip: "(SIG d f \<longrightarrow> SIG d (cflip n f)) \<and> (PI d f \<longrightarrow> PI d (cflip n f))"
proof (induction d arbitrary: f)
  case 0
  then show ?case by (cases f) auto
next
  case (Suc d)
  then show ?case by (cases f) auto
qed

lemma choose_mid: "1 \<le> n \<Longrightarrow> n choose (n div 2) \<le> 2 * (n choose (n div 2 + 1))"
proof -
  assume n: "1 \<le> n"
  define m where "m = n div 2"
  have e: "Suc m * (n choose Suc m) = (n - m) * (n choose m)"
    using binomial_absorption[of m n] binomial_absorb_comp[of n m] by simp
  have le: "Suc m \<le> 2 * (n - m)" using n unfolding m_def by presburger
  have "Suc m * (n choose m) \<le> 2 * (n - m) * (n choose m)" using le by (rule mult_right_mono) simp
  also have "\<dots> = Suc m * (2 * (n choose Suc m))" using e by (simp add: algebra_simps)
  finally have "Suc m * (n choose m) \<le> Suc m * (2 * (n choose Suc m))" .
  then have "n choose m \<le> 2 * (n choose Suc m)" by (simp only: Suc_mult_le_cancel1)
  then show ?thesis by (simp add: m_def)
qed

lemma majority_slices:
  fixes f :: "nat form" and r :: nat
  assumes f: "SIG 3 f \<or> PI 3 f" "\<forall>\<sigma>. eval \<sigma> f = majority n \<sigma>" and n: "1 \<le> n" and r: "1 \<le> r"
  shows "\<exists>t. n \<le> 2 * t \<and> real (n choose (n div 2)) \<le> 2 * real (n choose t)
           \<and> real (n choose t) \<le> real (gates f)
               * (2 ^ n / 2 powr (real t * (r - 1) ^ (r - 1) / r ^ r) + real n * 2 ^ (n - Suc r))"
proof (cases "SIG 3 f")
  case True
  define t where "t = (n + 1) div 2"
  have a1: "n \<le> 2 * t" and a2: "2 * t \<le> n + 1" and t1: "1 \<le> t" using n unfolding t_def by presburger+
  have bound: "real (n choose t) \<le> real (gates f)
               * (2 ^ n / 2 powr (real t * (r - 1) ^ (r - 1) / r ^ r) + real n * 2 ^ (n - Suc r))"
  proof (rule sigma3_threshold[OF True t1 r])
    show "\<forall>X. X \<subseteq> {..<n} \<longrightarrow> card X = t \<longrightarrow> eval (\<lambda>v. v \<in> X) f"
      using f(2) a1 by (auto simp: majority_def weight_set)
    show "\<forall>X. X \<subseteq> {..<n} \<longrightarrow> card X + 1 = t \<longrightarrow> \<not> eval (\<lambda>v. v \<in> X) f"
      using f(2) a2 by (auto simp: majority_def weight_set)
  qed
  have "n choose t = n choose (n div 2)"
  proof -
    have "n - n div 2 = t" unfolding t_def by presburger
    then show ?thesis using binomial_symmetric[of "n div 2" n] by simp
  qed
  then show ?thesis using a1 bound by (intro exI[of _ t]) simp
next
  case False
  then have pf: "PI 3 f" using f(1) by blast
  define t where "t = n div 2 + 1"
  define h where "h = cflip n (dual f)"
  have a1: "n < 2 * t" and a2: "2 * (n div 2) \<le> n" and t1: "1 \<le> t" unfolding t_def by presburger+
  have hS: "SIG 3 h" using sig_dual[OF pf] sig_pi_cflip by (simp add: h_def)
  have gh: "gates h = gates f" by (simp add: h_def gates_cflip)
  have ev: "eval (\<lambda>v. v \<in> X) h \<longleftrightarrow> n < 2 * card X" if X: "X \<subseteq> {..<n}" for X
  proof -
    have cX: "card X \<le> n" using X card_mono[of "{..<n}" X] by simp
    have "(\<lambda>v. if v < n then \<not> v \<in> X else v \<in> X) = (\<lambda>v. v \<in> {..<n} - X)" using X by auto
    then have "eval (\<lambda>v. v \<in> X) h \<longleftrightarrow> \<not> majority n (\<lambda>v. v \<in> {..<n} - X)"
      using f(2) by (simp add: h_def eval_cflip)
    also have "majority n (\<lambda>v. v \<in> {..<n} - X) \<longleftrightarrow> n \<le> 2 * (n - card X)"
    proof -
      have "weight n (\<lambda>v. v \<in> {..<n} - X) = card ({..<n} - X)" by (rule weight_set) blast
      also have "\<dots> = n - card X"
        using X by (subst card_Diff_subset) (auto intro: finite_subset)
      finally show ?thesis by (simp only: majority_def)
    qed
    finally show ?thesis using cX by linarith
  qed
  have bound: "real (n choose t) \<le> real (gates h)
               * (2 ^ n / 2 powr (real t * (r - 1) ^ (r - 1) / r ^ r) + real n * 2 ^ (n - Suc r))"
  proof (rule sigma3_threshold[OF hS t1 r])
    show "\<forall>X. X \<subseteq> {..<n} \<longrightarrow> card X = t \<longrightarrow> eval (\<lambda>v. v \<in> X) h" using ev a1 by simp
    show "\<forall>X. X \<subseteq> {..<n} \<longrightarrow> card X + 1 = t \<longrightarrow> \<not> eval (\<lambda>v. v \<in> X) h"
    proof (intro allI impI)
      fix X assume "X \<subseteq> {..<n}" "card X + 1 = t"
      then show "\<not> eval (\<lambda>v. v \<in> X) h" using ev a2 by (simp add: t_def)
    qed
  qed
  have "real (n choose (n div 2)) \<le> 2 * real (n choose t)"
  proof -
    have "n choose (n div 2) \<le> 2 * (n choose t)" unfolding t_def using n by (rule choose_mid)
    then have "real (n choose (n div 2)) \<le> real (2 * (n choose t))" by (simp only: of_nat_le_iff)
    then show ?thesis by simp
  qed
  then show ?thesis using a1 bound gh by (intro exI[of _ t]) simp
qed

text \<open>
  The depth-3 lower bound, explicitly: for every \<open>r \<ge> 1\<close>, a \<open>\<Sigma>\<^sub>3\<close> or \<open>\<Pi>\<^sub>3\<close> formula for
  Majority on \<open>n\<close> variables has size \<open>s\<close> with
  \<open>1 \<le> 2(n+1) s (2\<^sup>-\<^sup>y + n 2\<^sup>-\<^sup>r\<^sup>-\<^sup>1)\<close>, where \<open>y = n (r-1)\<^sup>r\<^sup>-\<^sup>1 / (2 r\<^sup>r) \<ge> n/(2er)\<close>.\<close>

theorem majority_depth3_lower:
  fixes f :: "nat form" and r :: nat
  assumes f: "SIG 3 f \<or> PI 3 f" "\<forall>\<sigma>. eval \<sigma> f = majority n \<sigma>" and n: "1 \<le> n" and r: "1 \<le> r"
  shows "2 ^ n \<le> 2 * real (n + 1) * real (gates f)
           * (2 ^ n / 2 powr (real n * (r - 1) ^ (r - 1) / (2 * r ^ r)) + real n * 2 ^ (n - Suc r))"
proof -
  obtain t where a: "n \<le> 2 * t" and b: "real (n choose (n div 2)) \<le> 2 * real (n choose t)"
    and c: "real (n choose t) \<le> real (gates f)
               * (2 ^ n / 2 powr (real t * (r - 1) ^ (r - 1) / r ^ r) + real n * 2 ^ (n - Suc r))"
    using majority_slices[OF f n r] by blast
  define Q :: real where "Q = (r - 1) ^ (r - 1)"
  define P :: real where "P = r ^ r"
  have Q0: "0 \<le> Q" and P0: "0 < P" using r by (simp_all add: Q_def P_def)
  have "real n * Q / (2 * P) \<le> real t * Q / P"
  proof -
    have "real n \<le> 2 * real t" using a by simp
    then have "real n * (Q / (2 * P)) \<le> 2 * real t * (Q / (2 * P))"
      using Q0 P0 by (intro mult_right_mono) simp_all
    then show ?thesis using P0 by (simp add: field_simps)
  qed
  then have "(2::real) ^ n / 2 powr (real t * Q / P) \<le> 2 ^ n / 2 powr (real n * Q / (2 * P))"
    by (intro divide_left_mono) simp_all
  then have c': "real (n choose t) \<le> real (gates f)
      * (2 ^ n / 2 powr (real n * Q / (2 * P)) + real n * 2 ^ (n - Suc r))"
    using c unfolding Q_def P_def by (smt (verit) mult_left_mono of_nat_0_le_iff)
  have "(2::real) ^ n \<le> real (n + 1) * real (n choose (n div 2))"
  proof -
    have "(2::nat) ^ n \<le> (n + 1) * (n choose (n div 2))" by (rule slice_lower)
    then have "real ((2::nat) ^ n) \<le> real ((n + 1) * (n choose (n div 2)))" by (simp only: of_nat_le_iff)
    then show ?thesis by (simp add: distrib_right)
  qed
  also have "\<dots> \<le> real (n + 1) * (2 * real (n choose t))" using b by (intro mult_left_mono) simp_all
  also have "\<dots> \<le> real (n + 1) * (2 * (real (gates f)
      * (2 ^ n / 2 powr (real n * Q / (2 * P)) + real n * 2 ^ (n - Suc r))))"
    using c' by (intro mult_left_mono) simp_all
  finally show ?thesis by (simp add: Q_def P_def algebra_simps)
qed

lemma exp_one_le_4: "exp (1::real) \<le> 4"
proof -
  have m: "1 / 2 \<le> exp (- (1 / 2 :: real))" using exp_ge_add_one_self[of "- (1 / 2 :: real)"] by simp
  have e: "exp (1 / 2 :: real) * exp (- (1 / 2)) = 1" by (rule exp_minus_inverse)
  have "exp (1 / 2 :: real) * (1 / 2) \<le> exp (1 / 2) * exp (- (1 / 2))"
    using m by (intro mult_left_mono) simp_all
  then have h: "exp (1 / 2 :: real) \<le> 2" using e by simp
  have "exp (1::real) = exp (1 / 2) * exp (1 / 2)" by (simp add: exp_add[symmetric])
  also have "\<dots> \<le> 2 * 2" using h by (intro mult_mono) simp_all
  finally show ?thesis by simp
qed

text \<open>
  In \<open>2\<^sup>\<Omega>\<^sup>(\<^sup>\<surd>\<^sup>n\<^sup>)\<close> form, with \<open>r = \<lceil>\<surd>n/4\<rceil>\<close>.  Together with \<open>majority_depth3\<close>, Majority has
  depth-3 complexity \<open>2\<^sup>\<Theta>\<^sup>(\<^sup>\<surd>\<^sup>n\<^sup>)\<close>.\<close>

corollary majority_depth3_sqrt:
  fixes f :: "nat form"
  assumes f: "SIG 3 f \<or> PI 3 f" "\<forall>\<sigma>. eval \<sigma> f = majority n \<sigma>" and n: "1 \<le> n"
  shows "2 powr (sqrt (real n) / 4) \<le> real (n + 1) * real (n + 2) * real (gates f)"
proof -
  have s1: "1 \<le> gates f"
    using f(1) gates_pos[of "Suc (Suc 0)" f] by (auto simp: numeral_3_eq_3)
  define x where "x = sqrt (real n)"
  have x0: "0 \<le> x" by (simp add: x_def)
  have xx: "x * x = real n" by (simp add: x_def)
  have A1: "6 \<le> real (n + 1) * real (n + 2) * real (gates f)"
  proof -
    have "2 * 3 * 1 \<le> (n + 1) * (n + 2) * gates f" using n s1 by (intro mult_mono) simp_all
    then have "real (2 * 3 * 1) \<le> real (n + 1) * real (n + 2) * real (gates f)"
      by (simp only: of_nat_le_iff of_nat_mult[symmetric])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (cases "n \<le> 16")
    case True
    have "x \<le> 4"
    proof (rule ccontr)
      assume "\<not> x \<le> 4"
      then have "4 * 4 < x * x" by (intro mult_strict_mono) simp_all
      then show False using xx True by simp
    qed
    then have "2 powr (x / 4) \<le> 2 powr 1" by (intro powr_mono) simp_all
    then show ?thesis using A1 by (simp add: x_def)
  next
    case False
    have x4: "4 \<le> x"
    proof (rule ccontr)
      assume "\<not> 4 \<le> x"
      then have "x * x \<le> 4 * 4" using x0 by (intro mult_mono) simp_all
      then show False using xx False by simp
    qed
    define r where "r = nat \<lceil>x / 4\<rceil>"
    have rlo: "x / 4 \<le> real r" by (simp add: r_def real_nat_ceiling_ge)
    have rhi: "real r \<le> x / 4 + 1"
    proof -
      have "0 \<le> \<lceil>x / 4\<rceil>" using x0 by simp
      then have "real r = of_int \<lceil>x / 4\<rceil>" by (simp add: r_def)
      also have "\<dots> \<le> x / 4 + 1" by (rule of_int_ceiling_le_add_one)
      finally show ?thesis .
    qed
    have r1: "1 \<le> r" using rlo x4 by simp
    have rn: "Suc r \<le> n"
    proof -
      have "4 * x \<le> x * x" using x4 x0 by (intro mult_right_mono) simp_all
      then have "real (Suc r) \<le> real n" using rhi xx False by simp
      then show ?thesis by (simp only: of_nat_le_iff)
    qed
    define Q :: real where "Q = (r - 1) ^ (r - 1)"
    define P :: real where "P = r ^ r"
    define y where "y = real n * Q / (2 * P)"
    define Z :: real where "Z = 2 powr (x / 4)"
    define K :: real where "K = 2 ^ n"
    define S where "S = real (gates f)"
    have Z0: "0 < Z" and K0: "0 < K" by (simp_all add: Z_def K_def)
    have main: "K \<le> 2 * real (n + 1) * S * (K / 2 powr y + real n * 2 ^ (n - Suc r))"
      using majority_depth3_lower[OF f n r1] by (simp add: K_def S_def y_def Q_def P_def)
    have qp: "1 / (exp 1 * real r) \<le> Q / P" using decoded_fraction[OF r1] by (simp add: Q_def P_def)
    have er: "exp 1 * real r \<le> 2 * x"
    proof -
      have "exp 1 * real r \<le> 4 * (x / 4 + 1)" using exp_one_le_4 rhi by (intro mult_mono) simp_all
      then show ?thesis using x4 by simp
    qed
    have er0: "0 < exp 1 * real r" using r1 by simp
    have xy: "x / 4 \<le> y"
    proof -
      have "x * (2 * (exp 1 * real r)) \<le> x * (2 * (2 * x))" using er x0 by (intro mult_left_mono) simp_all
      then have "x / 4 * (2 * (exp 1 * real r)) \<le> real n" using xx by simp
      then have "x / 4 \<le> real n / (2 * (exp 1 * real r))" using er0 by (simp add: le_divide_eq)
      also have "\<dots> = real n / 2 * (1 / (exp 1 * real r))" by simp
      also have "\<dots> \<le> real n / 2 * (Q / P)" using qp by (intro mult_left_mono) simp_all
      also have "\<dots> = y" by (simp add: y_def)
      finally show ?thesis .
    qed
    have h1: "K / 2 powr y \<le> K / Z"
      unfolding Z_def using xy K0 by (intro divide_left_mono powr_mono) simp_all
    have h2: "real n * 2 ^ (n - Suc r) \<le> real n * K / (2 * Z)"
    proof -
      have "Z \<le> 2 powr real r" unfolding Z_def using rlo by (intro powr_mono) simp_all
      also have "\<dots> = 2 ^ r" by (simp add: powr_realpow)
      finally have Zr: "2 * Z \<le> 2 ^ Suc r" by simp
      have ns: "n - Suc r + Suc r = n" using rn by simp
      have "(2::real) ^ (n - Suc r) * 2 ^ Suc r = 2 ^ (n - Suc r + Suc r)" by (simp only: power_add)
      then have "(2::real) ^ (n - Suc r) * 2 ^ Suc r = K" by (simp only: ns K_def)
      then have "(2::real) ^ (n - Suc r) = K / 2 ^ Suc r" by (simp add: eq_divide_eq)
      also have "\<dots> \<le> K / (2 * Z)" using Zr Z0 K0 by (intro divide_left_mono) simp_all
      finally have "real n * 2 ^ (n - Suc r) \<le> real n * (K / (2 * Z))"
        by (intro mult_left_mono) simp_all
      then show ?thesis by simp
    qed
    have S0: "0 \<le> S" by (simp add: S_def)
    have "K \<le> 2 * real (n + 1) * S * (K / Z + real n * K / (2 * Z))"
      using main h1 h2 S0 by (smt (verit) mult_left_mono of_nat_0_le_iff mult_nonneg_nonneg)
    also have "\<dots> = real (n + 1) * real (n + 2) * S * K / Z" using Z0 by (simp add: field_simps)
    finally have "K * Z \<le> real (n + 1) * real (n + 2) * S * K" using Z0 by (simp add: le_divide_eq)
    then have "Z * K \<le> (real (n + 1) * real (n + 2) * S) * K" by (simp add: algebra_simps)
    then have "Z \<le> real (n + 1) * real (n + 2) * S" using K0 by simp
    then show ?thesis by (simp add: Z_def S_def x_def)
  qed
qed

section \<open>ORs of narrow CNFs: Remark 1 of the paper is tight\<close>

text \<open>
  The paper's Remark 1 (\<open>majority_or_of_cnfs\<close>) writes Majority as an OR of \<open>2\<^sup>O\<^sup>(\<^sup>n\<^sup>/\<^sup>w\<^sup>)\<close> CNFs of
  width \<open>w\<close>, for every \<open>w \<le> 2\<surd>n\<close>.  By PPZ, at least \<open>2\<^sup>n\<^sup>/\<^sup>(\<^sup>2\<^sup>e\<^sup>w\<^sup>)\<^sup>/(n+1)\<close> are needed, for every \<open>w\<close>.
  So the number of width-\<open>w\<close> CNFs needed is \<open>2\<^sup>\<Theta>\<^sup>(\<^sup>n\<^sup>/\<^sup>w\<^sup>)\<close>.\<close>

lemma critical_clause:
  assumes X: "csat G X" and nX: "\<not> csat G (X - {i})" and i: "i \<in> X"
  shows "\<exists>C\<in>G. (i, True) \<in> C \<and> (i, False) \<notin> C \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l)"
proof -
  obtain C where C: "C \<in> G" and Cf: "\<forall>l\<in>C. \<not> lv (X - {i}) l" using nX by (auto simp: csat_def)
  have other: "\<not> lv X l" if "l \<in> C" "fst l \<noteq> i" for l
    using Cf that by (auto simp: lv_def)
  obtain l where l: "l \<in> C" "lv X l" using X C by (auto simp: csat_def)
  then have "fst l = i" using other by blast
  then have "l = (i, True)" using l(2) i by (cases l) (simp add: lv_def)
  then have iT: "(i, True) \<in> C" using l(1) by simp
  have iF: "(i, False) \<notin> C" using Cf by (auto simp: lv_def)
  show ?thesis using C iT iF other by blast
qed

lemma CNF_PI2: "CNF w f \<Longrightarrow> PI (Suc (Suc 0)) f"
  unfolding CNF_def by (force simp: pi_Suc_And sig_Suc_Or)

lemma clause_width:
  assumes ls: "length ls \<le> w" and i: "(i, True) \<in> clause_of (Or ls)"
  shows "card {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> clause_of (Or ls))} \<le> w - 1"
proof -
  define C where "C = clause_of (Or ls)"
  have Cv: "C = (\<lambda>(v, b). Lit v b) -` set ls" by (auto simp: C_def)
  have inj: "inj (\<lambda>(v, b). Lit v b :: nat form)" by (auto simp: inj_def)
  have finC: "finite C" unfolding Cv using inj by (intro finite_vimageI) simp_all
  have "card C \<le> card (set ls)"
  proof (rule card_inj_on_le)
    show "inj_on (\<lambda>(v, b). Lit v b) C" using inj by (rule inj_on_subset) simp
    show "(\<lambda>(v, b). Lit v b) ` C \<subseteq> set ls" by (auto simp: Cv)
  qed simp
  also have "\<dots> \<le> w" using ls card_length[of ls] by simp
  finally have cC: "card C \<le> w" .
  have iV: "i \<in> fst ` C" using i by (force simp: C_def)
  have "{v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)} \<subseteq> fst ` C - {i}" by force
  then have "card {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)} \<le> card (fst ` C - {i})"
    using finC by (intro card_mono) simp_all
  also have "\<dots> = card (fst ` C) - 1" using iV finC by simp
  also have "\<dots> \<le> card C - 1" using finC card_image_le[of C fst] by simp
  also have "\<dots> \<le> w - 1" using cC by simp
  finally show ?thesis by (simp add: C_def)
qed

theorem majority_cnfs_lower:
  fixes fs :: "nat form list" and w :: nat
  assumes cnf: "\<forall>f\<in>set fs. CNF w f" and maj: "\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma>"
    and n: "1 \<le> n" and w: "1 \<le> w"
  shows "2 powr (real n * (w - 1) ^ (w - 1) / (2 * w ^ w)) \<le> real (n + 1) * real (length fs)"
proof -
  define t where "t = (n + 1) div 2"
  define Q :: real where "Q = (w - 1) ^ (w - 1)"
  define P :: real where "P = w ^ w"
  define y where "y = real t * Q / P"
  define Sl where "Sl = {X. X \<subseteq> {..<n} \<and> card X = t}"
  define AG where "AG f = {X \<in> Sl. csat (cnf_of f) X}" for f
  have a1: "n \<le> 2 * t" and a2: "2 * t \<le> n + 1" and t1: "1 \<le> t" using n unfolding t_def by presburger+
  have Q0: "0 \<le> Q" and P0: "0 < P" using w by (simp_all add: Q_def P_def)
  have ev: "eval (\<lambda>v. v \<in> X) f \<longleftrightarrow> csat (cnf_of f) X" if "f \<in> set fs" for f X
    using eval_cnf CNF_PI2 cnf that by blast
  have acc: "\<exists>f\<in>set fs. csat (cnf_of f) X" if "X \<in> Sl" for X
  proof -
    have "majority n (\<lambda>v. v \<in> X)" using that a1 by (auto simp: Sl_def majority_def weight_set)
    then show ?thesis using maj ev by blast
  qed
  have rej: "\<not> csat (cnf_of f) X" if "f \<in> set fs" "X \<subseteq> {..<n}" "card X + 1 = t" for f X
  proof -
    have "\<not> majority n (\<lambda>v. v \<in> X)" using that a2 by (auto simp: majority_def weight_set)
    then show ?thesis using maj ev that(1) by blast
  qed
  have AGb: "real (card (AG f)) * 2 powr y \<le> 2 ^ n" if f: "f \<in> set fs" for f
    unfolding y_def Q_def P_def
  proof (rule ppz_count[OF _ w])
    show "AG f \<subseteq> {X. X \<subseteq> {..<n} \<and> csat (cnf_of f) X \<and> t \<le> card X}"
      by (auto simp: AG_def Sl_def)
    obtain cs where fcs: "f = And cs"
      and cs: "\<forall>c\<in>set cs. \<exists>ls. c = Or ls \<and> length ls \<le> w \<and> (\<forall>l\<in>set ls. \<exists>v b. l = Lit v b)"
      using cnf f by (auto simp: CNF_def)
    show "\<forall>X\<in>AG f. \<forall>i\<in>X. \<exists>C\<in>cnf_of f. (i, True) \<in> C \<and> (i, False) \<notin> C
        \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l) \<and> card {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)} \<le> w - 1"
    proof (intro ballI)
      fix X i assume X: "X \<in> AG f" and i: "i \<in> X"
      have XS: "X \<subseteq> {..<n}" "card X = t" "csat (cnf_of f) X" using X by (auto simp: AG_def Sl_def)
      have finX: "finite X" using XS(1) by (rule finite_subset) simp
      have "card (X - {i}) + 1 = t" using XS(2) i finX t1 by (simp add: card_Diff_singleton)
      then have "\<not> csat (cnf_of f) (X - {i})" using rej f XS(1) by blast
      then obtain C where C: "C \<in> cnf_of f" "(i, True) \<in> C" "(i, False) \<notin> C"
        and o: "\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l"
        using critical_clause[OF XS(3) _ i] by blast
      obtain c where c: "c \<in> set cs" "C = clause_of c" using C(1) by (auto simp: fcs)
      obtain ls where ls: "c = Or ls" "length ls \<le> w" using cs c(1) by blast
      have "card {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)} \<le> w - 1"
        using clause_width[OF ls(2), of i n] C(2) by (simp add: c(2) ls(1))
      then show "\<exists>C\<in>cnf_of f. (i, True) \<in> C \<and> (i, False) \<notin> C
          \<and> (\<forall>l\<in>C. fst l \<noteq> i \<longrightarrow> \<not> lv X l) \<and> card {v. v < n \<and> v \<noteq> i \<and> (\<exists>b. (v, b) \<in> C)} \<le> w - 1"
        using C o by blast
    qed
  qed
  have cover: "Sl \<subseteq> (\<Union>f\<in>set fs. AG f)" using acc by (auto simp: AG_def)
  have "n choose (n div 2) = n choose t"
  proof -
    have "n - n div 2 = t" unfolding t_def by presburger
    then show ?thesis using binomial_symmetric[of "n div 2" n] by simp
  qed
  also have "\<dots> = card Sl" by (simp add: Sl_def n_subsets)
  also have "\<dots> \<le> card (\<Union>f\<in>set fs. AG f)"
  proof (rule card_mono[OF _ cover])
    have "(\<Union>f\<in>set fs. AG f) \<subseteq> Pow {..<n}" by (auto simp: AG_def Sl_def)
    then show "finite (\<Union>f\<in>set fs. AG f)" by (rule finite_subset) simp
  qed
  also have "\<dots> \<le> (\<Sum>f\<in>set fs. card (AG f))" by (rule card_UN_le) simp
  finally have nat: "n choose (n div 2) \<le> (\<Sum>f\<in>set fs. card (AG f))" .
  have "(2::real) ^ n \<le> real (n + 1) * real (n choose (n div 2))"
  proof -
    have "(2::nat) ^ n \<le> (n + 1) * (n choose (n div 2))" by (rule slice_lower)
    then have "real ((2::nat) ^ n) \<le> real ((n + 1) * (n choose (n div 2)))" by (simp only: of_nat_le_iff)
    then show ?thesis by (simp only: of_nat_mult of_nat_power) simp
  qed
  also have "\<dots> \<le> real (n + 1) * (\<Sum>f\<in>set fs. real (card (AG f)))"
  proof -
    have "real (n choose (n div 2)) \<le> real (\<Sum>f\<in>set fs. card (AG f))" using nat by (simp only: of_nat_le_iff)
    then show ?thesis by (intro mult_left_mono) simp_all
  qed
  also have "\<dots> \<le> real (n + 1) * (\<Sum>f\<in>set fs. 2 ^ n / 2 powr y)"
    using AGb by (intro mult_left_mono sum_mono) (simp_all add: le_divide_eq)
  also have "\<dots> = real (n + 1) * (real (card (set fs)) * 2 ^ n / 2 powr y)" by simp
  also have "\<dots> \<le> real (n + 1) * (real (length fs) * 2 ^ n / 2 powr y)"
    using card_length[of fs] by (intro mult_left_mono divide_right_mono mult_right_mono) simp_all
  finally have "(2::real) ^ n \<le> real (n + 1) * real (length fs) * 2 ^ n / 2 powr y" by simp
  then have "2 ^ n * 2 powr y \<le> real (n + 1) * real (length fs) * 2 ^ n" by (simp add: le_divide_eq)
  then have Y: "2 powr y \<le> real (n + 1) * real (length fs)" by (simp add: mult.commute)
  have "real n * Q / (2 * P) \<le> y"
  proof -
    have "real n \<le> 2 * real t" using a1 by simp
    then have "real n * (Q / (2 * P)) \<le> 2 * real t * (Q / (2 * P))"
      using Q0 P0 by (intro mult_right_mono) simp_all
    then show ?thesis using P0 by (simp add: y_def field_simps)
  qed
  then have "2 powr (real n * Q / (2 * P)) \<le> 2 powr y" by (intro powr_mono) simp_all
  then have "2 powr (real n * Q / (2 * P)) \<le> real (n + 1) * real (length fs)" using Y by (rule order.trans)
  then show ?thesis by (simp add: Q_def P_def)
qed

corollary majority_cnfs_lower_e:
  fixes fs :: "nat form list" and w :: nat
  assumes "\<forall>f\<in>set fs. CNF w f" "\<forall>\<sigma>. (\<exists>f\<in>set fs. eval \<sigma> f) \<longleftrightarrow> majority n \<sigma>"
    and "1 \<le> n" and w: "1 \<le> w"
  shows "2 powr (real n / (2 * exp 1 * real w)) \<le> real (n + 1) * real (length fs)"
proof -
  have fr: "1 / (exp 1 * real w) \<le> real ((w - 1) ^ (w - 1)) / real (w ^ w)" by (rule decoded_fraction[OF w])
  have "real n / (2 * exp 1 * real w) = real n / 2 * (1 / (exp 1 * real w))" by simp
  also have "\<dots> \<le> real n / 2 * (real ((w - 1) ^ (w - 1)) / real (w ^ w))"
    using fr by (intro mult_left_mono) simp_all
  also have "\<dots> = real n * (w - 1) ^ (w - 1) / (2 * w ^ w)" by simp
  finally have "2 powr (real n / (2 * exp 1 * real w)) \<le> 2 powr (real n * (w - 1) ^ (w - 1) / (2 * w ^ w))"
    by simp
  also have "\<dots> \<le> real (n + 1) * real (length fs)" using majority_cnfs_lower assms by blast
  finally show ?thesis .
qed

end
