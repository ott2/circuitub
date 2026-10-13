theory Harris_PPZ
  imports Cluster_PPZ
begin

section \<open>PPZ for monotone CNFs via the Harris inequality\<close>

text \<open>
  In a monotone CNF, a one \<open>v\<close> of a transversal \<open>X\<close> is forced by a critical edge once all of the
  edge's other vertices, which are zeros, come earlier.  Each such event increases with the
  ones' colours and decreases with the zeros' colours.  So all of them are monotone in the same
  direction for the product order that reverses the coordinates in \<open>X\<close>, and by the Harris
  inequality they are positively correlated, however their zero sets overlap.  This replaces
  PPZ's Jensen step \<open>E 2\<^sup>F \<ge> 2\<^bsup>E F\<^esup>\<close> by \<open>E 2\<^sup>F \<ge> \<Prod>\<^sub>v (1 + P(v forced))\<close>:

  \<^item> \<open>harris_count\<close>: groups of ones need disjoint sets of ones only; their zero sets may overlap
    (in \<open>cluster_count\<close> the clusters had to be vertex-disjoint);
  \<^item> \<open>harris_ppz\<close>: transversals of size \<open>\<ge> t\<close> whose ones all have critical edges of size \<open>\<le> k\<close>
    number at most \<open>2\<^sup>n / (1 + 1/k)\<^sup>t\<close>.  PPZ gives \<open>2\<^sup>n / 2\<^bsup>t/k\<^esup>\<close>.\<close>

subsection \<open>Sums over colourings, one coordinate at a time\<close>

lemma sum_PiE_insert:
  fixes h :: "(nat \<Rightarrow> nat) \<Rightarrow> real"
  assumes i: "i \<notin> J"
  shows "(\<Sum>c\<in>insert i J \<rightarrow>\<^sub>E {..<r}. h c) = (\<Sum>y<r. \<Sum>b\<in>J \<rightarrow>\<^sub>E {..<r}. h (b(i := y)))"
proof -
  have inj: "inj_on (\<lambda>(y, g). g(i := y)) ({..<r} \<times> (J \<rightarrow>\<^sub>E {..<r}))"
    using inj_combinator[OF i, where T = "\<lambda>_. {..<r}"] by simp
  have "(\<Sum>c\<in>insert i J \<rightarrow>\<^sub>E {..<r}. h c) = (\<Sum>(y, b)\<in>{..<r} \<times> (J \<rightarrow>\<^sub>E {..<r}). h (b(i := y)))"
  proof (rule sum.reindex_cong[OF inj])
    show "insert i J \<rightarrow>\<^sub>E {..<r} = (\<lambda>(y, g). g(i := y)) ` ({..<r} \<times> (J \<rightarrow>\<^sub>E {..<r}))"
      using PiE_insert_eq[where x = i and S = J and T = "\<lambda>_. {..<r}"] by simp
  next
    fix p assume "p \<in> {..<r} \<times> (J \<rightarrow>\<^sub>E {..<r})"
    show "h ((\<lambda>(y, g). g(i := y)) p) = (case p of (y, b) \<Rightarrow> h (b(i := y)))" by (cases p) simp
  qed
  also have "\<dots> = (\<Sum>y<r. \<Sum>b\<in>J \<rightarrow>\<^sub>E {..<r}. h (b(i := y)))" by (rule sum.cartesian_product[symmetric])
  finally show ?thesis .
qed

subsection \<open>The Harris inequality on a product of chains\<close>

text \<open>\<open>sdec I P r f\<close>: \<open>f\<close> decreases when the coordinates in \<open>I - P\<close> go up and those in \<open>P\<close> go
  down.\<close>

definition sdec :: "nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> ((nat \<Rightarrow> nat) \<Rightarrow> real) \<Rightarrow> bool" where
  "sdec I P r f \<longleftrightarrow> (\<forall>a\<in>I \<rightarrow>\<^sub>E {..<r}. \<forall>b\<in>I \<rightarrow>\<^sub>E {..<r}.
      (\<forall>i\<in>I. if i \<in> P then b i \<le> a i else a i \<le> b i) \<longrightarrow> f b \<le> f a)"

lemma sdecD:
  assumes "sdec I P r f" "a \<in> I \<rightarrow>\<^sub>E {..<r}" "b \<in> I \<rightarrow>\<^sub>E {..<r}"
    and "\<forall>i\<in>I. if i \<in> P then b i \<le> a i else a i \<le> b i"
  shows "f b \<le> f a"
  using assms unfolding sdec_def by blast

lemma upd_PiE:
  assumes "b \<in> J \<rightarrow>\<^sub>E {..<r}" "y < r"
  shows "b(i := y) \<in> insert i J \<rightarrow>\<^sub>E {..<r}"
  using assms by (auto simp: PiE_iff extensional_def)

lemma sdec_upd:
  assumes f: "sdec (insert i J) P r f" and i: "i \<notin> J" and y: "y < r"
  shows "sdec J P r (\<lambda>b. f (b(i := y)))"
  unfolding sdec_def
proof (intro ballI impI)
  fix a b assume a: "a \<in> J \<rightarrow>\<^sub>E {..<r}" and b: "b \<in> J \<rightarrow>\<^sub>E {..<r}"
    and ab: "\<forall>j\<in>J. if j \<in> P then b j \<le> a j else a j \<le> b j"
  have "\<forall>j\<in>insert i J. if j \<in> P then (b(i := y)) j \<le> (a(i := y)) j else (a(i := y)) j \<le> (b(i := y)) j"
  proof
    fix j assume j: "j \<in> insert i J"
    show "if j \<in> P then (b(i := y)) j \<le> (a(i := y)) j else (a(i := y)) j \<le> (b(i := y)) j"
    proof (cases "j = i")
      case True
      then show ?thesis by simp
    next
      case False
      then have "j \<in> J" using j by blast
      then show ?thesis using ab False by simp
    qed
  qed
  then show "f (b(i := y)) \<le> f (a(i := y))" by (rule sdecD[OF f upd_PiE[OF a y] upd_PiE[OF b y]])
qed

lemma sdec_step:
  assumes f: "sdec (insert i J) P r f" and i: "i \<notin> J" and b: "b \<in> J \<rightarrow>\<^sub>E {..<r}"
    and yy: "y \<le> y'" "y' < r"
  shows "if i \<in> P then f (b(i := y)) \<le> f (b(i := y')) else f (b(i := y')) \<le> f (b(i := y))"
proof -
  have y: "y < r" using yy by simp
  have eq: "(b(i := y)) j = (b(i := y')) j" if "j \<in> J" for j using that i by auto
  show ?thesis
  proof (cases "i \<in> P")
    case True
    have "\<forall>j\<in>insert i J. if j \<in> P then (b(i := y)) j \<le> (b(i := y')) j else (b(i := y')) j \<le> (b(i := y)) j"
      using True yy eq by auto
    then have "f (b(i := y)) \<le> f (b(i := y'))" by (rule sdecD[OF f upd_PiE[OF b yy(2)] upd_PiE[OF b y]])
    then show ?thesis using True by simp
  next
    case False
    have "\<forall>j\<in>insert i J. if j \<in> P then (b(i := y')) j \<le> (b(i := y)) j else (b(i := y)) j \<le> (b(i := y')) j"
      using False yy eq by auto
    then have "f (b(i := y')) \<le> f (b(i := y))" by (rule sdecD[OF f upd_PiE[OF b y] upd_PiE[OF b yy(2)]])
    then show ?thesis using False by simp
  qed
qed

text \<open>Chebyshev's sum inequality for two sequences monotone in the same direction.\<close>

lemma cheb_same:
  fixes F G :: "nat \<Rightarrow> real"
  assumes "(\<forall>y y'. y \<le> y' \<longrightarrow> y' < r \<longrightarrow> F y' \<le> F y \<and> G y' \<le> G y)
         \<or> (\<forall>y y'. y \<le> y' \<longrightarrow> y' < r \<longrightarrow> F y \<le> F y' \<and> G y \<le> G y')"
  shows "(\<Sum>y<r. F y) * (\<Sum>y<r. G y) \<le> real r * (\<Sum>y<r. F y * G y)"
  using assms
proof
  assume d: "\<forall>y y'. y \<le> y' \<longrightarrow> y' < r \<longrightarrow> F y' \<le> F y \<and> G y' \<le> G y"
  have "of_nat r * (\<Sum>k=0..<r. (- F k) * G k) \<le> (\<Sum>k=0..<r. - F k) * (\<Sum>k=0..<r. G k)"
  proof (rule Chebyshev_sum_upper)
    fix i j assume "i \<le> j" "j < r"
    then show "- F i \<le> - F j" "G j \<le> G i" using d by auto
  qed
  then show ?thesis by (simp add: atLeast0LessThan sum_negf)
next
  assume u: "\<forall>y y'. y \<le> y' \<longrightarrow> y' < r \<longrightarrow> F y \<le> F y' \<and> G y \<le> G y'"
  have "of_nat r * (\<Sum>k=0..<r. F k * (- G k)) \<le> (\<Sum>k=0..<r. F k) * (\<Sum>k=0..<r. - G k)"
  proof (rule Chebyshev_sum_upper)
    fix i j assume "i \<le> j" "j < r"
    then show "F i \<le> F j" "- G j \<le> - G i" using u by auto
  qed
  then show ?thesis by (simp add: atLeast0LessThan sum_negf)
qed

theorem harris:
  fixes f g :: "(nat \<Rightarrow> nat) \<Rightarrow> real"
  assumes I: "finite I" and f: "sdec I P r f" and g: "sdec I P r g"
  shows "(\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. f c) * (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. g c)
       \<le> real r ^ card I * (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. f c * g c)"
  using I f g
proof (induction I arbitrary: f g rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i J)
  define F where "F y = (\<Sum>b\<in>J \<rightarrow>\<^sub>E {..<r}. f (b(i := y)))" for y
  define G where "G y = (\<Sum>b\<in>J \<rightarrow>\<^sub>E {..<r}. g (b(i := y)))" for y
  define FG where "FG y = (\<Sum>b\<in>J \<rightarrow>\<^sub>E {..<r}. f (b(i := y)) * g (b(i := y)))" for y
  have IH: "F y * G y \<le> real r ^ card J * FG y" if y: "y < r" for y
    unfolding F_def G_def FG_def
    by (rule insert.IH[OF sdec_upd[OF insert.prems(1) insert.hyps(2) y] sdec_upd[OF insert.prems(2) insert.hyps(2) y]])
  have mono: "(\<forall>y y'. y \<le> y' \<longrightarrow> y' < r \<longrightarrow> F y' \<le> F y \<and> G y' \<le> G y)
            \<or> (\<forall>y y'. y \<le> y' \<longrightarrow> y' < r \<longrightarrow> F y \<le> F y' \<and> G y \<le> G y')"
  proof (cases "i \<in> P")
    case True
    have "F y \<le> F y' \<and> G y \<le> G y'" if yy: "y \<le> y'" "y' < r" for y y'
    proof
      show "F y \<le> F y'" unfolding F_def
        using sdec_step[OF insert.prems(1) insert.hyps(2) _ yy] True by (intro sum_mono) simp
      show "G y \<le> G y'" unfolding G_def
        using sdec_step[OF insert.prems(2) insert.hyps(2) _ yy] True by (intro sum_mono) simp
    qed
    then show ?thesis by blast
  next
    case False
    have "F y' \<le> F y \<and> G y' \<le> G y" if yy: "y \<le> y'" "y' < r" for y y'
    proof
      show "F y' \<le> F y" unfolding F_def
        using sdec_step[OF insert.prems(1) insert.hyps(2) _ yy] False by (intro sum_mono) simp
      show "G y' \<le> G y" unfolding G_def
        using sdec_step[OF insert.prems(2) insert.hyps(2) _ yy] False by (intro sum_mono) simp
    qed
    then show ?thesis by blast
  qed
  have "(\<Sum>c\<in>insert i J \<rightarrow>\<^sub>E {..<r}. f c) * (\<Sum>c\<in>insert i J \<rightarrow>\<^sub>E {..<r}. g c) = (\<Sum>y<r. F y) * (\<Sum>y<r. G y)"
    by (simp only: sum_PiE_insert[OF insert.hyps(2)] F_def G_def)
  also have "\<dots> \<le> real r * (\<Sum>y<r. F y * G y)" by (rule cheb_same[OF mono])
  also have "\<dots> \<le> real r * (\<Sum>y<r. real r ^ card J * FG y)"
    using IH by (intro mult_left_mono sum_mono) auto
  also have "\<dots> = real r * (real r ^ card J * (\<Sum>y<r. FG y))" by (simp only: sum_distrib_left)
  also have "\<dots> = real r ^ card (insert i J) * (\<Sum>y<r. FG y)" using insert.hyps by simp
  also have "(\<Sum>y<r. FG y) = (\<Sum>c\<in>insert i J \<rightarrow>\<^sub>E {..<r}. f c * g c)"
    by (simp only: sum_PiE_insert[OF insert.hyps(2)] FG_def)
  finally show ?case .
qed

lemma sdec_mult:
  assumes f: "sdec I P r f" and g: "sdec I P r g"
    and f0: "\<forall>c\<in>I \<rightarrow>\<^sub>E {..<r}. 0 \<le> f c" and g0: "\<forall>c\<in>I \<rightarrow>\<^sub>E {..<r}. 0 \<le> g c"
  shows "sdec I P r (\<lambda>c. f c * g c)"
  unfolding sdec_def
proof (intro ballI impI)
  fix a b assume a: "a \<in> I \<rightarrow>\<^sub>E {..<r}" and b: "b \<in> I \<rightarrow>\<^sub>E {..<r}"
    and ab: "\<forall>i\<in>I. if i \<in> P then b i \<le> a i else a i \<le> b i"
  have "f b \<le> f a" by (rule sdecD[OF f a b ab])
  moreover have "g b \<le> g a" by (rule sdecD[OF g a b ab])
  moreover have "0 \<le> f a" by (rule bspec[OF f0 a])
  moreover have "0 \<le> g b" by (rule bspec[OF g0 b])
  ultimately show "f b * g b \<le> f a * g a" by (rule mult_mono)
qed

lemma sdec_prod:
  fixes \<phi> :: "'b \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> real"
  assumes K: "finite K" and d: "\<forall>x\<in>K. sdec I P r (\<phi> x)" and p: "\<forall>x\<in>K. \<forall>c\<in>I \<rightarrow>\<^sub>E {..<r}. 0 \<le> \<phi> x c"
  shows "sdec I P r (\<lambda>c. \<Prod>x\<in>K. \<phi> x c)"
  using K d p
proof (induction K rule: finite_induct)
  case empty
  then show ?case by (simp add: sdec_def)
next
  case (insert x K)
  have e: "(\<lambda>c. \<Prod>y\<in>insert x K. \<phi> y c) = (\<lambda>c. \<phi> x c * (\<Prod>y\<in>K. \<phi> y c))"
    using insert.hyps by simp
  have dK: "sdec I P r (\<lambda>c. \<Prod>y\<in>K. \<phi> y c)"
    by (rule insert.IH[OF ball_insertD[OF insert.prems(1)] ball_insertD[OF insert.prems(2)]])
  have px: "\<forall>c\<in>I \<rightarrow>\<^sub>E {..<r}. 0 \<le> \<phi> x c" by (rule bspec[OF insert.prems(2) insertI1])
  have pK: "\<forall>c\<in>I \<rightarrow>\<^sub>E {..<r}. 0 \<le> (\<Prod>y\<in>K. \<phi> y c)"
    using ball_insertD[OF insert.prems(2)] by (intro ballI prod_nonneg) blast
  show ?case unfolding e by (rule sdec_mult[OF bspec[OF insert.prems(1) insertI1] dK px pK])
qed

text \<open>Many functions: if each \<open>\<phi> x\<close> averages at least \<open>\<beta> x\<close>, their product averages at least
  \<open>\<Prod> \<beta> x\<close>.\<close>

theorem harris_prod:
  fixes \<phi> :: "'b \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> real" and \<beta> :: "'b \<Rightarrow> real"
  assumes K: "finite K" and I: "finite I" and r: "0 < r"
    and dec: "\<forall>x\<in>K. sdec I P r (\<phi> x)" and pos: "\<forall>x\<in>K. \<forall>c\<in>I \<rightarrow>\<^sub>E {..<r}. 0 \<le> \<phi> x c"
    and avg: "\<forall>x\<in>K. \<beta> x * real r ^ card I \<le> (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<phi> x c)"
    and b: "\<forall>x\<in>K. 0 \<le> \<beta> x"
  shows "(\<Prod>x\<in>K. \<beta> x) * real r ^ card I \<le> (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<Prod>x\<in>K. \<phi> x c)"
  using K dec pos avg b
proof (induction K rule: finite_induct)
  case empty
  have "card (I \<rightarrow>\<^sub>E {..<r}) = r ^ card I" using I by (simp add: card_PiE)
  then show ?case by simp
next
  case (insert x K)
  define R where "R = real r ^ card I"
  define Q where "Q c = (\<Prod>y\<in>K. \<phi> y c)" for c
  have IH: "(\<Prod>y\<in>K. \<beta> y) * R \<le> (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. Q c)"
    unfolding Q_def R_def
    by (rule insert.IH[OF ball_insertD[OF insert.prems(1)] ball_insertD[OF insert.prems(2)]
          ball_insertD[OF insert.prems(3)] ball_insertD[OF insert.prems(4)]])
  have Ax: "\<beta> x * R \<le> (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<phi> x c)"
    unfolding R_def by (rule bspec[OF insert.prems(3) insertI1])
  have dx: "sdec I P r (\<phi> x)" by (rule bspec[OF insert.prems(1) insertI1])
  have dQ: "sdec I P r Q"
    unfolding Q_def by (rule sdec_prod[OF insert.hyps(1) ball_insertD[OF insert.prems(1)] ball_insertD[OF insert.prems(2)]])
  have px: "\<forall>c\<in>I \<rightarrow>\<^sub>E {..<r}. 0 \<le> \<phi> x c" by (rule bspec[OF insert.prems(2) insertI1])
  have bK: "0 \<le> (\<Prod>y\<in>K. \<beta> y)" using ball_insertD[OF insert.prems(4)] by (intro prod_nonneg) blast
  have R0: "0 < R" using r by (simp add: R_def)
  have "R * ((\<Prod>y\<in>insert x K. \<beta> y) * R) = (\<beta> x * R) * ((\<Prod>y\<in>K. \<beta> y) * R)"
    using insert.hyps by (simp add: mult_ac)
  also have "\<dots> \<le> (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<phi> x c) * (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. Q c)"
  proof (rule mult_mono[OF Ax IH])
    show "0 \<le> (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<phi> x c)" using px by (intro sum_nonneg) blast
    show "0 \<le> (\<Prod>y\<in>K. \<beta> y) * R" using bK R0 by simp
  qed
  also have "\<dots> \<le> R * (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<phi> x c * Q c)" unfolding R_def by (rule harris[OF I dx dQ])
  also have "(\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<phi> x c * Q c) = (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<Prod>y\<in>insert x K. \<phi> y c)"
    using insert.hyps by (simp add: Q_def)
  finally have "R * ((\<Prod>y\<in>insert x K. \<beta> y) * R) \<le> R * (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<Prod>y\<in>insert x K. \<phi> y c)" .
  then show ?case unfolding R_def[symmetric] using R0 by (rule mult_left_le_imp_le)
qed

subsection \<open>Counting with groups of ones\<close>

text \<open>The average of \<open>2\<^sup>N\<close> for a group \<open>x = (G, Z)\<close>, where \<open>N\<close> counts the ones of \<open>G\<close> coloured above
  every zero of \<open>Z\<close>.\<close>

definition gav :: "nat \<Rightarrow> nat set \<times> nat set \<Rightarrow> real" where
  "gav r x = (\<Sum>a\<in>(fst x \<union> snd x) \<rightarrow>\<^sub>E {..<r}. (2::real) ^ card {v\<in>fst x. \<forall>y\<in>snd x. a y < a v})
     / real r ^ card (fst x \<union> snd x)"

lemma sum_local:
  fixes f :: "(nat \<Rightarrow> nat) \<Rightarrow> real"
  assumes I: "finite I" and S: "S \<subseteq> I" and f: "\<And>c. f c = f (restrict c S)"
  shows "(\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. f c) = (\<Sum>a\<in>S \<rightarrow>\<^sub>E {..<r}. f a) * real r ^ card (I - S)"
proof -
  have "(\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. f c * 1) = (\<Sum>a\<in>S \<rightarrow>\<^sub>E {..<r}. f a) * (\<Sum>b\<in>(I - S) \<rightarrow>\<^sub>E {..<r}. (1::real))"
    by (rule sum_PiE_mult[where f = f and g = "\<lambda>_. 1", OF S f]) simp
  moreover have "card ((I - S) \<rightarrow>\<^sub>E {..<r}) = r ^ card (I - S)" using I by (simp add: card_PiE)
  ultimately show ?thesis by simp
qed

theorem harris_count:
  fixes H A :: "nat set set" and n r :: nat and B :: real
  assumes A: "\<forall>X\<in>A. X \<subseteq> {..<n} \<and> (\<forall>e\<in>H. e \<inter> X \<noteq> {})" and r: "0 < r"
    and gr: "\<forall>X\<in>A. \<exists>K. finite K
      \<and> (\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x)))
      \<and> (\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> fst x \<inter> fst y = {})
      \<and> B \<le> (\<Prod>x\<in>K. gav r x)"
  shows "real (card A) * B \<le> 2 ^ n"
proof -
  define C where "C = {..<n} \<rightarrow>\<^sub>E {..<r}"
  define D where "D c X = card {i. i < n \<and> forced n c (mcnf H) X i}" for c X
  have finA: "finite A" by (rule finite_subset[of _ "Pow {..<n}"]) (use A in auto)
  have cC: "card C = r ^ n" by (simp add: C_def card_PiE)
  have kraft: "(\<Sum>X\<in>A. (2::real) ^ D c X) \<le> 2 ^ n" for c
  proof -
    have "A \<subseteq> {X. X \<subseteq> {..<n} \<and> csat (mcnf H) X}" using A by (auto simp: csat_mcnf)
    then have "(\<Sum>X\<in>A. (2::nat) ^ D c X) \<le> 2 ^ n" unfolding D_def by (rule forced_kraft)
    then have "real (\<Sum>X\<in>A. (2::nat) ^ D c X) \<le> real ((2::nat) ^ n)" by (simp only: of_nat_le_iff)
    then show ?thesis by simp
  qed
  have per: "B * real r ^ n \<le> (\<Sum>c\<in>C. (2::real) ^ D c X)" if X: "X \<in> A" for X
  proof -
    from bspec[OF gr X] obtain K where K: "finite K"
      and P: "\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x))"
      and dis: "\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> fst x \<inter> fst y = {}"
      and BK: "B \<le> (\<Prod>x\<in>K. gav r x)"
      by (elim exE conjE)
    have XV: "X \<subseteq> {..<n}" using A X by blast
    define S where "S x = fst x \<union> snd x" for x :: "nat set \<times> nat set"
    define f where "f x c = (2::real) ^ card {v\<in>fst x. \<forall>y\<in>snd x. c y < c v}"
      for x :: "nat set \<times> nat set" and c :: "nat \<Rightarrow> nat"
    have SV: "S x \<subseteq> {..<n}" if "x \<in> K" for x
    proof -
      have "fst x \<subseteq> X" "snd x \<subseteq> {..<n} - X" using P that by blast+
      then show ?thesis using XV by (auto simp: S_def)
    qed
    have lower: "(\<Prod>x\<in>K. f x c) \<le> 2 ^ D c X" for c
    proof -
      define W where "W x = {v\<in>fst x. \<forall>y\<in>snd x. c y < c v}" for x :: "nat set \<times> nat set"
      have WF: "W x \<subseteq> {i. i < n \<and> forced n c (mcnf H) X i}" if x: "x \<in> K" for x
      proof
        fix v assume v: "v \<in> W x"
        then have vG: "v \<in> fst x" and vc: "\<forall>y\<in>snd x. c y < c v" by (auto simp: W_def)
        have Px: "fst x \<subseteq> X" "snd x \<subseteq> {..<n} - X" "\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x)"
          using P x by blast+
        obtain e where e: "e \<in> H" "v \<in> e" "e \<subseteq> insert v (snd x)" using Px(3) vG by blast
        have "\<forall>w\<in>e. w \<noteq> v \<longrightarrow> w \<notin> X \<and> c w < c v" using e(3) Px(2) vc by blast
        then have "forced n c (mcnf H) X v" by (rule forced_mcnf[OF e(1,2)])
        moreover have "v < n" using vG Px(1) XV by blast
        ultimately show "v \<in> {i. i < n \<and> forced n c (mcnf H) X i}" by simp
      qed
      have finW: "finite (W x)" if "x \<in> K" for x using WF[OF that] by (rule finite_subset) simp
      have disW: "\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> W x \<inter> W y = {}"
      proof (intro ballI impI)
        fix x y assume "x \<in> K" "y \<in> K" "x \<noteq> y"
        then have "fst x \<inter> fst y = {}" using dis by blast
        moreover have "W x \<subseteq> fst x" "W y \<subseteq> fst y" by (auto simp: W_def)
        ultimately show "W x \<inter> W y = {}" by blast
      qed
      have "(\<Prod>x\<in>K. f x c) = 2 ^ (\<Sum>x\<in>K. card (W x))" by (simp add: f_def W_def power_sum)
      also have "(\<Sum>x\<in>K. card (W x)) = card (\<Union>x\<in>K. W x)"
        using K finW disW by (intro card_UN_disjoint[symmetric]) auto
      also have "card (\<Union>x\<in>K. W x) \<le> D c X"
        unfolding D_def using WF by (intro card_mono) auto
      then have "(2::real) ^ card (\<Union>x\<in>K. W x) \<le> 2 ^ D c X" by (rule power_increasing) simp
      finally show ?thesis .
    qed
    have dec: "\<forall>x\<in>K. sdec {..<n} X r (f x)"
    proof
      fix x assume x: "x \<in> K"
      have Px: "fst x \<subseteq> X" "snd x \<subseteq> {..<n} - X" using P x by blast+
      show "sdec {..<n} X r (f x)"
        unfolding sdec_def
      proof (intro ballI impI)
        fix a b :: "nat \<Rightarrow> nat"
        assume "a \<in> {..<n} \<rightarrow>\<^sub>E {..<r}" "b \<in> {..<n} \<rightarrow>\<^sub>E {..<r}"
          and ab: "\<forall>i\<in>{..<n}. if i \<in> X then b i \<le> a i else a i \<le> b i"
        have "{v\<in>fst x. \<forall>y\<in>snd x. b y < b v} \<subseteq> {v\<in>fst x. \<forall>y\<in>snd x. a y < a v}"
        proof
          fix v assume v: "v \<in> {v\<in>fst x. \<forall>y\<in>snd x. b y < b v}"
          have vX: "v \<in> X" "v < n" using v Px(1) XV by auto
          have bv: "b v \<le> a v" using ab vX by auto
          have "a y < a v" if y: "y \<in> snd x" for y
          proof -
            have "a y \<le> b y" using ab y Px(2) by auto
            moreover have "b y < b v" using v y by simp
            ultimately show ?thesis using bv by (rule le_less_trans[OF _ less_le_trans])
          qed
          then show "v \<in> {v\<in>fst x. \<forall>y\<in>snd x. a y < a v}" using v by simp
        qed
        then have "card {v\<in>fst x. \<forall>y\<in>snd x. b y < b v} \<le> card {v\<in>fst x. \<forall>y\<in>snd x. a y < a v}"
          by (rule card_mono[rotated]) (use Px(1) XV in \<open>auto intro: finite_subset\<close>)
        then show "f x b \<le> f x a" unfolding f_def by (rule power_increasing) simp
      qed
    qed
    have pos: "\<forall>x\<in>K. \<forall>c\<in>{..<n} \<rightarrow>\<^sub>E {..<r}. 0 \<le> f x c" by (simp add: f_def)
    have avg: "\<forall>x\<in>K. gav r x * real r ^ card {..<n} \<le> (\<Sum>c\<in>{..<n} \<rightarrow>\<^sub>E {..<r}. f x c)"
    proof
      fix x assume x: "x \<in> K"
      have loc: "f x c = f x (restrict c (S x))" for c
      proof -
        have "{v\<in>fst x. \<forall>y\<in>snd x. restrict c (S x) y < restrict c (S x) v} = {v\<in>fst x. \<forall>y\<in>snd x. c y < c v}"
          by (auto simp: S_def)
        then show ?thesis by (simp add: f_def)
      qed
      have e: "(\<Sum>c\<in>{..<n} \<rightarrow>\<^sub>E {..<r}. f x c) = (\<Sum>a\<in>S x \<rightarrow>\<^sub>E {..<r}. f x a) * real r ^ card ({..<n} - S x)"
        by (rule sum_local[where f = "f x" and S = "S x" and I = "{..<n}" and r = r, OF finite_lessThan SV[OF x] loc])
      have cn: "card {..<n} = card (S x) + card ({..<n} - S x)"
      proof -
        have "card ({..<n} - S x) = card {..<n} - card (S x)" by (rule card_Diff_subset[OF finite_subset[OF SV[OF x]] SV[OF x]]) simp
        moreover have "card (S x) \<le> card {..<n}" by (rule card_mono[OF _ SV[OF x]]) simp
        ultimately show ?thesis by simp
      qed
      have g: "gav r x * real r ^ card (S x) = (\<Sum>a\<in>S x \<rightarrow>\<^sub>E {..<r}. f x a)"
        using r by (simp add: gav_def S_def f_def)
      show "gav r x * real r ^ card {..<n} \<le> (\<Sum>c\<in>{..<n} \<rightarrow>\<^sub>E {..<r}. f x c)"
        unfolding e cn power_add g[symmetric] by (simp add: mult_ac)
    qed
    have gav0: "\<forall>x\<in>K. 0 \<le> gav r x" by (simp add: gav_def sum_nonneg)
    have "B * real r ^ n \<le> (\<Prod>x\<in>K. gav r x) * real r ^ card {..<n}"
      unfolding card_lessThan using BK by (rule mult_right_mono) simp
    also have "\<dots> \<le> (\<Sum>c\<in>{..<n} \<rightarrow>\<^sub>E {..<r}. \<Prod>x\<in>K. f x c)"
      by (rule harris_prod[OF K _ r dec pos avg gav0]) simp
    also have "\<dots> \<le> (\<Sum>c\<in>C. (2::real) ^ D c X)" unfolding C_def by (rule sum_mono) (rule lower)
    finally show ?thesis .
  qed
  have "real (card A) * (B * real r ^ n) = (\<Sum>X\<in>A. B * real r ^ n)" by simp
  also have "\<dots> \<le> (\<Sum>X\<in>A. \<Sum>c\<in>C. (2::real) ^ D c X)" by (rule sum_mono) (rule per)
  also have "\<dots> = (\<Sum>c\<in>C. \<Sum>X\<in>A. (2::real) ^ D c X)" by (rule sum.swap)
  also have "\<dots> \<le> (\<Sum>c\<in>C. 2 ^ n)" by (rule sum_mono) (rule kraft)
  also have "\<dots> = real r ^ n * 2 ^ n" using cC by simp
  finally have "real (card A) * B * real r ^ n \<le> 2 ^ n * real r ^ n" by (simp add: mult_ac)
  moreover have "0 < real r ^ n" using r by simp
  ultimately show ?thesis by simp
qed

subsection \<open>Single ones\<close>

lemma pow_up: "(b + 1 :: nat) ^ Suc s \<le> b ^ Suc s + Suc s * (b + 1) ^ s"
proof (induction s)
  case 0
  show ?case by simp
next
  case (Suc s)
  have m: "b ^ Suc s \<le> (b + 1) ^ Suc s" by (rule power_mono) simp_all
  have e: "(b + 1) * (b ^ Suc s + Suc s * (b + 1) ^ s) = b ^ Suc (Suc s) + b ^ Suc s + Suc s * (b + 1) ^ Suc s"
    by (simp add: algebra_simps)
  have "(b + 1) ^ Suc (Suc s) = (b + 1) * (b + 1) ^ Suc s" by simp
  also have "\<dots> \<le> (b + 1) * (b ^ Suc s + Suc s * (b + 1) ^ s)" using Suc.IH by (rule mult_left_mono) simp
  also have "\<dots> \<le> b ^ Suc (Suc s) + Suc (Suc s) * (b + 1) ^ Suc s" unfolding e using m by simp
  finally show ?case .
qed

lemma pow_sum_lower: "(r - 1 :: nat) ^ Suc s \<le> Suc s * (\<Sum>y<r. y ^ s)"
proof (induction r)
  case 0
  show ?case by simp
next
  case (Suc m)
  have st: "m ^ Suc s \<le> (m - 1) ^ Suc s + Suc s * m ^ s"
  proof (cases m)
    case 0
    then show ?thesis by simp
  next
    case (Suc b)
    then show ?thesis using pow_up[of b s] by simp
  qed
  have "(Suc m - 1) ^ Suc s = m ^ Suc s" by simp
  also have "\<dots> \<le> Suc s * (\<Sum>y<m. y ^ s) + Suc s * m ^ s" using st Suc.IH by linarith
  also have "\<dots> = Suc s * (\<Sum>y<Suc m. y ^ s)" by (simp add: algebra_simps)
  finally show ?case .
qed

lemma gav_single:
  assumes Z: "finite Z" and v: "v \<notin> Z" and r: "0 < r"
  shows "1 + (1 - 1 / real r) ^ Suc (card Z) / real (Suc (card Z)) \<le> gav r ({v}, Z)"
proof -
  define s where "s = card Z"
  have cZ: "card (Z \<rightarrow>\<^sub>E {..<r}) = r ^ s" using Z by (simp add: card_PiE s_def)
  have tm: "(2::real) ^ card {w\<in>{v}. \<forall>y\<in>Z. (b(v := y')) y < (b(v := y')) w}
      = 1 + (if \<forall>w\<in>Z. b w < y' then 1 else 0)" for b y'
  proof -
    have "(b(v := y')) y = b y" if "y \<in> Z" for y using that v by auto
    then have "{w\<in>{v}. \<forall>y\<in>Z. (b(v := y')) y < (b(v := y')) w} = (if \<forall>w\<in>Z. b w < y' then {v} else {})"
      by auto
    then show ?thesis by simp
  qed
  have cnt: "card {b \<in> Z \<rightarrow>\<^sub>E {..<r}. \<forall>w\<in>Z. b w < y'} = y' ^ s" if y': "y' < r" for y'
  proof -
    have "{b \<in> Z \<rightarrow>\<^sub>E {..<r}. \<forall>w\<in>Z. b w < y'} = Z \<rightarrow>\<^sub>E {..<y'}"
    proof (rule set_eqI, rule iffI)
      fix b assume "b \<in> {b \<in> Z \<rightarrow>\<^sub>E {..<r}. \<forall>w\<in>Z. b w < y'}"
      then show "b \<in> Z \<rightarrow>\<^sub>E {..<y'}" by (auto simp: PiE_iff)
    next
      fix b assume "b \<in> Z \<rightarrow>\<^sub>E {..<y'}"
      then have b: "\<forall>i\<in>Z. b i < y'" "b \<in> extensional Z" by (auto simp: PiE_iff)
      have "\<forall>i\<in>Z. b i < r" using b(1) y' by (auto intro: less_trans)
      then show "b \<in> {b \<in> Z \<rightarrow>\<^sub>E {..<r}. \<forall>w\<in>Z. b w < y'}" using b by (simp add: PiE_iff)
    qed
    then show ?thesis using Z by (simp add: card_PiE s_def)
  qed
  define h where "h a = (2::real) ^ card {w\<in>{v}. \<forall>y\<in>Z. a y < a w}" for a :: "nat \<Rightarrow> nat"
  have vZ: "{v} \<union> Z = insert v Z" by simp
  have "(\<Sum>a\<in>({v} \<union> Z) \<rightarrow>\<^sub>E {..<r}. (2::real) ^ card {w\<in>{v}. \<forall>y\<in>Z. a y < a w})
      = (\<Sum>a\<in>insert v Z \<rightarrow>\<^sub>E {..<r}. h a)" unfolding vZ h_def by (rule refl)
  also have "\<dots> = (\<Sum>y'<r. \<Sum>b\<in>Z \<rightarrow>\<^sub>E {..<r}. h (b(v := y')))" by (rule sum_PiE_insert[OF v])
  also have "\<dots> = (\<Sum>y'<r. \<Sum>b\<in>Z \<rightarrow>\<^sub>E {..<r}. 1 + (if \<forall>w\<in>Z. b w < y' then 1 else 0))"
    unfolding h_def by (intro sum.cong refl) (rule tm)
  also have "\<dots> = (\<Sum>y'<r. real (r ^ s) + real (y' ^ s))"
  proof (rule sum.cong[OF refl])
    fix y' assume "y' \<in> {..<r}"
    then have c: "card {b \<in> Z \<rightarrow>\<^sub>E {..<r}. \<forall>w\<in>Z. b w < y'} = y' ^ s" by (intro cnt) simp
    have fin: "finite (Z \<rightarrow>\<^sub>E {..<r})" using Z by (simp add: finite_PiE)
    have ind: "(\<Sum>b\<in>Z \<rightarrow>\<^sub>E {..<r}. if \<forall>w\<in>Z. b w < y' then (1::real) else 0)
        = real (card {b \<in> Z \<rightarrow>\<^sub>E {..<r}. \<forall>w\<in>Z. b w < y'})"
      using fin by (simp add: sum.inter_filter[symmetric])
    have "(\<Sum>b\<in>Z \<rightarrow>\<^sub>E {..<r}. 1 + (if \<forall>w\<in>Z. b w < y' then 1 else 0))
        = (\<Sum>b\<in>Z \<rightarrow>\<^sub>E {..<r}. (1::real)) + (\<Sum>b\<in>Z \<rightarrow>\<^sub>E {..<r}. if \<forall>w\<in>Z. b w < y' then 1 else 0)"
      by (rule sum.distrib)
    also have "\<dots> = real (r ^ s) + real (y' ^ s)" unfolding ind c using cZ by simp
    finally show "(\<Sum>b\<in>Z \<rightarrow>\<^sub>E {..<r}. 1 + (if \<forall>w\<in>Z. b w < y' then 1 else 0)) = real (r ^ s) + real (y' ^ s)" .
  qed
  also have "\<dots> = real r ^ Suc s + real (\<Sum>y'<r. y' ^ s)" by (simp add: sum.distrib)
  finally have tot: "(\<Sum>a\<in>({v} \<union> Z) \<rightarrow>\<^sub>E {..<r}. (2::real) ^ card {w\<in>{v}. \<forall>y\<in>Z. a y < a w})
      = real r ^ Suc s + real (\<Sum>y'<r. y' ^ s)" .
  have cU: "card ({v} \<union> Z) = Suc s" using Z v by (simp add: s_def)
  have R0: "0 < real r ^ Suc s" using r by simp
  have low: "real (r - 1) ^ Suc s \<le> real (Suc s) * real (\<Sum>y'<r. y' ^ s)"
  proof -
    have "real ((r - 1) ^ Suc s) \<le> real (Suc s * (\<Sum>y'<r. y' ^ s))" using pow_sum_lower by (simp only: of_nat_le_iff)
    then show ?thesis by (simp only: of_nat_mult of_nat_power)
  qed
  have r1: "1 - 1 / real r = real (r - 1) / real r" using r by (simp add: of_nat_diff field_simps)
  have "(1 - 1 / real r) ^ Suc s / real (Suc s) = real (r - 1) ^ Suc s / (real (Suc s) * real r ^ Suc s)"
    unfolding r1 by (simp add: power_divide)
  also have "\<dots> \<le> real (Suc s) * real (\<Sum>y'<r. y' ^ s) / (real (Suc s) * real r ^ Suc s)"
    using low R0 by (intro divide_right_mono) simp_all
  also have "\<dots> = real (\<Sum>y'<r. y' ^ s) / real r ^ Suc s" by simp
  finally have "1 + (1 - 1 / real r) ^ Suc s / real (Suc s) \<le> 1 + real (\<Sum>y'<r. y' ^ s) / real r ^ Suc s"
    by simp
  also have "\<dots> = gav r ({v}, Z)"
  proof -
    have "gav r ({v}, Z) = (real r ^ Suc s + real (\<Sum>y'<r. y' ^ s)) / real r ^ Suc s"
      unfolding gav_def by (simp only: fst_conv snd_conv tot cU)
    also have "\<dots> = 1 + real (\<Sum>y'<r. y' ^ s) / real r ^ Suc s" using R0 r by (simp add: add_divide_distrib)
    finally show ?thesis by (rule sym)
  qed
  finally show ?thesis by (simp add: s_def)
qed

subsection \<open>Clusters whose zero sets overlap\<close>

lemma gav_cluster:
  assumes G: "card G = z" and Z: "card Z = z" and GZ: "G \<inter> Z = {}" and z: "1 \<le> z" and qz: "q * q \<le> z"
  shows "1 + real q / 8 \<le> gav (4 * z) (G, Z)"
proof -
  have "(1 + real q / 8) * real (4 * z) ^ card (G \<union> Z)
      \<le> (\<Sum>c\<in>(G \<union> Z) \<rightarrow>\<^sub>E {..<4 * z}. (2::real) ^ card {v\<in>G. \<forall>y\<in>Z. c y < c v})"
    by (rule cluster_sum[OF G Z GZ z qz refl])
  moreover have "0 < real (4 * z) ^ card (G \<union> Z)" using z by simp
  ultimately show ?thesis unfolding gav_def by (simp add: pos_le_divide_eq)
qed

text \<open>\<open>cluster_count\<close> without disjoint zero sets: the clusters need disjoint sets of ones only.\<close>

theorem cluster_count_overlap:
  fixes H A :: "nat set set" and n m z q :: nat
  assumes A: "\<forall>X\<in>A. X \<subseteq> {..<n} \<and> (\<forall>e\<in>H. e \<inter> X \<noteq> {})"
    and z: "1 \<le> z" and qz: "q * q \<le> z"
    and cl: "\<forall>X\<in>A. \<exists>K. finite K \<and> card K = m
      \<and> (\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> card (fst x) = z \<and> card (snd x) = z
             \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x)))
      \<and> (\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> fst x \<inter> fst y = {})"
  shows "real (card A) * (1 + real q / 8) ^ m \<le> 2 ^ n"
proof (rule harris_count[OF A])
  show "0 < 4 * z" using z by simp
  show "\<forall>X\<in>A. \<exists>K. finite K
      \<and> (\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x)))
      \<and> (\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> fst x \<inter> fst y = {})
      \<and> (1 + real q / 8) ^ m \<le> (\<Prod>x\<in>K. gav (4 * z) x)"
  proof
    fix X assume X: "X \<in> A"
    from bspec[OF cl X] obtain K where K: "finite K" "card K = m"
      and P: "\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> card (fst x) = z \<and> card (snd x) = z
             \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x))"
      and dis: "\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> fst x \<inter> fst y = {}"
      by (elim exE conjE)
    have one: "1 + real q / 8 \<le> gav (4 * z) x" if x: "x \<in> K" for x
    proof -
      have Px: "fst x \<subseteq> X" "snd x \<subseteq> {..<n} - X" "card (fst x) = z" "card (snd x) = z"
        using P x by blast+
      have "fst x \<inter> snd x = {}" using Px(1,2) by blast
      then have "1 + real q / 8 \<le> gav (4 * z) (fst x, snd x)" by (rule gav_cluster[OF Px(3,4) _ z qz])
      then show ?thesis by simp
    qed
    have "(1 + real q / 8) ^ m = (\<Prod>x\<in>K. 1 + real q / 8)" using K(2) by simp
    also have "\<dots> \<le> (\<Prod>x\<in>K. gav (4 * z) x)" using one by (intro prod_mono) simp
    finally have "(1 + real q / 8) ^ m \<le> (\<Prod>x\<in>K. gav (4 * z) x)" .
    moreover have "\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x))"
      using P by blast
    ultimately show "\<exists>K. finite K
      \<and> (\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x)))
      \<and> (\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> fst x \<inter> fst y = {})
      \<and> (1 + real q / 8) ^ m \<le> (\<Prod>x\<in>K. gav (4 * z) x)"
      using K(1) dis by blast
  qed
qed

subsection \<open>PPZ with Harris in place of Jensen\<close>

theorem harris_ppz_r:
  fixes H A :: "nat set set" and n k t r :: nat
  assumes A: "\<forall>X\<in>A. X \<subseteq> {..<n} \<and> (\<forall>e\<in>H. e \<inter> X \<noteq> {}) \<and> t \<le> card X
      \<and> (\<forall>v\<in>X. \<exists>e\<in>H. v \<in> e \<and> e \<inter> X = {v} \<and> e \<subseteq> {..<n} \<and> card e \<le> k)"
    and r: "0 < r"
  shows "real (card A) * (1 + (1 - 1 / real r) ^ k / real k) ^ t \<le> 2 ^ n"
proof (rule harris_count[OF _ r])
  show "\<forall>X\<in>A. X \<subseteq> {..<n} \<and> (\<forall>e\<in>H. e \<inter> X \<noteq> {})" using A by blast
  define \<rho> where "\<rho> = (1 - 1 / real r) ^ k / real k"
  have q0: "0 \<le> 1 - 1 / real r" "1 - 1 / real r \<le> 1" using r by simp_all
  have \<rho>0: "0 \<le> \<rho>" using q0 by (simp add: \<rho>_def)
  show "\<forall>X\<in>A. \<exists>K. finite K
      \<and> (\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x)))
      \<and> (\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> fst x \<inter> fst y = {})
      \<and> (1 + \<rho>) ^ t \<le> (\<Prod>x\<in>K. gav r x)"
  proof
    fix X assume X: "X \<in> A"
    have AX: "X \<subseteq> {..<n} \<and> (\<forall>e\<in>H. e \<inter> X \<noteq> {}) \<and> t \<le> card X
        \<and> (\<forall>v\<in>X. \<exists>e\<in>H. v \<in> e \<and> e \<inter> X = {v} \<and> e \<subseteq> {..<n} \<and> card e \<le> k)"
      by (rule bspec[OF A X])
    have XV: "X \<subseteq> {..<n}" by (rule conjunct1[OF AX])
    have tX: "t \<le> card X" by (rule conjunct1[OF conjunct2[OF conjunct2[OF AX]]])
    have crit: "\<forall>v\<in>X. \<exists>e. e \<in> H \<and> v \<in> e \<and> e \<inter> X = {v} \<and> e \<subseteq> {..<n} \<and> card e \<le> k"
      using conjunct2[OF conjunct2[OF conjunct2[OF AX]]] by (simp only: Bex_def)
    obtain e where e: "\<forall>v\<in>X. e v \<in> H \<and> v \<in> e v \<and> e v \<inter> X = {v} \<and> e v \<subseteq> {..<n} \<and> card (e v) \<le> k"
      using bchoice[OF crit] by blast
    define K where "K = (\<lambda>v. ({v}, e v - {v})) ` X"
    have finX: "finite X" using XV by (rule finite_subset) simp
    have inj: "inj_on (\<lambda>v. ({v}, e v - {v})) X" by (rule inj_onI) simp
    have one: "1 + \<rho> \<le> gav r ({v}, e v - {v})" if v: "v \<in> X" for v
    proof -
      have e0: "e v \<in> H \<and> v \<in> e v \<and> e v \<inter> X = {v} \<and> e v \<subseteq> {..<n} \<and> card (e v) \<le> k"
        by (rule bspec[OF e v])
      have ev: "v \<in> e v" "e v \<subseteq> {..<n}" "card (e v) \<le> k" using e0 by simp_all
      have "e v - {v} \<subseteq> {..<n}" using ev(2) by blast
      then have fe: "finite (e v - {v})" by (rule finite_subset) simp
      have fev: "finite (e v)" using ev(2) by (rule finite_subset) simp
      have "0 < card (e v)" using ev(1) fev by (auto simp: card_gt_0_iff)
      then have ce: "Suc (card (e v - {v})) = card (e v)" using ev(1) by (simp add: card_Diff_singleton)
      have sk: "Suc (card (e v - {v})) \<le> k" using ce ev(3) by simp
      have kpos: "0 < real (Suc (card (e v - {v})))" by simp
      have "(1 - 1 / real r) ^ k \<le> (1 - 1 / real r) ^ Suc (card (e v - {v}))"
        by (rule power_decreasing[OF sk q0])
      moreover have "1 / real k \<le> 1 / real (Suc (card (e v - {v})))"
        using sk kpos by (intro divide_left_mono) simp_all
      ultimately have "(1 - 1 / real r) ^ k * (1 / real k)
          \<le> (1 - 1 / real r) ^ Suc (card (e v - {v})) * (1 / real (Suc (card (e v - {v}))))"
        using q0 by (intro mult_mono) simp_all
      then have "\<rho> \<le> (1 - 1 / real r) ^ Suc (card (e v - {v})) / real (Suc (card (e v - {v})))"
        by (simp add: \<rho>_def)
      also have "1 + \<dots> \<le> gav r ({v}, e v - {v})" by (rule gav_single[OF fe _ r]) simp
      finally show ?thesis by simp
    qed
    show "\<exists>K. finite K
      \<and> (\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x)))
      \<and> (\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> fst x \<inter> fst y = {})
      \<and> (1 + \<rho>) ^ t \<le> (\<Prod>x\<in>K. gav r x)"
    proof (rule exI[of _ K], intro conjI)
      show "finite K" unfolding K_def using finX by simp
      show "\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x))"
      proof
        fix x assume "x \<in> K"
        then obtain v where v: "v \<in> X" and xv: "x = ({v}, e v - {v})" unfolding K_def by blast
        have e0: "e v \<in> H \<and> v \<in> e v \<and> e v \<inter> X = {v} \<and> e v \<subseteq> {..<n} \<and> card (e v) \<le> k"
          by (rule bspec[OF e v])
        have ev: "e v \<in> H" "v \<in> e v" "e v \<inter> X = {v}" "e v \<subseteq> {..<n}" using e0 by simp_all
        show "fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> (\<forall>w\<in>fst x. \<exists>e\<in>H. w \<in> e \<and> e \<subseteq> insert w (snd x))"
          using ev v xv by auto
      qed
      show "\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> fst x \<inter> fst y = {}" unfolding K_def by auto
      have "(1 + \<rho>) ^ t \<le> (1 + \<rho>) ^ card X" using tX \<rho>0 by (intro power_increasing) simp_all
      also have "\<dots> = (\<Prod>v\<in>X. 1 + \<rho>)" by simp
      also have "\<dots> \<le> (\<Prod>v\<in>X. gav r ({v}, e v - {v}))" using one \<rho>0 by (intro prod_mono) simp
      also have "\<dots> = (\<Prod>x\<in>K. gav r x)" unfolding K_def by (simp add: prod.reindex[OF inj])
      finally show "(1 + \<rho>) ^ t \<le> (\<Prod>x\<in>K. gav r x)" .
    qed
  qed
qed

theorem harris_ppz:
  fixes H A :: "nat set set" and n k t :: nat
  assumes A: "\<forall>X\<in>A. X \<subseteq> {..<n} \<and> (\<forall>e\<in>H. e \<inter> X \<noteq> {}) \<and> t \<le> card X
      \<and> (\<forall>v\<in>X. \<exists>e\<in>H. v \<in> e \<and> e \<inter> X = {v} \<and> e \<subseteq> {..<n} \<and> card e \<le> k)"
  shows "real (card A) * (1 + 1 / real k) ^ t \<le> 2 ^ n"
proof -
  have L: "(\<lambda>r. real (card A) * (1 + (1 - 1 / real r) ^ k * inverse (real k)) ^ t)
      \<longlonglongrightarrow> real (card A) * (1 + (1 - 0) ^ k * inverse (real k)) ^ t"
    by (intro tendsto_intros)
  have "real (card A) * (1 + (1 - 0) ^ k * inverse (real k)) ^ t \<le> 2 ^ n"
  proof (rule LIMSEQ_le_const2[OF L], rule exI[of _ 1], intro allI impI)
    fix r :: nat assume "1 \<le> r"
    then have "real (card A) * (1 + (1 - 1 / real r) ^ k / real k) ^ t \<le> 2 ^ n"
      by (intro harris_ppz_r[OF A]) simp
    then show "real (card A) * (1 + (1 - 1 / real r) ^ k * inverse (real k)) ^ t \<le> 2 ^ n"
      by (simp only: divide_inverse)
  qed
  then show ?thesis by (simp only: diff_zero power_one mult_1 inverse_eq_divide)
qed

end
