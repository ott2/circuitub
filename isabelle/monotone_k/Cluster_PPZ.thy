theory Cluster_PPZ
  imports "Majority_AC0.Depth3_Lower"
begin

section \<open>PPZ without Jensen: clusters of critical clauses\<close>

text \<open>
  \<open>forced_kraft\<close> bounds \<open>\<Sum>\<^sub>X 2\<^bsup>F\<^sub>c(X)\<^esup> \<le> 2\<^sup>n\<close> for every colouring \<open>c\<close>, where \<open>F\<^sub>c(X)\<close> counts the ones of
  \<open>X\<close> forced by a critical clause.  PPZ then averages with Jensen, \<open>E 2\<^sup>F \<ge> 2\<^bsup>E F\<^esup>\<close>.  Here we average
  \<open>2\<^sup>F\<close> itself.  A \<^emph>\<open>cluster\<close> of a transversal \<open>X\<close> is a pair \<open>(G, Z)\<close>: \<open>z\<close> ones \<open>G\<close> and \<open>z\<close> zeros \<open>Z\<close>
  such that every \<open>v \<in> G\<close> lies in an edge inside \<open>Z \<union> {v}\<close>.  Given the colours of \<open>Z\<close>, the ones of
  \<open>G\<close> are forced independently, all against the same maximum colour on \<open>Z\<close>.  That shared
  maximum makes \<open>2\<^sup>N\<close> heavy-tailed: \<open>E 2\<^sup>N \<ge> 1 + \<lfloor>\<surd>z\<rfloor>/8\<close>, whereas \<open>2\<^bsup>E N\<^esup>\<close> is bounded.  Clusters on
  disjoint variables are independent (\<open>sum_PiE_prod_ge\<close>), so a family of transversals with
  \<open>m\<close> disjoint clusters each has at most \<open>2\<^sup>n / (1 + \<lfloor>\<surd>z\<rfloor>/8)\<^sup>m\<close> members (\<open>cluster_count\<close>).  For
  the extremal blocks \<open>K\<^sub>2\<^sub>k\<^sub>-\<^sub>2\<^sup>(\<^sup>k\<^sup>)\<close> (\<open>z = k - 1\<close>, \<open>m = n/(2k-2)\<close>) this is the conjectured
  \<open>2\<^sup>n k\<^bsup>-\<Omega>(n/k)\<^esup>\<close>.\<close>

subsection \<open>Monotone CNFs as literal CNFs\<close>

definition mcnf :: "nat set set \<Rightarrow> nat lit set set" where
  "mcnf H = (\<lambda>e. (\<lambda>v. (v, True)) ` e) ` H"

lemma csat_mcnf: "csat (mcnf H) X \<longleftrightarrow> (\<forall>e\<in>H. e \<inter> X \<noteq> {})"
  unfolding csat_def mcnf_def lv_def by auto

lemma forced_mcnf:
  assumes e: "e \<in> H" "i \<in> e" and o: "\<forall>w\<in>e. w \<noteq> i \<longrightarrow> w \<notin> X \<and> p w < p i"
  shows "forced n p (mcnf H) X i"
  unfolding forced_def
proof (rule bexI[of _ "(\<lambda>v. (v, True)) ` e"], rule exI[of _ True], intro conjI)
  show "(\<lambda>v. (v, True)) ` e \<in> mcnf H" using e(1) by (simp add: mcnf_def)
  show "(i, True) \<in> (\<lambda>v. (v, True)) ` e" using e(2) by simp
  show "(i, \<not> True) \<notin> (\<lambda>v. (v, True)) ` e" by auto
  show "\<forall>l\<in>(\<lambda>v. (v, True)) ` e. fst l \<noteq> i \<longrightarrow> (fst l < n \<longrightarrow> p (fst l) < p i) \<and> \<not> lv X l"
    using o by (auto simp: lv_def)
qed

subsection \<open>Sums over colourings split over disjoint coordinates\<close>

lemma sum_PiE_split:
  fixes h :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> real"
  assumes S: "S \<subseteq> I"
  shows "(\<Sum>c\<in>I \<rightarrow>\<^sub>E R. h (restrict c S) (restrict c (I - S))) = (\<Sum>a\<in>S \<rightarrow>\<^sub>E R. \<Sum>b\<in>(I - S) \<rightarrow>\<^sub>E R. h a b)"
proof -
  have "(\<Sum>a\<in>S \<rightarrow>\<^sub>E R. \<Sum>b\<in>(I - S) \<rightarrow>\<^sub>E R. h a b) = (\<Sum>(a, b)\<in>(S \<rightarrow>\<^sub>E R) \<times> ((I - S) \<rightarrow>\<^sub>E R). h a b)"
    by (rule sum.cartesian_product)
  also have "\<dots> = (\<Sum>c\<in>I \<rightarrow>\<^sub>E R. h (restrict c S) (restrict c (I - S)))"
  proof (rule sum.reindex_bij_witness[of _ "\<lambda>c. (restrict c S, restrict c (I - S))"
        "\<lambda>(a, b) k. if k \<in> S then a k else b k"])
    fix ab assume "ab \<in> (S \<rightarrow>\<^sub>E R) \<times> ((I - S) \<rightarrow>\<^sub>E R)"
    then obtain a b where ab: "ab = (a, b)" "a \<in> S \<rightarrow>\<^sub>E R" "b \<in> (I - S) \<rightarrow>\<^sub>E R" by blast
    have ra: "restrict (\<lambda>k. if k \<in> S then a k else b k) S = a"
      using ab(2) by (auto simp: fun_eq_iff PiE_def extensional_def)
    have rb: "restrict (\<lambda>k. if k \<in> S then a k else b k) (I - S) = b"
      using ab(3) by (auto simp: fun_eq_iff PiE_def extensional_def)
    show "(\<lambda>c. (restrict c S, restrict c (I - S))) ((\<lambda>(a, b) k. if k \<in> S then a k else b k) ab) = ab"
      using ra rb ab(1) by simp
    show "(\<lambda>(a, b) k. if k \<in> S then a k else b k) ab \<in> I \<rightarrow>\<^sub>E R"
      using ab S by (auto simp: PiE_def extensional_def Pi_def)
    show "h (restrict ((\<lambda>(a, b) k. if k \<in> S then a k else b k) ab) S)
        (restrict ((\<lambda>(a, b) k. if k \<in> S then a k else b k) ab) (I - S)) = (case ab of (a, b) \<Rightarrow> h a b)"
      using ra rb ab(1) by simp
  next
    fix c assume c: "c \<in> I \<rightarrow>\<^sub>E R"
    show "(\<lambda>(a, b) k. if k \<in> S then a k else b k) ((\<lambda>c. (restrict c S, restrict c (I - S))) c) = c"
      using c S by (auto simp: fun_eq_iff PiE_def extensional_def)
    show "(\<lambda>c. (restrict c S, restrict c (I - S))) c \<in> (S \<rightarrow>\<^sub>E R) \<times> ((I - S) \<rightarrow>\<^sub>E R)"
      using c S by (auto simp: PiE_def Pi_def)
  qed
  finally show ?thesis by simp
qed

lemma sum_PiE_mult:
  fixes f g :: "(nat \<Rightarrow> 'a) \<Rightarrow> real"
  assumes S: "S \<subseteq> I" and f: "\<And>c. f c = f (restrict c S)" and g: "\<And>c. g c = g (restrict c (I - S))"
  shows "(\<Sum>c\<in>I \<rightarrow>\<^sub>E R. f c * g c) = (\<Sum>a\<in>S \<rightarrow>\<^sub>E R. f a) * (\<Sum>b\<in>(I - S) \<rightarrow>\<^sub>E R. g b)"
proof -
  have "(\<Sum>c\<in>I \<rightarrow>\<^sub>E R. f c * g c) = (\<Sum>c\<in>I \<rightarrow>\<^sub>E R. f (restrict c S) * g (restrict c (I - S)))"
    by (rule sum.cong[OF refl]) (simp only: f[symmetric] g[symmetric])
  also have "\<dots> = (\<Sum>a\<in>S \<rightarrow>\<^sub>E R. \<Sum>b\<in>(I - S) \<rightarrow>\<^sub>E R. f a * g b)"
    by (rule sum_PiE_split[OF S])
  also have "\<dots> = (\<Sum>a\<in>S \<rightarrow>\<^sub>E R. f a) * (\<Sum>b\<in>(I - S) \<rightarrow>\<^sub>E R. g b)"
    by (rule sum_product[symmetric])
  finally show ?thesis .
qed

lemma ball_insertD: "\<forall>x\<in>insert a A. P x \<Longrightarrow> \<forall>x\<in>A. P x"
  by blast

text \<open>Independence: factors depending on disjoint sets of coordinates multiply.\<close>

lemma sum_PiE_prod_ge:
  fixes f :: "'b \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> real" and S :: "'b \<Rightarrow> nat set" and r :: nat
  assumes K: "finite K" and I: "finite I" and sub: "\<forall>x\<in>K. S x \<subseteq> I"
    and dis: "\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> S x \<inter> S y = {}"
    and dep: "\<forall>x\<in>K. \<forall>c. f x c = f x (restrict c (S x))" and pos: "\<forall>x\<in>K. \<forall>c. 0 \<le> f x c"
    and avg: "\<forall>x\<in>K. \<beta> * real r ^ card (S x) \<le> (\<Sum>a\<in>S x \<rightarrow>\<^sub>E {..<r}. f x a)" and b: "0 \<le> \<beta>"
  shows "\<beta> ^ card K * real r ^ card I \<le> (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<Prod>x\<in>K. f x c)"
  using K I sub dis dep pos avg
proof (induction K arbitrary: I rule: finite_induct)
  case empty
  have "card (I \<rightarrow>\<^sub>E {..<r}) = r ^ card I" using empty.prems(1) by (simp add: card_PiE)
  then show ?case by simp
next
  case (insert x K)
  have Sx: "S x \<subseteq> I" using insert.prems(2) by blast
  have sub': "\<forall>y\<in>K. S y \<subseteq> I - S x"
  proof
    fix y assume y: "y \<in> K"
    have "x \<noteq> y" using y insert.hyps(2) by blast
    then have "S x \<inter> S y = {}" using insert.prems(3) y by blast
    then show "S y \<subseteq> I - S x" using insert.prems(2) y by blast
  qed
  define g where "g c = (\<Prod>y\<in>K. f y c)" for c
  have gr: "g c = g (restrict c (I - S x))" for c
    unfolding g_def
  proof (rule prod.cong[OF refl])
    fix y assume y: "y \<in> K"
    have dy: "\<forall>c. f y c = f y (restrict c (S y))" by (rule bspec[OF insert.prems(4)]) (simp add: y)
    have "f y c = f y (restrict c (S y))" by (rule spec[OF dy])
    also have "restrict c (S y) = restrict (restrict c (I - S x)) (S y)"
      using sub' y by (auto simp: fun_eq_iff)
    also have "f y \<dots> = f y (restrict c (I - S x))" by (rule spec[OF dy, symmetric])
    finally show "f y c = f y (restrict c (I - S x))" .
  qed
  have fr: "f x c = f x (restrict c (S x))" for c
    by (rule spec[OF bspec[OF insert.prems(4) insertI1]])
  have dis': "\<forall>y\<in>K. \<forall>y'\<in>K. y \<noteq> y' \<longrightarrow> S y \<inter> S y' = {}" using insert.prems(3) by blast
  have IH: "\<beta> ^ card K * real r ^ card (I - S x) \<le> (\<Sum>c\<in>(I - S x) \<rightarrow>\<^sub>E {..<r}. g c)"
    unfolding g_def
  proof (rule insert.IH)
    show "finite (I - S x)" using insert.prems(1) by simp
  qed (rule sub', rule dis', rule ball_insertD[OF insert.prems(4)], rule ball_insertD[OF insert.prems(5)],
       rule ball_insertD[OF insert.prems(6)])
  have A: "\<beta> * real r ^ card (S x) \<le> (\<Sum>a\<in>S x \<rightarrow>\<^sub>E {..<r}. f x a)"
    by (rule bspec[OF insert.prems(6) insertI1])
  have g0: "0 \<le> (\<Sum>c\<in>(I - S x) \<rightarrow>\<^sub>E {..<r}. g c)"
    unfolding g_def using ball_insertD[OF insert.prems(5)] by (intro sum_nonneg prod_nonneg) blast
  have cI: "card I = card (S x) + card (I - S x)"
  proof -
    have "card (I - S x) = card I - card (S x)" by (rule card_Diff_subset[OF finite_subset[OF Sx insert.prems(1)] Sx])
    moreover have "card (S x) \<le> card I" by (rule card_mono[OF insert.prems(1) Sx])
    ultimately show ?thesis by simp
  qed
  have "\<beta> ^ card (insert x K) * real r ^ card I
      = (\<beta> * real r ^ card (S x)) * (\<beta> ^ card K * real r ^ card (I - S x))"
    using insert.hyps cI by (simp add: power_add mult_ac)
  also have "\<dots> \<le> (\<Sum>a\<in>S x \<rightarrow>\<^sub>E {..<r}. f x a) * (\<Sum>c\<in>(I - S x) \<rightarrow>\<^sub>E {..<r}. g c)"
  proof (rule mult_mono[OF A IH])
    show "0 \<le> (\<Sum>a\<in>S x \<rightarrow>\<^sub>E {..<r}. f x a)"
      by (rule sum_nonneg) (rule spec[OF bspec[OF insert.prems(5) insertI1]])
    show "0 \<le> \<beta> ^ card K * real r ^ card (I - S x)" using b by simp
  qed
  also have "\<dots> = (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. f x c * g c)"
    by (rule sum_PiE_mult[where S = "S x" and I = I and f = "f x" and g = g, OF Sx fr gr, symmetric])
  also have "\<dots> = (\<Sum>c\<in>I \<rightarrow>\<^sub>E {..<r}. \<Prod>y\<in>insert x K. f y c)"
    using insert.hyps by (simp add: g_def)
  finally show ?case .
qed

subsection \<open>One cluster\<close>

lemma inner_sum:
  fixes P :: "nat \<Rightarrow> bool"
  assumes G: "finite G"
  shows "(\<Sum>b\<in>G \<rightarrow>\<^sub>E {..<r}. (2::real) ^ card {v\<in>G. P (b v)})
       = (real r + real (card {y\<in>{..<r}. P y})) ^ card G"
proof -
  define \<phi> :: "nat \<Rightarrow> real" where "\<phi> y = (if P y then 2 else 1)" for y
  have p: "(2::real) ^ card {v\<in>G. P (b v)} = (\<Prod>v\<in>G. \<phi> (b v))" for b
  proof -
    have "(\<Prod>v\<in>G. \<phi> (b v)) = (\<Prod>v\<in>G \<inter> {v. P (b v)}. 2) * (\<Prod>v\<in>G \<inter> - {v. P (b v)}. 1)"
      unfolding \<phi>_def using G by (rule prod.If_cases)
    also have "G \<inter> {v. P (b v)} = {v\<in>G. P (b v)}" by blast
    finally show ?thesis by simp
  qed
  have "(\<Sum>b\<in>G \<rightarrow>\<^sub>E {..<r}. (2::real) ^ card {v\<in>G. P (b v)}) = (\<Sum>b\<in>G \<rightarrow>\<^sub>E {..<r}. \<Prod>v\<in>G. \<phi> (b v))"
    using p by simp
  also have "\<dots> = (\<Prod>v\<in>G. \<Sum>y\<in>{..<r}. \<phi> y)"
    using prod_sum_PiE[where A = G and B = "\<lambda>_. {..<r}" and f = "\<lambda>_ y. \<phi> y"] G by simp
  also have "\<dots> = (\<Sum>y\<in>{..<r}. \<phi> y) ^ card G" by simp
  also have "(\<Sum>y\<in>{..<r}. \<phi> y) = real r + real (card {y\<in>{..<r}. P y})"
  proof -
    have "(\<Sum>y\<in>{..<r}. \<phi> y) = (\<Sum>y\<in>{..<r}. 1 + (if P y then 1 else 0))"
      by (rule sum.cong) (auto simp: \<phi>_def)
    also have "\<dots> = real r + (\<Sum>y\<in>{..<r}. if P y then 1 else 0)" by (simp add: sum.distrib)
    also have "(\<Sum>y\<in>{..<r}. if P y then (1::real) else 0) = real (card {y\<in>{..<r}. P y})"
      by (simp add: sum.inter_filter[symmetric])
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma step_pow: "(b::nat) ^ Suc m + Suc m * b ^ m \<le> (b + 1) ^ Suc m"
proof (induction m)
  case 0
  show ?case by simp
next
  case (Suc m)
  have e: "(b + 1) * (b ^ Suc m + Suc m * b ^ m) = b ^ Suc (Suc m) + Suc (Suc m) * b ^ Suc m + Suc m * b ^ m"
    by (simp add: algebra_simps)
  have "b ^ Suc (Suc m) + Suc (Suc m) * b ^ Suc m \<le> (b + 1) * (b ^ Suc m + Suc m * b ^ m)"
    unfolding e by simp
  also have "\<dots> \<le> (b + 1) * (b + 1) ^ Suc m" using Suc.IH by (rule mult_left_mono) simp
  also have "\<dots> = (b + 1) ^ Suc (Suc m)" by simp
  finally show ?case .
qed

lemma pow_telescope:
  fixes r s z :: nat
  assumes z: "1 \<le> z"
  shows "r ^ z + (\<Sum>i<s. z * (r + i) ^ (z - 1)) \<le> (r + s) ^ z"
proof (induction s)
  case 0
  then show ?case by simp
next
  case (Suc s)
  obtain w where w: "z = Suc w" using z by (cases z) auto
  have st: "(r + s) ^ Suc w + Suc w * (r + s) ^ w \<le> (r + s + 1) ^ Suc w" by (rule step_pow)
  have "r ^ z + (\<Sum>i<Suc s. z * (r + i) ^ (z - 1)) = (r ^ z + (\<Sum>i<s. z * (r + i) ^ (z - 1))) + z * (r + s) ^ (z - 1)"
    by simp
  also have "\<dots> \<le> (r + s) ^ z + z * (r + s) ^ (z - 1)" using Suc.IH by simp
  also have "\<dots> \<le> (r + Suc s) ^ z" using st w by simp
  finally show ?case .
qed

lemma pt_bound:
  fixes r s z q :: nat
  assumes z: "1 \<le> z"
  shows "r ^ z + (\<Sum>i<q. if i < s then z * (r + i) ^ (z - 1) else 0) \<le> (r + s) ^ z"
proof -
  have "(\<Sum>i<q. if i < s then z * (r + i) ^ (z - 1) else 0) = (\<Sum>i\<in>{i\<in>{..<q}. i < s}. z * (r + i) ^ (z - 1))"
    by (rule sum.inter_filter[symmetric]) simp
  also have "\<dots> \<le> (\<Sum>i<s. z * (r + i) ^ (z - 1))" by (rule sum_mono2) auto
  finally show ?thesis using pow_telescope[OF z, of r s] by linarith
qed

lemma count_bound:
  assumes Z: "finite Z" and ir: "Suc i \<le> r"
  shows "(r - Suc i) ^ card Z \<le> card {a \<in> Z \<rightarrow>\<^sub>E {..<r}. i < card {y\<in>{..<r}. \<forall>w\<in>Z. a w < y}}"
proof -
  have sub: "Z \<rightarrow>\<^sub>E {..<r - Suc i} \<subseteq> {a \<in> Z \<rightarrow>\<^sub>E {..<r}. i < card {y\<in>{..<r}. \<forall>w\<in>Z. a w < y}}"
  proof
    fix a assume a: "a \<in> Z \<rightarrow>\<^sub>E {..<r - Suc i}"
    have aZ: "a \<in> Z \<rightarrow>\<^sub>E {..<r}" using a by (auto simp: PiE_iff)
    have "{r - Suc i..<r} \<subseteq> {y\<in>{..<r}. \<forall>w\<in>Z. a w < y}" using a by (auto simp: PiE_iff)
    then have "card {r - Suc i..<r} \<le> card {y\<in>{..<r}. \<forall>w\<in>Z. a w < y}" by (rule card_mono[rotated]) simp
    moreover have "card {r - Suc i..<r} = Suc i" using ir by simp
    ultimately show "a \<in> {a \<in> Z \<rightarrow>\<^sub>E {..<r}. i < card {y\<in>{..<r}. \<forall>w\<in>Z. a w < y}}" using aZ by simp
  qed
  have fin: "finite {a \<in> Z \<rightarrow>\<^sub>E {..<r}. i < card {y\<in>{..<r}. \<forall>w\<in>Z. a w < y}}"
    using Z by (intro finite_subset[OF _ finite_PiE[of Z "\<lambda>_. {..<r}"]]) auto
  have "card (Z \<rightarrow>\<^sub>E {..<r - Suc i}) = (r - Suc i) ^ card Z" using Z by (simp add: card_PiE)
  then show ?thesis using card_mono[OF fin sub] by simp
qed

text \<open>The main estimate, \<open>(r+i)\<^bsup>z-1\<^esup> (r-i-1)\<^sup>z \<ge> r\<^bsup>2z-1\<^esup>/2\<close> for \<open>i < \<lfloor>\<surd>z\<rfloor>\<close> and \<open>r = 4z\<close>.  The first-order
  terms cancel in the product \<open>(r+i)(r-i-1) = r\<^sup>2 - r - i\<^sup>2 - i \<ge> r\<^sup>2 (1 - 5/(16z))\<close>, and Bernoulli
  bounds the \<open>(z-1)\<close>-th power of the bracket by \<open>11/16\<close>.\<close>

lemma term_bound:
  fixes z q i r :: nat
  assumes z: "1 \<le> z" and iq: "Suc i \<le> q" and qz: "q * q \<le> z" and r: "r = 4 * z"
  shows "real z * real r ^ (2 * z - 1) / 2 \<le> real (z * (r + i) ^ (z - 1) * (r - Suc i) ^ z)"
proof -
  obtain w where w: "z = Suc w" using z by (cases z) auto
  define R where "R = real r"
  have Rz: "R = 4 * real z" using r by (simp add: R_def)
  have q1: "q \<le> q * q" using iq by simp
  have iz: "Suc i \<le> z" using iq q1 qz by linarith
  have ii: "Suc i * Suc i \<le> z" using mult_le_mono[OF iq iq] qz by linarith
  have i2: "real i * real i + real i \<le> real z"
  proof -
    have "i * i + i \<le> z" using ii by simp
    then have "real (i * i + i) \<le> real z" by (simp only: of_nat_le_iff)
    then show ?thesis by simp
  qed
  have izr: "real i + 1 \<le> real z" using iz by simp
  have ri: "real (r - Suc i) = R - real i - 1" using iz r by (simp add: R_def of_nat_diff)
  have zp: "0 < real z" using z by simp
  define x :: real where "x = 5 / (16 * real z)"
  define a where "a = (R + real i) * (R - real i - 1)"
  have ae: "a = R * R - R - real i * real i - real i" by (simp add: a_def algebra_simps)
  have a1: "R * R - 5 * real z \<le> a" using ae i2 Rz by linarith
  have Rx: "R * R * (1 - x) = R * R - 5 * real z"
    using zp by (simp add: x_def Rz field_simps)
  have x0: "0 \<le> x" "x \<le> 1" using z by (simp_all add: x_def)
  have wx: "real w * x \<le> 5 / 16"
  proof -
    have "real w * x = 5 * real w / (16 * real z)" by (simp add: x_def)
    also have "\<dots> \<le> 5 / 16" using zp w by (simp add: divide_le_eq)
    finally show ?thesis .
  qed
  have bern: "1 - real w * x \<le> (1 - x) ^ w"
    using Bernoulli_inequality[of "- x" w] x0 by simp
  have R0: "0 \<le> R" by (simp add: R_def)
  have aR: "R * R * (1 - x) \<le> a" using a1 Rx by simp
  have a0: "0 \<le> R * R * (1 - x)" using R0 x0 by simp
  have aw: "(R * R) ^ w * (11 / 16) \<le> a ^ w"
  proof -
    have "(R * R) ^ w * (11 / 16) \<le> (R * R) ^ w * (1 - real w * x)"
      using wx by (intro mult_left_mono) simp_all
    also have "\<dots> \<le> (R * R) ^ w * (1 - x) ^ w" using bern by (intro mult_left_mono) simp_all
    also have "\<dots> = (R * R * (1 - x)) ^ w" by (simp add: power_mult_distrib)
    also have "\<dots> \<le> a ^ w" using aR a0 by (intro power_mono) simp_all
    finally show ?thesis .
  qed
  have b: "3 / 4 * R \<le> R - real i - 1" using izr Rz by linarith
  have b0: "0 \<le> 3 / 4 * R" using R0 by simp
  have zw: "z - 1 = w" using w by simp
  have rr: "real (r + i) = R + real i" by (simp add: R_def)
  have "real (z * (r + i) ^ (z - 1) * (r - Suc i) ^ z) = real z * real (r + i) ^ (z - 1) * real (r - Suc i) ^ z"
    by (simp only: of_nat_mult of_nat_power)
  also have "\<dots> = real z * ((R + real i) ^ w * (R - real i - 1) ^ z)"
    by (simp only: rr ri zw mult.assoc)
  also have "(R + real i) ^ w * (R - real i - 1) ^ z = a ^ w * (R - real i - 1)"
    using w by (simp add: a_def power_mult_distrib mult_ac)
  finally have e: "real (z * (r + i) ^ (z - 1) * (r - Suc i) ^ z) = real z * (a ^ w * (R - real i - 1))" .
  have "(R * R) ^ w * (11 / 16) * (3 / 4 * R) \<le> a ^ w * (R - real i - 1)"
  proof (rule mult_mono[OF aw b])
    have "0 \<le> a" using aR a0 by linarith
    then show "0 \<le> a ^ w" by simp
  qed (rule b0)
  moreover have "(R * R) ^ w * (11 / 16) * (3 / 4 * R) = 33 / 64 * R ^ (2 * z - 1)"
    using w by (simp add: power_mult_distrib power2_eq_square[symmetric] power_mult[symmetric] mult_ac)
  moreover have "R ^ (2 * z - 1) / 2 \<le> 33 / 64 * R ^ (2 * z - 1)" using R0 by simp
  ultimately have "R ^ (2 * z - 1) / 2 \<le> a ^ w * (R - real i - 1)" by linarith
  then have "real z * (R ^ (2 * z - 1) / 2) \<le> real z * (a ^ w * (R - real i - 1))"
    by (rule mult_left_mono) simp
  then have fin: "real z * R ^ (2 * z - 1) / 2 \<le> real z * (a ^ w * (R - real i - 1))" by simp
  show ?thesis using fin by (simp only: e R_def)
qed

lemma cluster_sum:
  fixes G Z :: "nat set" and z q r :: nat
  assumes G: "card G = z" and Z: "card Z = z" and GZ: "G \<inter> Z = {}"
    and z: "1 \<le> z" and qz: "q * q \<le> z" and r: "r = 4 * z"
  shows "(1 + real q / 8) * real r ^ card (G \<union> Z)
       \<le> (\<Sum>c\<in>(G \<union> Z) \<rightarrow>\<^sub>E {..<r}. (2::real) ^ card {v\<in>G. \<forall>y\<in>Z. c y < c v})"
proof -
  have fG: "finite G" using G z by (intro card_ge_0_finite) simp
  have fZ: "finite Z" using Z z by (intro card_ge_0_finite) simp
  have cU: "card (G \<union> Z) = 2 * z" using card_Un_disjoint[OF fG fZ GZ] G Z by simp
  have IZ: "(G \<union> Z) - Z = G" using GZ by blast
  define cnt where "cnt a = card {y\<in>{..<r}. \<forall>w\<in>Z. a w < y}" for a :: "nat \<Rightarrow> nat"
  define h where "h a b = (2::real) ^ card {v\<in>G. \<forall>y\<in>Z. a y < b v}" for a b :: "nat \<Rightarrow> nat"
  define d where "d i = z * (r + i) ^ (z - 1)" for i
  have s1: "(\<Sum>c\<in>(G \<union> Z) \<rightarrow>\<^sub>E {..<r}. (2::real) ^ card {v\<in>G. \<forall>y\<in>Z. c y < c v})
      = (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. \<Sum>b\<in>G \<rightarrow>\<^sub>E {..<r}. h a b)"
  proof -
    have "(\<Sum>c\<in>(G \<union> Z) \<rightarrow>\<^sub>E {..<r}. (2::real) ^ card {v\<in>G. \<forall>y\<in>Z. c y < c v})
        = (\<Sum>c\<in>(G \<union> Z) \<rightarrow>\<^sub>E {..<r}. h (restrict c Z) (restrict c ((G \<union> Z) - Z)))"
    proof (rule sum.cong[OF refl])
      fix c :: "nat \<Rightarrow> nat"
      have "{v\<in>G. \<forall>y\<in>Z. restrict c Z y < restrict c ((G \<union> Z) - Z) v} = {v\<in>G. \<forall>y\<in>Z. c y < c v}"
        using IZ by auto
      then show "(2::real) ^ card {v\<in>G. \<forall>y\<in>Z. c y < c v} = h (restrict c Z) (restrict c ((G \<union> Z) - Z))"
        by (simp add: h_def)
    qed
    also have "\<dots> = (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. \<Sum>b\<in>((G \<union> Z) - Z) \<rightarrow>\<^sub>E {..<r}. h a b)"
      by (rule sum_PiE_split) blast
    finally show ?thesis using IZ by simp
  qed
  have s2: "(\<Sum>b\<in>G \<rightarrow>\<^sub>E {..<r}. h a b) = real ((r + cnt a) ^ z)" for a
    using inner_sum[OF fG, where r = r and P = "\<lambda>y. \<forall>w\<in>Z. a w < y"] G by (simp add: h_def cnt_def)
  have cZ: "card (Z \<rightarrow>\<^sub>E {..<r}) = r ^ z" using fZ Z by (simp add: card_PiE)
  have finZ: "finite (Z \<rightarrow>\<^sub>E {..<r})" using fZ by (simp add: finite_PiE)
  have s3: "r ^ z * r ^ z + (\<Sum>i<q. d i * (r - Suc i) ^ z) \<le> (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. (r + cnt a) ^ z)"
  proof -
    have "(\<Sum>i<q. d i * (r - Suc i) ^ z) \<le> (\<Sum>i<q. d i * card {a \<in> Z \<rightarrow>\<^sub>E {..<r}. i < cnt a})"
    proof (rule sum_mono)
      fix i assume "i \<in> {..<q}"
      then have iq: "Suc i \<le> q" by simp
      have "q \<le> q * q" by (rule le_square)
      then have "Suc i \<le> r" using iq qz r by linarith
      then show "d i * (r - Suc i) ^ z \<le> d i * card {a \<in> Z \<rightarrow>\<^sub>E {..<r}. i < cnt a}"
        using count_bound[OF fZ, where i = i and r = r] Z by (intro mult_left_mono) (simp_all add: cnt_def)
    qed
    also have "\<dots> = (\<Sum>i<q. \<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. if i < cnt a then d i else 0)"
      using finZ by (simp add: sum.inter_filter[symmetric] mult.commute)
    also have "\<dots> = (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. \<Sum>i<q. if i < cnt a then d i else 0)" by (rule sum.swap)
    finally have "r ^ z * r ^ z + (\<Sum>i<q. d i * (r - Suc i) ^ z)
        \<le> (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. r ^ z) + (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. \<Sum>i<q. if i < cnt a then d i else 0)"
      using cZ by simp
    also have "\<dots> = (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. r ^ z + (\<Sum>i<q. if i < cnt a then d i else 0))"
      by (simp add: sum.distrib)
    also have "\<dots> \<le> (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. (r + cnt a) ^ z)"
      by (rule sum_mono) (simp only: d_def pt_bound[OF z])
    finally show ?thesis .
  qed
  define R where "R = real r"
  have Rz: "R = 4 * real z" using r by (simp add: R_def)
  have tb: "real z * R ^ (2 * z - 1) / 2 \<le> real (d i * (r - Suc i) ^ z)" if "i < q" for i
    using term_bound[OF z _ qz r, of i] that by (simp add: d_def R_def)
  define P where "P = R ^ (2 * z - 1)"
  define T where "T = (\<Sum>i<q. real (d i * (r - Suc i) ^ z))"
  have qT: "real q * (real z * P / 2) \<le> T"
    using sum_mono[of "{..<q}" "\<lambda>_. real z * R ^ (2 * z - 1) / 2" "\<lambda>i. real (d i * (r - Suc i) ^ z)"] tb
    by (simp add: P_def T_def)
  have RP: "R ^ (2 * z) = R * P"
  proof -
    have "2 * z = Suc (2 * z - 1)" using z by simp
    then have "R ^ (2 * z) = R ^ Suc (2 * z - 1)" by (rule arg_cong)
    then show ?thesis by (simp add: P_def)
  qed
  have e1: "R ^ z * R ^ z = R * P" using RP by (simp add: power_add[symmetric] mult_2[symmetric])
  have e2: "(1 + real q / 8) * (R * P) = R * P + real q * (real z * P / 2)"
    using Rz by (simp add: algebra_simps)
  have "(1 + real q / 8) * R ^ (2 * z) \<le> R ^ z * R ^ z + (\<Sum>i<q. real (d i * (r - Suc i) ^ z))"
    unfolding RP e1 e2 T_def[symmetric] using qT by simp
  also have "\<dots> = real (r ^ z * r ^ z + (\<Sum>i<q. d i * (r - Suc i) ^ z))" by (simp add: R_def)
  also have "\<dots> \<le> real (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. (r + cnt a) ^ z)" using s3 by (simp only: of_nat_le_iff)
  also have "\<dots> = (\<Sum>a\<in>Z \<rightarrow>\<^sub>E {..<r}. \<Sum>b\<in>G \<rightarrow>\<^sub>E {..<r}. h a b)" by (simp add: s2)
  finally show ?thesis using s1 cU by (simp add: R_def)
qed

subsection \<open>The cluster count\<close>

theorem cluster_count:
  fixes H A :: "nat set set" and n m z q :: nat
  assumes A: "\<forall>X\<in>A. X \<subseteq> {..<n} \<and> (\<forall>e\<in>H. e \<inter> X \<noteq> {})"
    and z: "1 \<le> z" and qz: "q * q \<le> z"
    and cl: "\<forall>X\<in>A. \<exists>K. finite K \<and> card K = m
      \<and> (\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> card (fst x) = z \<and> card (snd x) = z
             \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x)))
      \<and> (\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> (fst x \<union> snd x) \<inter> (fst y \<union> snd y) = {})"
  shows "real (card A) * (1 + real q / 8) ^ m \<le> 2 ^ n"
proof -
  define r where "r = 4 * z"
  define C where "C = {..<n} \<rightarrow>\<^sub>E {..<r}"
  define D where "D c X = card {i. i < n \<and> forced n c (mcnf H) X i}" for c X
  define \<beta> :: real where "\<beta> = 1 + real q / 8"
  have finA: "finite A" by (rule finite_subset[of _ "Pow {..<n}"]) (use A in auto)
  have finC: "finite C" by (simp add: C_def finite_PiE)
  have cC: "card C = r ^ n" by (simp add: C_def card_PiE)
  have kraft: "(\<Sum>X\<in>A. (2::real) ^ D c X) \<le> 2 ^ n" for c
  proof -
    have "A \<subseteq> {X. X \<subseteq> {..<n} \<and> csat (mcnf H) X}" using A by (auto simp: csat_mcnf)
    then have "(\<Sum>X\<in>A. (2::nat) ^ D c X) \<le> 2 ^ n" unfolding D_def by (rule forced_kraft)
    then have "real (\<Sum>X\<in>A. (2::nat) ^ D c X) \<le> real ((2::nat) ^ n)" by (simp only: of_nat_le_iff)
    then show ?thesis by simp
  qed
  have per: "\<beta> ^ m * real r ^ n \<le> (\<Sum>c\<in>C. (2::real) ^ D c X)" if X: "X \<in> A" for X
  proof -
    from bspec[OF cl X] obtain K where K: "finite K" "card K = m"
      and P: "\<forall>x\<in>K. fst x \<subseteq> X \<and> snd x \<subseteq> {..<n} - X \<and> card (fst x) = z \<and> card (snd x) = z
             \<and> (\<forall>v\<in>fst x. \<exists>e\<in>H. v \<in> e \<and> e \<subseteq> insert v (snd x))"
      and dis: "\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> (fst x \<union> snd x) \<inter> (fst y \<union> snd y) = {}"
      by (elim exE conjE)
    have XV: "X \<subseteq> {..<n}" using A X by blast
    define S where "S x = fst x \<union> snd x" for x :: "nat set \<times> nat set"
    define f where "f x c = (2::real) ^ card {v\<in>fst x. \<forall>y\<in>snd x. c y < c v}"
      for x :: "nat set \<times> nat set" and c :: "nat \<Rightarrow> nat"
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
        then have "(fst x \<union> snd x) \<inter> (fst y \<union> snd y) = {}" using dis by blast
        moreover have "W x \<subseteq> fst x \<union> snd x" "W y \<subseteq> fst y \<union> snd y" by (auto simp: W_def)
        ultimately show "W x \<inter> W y = {}" by blast
      qed
      have "(\<Prod>x\<in>K. f x c) = 2 ^ (\<Sum>x\<in>K. card (W x))" by (simp add: f_def W_def power_sum)
      also have "(\<Sum>x\<in>K. card (W x)) = card (\<Union>x\<in>K. W x)"
        using K(1) finW disW by (intro card_UN_disjoint[symmetric]) auto
      also have "card (\<Union>x\<in>K. W x) \<le> D c X"
        unfolding D_def using WF by (intro card_mono) auto
      then have "(2::real) ^ card (\<Union>x\<in>K. W x) \<le> 2 ^ D c X" by (rule power_increasing) simp
      finally show ?thesis .
    qed
    have avg: "\<forall>x\<in>K. \<beta> * real r ^ card (S x) \<le> (\<Sum>a\<in>S x \<rightarrow>\<^sub>E {..<r}. f x a)"
    proof
      fix x assume x: "x \<in> K"
      have Px: "fst x \<subseteq> X" "snd x \<subseteq> {..<n} - X" "card (fst x) = z" "card (snd x) = z"
        using P x by blast+
      have "fst x \<inter> snd x = {}" using Px(1,2) by blast
      then show "\<beta> * real r ^ card (S x) \<le> (\<Sum>a\<in>S x \<rightarrow>\<^sub>E {..<r}. f x a)"
        using cluster_sum[OF Px(3,4) _ z qz r_def] by (simp add: \<beta>_def S_def f_def)
    qed
    have "\<beta> ^ card K * real r ^ card {..<n} \<le> (\<Sum>c\<in>{..<n} \<rightarrow>\<^sub>E {..<r}. \<Prod>x\<in>K. f x c)"
    proof (rule sum_PiE_prod_ge[where S = S])
      show "finite K" by (rule K(1))
      show "finite {..<n}" by simp
      show "\<forall>x\<in>K. S x \<subseteq> {..<n}"
      proof
        fix x assume "x \<in> K"
        then have "fst x \<subseteq> X" "snd x \<subseteq> {..<n} - X" using P by blast+
        then show "S x \<subseteq> {..<n}" using XV by (auto simp: S_def)
      qed
      show "\<forall>x\<in>K. \<forall>y\<in>K. x \<noteq> y \<longrightarrow> S x \<inter> S y = {}" using dis by (simp add: S_def)
      show "\<forall>x\<in>K. \<forall>c. f x c = f x (restrict c (S x))"
      proof (intro ballI allI)
        fix x and c :: "nat \<Rightarrow> nat" assume "x \<in> K"
        have "{v\<in>fst x. \<forall>y\<in>snd x. restrict c (S x) y < restrict c (S x) v} = {v\<in>fst x. \<forall>y\<in>snd x. c y < c v}"
          by (auto simp: S_def)
        then show "f x c = f x (restrict c (S x))" by (simp add: f_def)
      qed
      show "\<forall>x\<in>K. \<forall>c. 0 \<le> f x c" by (simp add: f_def)
      show "\<forall>x\<in>K. \<beta> * real r ^ card (S x) \<le> (\<Sum>a\<in>S x \<rightarrow>\<^sub>E {..<r}. f x a)" by (rule avg)
      show "0 \<le> \<beta>" by (simp add: \<beta>_def)
    qed
    also have "\<dots> \<le> (\<Sum>c\<in>C. (2::real) ^ D c X)" unfolding C_def by (rule sum_mono) (rule lower)
    finally show ?thesis using K(2) by simp
  qed
  have "real (card A) * (\<beta> ^ m * real r ^ n) = (\<Sum>X\<in>A. \<beta> ^ m * real r ^ n)" by simp
  also have "\<dots> \<le> (\<Sum>X\<in>A. \<Sum>c\<in>C. (2::real) ^ D c X)" by (rule sum_mono) (rule per)
  also have "\<dots> = (\<Sum>c\<in>C. \<Sum>X\<in>A. (2::real) ^ D c X)" by (rule sum.swap)
  also have "\<dots> \<le> (\<Sum>c\<in>C. 2 ^ n)" by (rule sum_mono) (rule kraft)
  also have "\<dots> = real r ^ n * 2 ^ n" using cC by simp
  finally have "real (card A) * \<beta> ^ m * real r ^ n \<le> 2 ^ n * real r ^ n" by (simp add: mult_ac)
  moreover have "0 < real r ^ n" using z by (simp add: r_def)
  ultimately show ?thesis by (simp add: \<beta>_def)
qed

end
