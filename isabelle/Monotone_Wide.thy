theory Monotone_Wide
  imports Monotone_Hyper
begin

section \<open>Block-symmetric tests of unbounded scope\<close>

text \<open>
  A test is now an arbitrary monotone predicate \<open>G\<close> of the \<open>k\<close> block weights (equivalently,
  a monotone CNF that is invariant under permuting the variables inside each block).  No bound
  on the number of blocks a clause reads is assumed.

  Fix a window \<open>[lo, hi]\<close> of typical block weights.  For a tight typical coordinate \<open>l\<close> of an
  accepted vector \<open>p\<close>, take a maximal false weight vector \<open>v\<close> above \<open>p - e\<^sub>l\<close>.  The decoder
  fills every unknown coordinate with \<open>hi\<close>; this is correct unless some typical coordinate
  \<open>i\<close> has \<open>v i < hi\<close>.  Only these \<^emph>\<open>light\<close> coordinates must be decoded before \<open>l\<close>
  (\<open>wdec_eq\<close>, \<open>wfree_determined\<close>).

  Each light coordinate multiplies the number of maximal false inputs with weights \<open>v\<close> by
  \<open>C(b, v i) \<ge> \<beta>\<close>, so a test whose CNF has fewer than \<open>\<beta>\<^sup>w\<^sup>+\<^sup>1\<close> clauses has fewer than \<open>w\<close>
  light coordinates per witness (\<open>wide_cost\<close>).  Averaging over \<open>w\<^sup>k\<close> colourings as in
  \<open>Monotone_Hyper\<close> then gives the count \<open>wide_compress\<close>, and for sound tests \<open>wide_cover\<close>.
  The width that matters is thus \<open>log(size) / log \<beta> \<approx> log(size) / b\<close>, whatever the scopes.
\<close>

subsection \<open>Definitions\<close>

definition wmono :: "nat \<Rightarrow> ((nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> bool" where
  "wmono k G \<longleftrightarrow> (\<forall>u v. (\<forall>i<k. u i \<le> v i) \<longrightarrow> G u \<longrightarrow> G v)"

definition atyp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "atyp k lo hi u = {i. i < k \<and> (u i < lo \<or> hi < u i)}"

definition wtight :: "nat \<Rightarrow> ((nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "wtight k G lo hi u = {l. l < k \<and> l \<notin> atyp k lo hi u \<and> \<not> G (u(l := u l - 1))}"

definition wfill :: "nat set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "wfill K u h = (\<lambda>i. if i \<in> K then u i else h)"

text \<open>\<open>l\<close> is decoded in the order \<open>\<sigma>\<close> if it is typical and has a false witness whose light
  coordinates all come earlier.\<close>

definition wdec :: "nat \<Rightarrow> ((nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat)
                      \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "wdec k G lo hi \<sigma> p l \<longleftrightarrow> l \<notin> atyp k lo hi p \<and>
     (\<exists>v. \<not> G v \<and> (\<forall>i<k. i \<noteq> l \<longrightarrow> p i \<le> v i) \<and> p l - 1 \<le> v l
          \<and> (\<forall>i<k. i \<noteq> l \<longrightarrow> i \<notin> atyp k lo hi p \<longrightarrow> v i < hi \<longrightarrow> \<sigma> i < \<sigma> l))"

definition wfree :: "nat \<Rightarrow> ((nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat)
                       \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "wfree k G lo hi \<sigma> p = {l. l < k \<and> \<not> wdec k G lo hi \<sigma> p l}"

lemma atyp_sub: "atyp k lo hi u \<subseteq> {..<k}"
  by (auto simp: atyp_def)

lemma wtight_sub: "wtight k G lo hi u \<subseteq> {..<k}"
  by (auto simp: wtight_def)

subsection \<open>Decoding\<close>

lemma wdec_eq:
  assumes mono: "wmono k G" and p: "G p" and l: "l < k" and d: "wdec k G lo hi \<sigma> p l"
    and K: "\<forall>i<k. i \<noteq> l \<longrightarrow> i \<notin> K \<longrightarrow> i \<notin> atyp k lo hi p \<and> \<not> \<sigma> i < \<sigma> l"
  shows "p l = (LEAST x. G ((wfill K p hi)(l := x)))"
proof -
  obtain v where v: "\<not> G v" "\<forall>i<k. i \<noteq> l \<longrightarrow> p i \<le> v i" "p l - 1 \<le> v l"
      "\<forall>i<k. i \<noteq> l \<longrightarrow> i \<notin> atyp k lo hi p \<longrightarrow> v i < hi \<longrightarrow> \<sigma> i < \<sigma> l"
    using d by (auto simp: wdec_def)
  have up: "G ((wfill K p hi)(l := p l))"
  proof -
    have "\<forall>i<k. p i \<le> ((wfill K p hi)(l := p l)) i"
    proof (intro allI impI)
      fix i assume i: "i < k"
      show "p i \<le> ((wfill K p hi)(l := p l)) i"
      proof (cases "i = l \<or> i \<in> K")
        case True
        then show ?thesis by (auto simp: wfill_def)
      next
        case False
        then have "i \<notin> atyp k lo hi p" using K i by blast
        then have "p i \<le> hi" using i by (auto simp: atyp_def)
        then show ?thesis using False by (simp add: wfill_def)
      qed
    qed
    then show ?thesis using mono p unfolding wmono_def by blast
  qed
  have down: "\<not> G ((wfill K p hi)(l := x))" if x: "x < p l" for x
  proof
    assume g: "G ((wfill K p hi)(l := x))"
    have "\<forall>i<k. ((wfill K p hi)(l := x)) i \<le> v i"
    proof (intro allI impI)
      fix i assume i: "i < k"
      show "((wfill K p hi)(l := x)) i \<le> v i"
      proof (cases "i = l")
        case True
        have "x \<le> v l" using x v(3) by linarith
        then show ?thesis using True by simp
      next
        case False
        show ?thesis
        proof (cases "i \<in> K")
          case True
          then show ?thesis using False v(2) i by (simp add: wfill_def)
        next
          case nK: False
          have "i \<notin> atyp k lo hi p" "\<not> \<sigma> i < \<sigma> l" using K i False nK by blast+
          then have "\<not> v i < hi" using v(4) i False by blast
          then show ?thesis using False nK by (simp add: wfill_def)
        qed
      qed
    qed
    then have "G v" using mono g unfolding wmono_def by blast
    with v(1) show False ..
  qed
  have "(LEAST x. G ((wfill K p hi)(l := x))) = p l"
  proof (rule Least_equality)
    show "G ((wfill K p hi)(l := p l))" by (rule up)
  next
    fix y assume "G ((wfill K p hi)(l := y))"
    then show "p l \<le> y" using down not_less by blast
  qed
  then show ?thesis by simp
qed

lemma wfree_determined:
  assumes mono: "wmono k G" and p: "G p" and q: "G q"
    and box: "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" "q \<in> {..<k} \<rightarrow>\<^sub>E {..b}"
    and F: "wfree k G lo hi \<sigma> p = wfree k G lo hi \<sigma> q"
    and agree: "\<forall>l\<in>wfree k G lo hi \<sigma> p. p l = q l"
  shows "p = q"
proof -
  let ?F = "wfree k G lo hi \<sigma> p"
  have out: "p i = q i" if "\<not> i < k" for i
    using PiE_arb[OF box(1), of i] PiE_arb[OF box(2), of i] that by simp
  have all: "\<forall>l<k. \<sigma> l = m \<longrightarrow> p l = q l" for m
  proof (induction m rule: less_induct)
    case (less m)
    show ?case
    proof (intro allI impI)
      fix l assume l: "l < k" "\<sigma> l = m"
      show "p l = q l"
      proof (cases "l \<in> ?F")
        case True
        then show ?thesis using agree by blast
      next
        case False
        define K where "K = {i. i \<in> ?F \<or> \<sigma> i < \<sigma> l}"
        have nq: "l \<notin> wfree k G lo hi \<sigma> q" using False F by simp
        have dp: "wdec k G lo hi \<sigma> p l" using False l(1) by (simp add: wfree_def)
        have dq: "wdec k G lo hi \<sigma> q l" using nq l(1) by (simp add: wfree_def)
        have Kp: "\<forall>i<k. i \<noteq> l \<longrightarrow> i \<notin> K \<longrightarrow> i \<notin> atyp k lo hi p \<and> \<not> \<sigma> i < \<sigma> l"
        proof (intro allI impI)
          fix i assume i: "i < k" "i \<noteq> l" "i \<notin> K"
          then have "wdec k G lo hi \<sigma> p i" "\<not> \<sigma> i < \<sigma> l" by (auto simp: K_def wfree_def)
          then show "i \<notin> atyp k lo hi p \<and> \<not> \<sigma> i < \<sigma> l" by (simp add: wdec_def)
        qed
        have Kq: "\<forall>i<k. i \<noteq> l \<longrightarrow> i \<notin> K \<longrightarrow> i \<notin> atyp k lo hi q \<and> \<not> \<sigma> i < \<sigma> l"
        proof (intro allI impI)
          fix i assume i: "i < k" "i \<noteq> l" "i \<notin> K"
          then have "i \<notin> wfree k G lo hi \<sigma> q" "\<not> \<sigma> i < \<sigma> l" using F by (simp_all add: K_def)
          then have "wdec k G lo hi \<sigma> q i" "\<not> \<sigma> i < \<sigma> l" using i(1) by (simp_all add: wfree_def)
          then show "i \<notin> atyp k lo hi q \<and> \<not> \<sigma> i < \<sigma> l" by (simp add: wdec_def)
        qed
        have fill: "\<forall>i<k. wfill K p hi i = wfill K q hi i"
        proof (intro allI impI)
          fix i assume i: "i < k"
          show "wfill K p hi i = wfill K q hi i"
          proof (cases "i \<in> ?F")
            case True
            then show ?thesis using agree by (simp add: wfill_def K_def)
          next
            case nF: False
            show ?thesis
            proof (cases "\<sigma> i < \<sigma> l")
              case True
              then have "p i = q i" using less.IH[of "\<sigma> i"] i l(2) by blast
              then show ?thesis by (simp add: wfill_def)
            next
              case False
              then have "i \<notin> K" using nF by (simp add: K_def)
              then show ?thesis by (simp add: wfill_def)
            qed
          qed
        qed
        have eqG: "G ((wfill K p hi)(l := x)) = G ((wfill K q hi)(l := x))" for x
        proof -
          have "\<forall>i<k. ((wfill K p hi)(l := x)) i \<le> ((wfill K q hi)(l := x)) i"
            "\<forall>i<k. ((wfill K q hi)(l := x)) i \<le> ((wfill K p hi)(l := x)) i" using fill by auto
          then show ?thesis using mono unfolding wmono_def by blast
        qed
        have "p l = (LEAST x. G ((wfill K p hi)(l := x)))" by (rule wdec_eq[OF mono p l(1) dp Kp])
        also have "\<dots> = (LEAST x. G ((wfill K q hi)(l := x)))" using eqG by simp
        also have "\<dots> = q l" by (rule wdec_eq[OF mono q l(1) dq Kq, symmetric])
        finally show ?thesis .
      qed
    qed
  qed
  show "p = q"
  proof (rule ext)
    fix i
    show "p i = q i"
    proof (cases "i < k")
      case True
      then show ?thesis using all[of "\<sigma> i"] by blast
    next
      case False
      then show ?thesis by (rule out)
    qed
  qed
qed

subsection \<open>Maximal false witnesses and their cost\<close>

lemma max_false:
  assumes mono: "wmono k G" and u: "u \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and nu: "\<not> G u"
  obtains v where "v \<in> {..<k} \<rightarrow>\<^sub>E {..b}" "\<not> G v" "\<forall>i<k. u i \<le> v i"
    "\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i)))"
proof -
  define M where "M = {v \<in> {..<k} \<rightarrow>\<^sub>E {..b}. \<not> G v \<and> (\<forall>i<k. u i \<le> v i)}"
  define s where "s v = (\<Sum>i<k. v i)" for v :: "nat \<Rightarrow> nat"
  have M_sub: "M \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" by (auto simp: M_def)
  have finM: "finite M" by (rule finite_subset[OF M_sub]) (intro finite_PiE; simp)
  have uM: "u \<in> M" using u nu by (simp add: M_def)
  have ne: "s ` M \<noteq> {}" using uM by blast
  obtain v where vM: "v \<in> M" and vs: "s v = Max (s ` M)"
    using Max_in[OF finite_imageI[OF finM] ne] by auto
  have vmax: "s v' \<le> s v" if "v' \<in> M" for v'
    using vs Max_ge[OF finite_imageI[OF finM] imageI[OF that]] by simp
  have vb: "v \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and nv: "\<not> G v" and uv: "\<forall>i<k. u i \<le> v i"
    using vM by (simp_all add: M_def)
  have top: "G (v(i := Suc (v i)))" if i: "i < k" "v i < b" for i
  proof (rule ccontr)
    assume ng: "\<not> G (v(i := Suc (v i)))"
    have "v(i := Suc (v i)) \<in> {..<k} \<rightarrow>\<^sub>E {..b}" using vb i by (auto simp: PiE_iff extensional_def)
    moreover have "\<forall>j<k. u j \<le> (v(i := Suc (v i))) j" using uv by auto
    ultimately have "v(i := Suc (v i)) \<in> M" using ng by (simp add: M_def)
    then have le: "s (v(i := Suc (v i))) \<le> s v" by (rule vmax)
    have "s v < s (v(i := Suc (v i)))" unfolding s_def using i by (intro sum_strict_mono_ex1) auto
    with le show False by simp
  qed
  have top': "\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i)))" using top by blast
  show ?thesis by (rule that[OF vb nv uv top'])
qed

lemma wide_maxfalse:
  assumes mono: "wmono k G" and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and V: "V = (\<Union>i<k. blk i)"
    and nv: "\<not> G v" and vmax: "\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i)))"
    and X: "X \<subseteq> V" "bw blk k X = v"
  shows "maxfalse V (\<lambda>X. G (bw blk k X)) X"
proof -
  have vX: "v j = card (X \<inter> blk j)" if "j < k" for j
    using fun_cong[OF X(2), of j] that by (simp add: bw_def)
  have up: "G (bw blk k Y)" if Y: "X \<subset> Y" "Y \<subseteq> V" for Y
  proof -
    obtain y where y: "y \<in> Y" "y \<notin> X" using Y(1) by blast
    obtain i where i: "i < k" "y \<in> blk i" using y(1) Y(2) V by blast
    have fin: "finite (Y \<inter> blk j)" if "j < k" for j using blk that by simp
    have bY: "bw blk k Y j = card (Y \<inter> blk j)" if "j < k" for j using that by (simp add: bw_def)
    have ge: "v j \<le> bw blk k Y j" if j: "j < k" for j
    proof -
      have "card (X \<inter> blk j) \<le> card (Y \<inter> blk j)" using Y(1) fin[OF j] by (intro card_mono) auto
      then show ?thesis using vX[OF j] bY[OF j] by simp
    qed
    have "insert y (X \<inter> blk i) \<subseteq> Y \<inter> blk i" using y i Y(1) by blast
    then have "card (insert y (X \<inter> blk i)) \<le> card (Y \<inter> blk i)" using fin[OF i(1)] by (rule card_mono[rotated])
    moreover have "card (insert y (X \<inter> blk i)) = Suc (card (X \<inter> blk i))" using y(2) blk i(1) by simp
    ultimately have gi: "Suc (v i) \<le> bw blk k Y i" using vX[OF i(1)] bY[OF i(1)] by simp
    have "card (Y \<inter> blk i) \<le> card (blk i)" using blk i(1) by (intro card_mono) auto
    then have "bw blk k Y i \<le> b" using bY[OF i(1)] blk i(1) by simp
    then have "v i < b" using gi by linarith
    then have g: "G (v(i := Suc (v i)))" using vmax i(1) by blast
    have "\<forall>j<k. (v(i := Suc (v i))) j \<le> bw blk k Y j" using ge gi by auto
    then show ?thesis using mono g unfolding wmono_def by blast
  qed
  show ?thesis unfolding maxfalse_def using X nv up by auto
qed

text \<open>A maximal false weight vector \<open>v\<close> costs \<open>\<Prod> C(b, v i)\<close> clauses.\<close>

lemma wide_cost:
  assumes mono: "wmono k G" and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and v: "v \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and nv: "\<not> G v"
    and vmax: "\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i)))"
    and cs: "finite cs" "\<forall>X\<subseteq>V. G (bw blk k X) = cnf_val cs X"
  shows "(\<Prod>i<k. b choose v i) \<le> card cs"
proof -
  let ?C = "\<Pi>\<^sub>E i\<in>{..<k}. {T. T \<subseteq> blk i \<and> card T = v i}"
  let ?g = "\<lambda>T. \<Union>i<k. T i"
  let ?M = "{X. maxfalse V (\<lambda>X. G (bw blk k X)) X}"
  have Ti: "T i \<subseteq> blk i" "card (T i) = v i" if T: "T \<in> ?C" and i: "i < k" for T i
    using PiE_mem[OF T, of i] i by simp_all
  have cut: "?g T \<inter> blk j = T j" if T: "T \<in> ?C" and j: "j < k" for T j
  proof -
    have "T i \<inter> blk j = {}" if "i < k" "i \<noteq> j" for i using Ti(1)[OF T that(1)] disj that j by blast
    then show ?thesis using Ti(1)[OF T j] j by blast
  qed
  have inj: "inj_on ?g ?C"
  proof (rule inj_onI)
    fix T T' assume T: "T \<in> ?C" and T': "T' \<in> ?C" and eq: "?g T = ?g T'"
    show "T = T'"
    proof (rule PiE_ext[OF T T'])
      fix j assume j: "j \<in> {..<k}"
      show "T j = T' j" using cut[OF T, of j] cut[OF T', of j] eq j by simp
    qed
  qed
  have img: "?g ` ?C \<subseteq> ?M"
  proof
    fix X assume "X \<in> ?g ` ?C"
    then obtain T where T: "T \<in> ?C" and X: "X = ?g T" by blast
    have XV: "X \<subseteq> V" unfolding X V using Ti(1)[OF T] by blast
    have bwX: "bw blk k X = v"
    proof (rule ext)
      fix j
      show "bw blk k X j = v j"
      proof (cases "j < k")
        case True
        have "X \<inter> blk j = T j" using cut[OF T True] X by simp
        then show ?thesis using Ti(2)[OF T True] True by (simp add: bw_def)
      next
        case False
        then show ?thesis using PiE_arb[OF v, of j] by (simp add: bw_def)
      qed
    qed
    have "maxfalse V (\<lambda>X. G (bw blk k X)) X" by (rule wide_maxfalse[OF mono blk V nv vmax XV bwX])
    then show "X \<in> ?M" by simp
  qed
  have finV: "finite V" using blk V by simp
  have finM: "finite ?M" by (rule finite_subset[of _ "Pow V"]) (auto simp: maxfalse_def finV)
  have "(\<Prod>i<k. b choose v i) = (\<Prod>i<k. card {T. T \<subseteq> blk i \<and> card T = v i})"
    using blk by (intro prod.cong) (auto simp: n_subsets)
  also have "\<dots> = card ?C" by (simp add: card_PiE)
  also have "\<dots> = card (?g ` ?C)" using inj by (simp add: card_image)
  also have "\<dots> \<le> card ?M" using img finM by (rule card_mono[rotated])
  also have "\<dots> \<le> card cs" by (rule clause_per_maxfalse[OF cs])
  finally show ?thesis .
qed

subsection \<open>The counting theorem\<close>

text \<open>A tight coordinate is decoded under a \<open>(w-1)\<^sup>w\<^sup>-\<^sup>1 / w\<^sup>w\<close> fraction of the colourings.\<close>

lemma wide_good:
  fixes k :: nat and G :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  assumes mono: "wmono k G" and w: "1 \<le> w" and beta: "1 < \<beta>"
    and range: "\<forall>x. lo - 1 \<le> x \<longrightarrow> x < hi \<longrightarrow> \<beta> \<le> b choose x"
    and cost: "\<forall>v\<in>{..<k} \<rightarrow>\<^sub>E {..b}. \<not> G v \<longrightarrow> (\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i))))
                 \<longrightarrow> (\<Prod>i<k. b choose v i) < \<beta> ^ (w + 1)"
    and ub: "u \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and Gu: "G u" and l: "l \<in> wtight k G lo hi u"
    and C_def: "C = {..<k} \<rightarrow>\<^sub>E {..<w}"
  shows "w ^ k * (w - 1) ^ (w - 1) \<le> w ^ w * card {c \<in> C. l \<notin> wfree k G lo hi (cord k c) u}"
proof -
  define F where "F c = wfree k G lo hi (cord k c) u" for c
  have finC: "finite C" by (simp add: C_def finite_PiE)
  have lk: "l < k" and lt: "l \<notin> atyp k lo hi u" and nl: "\<not> G (u(l := u l - 1))"
    using l by (simp_all add: wtight_def)
  have tyl: "lo \<le> u l" "u l \<le> hi" using lt lk by (auto simp: atyp_def)
  have ul: "u l \<le> b" using PiE_mem[OF ub, of l] lk by simp
  have ul1: "u l - 1 \<le> b" using ul by linarith
  have ub': "u(l := u l - 1) \<in> {..<k} \<rightarrow>\<^sub>E {..b}" using ub lk ul1 by (auto simp: PiE_iff extensional_def)
  note mf = max_false[of k G "u(l := u l - 1)" b, OF mono ub' nl]
  obtain v where vb: "v \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and nv: "\<not> G v"
    and ge: "\<forall>i<k. (u(l := u l - 1)) i \<le> v i"
    and vmax: "\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i)))"
    by (rule mf)
  have vi: "u i \<le> v i" if "i < k" "i \<noteq> l" for i using ge[rule_format, OF that(1)] that(2) by simp
  have vl1: "u l - 1 \<le> v l" using ge[rule_format, OF lk] by simp
  have vl2: "v l < u l"
  proof (rule ccontr)
    assume nlt: "\<not> v l < u l"
    have "\<forall>i<k. u i \<le> v i"
    proof (intro allI impI)
      fix i assume "i < k"
      then show "u i \<le> v i" using vi nlt by (cases "i = l") auto
    qed
    then have "G v" using mono Gu unfolding wmono_def by blast
    with nv show False ..
  qed
  define f where "f i = b choose v i" for i
  define L where "L = {i. i < k \<and> i \<noteq> l \<and> i \<notin> atyp k lo hi u \<and> v i < hi}"
  have Lsub: "L \<subseteq> {..<k} - {l}" by (auto simp: L_def)
  have f1: "1 \<le> f i" if "i < k" for i
  proof -
    have "v i \<le> b" using PiE_mem[OF vb, of i] that by simp
    then have "0 < f i" by (simp add: f_def)
    then show ?thesis by simp
  qed
  have bl: "\<beta> \<le> f l"
  proof -
    have "lo - 1 \<le> v l" "v l < hi" using vl1 vl2 tyl by linarith+
    then show ?thesis using range by (simp add: f_def)
  qed
  have bL: "\<beta> \<le> f i" if "i \<in> L" for i
  proof -
    have i: "i < k" "i \<noteq> l" "i \<notin> atyp k lo hi u" "v i < hi" using that by (simp_all add: L_def)
    have "lo \<le> u i" using i(1,3) by (auto simp: atyp_def)
    moreover have "u i \<le> v i" using vi i(1,2) by blast
    ultimately have "lo - 1 \<le> v i" by linarith
    then show ?thesis using range i(4) by (simp add: f_def)
  qed
  have rest: "1 \<le> (\<Prod>i\<in>({..<k} - {l}) - L. f i)" by (rule prod_ge_1) (use f1 in auto)
  have pL: "\<beta> ^ card L \<le> (\<Prod>i\<in>L. f i)"
  proof -
    have "(\<Prod>i\<in>L. \<beta>) \<le> (\<Prod>i\<in>L. f i)" by (rule prod_mono) (use bL in auto)
    then show ?thesis by simp
  qed
  have "\<beta> ^ (card L + 1) = \<beta> * \<beta> ^ card L" by simp
  also have "\<dots> \<le> f l * (\<Prod>i\<in>L. f i)" using bl pL by (rule mult_le_mono)
  also have "\<dots> = f l * (\<Prod>i\<in>L. f i) * 1" by simp
  also have "\<dots> \<le> f l * (\<Prod>i\<in>L. f i) * (\<Prod>i\<in>({..<k} - {l}) - L. f i)" by (rule mult_le_mono2[OF rest])
  also have "\<dots> = f l * (\<Prod>i\<in>{..<k} - {l}. f i)"
    using prod.subset_diff[of L "{..<k} - {l}" f] Lsub by (simp add: mult_ac)
  also have "\<dots> = (\<Prod>i<k. f i)" using prod.remove[of "{..<k}" l f] lk by simp
  finally have pc: "\<beta> ^ (card L + 1) \<le> (\<Prod>i<k. b choose v i)" by (simp add: f_def)
  have "(\<Prod>i<k. b choose v i) < \<beta> ^ (w + 1)" using cost vb nv vmax by blast
  then have "\<beta> ^ (card L + 1) < \<beta> ^ (w + 1)" using pc by linarith
  then have "card L + 1 < w + 1" by (rule power_less_imp_less_exp[OF beta])
  then have cL: "card L \<le> w - 1" by linarith
  have sub: "{c \<in> C. \<forall>e\<in>L. c e < c l} \<subseteq> {c \<in> C. l \<notin> F c}"
  proof
    fix c assume c: "c \<in> {c \<in> C. \<forall>e\<in>L. c e < c l}"
    have ord: "\<forall>i<k. i \<noteq> l \<longrightarrow> i \<notin> atyp k lo hi u \<longrightarrow> v i < hi \<longrightarrow> cord k c i < cord k c l"
    proof (intro allI impI)
      fix i assume i: "i < k" "i \<noteq> l" "i \<notin> atyp k lo hi u" "v i < hi"
      then have "i \<in> L" by (simp add: L_def)
      then have "c i < c l" using c by blast
      then show "cord k c i < cord k c l" using i(1) by (rule cord_less)
    qed
    have vi': "\<forall>i<k. i \<noteq> l \<longrightarrow> u i \<le> v i" using vi by blast
    have "wdec k G lo hi (cord k c) u l" unfolding wdec_def using lt nv vi' vl1 ord by blast
    then have "l \<notin> F c" by (simp add: F_def wfree_def)
    then show "c \<in> {c \<in> C. l \<notin> F c}" using c by simp
  qed
  have fin: "finite {c \<in> C. l \<notin> F c}" using finC by simp
  have "w ^ k * (w - 1) ^ (w - 1) \<le> w ^ w * card {c \<in> C. \<forall>e\<in>L. c e < c l}"
    unfolding C_def by (rule good_colorings[OF lk Lsub cL w])
  also have "\<dots> \<le> w ^ w * card {c \<in> C. l \<notin> F c}"
    using sub fin by (intro mult_left_mono card_mono) simp_all
  finally show ?thesis by (simp add: F_def)
qed

theorem wide_compress:
  fixes k :: nat and blk :: "nat \<Rightarrow> 'a set" and G :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  assumes mono: "wmono k G" and w: "1 \<le> w" and beta: "1 < \<beta>"
    and range: "\<forall>x. lo - 1 \<le> x \<longrightarrow> x < hi \<longrightarrow> \<beta> \<le> b choose x"
    and cost: "\<forall>v\<in>{..<k} \<rightarrow>\<^sub>E {..b}. \<not> G v \<longrightarrow> (\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i))))
                 \<longrightarrow> (\<Prod>i<k. b choose v i) < \<beta> ^ (w + 1)"
    and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b" and V: "V = (\<Union>i<k. blk i)"
    and t: "t \<le> k"
  shows "card {X. X \<subseteq> V \<and> G (bw blk k X) \<and> t \<le> card (wtight k G lo hi (bw blk k X))}
           \<le> (w ^ k * 2 ^ k)
             * ((2 ^ b) ^ (k - t * (w - 1) ^ (w - 1) div w ^ w)
                * (b choose (b div 2)) ^ (t * (w - 1) ^ (w - 1) div w ^ w))"
proof -
  define y where "y = t * (w - 1) ^ (w - 1) div w ^ w"
  define m where "m = k - y"
  define C where "C = {..<k} \<rightarrow>\<^sub>E {..<w}"
  define U where "U = {u \<in> {..<k} \<rightarrow>\<^sub>E {..b}. G u \<and> t \<le> card (wtight k G lo hi u)}"
  define I where "I = C \<times> {F. F \<subseteq> {..<k} \<and> card F \<le> m}"
  define Cl where "Cl a = {u \<in> U. wfree k G lo hi (cord k (fst a)) u = snd a}"
    for a :: "(nat \<Rightarrow> nat) \<times> nat set"
  have Ppos: "0 < w ^ w" using w by simp
  have qP: "(w - 1) ^ (w - 1) \<le> w ^ w"
  proof -
    have "(w - 1) ^ (w - 1) \<le> w ^ (w - 1)" by (rule power_mono) simp_all
    also have "\<dots> \<le> w ^ w" using w by (intro power_increasing) simp_all
    finally show ?thesis .
  qed
  have yt: "y \<le> t"
  proof -
    have "y \<le> t * w ^ w div w ^ w" unfolding y_def using qP by (intro div_le_mono mult_left_mono) simp_all
    moreover have "t * w ^ w div w ^ w = t" using Ppos by (rule nonzero_mult_div_cancel_right[OF neq0_conv[THEN iffD2]])
    ultimately show ?thesis by simp
  qed
  have km: "k - m = y" using yt t by (simp add: m_def)
  have finV: "finite V" using blk by (simp add: V)
  have box: "U \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" by (auto simp: U_def)
  have finU: "finite U" using box by (rule finite_subset) (intro finite_PiE; simp)
  have finC: "finite C" by (simp add: C_def finite_PiE)
  have I_sub: "I \<subseteq> C \<times> Pow {..<k}" by (auto simp: I_def)
  have finI: "finite I" by (rule finite_subset[OF I_sub]) (simp add: finC)
  have cardI: "card I \<le> w ^ k * 2 ^ k"
  proof -
    have "card I \<le> card (C \<times> Pow {..<k})" using finC by (intro card_mono[OF _ I_sub]) simp
    also have "\<dots> = w ^ k * 2 ^ k" by (simp add: C_def card_cartesian_product card_Pow card_PiE)
    finally show ?thesis .
  qed
  have cover: "U \<subseteq> (\<Union>a\<in>I. Cl a)"
  proof
    fix u assume u: "u \<in> U"
    have tu: "t \<le> card (wtight k G lo hi u)" using u by (simp add: U_def)
    have ub: "u \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and Gu: "G u" using u by (simp_all add: U_def)
    define F where "F c = wfree k G lo hi (cord k c) u" for c
    have goodl: "\<forall>l\<in>wtight k G lo hi u. w ^ k * (w - 1) ^ (w - 1) \<le> w ^ w * card {c \<in> C. l \<notin> F c}"
      using wide_good[OF mono w beta range cost ub Gu _ C_def] by (simp add: F_def)
    have Fsub: "\<forall>c\<in>C. F c \<subseteq> {..<k}" by (auto simp: F_def wfree_def)
    obtain c where c: "c \<in> C" and cF: "card (F c) * w ^ w + t * (w - 1) ^ (w - 1) \<le> k * w ^ w"
      using average_free[OF C_def w Fsub wtight_sub tu goodl] by blast
    have "card (F c) \<le> m" unfolding m_def y_def by (rule free_bound[OF cF Ppos])
    then have "(c, F c) \<in> I" using c Fsub by (simp add: I_def)
    moreover have "u \<in> Cl (c, F c)" using u by (simp add: Cl_def F_def)
    ultimately show "u \<in> (\<Union>a\<in>I. Cl a)" by blast
  qed
  have sub: "\<forall>a\<in>I. Cl a \<subseteq> U" by (auto simp: Cl_def)
  have R: "\<forall>a\<in>I. snd a \<subseteq> {..<k} \<and> card (snd a) \<le> m" by (auto simp: I_def)
  have inj: "\<forall>a\<in>I. inj_on (\<lambda>p. restrict p (snd a)) (Cl a)"
  proof
    fix a assume "a \<in> I"
    show "inj_on (\<lambda>p. restrict p (snd a)) (Cl a)"
    proof (rule inj_onI)
      fix p q assume p: "p \<in> Cl a" and q: "q \<in> Cl a"
        and eq: "restrict p (snd a) = restrict q (snd a)"
      have pU: "p \<in> U" and qU: "q \<in> U" using p q by (auto simp: Cl_def)
      have Sp: "wfree k G lo hi (cord k (fst a)) p = snd a"
        and Sq: "wfree k G lo hi (cord k (fst a)) q = snd a" using p q by (simp_all add: Cl_def)
      have "\<forall>l\<in>snd a. p l = q l" using eq by (metis restrict_apply')
      then have ag: "\<forall>l\<in>wfree k G lo hi (cord k (fst a)) p. p l = q l" using Sp by simp
      have bp: "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and ap: "G p" using pU by (simp_all add: U_def)
      have bq: "q \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and aq: "G q" using qU by (simp_all add: U_def)
      show "p = q" by (rule wfree_determined[OF mono ap aq bp bq _ ag]) (simp add: Sp Sq)
    qed
  qed
  have W: "(\<Sum>u\<in>U. \<Prod>i<k. b choose u i)
             \<le> card I * ((2 ^ b) ^ m * (b choose (b div 2)) ^ (k - m))"
    by (rule classes_gen[OF box finI cover sub R _ inj]) (simp add: m_def)
  let ?S = "{X. X \<subseteq> V \<and> G (bw blk k X) \<and> t \<le> card (wtight k G lo hi (bw blk k X))}"
  have sub2: "?S \<subseteq> {X. X \<subseteq> V \<and> bw blk k X \<in> U}"
  proof
    fix X assume X: "X \<in> ?S"
    have "card (X \<inter> blk i) \<le> b" if "i < k" for i
      using blk that card_mono[of "blk i" "X \<inter> blk i"] by auto
    then have "bw blk k X \<in> {..<k} \<rightarrow>\<^sub>E {..b}" by (auto simp: bw_def)
    then show "X \<in> {X. X \<subseteq> V \<and> bw blk k X \<in> U}" using X by (simp add: U_def)
  qed
  have fin2: "finite {X. X \<subseteq> V \<and> bw blk k X \<in> U}"
    using finV by (auto intro: finite_subset[of _ "Pow V"])
  have "card ?S \<le> card {X. X \<subseteq> V \<and> bw blk k X \<in> U}" using sub2 fin2 by (rule card_mono[rotated])
  also have "\<dots> \<le> (\<Sum>u\<in>U. \<Prod>i<k. b choose u i)" by (rule inputs_count[OF blk V finU])
  also have "\<dots> \<le> card I * ((2 ^ b) ^ m * (b choose (b div 2)) ^ y)" using W by (simp add: km)
  also have "\<dots> \<le> (w ^ k * 2 ^ k) * ((2 ^ b) ^ m * (b choose (b div 2)) ^ y)"
    using cardI by (rule mult_right_mono) simp
  finally show ?thesis by (simp only: m_def y_def)
qed

subsection \<open>Sound tests given by a CNF\<close>

text \<open>
  A sound block-symmetric monotone CNF with fewer than \<open>\<beta>\<^sup>w\<^sup>+\<^sup>1\<close> clauses covers few slice
  inputs with at most \<open>a\<close> atypical blocks.  Every typical block of a covered slice input is
  tight, so \<open>t = k - a\<close>.
\<close>

lemma wide_cnf_cost:
  fixes k :: nat and blk :: "nat \<Rightarrow> 'a set" and G :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  assumes mono: "wmono k G" and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and cs: "finite cs" "\<forall>X\<subseteq>V. G (bw blk k X) = cnf_val cs X"
    and size: "card cs < \<beta> ^ (w + 1)"
  shows "\<forall>v\<in>{..<k} \<rightarrow>\<^sub>E {..b}. \<not> G v \<longrightarrow> (\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i))))
           \<longrightarrow> (\<Prod>i<k. b choose v i) < \<beta> ^ (w + 1)"
proof (intro ballI impI)
  fix v assume v: "v \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and nv: "\<not> G v"
    and vmax: "\<forall>i<k. v i < b \<longrightarrow> G (v(i := Suc (v i)))"
  have "(\<Prod>i<k. b choose v i) \<le> card cs" by (rule wide_cost[OF mono blk disj V v nv vmax cs])
  then show "(\<Prod>i<k. b choose v i) < \<beta> ^ (w + 1)" using size by linarith
qed

lemma wide_sound_tight:
  assumes sound: "\<forall>u. G u \<longrightarrow> N \<le> (\<Sum>i<k. u i)" and lo: "1 \<le> lo"
    and su: "(\<Sum>i<k. u i) = N" and ca: "card (atyp k lo hi u) \<le> a"
  shows "k - a \<le> card (wtight k G lo hi u)"
proof -
  have tsub: "{..<k} - atyp k lo hi u \<subseteq> wtight k G lo hi u"
  proof
    fix l assume l: "l \<in> {..<k} - atyp k lo hi u"
    then have lk: "l < k" and lt: "l \<notin> atyp k lo hi u" by simp_all
    have "lo \<le> u l" using lk lt by (auto simp: atyp_def)
    then have pos: "0 < u l" using lo by linarith
    have "(\<Sum>i<k. (u(l := u l - 1)) i) < (\<Sum>i<k. u i)" using lk pos by (intro sum_strict_mono_ex1) auto
    then have "\<not> G (u(l := u l - 1))" using sound su by fastforce
    then show "l \<in> wtight k G lo hi u" using lk lt by (simp add: wtight_def)
  qed
  have finA: "finite (atyp k lo hi u)" by (rule finite_subset[OF atyp_sub]) simp
  have finW: "finite (wtight k G lo hi u)" by (rule finite_subset[OF wtight_sub]) simp
  have "k - a \<le> k - card (atyp k lo hi u)" using ca by simp
  also have "\<dots> = card ({..<k} - atyp k lo hi u)" using finA atyp_sub by (simp add: card_Diff_subset)
  also have "\<dots> \<le> card (wtight k G lo hi u)" using tsub finW by (rule card_mono[rotated])
  finally show ?thesis .
qed

theorem wide_cover:
  fixes k :: nat and blk :: "nat \<Rightarrow> 'a set" and G :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  assumes mono: "wmono k G" and sound: "\<forall>u. G u \<longrightarrow> N \<le> (\<Sum>i<k. u i)"
    and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and cs: "finite cs" "\<forall>X\<subseteq>V. G (bw blk k X) = cnf_val cs X"
    and size: "card cs < \<beta> ^ (w + 1)" and w: "1 \<le> w" and beta: "1 < \<beta>"
    and lo: "1 \<le> lo" and range: "\<forall>x. lo - 1 \<le> x \<longrightarrow> x < hi \<longrightarrow> \<beta> \<le> b choose x"
    and a: "a \<le> k"
  shows "card {X. X \<subseteq> V \<and> G (bw blk k X) \<and> (\<Sum>i<k. bw blk k X i) = N
                  \<and> card (atyp k lo hi (bw blk k X)) \<le> a}
           \<le> (w ^ k * 2 ^ k)
             * ((2 ^ b) ^ (k - (k - a) * (w - 1) ^ (w - 1) div w ^ w)
                * (b choose (b div 2)) ^ ((k - a) * (w - 1) ^ (w - 1) div w ^ w))"
proof -
  note cost = wide_cnf_cost[OF mono blk disj V cs size]
  let ?S = "{X. X \<subseteq> V \<and> G (bw blk k X) \<and> (\<Sum>i<k. bw blk k X i) = N
                 \<and> card (atyp k lo hi (bw blk k X)) \<le> a}"
  let ?T = "{X. X \<subseteq> V \<and> G (bw blk k X) \<and> k - a \<le> card (wtight k G lo hi (bw blk k X))}"
  have sub: "?S \<subseteq> ?T"
  proof
    fix X assume X: "X \<in> ?S"
    have su: "(\<Sum>i<k. bw blk k X i) = N" and ca: "card (atyp k lo hi (bw blk k X)) \<le> a"
      using X by simp_all
    have "k - a \<le> card (wtight k G lo hi (bw blk k X))" by (rule wide_sound_tight[OF sound lo su ca])
    then show "X \<in> ?T" using X by simp
  qed
  have finV: "finite V" using blk by (simp add: V)
  have finT: "finite ?T" using finV by (auto intro: finite_subset[of _ "Pow V"])
  have "card ?S \<le> card ?T" using sub finT by (rule card_mono[rotated])
  also have "\<dots> \<le> (w ^ k * 2 ^ k)
             * ((2 ^ b) ^ (k - (k - a) * (w - 1) ^ (w - 1) div w ^ w)
                * (b choose (b div 2)) ^ ((k - a) * (w - 1) ^ (w - 1) div w ^ w))"
    by (rule wide_compress[OF mono w beta range cost blk V]) simp
  finally show ?thesis .
qed

end
