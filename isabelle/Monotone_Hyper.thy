theory Monotone_Hyper
  imports Monotone_Cost
begin

section \<open>Monotone tests with constraints on several blocks\<close>

text \<open>
  A test on \<open>k\<close> block weights is now an AND of monotone constraints \<open>G j\<close>, \<open>j \<in> J\<close>, each
  depending only on the weights of the blocks in its scope \<open>S j\<close>, a set of at most \<open>r\<close> blocks.
  Pairwise tests are the case \<open>r = 2\<close>; with blocks of size 1, the constraints are arbitrary
  monotone clauses of width \<open>r\<close>.

  As in \<open>Monotone_Mixed\<close>, a coordinate \<open>l\<close> of an accepted vector is \<^emph>\<open>tight\<close> if lowering it
  by one violates a constraint \<open>j\<close> (a witness); then \<open>u l\<close> is the least value that satisfies
  \<open>G j\<close> given the other coordinates of \<open>S j\<close>.  Decoding in any order recovers \<open>u l\<close> once
  some witness scope lies entirely before \<open>l\<close> (\<open>hfree_determined\<close>).

  Instead of averaging over all orders (and Jensen), we average over the \<open>r\<^sup>k\<close> colourings
  \<open>c : {..<k} \<rightarrow> {..<r}\<close>, ordering coordinates by colour and then by index.  A tight coordinate
  is decoded whenever its witness scope gets strictly smaller colours, which happens for at
  least \<open>(r-1)\<^sup>r\<^sup>-\<^sup>1 r\<^sup>k\<^sup>-\<^sup>r\<close> colourings (\<open>good_colorings\<close>).  So some colouring leaves at most
  \<open>k - t (r-1)\<^sup>r\<^sup>-\<^sup>1 / r\<^sup>r \<approx> k - t/(er)\<close> coordinates free (\<open>average_free\<close>), and the inputs with
  \<open>t\<close> tight coordinates are counted by \<open>hyper_compress\<close>.
\<close>

subsection \<open>Tests, tight coordinates, thresholds\<close>

definition hyper :: "'j set \<Rightarrow> ('j \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> ('j \<Rightarrow> nat set) \<Rightarrow> bool" where
  "hyper J G S \<longleftrightarrow> (\<forall>j\<in>J. \<forall>u v. (\<forall>i\<in>S j. u i = v i) \<longrightarrow> G j u = G j v)
                  \<and> (\<forall>j\<in>J. \<forall>u v. (\<forall>i. u i \<le> v i) \<longrightarrow> G j u \<longrightarrow> G j v)"

definition hacc :: "'j set \<Rightarrow> ('j \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "hacc J G u \<longleftrightarrow> (\<forall>j\<in>J. G j u)"

definition htw :: "'j set \<Rightarrow> ('j \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> ('j \<Rightarrow> nat set)
                    \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'j \<Rightarrow> bool" where
  "htw J G S u l j \<longleftrightarrow> j \<in> J \<and> l \<in> S j \<and> 0 < u l \<and> \<not> G j (u(l := u l - 1))"

definition htight :: "'j set \<Rightarrow> ('j \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> ('j \<Rightarrow> nat set)
                        \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "htight J G S k u = {l. l < k \<and> (\<exists>j. htw J G S u l j)}"

definition hth :: "('j \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> 'j \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "hth G j l u = (LEAST x. G j (u(l := x)))"

definition hfree :: "'j set \<Rightarrow> ('j \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> ('j \<Rightarrow> nat set)
                       \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "hfree J G S k \<sigma> u = {l. l < k \<and> \<not> (\<exists>j. htw J G S u l j \<and> (\<forall>i\<in>S j - {l}. \<sigma> i < \<sigma> l))}"

lemma hth_le:
  assumes "hacc J G u" "j \<in> J"
  shows "hth G j l u \<le> u l"
  unfolding hth_def by (rule Least_le) (use assms in \<open>simp add: hacc_def\<close>)

lemma hth_eq:
  assumes h: "hyper J G S" and u: "hacc J G u" and w: "htw J G S u l j"
  shows "u l = hth G j l u"
proof -
  have j: "j \<in> J" using w by (simp add: htw_def)
  have mono: "\<forall>u v. (\<forall>i. u i \<le> v i) \<longrightarrow> G j u \<longrightarrow> G j v" using h j by (simp add: hyper_def)
  have ex: "G j (u(l := u l))" using u j by (simp add: hacc_def)
  have Q: "G j (u(l := hth G j l u))"
    unfolding hth_def by (rule LeastI[of "\<lambda>x. G j (u(l := x))", OF ex])
  have le: "hth G j l u \<le> u l" by (rule hth_le[OF u j])
  show ?thesis
  proof (rule ccontr)
    assume "u l \<noteq> hth G j l u"
    then have lt: "hth G j l u \<le> u l - 1" using le by linarith
    have "\<forall>i. (u(l := hth G j l u)) i \<le> (u(l := u l - 1)) i" using lt by simp
    then have "G j (u(l := u l - 1))" using mono Q by blast
    then show False using w by (simp add: htw_def)
  qed
qed

lemma hth_local:
  assumes h: "hyper J G S" and j: "j \<in> J" and agree: "\<forall>i\<in>S j - {l}. u i = v i"
  shows "hth G j l u = hth G j l v"
proof -
  have loc: "\<forall>u v. (\<forall>i\<in>S j. u i = v i) \<longrightarrow> G j u = G j v" using h j by (simp add: hyper_def)
  have "G j (u(l := x)) = G j (v(l := x))" for x
  proof -
    have "\<forall>i\<in>S j. (u(l := x)) i = (v(l := x)) i" using agree by auto
    then show ?thesis using loc by blast
  qed
  then show ?thesis unfolding hth_def by simp
qed

lemma hyper_lower_nontight:
  assumes h: "hyper J G S" and u: "hacc J G u"
    and l: "l < k" "0 < u l" "l \<notin> htight J G S k u"
  shows "hacc J G (u(l := u l - 1))"
  unfolding hacc_def
proof
  fix j assume j: "j \<in> J"
  show "G j (u(l := u l - 1))"
  proof (cases "l \<in> S j")
    case True
    then show ?thesis using j l by (auto simp: htight_def htw_def)
  next
    case False
    have loc: "\<forall>u v. (\<forall>i\<in>S j. u i = v i) \<longrightarrow> G j u = G j v" using h j by (simp add: hyper_def)
    have "\<forall>i\<in>S j. u i = (u(l := u l - 1)) i" using False by auto
    then have "G j u = G j (u(l := u l - 1))" using loc by blast
    then show ?thesis using u j by (simp add: hacc_def)
  qed
qed

text \<open>For a sound test, every positive coordinate of a slice point is tight.\<close>

lemma hyper_sound_tight:
  assumes h: "hyper J G S" and sound: "\<forall>v. hacc J G v \<longrightarrow> N \<le> (\<Sum>i<k. v i)"
    and u: "hacc J G u" "(\<Sum>i<k. u i) = N" and l: "l < k" "0 < u l"
  shows "l \<in> htight J G S k u"
proof -
  define v where "v = u(l := u l - 1)"
  have "(\<Sum>i<k. v i) < (\<Sum>i<k. u i)" using l by (intro sum_strict_mono_ex1) (auto simp: v_def)
  then have "\<not> hacc J G v" using sound u(2) by fastforce
  then obtain j where j: "j \<in> J" "\<not> G j v" by (auto simp: hacc_def)
  have "l \<in> S j"
  proof (rule ccontr)
    assume "l \<notin> S j"
    then have ag: "\<forall>i\<in>S j. u i = v i" by (auto simp: v_def)
    have loc: "\<forall>u v. (\<forall>i\<in>S j. u i = v i) \<longrightarrow> G j u = G j v" using h j by (simp add: hyper_def)
    have "G j u = G j v" using loc ag by blast
    then show False using j u(1) by (simp add: hacc_def)
  qed
  then show ?thesis using j l by (auto simp: htight_def htw_def v_def)
qed

subsection \<open>Decoding in a fixed order\<close>

lemma hfree_determined:
  assumes h: "hyper J G S" and u: "hacc J G u" and v: "hacc J G v"
    and box: "u \<in> {..<k} \<rightarrow>\<^sub>E {..b}" "v \<in> {..<k} \<rightarrow>\<^sub>E {..b}"
    and F: "hfree J G S k \<sigma> u = hfree J G S k \<sigma> v" and agree: "\<forall>l\<in>hfree J G S k \<sigma> u. u l = v l"
  shows "u = v"
proof -
  have out: "u i = v i" if "\<not> i < k" for i
    using PiE_arb[OF box(1), of i] PiE_arb[OF box(2), of i] that by simp
  have earlier: "\<exists>j. htw J G S s l j \<and> (\<forall>i\<in>S j - {l}. \<sigma> i < \<sigma> l)"
    if s: "s = u \<or> s = v" and l: "l < k" "l \<notin> hfree J G S k \<sigma> u" for s l
  proof -
    have "l \<notin> hfree J G S k \<sigma> s" using s l F by auto
    then show ?thesis using l(1) by (simp add: hfree_def)
  qed
  have all: "\<forall>l<k. \<sigma> l = m \<longrightarrow> u l = v l" for m
  proof (induction m rule: less_induct)
    case (less m)
    show ?case
    proof (intro allI impI)
      fix l assume l: "l < k" "\<sigma> l = m"
      show "u l = v l"
      proof (cases "l \<in> hfree J G S k \<sigma> u")
        case True
        then show ?thesis using agree by blast
      next
        case False
        have ag: "\<forall>i\<in>S j - {l}. u i = v i" if j: "\<forall>i\<in>S j - {l}. \<sigma> i < \<sigma> l" for j
        proof
          fix i assume i: "i \<in> S j - {l}"
          show "u i = v i"
          proof (cases "i < k")
            case True
            then show ?thesis using less.IH[of "\<sigma> i"] j i l by auto
          next
            case False
            then show ?thesis by (rule out)
          qed
        qed
        obtain j where j: "htw J G S u l j" "\<forall>i\<in>S j - {l}. \<sigma> i < \<sigma> l"
          using earlier[of u l] l False by blast
        obtain j' where j': "htw J G S v l j'" "\<forall>i\<in>S j' - {l}. \<sigma> i < \<sigma> l"
          using earlier[of v l] l False by blast
        have jJ: "j \<in> J" "j' \<in> J" using j(1) j'(1) by (simp_all add: htw_def)
        have "u l = hth G j l u" by (rule hth_eq[OF h u j(1)])
        also have "\<dots> = hth G j l v" by (rule hth_local[OF h jJ(1) ag[OF j(2)]])
        also have "\<dots> \<le> v l" by (rule hth_le[OF v jJ(1)])
        finally have le1: "u l \<le> v l" .
        have "v l = hth G j' l v" by (rule hth_eq[OF h v j'(1)])
        also have "\<dots> = hth G j' l u" using hth_local[OF h jJ(2) ag[OF j'(2)]] by simp
        also have "\<dots> \<le> u l" by (rule hth_le[OF u jJ(2)])
        finally have "v l \<le> u l" .
        with le1 show ?thesis by simp
      qed
    qed
  qed
  show "u = v"
  proof (rule ext)
    fix i
    show "u i = v i"
    proof (cases "i < k")
      case True
      then show ?thesis using all[of "\<sigma> i"] by blast
    next
      case False
      then show ?thesis by (rule out)
    qed
  qed
qed

subsection \<open>Averaging over colourings\<close>

definition cord :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "cord k c i = c i * k + i"

lemma cord_less:
  assumes "c e < c l" "e < k"
  shows "cord k c e < cord k c l"
proof -
  have "(c e + 1) * k \<le> c l * k" using assms(1) by (intro mult_right_mono) simp_all
  then have "c e * k + k \<le> c l * k" by (simp add: algebra_simps)
  then show ?thesis using assms(2) unfolding cord_def by linarith
qed

text \<open>
  Colourings that give \<open>l\<close> the top colour \<open>r - 1\<close> and \<open>E\<close> colours below it form a product set
  of size \<open>(r-1)\<^sup>|\<^sup>E\<^sup>| r\<^sup>k\<^sup>-\<^sup>1\<^sup>-\<^sup>|\<^sup>E\<^sup>|\<close>.
\<close>

lemma good_colorings:
  assumes l: "l < k" and E: "E \<subseteq> {..<k} - {l}" "card E \<le> r - 1" and r: "1 \<le> r"
  shows "r ^ k * (r - 1) ^ (r - 1) \<le> r ^ r * card {c \<in> {..<k} \<rightarrow>\<^sub>E {..<r}. \<forall>e\<in>E. c e < c l}"
proof -
  define g where "g i = (if i = l then {r - 1} else if i \<in> E then {..<r - 1} else {..<r})" for i
  define D where "D = (\<Pi>\<^sub>E i\<in>{..<k}. g i)"
  let ?good = "{c \<in> {..<k} \<rightarrow>\<^sub>E {..<r}. \<forall>e\<in>E. c e < c l}"
  have gsub: "g i \<subseteq> {..<r}" for i using r by (auto simp: g_def)
  have DC: "D \<subseteq> ?good"
  proof
    fix c assume c: "c \<in> D"
    have ci: "c i \<in> g i" if "i < k" for i using PiE_mem[of c "{..<k}" g i] c that by (simp add: D_def)
    have "D \<subseteq> {..<k} \<rightarrow>\<^sub>E {..<r}" unfolding D_def using gsub by (intro PiE_mono) blast
    then have "c \<in> {..<k} \<rightarrow>\<^sub>E {..<r}" using c by blast
    moreover have "c e < c l" if "e \<in> E" for e
    proof -
      have "e < k" "e \<noteq> l" using E(1) that by auto
      then have "c e \<in> {..<r - 1}" using ci[of e] that by (simp add: g_def)
      moreover have "c l = r - 1" using ci[OF l] by (simp add: g_def)
      ultimately show ?thesis by simp
    qed
    ultimately show "c \<in> ?good" by blast
  qed
  have finG: "finite ?good" by (rule finite_subset[of _ "{..<k} \<rightarrow>\<^sub>E {..<r}"]) (auto intro: finite_PiE)
  have cE: "card E \<le> k - 1"
  proof -
    have "card E \<le> card ({..<k} - {l})" using E(1) by (intro card_mono) simp_all
    then show ?thesis using l by simp
  qed
  have p1: "card D = (\<Prod>i<k. card (g i))" by (simp add: D_def card_PiE)
  also have "\<dots> = card (g l) * (\<Prod>i\<in>{..<k} - {l}. card (g i))" using l by (intro prod.remove) simp_all
  also have "(\<Prod>i\<in>{..<k} - {l}. card (g i)) = (\<Prod>i\<in>{..<k} - {l}. if i \<in> E then r - 1 else r)"
    by (rule prod.cong) (auto simp: g_def)
  also have "\<dots> = (\<Prod>i\<in>({..<k} - {l}) \<inter> {i. i \<in> E}. r - 1) * (\<Prod>i\<in>({..<k} - {l}) \<inter> - {i. i \<in> E}. r)"
    by (rule prod.If_cases) simp
  also have "({..<k} - {l}) \<inter> {i. i \<in> E} = E" using E(1) by blast
  also have "({..<k} - {l}) \<inter> - {i. i \<in> E} = ({..<k} - {l}) - E" by blast
  also have "card (g l) = 1" by (simp add: g_def)
  finally have cD: "card D = (r - 1) ^ card E * r ^ card (({..<k} - {l}) - E)" by simp
  have c2: "card (({..<k} - {l}) - E) = k - 1 - card E"
    using E(1) l by (simp add: card_Diff_subset finite_subset)
  obtain d where d: "r - 1 = card E + d" using E(2) le_iff_add by blast
  obtain f where f: "k - 1 = card E + f" using cE le_iff_add by blast
  have kf: "k = Suc (card E + f)" using l f by simp
  have rd: "r = Suc (card E + d)" using r d by simp
  have e1: "r ^ k = r * r ^ card E * r ^ f" using kf by (simp add: power_add)
  have e2: "(r - 1) ^ (r - 1) = (r - 1) ^ card E * (r - 1) ^ d" using d by (simp add: power_add)
  have e3: "r ^ r = r * r ^ card E * r ^ d"
  proof -
    have "r ^ r = r ^ Suc (card E + d)" using rd by simp
    then show ?thesis by (simp add: power_add)
  qed
  have e4: "k - 1 - card E = f" using f by simp
  have qd: "(r - 1) ^ d \<le> r ^ d" by (rule power_mono) simp_all
  have "r ^ k * (r - 1) ^ (r - 1) = (r * r ^ card E * r ^ f * (r - 1) ^ card E) * (r - 1) ^ d"
    unfolding e1 e2 by (simp add: mult_ac)
  also have "\<dots> \<le> (r * r ^ card E * r ^ f * (r - 1) ^ card E) * r ^ d" using qd by (rule mult_left_mono) simp
  also have "\<dots> = r ^ r * card D" unfolding cD c2 e4 e3 by (simp add: mult_ac)
  also have "\<dots> \<le> r ^ r * card ?good" using DC finG by (intro mult_left_mono card_mono) simp_all
  finally show ?thesis .
qed

text \<open>
  If each tight coordinate is decoded for many colourings, some colouring leaves few free
  coordinates.  Stated without division: \<open>|F c| r\<^sup>r + t (r-1)\<^sup>r\<^sup>-\<^sup>1 \<le> k r\<^sup>r\<close>.
\<close>

lemma average_free:
  fixes F :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set"
  assumes C: "C = {..<k} \<rightarrow>\<^sub>E {..<r}" and r: "1 \<le> r"
    and Fsub: "\<forall>c\<in>C. F c \<subseteq> {..<k}" and T: "T \<subseteq> {..<k}" "t \<le> card T"
    and good: "\<forall>l\<in>T. r ^ k * (r - 1) ^ (r - 1) \<le> r ^ r * card {c \<in> C. l \<notin> F c}"
  shows "\<exists>c\<in>C. card (F c) * r ^ r + t * (r - 1) ^ (r - 1) \<le> k * r ^ r"
proof (rule ccontr)
  assume neg: "\<not> ?thesis"
  define P where "P = r ^ r"
  define q where "q = (r - 1) ^ (r - 1)"
  define R where "R = card C"
  define S where "S = (\<Sum>c\<in>C. card (F c))"
  have cC: "R = r ^ k" by (simp add: R_def C card_PiE)
  have Rpos: "0 < R" using cC r by simp
  have finC: "finite C" by (simp add: C finite_PiE)
  have each: "card {c \<in> C. l \<in> F c} * P + (if l \<in> T then R * q else 0) \<le> R * P" for l
  proof -
    have split: "card {c \<in> C. l \<in> F c} + card {c \<in> C. l \<notin> F c} = R"
    proof -
      have "{c \<in> C. l \<in> F c} \<union> {c \<in> C. l \<notin> F c} = C" by blast
      moreover have "{c \<in> C. l \<in> F c} \<inter> {c \<in> C. l \<notin> F c} = {}" by blast
      ultimately show ?thesis
        using finC card_Un_disjoint[of "{c \<in> C. l \<in> F c}" "{c \<in> C. l \<notin> F c}"] by (simp add: R_def)
    qed
    show ?thesis
    proof (cases "l \<in> T")
      case True
      have "R * q \<le> P * card {c \<in> C. l \<notin> F c}" using good True cC by (simp add: P_def q_def)
      then have "card {c \<in> C. l \<in> F c} * P + R * q
                   \<le> card {c \<in> C. l \<in> F c} * P + card {c \<in> C. l \<notin> F c} * P" by (simp add: mult.commute)
      also have "\<dots> = R * P" by (simp add: split[symmetric] add_mult_distrib)
      finally show ?thesis using True by simp
    next
      case False
      have "card {c \<in> C. l \<in> F c} \<le> R" using split by linarith
      then show ?thesis using False by (simp add: mult_right_mono)
    qed
  qed
  have dbl: "S = (\<Sum>l<k. card {c \<in> C. l \<in> F c})"
  proof -
    have "S = (\<Sum>c\<in>C. \<Sum>l<k. if l \<in> F c then 1 else 0)"
      unfolding S_def
    proof (rule sum.cong[OF refl])
      fix c assume c: "c \<in> C"
      have "(\<Sum>l<k. if l \<in> F c then 1 else 0) = (\<Sum>l\<in>{..<k} \<inter> F c. 1::nat)"
        by (rule sum.inter_restrict[symmetric]) simp
      also have "\<dots> = card (F c)" using Fsub c by (simp add: Int_absorb1)
      finally show "card (F c) = (\<Sum>l<k. if l \<in> F c then 1 else 0)" by simp
    qed
    also have "\<dots> = (\<Sum>l<k. \<Sum>c\<in>C. if l \<in> F c then 1 else 0)" by (rule sum.swap)
    also have "\<dots> = (\<Sum>l<k. card {c \<in> C. l \<in> F c})"
    proof (rule sum.cong[OF refl])
      fix l
      have "(\<Sum>c\<in>C \<inter> {c. l \<in> F c}. 1::nat) = (\<Sum>c\<in>C. if c \<in> {c. l \<in> F c} then 1 else 0)"
        by (rule sum.inter_restrict[OF finC])
      moreover have "C \<inter> {c. l \<in> F c} = {c \<in> C. l \<in> F c}" by blast
      ultimately show "(\<Sum>c\<in>C. if l \<in> F c then 1 else 0) = card {c \<in> C. l \<in> F c}" by simp
    qed
    finally show ?thesis .
  qed
  have sumT: "(\<Sum>l<k. if l \<in> T then R * q else 0) = card T * (R * q)"
  proof -
    have "(\<Sum>l<k. if l \<in> T then R * q else 0) = (\<Sum>l\<in>{..<k} \<inter> T. R * q)"
      by (rule sum.inter_restrict[symmetric]) simp
    also have "{..<k} \<inter> T = T" using T(1) by blast
    finally show ?thesis by simp
  qed
  have H1: "S * P + card T * (R * q) \<le> k * (R * P)"
  proof -
    have "(\<Sum>l<k. card {c \<in> C. l \<in> F c} * P + (if l \<in> T then R * q else 0)) \<le> (\<Sum>l<k. R * P)"
      using each by (intro sum_mono) blast
    moreover have "(\<Sum>l<k. card {c \<in> C. l \<in> F c} * P + (if l \<in> T then R * q else 0))
                     = S * P + card T * (R * q)"
      by (simp add: sum.distrib sum_distrib_right dbl sumT)
    ultimately show ?thesis by simp
  qed
  have H2: "R * (k * P) + R \<le> S * P + R * (t * q)"
  proof -
    have "\<forall>c\<in>C. k * P + 1 \<le> card (F c) * P + t * q" using neg by (auto simp: P_def q_def not_le)
    then have "(\<Sum>c\<in>C. k * P + 1) \<le> (\<Sum>c\<in>C. card (F c) * P + t * q)" by (intro sum_mono) blast
    then show ?thesis
      by (simp add: S_def R_def sum.distrib sum_distrib_right sum_distrib_left algebra_simps)
  qed
  have a1: "R * (t * q) = t * (R * q)" by (simp add: mult_ac)
  have a2: "t * (R * q) \<le> card T * (R * q)" using T(2) by (rule mult_right_mono) simp
  have a3: "k * (R * P) = R * (k * P)" by (simp add: mult_ac)
  show False using H1 H2 a1 a2 a3 Rpos by linarith
qed

lemma free_bound:
  assumes "x * P + y \<le> k * P" "0 < (P :: nat)"
  shows "x \<le> k - y div P"
proof -
  have "y div P * P \<le> y" using div_mult_mod_eq[of y P] by linarith
  then have "x * P + y div P * P \<le> k * P" using assms(1) by linarith
  then have "(x + y div P) * P \<le> k * P" by (simp add: add_mult_distrib)
  then have "x + y div P \<le> k" using assms(2) by simp
  then show ?thesis by simp
qed

subsection \<open>The counting theorem\<close>

theorem hyper_compress:
  fixes k :: nat and blk :: "nat \<Rightarrow> 'a set" and S :: "'j \<Rightarrow> nat set"
  assumes h: "hyper J G S" and sc: "\<forall>j\<in>J. S j \<subseteq> {..<k} \<and> card (S j) \<le> r" and r: "1 \<le> r"
    and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b" and V: "V = (\<Union>i<k. blk i)"
    and t: "t \<le> k"
  shows "card {X. X \<subseteq> V \<and> hacc J G (bw blk k X) \<and> t \<le> card (htight J G S k (bw blk k X))}
           \<le> (r ^ k * 2 ^ k)
             * ((2 ^ b) ^ (k - t * (r - 1) ^ (r - 1) div r ^ r)
                * (b choose (b div 2)) ^ (t * (r - 1) ^ (r - 1) div r ^ r))"
proof -
  define y where "y = t * (r - 1) ^ (r - 1) div r ^ r"
  define m where "m = k - y"
  define C where "C = {..<k} \<rightarrow>\<^sub>E {..<r}"
  define U where "U = {u \<in> {..<k} \<rightarrow>\<^sub>E {..b}. hacc J G u \<and> t \<le> card (htight J G S k u)}"
  define I where "I = C \<times> {F. F \<subseteq> {..<k} \<and> card F \<le> m}"
  define Cl where "Cl a = {u \<in> U. hfree J G S k (cord k (fst a)) u = snd a}"
    for a :: "(nat \<Rightarrow> nat) \<times> nat set"
  have Ppos: "0 < r ^ r" using r by simp
  have qP: "(r - 1) ^ (r - 1) \<le> r ^ r"
  proof -
    have "(r - 1) ^ (r - 1) \<le> r ^ (r - 1)" by (rule power_mono) simp_all
    also have "\<dots> \<le> r ^ r" using r by (intro power_increasing) simp_all
    finally show ?thesis .
  qed
  have yt: "y \<le> t"
  proof -
    have "y \<le> t * r ^ r div r ^ r" unfolding y_def using qP by (intro div_le_mono mult_left_mono) simp_all
    moreover have "t * r ^ r div r ^ r = t" using Ppos by (rule nonzero_mult_div_cancel_right[OF neq0_conv[THEN iffD2]])
    ultimately show ?thesis by simp
  qed
  have km: "k - m = y" using yt t by (simp add: m_def)
  have finV: "finite V" using blk by (simp add: V)
  have box: "U \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" by (auto simp: U_def)
  have finU: "finite U" using box by (rule finite_subset) (intro finite_PiE; simp)
  have finC: "finite C" by (simp add: C_def finite_PiE)
  have I_sub: "I \<subseteq> C \<times> Pow {..<k}" by (auto simp: I_def)
  have finI: "finite I" by (rule finite_subset[OF I_sub]) (simp add: finC)
  have cardI: "card I \<le> r ^ k * 2 ^ k"
  proof -
    have "card I \<le> card (C \<times> Pow {..<k})" using finC by (intro card_mono[OF _ I_sub]) simp
    also have "\<dots> = r ^ k * 2 ^ k" by (simp add: C_def card_cartesian_product card_Pow card_PiE)
    finally show ?thesis .
  qed
  have cover: "U \<subseteq> (\<Union>a\<in>I. Cl a)"
  proof
    fix u assume u: "u \<in> U"
    have tu: "t \<le> card (htight J G S k u)" using u by (simp add: U_def)
    define F where "F c = hfree J G S k (cord k c) u" for c
    have goodl: "\<forall>l\<in>htight J G S k u. r ^ k * (r - 1) ^ (r - 1) \<le> r ^ r * card {c \<in> C. l \<notin> F c}"
    proof
      fix l assume l: "l \<in> htight J G S k u"
      then obtain j where lk: "l < k" and w: "htw J G S u l j" by (auto simp: htight_def)
      have j: "j \<in> J" "l \<in> S j" using w by (simp_all add: htw_def)
      have Sk: "S j \<subseteq> {..<k}" and Sr: "card (S j) \<le> r" using sc j(1) by auto
      have finS: "finite (S j)" using Sk by (rule finite_subset) simp
      have Ek: "S j - {l} \<subseteq> {..<k} - {l}" using Sk by blast
      have cE: "card (S j - {l}) \<le> r - 1" using Sr j(2) finS by simp
      have sub: "{c \<in> C. \<forall>e\<in>S j - {l}. c e < c l} \<subseteq> {c \<in> C. l \<notin> F c}"
      proof
        fix c assume c: "c \<in> {c \<in> C. \<forall>e\<in>S j - {l}. c e < c l}"
        have "\<forall>i\<in>S j - {l}. cord k c i < cord k c l"
        proof
          fix i assume i: "i \<in> S j - {l}"
          then have "c i < c l" "i < k" using c Sk by auto
          then show "cord k c i < cord k c l" by (rule cord_less)
        qed
        then have "l \<notin> F c" using w by (auto simp: F_def hfree_def)
        then show "c \<in> {c \<in> C. l \<notin> F c}" using c by simp
      qed
      have fin: "finite {c \<in> C. l \<notin> F c}" using finC by simp
      have "r ^ k * (r - 1) ^ (r - 1) \<le> r ^ r * card {c \<in> C. \<forall>e\<in>S j - {l}. c e < c l}"
        unfolding C_def by (rule good_colorings[OF lk Ek cE r])
      also have "\<dots> \<le> r ^ r * card {c \<in> C. l \<notin> F c}"
        using sub fin by (intro mult_left_mono card_mono) simp_all
      finally show "r ^ k * (r - 1) ^ (r - 1) \<le> r ^ r * card {c \<in> C. l \<notin> F c}" .
    qed
    have Fsub: "\<forall>c\<in>C. F c \<subseteq> {..<k}" by (auto simp: F_def hfree_def)
    have Tk: "htight J G S k u \<subseteq> {..<k}" by (auto simp: htight_def)
    obtain c where c: "c \<in> C" and cF: "card (F c) * r ^ r + t * (r - 1) ^ (r - 1) \<le> k * r ^ r"
      using average_free[OF C_def r Fsub Tk tu goodl] by blast
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
      have Sp: "hfree J G S k (cord k (fst a)) p = snd a"
        and Sq: "hfree J G S k (cord k (fst a)) q = snd a" using p q by (simp_all add: Cl_def)
      have "\<forall>l\<in>snd a. p l = q l" using eq by (metis restrict_apply')
      then have ag: "\<forall>l\<in>hfree J G S k (cord k (fst a)) p. p l = q l" using Sp by simp
      have bp: "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and ap: "hacc J G p" using pU by (simp_all add: U_def)
      have bq: "q \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and aq: "hacc J G q" using qU by (simp_all add: U_def)
      show "p = q" by (rule hfree_determined[OF h ap aq bp bq _ ag]) (simp add: Sp Sq)
    qed
  qed
  have W: "(\<Sum>u\<in>U. \<Prod>i<k. b choose u i)
             \<le> card I * ((2 ^ b) ^ m * (b choose (b div 2)) ^ (k - m))"
    by (rule classes_gen[OF box finI cover sub R _ inj]) (simp add: m_def)
  let ?S = "{X. X \<subseteq> V \<and> hacc J G (bw blk k X) \<and> t \<le> card (htight J G S k (bw blk k X))}"
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
  also have "\<dots> \<le> (r ^ k * 2 ^ k) * ((2 ^ b) ^ m * (b choose (b div 2)) ^ y)"
    using cardI by (rule mult_right_mono) simp
  finally show ?thesis by (simp only: m_def y_def)
qed

end
