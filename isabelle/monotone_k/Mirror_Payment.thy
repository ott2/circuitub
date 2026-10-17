theory Mirror_Payment
  imports Deep_Payment
begin

section \<open>Mirror payments: deficient blocks that do occur\<close>

text \<open>
  Blocks \<open>B\<^sub>i = {i} \<times> {..<2k-2}\<close> as in \<open>Deep_Payment\<close>, with the special vertex \<open>r\<^sub>i = (i, 2k-3)\<close>
  and \<open>R\<^sub>i = {i} \<times> {..<2k-3}\<close>. The inside edges are the \<open>k\<close>-subsets of \<open>B\<^sub>i\<close> containing \<open>r\<^sub>i\<close>; the
  payments are \<open>A \<union> {(nxt i, j)}\<close> for a \<open>(k-1)\<close>-subset \<open>A\<close> of \<open>R\<^sub>i\<close> and \<open>(i, j) \<in> A\<close>.
  A block missing \<open>C\<close> with \<open>|C| \<ge> k\<close> forces the mirror image of \<open>C\<close> into the next block
  (\<open>mp_forces\<close>), so \<open>\<tau> = N(k-1)\<close> (\<open>mp_tau\<close>). Unlike deep payments, every deficiency level
  occurs in a minimum transversal (\<open>mp_deficient\<close>), so the trace on one block has at least
  \<open>2^(2k-4)\<close> patterns (\<open>mp_trace\<close>). The normal choices give \<open>C(2k-3, k-1)^N\<close> minimum
  transversals (\<open>mp_count\<close>).
\<close>

definition mp :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set set" where
  "mp N k = {e. \<exists>i<N. e \<subseteq> blk k i \<and> card e = k \<and> (i, 2*k-3) \<in> e}
     \<union> {insert (nxt N i, j) A | i A j. i < N \<and> A \<subseteq> {i} \<times> {..<2*k-3} \<and> card A = k - 1 \<and> (i, j) \<in> A}"

subsection \<open>A deficient block forces its mirror image\<close>

lemma mp_forces:
  assumes k: "2 \<le> k" and i: "i < N" and tr: "tr (mp N k) X"
    and small: "card (X \<inter> blk k i) < k - 1" and c: "(i, j) \<in> blk k i - X"
  shows "(nxt N i, j) \<in> X"
proof -
  define C where "C = blk k i - X"
  have fC: "finite C" by (simp add: C_def)
  have "card C = card (blk k i) - card (blk k i \<inter> X)"
    unfolding C_def by (rule card_Diff_subset_Int) simp
  also have "card (blk k i \<inter> X) = card (X \<inter> blk k i)" by (simp add: Int_commute)
  finally have cardC: "k \<le> card C" using small k by simp
  have rC: "(i, 2*k-3) \<notin> C"
  proof
    assume r: "(i, 2*k-3) \<in> C"
    have "k - 1 \<le> card (C - {(i, 2*k-3)})" using cardC r fC by simp
    then obtain T where T: "T \<subseteq> C - {(i, 2*k-3)}" "card T = k - 1"
      using obtain_subset_with_card_n by metis
    have fT: "finite T" using T(1) fC by (meson finite_Diff finite_subset)
    have rT: "(i, 2*k-3) \<notin> T" using T(1) by blast
    have ce: "card (insert (i, 2*k-3) T) = k" using T(2) fT rT k by simp
    have "insert (i, 2*k-3) T \<subseteq> blk k i" using T(1) r by (auto simp: C_def)
    then have "insert (i, 2*k-3) T \<in> mp N k" using i ce unfolding mp_def by blast
    then have "insert (i, 2*k-3) T \<inter> X \<noteq> {}" using tr unfolding tr_def by blast
    moreover have "insert (i, 2*k-3) T \<inter> X = {}" using T(1) r by (auto simp: C_def)
    ultimately show False by blast
  qed
  have CR: "C \<subseteq> {i} \<times> {..<2*k-3}"
  proof
    fix x assume x: "x \<in> C"
    then obtain l where xl: "x = (i, l)" and l: "l < 2*k-2" by (auto simp: C_def blk_def)
    have "l \<noteq> 2*k-3" using rC x xl by blast
    then show "x \<in> {i} \<times> {..<2*k-3}" using xl l by auto
  qed
  have cC: "(i, j) \<in> C" using c by (simp add: C_def)
  have "k - 2 \<le> card (C - {(i, j)})" using cardC cC fC by simp
  then obtain T where T: "T \<subseteq> C - {(i, j)}" "card T = k - 2"
    using obtain_subset_with_card_n by metis
  have fT: "finite T" using T(1) fC by (meson finite_Diff finite_subset)
  have jT: "(i, j) \<notin> T" using T(1) by blast
  define A where "A = insert (i, j) T"
  have cA: "card A = k - 1" unfolding A_def using T(2) fT jT k by simp
  have AC: "A \<subseteq> C" unfolding A_def using T(1) cC by blast
  have AR: "A \<subseteq> {i} \<times> {..<2*k-3}" using AC CR by blast
  have AX: "A \<inter> X = {}" using AC by (auto simp: C_def)
  have jA: "(i, j) \<in> A" unfolding A_def by simp
  have "insert (nxt N i, j) A \<in> mp N k" unfolding mp_def using i AR cA jA by blast
  then have "insert (nxt N i, j) A \<inter> X \<noteq> {}" using tr unfolding tr_def by blast
  then show ?thesis using AX by blast
qed

lemma mp_mirror:
  assumes k: "2 \<le> k" and i: "i < N" and N: "0 < N" and tr: "tr (mp N k) X"
    and small: "card (X \<inter> blk k i) < k - 1"
  shows "2*k-2 - card (X \<inter> blk k i) \<le> card (X \<inter> blk k (nxt N i))"
proof -
  define C where "C = blk k i - X"
  have "card C = card (blk k i) - card (blk k i \<inter> X)"
    unfolding C_def by (rule card_Diff_subset_Int) simp
  also have "card (blk k i \<inter> X) = card (X \<inter> blk k i)" by (simp add: Int_commute)
  finally have cardC: "card C = 2*k-2 - card (X \<inter> blk k i)" by simp
  define m where "m x = (nxt N i, snd x)" for x :: "nat \<times> nat"
  have inj: "inj_on m C" by (rule inj_onI) (auto simp: m_def C_def blk_def)
  have sub: "m ` C \<subseteq> X \<inter> blk k (nxt N i)"
  proof
    fix y assume "y \<in> m ` C"
    then obtain x where x: "x \<in> C" and y: "y = m x" by blast
    obtain j where xj: "x = (i, j)" and j: "j < 2*k-2" using x by (auto simp: C_def blk_def)
    have "(nxt N i, j) \<in> X" by (rule mp_forces[OF k i tr small]) (use x xj in \<open>simp add: C_def\<close>)
    then show "y \<in> X \<inter> blk k (nxt N i)" using y xj j by (simp add: m_def blk_def)
  qed
  have "card C = card (m ` C)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card (X \<inter> blk k (nxt N i))" by (rule card_mono[OF _ sub]) simp
  finally show ?thesis using cardC by simp
qed

subsection \<open>The transversal number\<close>

theorem mp_tau:
  assumes k: "2 \<le> k" and N: "0 < N" and tr: "tr (mp N k) X" and fX: "finite X"
  shows "N * (k - 1) \<le> card X"
proof -
  define f where "f i = card (X \<inter> blk k i)" for i
  define d where "d i = (if f i < k - 1 then k - 1 - f i else 0)" for i
  have step: "(k - 1) + d i \<le> f (nxt N i) + d (nxt N i)" if i: "i < N" for i
  proof (cases "f i < k - 1")
    case True
    have "2*k-2 - f i \<le> f (nxt N i)" using mp_mirror[OF k i N tr] True by (simp add: f_def)
    then show ?thesis using True k by (simp add: d_def)
  next
    case False
    then show ?thesis unfolding d_def by (simp; arith)
  qed
  have "(\<Sum>i<N. (k - 1) + d i) \<le> (\<Sum>i<N. f (nxt N i) + d (nxt N i))"
    by (rule sum_mono) (rule step, simp)
  also have "\<dots> = (\<Sum>i<N. f i + d i)"
    using sum.reindex_bij_betw[OF bij_nxt[OF N], of "\<lambda>i. f i + d i"] by simp
  finally have "N * (k - 1) + (\<Sum>i<N. d i) \<le> (\<Sum>i<N. f i) + (\<Sum>i<N. d i)"
    by (simp add: sum.distrib)
  then have sumf: "N * (k - 1) \<le> (\<Sum>i<N. f i)" by linarith
  have "(\<Sum>i<N. f i) = card (\<Union>i<N. X \<inter> blk k i)"
    unfolding f_def by (rule card_UN_disjoint[symmetric]) (auto simp: blk_def)
  also have "\<dots> \<le> card X" by (rule card_mono[OF fX]) blast
  finally show ?thesis using sumf by linarith
qed

subsection \<open>Glued choices that are transversals\<close>

lemma mp_glue_tr:
  assumes k: "2 \<le> k" and N: "0 < N" and S: "\<forall>i<N. S i \<subseteq> {..<2*k-2}"
    and ins: "\<forall>i<N. 2*k-3 \<in> S i \<or> card ({..<2*k-2} - S i) < k"
    and pay: "\<forall>i<N. card ({..<2*k-3} - S i) < k - 1 \<or> {..<2*k-3} - S i \<subseteq> S (nxt N i)"
  shows "tr (mp N k) (glue N S)"
  unfolding tr_def
proof
  fix e assume e: "e \<in> mp N k"
  show "e \<inter> glue N S \<noteq> {}"
  proof (cases "\<exists>i<N. e \<subseteq> blk k i \<and> card e = k \<and> (i, 2*k-3) \<in> e")
    case True
    then obtain i where i: "i < N" and eB: "e \<subseteq> blk k i" and ce: "card e = k"
      and r: "(i, 2*k-3) \<in> e" by blast
    show ?thesis
    proof
      assume dis: "e \<inter> glue N S = {}"
      have nr: "2*k-3 \<notin> S i" using r dis i by (auto simp: glue_def)
      have "e \<subseteq> {i} \<times> ({..<2*k-2} - S i)" using eB dis i by (auto simp: blk_def glue_def)
      then have "card e \<le> card ({i} \<times> ({..<2*k-2} - S i))" by (rule card_mono[rotated]) simp
      also have "\<dots> = card ({..<2*k-2} - S i)" by (simp add: card_cartesian_product)
      finally show False using ins i nr ce by auto
    qed
  next
    case False
    then obtain i A j where i: "i < N" and AR: "A \<subseteq> {i} \<times> {..<2*k-3}" and cA: "card A = k - 1"
      and jA: "(i, j) \<in> A" and eq: "e = insert (nxt N i, j) A" using e unfolding mp_def by blast
    show ?thesis
    proof
      assume dis: "e \<inter> glue N S = {}"
      have AS: "A \<subseteq> {i} \<times> ({..<2*k-3} - S i)" using AR dis i eq by (auto simp: glue_def)
      show False
      proof (cases "card ({..<2*k-3} - S i) < k - 1")
        case True
        have "card A \<le> card ({i} \<times> ({..<2*k-3} - S i))" by (rule card_mono[OF _ AS]) simp
        also have "\<dots> = card ({..<2*k-3} - S i)" by (simp add: card_cartesian_product)
        finally show False using True cA by simp
      next
        case False
        then have sub: "{..<2*k-3} - S i \<subseteq> S (nxt N i)" using pay i by blast
        have "j \<in> {..<2*k-3} - S i" using AS jA by blast
        then have "j \<in> S (nxt N i)" using sub by blast
        then have "(nxt N i, j) \<in> glue N S" using nxt_lt[OF N] by (auto simp: glue_def)
        then show False using dis eq by blast
      qed
    qed
  qed
qed

lemma card_glue:
  assumes S: "\<forall>i<N. S i \<subseteq> {..<2*k-2}"
  shows "card (glue N S) = (\<Sum>i<N. card (S i))"
proof -
  have fS: "finite (S i)" if "i < N" for i using S that finite_subset by blast
  have "card (glue N S) = (\<Sum>i<N. card ({i} \<times> S i))"
    unfolding glue_def by (rule card_UN_disjoint) (auto simp: fS)
  also have "\<dots> = (\<Sum>i<N. card (S i))" by (simp add: card_cartesian_product)
  finally show ?thesis .
qed

lemma glue_blk:
  assumes "i < N" and "S i \<subseteq> {..<2*k-2}"
  shows "glue N S \<inter> blk k i = {i} \<times> S i"
  using assms by (auto simp: glue_def blk_def)

subsection \<open>Every deficiency level occurs\<close>

definition mtr :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set set" where
  "mtr N k = {X. X \<subseteq> vdp N k \<and> tr (mp N k) X \<and> card X = N * (k - 1)}"

lemma glue_vdp:
  assumes "\<forall>i<N. S i \<subseteq> {..<2*k-2}"
  shows "glue N S \<subseteq> vdp N k"
  using assms by (auto simp: glue_def vdp_def blk_def)

theorem mp_deficient:
  assumes k: "2 \<le> k" and N: "2 \<le> N" and Z: "Z \<subseteq> {..<2*k-3}" "k - 1 \<le> card Z"
  shows "\<exists>X\<in>mtr N k. X \<inter> blk k 0 = {0} \<times> ({..<2*k-2} - Z)"
proof -
  define T where "T = {..<k-1}"
  define S where "S i = (if i = 0 then {..<2*k-2} - Z else if i = 1 then Z else T)" for i :: nat
  have N0: "0 < N" using N by simp
  have n01: "nxt N 0 = 1" using N by (simp add: nxt_def)
  have fZ: "finite Z" using Z(1) finite_subset by blast
  have Z2: "Z \<subseteq> {..<2*k-2}" using Z(1) by auto
  have cZ: "card Z \<le> 2*k-3" using card_mono[OF finite_lessThan Z(1)] by simp
  have Ssub: "\<forall>i<N. S i \<subseteq> {..<2*k-2}" using Z(1) k by (auto simp: S_def T_def)
  have cS0: "card ({..<2*k-2} - Z) = 2*k-2 - card Z"
    using card_Diff_subset[OF fZ Z2] by simp
  have cT: "card T = k - 1" by (simp add: T_def)
  have Tc: "card ({..<2*k-2} - T) = k - 1" and Tc3: "card ({..<2*k-3} - T) = k - 2"
    using k by (simp_all add: T_def card_Diff_subset)
  have Zc: "card ({..<2*k-2} - Z) < k" and Zc3: "card ({..<2*k-3} - Z) < k - 1"
  proof -
    have "card ({..<2*k-2} - Z) = 2*k-2 - card Z"
      using card_Diff_subset[OF fZ Z2] by simp
    then show "card ({..<2*k-2} - Z) < k" using Z(2) k by simp
    have "card ({..<2*k-3} - Z) = 2*k-3 - card Z" using card_Diff_subset[OF fZ Z(1)] by simp
    then show "card ({..<2*k-3} - Z) < k - 1" using Z(2) k by simp
  qed
  have ins: "\<forall>i<N. 2*k-3 \<in> S i \<or> card ({..<2*k-2} - S i) < k"
  proof (intro allI impI)
    fix i assume "i < N"
    show "2*k-3 \<in> S i \<or> card ({..<2*k-2} - S i) < k"
    proof (cases "i = 0")
      case True
      have "2*k-3 \<notin> Z" using Z(1) by auto
      then show ?thesis using True k by (simp add: S_def; arith)
    next
      case False
      then show ?thesis using Zc Tc k by (simp add: S_def)
    qed
  qed
  have pay: "\<forall>i<N. card ({..<2*k-3} - S i) < k - 1 \<or> {..<2*k-3} - S i \<subseteq> S (nxt N i)"
  proof (intro allI impI)
    fix i assume "i < N"
    show "card ({..<2*k-3} - S i) < k - 1 \<or> {..<2*k-3} - S i \<subseteq> S (nxt N i)"
    proof (cases "i = 0")
      case True
      have "{..<2*k-3} - ({..<2*k-2} - Z) \<subseteq> Z" by auto
      then show ?thesis using True n01 by (simp add: S_def)
    next
      case False
      have "card ({..<2*k-3} - S i) < k - 1"
      proof (cases "i = 1")
        case True
        then show ?thesis using Zc3 by (simp add: S_def)
      next
        case i1: False
        have "S i = T" using False i1 by (simp add: S_def)
        then show ?thesis using Tc3 k by simp
      qed
      then show ?thesis by (rule disjI1)
    qed
  qed
  have trX: "tr (mp N k) (glue N S)" by (rule mp_glue_tr[OF k N0 Ssub ins pay])
  have "card (glue N S) = (\<Sum>i<N. card (S i))" by (rule card_glue[OF Ssub])
  also have "\<dots> = (\<Sum>i\<in>{0, 1} \<union> {2..<N}. card (S i))"
    by (rule sum.cong) (use N in auto)
  also have "\<dots> = card (S 0) + card (S 1) + (\<Sum>i\<in>{2..<N}. card (S i))"
    by (subst sum.union_disjoint) auto
  also have "(\<Sum>i\<in>{2..<N}. card (S i)) = (\<Sum>i\<in>{2..<N}. k - 1)"
    by (rule sum.cong) (auto simp: S_def cT)
  also have "card (S 0) + card (S 1) = 2*k-2" using cS0 cZ k by (simp add: S_def)
  finally have "card (glue N S) = 2*k-2 + (N - 2) * (k - 1)" by simp
  also have "\<dots> = N * (k - 1)"
  proof -
    have e1: "2*k-2 = 2 * (k - 1)" using k by simp
    have e2: "2 + (N - 2) = N" using N by simp
    have "2 * (k - 1) + (N - 2) * (k - 1) = (2 + (N - 2)) * (k - 1)" by (simp only: add_mult_distrib)
    then show ?thesis unfolding e1 e2 .
  qed
  finally have cX: "card (glue N S) = N * (k - 1)" .
  have "glue N S \<in> mtr N k" unfolding mtr_def using glue_vdp[OF Ssub] trX cX by blast
  moreover have "glue N S \<inter> blk k 0 = {0} \<times> ({..<2*k-2} - Z)"
    using glue_blk[of 0 N S k] Ssub N0 by (simp add: S_def)
  ultimately show ?thesis by blast
qed

subsection \<open>The trace on one block is nearly full\<close>

lemma half_subsets:
  assumes k: "2 \<le> k"
  shows "2 ^ (2*k-4) \<le> card {Z. Z \<subseteq> {..<2*k-3} \<and> k - 1 \<le> card Z}"
proof -
  define m where "m = 2*k-3"
  define U where "U = {Z. Z \<subseteq> {..<m} \<and> k - 1 \<le> card Z}"
  define L where "L = {Z. Z \<subseteq> {..<m} \<and> \<not> k - 1 \<le> card Z}"
  have fU: "finite U" and fL: "finite L" unfolding U_def L_def by (auto intro: finite_subset[of _ "Pow {..<m}"])
  have UL: "U \<union> L = Pow {..<m}" and dis: "U \<inter> L = {}" unfolding U_def L_def by auto
  have tot: "card U + card L = 2 ^ m"
    using card_Un_disjoint[OF fU fL dis] UL by (simp add: card_Pow)
  define \<phi> where "\<phi> Z = {..<m} - Z" for Z :: "nat set"
  have inj: "inj_on \<phi> L" by (rule inj_onI) (auto simp: \<phi>_def L_def)
  have sub: "\<phi> ` L \<subseteq> U"
  proof
    fix Y assume "Y \<in> \<phi> ` L"
    then obtain Z where Z: "Z \<in> L" and Y: "Y = \<phi> Z" by blast
    have Zm: "Z \<subseteq> {..<m}" and cZ: "card Z < k - 1" using Z by (auto simp: L_def)
    have fZ: "finite Z" using Zm finite_subset by blast
    have "card Y = m - card Z" unfolding Y \<phi>_def using card_Diff_subset[OF fZ Zm] by simp
    then have "k - 1 \<le> card Y" using cZ unfolding m_def by simp
    then show "Y \<in> U" unfolding U_def Y \<phi>_def by auto
  qed
  have "card L = card (\<phi> ` L)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card U" by (rule card_mono[OF fU sub])
  finally have "card L \<le> card U" .
  then have "2 ^ m \<le> 2 * card U" using tot by simp
  moreover have "m = Suc (2*k-4)" unfolding m_def using k by simp
  ultimately have "2 ^ (2*k-4) \<le> card U" by simp
  then show ?thesis unfolding U_def m_def .
qed

theorem mp_trace:
  assumes k: "2 \<le> k" and N: "2 \<le> N"
  shows "2 ^ (2*k-4) \<le> card ((\<lambda>X. X \<inter> blk k 0) ` mtr N k)"
proof -
  define Q where "Q = {Z. Z \<subseteq> {..<2*k-3} \<and> k - 1 \<le> card Z}"
  define p where "p Z = {0::nat} \<times> ({..<2*k-2} - Z)" for Z
  have inj: "inj_on p Q"
  proof (rule inj_onI)
    fix Z Z' assume Z: "Z \<in> Q" and Z': "Z' \<in> Q" and e: "p Z = p Z'"
    have "{..<2*k-2} - Z = {..<2*k-2} - Z'" using e by (auto simp: p_def)
    moreover have "Z \<subseteq> {..<2*k-2}" "Z' \<subseteq> {..<2*k-2}" using Z Z' by (auto simp: Q_def)
    ultimately show "Z = Z'" by blast
  qed
  have sub: "p ` Q \<subseteq> (\<lambda>X. X \<inter> blk k 0) ` mtr N k"
  proof
    fix Y assume "Y \<in> p ` Q"
    then obtain Z where Z: "Z \<in> Q" and Y: "Y = p Z" by blast
    have Zq: "Z \<subseteq> {..<2*k-3}" "k - 1 \<le> card Z" using Z by (auto simp: Q_def)
    obtain X where X1: "X \<in> mtr N k" and X2: "X \<inter> blk k 0 = {0} \<times> ({..<2*k-2} - Z)"
      using mp_deficient[OF k N Zq] by blast
    show "Y \<in> (\<lambda>X. X \<inter> blk k 0) ` mtr N k"
      by (rule image_eqI[OF _ X1]) (simp only: Y p_def X2)
  qed
  have fin: "finite ((\<lambda>X. X \<inter> blk k 0) ` mtr N k)"
    by (rule finite_subset[of _ "Pow (blk k 0)"]) auto
  have "2 ^ (2*k-4) \<le> card Q" unfolding Q_def by (rule half_subsets[OF k])
  also have "\<dots> = card (p ` Q)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card ((\<lambda>X. X \<inter> blk k 0) ` mtr N k)" by (rule card_mono[OF fin sub])
  finally show ?thesis .
qed

subsection \<open>The count\<close>

theorem mp_count:
  assumes k: "2 \<le> k" and N: "0 < N"
  shows "((2*k-3) choose (k-1)) ^ N \<le> card (mtr N k)"
proof -
  define G where "G = {T. T \<subseteq> {..<2*k-3} \<and> card T = k - 1}"
  define P where "P = {..<N} \<rightarrow>\<^sub>E G"
  have cG: "card G = (2*k-3) choose (k-1)" unfolding G_def using n_subsets[of "{..<2*k-3}" "k-1"] by simp
  have inj: "inj_on (glue N) P"
  proof (rule inj_onI)
    fix S S' assume S: "S \<in> P" and S': "S' \<in> P" and e: "glue N S = glue N S'"
    show "S = S'"
    proof
      fix i show "S i = S' i"
      proof (cases "i < N")
        case True
        have "S i = {j. (i, j) \<in> glue N S}" using True by (auto simp: glue_def)
        also have "\<dots> = {j. (i, j) \<in> glue N S'}" using e by simp
        also have "\<dots> = S' i" using True by (auto simp: glue_def)
        finally show ?thesis .
      next
        case False
        have "S i = undefined" using S False unfolding P_def by (intro PiE_arb) auto
        moreover have "S' i = undefined" using S' False unfolding P_def by (intro PiE_arb) auto
        ultimately show ?thesis by simp
      qed
    qed
  qed
  have sub: "glue N ` P \<subseteq> mtr N k"
  proof
    fix X assume "X \<in> glue N ` P"
    then obtain S where S: "S \<in> P" and X: "X = glue N S" by blast
    have SG: "S i \<subseteq> {..<2*k-3}" "card (S i) = k - 1" if "i < N" for i
      using S that by (auto simp: P_def G_def)
    have Ssub: "\<forall>i<N. S i \<subseteq> {..<2*k-2}" using SG(1) by fastforce
    have c3: "card ({..<2*k-3} - S i) = k - 2" and c2: "card ({..<2*k-2} - S i) = k - 1"
      if "i < N" for i
    proof -
      have fS: "finite (S i)" using SG(1)[OF that] finite_subset by blast
      show "card ({..<2*k-3} - S i) = k - 2"
        using card_Diff_subset[OF fS SG(1)[OF that]] SG(2)[OF that] k by simp
      have "S i \<subseteq> {..<2*k-2}" using SG(1)[OF that] by auto
      then show "card ({..<2*k-2} - S i) = k - 1"
        using card_Diff_subset[OF fS] SG(2)[OF that] k by simp
    qed
    have ins: "\<forall>i<N. 2*k-3 \<in> S i \<or> card ({..<2*k-2} - S i) < k"
    proof (intro allI impI disjI2)
      fix i assume "i < N"
      then show "card ({..<2*k-2} - S i) < k" using c2 k by simp
    qed
    have pay: "\<forall>i<N. card ({..<2*k-3} - S i) < k - 1 \<or> {..<2*k-3} - S i \<subseteq> S (nxt N i)"
    proof (intro allI impI disjI1)
      fix i assume "i < N"
      then have "card ({..<2*k-3} - S i) = k - 2" by (rule c3)
      then show "card ({..<2*k-3} - S i) < k - 1" using k by arith
    qed
    have "tr (mp N k) X" unfolding X by (rule mp_glue_tr[OF k N Ssub ins pay])
    moreover have "card X = N * (k - 1)" unfolding X card_glue[OF Ssub] using SG(2) by simp
    ultimately show "X \<in> mtr N k" unfolding mtr_def using glue_vdp[OF Ssub] X by blast
  qed
  have fin: "finite (mtr N k)"
    by (rule finite_subset[of _ "Pow (vdp N k)"]) (auto simp: mtr_def vdp_def)
  have "((2*k-3) choose (k-1)) ^ N = card P" by (simp add: P_def card_PiE cG)
  also have "\<dots> = card (glue N ` P)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card (mtr N k)" by (rule card_mono[OF fin sub])
  finally show ?thesis .
qed

end
