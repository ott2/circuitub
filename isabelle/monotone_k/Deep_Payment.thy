theory Deep_Payment
  imports Shadow_Branch "HOL-Library.FuncSet"
begin

section \<open>Deep payments: a counterexample to the deficit conjecture\<close>

text \<open>
  Blocks \<open>B\<^sub>i = {i} \<times> {..<2k-2}\<close> for \<open>i < N\<close>, with \<open>R\<^sub>i = {i} \<times> {..<k-1+s}\<close>.  The edges are the
  \<open>k\<close>-subsets of a block not inside its \<open>R\<^sub>i\<close>, and the payments \<open>A \<union> {g}\<close> with \<open>A\<close> a
  \<open>(k-1)\<close>-subset of \<open>R\<^sub>i\<close> and \<open>g\<close> in the next block along the cycle.  A block with fewer than
  \<open>k-1\<close> chosen vertices forces the whole next block (\<open>dp_forces\<close>), so \<open>\<tau> = N(k-1)\<close>
  (\<open>dp_tau\<close>).  Every choice of \<open>(k-1)\<close>-sets meeting \<open>R\<^sub>i\<close> in more than \<open>s\<close> vertices is a minimum
  transversal (\<open>dp_normal\<close>), so there are at least \<open>|good|\<^sup>N\<close> of them (\<open>dp_count\<close>): the count of
  disjoint \<open>K\<^bsub>2k-2\<^esub>\<^sup>(k)\<close> blocks up to a factor \<open>1 - e\<^sup>-\<^sup>\<Omega>\<^sup>(\<^sup>k\<^sup>)\<close> per block.  Yet every block falls short
  locally by \<open>s\<close>, since \<open>B\<^sub>i - R\<^sub>i\<close> meets all inside edges (log \<section>6e, by hand).\<close>

definition blk :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "blk k i = {i} \<times> {..<2*k-2}"

definition rr :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "rr k s i = {i} \<times> {..<k-1+s}"

definition nxt :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nxt N i = Suc i mod N"

definition dp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set set" where
  "dp N k s = {e. \<exists>i<N. e \<subseteq> blk k i \<and> card e = k \<and> \<not> e \<subseteq> rr k s i}
     \<union> {insert g A | i A g. i < N \<and> A \<subseteq> rr k s i \<and> card A = k - 1 \<and> g \<in> blk k (nxt N i)}"

definition vdp :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "vdp N k = (\<Union>i<N. blk k i)"

lemma finite_blk [simp]: "finite (blk k i)"
  by (simp add: blk_def)

lemma card_blk [simp]: "card (blk k i) = 2*k-2"
  by (simp add: blk_def card_cartesian_product)

lemma blk_disj: "i \<noteq> j \<Longrightarrow> blk k i \<inter> blk k j = {}"
  by (auto simp: blk_def)

lemma nxt_lt: "0 < N \<Longrightarrow> nxt N i < N"
  by (simp add: nxt_def)

lemma nxt_eq: "i < N \<Longrightarrow> nxt N i = (if Suc i = N then 0 else Suc i)"
  by (auto simp: nxt_def)

lemma bij_nxt:
  assumes N: "0 < N"
  shows "bij_betw (nxt N) {..<N} {..<N}"
proof -
  have inj: "inj_on (nxt N) {..<N}"
  proof (rule inj_onI)
    fix i j assume i: "i \<in> {..<N}" and j: "j \<in> {..<N}" and e: "nxt N i = nxt N j"
    then show "i = j" using nxt_eq[of i N] nxt_eq[of j N] by (auto split: if_splits)
  qed
  have sub: "nxt N ` {..<N} \<subseteq> {..<N}" using nxt_lt[OF N] by auto
  have "nxt N ` {..<N} = {..<N}" by (rule endo_inj_surj[OF _ sub inj]) simp
  then show ?thesis using inj by (simp add: bij_betw_def)
qed

subsection \<open>A deficient block forces the next one\<close>

lemma dp_forces:
  assumes k: "2 \<le> k" and i: "i < N" and tr: "tr (dp N k s) X"
    and small: "card (X \<inter> blk k i) < k - 1"
  shows "blk k (nxt N i) \<subseteq> X"
proof -
  define C where "C = blk k i - X"
  have fC: "finite C" by (simp add: C_def)
  have "card C = card (blk k i) - card (blk k i \<inter> X)"
    unfolding C_def by (rule card_Diff_subset_Int) simp
  also have "card (blk k i \<inter> X) = card (X \<inter> blk k i)" by (simp add: Int_commute)
  finally have cardC: "k \<le> card C" using small k by simp
  have CR: "C \<subseteq> rr k s i"
  proof
    fix c assume c: "c \<in> C"
    show "c \<in> rr k s i"
    proof (rule ccontr)
      assume nc: "c \<notin> rr k s i"
      have "k - 1 \<le> card (C - {c})" using cardC c fC by simp
      then obtain T where T: "T \<subseteq> C - {c}" "card T = k - 1"
        using obtain_subset_with_card_n by metis
      have fT: "finite T" using T(1) fC by (meson finite_Diff finite_subset)
      have cT: "c \<notin> T" using T(1) by blast
      have ce: "card (insert c T) = k" using T(2) fT cT k by simp
      have "insert c T \<subseteq> blk k i" using T(1) c by (auto simp: C_def)
      moreover have "\<not> insert c T \<subseteq> rr k s i" using nc by simp
      ultimately have "insert c T \<in> dp N k s" using i ce unfolding dp_def by blast
      then have "insert c T \<inter> X \<noteq> {}" using tr unfolding tr_def by blast
      moreover have "insert c T \<inter> X = {}" using T(1) c by (auto simp: C_def)
      ultimately show False by blast
    qed
  qed
  have "k - 1 \<le> card C" using cardC by simp
  then obtain A where A: "A \<subseteq> C" "card A = k - 1" using obtain_subset_with_card_n by metis
  have AR: "A \<subseteq> rr k s i" using A(1) CR by blast
  have AX: "A \<inter> X = {}" using A(1) by (auto simp: C_def)
  show ?thesis
  proof
    fix g assume g: "g \<in> blk k (nxt N i)"
    have "insert g A \<in> dp N k s" unfolding dp_def using i AR A(2) g by blast
    then have "insert g A \<inter> X \<noteq> {}" using tr unfolding tr_def by blast
    then show "g \<in> X" using AX by blast
  qed
qed

subsection \<open>The transversal number\<close>

theorem dp_tau:
  assumes k: "2 \<le> k" and N: "0 < N" and tr: "tr (dp N k s) X" and fX: "finite X"
  shows "N * (k - 1) \<le> card X"
proof -
  define f where "f i = card (X \<inter> blk k i)" for i
  define d where "d i = (if f i < k - 1 then k - 1 else 0)" for i
  have full: "f (nxt N i) = 2*k-2" if "i < N" "f i < k - 1" for i
  proof -
    have "blk k (nxt N i) \<subseteq> X" using dp_forces[OF k that(1) tr] that(2) by (simp add: f_def)
    then have "X \<inter> blk k (nxt N i) = blk k (nxt N i)" by blast
    then show ?thesis by (simp add: f_def)
  qed
  have step: "(k - 1) + d i \<le> f (nxt N i) + d (nxt N i)" if i: "i < N" for i
  proof (cases "f i < k - 1")
    case True
    then show ?thesis using full[OF i True] k by (simp add: d_def)
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

subsection \<open>Normal choices are minimum transversals\<close>

definition good :: "nat \<Rightarrow> nat \<Rightarrow> nat set set" where
  "good k s = {T. T \<subseteq> {..<2*k-2} \<and> card T = k - 1 \<and> s < card (T \<inter> {..<k-1+s})}"

definition glue :: "nat \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> (nat \<times> nat) set" where
  "glue N S = (\<Union>i<N. {i} \<times> S i)"

lemma finite_good: "finite (good k s)"
  by (rule finite_subset[of _ "Pow {..<2*k-2}"]) (auto simp: good_def)

theorem dp_normal:
  assumes k: "2 \<le> k" and S: "\<forall>i<N. S i \<in> good k s"
  shows "tr (dp N k s) (glue N S)" and "card (glue N S) = N * (k - 1)"
proof -
  have Sg: "S i \<subseteq> {..<2*k-2}" "card (S i) = k - 1" "s < card (S i \<inter> {..<k-1+s})"
    if "i < N" for i using S that by (auto simp: good_def)
  have fS: "finite (S i)" if "i < N" for i using Sg(1)[OF that] finite_subset by blast
  show "tr (dp N k s) (glue N S)"
    unfolding tr_def
  proof
    fix e assume e: "e \<in> dp N k s"
    show "e \<inter> glue N S \<noteq> {}"
    proof (cases "\<exists>i<N. e \<subseteq> blk k i \<and> card e = k \<and> \<not> e \<subseteq> rr k s i")
      case True
      then obtain i where i: "i < N" and eB: "e \<subseteq> blk k i" and ce: "card e = k" by blast
      show ?thesis
      proof
        assume dis: "e \<inter> glue N S = {}"
        have "e \<subseteq> {i} \<times> ({..<2*k-2} - S i)"
          using eB dis i by (auto simp: blk_def glue_def)
        then have "card e \<le> card ({i} \<times> ({..<2*k-2} - S i))" by (rule card_mono[rotated]) simp
        also have "\<dots> = card ({..<2*k-2} - S i)" by (simp add: card_cartesian_product)
        also have "\<dots> = 2*k-2 - (k - 1)"
          using Sg(1,2)[OF i] by (simp add: card_Diff_subset fS[OF i])
        finally show False using ce k by simp
      qed
    next
      case False
      then obtain i A g where i: "i < N" and AR: "A \<subseteq> rr k s i" and cA: "card A = k - 1"
        and eq: "e = insert g A" using e unfolding dp_def by blast
      show ?thesis
      proof
        assume dis: "e \<inter> glue N S = {}"
        have "A \<subseteq> {i} \<times> ({..<k-1+s} - S i \<inter> {..<k-1+s})"
          using AR dis i eq by (auto simp: rr_def glue_def)
        then have "card A \<le> card ({i} \<times> ({..<k-1+s} - S i \<inter> {..<k-1+s}))"
          by (rule card_mono[rotated]) simp
        also have "\<dots> = card ({..<k-1+s} - S i \<inter> {..<k-1+s})" by (simp add: card_cartesian_product)
        also have "\<dots> = k - 1 + s - card (S i \<inter> {..<k-1+s})"
          by (subst card_Diff_subset) auto
        finally have "card A \<le> k - 1 + s - card (S i \<inter> {..<k-1+s})" .
        moreover have "card (S i \<inter> {..<k-1+s}) \<le> k - 1 + s"
          using card_mono[OF finite_lessThan Int_lower2, of "S i" "k-1+s"] by simp
        ultimately show False using cA Sg(3)[OF i] k by arith
      qed
    qed
  qed
  have "card (glue N S) = (\<Sum>i<N. card ({i} \<times> S i))"
    unfolding glue_def by (rule card_UN_disjoint) (auto simp: fS)
  also have "\<dots> = (\<Sum>i<N. k - 1)" by (rule sum.cong) (simp_all add: card_cartesian_product Sg(2))
  finally show "card (glue N S) = N * (k - 1)" by simp
qed

subsection \<open>The count\<close>

theorem dp_count:
  assumes k: "2 \<le> k"
  shows "card (good k s) ^ N \<le> card {X. X \<subseteq> vdp N k \<and> tr (dp N k s) X \<and> card X = N * (k - 1)}"
proof -
  define P where "P = {..<N} \<rightarrow>\<^sub>E good k s"
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
  have sub: "glue N ` P \<subseteq> {X. X \<subseteq> vdp N k \<and> tr (dp N k s) X \<and> card X = N * (k - 1)}"
  proof
    fix X assume "X \<in> glue N ` P"
    then obtain S where S: "S \<in> P" and X: "X = glue N S" by blast
    have Sg: "\<forall>i<N. S i \<in> good k s" using S by (auto simp: P_def)
    have "X \<subseteq> vdp N k"
      using Sg unfolding X glue_def vdp_def blk_def good_def by blast
    then show "X \<in> {X. X \<subseteq> vdp N k \<and> tr (dp N k s) X \<and> card X = N * (k - 1)}"
      using dp_normal[OF k Sg] X by simp
  qed
  have fin: "finite {X. X \<subseteq> vdp N k \<and> tr (dp N k s) X \<and> card X = N * (k - 1)}"
    by (rule finite_subset[of _ "Pow (vdp N k)"]) (auto simp: vdp_def)
  have "card (good k s) ^ N = card P" by (simp add: P_def card_PiE)
  also have "\<dots> = card (glue N ` P)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card {X. X \<subseteq> vdp N k \<and> tr (dp N k s) X \<and> card X = N * (k - 1)}"
    by (rule card_mono[OF fin sub])
  finally show ?thesis .
qed

end
