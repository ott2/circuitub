theory Closed_Blocks
  imports Past_Antichain Minterm_Cover
begin

text \<open>Closed blocks. Fix blocks \<open>B\<^sub>0, \<dots>, B\<^sub>N\<^sub>-\<^sub>1\<close>. A block is closed for \<open>X\<close> if every one of
  \<open>X\<close> in it has a critical edge inside it. If every one lies in some closed block, label \<open>X\<close>
  by its set \<open>T\<close> of closed blocks (at most \<open>2^N\<close> labels), and reveal the closed blocks in
  order: the new part of \<open>B\<^sub>i\<close> is \<open>B\<^sub>i\<close> minus the earlier closed blocks, and by
  \<open>past_antichain\<close> its traces form an antichain given the past. Nothing outside the closed
  blocks is a one. The blocks may overlap arbitrarily.\<close>

definition bclosed :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "bclosed H X B \<longleftrightarrow> (\<forall>u\<in>X \<inter> B. \<exists>e\<in>H. e \<subseteq> B \<and> e \<inter> X = {u})"

definition upto :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> 'a set" where
  "upto B T j = \<Union>(B ` {i\<in>T. i < j})"

definition part :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> 'a set" where
  "part B T i = B i - upto B T i"

lemma fibre_count:
  assumes finG: "finite G" and b: "\<forall>s. card ((\<lambda>X. X \<inter> K) ` {X\<in>G. X \<inter> S = s}) \<le> b"
  shows "card ((\<lambda>X. X \<inter> (S \<union> K)) ` G) \<le> card ((\<lambda>X. X \<inter> S) ` G) * b"
proof -
  define G' where "G' s = {X\<in>G. X \<inter> S = s}" for s
  have eq: "(\<lambda>X. X \<inter> (S \<union> K)) ` G = (\<Union>s\<in>(\<lambda>X. X \<inter> S) ` G. (\<lambda>X. X \<inter> (S \<union> K)) ` G' s)"
    unfolding G'_def by blast
  have each: "card ((\<lambda>X. X \<inter> (S \<union> K)) ` G' s) \<le> b" for s
  proof -
    have "(\<lambda>X. X \<inter> (S \<union> K)) ` G' s = (\<lambda>Z. s \<union> Z) ` ((\<lambda>X. X \<inter> K) ` G' s)"
      unfolding G'_def by (auto simp: image_iff Int_Un_distrib)
    then have "card ((\<lambda>X. X \<inter> (S \<union> K)) ` G' s) \<le> card ((\<lambda>X. X \<inter> K) ` G' s)"
      by (simp add: card_image_le finG G'_def)
    then show ?thesis using b unfolding G'_def by (meson order_trans)
  qed
  have "card ((\<lambda>X. X \<inter> (S \<union> K)) ` G) \<le> (\<Sum>s\<in>(\<lambda>X. X \<inter> S) ` G. card ((\<lambda>X. X \<inter> (S \<union> K)) ` G' s))"
    by (subst eq) (rule card_UN_le, simp add: finG)
  also have "\<dots> \<le> (\<Sum>s\<in>(\<lambda>X. X \<inter> S) ` G. b)" by (rule sum_mono) (rule each)
  also have "\<dots> = card ((\<lambda>X. X \<inter> S) ` G) * b" by simp
  finally show ?thesis .
qed

lemma closed_fixed:
  assumes finG: "finite G" and tr: "\<forall>X\<in>G. \<forall>e\<in>H. e \<inter> X \<noteq> {}"
    and clT: "\<forall>X\<in>G. \<forall>i\<in>T. bclosed H X (B i)"
    and cov: "\<forall>X\<in>G. X \<subseteq> \<Union>(B ` T)"
    and finB: "\<forall>i\<in>T. finite (B i)" and TN: "T \<subseteq> {..<N}"
  shows "card G \<le> (\<Prod>i\<in>T. card (part B T i) choose (card (part B T i) div 2))"
proof -
  define b where "b i = card (part B T i) choose (card (part B T i) div 2)" for i
  have step: "card ((\<lambda>X. X \<inter> upto B T j) ` G) \<le> (\<Prod>i\<in>{i\<in>T. i < j}. b i)" for j
  proof (induction j)
    case 0
    have "(\<lambda>X. X \<inter> upto B T 0) ` G \<subseteq> {{}}" unfolding upto_def by auto
    then have "card ((\<lambda>X. X \<inter> upto B T 0) ` G) \<le> card {{}::'a set}" by (rule card_mono[rotated]) simp
    then have "card ((\<lambda>X. X \<inter> upto B T 0) ` G) \<le> 1" by simp
    then show ?case by simp
  next
    case (Suc j)
    show ?case
    proof (cases "j \<in> T")
      case False
      have "{i\<in>T. i < Suc j} = {i\<in>T. i < j}" using False less_Suc_eq by auto
      moreover then have "upto B T (Suc j) = upto B T j" unfolding upto_def by simp
      ultimately show ?thesis using Suc.IH by simp
    next
      case True
      have idx: "{i\<in>T. i < Suc j} = insert j {i\<in>T. i < j}" using True less_Suc_eq by auto
      have U: "upto B T (Suc j) = upto B T j \<union> part B T j"
        unfolding upto_def part_def idx by auto
      have fibre: "card ((\<lambda>X. X \<inter> part B T j) ` {X\<in>G. X \<inter> upto B T j = s}) \<le> b j" for s
      proof -
        have trs: "\<forall>X\<in>{X\<in>G. X \<inter> upto B T j = s}. \<forall>e\<in>H. e \<inter> X \<noteq> {}" using tr by blast
        have ags: "\<forall>X\<in>{X\<in>G. X \<inter> upto B T j = s}. \<forall>X'\<in>{X\<in>G. X \<inter> upto B T j = s}.
            X \<inter> upto B T j = X' \<inter> upto B T j" by simp
        have ls: "\<forall>X\<in>{X\<in>G. X \<inter> upto B T j = s}. \<forall>v\<in>X \<inter> part B T j. loc H (upto B T j) (part B T j) X v"
        proof (intro ballI)
          fix X v assume X: "X \<in> {X\<in>G. X \<inter> upto B T j = s}" and v: "v \<in> X \<inter> part B T j"
          have "bclosed H X (B j)" using clT X True by blast
          moreover have "v \<in> X \<inter> B j" using v unfolding part_def by blast
          ultimately obtain e where e: "e \<in> H" "e \<subseteq> B j" "e \<inter> X = {v}" unfolding bclosed_def by blast
          have "B j \<subseteq> upto B T j \<union> part B T j" unfolding part_def by blast
          then show "loc H (upto B T j) (part B T j) X v" unfolding loc_def using e by blast
        qed
        have finP: "finite (part B T j)" using finB True unfolding part_def by simp
        show ?thesis unfolding b_def
          by (rule sperner[OF past_antichain[OF trs ags ls] finP]) blast
      qed
      have "card ((\<lambda>X. X \<inter> upto B T (Suc j)) ` G) \<le> card ((\<lambda>X. X \<inter> upto B T j) ` G) * b j"
        unfolding U by (rule fibre_count[OF finG]) (use fibre in blast)
      also have "\<dots> \<le> (\<Prod>i\<in>{i\<in>T. i < j}. b i) * b j" by (rule mult_right_mono[OF Suc.IH]) simp
      also have "\<dots> = (\<Prod>i\<in>{i\<in>T. i < Suc j}. b i)"
      proof -
        have "finite {i\<in>T. i < j}" by simp
        moreover have "j \<notin> {i\<in>T. i < j}" by simp
        ultimately show ?thesis unfolding idx by (simp add: mult.commute)
      qed
      finally show ?thesis .
    qed
  qed
  have UN: "upto B T N = \<Union>(B ` T)" unfolding upto_def using TN by auto
  have "(\<lambda>X. X \<inter> upto B T N) ` G = G" unfolding UN using cov by (auto simp: Int_absorb2 image_iff)
  moreover have "{i\<in>T. i < N} = T" using TN by auto
  ultimately show ?thesis using step[of N] unfolding b_def by simp
qed

definition closedset :: "'a set set \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> nat set" where
  "closedset H B N X = {i. i < N \<and> bclosed H X (B i)}"

theorem closed_blocks:
  assumes finF: "finite F" and tr: "\<forall>X\<in>F. \<forall>e\<in>H. e \<inter> X \<noteq> {}"
    and finB: "\<forall>i<N. finite (B i)"
    and cov: "\<forall>X\<in>F. \<forall>v\<in>X. \<exists>i<N. v \<in> B i \<and> bclosed H X (B i)"
  shows "card F \<le> (\<Sum>T\<in>Pow {..<N}. \<Prod>i\<in>T. card (part B T i) choose (card (part B T i) div 2))"
proof -
  define G where "G T = {X\<in>F. closedset H B N X = T}" for T
  have eq: "F = (\<Union>T\<in>Pow {..<N}. G T)" unfolding G_def closedset_def by auto
  have each: "card (G T) \<le> (\<Prod>i\<in>T. card (part B T i) choose (card (part B T i) div 2))"
    if T: "T \<in> Pow {..<N}" for T
  proof (rule closed_fixed)
    show "finite (G T)" using finF unfolding G_def by simp
    show "\<forall>X\<in>G T. \<forall>e\<in>H. e \<inter> X \<noteq> {}" using tr unfolding G_def by blast
    show "\<forall>X\<in>G T. \<forall>i\<in>T. bclosed H X (B i)" unfolding G_def closedset_def by blast
    show "\<forall>X\<in>G T. X \<subseteq> \<Union>(B ` T)"
    proof (intro ballI subsetI)
      fix X v assume X: "X \<in> G T" and v: "v \<in> X"
      obtain i where "i < N" "v \<in> B i" "bclosed H X (B i)" using cov X v unfolding G_def by blast
      then have "i \<in> T" using X unfolding G_def closedset_def by blast
      then show "v \<in> \<Union>(B ` T)" using \<open>v \<in> B i\<close> by blast
    qed
    show "\<forall>i\<in>T. finite (B i)" using finB T by blast
    show "T \<subseteq> {..<N}" using T by blast
  qed
  have "card F \<le> (\<Sum>T\<in>Pow {..<N}. card (G T))" by (subst eq) (rule card_UN_le, simp)
  also have "\<dots> \<le> (\<Sum>T\<in>Pow {..<N}. \<Prod>i\<in>T. card (part B T i) choose (card (part B T i) div 2))"
    by (rule sum_mono) (rule each)
  finally show ?thesis .
qed

text \<open>Unions of cliques: every edge is a \<open>(c\<^sub>i+1)\<close>-subset of some block \<open>B\<^sub>i\<close>, and all
  such subsets are edges. A critical edge of a one in \<open>B\<^sub>i\<close> gives every other one in \<open>B\<^sub>i\<close>
  a critical edge by a swap, so the block is closed.\<close>

lemma clique_closed:
  assumes finB: "\<forall>i<N. finite (B i)"
    and inside: "\<forall>e\<in>H. \<exists>i<N. e \<subseteq> B i \<and> card e = Suc (c i)"
    and full: "\<forall>i<N. \<forall>e. e \<subseteq> B i \<and> card e = Suc (c i) \<longrightarrow> e \<in> H"
    and m: "mtr H X" and v: "v \<in> X"
  shows "\<exists>i<N. v \<in> B i \<and> bclosed H X (B i)"
proof -
  obtain e where e: "e \<in> H" and eX: "e \<inter> X = {v}" using mtr_crit[OF m v] by blast
  obtain i where i: "i < N" and eB: "e \<subseteq> B i" and ce: "card e = Suc (c i)" using inside e by blast
  have fine: "finite e" using finB i eB finite_subset by blast
  have "bclosed H X (B i)"
    unfolding bclosed_def
  proof (intro ballI)
    fix u assume u: "u \<in> X \<inter> B i"
    define e' where "e' = insert u (e - {v})"
    have ve: "v \<in> e" using eX by blast
    have un: "u \<notin> e - {v}" using u eX by blast
    have "card e' = Suc (card (e - {v}))" unfolding e'_def using un fine by simp
    also have "\<dots> = card e" by (rule card_Suc_Diff1[OF fine ve])
    finally have ce': "card e' = Suc (c i)" using ce by simp
    have sub: "e' \<subseteq> B i" unfolding e'_def using eB u by blast
    have "e' \<in> H" using full i sub ce' by blast
    moreover have "e' \<inter> X = {u}" unfolding e'_def using u eX by blast
    ultimately show "\<exists>e\<in>H. e \<subseteq> B i \<and> e \<inter> X = {u}" using sub by blast
  qed
  moreover have "v \<in> B i" using eB eX by blast
  ultimately show ?thesis using i by blast
qed

corollary clique_union:
  assumes finV: "finite V" and finB: "\<forall>i<N. finite (B i)"
    and inside: "\<forall>e\<in>H. \<exists>i<N. e \<subseteq> B i \<and> card e = Suc (c i)"
    and full: "\<forall>i<N. \<forall>e. e \<subseteq> B i \<and> card e = Suc (c i) \<longrightarrow> e \<in> H"
  shows "card {X. X \<subseteq> V \<and> mtr H X}
    \<le> (\<Sum>T\<in>Pow {..<N}. \<Prod>i\<in>T. card (part B T i) choose (card (part B T i) div 2))"
proof (rule closed_blocks[OF _ _ finB])
  show "finite {X. X \<subseteq> V \<and> mtr H X}" by (rule finite_subset[of _ "Pow V"]) (use finV in auto)
  show "\<forall>X\<in>{X. X \<subseteq> V \<and> mtr H X}. \<forall>e\<in>H. e \<inter> X \<noteq> {}" unfolding mtr_def tr_def by blast
  show "\<forall>X\<in>{X. X \<subseteq> V \<and> mtr H X}. \<forall>v\<in>X. \<exists>i<N. v \<in> B i \<and> bclosed H X (B i)"
    using clique_closed[OF finB inside full] by blast
qed

text \<open>The numeric form. With blocks of size \<open>\<le> m\<close>, each part of size \<open>j\<close> saves
  \<open>ln((3j+2)/2)/2 \<ge> (j/m) ln((3m+2)/2)/2\<close> (concavity, by weighted AM-GM), so every label
  saves \<open>ln((3m+2)/2)/(2m)\<close> per vertex, and the labels cost \<open>N ln 2\<close>.\<close>

lemma wamgm:
  fixes a b t :: real
  assumes a: "0 < a" and b: "0 < b" and t0: "0 \<le> t" and t1: "t \<le> 1"
  shows "t * ln a + (1 - t) * ln b \<le> ln (t * a + (1 - t) * b)"
proof -
  define M where "M = t * a + (1 - t) * b"
  have M: "0 < M"
  proof (cases "t = 0")
    case True then show ?thesis unfolding M_def using b by simp
  next
    case False then have "0 < t * a" using t0 a by simp
    moreover have "0 \<le> (1 - t) * b" using t1 b by simp
    ultimately show ?thesis unfolding M_def by simp
  qed
  have la: "ln a - ln M \<le> a / M - 1" using ln_le_minus_one[of "a / M"] a M by (simp add: ln_div)
  have lb: "ln b - ln M \<le> b / M - 1" using ln_le_minus_one[of "b / M"] b M by (simp add: ln_div)
  have "t * (ln a - ln M) + (1 - t) * (ln b - ln M) \<le> t * (a / M - 1) + (1 - t) * (b / M - 1)"
    by (rule add_mono; rule mult_left_mono) (use la lb t0 t1 in simp_all)
  also have "\<dots> = (t * a + (1 - t) * b) / M - 1" using M by (simp add: field_simps)
  also have "\<dots> = 0" using M unfolding M_def[symmetric] by simp
  finally show ?thesis unfolding M_def[symmetric] by (simp add: algebra_simps)
qed

lemma chord:
  fixes j m :: real
  assumes m: "0 < m" and j0: "0 \<le> j" and jm: "j \<le> m"
  shows "j / m * ln ((3 * m + 2) / 2) \<le> ln ((3 * j + 2) / 2)"
proof -
  have t1: "j / m \<le> 1" using jm m by simp
  have t0: "0 \<le> j / m" using j0 m by simp
  have "j / m * ln ((3 * m + 2) / 2) + (1 - j / m) * ln 1 \<le> ln (j / m * ((3 * m + 2) / 2) + (1 - j / m) * 1)"
    by (rule wamgm) (use m t0 t1 in simp_all)
  also have "j / m * ((3 * m + 2) / 2) + (1 - j / m) * 1 = (3 * j + 2) / 2" using m by (simp add: field_simps)
  finally show ?thesis by simp
qed

lemma part_saving:
  assumes jm: "j \<le> m" and m: "0 < m"
  shows "ln (real (j choose (j div 2))) \<le> real j * (ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m))"
proof -
  have "ln (real (j choose (j div 2))) \<le> real j * ln 2 - ln ((3 * real j + 2) / 2) / 2"
    by (rule ln_binom) simp
  also have "\<dots> \<le> real j * ln 2 - real j / real m * ln ((3 * real m + 2) / 2) / 2"
    using chord[of "real m" "real j"] jm m by simp
  also have "\<dots> = real j * (ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m))"
    using m by (simp add: field_simps)
  finally show ?thesis .
qed

lemma saving_nonneg:
  assumes m: "0 < m"
  shows "0 \<le> ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m)"
proof -
  have p4: "(3 * real j + 2) / 2 \<le> (4::real) ^ j" for j
  proof (induction j)
    case 0 then show ?case by simp
  next
    case (Suc j)
    have "(1::real) \<le> 4 ^ j" by (rule one_le_power) simp
    then show ?case using Suc.IH by simp
  qed
  have "ln ((3 * real m + 2) / 2) \<le> ln ((4::real) ^ m)" by (rule ln_mono[OF p4]) simp
  also have "ln ((4::real) ^ m) = real m * ln 4" by (simp add: ln_realpow)
  also have "ln (4::real) = 2 * ln 2" using ln_mult[of 2 2] by simp
  finally show ?thesis using m by (simp add: field_simps)
qed

lemma prod_bound:
  assumes finV: "finite V" and BV: "\<forall>i<N. B i \<subseteq> V" and Bm: "\<forall>i<N. card (B i) \<le> m" and m: "0 < m"
    and T: "T \<in> Pow {..<N}"
  shows "real (\<Prod>i\<in>T. card (part B T i) choose (card (part B T i) div 2))
    \<le> exp (real (card V) * (ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m)))"
proof -
  define c where "c = ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m)"
  have c0: "0 \<le> c" unfolding c_def by (rule saving_nonneg[OF m])
  have finB: "\<forall>i<N. finite (B i)" using BV finV finite_subset by blast
  define b where "b T i = card (part B T i) choose (card (part B T i) div 2)" for T i
  have finT: "finite T" using T finite_subset by blast
  have pos: "0 < real (b T i)" for i unfolding b_def by simp
  have partB: "part B T i \<subseteq> B i" for i unfolding part_def by blast
  have cardp: "card (part B T i) \<le> m" if "i \<in> T" for i
    using card_mono[OF _ partB[of i]] finB Bm that T by (meson PowD lessThan_iff subsetD order_trans)
  have "ln (real (\<Prod>i\<in>T. b T i)) = (\<Sum>i\<in>T. ln (real (b T i)))"
    using ln_prod[OF finT, of "\<lambda>i. real (b T i)"] pos by (simp add: of_nat_prod)
  also have "\<dots> \<le> (\<Sum>i\<in>T. real (card (part B T i)) * c)"
    by (rule sum_mono) (unfold b_def c_def, rule part_saving[OF cardp m], simp)
  also have "\<dots> = real (\<Sum>i\<in>T. card (part B T i)) * c" by (simp add: sum_distrib_right)
  also have "(\<Sum>i\<in>T. card (part B T i)) = card (\<Union>(part B T ` T))"
  proof (rule card_UN_disjoint[symmetric, OF finT])
    show "\<forall>i\<in>T. finite (part B T i)"
    proof
      fix i assume "i \<in> T"
      then have "i < N" using T by blast
      then have "finite (B i)" using finB by blast
      then show "finite (part B T i)" by (rule finite_subset[OF partB])
    qed
    show "\<forall>i\<in>T. \<forall>j\<in>T. i \<noteq> j \<longrightarrow> part B T i \<inter> part B T j = {}"
    proof (intro ballI impI)
      fix i j assume i: "i \<in> T" and j: "j \<in> T" and ij: "i \<noteq> j"
      show "part B T i \<inter> part B T j = {}"
      proof (cases "i < j")
        case True then have "B i \<subseteq> upto B T j" unfolding upto_def using i by blast
        then show ?thesis unfolding part_def by blast
      next
        case False then have "j < i" using ij by simp
        then have "B j \<subseteq> upto B T i" unfolding upto_def using j by blast
        then show ?thesis unfolding part_def by blast
      qed
    qed
  qed
  also have "real (card (\<Union>(part B T ` T))) * c \<le> real (card V) * c"
  proof (rule mult_right_mono[OF _ c0])
    have "\<Union>(part B T ` T) \<subseteq> V" using partB BV T by blast
    then show "real (card (\<Union>(part B T ` T))) \<le> real (card V)" by (simp add: card_mono finV)
  qed
  finally have "ln (real (\<Prod>i\<in>T. b T i)) \<le> real (card V) * c" .
  moreover have "0 < real (\<Prod>i\<in>T. b T i)" using pos by (simp add: prod_pos)
  ultimately have "real (\<Prod>i\<in>T. b T i) \<le> exp (real (card V) * c)" by (metis exp_ln exp_le_cancel_iff)
  then show ?thesis unfolding b_def c_def .
qed

theorem closed_bound:
  assumes finF: "finite F" and ne: "F \<noteq> {}" and finV: "finite V"
    and tr: "\<forall>X\<in>F. \<forall>e\<in>H. e \<inter> X \<noteq> {}"
    and BV: "\<forall>i<N. B i \<subseteq> V" and Bm: "\<forall>i<N. card (B i) \<le> m" and m: "0 < m"
    and cov: "\<forall>X\<in>F. \<forall>v\<in>X. \<exists>i<N. v \<in> B i \<and> bclosed H X (B i)"
  shows "ln (real (card F)) \<le> real N * ln 2 + real (card V) * (ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m))"
proof -
  define c where "c = ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m)"
  have finB: "\<forall>i<N. finite (B i)" using BV finV finite_subset by blast
  define b where "b T i = card (part B T i) choose (card (part B T i) div 2)" for T i
  have each: "real (\<Prod>i\<in>T. b T i) \<le> exp (real (card V) * c)" if T: "T \<in> Pow {..<N}" for T
    unfolding b_def c_def by (rule prod_bound[OF finV BV Bm m T])
  have "real (card F) \<le> real (\<Sum>T\<in>Pow {..<N}. \<Prod>i\<in>T. b T i)"
    unfolding b_def by (rule of_nat_mono, rule closed_blocks[OF finF tr finB cov])
  also have "\<dots> = (\<Sum>T\<in>Pow {..<N}. real (\<Prod>i\<in>T. b T i))" by simp
  also have "\<dots> \<le> (\<Sum>T\<in>Pow {..<N}. exp (real (card V) * c))" by (rule sum_mono) (rule each)
  also have "\<dots> = 2 ^ N * exp (real (card V) * c)" by (simp add: card_Pow)
  finally have le: "real (card F) \<le> 2 ^ N * exp (real (card V) * c)" .
  have posF: "0 < real (card F)" using ne finF by (simp add: card_gt_0_iff)
  have "ln (real (card F)) \<le> ln (2 ^ N * exp (real (card V) * c))" by (rule ln_mono[OF le posF])
  also have "\<dots> = real N * ln 2 + real (card V) * c" by (simp add: ln_mult ln_realpow)
  finally show ?thesis unfolding c_def .
qed

corollary clique_bound:
  assumes finV: "finite V" and BV: "\<forall>i<N. B i \<subseteq> V" and Bm: "\<forall>i<N. card (B i) \<le> m" and m: "0 < m"
    and inside: "\<forall>e\<in>H. \<exists>i<N. e \<subseteq> B i \<and> card e = Suc (c i)"
    and full: "\<forall>i<N. \<forall>e. e \<subseteq> B i \<and> card e = Suc (c i) \<longrightarrow> e \<in> H"
    and ne: "{X. X \<subseteq> V \<and> mtr H X} \<noteq> {}"
  shows "ln (real (card {X. X \<subseteq> V \<and> mtr H X}))
    \<le> real N * ln 2 + real (card V) * (ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m))"
proof (rule closed_bound[OF _ ne finV _ BV Bm m])
  have finB: "\<forall>i<N. finite (B i)" using BV finV finite_subset by blast
  show "finite {X. X \<subseteq> V \<and> mtr H X}" by (rule finite_subset[of _ "Pow V"]) (use finV in auto)
  show "\<forall>X\<in>{X. X \<subseteq> V \<and> mtr H X}. \<forall>e\<in>H. e \<inter> X \<noteq> {}" unfolding mtr_def tr_def by blast
  show "\<forall>X\<in>{X. X \<subseteq> V \<and> mtr H X}. \<forall>v\<in>X. \<exists>i<N. v \<in> B i \<and> bclosed H X (B i)"
    using clique_closed[OF finB inside full] by blast
qed

end
