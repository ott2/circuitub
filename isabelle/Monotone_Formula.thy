theory Monotone_Formula
  imports Monotone_Kraft Binomial_Estimates
begin

section \<open>Monotone formulas with block-symmetric tests: Theorem E\<Zprime> in finite form\<close>

text \<open>
  A monotone \<open>\<Sigma>\<^sub>3\<close> formula is an OR of tests; each test is a monotone CNF, given by its set of
  clauses (sets of variables).  The variables \<open>V\<close> are split into \<open>k\<close> blocks of size \<open>b\<close>, and
  every test is \<^emph>\<open>block-symmetric\<close>: its value depends only on the block weights.  No bound on
  the number of blocks a clause reads is assumed.

  \<open>formula_kraft\<close> applies \<open>wide_cover_kraft\<close> to every test of a formula that computes a
  threshold function, which needs a monotone predicate on weight vectors for each test
  (\<open>tw\<close>, \<open>tw_cnf\<close>, \<open>tw_sound\<close>).  \<open>atypical_count\<close> bounds the inputs with many atypical
  blocks.  \<open>majority_wide_tests\<close> combines these with \<open>Binomial_Estimates\<close> into an explicit
  lower bound on the number of tests of a formula for Majority.
\<close>

subsection \<open>Block weights\<close>

lemma card_blocks_sum:
  fixes blk :: "nat \<Rightarrow> 'a set"
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and X: "X \<subseteq> V"
  shows "card X = (\<Sum>i<k. bw blk k X i)"
proof -
  have "X = (\<Union>i<k. X \<inter> blk i)" using X by (auto simp: V)
  then have "card X = card (\<Union>i<k. X \<inter> blk i)" by simp
  also have "\<dots> = (\<Sum>i<k. card (X \<inter> blk i))" using blk disj by (intro card_UN_disjoint) auto
  also have "\<dots> = (\<Sum>i<k. bw blk k X i)" by (simp add: bw_def)
  finally show ?thesis .
qed

lemma bw_box:
  fixes blk :: "nat \<Rightarrow> 'a set"
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
  shows "bw blk k X \<in> {..<k} \<rightarrow>\<^sub>E {..b}"
proof -
  have "card (X \<inter> blk i) \<le> b" if "i < k" for i
    using blk that card_mono[of "blk i" "X \<inter> blk i"] by auto
  then show ?thesis by (auto simp: bw_def)
qed

text \<open>Inside \<open>X\<close>, any smaller block weights are realized by a subset.\<close>

lemma sub_with_weights:
  fixes blk :: "nat \<Rightarrow> 'a set"
  assumes disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}"
    and le: "\<forall>i<k. m i \<le> card (X \<inter> blk i)"
  shows "\<exists>Y\<subseteq>X. \<forall>i<k. card (Y \<inter> blk i) = m i"
proof -
  have "\<forall>i\<in>{..<k}. \<exists>T. T \<subseteq> X \<inter> blk i \<and> card T = m i"
  proof
    fix i assume "i \<in> {..<k}"
    then have "m i \<le> card (X \<inter> blk i)" using le by simp
    then obtain T where "T \<subseteq> X \<inter> blk i" "card T = m i" by (rule obtain_subset_with_card_n)
    then show "\<exists>T. T \<subseteq> X \<inter> blk i \<and> card T = m i" by blast
  qed
  from bchoice[OF this] obtain T where T: "\<forall>i\<in>{..<k}. T i \<subseteq> X \<inter> blk i \<and> card (T i) = m i"
    by blast
  define Y where "Y = (\<Union>i<k. T i)"
  have YX: "Y \<subseteq> X" using T by (auto simp: Y_def)
  have YT: "Y \<inter> blk i = T i" if i: "i < k" for i
  proof
    show "T i \<subseteq> Y \<inter> blk i" using T i by (auto simp: Y_def)
    show "Y \<inter> blk i \<subseteq> T i"
    proof
      fix x assume x: "x \<in> Y \<inter> blk i"
      then obtain j where j: "j < k" "x \<in> T j" by (auto simp: Y_def)
      have xj: "x \<in> blk j" using T j by blast
      show "x \<in> T i"
      proof (cases "j = i")
        case True
        then show ?thesis using j by simp
      next
        case False
        then have "blk i \<inter> blk j = {}" using disj i j(1) by blast
        then show ?thesis using x xj by blast
      qed
    qed
  qed
  show ?thesis using YX YT T by auto
qed

subsection \<open>A test as a monotone predicate on weight vectors\<close>

definition tw :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "tw blk k V cs u \<longleftrightarrow> (\<exists>X\<subseteq>V. (\<forall>i<k. bw blk k X i \<le> u i) \<and> cnf_val cs X)"

lemma tw_mono: "wmono k (tw blk k V cs)"
  unfolding wmono_def
proof (intro allI impI)
  fix u v assume uv: "\<forall>i<k. u i \<le> v i" and "tw blk k V cs u"
  then obtain X where X: "X \<subseteq> V" "\<forall>i<k. bw blk k X i \<le> u i" "cnf_val cs X" by (auto simp: tw_def)
  have "\<forall>i<k. bw blk k X i \<le> v i" using X(2) uv le_trans by blast
  then show "tw blk k V cs v" using X(1,3) by (auto simp: tw_def)
qed

lemma tw_cnf:
  fixes blk :: "nat \<Rightarrow> 'a set"
  assumes disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}"
    and sym: "\<forall>X\<subseteq>V. \<forall>Y\<subseteq>V. bw blk k X = bw blk k Y \<longrightarrow> cnf_val cs X = cnf_val cs Y"
  shows "\<forall>X\<subseteq>V. tw blk k V cs (bw blk k X) = cnf_val cs X"
proof (intro allI impI)
  fix X assume X: "X \<subseteq> V"
  show "tw blk k V cs (bw blk k X) = cnf_val cs X"
  proof
    assume "tw blk k V cs (bw blk k X)"
    then obtain X' where X': "X' \<subseteq> V" "\<forall>i<k. bw blk k X' i \<le> bw blk k X i" "cnf_val cs X'"
      by (auto simp: tw_def)
    have le: "\<forall>i<k. card (X' \<inter> blk i) \<le> card (X \<inter> blk i)" using X'(2) by (simp add: bw_def)
    obtain Y where Y: "Y \<subseteq> X" "\<forall>i<k. card (Y \<inter> blk i) = card (X' \<inter> blk i)"
      using sub_with_weights[OF disj le] by blast
    have "bw blk k Y = bw blk k X'" unfolding bw_def by (intro restrict_ext) (simp add: Y(2))
    moreover have YV: "Y \<subseteq> V" using Y(1) X by blast
    ultimately have "cnf_val cs Y = cnf_val cs X'" using sym X'(1) by blast
    then have "cnf_val cs Y" using X'(3) by simp
    then show "cnf_val cs X" using Y(1) by (auto simp: cnf_val_def)
  next
    assume "cnf_val cs X"
    then show "tw blk k V cs (bw blk k X)" using X by (auto simp: tw_def)
  qed
qed

lemma tw_sound:
  fixes blk :: "nat \<Rightarrow> 'a set"
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and sound: "\<forall>X\<subseteq>V. cnf_val cs X \<longrightarrow> N \<le> card X"
  shows "\<forall>u. tw blk k V cs u \<longrightarrow> N \<le> (\<Sum>i<k. u i)"
proof (intro allI impI)
  fix u assume "tw blk k V cs u"
  then obtain X where X: "X \<subseteq> V" "\<forall>i<k. bw blk k X i \<le> u i" "cnf_val cs X" by (auto simp: tw_def)
  have "N \<le> card X" using sound X by blast
  also have "\<dots> = (\<Sum>i<k. bw blk k X i)" by (rule card_blocks_sum[OF blk disj V X(1)])
  also have "\<dots> \<le> (\<Sum>i<k. u i)" using X(2) by (intro sum_mono) simp
  finally show "N \<le> (\<Sum>i<k. u i)" .
qed

subsection \<open>The count for a whole formula\<close>

theorem formula_kraft:
  fixes Fm :: "'a set set set" and blk :: "nat \<Rightarrow> 'a set" and \<delta> :: real
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and Fm: "finite Fm" "\<forall>cs\<in>Fm. finite cs"
    and sym: "\<forall>cs\<in>Fm. \<forall>X\<subseteq>V. \<forall>Y\<subseteq>V. bw blk k X = bw blk k Y \<longrightarrow> cnf_val cs X = cnf_val cs Y"
    and sound: "\<forall>cs\<in>Fm. \<forall>X\<subseteq>V. cnf_val cs X \<longrightarrow> N \<le> card X"
    and cover: "\<forall>X\<subseteq>V. card X = N \<longrightarrow> (\<exists>cs\<in>Fm. cnf_val cs X)"
    and size: "\<forall>cs\<in>Fm. card cs < \<beta> ^ (w + 1)" and w: "1 \<le> w" and beta: "1 < \<beta>"
    and lo: "1 \<le> lo" and range: "\<forall>x. lo - 1 \<le> x \<longrightarrow> x < hi \<longrightarrow> \<beta> \<le> b choose x"
    and \<delta>: "0 < \<delta>" "\<delta> < 1" and lam: "(1 - \<delta>) * (b choose (b div 2)) \<le> \<delta> * 2 ^ b"
  shows "real (card {X. X \<subseteq> V \<and> card X = N \<and> card (atyp k lo hi (bw blk k X)) \<le> a})
           * (\<delta> * 2 ^ b / ((1 - \<delta>) * (b choose (b div 2))))
               powr (real (k - a) * (w - 1) ^ (w - 1) / w ^ w)
         \<le> real (card Fm) * (2 ^ b / (1 - \<delta>)) ^ k"
proof -
  let ?p = "(\<delta> * 2 ^ b / ((1 - \<delta>) * (b choose (b div 2)))) powr (real (k - a) * (w - 1) ^ (w - 1) / w ^ w)"
  let ?K = "(2 ^ b / (1 - \<delta>)) ^ k"
  define S where "S cs = {X. X \<subseteq> V \<and> tw blk k V cs (bw blk k X) \<and> (\<Sum>i<k. bw blk k X i) = N
                          \<and> card (atyp k lo hi (bw blk k X)) \<le> a}" for cs
  let ?T = "{X. X \<subseteq> V \<and> card X = N \<and> card (atyp k lo hi (bw blk k X)) \<le> a}"
  have sub: "?T \<subseteq> (\<Union>cs\<in>Fm. S cs)"
  proof
    fix X assume X: "X \<in> ?T"
    then have XV: "X \<subseteq> V" and cX: "card X = N" by simp_all
    obtain cs where cs: "cs \<in> Fm" "cnf_val cs X" using cover XV cX by blast
    have "tw blk k V cs (bw blk k X)" using cs XV by (auto simp: tw_def)
    moreover have "(\<Sum>i<k. bw blk k X i) = N" using card_blocks_sum[OF blk disj V XV] cX by simp
    ultimately show "X \<in> (\<Union>cs\<in>Fm. S cs)" using X cs(1) by (auto simp: S_def)
  qed
  have finV: "finite V" using blk by (simp add: V)
  have finS: "finite (S cs)" for cs using finV by (auto simp: S_def intro: finite_subset[of _ "Pow V"])
  have each: "real (card (S cs)) * ?p \<le> ?K" if cs: "cs \<in> Fm" for cs
  proof -
    have fin: "finite cs" using Fm(2) cs by blast
    have cnf: "\<forall>X\<subseteq>V. tw blk k V cs (bw blk k X) = cnf_val cs X"
      by (rule tw_cnf[OF disj]) (use sym cs in blast)
    have snd: "\<forall>u. tw blk k V cs u \<longrightarrow> N \<le> (\<Sum>i<k. u i)"
      by (rule tw_sound[OF blk disj V]) (use sound cs in blast)
    have sz: "card cs < \<beta> ^ (w + 1)" using size cs by blast
    show ?thesis unfolding S_def
      by (rule wide_cover_kraft[OF tw_mono snd blk disj V fin cnf sz w beta lo range \<delta> lam])
  qed
  have "card ?T \<le> card (\<Union>cs\<in>Fm. S cs)" using sub finS Fm(1) by (intro card_mono) auto
  also have "\<dots> \<le> (\<Sum>cs\<in>Fm. card (S cs))" by (rule card_UN_le[OF Fm(1)])
  finally have cT: "card ?T \<le> (\<Sum>cs\<in>Fm. card (S cs))" .
  have "real (card ?T) \<le> (\<Sum>cs\<in>Fm. real (card (S cs)))" using of_nat_mono[OF cT] by simp
  then have "real (card ?T) * ?p \<le> (\<Sum>cs\<in>Fm. real (card (S cs))) * ?p" by (rule mult_right_mono) simp
  also have "\<dots> = (\<Sum>cs\<in>Fm. real (card (S cs)) * ?p)" by (rule sum_distrib_right)
  also have "\<dots> \<le> (\<Sum>cs\<in>Fm. ?K)" using each by (rule sum_mono)
  also have "\<dots> = real (card Fm) * ?K" by simp
  finally show ?thesis .
qed

subsection \<open>Inputs with many atypical blocks\<close>

lemma atypical_count:
  fixes blk :: "nat \<Rightarrow> 'a set"
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b" and V: "V = (\<Union>i<k. blk i)"
  shows "card {X. X \<subseteq> V \<and> a < card (atyp k lo hi (bw blk k X))}
           \<le> (k choose Suc a) * ((\<Sum>x\<in>{x. x \<le> b \<and> (x < lo \<or> hi < x)}. b choose x) ^ Suc a
                                * (2 ^ b) ^ (k - Suc a))"
proof -
  define At where "At = {x. x \<le> b \<and> (x < lo \<or> hi < x)}"
  define q where "q = (\<Sum>x\<in>At. b choose x)"
  define As where "As = {A. A \<subseteq> {..<k} \<and> card A = Suc a}"
  define S where "S A i = (if i \<in> A then At else {..b})" for A :: "nat set" and i
  define U where "U A = (\<Pi>\<^sub>E i\<in>{..<k}. S A i)" for A
  let ?M = "{X. X \<subseteq> V \<and> a < card (atyp k lo hi (bw blk k X))}"
  have finV: "finite V" using blk by (simp add: V)
  have finAs: "finite As" by (auto simp: As_def)
  have sub: "?M \<subseteq> (\<Union>A\<in>As. {X. X \<subseteq> V \<and> bw blk k X \<in> U A})"
  proof
    fix X assume X: "X \<in> ?M"
    then have XV: "X \<subseteq> V" and ca: "Suc a \<le> card (atyp k lo hi (bw blk k X))" by simp_all
    obtain A where A: "A \<subseteq> atyp k lo hi (bw blk k X)" "card A = Suc a"
      by (rule obtain_subset_with_card_n[OF ca])
    have box: "bw blk k X \<in> {..<k} \<rightarrow>\<^sub>E {..b}" by (rule bw_box[OF blk])
    have Ak: "A \<subseteq> {..<k}" using A(1) atyp_sub by blast
    have "bw blk k X \<in> U A"
    proof -
      have "bw blk k X i \<in> S A i" if i: "i < k" for i
      proof (cases "i \<in> A")
        case True
        then have "i \<in> atyp k lo hi (bw blk k X)" using A(1) by blast
        moreover have "bw blk k X i \<le> b" using PiE_mem[OF box, of i] i by simp
        ultimately show ?thesis using True by (auto simp: S_def At_def atyp_def)
      next
        case False
        then show ?thesis using PiE_mem[OF box, of i] i by (simp add: S_def)
      qed
      moreover have "bw blk k X i = undefined" if "i \<notin> {..<k}" for i
        using that by (simp add: bw_def)
      ultimately show ?thesis by (auto simp: U_def PiE_iff extensional_def)
    qed
    moreover have "A \<in> As" using Ak A(2) by (simp add: As_def)
    ultimately show "X \<in> (\<Union>A\<in>As. {X. X \<subseteq> V \<and> bw blk k X \<in> U A})" using XV by blast
  qed
  have each: "card {X. X \<subseteq> V \<and> bw blk k X \<in> U A} \<le> q ^ Suc a * (2 ^ b) ^ (k - Suc a)"
    if A: "A \<in> As" for A
  proof -
    have Ak: "A \<subseteq> {..<k}" and cA: "card A = Suc a" using A by (simp_all add: As_def)
    have finS: "finite (S A i)" for i by (simp add: S_def At_def)
    have finU: "finite (U A)" unfolding U_def using finS by (intro finite_PiE) simp_all
    have "card {X. X \<subseteq> V \<and> bw blk k X \<in> U A} \<le> (\<Sum>u\<in>U A. \<Prod>i<k. b choose u i)"
      by (rule inputs_count[OF blk V finU])
    also have "\<dots> = (\<Prod>i<k. \<Sum>x\<in>S A i. b choose x)"
      unfolding U_def by (rule prod_sum_PiE[symmetric]) (simp_all add: finS)
    also have "\<dots> = (\<Prod>i<k. if i \<in> A then q else 2 ^ b)"
      by (rule prod.cong) (simp_all add: S_def q_def choose_row_sum)
    also have "\<dots> = (\<Prod>i\<in>{..<k} \<inter> {i. i \<in> A}. q) * (\<Prod>i\<in>{..<k} \<inter> - {i. i \<in> A}. 2 ^ b)"
      by (rule prod.If_cases) simp
    also have "\<dots> = q ^ Suc a * (2 ^ b) ^ (k - Suc a)"
    proof -
      have e1: "{..<k} \<inter> {i. i \<in> A} = A" using Ak by blast
      have e2: "{..<k} \<inter> - {i. i \<in> A} = {..<k} - A" by blast
      have e3: "card ({..<k} - A) = k - Suc a" using Ak cA by (simp add: card_Diff_subset finite_subset)
      show ?thesis unfolding e1 e2 using cA e3 by simp
    qed
    finally show ?thesis .
  qed
  have "card ?M \<le> card (\<Union>A\<in>As. {X. X \<subseteq> V \<and> bw blk k X \<in> U A})"
    using sub finAs finV by (intro card_mono) (auto intro: finite_subset[of _ "Pow V"])
  also have "\<dots> \<le> (\<Sum>A\<in>As. card {X. X \<subseteq> V \<and> bw blk k X \<in> U A})" by (rule card_UN_le[OF finAs])
  also have "\<dots> \<le> (\<Sum>A\<in>As. q ^ Suc a * (2 ^ b) ^ (k - Suc a))" using each by (rule sum_mono)
  also have "\<dots> = card As * (q ^ Suc a * (2 ^ b) ^ (k - Suc a))" by simp
  also have "card As = k choose Suc a" unfolding As_def by (simp add: n_subsets)
  finally show ?thesis by (simp add: q_def At_def)
qed

text \<open>
  With the window \<open>[m - d, m + d]\<close>, \<open>d\<^sup>2 \<ge> 4b\<close> and \<open>a = k/2\<close>, at most \<open>2\<^sup>n / 2\<^sup>k\<close> inputs have more
  than \<open>a\<close> atypical blocks; with \<open>2(n+1) \<le> 2\<^sup>k\<close>, at least half of the Majority slice is typical.
\<close>

lemma typical_half:
  fixes blk :: "nat \<Rightarrow> 'a set"
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and m: "m = b div 2" and d: "4 * b \<le> d\<^sup>2" and b: "1 \<le> b"
    and k: "2 * (k * b + 1) \<le> 2 ^ k"
  shows "2 ^ (k * b) \<le> 2 * (k * b + 1)
           * card {X. X \<subseteq> V \<and> card X = (k * b) div 2 \<and> card (atyp k (m - d) (m + d) (bw blk k X)) \<le> k div 2}"
proof -
  define n where "n = k * b"
  define a where "a = k div 2"
  define q where "q = (\<Sum>x\<in>{x. x \<le> b \<and> (x < m - d \<or> m + d < x)}. b choose x)"
  let ?T = "{X. X \<subseteq> V \<and> card X = n div 2 \<and> card (atyp k (m - d) (m + d) (bw blk k X)) \<le> a}"
  let ?B = "{X. X \<subseteq> V \<and> a < card (atyp k (m - d) (m + d) (bw blk k X))}"
  let ?S = "{X. X \<subseteq> V \<and> card X = n div 2}"
  have finV: "finite V" using blk by (simp add: V)
  have cV: "card V = n" unfolding V n_def by (rule card_blocks[OF blk disj])
  have k1: "1 \<le> k" using k by (cases k) simp_all
  have ak: "Suc a \<le> k" using k1 by (simp add: a_def)
  text \<open>Few inputs have many atypical blocks.\<close>
  have q16: "16 * q \<le> 2 ^ b"
  proof -
    have "16 * q * b = 4 * q * (4 * b)" by simp
    also have "\<dots> \<le> 4 * q * d\<^sup>2" using d by (rule mult_left_mono) simp
    also have "\<dots> = 4 * d\<^sup>2 * q" by simp
    also have "\<dots> \<le> b * 2 ^ b" unfolding q_def by (rule chebyshev_window[OF m])
    also have "\<dots> = 2 ^ b * b" by simp
    finally show ?thesis using b by simp
  qed
  have cB: "card ?B \<le> (k choose Suc a) * (q ^ Suc a * (2 ^ b) ^ (k - Suc a))"
    unfolding q_def by (rule atypical_count[OF blk V])
  have "card ?B * 16 ^ Suc a \<le> (k choose Suc a) * ((16 * q) ^ Suc a * (2 ^ b) ^ (k - Suc a))"
    using cB by (simp add: power_mult_distrib algebra_simps)
  also have "\<dots> \<le> 2 ^ k * ((2 ^ b) ^ Suc a * (2 ^ b) ^ (k - Suc a))"
    using q16 by (intro mult_mono power_mono binomial_le_pow2) simp_all
  also have "(2 ^ b) ^ Suc a * (2 ^ b) ^ (k - Suc a) = (2::nat) ^ n"
  proof -
    have e: "Suc a + (k - Suc a) = k" using ak by simp
    have "((2::nat) ^ b) ^ Suc a * (2 ^ b) ^ (k - Suc a) = (2 ^ b) ^ k" by (simp only: power_add[symmetric] e)
    also have "\<dots> = 2 ^ n" by (simp add: power_mult[symmetric] n_def mult.commute)
    finally show ?thesis .
  qed
  finally have B16: "card ?B * 16 ^ Suc a \<le> 2 ^ k * 2 ^ n" .
  have "(4::nat) ^ k \<le> 4 ^ (2 * Suc a)" by (intro power_increasing) (simp_all add: a_def)
  also have "\<dots> = 16 ^ Suc a" by (simp add: power_mult)
  finally have "card ?B * 4 ^ k \<le> card ?B * 16 ^ Suc a" by simp
  then have c4: "card ?B * 4 ^ k \<le> 2 ^ k * 2 ^ n" using B16 by (rule le_trans)
  have four: "(4::nat) ^ k = 2 ^ k * 2 ^ k"
  proof -
    have "(4::nat) ^ k = (2 * 2) ^ k" by simp
    also have "\<dots> = 2 ^ k * 2 ^ k" by (rule power_mult_distrib)
    finally show ?thesis .
  qed
  have "card ?B * 2 ^ k * 2 ^ k = card ?B * 4 ^ k" by (simp only: four mult.assoc)
  also have "\<dots> \<le> 2 ^ k * 2 ^ n" by (rule c4)
  also have "\<dots> = 2 ^ n * 2 ^ k" by (rule mult.commute)
  finally have "card ?B * 2 ^ k * 2 ^ k \<le> 2 ^ n * 2 ^ k" .
  then have B: "card ?B * 2 ^ k \<le> 2 ^ n" by simp
  text \<open>The slice is covered by the typical inputs and the bad ones.\<close>
  have SU: "?S \<subseteq> ?T \<union> ?B" by auto
  have finT: "finite ?T" and finB: "finite ?B" using finV by (auto intro: finite_subset[of _ "Pow V"])
  have cS: "card ?S \<le> card ?T + card ?B"
    using card_mono[OF _ SU] card_Un_le[of ?T ?B] finT finB by simp
  have slice: "card ?S = n choose (n div 2)" using n_subsets[OF finV, of "n div 2"] cV by simp
  have P: "2 ^ n \<le> (n + 1) * card ?S" using slice_lower[of n] slice by simp
  define t where "t = card ?T"
  define c where "c = card ?B"
  define s where "s = card ?S"
  define r where "r = n + 1"
  have "2 ^ n * 2 ^ k \<le> r * s * 2 ^ k" using P by (simp add: r_def s_def)
  also have "\<dots> \<le> r * (t + c) * 2 ^ k" using cS by (simp add: s_def t_def c_def)
  also have "\<dots> = r * t * 2 ^ k + r * (c * 2 ^ k)" by (simp add: algebra_simps)
  also have "\<dots> \<le> r * t * 2 ^ k + r * 2 ^ n" using B by (simp add: c_def)
  finally have I: "2 ^ n * 2 ^ k \<le> r * t * 2 ^ k + r * 2 ^ n" .
  have "2 * r \<le> 2 ^ k" using k by (simp add: r_def n_def)
  then have "2 * r * 2 ^ n \<le> 2 ^ k * 2 ^ n" by (rule mult_right_mono) simp
  then have F: "2 * (r * 2 ^ n) \<le> 2 ^ n * 2 ^ k" by (simp only: ac_simps)
  have "2 ^ n * 2 ^ k \<le> 2 * (r * t * 2 ^ k)" using I F by linarith
  then have "2 ^ n * 2 ^ k \<le> (2 * r * t) * 2 ^ k" by (simp only: ac_simps)
  then have "2 ^ n \<le> 2 * r * t" by simp
  then show ?thesis by (simp add: r_def t_def n_def a_def)
qed

subsection \<open>Theorem E\<Zprime>, finite form\<close>

text \<open>
  Let a monotone formula for Majority on \<open>n = kb\<close> variables be an OR of block-symmetric
  monotone CNFs, each with fewer than \<open>\<beta>\<^sup>w\<^sup>+\<^sup>1\<close> clauses, where \<open>\<beta> = C(b, m - d - 1)\<close> is the
  smallest binomial coefficient of the window.  Then the number \<open>T\<close> of tests satisfies
  \<open>log\<^sub>2 T \<ge> (k / (2ew)) (\<frac>12 log\<^sub>2((3b+2)/2) - log\<^sub>2 w - 2e log\<^sub>2 e) - log\<^sub>2(2(n+1))\<close>.
  Here \<open>2e log\<^sub>2 e < 7.85\<close>.  The hypotheses: the window half-width \<open>d\<close> has \<open>d\<^sup>2 \<ge> 4b\<close>, the
  window stays inside \<open>[2, b - 2]\<close>, \<open>w C(b, b/2) \<le> 2\<^sup>b\<close> (otherwise the bound is negative anyway),
  and \<open>2(n+1) \<le> 2\<^sup>k\<close>.
\<close>

theorem majority_wide_tests:
  fixes Fm :: "'a set set set" and blk :: "nat \<Rightarrow> 'a set"
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and Fm: "finite Fm" "\<forall>cs\<in>Fm. finite cs"
    and sym: "\<forall>cs\<in>Fm. \<forall>X\<subseteq>V. \<forall>Y\<subseteq>V. bw blk k X = bw blk k Y \<longrightarrow> cnf_val cs X = cnf_val cs Y"
    and maj: "\<forall>X\<subseteq>V. (\<exists>cs\<in>Fm. cnf_val cs X) \<longleftrightarrow> (k * b) div 2 \<le> card X"
    and d: "4 * b \<le> d\<^sup>2" "d + 2 \<le> b div 2"
    and size: "\<forall>cs\<in>Fm. card cs < (b choose (b div 2 - d - 1)) ^ (w + 1)"
    and w: "1 \<le> w" "w * (b choose (b div 2)) \<le> 2 ^ b"
    and k: "2 * (k * b + 1) \<le> 2 ^ k"
  shows "real k / (2 * exp 1 * real w)
           * (log 2 ((3 * real b + 2) / 2) / 2 - log 2 (real w) - 2 * exp 1 * log 2 (exp 1))
         - log 2 (2 * (real (k * b) + 1))
         \<le> log 2 (real (card Fm))"
proof -
  define n where "n = k * b"
  define m where "m = b div 2"
  define a where "a = k div 2"
  define \<beta> where "\<beta> = b choose (m - d - 1)"
  define \<delta> :: real where "\<delta> = 1 / (real w + 1)"
  define C :: real where "C = real (b choose (b div 2))"
  define L :: real where "L = 2 ^ b / C"
  define lam :: real where "lam = \<delta> * 2 ^ b / ((1 - \<delta>) * C)"
  define y :: real where "y = real (k - a) * real (w - 1) ^ (w - 1) / real w ^ w"
  define T where "T = card {X. X \<subseteq> V \<and> card X = n div 2 \<and> card (atyp k (m - d) (m + d) (bw blk k X)) \<le> a}"
  have b4: "4 \<le> b" using d(2) by linarith
  have wpos: "0 < real w" using w(1) by simp
  have Cpos: "0 < C" by (simp add: C_def)
  have Lpos: "0 < L" using Cpos by (simp add: L_def)
  have d0: "0 < \<delta>" "\<delta> < 1" using wpos by (simp_all add: \<delta>_def)
  have d1: "1 - \<delta> = real w / (real w + 1)" using wpos by (simp add: \<delta>_def field_simps)
  have lamL: "lam = L / real w"
  proof -
    have dd: "\<delta> / (1 - \<delta>) = 1 / real w" using wpos by (simp add: d1 \<delta>_def field_simps)
    have "lam = \<delta> / (1 - \<delta>) * (2 ^ b / C)" unfolding lam_def by (rule times_divide_times_eq[symmetric])
    then show ?thesis by (simp add: dd L_def)
  qed
  have wC: "real w * C \<le> 2 ^ b" using of_nat_mono[OF w(2)] by (simp add: C_def)
  have lam1: "1 \<le> lam" using wC wpos Cpos by (simp add: lamL L_def field_simps)
  have lamc: "(1 - \<delta>) * real (b choose (b div 2)) \<le> \<delta> * 2 ^ b"
  proof -
    have "(1 - \<delta>) * real (b choose (b div 2)) = real w * C / (real w + 1)" by (simp add: d1 C_def)
    also have "\<dots> \<le> 2 ^ b / (real w + 1)" using wC wpos by (intro divide_right_mono) simp_all
    also have "\<dots> = \<delta> * 2 ^ b" by (simp add: \<delta>_def)
    finally show ?thesis .
  qed
  text \<open>The hypotheses of \<open>formula_kraft\<close>.\<close>
  have sound: "\<forall>cs\<in>Fm. \<forall>X\<subseteq>V. cnf_val cs X \<longrightarrow> n div 2 \<le> card X" using maj by (auto simp: n_def)
  have cover: "\<forall>X\<subseteq>V. card X = n div 2 \<longrightarrow> (\<exists>cs\<in>Fm. cnf_val cs X)" using maj by (auto simp: n_def)
  have size': "\<forall>cs\<in>Fm. card cs < \<beta> ^ (w + 1)" using size by (simp add: \<beta>_def m_def)
  have beta: "1 < \<beta>"
  proof -
    have "b choose 1 \<le> b choose (m - d - 1)" using d(2) by (intro binomial_mono) (simp_all add: m_def)
    then show ?thesis using b4 by (simp add: \<beta>_def)
  qed
  have lo: "1 \<le> m - d" using d(2) by (simp add: m_def)
  have range: "\<forall>x. m - d - 1 \<le> x \<longrightarrow> x < m + d \<longrightarrow> \<beta> \<le> b choose x"
    unfolding \<beta>_def by (rule window_range) (use d(2) in \<open>simp_all add: m_def\<close>)
  have FK: "real T * lam powr y \<le> real (card Fm) * (2 ^ b / (1 - \<delta>)) ^ k"
    using formula_kraft[OF blk disj V Fm sym sound cover size' w(1) beta lo range d0 lamc, of a]
    by (simp add: T_def lam_def C_def y_def)
  text \<open>At least \<open>2\<^sup>n / (2(n+1))\<close> slice inputs are typical.\<close>
  have TH: "2 ^ n \<le> 2 * (n + 1) * T"
    unfolding T_def n_def a_def by (rule typical_half[OF blk disj V m_def d(1) _ k]) (use b4 in simp)
  have TR: "2 ^ n / (2 * (real n + 1)) \<le> real T"
  proof -
    have "real (2 ^ n) \<le> real (2 * (n + 1) * T)" by (rule of_nat_mono[OF TH])
    then show ?thesis by (simp add: field_simps)
  qed
  text \<open>The factor \<open>(2\<^sup>b / (1 - \<delta>))\<^sup>k\<close>.\<close>
  have K: "(2 ^ b / (1 - \<delta>)) ^ k \<le> 2 ^ n * exp (real k / real w)"
  proof -
    have "2 ^ b / (1 - \<delta>) = 2 ^ b * (1 + 1 / real w)" using wpos by (simp add: d1 field_simps)
    then have "(2 ^ b / (1 - \<delta>)) ^ k = 2 ^ n * (1 + 1 / real w) ^ k"
      by (simp add: power_mult_distrib power_mult[symmetric] n_def mult.commute)
    also have "\<dots> \<le> 2 ^ n * exp (real k / real w)" using one_plus_power[OF w(1)] by simp
    finally show ?thesis .
  qed
  have lp: "0 < lam powr y" using lam1 by simp
  have main: "lam powr y \<le> real (card Fm) * (2 * (real n + 1) * exp (real k / real w))"
  proof -
    have "2 ^ n / (2 * (real n + 1)) * lam powr y \<le> real T * lam powr y"
      using TR lp by (intro mult_right_mono) simp_all
    also have "\<dots> \<le> real (card Fm) * (2 ^ b / (1 - \<delta>)) ^ k" by (rule FK)
    also have "\<dots> \<le> real (card Fm) * (2 ^ n * exp (real k / real w))" using K by (intro mult_left_mono) simp_all
    finally have H: "2 ^ n / (2 * (real n + 1)) * lam powr y \<le> real (card Fm) * (2 ^ n * exp (real k / real w))" .
    have "lam powr y = (2 * (real n + 1) / 2 ^ n) * (2 ^ n / (2 * (real n + 1)) * lam powr y)" by simp
    also have "\<dots> \<le> (2 * (real n + 1) / 2 ^ n) * (real (card Fm) * (2 ^ n * exp (real k / real w)))"
      using H by (rule mult_left_mono) simp
    also have "\<dots> = real (card Fm) * (2 * (real n + 1) * exp (real k / real w))" by simp
    finally show ?thesis .
  qed
  have Fpos: "0 < real (card Fm)"
  proof (rule ccontr)
    assume "\<not> 0 < real (card Fm)"
    then have "real (card Fm) = 0" by simp
    then show False using main lp by simp
  qed
  text \<open>Taking logarithms.\<close>
  have L1: "y * log 2 lam \<le> log 2 (real (card Fm)) + log 2 (2 * (real n + 1)) + real k / real w * log 2 (exp 1)"
  proof -
    have "y * log 2 lam = log 2 (lam powr y)" using lam1 by (simp add: log_powr)
    also have "\<dots> \<le> log 2 (real (card Fm) * (2 * (real n + 1) * exp (real k / real w)))"
      by (rule log_mono[OF _ lp main]) simp
    also have "\<dots> = log 2 (real (card Fm)) + log 2 (2 * (real n + 1)) + log 2 (exp (real k / real w))"
      using Fpos by (simp add: log_mult)
    also have "log 2 (exp (real k / real w)) = real k / real w * log 2 (exp 1)" by (simp add: log_def)
    finally show ?thesis .
  qed
  have yk: "real k / (2 * exp 1 * real w) \<le> y"
  proof -
    have ka: "real k / 2 \<le> real (k - a)" by (simp add: a_def)
    have fr: "1 / (exp 1 * real w) \<le> real (w - 1) ^ (w - 1) / real w ^ w"
      using decoded_fraction[OF w(1)] by simp
    have "real k / (2 * exp 1 * real w) = real k / 2 * (1 / (exp 1 * real w))" by simp
    also have "\<dots> \<le> real (k - a) * (real (w - 1) ^ (w - 1) / real w ^ w)"
      using ka fr by (intro mult_mono) simp_all
    also have "\<dots> = y" by (simp add: y_def)
    finally show ?thesis .
  qed
  have loglam: "log 2 ((3 * real b + 2) / 2) / 2 - log 2 (real w) \<le> log 2 lam"
  proof -
    have "log 2 ((3 * real b + 2) / 2) \<le> log 2 (L\<^sup>2)"
      using central_ratio[of b] by (simp add: L_def C_def)
    also have "\<dots> = 2 * log 2 L" using Lpos by (simp add: log_nat_power)
    finally have "log 2 ((3 * real b + 2) / 2) / 2 \<le> log 2 L" by simp
    moreover have "log 2 lam = log 2 L - log 2 (real w)" using Lpos wpos by (simp add: lamL log_divide)
    ultimately show ?thesis by simp
  qed
  have lg0: "0 \<le> log 2 lam" using lam1 by simp
  have "real k / (2 * exp 1 * real w)
          * (log 2 ((3 * real b + 2) / 2) / 2 - log 2 (real w) - 2 * exp 1 * log 2 (exp 1))
        = real k / (2 * exp 1 * real w) * (log 2 ((3 * real b + 2) / 2) / 2 - log 2 (real w))
          - real k / real w * log 2 (exp 1)"
    using wpos by (simp add: field_simps)
  also have "\<dots> \<le> real k / (2 * exp 1 * real w) * log 2 lam - real k / real w * log 2 (exp 1)"
    by (intro diff_right_mono mult_left_mono loglam) simp
  also have "\<dots> \<le> y * log 2 lam - real k / real w * log 2 (exp 1)"
    by (intro diff_right_mono mult_right_mono yk lg0)
  finally show ?thesis using L1 by (simp add: n_def)
qed

text \<open>
  Theorem E\<Zprime> in terms of the size alone.  If the formula has at most \<open>2\<^sup>z\<close> tests and every
  test at most \<open>2\<^sup>z\<close> clauses, take \<open>w = \<lfloor>z / log\<^sub>2 \<beta>\<rfloor> + 1\<close>: then every test has fewer than
  \<open>\<beta>\<^sup>w\<close> clauses.  The hypothesis \<open>w C(b, b/2) \<le> 2\<^sup>b\<close> of \<open>majority_wide_tests\<close> is not needed:
  when it fails, the bracket is negative and the bound is trivial.\<close>

lemma choose_ge_2: "1 \<le> j \<Longrightarrow> j < b \<Longrightarrow> 2 \<le> b choose j"
proof -
  assume j: "1 \<le> j" "j < b"
  obtain b' where b: "b = Suc b'" using j by (cases b) auto
  obtain j' where jj: "j = Suc j'" using j by (cases j) auto
  have p: "0 < b' choose j'" "0 < b' choose Suc j'" using j by (simp_all add: b jj)
  have "b choose j = (b' choose j') + (b' choose Suc j')" by (simp add: b jj)
  then show ?thesis using p by linarith
qed

theorem majority_wide_size:
  fixes Fm :: "'a set set set" and blk :: "nat \<Rightarrow> 'a set" and z :: real
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and Fm: "finite Fm" "\<forall>cs\<in>Fm. finite cs"
    and sym: "\<forall>cs\<in>Fm. \<forall>X\<subseteq>V. \<forall>Y\<subseteq>V. bw blk k X = bw blk k Y \<longrightarrow> cnf_val cs X = cnf_val cs Y"
    and maj: "\<forall>X\<subseteq>V. (\<exists>cs\<in>Fm. cnf_val cs X) \<longleftrightarrow> (k * b) div 2 \<le> card X"
    and d: "4 * b \<le> d\<^sup>2" "d + 2 \<le> b div 2"
    and k: "2 * (k * b + 1) \<le> 2 ^ k"
    and z: "0 \<le> z" "real (card Fm) \<le> 2 powr z" "\<forall>cs\<in>Fm. real (card cs) \<le> 2 powr z"
    and W: "W = z / log 2 (real (b choose (b div 2 - d - 1))) + 1"
  shows "real k / (2 * exp 1 * W)
           * (log 2 ((3 * real b + 2) / 2) / 2 - log 2 W - 2 * exp 1 * log 2 (exp 1))
         - log 2 (2 * (real (k * b) + 1))
         \<le> z"
proof -
  define \<beta> where "\<beta> = b choose (b div 2 - d - 1)"
  define lb where "lb = log 2 (real \<beta>)"
  define B where "B x = log 2 ((3 * real b + 2) / 2) / 2 - log 2 x - 2 * exp 1 * log 2 (exp 1)" for x :: real
  define Ln where "Ln = log 2 (2 * (real (k * b) + 1))"
  define w where "w = nat \<lfloor>z / lb\<rfloor> + 1"
  have b2: "2 \<le> \<beta>" unfolding \<beta>_def using d(2) by (intro choose_ge_2) simp_all
  have lb1: "1 \<le> lb"
  proof -
    have "log 2 2 \<le> log 2 (real \<beta>)" using b2 by (intro log_mono) simp_all
    then show ?thesis by (simp add: lb_def)
  qed
  have Wlb: "W = z / lb + 1" by (simp add: W lb_def \<beta>_def)
  have zl0: "0 \<le> z / lb" using z(1) lb1 by simp
  have wW: "real w \<le> W"
  proof -
    have "real (nat \<lfloor>z / lb\<rfloor>) \<le> z / lb" using zl0 by (simp add: of_nat_nat)
    then show ?thesis by (simp add: w_def Wlb)
  qed
  have w1: "1 \<le> w" by (simp add: w_def)
  have wpos: "0 < real w" using w1 by simp
  have Wpos: "0 < W" using wW wpos by simp
  have zw: "z < real w * lb"
  proof -
    have "z / lb < real w" using zl0 by (simp add: w_def of_nat_nat) linarith
    then show ?thesis using lb1 by (simp add: divide_less_eq mult.commute)
  qed
  have size: "\<forall>cs\<in>Fm. card cs < (b choose (b div 2 - d - 1)) ^ (w + 1)"
  proof
    fix cs assume cs: "cs \<in> Fm"
    have "real (card cs) \<le> 2 powr z" using z(3) cs by blast
    also have "\<dots> < 2 powr (real w * lb)" using zw by simp
    also have "\<dots> = (2 powr lb) ^ w" by (simp add: powr_powr[symmetric] powr_realpow mult.commute)
    also have "2 powr lb = real \<beta>" using b2 by (simp add: lb_def)
    finally have "real (card cs) < real (\<beta> ^ w)" by simp
    then have "card cs < \<beta> ^ w" by (simp only: of_nat_less_iff)
    also have "\<dots> \<le> \<beta> ^ (w + 1)" using b2 by (intro power_increasing) simp_all
    finally show "card cs < (b choose (b div 2 - d - 1)) ^ (w + 1)" by (simp add: \<beta>_def)
  qed
  have Ln0: "0 \<le> Ln"
  proof -
    have h: "\<And>x::real. 0 \<le> x \<Longrightarrow> 1 \<le> 2 * (x + 1)" by simp
    have "(1::real) \<le> 2 * (real (k * b) + 1)" by (rule h) (rule of_nat_0_le_iff)
    then have "log 2 1 \<le> Ln" unfolding Ln_def by (intro log_mono) simp_all
    then show ?thesis by simp
  qed
  have BW: "B W \<le> B (real w)" using wW wpos by (simp add: B_def)
  have Fz: "log 2 (real (card Fm)) \<le> z"
  proof -
    have "card V = (\<Sum>i<k. card (blk i))" unfolding V using blk disj by (intro card_UN_disjoint) auto
    also have "\<dots> = k * b" using blk by simp
    finally have "(k * b) div 2 \<le> card V" by simp
    then have "\<exists>cs\<in>Fm. cnf_val cs V" using maj by blast
    then have "1 \<le> real (card Fm)" using Fm(1) by (simp add: Suc_le_eq card_gt_0_iff) blast
    then have "log 2 (real (card Fm)) \<le> log 2 (2 powr z)" using z(2) by (intro log_mono) simp_all
    then show ?thesis by simp
  qed
  show ?thesis
  proof (cases "B W < 0")
    case True
    have "real k / (2 * exp 1 * W) * B W \<le> 0"
      using True Wpos by (intro mult_nonneg_nonpos) simp_all
    then show ?thesis using Ln0 z(1) by (simp add: B_def Ln_def)
  next
    case False
    then have BW0: "0 \<le> B W" by simp
    have wC: "w * (b choose (b div 2)) \<le> 2 ^ b"
    proof (rule ccontr)
      assume "\<not> w * (b choose (b div 2)) \<le> 2 ^ b"
      then have lt: "real (2 ^ b) < real (w * (b choose (b div 2)))" by (simp only: of_nat_less_iff not_le)
      define C where "C = real (b choose (b div 2))"
      have Cpos: "0 < C" by (simp add: C_def)
      have "2 ^ b / C < real w" using lt Cpos by (simp add: C_def divide_less_eq)
      then have "(2 ^ b / C)\<^sup>2 < (real w)\<^sup>2" using Cpos by (intro power_strict_mono) simp_all
      then have "(3 * real b + 2) / 2 < (real w)\<^sup>2" using central_ratio[of b] by (simp add: C_def)
      then have "log 2 ((3 * real b + 2) / 2) < log 2 ((real w)\<^sup>2)" by (intro log_less) simp_all
      also have "\<dots> = 2 * log 2 (real w)" using wpos by (simp add: log_nat_power)
      finally have lw: "log 2 ((3 * real b + 2) / 2) < 2 * log 2 (real w)" .
      have "0 < 2 * exp 1 * log 2 (exp 1)" by simp
      then have "B (real w) < 0" using lw unfolding B_def by linarith
      then show False using BW BW0 by simp
    qed
    have T: "real k / (2 * exp 1 * real w) * B (real w) - Ln \<le> log 2 (real (card Fm))"
      using majority_wide_tests[OF blk disj V Fm sym maj d size w1 wC k] by (simp add: B_def Ln_def)
    have "real k / (2 * exp 1 * W) * B W \<le> real k / (2 * exp 1 * real w) * B W"
      using wW wpos BW0 by (intro mult_right_mono divide_left_mono) simp_all
    also have "\<dots> \<le> real k / (2 * exp 1 * real w) * B (real w)"
      using BW by (intro mult_left_mono) simp_all
    finally have "real k / (2 * exp 1 * W) * B W - Ln \<le> z" using T Fz by linarith
    then show ?thesis by (simp add: B_def Ln_def)
  qed
qed

text \<open>The smallest binomial of the window, explicitly: \<open>log\<^sub>2 \<beta> \<ge> b - log\<^sub>2(b+1) - O(d\<^sup>2/b)\<close>.\<close>

lemma beta_log:
  assumes m: "m = b div 2" and j: "4 * (d + 1) \<le> m"
  shows "real b - log 2 (real b + 1) - 2 * real (d + 1) * real (d + 2) / (real m * ln 2)
           \<le> log 2 (real (b choose (m - d - 1)))"
proof -
  have "2 ^ b / (real b + 1) * exp (- 2 * real (d + 1) * (real (d + 1) + 1) / real m)
          \<le> real (b choose (m - (d + 1)))" by (rule window_beta[OF m j])
  then have le: "2 ^ b / (real b + 1) * exp (- 2 * real (d + 1) * real (d + 2) / real m)
          \<le> real (b choose (m - d - 1))" by (simp add: add.commute)
  have pos: "0 < 2 ^ b / (real b + 1) * exp (- 2 * real (d + 1) * real (d + 2) / real m)" by simp
  have "log 2 (2 ^ b / (real b + 1) * exp (- 2 * real (d + 1) * real (d + 2) / real m))
          = log 2 (2 ^ b) - log 2 (real b + 1) + log 2 (exp (- 2 * real (d + 1) * real (d + 2) / real m))"
    by (simp add: log_mult_pos log_divide_pos)
  also have "\<dots> = real b - log 2 (real b + 1) - 2 * real (d + 1) * real (d + 2) / (real m * ln 2)"
    by (simp add: log_nat_power) (simp add: algebra_simps minus_divide_left)
  moreover have "log 2 (2 ^ b / (real b + 1) * exp (- 2 * real (d + 1) * real (d + 2) / real m))
          \<le> log 2 (real (b choose (m - d - 1)))" by (rule log_mono[OF _ pos le]) simp
  ultimately show ?thesis by simp
qed

text \<open>A window of half-width \<open>d \<approx> 2\<surd>b\<close> exists once \<open>b \<ge> 300\<close>.\<close>

lemma window_d:
  fixes b :: nat
  assumes b: "300 \<le> b"
  shows "\<exists>d. 4 * b \<le> d\<^sup>2 \<and> (d + 1) * (d + 2) \<le> 5 * b \<and> 4 * (d + 1) \<le> b div 2"
proof -
  define s where "s = sqrt (real b)"
  define d where "d = nat \<lceil>2 * s\<rceil>"
  have s0: "0 \<le> s" by (simp add: s_def)
  have ss: "s * s = real b" by (simp add: s_def)
  have s17: "17 \<le> s"
  proof (rule ccontr)
    assume "\<not> 17 \<le> s"
    then have "s * s \<le> 17 * 17" using s0 by (intro mult_mono) simp_all
    then show False using ss b by simp
  qed
  have dlo: "2 * s \<le> real d" by (simp add: d_def real_nat_ceiling_ge)
  have dhi: "real d \<le> 2 * s + 1"
  proof -
    have "0 \<le> \<lceil>2 * s\<rceil>" using s0 by simp
    then have "real d = of_int \<lceil>2 * s\<rceil>" by (simp add: d_def)
    also have "\<dots> \<le> 2 * s + 1" by (rule of_int_ceiling_le_add_one)
    finally show ?thesis .
  qed
  have m: "real b - 1 \<le> 2 * real (b div 2)"
  proof -
    have "b \<le> 2 * (b div 2) + 1" by simp
    then have "real b \<le> real (2 * (b div 2) + 1)" by (simp only: of_nat_le_iff)
    then show ?thesis by simp
  qed
  have A: "4 * b \<le> d\<^sup>2"
  proof -
    have "(2 * s) * (2 * s) \<le> real d * real d" using dlo s0 by (intro mult_mono) simp_all
    then have "real (4 * b) \<le> real (d\<^sup>2)" using ss by (simp add: power2_eq_square)
    then show ?thesis by (simp only: of_nat_le_iff)
  qed
  have B: "(d + 1) * (d + 2) \<le> 5 * b"
  proof -
    have "(real d + 1) * (real d + 2) \<le> (2 * s + 2) * (2 * s + 3)" using dhi by (intro mult_mono) simp_all
    also have "\<dots> = 4 * (s * s) + 10 * s + 6" by (simp add: algebra_simps)
    also have "\<dots> \<le> 5 * (s * s)"
    proof -
      have "17 * s \<le> s * s" using s17 s0 by (intro mult_right_mono) simp_all
      then show ?thesis using s17 by linarith
    qed
    finally have "real ((d + 1) * (d + 2)) \<le> real (5 * b)" using ss by (simp add: algebra_simps)
    then show ?thesis by (simp only: of_nat_le_iff)
  qed
  have C: "4 * (d + 1) \<le> b div 2"
  proof -
    have "17 * s \<le> s * s" using s17 s0 by (intro mult_right_mono) simp_all
    then have "16 * s + 17 \<le> s * s" using s17 by linarith
    then have q: "16 * s + 16 \<le> s * s - 1" by linarith
    have "2 * (4 * (real d + 1)) = 8 * (real d + 1)" by simp
    also have "\<dots> \<le> 8 * (2 * s + 2)" using dhi by (intro mult_left_mono) simp_all
    also have "\<dots> = 16 * s + 16" by simp
    also have "\<dots> \<le> s * s - 1" by (rule q)
    also have "\<dots> = real b - 1" using ss by simp
    also have "\<dots> \<le> 2 * real (b div 2)" by (rule m)
    finally have "4 * (real d + 1) \<le> real (b div 2)" by simp
    then have "real (4 * (d + 1)) \<le> real (b div 2)" by simp
    then show ?thesis by (simp only: of_nat_le_iff)
  qed
  show ?thesis using A B C by blast
qed

lemma four_le_pow: "5 \<le> m \<Longrightarrow> 4 * m + 4 \<le> (2::nat) ^ m"
proof (induction m rule: nat_induct_at_least)
  case base
  then show ?case by simp
next
  case (Suc m)
  then show ?case by simp
qed

lemma ln2_ge_half: "1 / 2 \<le> ln (2::real)"
proof -
  have m: "1 / 2 \<le> exp (- (1 / 2 :: real))" using exp_ge_add_one_self[of "- (1 / 2 :: real)"] by simp
  have e: "exp (1 / 2 :: real) * exp (- (1 / 2)) = 1" by (rule exp_minus_inverse)
  have "exp (1 / 2 :: real) * (1 / 2) \<le> exp (1 / 2) * exp (- (1 / 2))"
    using m by (intro mult_left_mono) simp_all
  then have "exp (1 / 2 :: real) \<le> 2" using e by simp
  then show ?thesis by (simp add: ln_ge_iff[symmetric])
qed

text \<open>With such a window, \<open>log\<^sub>2 \<beta> \<ge> b/2\<close>.\<close>

lemma beta_half:
  assumes b: "300 \<le> b" and d: "(d + 1) * (d + 2) \<le> 5 * b" "4 * (d + 1) \<le> b div 2"
  shows "real b / 2 \<le> log 2 (real (b choose (b div 2 - d - 1)))"
proof -
  define m where "m = b div 2"
  have bl: "real b - log 2 (real b + 1) - 2 * real (d + 1) * real (d + 2) / (real m * ln 2)
              \<le> log 2 (real (b choose (m - d - 1)))"
    by (rule beta_log) (use d(2) in \<open>simp_all add: m_def\<close>)
  have mb: "real b \<le> 3 * real m"
  proof -
    have "b \<le> 3 * (b div 2)" using b by simp
    then show ?thesis by (simp add: m_def)
  qed
  have m0: "0 < real m" using b by (simp add: m_def)
  have l2: "1 / 2 \<le> ln (2::real)" by (rule ln2_ge_half)
  have corr: "2 * real (d + 1) * real (d + 2) / (real m * ln 2) \<le> 60"
  proof -
    have "2 * real (d + 1) * real (d + 2) = 2 * real ((d + 1) * (d + 2))"
      by (simp only: of_nat_mult mult.assoc)
    also have "\<dots> \<le> 2 * real (5 * b)" using d(1) by (simp only: of_nat_le_iff mult_le_cancel_left) simp
    also have "\<dots> \<le> 60 * (real m * (1 / 2))" using mb by simp
    also have "\<dots> \<le> 60 * (real m * ln 2)" using l2 m0 by (intro mult_left_mono) simp_all
    finally show ?thesis using m0 l2 by (simp add: divide_le_eq)
  qed
  have lg: "log 2 (real b + 1) \<le> real b / 4"
  proof -
    have "4 * (b div 4) + 4 \<le> 2 ^ (b div 4)" using b by (intro four_le_pow) simp
    moreover have "b + 1 \<le> 4 * (b div 4) + 4" by simp
    ultimately have "real (b + 1) \<le> real ((2::nat) ^ (b div 4))" by (simp only: of_nat_le_iff)
    then have "real b + 1 \<le> 2 ^ (b div 4)" by simp
    then have "log 2 (real b + 1) \<le> log 2 (2 ^ (b div 4))" by (intro log_mono) simp_all
    also have "\<dots> = real (b div 4)" by (simp add: log_nat_power)
    also have "\<dots> \<le> real b / 4" by (simp add: real_of_nat_div)
    finally show ?thesis .
  qed
  have "real b / 2 \<le> real b - log 2 (real b + 1) - 2 * real (d + 1) * real (d + 2) / (real m * ln 2)"
    using corr lg b by simp
  then show ?thesis using bl by (simp add: m_def)
qed

text \<open>
  Theorem E\<Zprime>, explicitly.  Put \<open>Z = max z b\<close>.  If \<open>b \<ge> 300\<close>, the formula has at most \<open>2\<^sup>z\<close>
  tests and every test at most \<open>2\<^sup>z\<close> clauses, then
  \<open>n (\<onehalf> log\<^sub>2((3b+2)/2) - log\<^sub>2(3Z/b) - 2e log\<^sub>2 e) \<le> 6e Z (Z + log\<^sub>2(2(n+1)))\<close>.
  For \<open>n\<^sup>\<alpha> \<le> b \<le> \<surd>(n log n)\<close> and \<open>\<alpha> > 1/3\<close> this forces \<open>z = \<Omega>(\<surd>((3\<alpha>-1) n log n))\<close>.\<close>

theorem majority_wide_explicit:
  fixes Fm :: "'a set set set" and blk :: "nat \<Rightarrow> 'a set" and z :: real
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}" and V: "V = (\<Union>i<k. blk i)"
    and Fm: "finite Fm" "\<forall>cs\<in>Fm. finite cs"
    and sym: "\<forall>cs\<in>Fm. \<forall>X\<subseteq>V. \<forall>Y\<subseteq>V. bw blk k X = bw blk k Y \<longrightarrow> cnf_val cs X = cnf_val cs Y"
    and maj: "\<forall>X\<subseteq>V. (\<exists>cs\<in>Fm. cnf_val cs X) \<longleftrightarrow> (k * b) div 2 \<le> card X"
    and b: "300 \<le> b" and k: "2 * (k * b + 1) \<le> 2 ^ k"
    and z: "real (card Fm) \<le> 2 powr z" "\<forall>cs\<in>Fm. real (card cs) \<le> 2 powr z"
    and Z: "Z = max z (real b)"
  shows "real (k * b) * (log 2 ((3 * real b + 2) / 2) / 2 - log 2 (3 * Z / real b)
           - 2 * exp 1 * log 2 (exp 1))
         \<le> 6 * exp 1 * Z * (Z + log 2 (2 * (real (k * b) + 1)))"
proof -
  obtain d where d: "4 * b \<le> d\<^sup>2" "(d + 1) * (d + 2) \<le> 5 * b" "4 * (d + 1) \<le> b div 2"
    using window_d[OF b] by blast
  have d2: "d + 2 \<le> b div 2" using d(3) by simp
  define lb where "lb = log 2 (real (b choose (b div 2 - d - 1)))"
  define W where "W = Z / lb + 1"
  define B where "B x = log 2 ((3 * real b + 2) / 2) / 2 - log 2 x - 2 * exp 1 * log 2 (exp 1)" for x :: real
  define Ln where "Ln = log 2 (2 * (real (k * b) + 1))"
  have lbh: "real b / 2 \<le> lb" unfolding lb_def by (rule beta_half[OF b d(2) d(3)])
  have b0: "0 < real b" using b by simp
  have lb0: "0 < lb" using lbh b0 by simp
  have Zb: "real b \<le> Z" and zZ: "z \<le> Z" by (simp_all add: Z)
  have Z0: "0 < Z" using Zb b0 by simp
  have zZ': "real (card Fm) \<le> 2 powr Z" "\<forall>cs\<in>Fm. real (card cs) \<le> 2 powr Z"
    using z zZ by (auto intro: order.trans)
  have Z0': "0 \<le> Z" using Z0 by simp
  have W': "W = Z / log 2 (real (b choose (b div 2 - d - 1))) + 1" by (simp add: W_def lb_def)
  have main: "real k / (2 * exp 1 * W) * B W - Ln \<le> Z"
    using majority_wide_size[OF blk disj V Fm sym maj d(1) d2 k Z0' zZ'(1) zZ'(2) W']
    unfolding B_def Ln_def .
  have W3: "W \<le> 3 * Z / real b"
  proof -
    have "Z / lb \<le> Z / (real b / 2)" using lbh b0 Z0 by (intro divide_left_mono) simp_all
    also have "\<dots> = 2 * Z / real b" by simp
    finally have "W \<le> 2 * Z / real b + 1" by (simp add: W_def)
    also have "1 \<le> Z / real b" using Zb b0 by simp
    then have "2 * Z / real b + 1 \<le> 3 * Z / real b" by simp
    finally show ?thesis .
  qed
  have "0 < Z / lb" using lb0 Z0 by simp
  then have Wpos: "0 < W" by (simp add: W_def)
  have Ln0: "0 \<le> Ln"
  proof -
    have h: "\<And>x::real. 0 \<le> x \<Longrightarrow> 1 \<le> 2 * (x + 1)" by simp
    have "(1::real) \<le> 2 * (real (k * b) + 1)" by (rule h) (rule of_nat_0_le_iff)
    then have "log 2 1 \<le> Ln" unfolding Ln_def by (intro log_mono) simp_all
    then show ?thesis by simp
  qed
  have BB: "B (3 * Z / real b) \<le> B W" using W3 Wpos by (simp add: B_def)
  show ?thesis
  proof (cases "B (3 * Z / real b) < 0")
    case True
    have "real (k * b) * B (3 * Z / real b) \<le> 0" using True by (intro mult_nonneg_nonpos) simp_all
    moreover have "0 \<le> 6 * exp 1 * Z * (Z + Ln)" using Z0 Ln0 by simp
    ultimately show ?thesis unfolding B_def Ln_def by linarith
  next
    case False
    then have B0: "0 \<le> B (3 * Z / real b)" by simp
    have kW: "real (k * b) / (6 * exp 1 * Z) \<le> real k / (2 * exp 1 * W)"
    proof -
      have "2 * exp 1 * W \<le> 2 * exp 1 * (3 * Z / real b)" using W3 by (intro mult_left_mono) simp_all
      then have "real k / (2 * exp 1 * (3 * Z / real b)) \<le> real k / (2 * exp 1 * W)"
        using Wpos Z0 b0 by (intro divide_left_mono mult_pos_pos) simp_all
      moreover have "real k / (2 * exp 1 * (3 * Z / real b)) = real (k * b) / (6 * exp 1 * Z)"
        using b0 by (simp add: field_simps)
      ultimately show ?thesis by simp
    qed
    have "real (k * b) / (6 * exp 1 * Z) * B (3 * Z / real b) \<le> real k / (2 * exp 1 * W) * B W"
      using kW BB B0 Wpos by (intro mult_mono) simp_all
    also have "\<dots> \<le> Z + Ln" using main by simp
    finally have "real (k * b) / (6 * exp 1 * Z) * B (3 * Z / real b) \<le> Z + Ln" .
    then have "real (k * b) * B (3 * Z / real b) \<le> (Z + Ln) * (6 * exp 1 * Z)"
      using Z0 by (simp add: divide_le_eq mult.commute)
    then show ?thesis by (simp add: B_def Ln_def algebra_simps)
  qed
qed

end
