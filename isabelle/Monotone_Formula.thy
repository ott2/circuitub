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

end
