theory Monotone_Cost
  imports Monotone_Pairs
begin

section \<open>The cost of monotone pairwise tests\<close>

text \<open>
  Two ingredients of the lower bound for monotone formulas of the L-R test shape
  (Theorem C of \<open>extensions/locality-and-monotonicity.md\<close>):
  \<^item> a sound test that covers a point \<open>p\<close> of the slice with \<open>p l \<ge> 1\<close> contains a pair CNF with
    at least \<open>C(b, p l - 1)\<close> clauses (\<open>test_cost\<close>), because a monotone CNF needs one clause per
    maximal false point (\<open>clause_per_maxfalse\<close>);
  \<^item> covering the slice needs at least \<open>C(kb, N)\<close> divided by the bound of Theorem B tests
    (\<open>tests_needed\<close>).
  The split into expensive and cheap tests and the optimisation over \<open>b\<close> remain on paper.
\<close>

subsection \<open>Lemma 4: a monotone CNF needs one clause per maximal false point\<close>

text \<open>Inputs are sets of true variables; a monotone clause is a set of variables.\<close>

definition cnf_val :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "cnf_val cs X \<longleftrightarrow> (\<forall>c\<in>cs. c \<inter> X \<noteq> {})"

definition maxfalse :: "'a set \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "maxfalse V f X \<longleftrightarrow> X \<subseteq> V \<and> \<not> f X \<and> (\<forall>Y. X \<subset> Y \<and> Y \<subseteq> V \<longrightarrow> f Y)"

lemma clause_per_maxfalse:
  assumes cs: "finite cs" and f: "\<forall>X\<subseteq>V. f X = cnf_val cs X"
  shows "card {X. maxfalse V f X} \<le> card cs"
proof -
  let ?M = "{X. maxfalse V f X}"
  have "\<forall>X\<in>?M. \<exists>c. c \<in> cs \<and> c \<inter> X = {}"
    using f by (auto simp: maxfalse_def cnf_val_def)
  from bchoice[OF this] obtain g where g: "\<forall>X\<in>?M. g X \<in> cs \<and> g X \<inter> X = {}" by blast
  have inj: "inj_on g ?M"
  proof (rule inj_onI)
    fix X Y assume X: "X \<in> ?M" and Y: "Y \<in> ?M" and eq: "g X = g Y"
    have XV: "X \<subseteq> V" and YV: "Y \<subseteq> V" using X Y by (simp_all add: maxfalse_def)
    have "g X \<inter> (X \<union> Y) = {}" using g X Y eq by blast
    moreover have "g X \<in> cs" using g X by blast
    ultimately have "\<not> cnf_val cs (X \<union> Y)" by (auto simp: cnf_val_def)
    then have nf: "\<not> f (X \<union> Y)" using f XV YV by simp
    show "X = Y"
    proof (rule ccontr)
      assume "X \<noteq> Y"
      then have "X \<subset> X \<union> Y \<or> Y \<subset> X \<union> Y" by blast
      moreover have "X \<union> Y \<subseteq> V" using XV YV by blast
      moreover have "\<forall>Z. X \<subset> Z \<and> Z \<subseteq> V \<longrightarrow> f Z" "\<forall>Z. Y \<subset> Z \<and> Z \<subseteq> V \<longrightarrow> f Z"
        using X Y by (simp_all add: maxfalse_def)
      ultimately have "f (X \<union> Y)" by blast
      with nf show False by simp
    qed
  qed
  have "g ` ?M \<subseteq> cs" using g by blast
  then show ?thesis using card_inj_on_le[OF inj _ cs] by blast
qed

subsection \<open>Block-symmetric pair functions\<close>

definition pairfun :: "'a set \<Rightarrow> 'a set \<Rightarrow> (nat \<times> nat) set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "pairfun A B P X \<longleftrightarrow> (card (X \<inter> A), card (X \<inter> B)) \<in> P"

text \<open>
  If \<open>(s, t)\<close> is a maximal false weight pair of an up-closed \<open>P\<close>, then every input with these
  block weights is a maximal false point of the Boolean pair function.
\<close>

lemma pair_maxfalse:
  assumes up: "upclosed P" and AB: "A \<inter> B = {}" "finite A" "finite B"
    and st: "(s, t) \<notin> P" "(Suc s, t) \<in> P" "t = card B \<or> (s, Suc t) \<in> P"
    and X: "X \<subseteq> A \<union> B" "card (X \<inter> A) = s" "card (X \<inter> B) = t"
  shows "maxfalse (A \<union> B) (pairfun A B P) X"
proof -
  have nf: "\<not> pairfun A B P X" using X st(1) by (simp add: pairfun_def)
  have upY: "pairfun A B P Y" if Y: "X \<subset> Y" "Y \<subseteq> A \<union> B" for Y
  proof -
    obtain y where y: "y \<in> Y" "y \<notin> X" using Y(1) by blast
    have finYA: "finite (Y \<inter> A)" and finYB: "finite (Y \<inter> B)" using AB by simp_all
    have geA: "s \<le> card (Y \<inter> A)" unfolding X(2)[symmetric] using Y(1) finYA by (intro card_mono) auto
    have geB: "t \<le> card (Y \<inter> B)" unfolding X(3)[symmetric] using Y(1) finYB by (intro card_mono) auto
    show ?thesis
    proof (cases "y \<in> A")
      case True
      have "insert y (X \<inter> A) \<subseteq> Y \<inter> A" using y True Y(1) by blast
      then have "card (insert y (X \<inter> A)) \<le> card (Y \<inter> A)" using finYA by (rule card_mono[rotated])
      moreover have "card (insert y (X \<inter> A)) = Suc s" using X(2) y(2) AB(2) by simp
      ultimately have "Suc s \<le> card (Y \<inter> A)" by simp
      then show ?thesis using up st(2) geB unfolding upclosed_def pairfun_def by blast
    next
      case False
      then have yB: "y \<in> B" using y Y(2) by blast
      have "insert y (X \<inter> B) \<subseteq> Y \<inter> B" using y yB Y(1) by blast
      then have "card (insert y (X \<inter> B)) \<le> card (Y \<inter> B)" using finYB by (rule card_mono[rotated])
      moreover have "card (insert y (X \<inter> B)) = Suc t" using X(3) y(2) AB(3) by simp
      ultimately have tY: "Suc t \<le> card (Y \<inter> B)" by simp
      have "card (Y \<inter> B) \<le> card B" using AB(3) by (intro card_mono) auto
      then have "(s, Suc t) \<in> P" using st(3) tY by auto
      then show ?thesis using up geA tY unfolding upclosed_def pairfun_def by blast
    qed
  qed
  show ?thesis using X(1) nf upY by (simp add: maxfalse_def)
qed

lemma pair_cost:
  assumes up: "upclosed P" and AB: "A \<inter> B = {}" "finite A" "finite B"
    and st: "(s, t) \<notin> P" "(Suc s, t) \<in> P" "t = card B \<or> (s, Suc t) \<in> P"
    and t: "t \<le> card B"
    and cs: "finite cs" "\<forall>X\<subseteq>A \<union> B. pairfun A B P X = cnf_val cs X"
  shows "card A choose s \<le> card cs"
proof -
  obtain T where T: "T \<subseteq> B" "card T = t" using obtain_subset_with_card_n[OF t] by metis
  let ?S = "{S. S \<subseteq> A \<and> card S = s}"
  let ?M = "{X. maxfalse (A \<union> B) (pairfun A B P) X}"
  have cS: "card ?S = card A choose s" using AB(2) by (rule n_subsets)
  have inj: "inj_on (\<lambda>S. S \<union> T) ?S"
  proof (rule inj_onI)
    fix S S' assume S: "S \<in> ?S" and S': "S' \<in> ?S" and eq: "S \<union> T = S' \<union> T"
    have "(S \<union> T) \<inter> A = (S' \<union> T) \<inter> A" using eq by simp
    then show "S = S'" using S S' T(1) AB(1) by blast
  qed
  have img: "(\<lambda>S. S \<union> T) ` ?S \<subseteq> ?M"
  proof
    fix X assume "X \<in> (\<lambda>S. S \<union> T) ` ?S"
    then obtain S where S: "S \<subseteq> A" "card S = s" "X = S \<union> T" by blast
    have XA: "X \<inter> A = S" using S T(1) AB(1) by blast
    have XB: "X \<inter> B = T" using S T(1) AB(1) by blast
    have "maxfalse (A \<union> B) (pairfun A B P) X"
      by (rule pair_maxfalse[OF up AB st]) (use S T XA XB in auto)
    then show "X \<in> ?M" by simp
  qed
  have fin: "finite ?M"
    by (rule finite_subset[of _ "Pow (A \<union> B)"]) (auto simp: maxfalse_def AB)
  have "card A choose s = card ((\<lambda>S. S \<union> T) ` ?S)" using inj cS by (simp add: card_image)
  also have "\<dots> \<le> card ?M" using img fin by (rule card_mono[rotated])
  also have "\<dots> \<le> card cs" by (rule clause_per_maxfalse[OF cs])
  finally show ?thesis .
qed

text \<open>Going up in the second coordinate turns a false pair below a true one into a maximal one.\<close>

lemma boundary:
  assumes up: "upclosed P" and st: "(s, t0) \<notin> P" "(Suc s, t0) \<in> P" and t0: "t0 \<le> b"
  shows "\<exists>t. t \<le> b \<and> (s, t) \<notin> P \<and> (Suc s, t) \<in> P \<and> (t = b \<or> (s, Suc t) \<in> P)"
proof -
  define U where "U = {u. t0 \<le> u \<and> u \<le> b \<and> (s, u) \<notin> P}"
  define t where "t = Max U"
  have fin: "finite U" by (rule finite_subset[of _ "{..b}"]) (auto simp: U_def)
  have "t0 \<in> U" using st t0 by (simp add: U_def)
  then have tU: "t \<in> U" unfolding t_def using fin by (intro Max_in) auto
  have tmax: "u \<le> t" if "u \<in> U" for u unfolding t_def using fin that by (rule Max_ge)
  have "(Suc s, t) \<in> P" using up st(2) tU unfolding upclosed_def U_def by blast
  moreover have "t = b \<or> (s, Suc t) \<in> P"
  proof (rule ccontr)
    assume neg: "\<not> (t = b \<or> (s, Suc t) \<in> P)"
    then have "Suc t \<in> U" using tU by (auto simp: U_def)
    then show False using tmax by fastforce
  qed
  ultimately show ?thesis using tU by (auto simp: U_def)
qed

lemma upclosed_converse: "upclosed P \<Longrightarrow> upclosed (P\<inverse>)"
  by (auto simp: upclosed_def)

lemma pairfun_converse: "pairfun A B (P\<inverse>) X = pairfun B A P X"
  by (simp add: pairfun_def)

subsection \<open>The cost of one test\<close>

text \<open>
  If a sound test accepts \<open>p\<close> on the slice and \<open>p l \<ge> 1\<close>, then it rejects \<open>p - e\<^sub>l\<close>, and some
  pair function involving \<open>l\<close> changes value there.
\<close>

lemma test_boundary:
  assumes sound: "\<forall>z. accepts k P z \<longrightarrow> N \<le> (\<Sum>i<k. z i)"
    and p: "accepts k P p" "(\<Sum>i<k. p i) = N" and l: "l < k" "0 < p l"
  shows "\<exists>j<k. j \<noteq> l \<and> (((p l - 1, p j) \<notin> P l j \<and> (p l, p j) \<in> P l j)
                       \<or> ((p j, p l - 1) \<notin> P j l \<and> (p j, p l) \<in> P j l))"
proof -
  define z where "z = p(l := p l - 1)"
  have "(\<Sum>i<k. z i) < (\<Sum>i<k. p i)" using l by (intro sum_strict_mono_ex1) (auto simp: z_def)
  then have "\<not> accepts k P z" using sound p(2) by fastforce
  then obtain i j where ij: "i < k" "j < k" "i \<noteq> j" "(z i, z j) \<notin> P i j"
    by (auto simp: accepts_def)
  have pij: "(p i, p j) \<in> P i j" using p(1) ij by (simp add: accepts_def)
  have "i = l \<or> j = l"
  proof (rule ccontr)
    assume "\<not> (i = l \<or> j = l)"
    then have "z i = p i" "z j = p j" by (simp_all add: z_def)
    then show False using ij(4) pij by simp
  qed
  then show ?thesis
  proof
    assume il: "i = l"
    then have "z i = p l - 1" "z j = p j" using ij(3) by (simp_all add: z_def)
    then show ?thesis using ij pij il by auto
  next
    assume jl: "j = l"
    then have "z i = p i" "z j = p l - 1" using ij(3) by (simp_all add: z_def)
    then show ?thesis using ij pij jl by auto
  qed
qed

text \<open>
  A test is given on Boolean inputs by blocks \<open>blk i\<close> of size \<open>b\<close> and, for each ordered pair of
  blocks, a monotone CNF \<open>cs i j\<close> computing the pair function \<open>P i j\<close>.  If it is sound and
  accepts a slice point \<open>p\<close> with \<open>p l \<ge> 1\<close>, one of these CNFs has \<open>C(b, p l - 1)\<close> clauses.
\<close>

theorem test_cost:
  assumes up: "\<forall>i j. upclosed (P i j)" and sound: "\<forall>z. accepts k P z \<longrightarrow> N \<le> (\<Sum>i<k. z i)"
    and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}"
    and cs: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> finite (cs i j) \<and>
               (\<forall>X\<subseteq>blk i \<union> blk j. pairfun (blk i) (blk j) (P i j) X = cnf_val (cs i j) X)"
    and p: "accepts k P p" "(\<Sum>i<k. p i) = N" "\<forall>i<k. p i \<le> b"
    and l: "l < k" "0 < p l"
  shows "\<exists>i<k. \<exists>j<k. i \<noteq> j \<and> b choose (p l - 1) \<le> card (cs i j)"
proof -
  have sl: "Suc (p l - 1) = p l" using l(2) by simp
  obtain j where j: "j < k" "j \<noteq> l"
    and c: "((p l - 1, p j) \<notin> P l j \<and> (p l, p j) \<in> P l j)
            \<or> ((p j, p l - 1) \<notin> P j l \<and> (p j, p l) \<in> P j l)"
    using test_boundary[OF sound p(1,2) l] by blast
  have Bl: "finite (blk l)" "card (blk l) = b" and Bj: "finite (blk j)" "card (blk j) = b"
    using blk l(1) j(1) by auto
  have pj: "p j \<le> b" using p(3) j(1) by blast
  from c show ?thesis
  proof
    assume c1: "(p l - 1, p j) \<notin> P l j \<and> (p l, p j) \<in> P l j"
    obtain t where t: "t \<le> b" "(p l - 1, t) \<notin> P l j" "(Suc (p l - 1), t) \<in> P l j"
        "t = b \<or> (p l - 1, Suc t) \<in> P l j"
      using boundary[of "P l j" "p l - 1" "p j" b] up c1 sl pj by auto
    have AB: "blk l \<inter> blk j = {}" using disj l(1) j by blast
    have csl: "finite (cs l j)"
      "\<forall>X\<subseteq>blk l \<union> blk j. pairfun (blk l) (blk j) (P l j) X = cnf_val (cs l j) X"
      using cs l(1) j by auto
    have "card (blk l) choose (p l - 1) \<le> card (cs l j)"
      by (rule pair_cost[OF _ AB Bl(1) Bj(1) t(2) t(3) _ _ csl]) (use up t Bj in auto)
    then show ?thesis using Bl(2) l(1) j by auto
  next
    assume c2: "(p j, p l - 1) \<notin> P j l \<and> (p j, p l) \<in> P j l"
    let ?Q = "(P j l)\<inverse>"
    have upQ: "upclosed ?Q" using up by (simp add: upclosed_converse)
    obtain t where t: "t \<le> b" "(p l - 1, t) \<notin> ?Q" "(Suc (p l - 1), t) \<in> ?Q"
        "t = b \<or> (p l - 1, Suc t) \<in> ?Q"
      using boundary[of ?Q "p l - 1" "p j" b] upQ c2 sl pj by auto
    have AB: "blk l \<inter> blk j = {}" using disj l(1) j by blast
    have csj: "finite (cs j l)"
      "\<forall>X\<subseteq>blk l \<union> blk j. pairfun (blk l) (blk j) ?Q X = cnf_val (cs j l) X"
      using cs l(1) j by (auto simp: pairfun_converse Un_commute)
    have "card (blk l) choose (p l - 1) \<le> card (cs j l)"
      by (rule pair_cost[OF upQ AB Bl(1) Bj(1) t(2) t(3) _ _ csj]) (use t Bj in auto)
    then show ?thesis using Bl(2) l(1) j by auto
  qed
qed

subsection \<open>The number of tests\<close>

text \<open>
  The weight vectors of the Majority slice account for all \<open>C(kb, N)\<close> inputs of weight \<open>N\<close>.
  Only the inequality is needed, and it avoids the Vandermonde identity: an input is
  determined by its intersections with the blocks.
\<close>

definition slice :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "slice k b N = {w \<in> {..<k} \<rightarrow>\<^sub>E {..b}. (\<Sum>i<k. w i) = N}"

lemma card_blocks:
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}"
  shows "card (\<Union>i<k. blk i) = k * b"
proof -
  have "card (\<Union>i<k. blk i) = (\<Sum>i<k. card (blk i))"
    using blk disj by (intro card_UN_disjoint) auto
  also have "\<dots> = (\<Sum>i<k. b)" using blk by (intro sum.cong) auto
  finally show ?thesis by simp
qed

lemma slice_count:
  assumes blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}"
  shows "(k * b) choose N \<le> (\<Sum>w\<in>slice k b N. \<Prod>i<k. b choose w i)"
proof -
  define V where "V = (\<Union>i<k. blk i)"
  define Xs where "Xs = {X. X \<subseteq> V \<and> card X = N}"
  define wv where "wv X = (\<lambda>i\<in>{..<k}. card (X \<inter> blk i))" for X
  define fib where "fib w = {X \<in> Xs. wv X = w}" for w
  have finV: "finite V" using blk by (auto simp: V_def)
  have cV: "card V = k * b" unfolding V_def by (rule card_blocks[OF blk disj])
  have finS: "finite (slice k b N)"
    by (rule finite_subset[of _ "{..<k} \<rightarrow>\<^sub>E {..b}"]) (auto simp: slice_def intro: finite_PiE)
  have inS: "wv X \<in> slice k b N" if X: "X \<in> Xs" for X
  proof -
    have XV: "X \<subseteq> V" and cX: "card X = N" using X by (simp_all add: Xs_def)
    have "card (X \<inter> blk i) \<le> b" if "i < k" for i
      using blk that card_mono[of "blk i" "X \<inter> blk i"] by auto
    then have box: "wv X \<in> {..<k} \<rightarrow>\<^sub>E {..b}" by (auto simp: wv_def)
    have "X = (\<Union>i<k. X \<inter> blk i)" using XV by (auto simp: V_def)
    then have "card X = card (\<Union>i<k. X \<inter> blk i)" by simp
    also have "\<dots> = (\<Sum>i<k. card (X \<inter> blk i))"
      using blk disj by (intro card_UN_disjoint) auto
    also have "\<dots> = (\<Sum>i<k. wv X i)" by (simp add: wv_def)
    finally show ?thesis using box cX by (simp add: slice_def)
  qed
  have each: "card (fib w) \<le> (\<Prod>i<k. b choose w i)" for w
  proof -
    let ?C = "\<Pi>\<^sub>E i\<in>{..<k}. {T. T \<subseteq> blk i \<and> card T = w i}"
    let ?g = "\<lambda>X. \<lambda>i\<in>{..<k}. X \<inter> blk i"
    have inj: "inj_on ?g (fib w)"
    proof (rule inj_onI)
      fix X Y assume X: "X \<in> fib w" and Y: "Y \<in> fib w" and eq: "?g X = ?g Y"
      have XV: "X \<subseteq> V" "Y \<subseteq> V" using X Y by (simp_all add: fib_def Xs_def)
      have "X \<inter> blk i = Y \<inter> blk i" if "i < k" for i
        using fun_cong[OF eq, of i] that by simp
      then have "(\<Union>i<k. X \<inter> blk i) = (\<Union>i<k. Y \<inter> blk i)" by simp
      moreover have "X = (\<Union>i<k. X \<inter> blk i)" "Y = (\<Union>i<k. Y \<inter> blk i)"
        using XV by (auto simp: V_def)
      ultimately show "X = Y" by simp
    qed
    have img: "?g ` fib w \<subseteq> ?C"
    proof
      fix G assume "G \<in> ?g ` fib w"
      then obtain X where X: "X \<in> fib w" "G = ?g X" by blast
      have "card (X \<inter> blk i) = w i" if "i < k" for i
        using X(1) that by (auto simp: fib_def wv_def)
      then show "G \<in> ?C" using X(2) by auto
    qed
    have finC: "finite ?C" using blk by (intro finite_PiE) auto
    have "card (fib w) = card (?g ` fib w)" using inj by (simp add: card_image)
    also have "\<dots> \<le> card ?C" using img finC by (rule card_mono[rotated])
    also have "\<dots> = (\<Prod>i<k. card {T. T \<subseteq> blk i \<and> card T = w i})" by (simp add: card_PiE)
    also have "\<dots> = (\<Prod>i<k. b choose w i)" using blk by (intro prod.cong) (auto simp: n_subsets)
    finally show ?thesis .
  qed
  have "(k * b) choose N = card Xs" using finV cV by (simp add: Xs_def n_subsets)
  also have "\<dots> \<le> card (\<Union>w\<in>slice k b N. fib w)"
  proof (rule card_mono)
    show "finite (\<Union>w\<in>slice k b N. fib w)"
      using finS finV by (auto simp: fib_def Xs_def intro: finite_subset[of _ "Pow V"])
    show "Xs \<subseteq> (\<Union>w\<in>slice k b N. fib w)" using inS by (auto simp: fib_def)
  qed
  also have "\<dots> \<le> (\<Sum>w\<in>slice k b N. card (fib w))" by (rule card_UN_le[OF finS])
  also have "\<dots> \<le> (\<Sum>w\<in>slice k b N. \<Prod>i<k. b choose w i)" using each by (intro sum_mono) blast
  finally show ?thesis .
qed

lemma sum_UN_le:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite I" "\<forall>i\<in>I. finite (A i)"
  shows "sum f (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. sum f (A i))"
  using assms
proof (induction I rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have finU: "finite (\<Union>i\<in>F. A i)" using insert by auto
  have "sum f (\<Union>i\<in>insert x F. A i) = sum f (A x \<union> (\<Union>i\<in>F. A i))" by simp
  also have "\<dots> \<le> sum f (A x) + sum f (\<Union>i\<in>F. A i)"
    using sum.union_inter[of "A x" "\<Union>i\<in>F. A i" f] insert finU by simp
  also have "\<dots> \<le> sum f (A x) + (\<Sum>i\<in>F. sum f (A i))" using insert by simp
  also have "\<dots> = (\<Sum>i\<in>insert x F. sum f (A i))" using insert by simp
  finally show ?case .
qed

text \<open>
  A family \<open>T\<close> of sound monotone pairwise tests that accepts every weight vector of the slice
  has at least \<open>C(kb, N) / (2\<^sup>k\<^sup>+\<^sup>1 (2\<^sup>b)\<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2 C(b, b/2)\<^sup>k \<^sup>- \<^sup>k \<^sup>d\<^sup>i\<^sup>v \<^sup>2)\<close> members (Theorem B).
\<close>

theorem tests_needed:
  assumes T: "finite T" and k: "2 \<le> k"
    and up: "\<forall>t\<in>T. \<forall>i j. upclosed (P t i j)"
    and sound: "\<forall>t\<in>T. \<forall>z. accepts k (P t) z \<longrightarrow> N \<le> (\<Sum>i<k. z i)"
    and cover: "\<forall>w\<in>slice k b N. \<exists>t\<in>T. accepts k (P t) w"
    and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}"
  shows "(k * b) choose N
           \<le> card T * (2 ^ (k + 1) * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2)))"
proof -
  define H where "H t = {w \<in> slice k b N. accepts k (P t) w}" for t
  define wt where "wt w = (\<Prod>i<k. b choose w i)" for w :: "nat \<Rightarrow> nat"
  define B where "B = 2 ^ (k + 1) * ((2 ^ b) ^ (k div 2) * (b choose (b div 2)) ^ (k - k div 2))"
  have finS: "finite (slice k b N)"
    by (rule finite_subset[of _ "{..<k} \<rightarrow>\<^sub>E {..b}"]) (auto simp: slice_def intro: finite_PiE)
  have finH: "\<forall>t\<in>T. finite (H t)" using finS by (auto simp: H_def)
  have each: "sum wt (H t) \<le> B" if t: "t \<in> T" for t
  proof -
    have v: "valid k N (H t)"
      by (rule test_valid[of "P t"]) (use up sound t in \<open>auto simp: H_def slice_def\<close>)
    have box: "H t \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" by (auto simp: H_def slice_def)
    show ?thesis using sharp_bounds(2)[OF v k box] by (simp add: wt_def B_def)
  qed
  have "(k * b) choose N \<le> sum wt (slice k b N)"
    using slice_count[OF blk disj] by (simp add: wt_def)
  also have "\<dots> \<le> sum wt (\<Union>t\<in>T. H t)"
    using cover finH T by (intro sum_mono2) (auto simp: H_def)
  also have "\<dots> \<le> (\<Sum>t\<in>T. sum wt (H t))" by (rule sum_UN_le[OF T finH])
  also have "\<dots> \<le> (\<Sum>t\<in>T. B)" using each by (intro sum_mono) blast
  also have "\<dots> = card T * B" by simp
  finally show ?thesis by (simp add: B_def)
qed

end
