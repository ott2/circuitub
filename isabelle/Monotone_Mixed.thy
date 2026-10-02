theory Monotone_Mixed
  imports Monotone_Cost
begin

section \<open>Monotone tests that mix two partitions\<close>

text \<open>
  The L-R tests contain pair checks for two partitions of the variables.  Here a test is an AND
  of monotone block-symmetric pair functions on the blocks \<open>A i\<close> (\<open>i < kA\<close>, size \<open>a\<close>) of one
  partition and on the blocks \<open>B j\<close> (\<open>j < kB\<close>, size \<open>b\<close>) of another: it accepts \<open>X\<close> iff the
  block-weight vectors \<open>bw A kA X\<close> and \<open>bw B kB X\<close> pass the pairwise up-closed constraints
  \<open>P\<close> and \<open>Q\<close>.

  A coordinate \<open>l\<close> of an accepted weight vector \<open>u\<close> is \<^emph>\<open>tight\<close> if lowering \<open>u l\<close> by one
  violates a constraint between \<open>l\<close> and some \<open>i\<close>.  Then \<open>u l\<close> is the threshold \<open>th P l i (u i)\<close>,
  and \<open>u l \<ge> th P l j (u j)\<close> for every \<open>j\<close>, so Theorem B's decoding applies to the tight
  coordinates of any accepted vector, without soundness (\<open>tight_compress\<close>).

  If the test is sound for Majority and accepts \<open>X\<close> of weight \<open>N\<close>, every \<open>e \<in> X\<close> lies in a
  tight \<open>A\<close>-block or a tight \<open>B\<close>-block (\<open>mixed_tight\<close>), so the tight blocks of one of the two
  partitions carry many ones, and that partition compresses (\<open>mixed_cover\<close>).  Every tight
  coordinate also costs \<open>C(b, u l - 1)\<close> clauses (\<open>tight_cost\<close>).
\<close>

subsection \<open>Tight coordinates and thresholds\<close>

definition tw :: "(nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "tw P u l i \<longleftrightarrow> 0 < u l \<and> ((u l - 1, u i) \<notin> P l i \<or> (u i, u l - 1) \<notin> P i l)"

definition tight :: "(nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "tight P k u = {l. l < k \<and> (\<exists>i<k. i \<noteq> l \<and> tw P u l i)}"

definition th :: "(nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "th P l i y = (LEAST x. (x, y) \<in> P l i \<and> (y, x) \<in> P i l)"

lemma th_le:
  assumes "accepts k P u" "l < k" "i < k" "i \<noteq> l"
  shows "th P l i (u i) \<le> u l"
  unfolding th_def by (rule Least_le) (use assms in \<open>auto simp: accepts_def\<close>)

lemma th_eq:
  assumes up: "\<forall>i j. upclosed (P i j)" and u: "accepts k P u"
    and l: "l < k" "i < k" "i \<noteq> l" and w: "tw P u l i"
  shows "u l = th P l i (u i)"
proof -
  let ?Q = "\<lambda>x. (x, u i) \<in> P l i \<and> (u i, x) \<in> P i l"
  have ex: "?Q (u l)" using u l by (auto simp: accepts_def)
  have Q: "?Q (th P l i (u i))" unfolding th_def by (rule LeastI[of ?Q, OF ex])
  have le: "th P l i (u i) \<le> u l" by (rule th_le[OF u l])
  show ?thesis
  proof (rule ccontr)
    assume "u l \<noteq> th P l i (u i)"
    then have lt: "th P l i (u i) \<le> u l - 1" using le by linarith
    have "upclosed (P l i)" "upclosed (P i l)" using up by simp_all
    then have "(u l - 1, u i) \<in> P l i" "(u i, u l - 1) \<in> P i l"
      using Q lt by (auto simp: upclosed_def)
    then show False using w by (simp add: tw_def)
  qed
qed

lemma lower_nontight:
  assumes u: "accepts k P u" and l: "l < k" "0 < u l" "l \<notin> tight P k u"
  shows "accepts k P (u(l := u l - 1))"
  unfolding accepts_def
proof (intro allI impI)
  fix p q assume pq: "p < k" "q < k" "p \<noteq> q"
  have nw: "(u l - 1, u i) \<in> P l i \<and> (u i, u l - 1) \<in> P i l" if "i < k" "i \<noteq> l" for i
    using l that by (auto simp: tight_def tw_def)
  show "((u(l := u l - 1)) p, (u(l := u l - 1)) q) \<in> P p q"
  proof (cases "p = l")
    case True
    then have "q \<noteq> l" using pq(3) by simp
    then show ?thesis using nw[OF pq(2)] True by simp
  next
    case pl: False
    show ?thesis
    proof (cases "q = l")
      case True
      then show ?thesis using nw[OF pq(1) pl] pl by simp
    next
      case False
      then show ?thesis using pl u pq by (simp add: accepts_def)
    qed
  qed
qed

subsection \<open>Decoding tight coordinates (Theorem B without validity)\<close>

definition tfree :: "(nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set"
  where "tfree P k r u = {l. l < k \<and> (\<forall>i<k. i \<noteq> l \<longrightarrow> tw P u l i \<longrightarrow> r l < r i)}"

lemma tfree_determined:
  assumes r: "inj_on r {..<k}" and up: "\<forall>i j. upclosed (P i j)"
    and p: "accepts k P p" and q: "accepts k P q"
    and box: "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" "q \<in> {..<k} \<rightarrow>\<^sub>E {..b}"
    and F: "tfree P k r p = tfree P k r q" and agree: "\<forall>l\<in>tfree P k r p. p l = q l"
  shows "p = q"
proof -
  have earlier: "\<exists>i<k. i \<noteq> l \<and> r i < r l \<and> tw P s l i"
    if s: "s = p \<or> s = q" and l: "l < k" "l \<notin> tfree P k r p" for s l
  proof -
    have "l \<notin> tfree P k r s" using s l F by auto
    then obtain i where i: "i < k" "i \<noteq> l" "tw P s l i" "\<not> r l < r i"
      using l(1) by (auto simp: tfree_def)
    have "r i \<noteq> r l" using r i(1,2) l(1) by (auto dest: inj_onD)
    then show ?thesis using i by auto
  qed
  have all: "\<forall>l<k. r l = m \<longrightarrow> p l = q l" for m
  proof (induction m rule: less_induct)
    case (less m)
    show ?case
    proof (intro allI impI)
      fix l assume l: "l < k" "r l = m"
      show "p l = q l"
      proof (cases "l \<in> tfree P k r p")
        case True
        then show ?thesis using agree by blast
      next
        case False
        obtain i where i: "i < k" "i \<noteq> l" "r i < r l" "tw P p l i"
          using earlier[of p l] l False by blast
        obtain j where j: "j < k" "j \<noteq> l" "r j < r l" "tw P q l j"
          using earlier[of q l] l False by blast
        have pi: "p i = q i" using less.IH[of "r i"] i l by simp
        have pj: "p j = q j" using less.IH[of "r j"] j l by simp
        have "p l = th P l i (p i)" by (rule th_eq[OF up p l(1) i(1,2,4)])
        also have "\<dots> = th P l i (q i)" using pi by simp
        also have "\<dots> \<le> q l" by (rule th_le[OF q l(1) i(1,2)])
        finally have le1: "p l \<le> q l" .
        have "q l = th P l j (q j)" by (rule th_eq[OF up q l(1) j(1,2,4)])
        also have "\<dots> = th P l j (p j)" using pj by simp
        also have "\<dots> \<le> p l" by (rule th_le[OF p l(1) j(1,2)])
        finally have "q l \<le> p l" .
        with le1 show ?thesis by simp
      qed
    qed
  qed
  have "p l = q l" if "l \<in> {..<k}" for l using all[of "r l"] that by blast
  then show "p = q" using box by (intro PiE_ext[of p "{..<k}" "\<lambda>_. {..b}" q]) auto
qed

text \<open>
  A tight coordinate is not free both in an order and in its reverse, so one of the two free
  sets has at most \<open>k - \<lceil>t/2\<rceil>\<close> elements when \<open>t\<close> coordinates are tight.
\<close>

lemma tfree_small:
  assumes t: "t \<le> card (tight P k u)"
  shows "card (tfree P k (\<lambda>i. i) u) \<le> k - (t - t div 2)
         \<or> card (tfree P k (\<lambda>i. k - i) u) \<le> k - (t - t div 2)"
proof -
  let ?A = "tfree P k (\<lambda>i. i) u" and ?B = "tfree P k (\<lambda>i. k - i) u" and ?T = "tight P k u"
  have AB: "?A \<inter> ?B \<subseteq> {..<k} - ?T"
  proof
    fix l assume l: "l \<in> ?A \<inter> ?B"
    then have lk: "l < k" by (simp add: tfree_def)
    show "l \<in> {..<k} - ?T"
    proof (rule ccontr)
      assume "l \<notin> {..<k} - ?T"
      then obtain i where i: "i < k" "i \<noteq> l" "tw P u l i" using lk by (auto simp: tight_def)
      have "l < i" using l i by (simp add: tfree_def)
      moreover have "k - l < k - i" using l i by (simp add: tfree_def)
      ultimately show False by simp
    qed
  qed
  have finA: "finite ?A" by (rule finite_subset[of _ "{..<k}"]) (auto simp: tfree_def)
  have finB: "finite ?B" by (rule finite_subset[of _ "{..<k}"]) (auto simp: tfree_def)
  have T: "?T \<subseteq> {..<k}" by (auto simp: tight_def)
  have cT: "card ?T \<le> k" using card_mono[OF _ T] by simp
  have "card (?A \<inter> ?B) \<le> card ({..<k} - ?T)" using AB by (intro card_mono) simp_all
  also have "\<dots> = k - card ?T" using T by (simp add: card_Diff_subset finite_subset)
  finally have I: "card (?A \<inter> ?B) \<le> k - card ?T" .
  have U: "card (?A \<union> ?B) \<le> k"
    using card_mono[of "{..<k}" "?A \<union> ?B"] by (auto simp: tfree_def)
  have "card ?A + card ?B = card (?A \<union> ?B) + card (?A \<inter> ?B)" by (rule card_Un_Int[OF finA finB])
  then have sum: "card ?A + card ?B + card ?T \<le> 2 * k" using I U cT by linarith
  define c where "c = t - t div 2"
  have c1: "c + t div 2 = t" by (simp add: c_def)
  have c2: "t = 2 * (t div 2) + t mod 2" "t mod 2 < 2" by simp_all
  have ck: "c \<le> k" using c1 t cT by linarith
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "k - c < card ?A" "k - c < card ?B" by (simp_all add: c_def)
    then show False using sum c1 c2 ck t by linarith
  qed
qed

theorem tight_compress:
  fixes k :: nat and blk :: "nat \<Rightarrow> 'a set"
  assumes up: "\<forall>i j. upclosed (P i j)"
    and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b" and V: "V = (\<Union>i<k. blk i)"
    and t: "t \<le> k"
  shows "card {X. X \<subseteq> V \<and> accepts k P (bw blk k X) \<and> t \<le> card (tight P k (bw blk k X))}
           \<le> 2 ^ (k + 1) * ((2 ^ b) ^ (k - (t - t div 2)) * (b choose (b div 2)) ^ (t - t div 2))"
proof -
  define c where "c = t - t div 2"
  define U where "U = {u \<in> {..<k} \<rightarrow>\<^sub>E {..b}. accepts k P u \<and> t \<le> card (tight P k u)}"
  define r where "r d = (if d then (\<lambda>i. i) else (\<lambda>i. k - i))" for d :: bool
  define I where "I = (UNIV :: bool set) \<times> {S. S \<subseteq> {..<k} \<and> card S \<le> k - c}"
  define Cl where "Cl a = {u \<in> U. tfree P k (r (fst a)) u = snd a}" for a :: "bool \<times> nat set"
  have ck: "c \<le> k" using t by (simp add: c_def)
  have finV: "finite V" using blk by (simp add: V)
  have box: "U \<subseteq> {..<k} \<rightarrow>\<^sub>E {..b}" by (auto simp: U_def)
  have finU: "finite U" using box by (rule finite_subset) (intro finite_PiE; simp)
  have rinj: "inj_on (r d) {..<k}" for d by (cases d) (auto simp: r_def inj_on_def)
  have I_sub: "I \<subseteq> UNIV \<times> Pow {..<k}" by (auto simp: I_def)
  have finI: "finite I" using I_sub by (rule finite_subset) simp
  have cardI: "card I \<le> 2 ^ (k + 1)"
  proof -
    have "card I \<le> card ((UNIV :: bool set) \<times> Pow {..<k})" by (rule card_mono[OF _ I_sub]) simp
    also have "\<dots> = 2 ^ (k + 1)" by (simp add: card_cartesian_product card_Pow)
    finally show ?thesis .
  qed
  have cover: "U \<subseteq> (\<Union>a\<in>I. Cl a)"
  proof
    fix u assume u: "u \<in> U"
    have "card (tfree P k (r True) u) \<le> k - c \<or> card (tfree P k (r False) u) \<le> k - c"
      using tfree_small[of t P k u] u by (simp add: U_def r_def c_def)
    then obtain d where d: "card (tfree P k (r d) u) \<le> k - c" by blast
    have "tfree P k (r d) u \<subseteq> {..<k}" by (auto simp: tfree_def)
    then have "(d, tfree P k (r d) u) \<in> I" using d by (simp add: I_def)
    moreover have "u \<in> Cl (d, tfree P k (r d) u)" using u by (simp add: Cl_def)
    ultimately show "u \<in> (\<Union>a\<in>I. Cl a)" by blast
  qed
  have sub: "\<forall>a\<in>I. Cl a \<subseteq> U" by (auto simp: Cl_def)
  have R: "\<forall>a\<in>I. snd a \<subseteq> {..<k} \<and> card (snd a) \<le> k - c" by (auto simp: I_def)
  have inj: "\<forall>a\<in>I. inj_on (\<lambda>p. restrict p (snd a)) (Cl a)"
  proof
    fix a assume "a \<in> I"
    show "inj_on (\<lambda>p. restrict p (snd a)) (Cl a)"
    proof (rule inj_onI)
      fix p q assume p: "p \<in> Cl a" and q: "q \<in> Cl a"
        and eq: "restrict p (snd a) = restrict q (snd a)"
      have pU: "p \<in> U" and qU: "q \<in> U" using p q by (auto simp: Cl_def)
      have Sp: "tfree P k (r (fst a)) p = snd a" and Sq: "tfree P k (r (fst a)) q = snd a"
        using p q by (simp_all add: Cl_def)
      have "\<forall>l\<in>snd a. p l = q l" using eq by (metis restrict_apply')
      then have ag: "\<forall>l\<in>tfree P k (r (fst a)) p. p l = q l" using Sp by simp
      have bp: "p \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and ap: "accepts k P p" using pU by (simp_all add: U_def)
      have bq: "q \<in> {..<k} \<rightarrow>\<^sub>E {..b}" and aq: "accepts k P q" using qU by (simp_all add: U_def)
      show "p = q" by (rule tfree_determined[OF rinj up ap aq bp bq _ ag]) (simp add: Sp Sq)
    qed
  qed
  have W: "(\<Sum>u\<in>U. \<Prod>i<k. b choose u i)
             \<le> card I * ((2 ^ b) ^ (k - c) * (b choose (b div 2)) ^ (k - (k - c)))"
    by (rule classes_gen[OF box finI cover sub R _ inj]) simp
  have kc: "k - (k - c) = c" using ck by simp
  let ?S = "{X. X \<subseteq> V \<and> accepts k P (bw blk k X) \<and> t \<le> card (tight P k (bw blk k X))}"
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
  also have "\<dots> \<le> card I * ((2 ^ b) ^ (k - c) * (b choose (b div 2)) ^ c)" using W by (simp add: kc)
  also have "\<dots> \<le> 2 ^ (k + 1) * ((2 ^ b) ^ (k - c) * (b choose (b div 2)) ^ c)"
    using cardI by (rule mult_right_mono) simp
  finally show ?thesis by (simp only: c_def)
qed

subsection \<open>Every one of a covered input lies in a tight block\<close>

lemma bw_remove:
  assumes blk: "\<forall>i<k. finite (blk i)" and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}"
    and e: "i < k" "e \<in> blk i" "e \<in> X"
  shows "bw blk k (X - {e}) = (bw blk k X)(i := bw blk k X i - 1)"
proof (rule ext)
  fix j
  show "bw blk k (X - {e}) j = ((bw blk k X)(i := bw blk k X i - 1)) j"
  proof (cases "j = i")
    case True
    have "(X - {e}) \<inter> blk i = (X \<inter> blk i) - {e}" by blast
    moreover have "finite (X \<inter> blk i)" using blk e(1) by simp
    ultimately show ?thesis using True e by (simp add: bw_def card_Diff_singleton)
  next
    case ji: False
    show ?thesis
    proof (cases "j < k")
      case True
      then have "e \<notin> blk j" using disj e ji by blast
      then have "(X - {e}) \<inter> blk j = X \<inter> blk j" by blast
      then show ?thesis using ji True by (simp add: bw_def)
    next
      case False
      then show ?thesis using ji by (simp add: bw_def)
    qed
  qed
qed

lemma mixed_tight:
  fixes A B :: "nat \<Rightarrow> 'a set"
  assumes blkA: "\<forall>i<kA. finite (A i)" and disjA: "\<forall>i<kA. \<forall>j<kA. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
    and VA: "V = (\<Union>i<kA. A i)"
    and blkB: "\<forall>j<kB. finite (B j)" and disjB: "\<forall>i<kB. \<forall>j<kB. i \<noteq> j \<longrightarrow> B i \<inter> B j = {}"
    and sound: "\<forall>Y\<subseteq>V. accepts kA P (bw A kA Y) \<and> accepts kB Q (bw B kB Y) \<longrightarrow> N \<le> card Y"
    and X: "X \<subseteq> V" "card X = N" "accepts kA P (bw A kA X)" "accepts kB Q (bw B kB X)"
    and e: "e \<in> X" "i < kA" "e \<in> A i" "j < kB" "e \<in> B j"
  shows "i \<in> tight P kA (bw A kA X) \<or> j \<in> tight Q kB (bw B kB X)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have nA: "i \<notin> tight P kA (bw A kA X)" and nB: "j \<notin> tight Q kB (bw B kB X)" by simp_all
  have finV: "finite V" using blkA VA by simp
  have finX: "finite X" using X(1) finV by (rule finite_subset)
  have posA: "0 < bw A kA X i"
  proof -
    have "X \<inter> A i \<noteq> {}" using e by blast
    then show ?thesis using blkA e(2) by (simp add: bw_def card_gt_0_iff)
  qed
  have posB: "0 < bw B kB X j"
  proof -
    have "X \<inter> B j \<noteq> {}" using e by blast
    then show ?thesis using blkB e(4) by (simp add: bw_def card_gt_0_iff)
  qed
  have aA: "accepts kA P (bw A kA (X - {e}))"
    unfolding bw_remove[OF blkA disjA e(2,3,1)] by (rule lower_nontight[OF X(3) e(2) posA nA])
  have aB: "accepts kB Q (bw B kB (X - {e}))"
    unfolding bw_remove[OF blkB disjB e(4,5,1)] by (rule lower_nontight[OF X(4) e(4) posB nB])
  have "N \<le> card (X - {e})" using sound aA aB X(1) by blast
  moreover have "card (X - {e}) < card X" using finX e(1) by (rule card_Diff1_less)
  ultimately show False using X(2) by simp
qed

lemma mixed_weight:
  fixes A B :: "nat \<Rightarrow> 'a set"
  assumes blkA: "\<forall>i<kA. finite (A i) \<and> card (A i) = a"
    and disjA: "\<forall>i<kA. \<forall>j<kA. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" and VA: "V = (\<Union>i<kA. A i)"
    and blkB: "\<forall>j<kB. finite (B j) \<and> card (B j) = b"
    and disjB: "\<forall>i<kB. \<forall>j<kB. i \<noteq> j \<longrightarrow> B i \<inter> B j = {}" and VB: "V = (\<Union>j<kB. B j)"
    and sound: "\<forall>Y\<subseteq>V. accepts kA P (bw A kA Y) \<and> accepts kB Q (bw B kB Y) \<longrightarrow> N \<le> card Y"
    and X: "X \<subseteq> V" "card X = N" "accepts kA P (bw A kA X)" "accepts kB Q (bw B kB X)"
  shows "card X \<le> card (tight P kA (bw A kA X)) * a + card (tight Q kB (bw B kB X)) * b"
proof -
  let ?TA = "tight P kA (bw A kA X)" and ?TB = "tight Q kB (bw B kB X)"
  have TA: "?TA \<subseteq> {..<kA}" and TB: "?TB \<subseteq> {..<kB}" by (auto simp: tight_def)
  have finTA: "finite ?TA" using TA by (rule finite_subset) simp
  have finTB: "finite ?TB" using TB by (rule finite_subset) simp
  have fA: "\<forall>i<kA. finite (A i)" and fB: "\<forall>j<kB. finite (B j)" using blkA blkB by simp_all
  have sub: "X \<subseteq> (\<Union>i\<in>?TA. A i) \<union> (\<Union>j\<in>?TB. B j)"
  proof
    fix e assume e: "e \<in> X"
    then have "e \<in> V" using X(1) by blast
    then obtain i j where ij: "i < kA" "e \<in> A i" "j < kB" "e \<in> B j" using VA VB by blast
    have "i \<in> ?TA \<or> j \<in> ?TB" by (rule mixed_tight[OF fA disjA VA fB disjB sound X e ij])
    then show "e \<in> (\<Union>i\<in>?TA. A i) \<union> (\<Union>j\<in>?TB. B j)" using ij by blast
  qed
  have cA: "card (\<Union>i\<in>?TA. A i) \<le> card ?TA * a"
  proof -
    have "card (\<Union>i\<in>?TA. A i) \<le> (\<Sum>i\<in>?TA. card (A i))" by (rule card_UN_le[OF finTA])
    also have "\<dots> = (\<Sum>i\<in>?TA. a)" using TA blkA by (intro sum.cong) auto
    finally show ?thesis by simp
  qed
  have cB: "card (\<Union>j\<in>?TB. B j) \<le> card ?TB * b"
  proof -
    have "card (\<Union>j\<in>?TB. B j) \<le> (\<Sum>j\<in>?TB. card (B j))" by (rule card_UN_le[OF finTB])
    also have "\<dots> = (\<Sum>j\<in>?TB. b)" using TB blkB by (intro sum.cong) auto
    finally show ?thesis by simp
  qed
  have finU: "finite ((\<Union>i\<in>?TA. A i) \<union> (\<Union>j\<in>?TB. B j))" using finTA finTB TA TB fA fB by auto
  have "card X \<le> card ((\<Union>i\<in>?TA. A i) \<union> (\<Union>j\<in>?TB. B j))" using finU sub by (rule card_mono)
  also have "\<dots> \<le> card (\<Union>i\<in>?TA. A i) + card (\<Union>j\<in>?TB. B j)" by (rule card_Un_le)
  finally show ?thesis using cA cB by linarith
qed

subsection \<open>Coverage of a mixed test\<close>

text \<open>
  If \<open>(tA - 1) a + (tB - 1) b < N\<close>, every covered input has at least \<open>tA\<close> tight \<open>A\<close>-blocks or
  at least \<open>tB\<close> tight \<open>B\<close>-blocks, and \<open>tight_compress\<close> bounds both kinds.  With
  \<open>tA = \<lceil>kA/4\<rceil>\<close> and \<open>tB = \<lceil>kB/4\<rceil>\<close>, the bound is \<open>2\<^sup>n\<close> times
  \<open>2\<^sup>k\<^sup>A\<^sup>+\<^sup>1 (\<pi>a/2)\<^sup>-\<^sup>k\<^sup>A\<^sup>/\<^sup>1\<^sup>6 + 2\<^sup>k\<^sup>B\<^sup>+\<^sup>1 (\<pi>b/2)\<^sup>-\<^sup>k\<^sup>B\<^sup>/\<^sup>1\<^sup>6\<close>.
\<close>

theorem mixed_cover:
  fixes A B :: "nat \<Rightarrow> 'a set"
  assumes upP: "\<forall>i j. upclosed (P i j)" and upQ: "\<forall>i j. upclosed (Q i j)"
    and blkA: "\<forall>i<kA. finite (A i) \<and> card (A i) = a"
    and disjA: "\<forall>i<kA. \<forall>j<kA. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" and VA: "V = (\<Union>i<kA. A i)"
    and blkB: "\<forall>j<kB. finite (B j) \<and> card (B j) = b"
    and disjB: "\<forall>i<kB. \<forall>j<kB. i \<noteq> j \<longrightarrow> B i \<inter> B j = {}" and VB: "V = (\<Union>j<kB. B j)"
    and sound: "\<forall>Y\<subseteq>V. accepts kA P (bw A kA Y) \<and> accepts kB Q (bw B kB Y) \<longrightarrow> N \<le> card Y"
    and t: "(tA - 1) * a + (tB - 1) * b < N" "tA \<le> kA" "tB \<le> kB"
  shows "card {X. X \<subseteq> V \<and> card X = N \<and> accepts kA P (bw A kA X) \<and> accepts kB Q (bw B kB X)}
           \<le> 2 ^ (kA + 1) * ((2 ^ a) ^ (kA - (tA - tA div 2)) * (a choose (a div 2)) ^ (tA - tA div 2))
             + 2 ^ (kB + 1) * ((2 ^ b) ^ (kB - (tB - tB div 2)) * (b choose (b div 2)) ^ (tB - tB div 2))"
proof -
  let ?C = "{X. X \<subseteq> V \<and> card X = N \<and> accepts kA P (bw A kA X) \<and> accepts kB Q (bw B kB X)}"
  let ?SA = "{X. X \<subseteq> V \<and> accepts kA P (bw A kA X) \<and> tA \<le> card (tight P kA (bw A kA X))}"
  let ?SB = "{X. X \<subseteq> V \<and> accepts kB Q (bw B kB X) \<and> tB \<le> card (tight Q kB (bw B kB X))}"
  have finV: "finite V" using blkA VA by simp
  have sub: "?C \<subseteq> ?SA \<union> ?SB"
  proof
    fix X assume "X \<in> ?C"
    then have Xs: "X \<subseteq> V" "card X = N" "accepts kA P (bw A kA X)" "accepts kB Q (bw B kB X)"
      by simp_all
    have w: "N \<le> card (tight P kA (bw A kA X)) * a + card (tight Q kB (bw B kB X)) * b"
      using mixed_weight[OF blkA disjA VA blkB disjB VB sound Xs] Xs(2) by simp
    show "X \<in> ?SA \<union> ?SB"
    proof (rule ccontr)
      assume "X \<notin> ?SA \<union> ?SB"
      then have "card (tight P kA (bw A kA X)) \<le> tA - 1" "card (tight Q kB (bw B kB X)) \<le> tB - 1"
        using Xs by auto
      then have "card (tight P kA (bw A kA X)) * a \<le> (tA - 1) * a"
        "card (tight Q kB (bw B kB X)) * b \<le> (tB - 1) * b" by (simp_all add: mult_right_mono)
      then show False using w t(1) by linarith
    qed
  qed
  have finS: "finite (?SA \<union> ?SB)" using finV by (auto intro: finite_subset[of _ "Pow V"])
  have "card ?C \<le> card (?SA \<union> ?SB)" using finS sub by (rule card_mono)
  also have "\<dots> \<le> card ?SA + card ?SB" by (rule card_Un_le)
  also have "\<dots> \<le> 2 ^ (kA + 1) * ((2 ^ a) ^ (kA - (tA - tA div 2)) * (a choose (a div 2)) ^ (tA - tA div 2))
             + 2 ^ (kB + 1) * ((2 ^ b) ^ (kB - (tB - tB div 2)) * (b choose (b div 2)) ^ (tB - tB div 2))"
    by (intro add_mono tight_compress[OF upP blkA VA t(2)] tight_compress[OF upQ blkB VB t(3)])
  finally show ?thesis .
qed

subsection \<open>The cost of a tight coordinate\<close>

text \<open>
  Soundness is not needed: if coordinate \<open>l\<close> of an accepted weight vector is tight, one pair CNF
  has at least \<open>C(b, u l - 1)\<close> clauses.
\<close>

theorem tight_cost:
  assumes up: "\<forall>i j. upclosed (P i j)"
    and blk: "\<forall>i<k. finite (blk i) \<and> card (blk i) = b"
    and disj: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> blk i \<inter> blk j = {}"
    and cs: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> finite (cs i j) \<and>
               (\<forall>X\<subseteq>blk i \<union> blk j. pairfun (blk i) (blk j) (P i j) X = cnf_val (cs i j) X)"
    and u: "accepts k P u" "\<forall>i<k. u i \<le> b" and l: "l \<in> tight P k u"
  shows "\<exists>i<k. \<exists>j<k. i \<noteq> j \<and> b choose (u l - 1) \<le> card (cs i j)"
proof -
  obtain j where j: "l < k" "j < k" "j \<noteq> l" "tw P u l j" using l by (auto simp: tight_def)
  have pos: "0 < u l" using j(4) by (simp add: tw_def)
  have "(u l, u j) \<in> P l j" "(u j, u l) \<in> P j l" using u(1) j(1-3) by (auto simp: accepts_def)
  then have c: "((u l - 1, u j) \<notin> P l j \<and> (u l, u j) \<in> P l j)
                \<or> ((u j, u l - 1) \<notin> P j l \<and> (u j, u l) \<in> P j l)"
    using j(4) by (auto simp: tw_def)
  have uj: "u j \<le> b" using u(2) j(2) by blast
  show ?thesis by (rule boundary_cost[OF up blk disj cs j(1) pos j(2,3) uj c])
qed

end
