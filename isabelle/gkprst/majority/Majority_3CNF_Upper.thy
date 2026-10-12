theory Majority_3CNF_Upper
  imports Majority_3CNF "HOL-Combinatorics.Permutations"
begin

section \<open>The matching upper bound: covering the slice with permuted copies\<close>

text \<open>
  The lower bound \<open>majority_mcnfs\<close> is tight up to a factor \<open>n + 1\<close>.  The paper cites this
  direction (Gurumukhani, Künnemann and Paturi 2024); here it is proved.  For any monotone
  3-CNF \<open>F\<close> with threshold \<open>t\<close> and \<open>T\<close> transversals of size \<open>t\<close>, permuted copies of \<open>F\<close>
  keep the threshold.  For a fixed \<open>t\<close>-set \<open>X\<close>, the image \<open>p ` X\<close> under a permutation \<open>p\<close> is
  equidistributed over the slice, so some copy covers a \<open>T/N\<close> fraction of any set of
  uncovered points (\<open>N = n choose t\<close>).  Greedily, \<open>(n+1) N / T + 1\<close> copies cover the slice,
  and their OR is the threshold-\<open>t\<close> function.  For Majority with \<open>4 \<le> n\<close> dividing \<open>n\<close>, disjoint
  copies of the 4-clique \<open>K\<^sub>4\<^sup>(\<^sup>3\<^sup>)\<close> give \<open>T = 6\<^bsup>n/4\<^esup>\<close>.
\<close>

subsection \<open>Permuted CNFs\<close>

definition pmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "pmap p F = (\<lambda>C. p ` C) ` F"

lemma hits_mono: "hits F X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> hits F Y"
  unfolding hits_def by blast

lemma hits_pmap_image:
  assumes "inj p"
  shows "hits (pmap p F) (p ` X) \<longleftrightarrow> hits F X"
proof -
  have i: "p ` C \<inter> p ` X = p ` (C \<inter> X)" for C using assms by (simp add: image_Int)
  show ?thesis unfolding hits_def pmap_def using i by auto
qed

lemma pmap_cnf:
  assumes p: "p permutes V" and F: "cnf V F"
  shows "cnf V (pmap p F)"
proof -
  have "D \<subseteq> V \<and> card D \<le> 3" if D: "D \<in> pmap p F" for D
  proof -
    obtain C where C: "C \<in> F" "D = p ` C" using D by (auto simp: pmap_def)
    have CV: "C \<subseteq> V" "card C \<le> 3" using F C(1) by (auto simp: cnf_def)
    have "p ` C \<subseteq> p ` V" using CV(1) by (rule image_mono)
    then have "D \<subseteq> V" using C(2) permutes_image[OF p] by simp
    moreover have "card D = card C"
      using C(2) card_image[OF permutes_inj_on[OF p]] by simp
    ultimately show ?thesis using CV(2) by simp
  qed
  moreover have "finite V" using F by (simp add: cnf_def)
  ultimately show ?thesis by (simp add: cnf_def)
qed

lemma pmap_thr:
  assumes p: "p permutes V" and F: "thr V F t"
  shows "thr V (pmap p F) t"
  unfolding thr_def
proof (intro allI impI)
  fix Y assume Y: "Y \<subseteq> V" and h: "hits (pmap p F) Y"
  define X where "X = inv p ` Y"
  have pX: "p ` X = Y"
  proof -
    have "p ` X = (p \<circ> inv p) ` Y" by (simp add: X_def image_comp)
    also have "\<dots> = Y" by (simp add: permutes_inv_o(1)[OF p])
    finally show ?thesis .
  qed
  have hX: "hits F X" using h hits_pmap_image[OF permutes_inj[OF p], of F X] pX by simp
  have "inv p ` Y \<subseteq> inv p ` V" using Y by (rule image_mono)
  then have XV: "X \<subseteq> V" using permutes_image[OF permutes_inv[OF p]] by (simp add: X_def)
  have "card Y = card X" using pX card_image[OF permutes_inj_on[OF p], of X] by simp
  then show "t \<le> card Y" using F XV hX by (simp add: thr_def)
qed

lemma pmap_trans:
  assumes p: "p permutes V" and X: "X \<in> trans V F t"
  shows "p ` X \<in> trans V (pmap p F) t"
proof -
  have X': "X \<subseteq> V" "hits F X" "card X = t" using X by (auto simp: trans_def)
  have "p ` X \<subseteq> p ` V" using X'(1) by (rule image_mono)
  then have "p ` X \<subseteq> V" using permutes_image[OF p] by simp
  moreover have "hits (pmap p F) (p ` X)" using hits_pmap_image[OF permutes_inj[OF p]] X'(2) by simp
  moreover have "card (p ` X) = t" using card_image[OF permutes_inj_on[OF p], of X] X'(3) by simp
  ultimately show ?thesis by (simp add: trans_def)
qed

subsection \<open>Permutations move a \<open>t\<close>-set uniformly over the slice\<close>

definition slice :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "slice A t = {X. X \<subseteq> A \<and> card X = t}"

lemma perm_slice:
  assumes p: "p permutes A" and X: "X \<in> slice A t"
  shows "p ` X \<in> slice A t"
proof -
  have "p ` X \<subseteq> p ` A" using X by (intro image_mono) (simp add: slice_def)
  then have "p ` X \<subseteq> A" using permutes_image[OF p] by simp
  moreover have "card (p ` X) = t" using card_image[OF permutes_inj_on[OF p], of X] X
    by (simp add: slice_def)
  ultimately show ?thesis by (simp add: slice_def)
qed

lemma perm_exists:
  assumes A: "finite A" and X: "X \<in> slice A t" and Y: "Y \<in> slice A t"
  obtains s where "s permutes A" "s ` X = Y"
proof -
  have XA: "X \<subseteq> A" "card X = t" and YA: "Y \<subseteq> A" "card Y = t" using X Y by (auto simp: slice_def)
  have fX: "finite X" "finite Y" using XA(1) YA(1) A by (auto intro: finite_subset)
  obtain f where f: "bij_betw f X Y" using finite_same_card_bij[OF fX] XA(2) YA(2) by auto
  have c: "card (A - X) = card (A - Y)"
    using card_Diff_subset[OF fX(1) XA(1)] card_Diff_subset[OF fX(2) YA(1)] XA(2) YA(2) by simp
  obtain g where g: "bij_betw g (A - X) (A - Y)"
    using finite_same_card_bij[of "A - X" "A - Y"] A c by auto
  define s where "s x = (if x \<in> X then f x else if x \<in> A then g x else x)" for x
  have sX: "bij_betw s X Y" using f by (rule bij_betw_cong[THEN iffD1, rotated]) (simp add: s_def)
  have sR: "bij_betw s (A - X) (A - Y)" using g by (rule bij_betw_cong[THEN iffD1, rotated]) (simp add: s_def)
  have "bij_betw s (X \<union> (A - X)) (Y \<union> (A - Y))" by (rule bij_betw_combine[OF sX sR]) blast
  moreover have "X \<union> (A - X) = A" using XA(1) by blast
  moreover have "Y \<union> (A - Y) = A" using YA(1) by blast
  ultimately have "bij_betw s A A" by simp
  moreover have "s x = x" if "x \<notin> A" for x using that XA(1) by (auto simp: s_def)
  ultimately have "s permutes A" by (rule bij_imp_permutes)
  moreover have "s ` X = Y" using sX by (simp add: bij_betw_def)
  ultimately show ?thesis by (rule that)
qed

lemma fiber_card:
  assumes A: "finite A" and X: "X \<in> slice A t" and Y: "Y \<in> slice A t"
  shows "card {p. p permutes A \<and> p ` X = Y} = card {p. p permutes A \<and> p ` X = X}"
proof -
  obtain s where s: "s permutes A" "s ` X = Y" by (rule perm_exists[OF A X Y])
  have iY: "inv s ` Y = X"
  proof -
    have "inv s ` Y = (inv s \<circ> s) ` X" by (simp only: image_comp[symmetric] s(2))
    also have "\<dots> = X" by (simp add: permutes_inv_o(2)[OF s(1)])
    finally show ?thesis .
  qed
  have "bij_betw (\<lambda>p. s \<circ> p) {p. p permutes A \<and> p ` X = X} {p. p permutes A \<and> p ` X = Y}"
  proof (rule bij_betw_byWitness[where f' = "\<lambda>q. inv s \<circ> q"])
    show "\<forall>p\<in>{p. p permutes A \<and> p ` X = X}. inv s \<circ> (s \<circ> p) = p"
      by (simp add: o_assoc permutes_inv_o(2)[OF s(1)])
    show "\<forall>q\<in>{p. p permutes A \<and> p ` X = Y}. s \<circ> (inv s \<circ> q) = q"
      by (simp add: o_assoc permutes_inv_o(1)[OF s(1)])
    show "(\<lambda>p. s \<circ> p) ` {p. p permutes A \<and> p ` X = X} \<subseteq> {p. p permutes A \<and> p ` X = Y}"
    proof
      fix q assume "q \<in> (\<lambda>p. s \<circ> p) ` {p. p permutes A \<and> p ` X = X}"
      then obtain p where p: "p permutes A" "p ` X = X" "q = s \<circ> p" by blast
      have "q permutes A" using permutes_compose[OF p(1) s(1)] p(3) by simp
      moreover have "q ` X = Y"
      proof -
        have "q ` X = s ` (p ` X)" by (simp only: p(3) image_comp)
        then show ?thesis using p(2) s(2) by simp
      qed
      ultimately show "q \<in> {p. p permutes A \<and> p ` X = Y}" by simp
    qed
    show "(\<lambda>q. inv s \<circ> q) ` {p. p permutes A \<and> p ` X = Y} \<subseteq> {p. p permutes A \<and> p ` X = X}"
    proof
      fix r assume "r \<in> (\<lambda>q. inv s \<circ> q) ` {p. p permutes A \<and> p ` X = Y}"
      then obtain q where q: "q permutes A" "q ` X = Y" "r = inv s \<circ> q" by blast
      have "r permutes A" using permutes_compose[OF q(1) permutes_inv[OF s(1)]] q(3) by simp
      moreover have "r ` X = X"
      proof -
        have "r ` X = inv s ` (q ` X)" by (simp only: q(3) image_comp)
        then show ?thesis using q(2) iY by simp
      qed
      ultimately show "r \<in> {p. p permutes A \<and> p ` X = X}" by simp
    qed
  qed
  then show ?thesis by (simp add: bij_betw_same_card)
qed

lemma fiber_sum:
  assumes A: "finite A" and X: "X \<in> slice A t" and U: "U \<subseteq> slice A t"
  shows "card {p. p permutes A \<and> p ` X \<in> U} = card U * card {p. p permutes A \<and> p ` X = X}"
proof -
  have finU: "finite U"
  proof (rule finite_subset[OF U])
    show "finite (slice A t)" unfolding slice_def using A by simp
  qed
  have fin: "finite {p. p permutes A \<and> p ` X = Y}" for Y
    by (rule finite_subset[OF _ finite_permutations[OF A]]) blast
  have eq: "{p. p permutes A \<and> p ` X \<in> U} = (\<Union>Y\<in>U. {p. p permutes A \<and> p ` X = Y})" by blast
  have "card (\<Union>Y\<in>U. {p. p permutes A \<and> p ` X = Y}) = (\<Sum>Y\<in>U. card {p. p permutes A \<and> p ` X = Y})"
    by (rule card_UN_disjoint[OF finU]) (use fin in auto)
  also have "\<dots> = (\<Sum>Y\<in>U. card {p. p permutes A \<and> p ` X = X})"
  proof (rule sum.cong[OF refl])
    fix Y assume "Y \<in> U"
    then have "Y \<in> slice A t" using U by blast
    then show "card {p. p permutes A \<and> p ` X = Y} = card {p. p permutes A \<and> p ` X = X}"
      by (rule fiber_card[OF A X])
  qed
  also have "\<dots> = card U * card {p. p permutes A \<and> p ` X = X}" by simp
  finally show ?thesis by (simp only: eq)
qed

text \<open>Hence \<open>#{p. p ` X \<in> U} \<cdot> N = |U| \<cdot> #perms\<close>.\<close>

lemma fiber_ratio:
  assumes A: "finite A" and X: "X \<in> slice A t" and U: "U \<subseteq> slice A t"
  shows "card {p. p permutes A \<and> p ` X \<in> U} * card (slice A t) = card U * card {p. p permutes A}"
proof -
  have all: "{p. p permutes A \<and> p ` X \<in> slice A t} = {p. p permutes A}"
    using perm_slice[OF _ X] by blast
  have "card {p. p permutes A} = card (slice A t) * card {p. p permutes A \<and> p ` X = X}"
    using fiber_sum[OF A X order_refl] by (simp only: all)
  then show ?thesis using fiber_sum[OF A X U] by simp
qed

subsection \<open>Averaging: some copy covers its share\<close>

lemma card_filter_sum:
  assumes "finite S"
  shows "card {x\<in>S. Q x} = (\<Sum>x\<in>S. if Q x then 1 else 0)"
proof -
  have "card {x\<in>S. Q x} = (\<Sum>x\<in>{x\<in>S. Q x}. 1)" by (rule card_eq_sum)
  also have "\<dots> = (\<Sum>x\<in>S. if Q x then 1 else 0)" by (rule sum.inter_filter[OF assms])
  finally show ?thesis .
qed

lemma good_perm:
  assumes A: "finite A" and S: "S \<subseteq> slice A t" and U: "U \<subseteq> slice A t"
  obtains p where "p permutes A" "card S * card U \<le> card {X\<in>S. p ` X \<in> U} * card (slice A t)"
proof -
  define P where "P = {p. p permutes A}"
  define N where "N = card (slice A t)"
  have finP: "finite P" unfolding P_def by (rule finite_permutations[OF A])
  have finS: "finite S"
  proof (rule finite_subset[OF S])
    show "finite (slice A t)" unfolding slice_def using A by simp
  qed
  have idP: "id \<in> P" by (simp add: P_def permutes_id)
  have sw: "(\<Sum>p\<in>P. card {X\<in>S. p ` X \<in> U}) = (\<Sum>X\<in>S. card {p\<in>P. p ` X \<in> U})"
  proof -
    have "(\<Sum>p\<in>P. card {X\<in>S. p ` X \<in> U}) = (\<Sum>p\<in>P. \<Sum>X\<in>S. if p ` X \<in> U then 1 else 0)"
      by (rule sum.cong[OF refl]) (rule card_filter_sum[OF finS])
    also have "\<dots> = (\<Sum>X\<in>S. \<Sum>p\<in>P. if p ` X \<in> U then 1 else 0)" by (rule sum.swap)
    also have "\<dots> = (\<Sum>X\<in>S. card {p\<in>P. p ` X \<in> U})"
      by (rule sum.cong[OF refl]) (rule card_filter_sum[OF finP, symmetric])
    finally show ?thesis .
  qed
  have each: "card {p\<in>P. p ` X \<in> U} * N = card U * card P" if X: "X \<in> S" for X
  proof -
    have "{p\<in>P. p ` X \<in> U} = {p. p permutes A \<and> p ` X \<in> U}" by (simp add: P_def)
    then show ?thesis using fiber_ratio[OF A _ U, of X] X S by (auto simp: P_def N_def)
  qed
  have tot: "(\<Sum>p\<in>P. card {X\<in>S. p ` X \<in> U} * N) = card S * card U * card P"
  proof -
    have "(\<Sum>p\<in>P. card {X\<in>S. p ` X \<in> U} * N) = (\<Sum>p\<in>P. card {X\<in>S. p ` X \<in> U}) * N"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>X\<in>S. card {p\<in>P. p ` X \<in> U} * N)" by (simp add: sw sum_distrib_right)
    also have "\<dots> = (\<Sum>X\<in>S. card U * card P)" by (rule sum.cong[OF refl]) (rule each)
    finally show ?thesis by simp
  qed
  have "\<exists>p\<in>P. card S * card U \<le> card {X\<in>S. p ` X \<in> U} * N"
  proof (rule ccontr)
    assume "\<not> (\<exists>p\<in>P. card S * card U \<le> card {X\<in>S. p ` X \<in> U} * N)"
    then have lt: "\<forall>p\<in>P. card {X\<in>S. p ` X \<in> U} * N < card S * card U" by (simp add: not_le)
    have "(\<Sum>p\<in>P. card {X\<in>S. p ` X \<in> U} * N) < (\<Sum>p\<in>P. card S * card U)"
      by (rule sum_strict_mono[OF finP]) (use idP lt in auto)
    then show False using tot by (simp add: mult.commute)
  qed
  then obtain p where "p \<in> P" "card S * card U \<le> card {X\<in>S. p ` X \<in> U} * N" by blast
  then show ?thesis using that by (simp add: P_def N_def)
qed

end
