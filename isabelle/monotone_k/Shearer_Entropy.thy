theory Shearer_Entropy
  imports Shearer_Sub
begin

text \<open>
  Shearer's lemma for a uniform member \<open>X\<close> of a finite family \<open>F\<close> of subsets of \<open>{..<n}\<close>.
  \<open>cls F B X\<close> counts the members agreeing with \<open>X\<close> on \<open>B\<close>, and
  \<open>ent F B = ln |F| - (1/|F|) \<Sum>\<^sub>X ln (cls F B X)\<close> is the entropy (in nats) of the trace \<open>X \<inter> B\<close>.
  \<open>ent_sub\<close> is submodularity, proved from \<open>ln y \<le> y - 1\<close> and a class-counting bound; with
  \<open>shearer_sub\<close> it gives \<open>shearer_ent\<close>: \<open>ln |F| \<le> \<Sum>\<^sub>B w B * ent F B\<close> for every fractional cover.
\<close>

definition cls :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> nat" where
  "cls F B X = card {Y\<in>F. Y \<inter> B = X \<inter> B}"

definition ent :: "'a set set \<Rightarrow> 'a set \<Rightarrow> real" where
  "ent F B = ln (real (card F)) - (\<Sum>X\<in>F. ln (real (cls F B X))) / real (card F)"

lemma cls_pos:
  assumes "finite F" "X \<in> F"
  shows "0 < real (cls F B X)"
proof -
  have "X \<in> {Y\<in>F. Y \<inter> B = X \<inter> B}" using assms(2) by blast
  moreover have "finite {Y\<in>F. Y \<inter> B = X \<inter> B}" using assms(1) by simp
  ultimately have "0 < card {Y\<in>F. Y \<inter> B = X \<inter> B}" using card_gt_0_iff by blast
  then show ?thesis unfolding cls_def by simp
qed

lemma ent_empty: "ent F {} = 0"
proof (cases "card F = 0")
  case True
  then show ?thesis unfolding ent_def by simp
next
  case False
  have c: "cls F {} X = card F" for X unfolding cls_def by simp
  have "(\<Sum>X\<in>F. ln (real (cls F {} X))) = real (card F) * ln (real (card F))"
    unfolding c by simp
  then show ?thesis unfolding ent_def using False by simp
qed

lemma ent_full:
  assumes "finite F" "F \<subseteq> Pow V"
  shows "ent F V = ln (real (card F))"
proof -
  have "cls F V X = 1" if X: "X \<in> F" for X
  proof -
    have "{Y\<in>F. Y \<inter> V = X \<inter> V} = {X}" using assms(2) X by blast
    then show ?thesis unfolding cls_def by simp
  qed
  then have "(\<Sum>X\<in>F. ln (real (cls F V X))) = 0" by simp
  then show ?thesis unfolding ent_def by simp
qed

lemma ent_mono:
  assumes fin: "finite F" and B: "B \<subseteq> B'"
  shows "ent F B \<le> ent F B'"
proof (cases "F = {}")
  case True
  then show ?thesis unfolding ent_def by simp
next
  case False
  have "ln (real (cls F B' X)) \<le> ln (real (cls F B X))" if X: "X \<in> F" for X
  proof -
    have "{Y\<in>F. Y \<inter> B' = X \<inter> B'} \<subseteq> {Y\<in>F. Y \<inter> B = X \<inter> B}" using B by blast
    then have "cls F B' X \<le> cls F B X" unfolding cls_def by (rule card_mono[rotated]) (use fin in simp)
    then show ?thesis using cls_pos[OF fin X, of B'] by simp
  qed
  then have s: "(\<Sum>X\<in>F. ln (real (cls F B' X))) \<le> (\<Sum>X\<in>F. ln (real (cls F B X)))" by (rule sum_mono)
  have "0 < real (card F)" using False fin by (simp add: card_gt_0_iff)
  then have "(\<Sum>X\<in>F. ln (real (cls F B' X))) / real (card F) \<le> (\<Sum>X\<in>F. ln (real (cls F B X))) / real (card F)"
    by (intro divide_right_mono[OF s]) simp
  then show ?thesis unfolding ent_def by linarith
qed

lemma sum_split_pred:
  assumes "finite K"
  shows "sum f K = sum f {Y\<in>K. P Y} + sum f {Y\<in>K. \<not> P Y}"
proof -
  have "sum f ({Y\<in>K. P Y} \<union> {Y\<in>K. \<not> P Y}) = sum f {Y\<in>K. P Y} + sum f {Y\<in>K. \<not> P Y}"
    by (rule sum.union_disjoint) (use assms in auto)
  moreover have "{Y\<in>K. P Y} \<union> {Y\<in>K. \<not> P Y} = K" by blast
  ultimately show ?thesis by simp
qed

lemma const_sum_le:
  fixes q :: "'x \<Rightarrow> real"
  assumes "finite K" "0 \<le> c" "\<forall>X\<in>K. q X = c / real (card K)"
  shows "sum q K \<le> c"
proof (cases "K = {}")
  case True
  then show ?thesis using assms(2) by simp
next
  case False
  then have "0 < card K" using assms(1) by (simp add: card_gt_0_iff)
  have "sum q K = real (card K) * (c / real (card K))" using assms(3) by simp
  also have "\<dots> = c" using \<open>0 < card K\<close> by simp
  finally show ?thesis by simp
qed

lemma block_sum:
  fixes q :: "'x \<Rightarrow> real"
  assumes fK: "finite K" and c: "0 \<le> c1" "0 \<le> c2"
    and q: "\<forall>X\<in>K. q X = (if P X then c1 / real (card {Y\<in>K. P Y}) else c2 / real (card {Y\<in>K. \<not> P Y}))"
  shows "sum q K \<le> c1 + c2"
proof -
  have "sum q {Y\<in>K. P Y} \<le> c1" by (rule const_sum_le) (use fK c q in auto)
  moreover have "sum q {Y\<in>K. \<not> P Y} \<le> c2" by (rule const_sum_le) (use fK c q in auto)
  ultimately show ?thesis using sum_split_pred[OF fK, of q P] by linarith
qed

lemma ins_eq:
  assumes "i \<notin> A"
  shows "(Y \<inter> insert i A = X \<inter> insert i A) \<longleftrightarrow> (Y \<inter> A = X \<inter> A \<and> (i \<in> Y \<longleftrightarrow> i \<in> X))"
  using assms unfolding set_eq_iff by blast

lemma count_bound:
  assumes fin: "finite F" and AA: "A \<subseteq> A'" and i: "i \<notin> A'"
  shows "(\<Sum>X\<in>F. real (cls F (insert i A) X) * real (cls F A' X)
            / (real (cls F A X) * real (cls F (insert i A') X))) \<le> real (card F)"
proof -
  define q where "q X = real (cls F (insert i A) X) * real (cls F A' X)
            / (real (cls F A X) * real (cls F (insert i A') X))" for X
  define K where "K T = {X\<in>F. X \<inter> A' = T}" for T
  have iA: "i \<notin> A" using AA i by blast
  have blk: "sum q (K T) \<le> real (card (K T))" if T: "T \<in> (\<lambda>X. X \<inter> A') ` F" for T
  proof -
    define L where "L = {Y\<in>F. Y \<inter> A = T \<inter> A}"
    obtain X0 where X0: "X0 \<in> F" "X0 \<inter> A' = T" using T by blast
    have X0L: "X0 \<in> L" unfolding L_def using X0 AA by blast
    have fL: "finite L" unfolding L_def using fin by simp
    have Lpos: "0 < real (card L)" using X0L fL by (auto simp: card_gt_0_iff)
    have fK: "finite (K T)" unfolding K_def using fin by simp
    define c1 where "c1 = real (card (K T)) * real (card {Y\<in>L. i \<in> Y}) / real (card L)"
    define c2 where "c2 = real (card (K T)) * real (card {Y\<in>L. i \<notin> Y}) / real (card L)"
    have qX: "q X = (if i \<in> X then c1 / real (card {Y\<in>K T. i \<in> Y})
                     else c2 / real (card {Y\<in>K T. i \<notin> Y}))" if X: "X \<in> K T" for X
    proof -
      have XF: "X \<in> F" and XT: "X \<inter> A' = T" using X unfolding K_def by auto
      have XA: "X \<inter> A = T \<inter> A" using XT AA by blast
      have eb: "cls F A' X = card (K T)" unfolding cls_def K_def XT ..
      have ea: "cls F A X = card L" unfolding cls_def L_def XA ..
      have "{Y\<in>F. Y \<inter> insert i A' = X \<inter> insert i A'} = {Y\<in>K T. (i \<in> Y) = (i \<in> X)}"
        unfolding K_def by (auto simp: ins_eq[OF i] XT)
      then have ebi: "cls F (insert i A') X = card {Y\<in>K T. (i \<in> Y) = (i \<in> X)}"
        unfolding cls_def by simp
      have "{Y\<in>F. Y \<inter> insert i A = X \<inter> insert i A} = {Y\<in>L. (i \<in> Y) = (i \<in> X)}"
        unfolding L_def by (auto simp: ins_eq[OF iA] XA)
      then have eai: "cls F (insert i A) X = card {Y\<in>L. (i \<in> Y) = (i \<in> X)}"
        unfolding cls_def by simp
      show ?thesis
        unfolding q_def c1_def c2_def ea eb eai ebi
        by (cases "i \<in> X") (simp_all add: divide_divide_eq_left ac_simps)
    qed
    have c1: "0 \<le> c1" "0 \<le> c2" unfolding c1_def c2_def by simp_all
    have le: "sum q (K T) \<le> c1 + c2"
      by (rule block_sum[OF fK c1, where P = "\<lambda>Y. i \<in> Y"]) (use qX in simp)
    have sp: "real (card {Y\<in>L. i \<in> Y}) + real (card {Y\<in>L. i \<notin> Y}) = real (card L)"
      using sum_split_pred[OF fL, of "\<lambda>_. (1::real)" "\<lambda>Y. i \<in> Y"] by simp
    have e: "c1 + c2 = real (card (K T)) * (real (card {Y\<in>L. i \<in> Y}) + real (card {Y\<in>L. i \<notin> Y})) / real (card L)"
      unfolding c1_def c2_def by (simp add: add_divide_distrib distrib_left)
    have "c1 + c2 = real (card (K T))" unfolding e sp using Lpos by simp
    then show ?thesis using le by simp
  qed
  have "(\<Sum>X\<in>F. q X) = (\<Sum>T\<in>(\<lambda>X. X \<inter> A') ` F. sum q (K T))"
    unfolding K_def by (rule sum.image_gen[OF fin])
  also have "\<dots> \<le> (\<Sum>T\<in>(\<lambda>X. X \<inter> A') ` F. real (card (K T)))" by (rule sum_mono) (rule blk)
  also have "\<dots> = (\<Sum>T\<in>(\<lambda>X. X \<inter> A') ` F. \<Sum>X\<in>K T. (1::real))" by simp
  also have "\<dots> = (\<Sum>X\<in>F. (1::real))" unfolding K_def by (rule sum.image_gen[OF fin, symmetric])
  also have "\<dots> = real (card F)" by simp
  finally show ?thesis unfolding q_def .
qed

lemma ln_quad:
  fixes a ai b bi :: real
  assumes "0 < a" "0 < ai" "0 < b" "0 < bi"
  shows "1 - ai * b / (a * bi) \<le> ln a + ln bi - ln ai - ln b"
proof -
  define y where "y = ai * b / (a * bi)"
  have y0: "0 < y" unfolding y_def using assms by simp
  have "ln y = ln ai + ln b - ln a - ln bi"
    unfolding y_def using assms by (simp add: ln_div ln_mult)
  moreover have "ln y \<le> y - 1" by (rule ln_le_minus_one[OF y0])
  ultimately show ?thesis unfolding y_def by linarith
qed

theorem ent_sub:
  assumes fin: "finite F" and AA: "A \<subseteq> A'" and i: "i \<notin> A'"
  shows "ent F (insert i A') - ent F A' \<le> ent F (insert i A) - ent F A"
proof (cases "F = {}")
  case True
  then show ?thesis unfolding ent_def by simp
next
  case False
  define a where "a X = real (cls F A X)" for X
  define ai where "ai X = real (cls F (insert i A) X)" for X
  define b where "b X = real (cls F A' X)" for X
  define bi where "bi X = real (cls F (insert i A') X)" for X
  have N: "0 < real (card F)" using False fin by (simp add: card_gt_0_iff)
  have pt: "1 - ai X * b X / (a X * bi X) \<le> ln (a X) + ln (bi X) - ln (ai X) - ln (b X)"
    if X: "X \<in> F" for X
    unfolding a_def ai_def b_def bi_def by (rule ln_quad) (use cls_pos[OF fin X] in auto)
  have "real (card F) - (\<Sum>X\<in>F. ai X * b X / (a X * bi X)) = (\<Sum>X\<in>F. 1 - ai X * b X / (a X * bi X))"
    by (simp add: sum_subtractf)
  also have "\<dots> \<le> (\<Sum>X\<in>F. ln (a X) + ln (bi X) - ln (ai X) - ln (b X))" by (rule sum_mono) (rule pt)
  finally have s1: "real (card F) - (\<Sum>X\<in>F. ai X * b X / (a X * bi X))
      \<le> (\<Sum>X\<in>F. ln (a X) + ln (bi X) - ln (ai X) - ln (b X))" .
  have s2: "(\<Sum>X\<in>F. ai X * b X / (a X * bi X)) \<le> real (card F)"
    using count_bound[OF fin AA i] unfolding a_def ai_def b_def bi_def .
  have s3: "(\<Sum>X\<in>F. ln (a X) + ln (bi X) - ln (ai X) - ln (b X))
      = (\<Sum>X\<in>F. ln (a X)) + (\<Sum>X\<in>F. ln (bi X)) - (\<Sum>X\<in>F. ln (ai X)) - (\<Sum>X\<in>F. ln (b X))"
    by (simp add: sum_subtractf sum.distrib)
  have key: "(\<Sum>X\<in>F. ln (b X)) - (\<Sum>X\<in>F. ln (bi X)) \<le> (\<Sum>X\<in>F. ln (a X)) - (\<Sum>X\<in>F. ln (ai X))"
    using s1 s2 s3 by linarith
  have "ent F (insert i A') - ent F A' = ((\<Sum>X\<in>F. ln (b X)) - (\<Sum>X\<in>F. ln (bi X))) / real (card F)"
    unfolding ent_def b_def bi_def by (simp add: diff_divide_distrib)
  also have "\<dots> \<le> ((\<Sum>X\<in>F. ln (a X)) - (\<Sum>X\<in>F. ln (ai X))) / real (card F)"
    by (rule divide_right_mono[OF key]) (use N in simp)
  also have "\<dots> = ent F (insert i A) - ent F A"
    unfolding ent_def a_def ai_def by (simp add: diff_divide_distrib)
  finally show ?thesis .
qed

theorem shearer_ent:
  fixes w :: "nat set \<Rightarrow> real"
  assumes fin: "finite F" and FV: "F \<subseteq> Pow {..<n}"
    and finB: "finite \<B>" and Bsub: "\<forall>B\<in>\<B>. B \<subseteq> {..<n}" and w0: "\<forall>B\<in>\<B>. 0 \<le> w B"
    and cover: "\<forall>i<n. 1 \<le> (\<Sum>B\<in>\<B>. if i \<in> B then w B else 0)"
  shows "ln (real (card F)) \<le> (\<Sum>B\<in>\<B>. w B * ent F B)"
proof -
  have sub: "\<forall>A i. A \<subseteq> {..<i} \<longrightarrow> i < n \<longrightarrow>
      ent F (insert i {..<i}) - ent F {..<i} \<le> ent F (insert i A) - ent F A"
  proof (intro allI impI)
    fix A and i :: nat assume A: "A \<subseteq> {..<i}" and "i < n"
    show "ent F (insert i {..<i}) - ent F {..<i} \<le> ent F (insert i A) - ent F A"
      by (rule ent_sub[OF fin A]) simp
  qed
  have mono: "\<forall>i<n. ent F {..<i} \<le> ent F {..<Suc i}"
    by (intro allI impI ent_mono[OF fin]) auto
  have "ent F {..<n} \<le> (\<Sum>B\<in>\<B>. w B * ent F B)"
    by (rule shearer_sub[OF ent_empty mono sub finB Bsub w0 cover])
  then show ?thesis using ent_full[OF fin FV] by simp
qed

end
