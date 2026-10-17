theory Shearer_Concentration
  imports Shearer_Entropy "Majority_AC0.Binomial_Estimates"
begin

text \<open>
  The concentration form of the certificate theorem (log \<section>6d), in nats. For \<open>X\<close> uniform on a
  finite family \<open>F\<close> of subsets of \<open>{..<n}\<close> and any fractional cover \<open>w\<close>,
  \<open>ln |F| \<le> \<Sum>\<^sub>B w B * (|B| ln 2 - \<onehalf> ln ((3|B|+2)/2) + H(|X \<inter> B|))\<close> (\<open>shearer_conc\<close>).
  A block saves \<open>\<onehalf> ln ((3|B|+2)/2)\<close> unless the size of \<open>X \<inter> B\<close> has entropy.
  \<open>lent F g\<close> is the entropy of a labelling \<open>g\<close>; \<open>group_bound\<close> is the grouping inequality
  \<open>H(g) \<le> H(f) + E ln #(g-values in the f-class)\<close> when \<open>g\<close> determines \<open>f\<close>.
\<close>

definition lcls :: "'a set set \<Rightarrow> ('a set \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> nat" where
  "lcls F g X = card {Y\<in>F. g Y = g X}"

definition lent :: "'a set set \<Rightarrow> ('a set \<Rightarrow> 'b) \<Rightarrow> real" where
  "lent F g = ln (real (card F)) - (\<Sum>X\<in>F. ln (real (lcls F g X))) / real (card F)"

lemma ent_lent: "ent F B = lent F (\<lambda>X. X \<inter> B)"
  unfolding ent_def lent_def cls_def lcls_def ..

lemma lcls_pos:
  assumes "finite F" "X \<in> F"
  shows "0 < real (lcls F g X)"
proof -
  have "X \<in> {Y\<in>F. g Y = g X}" using assms(2) by blast
  then have "0 < card {Y\<in>F. g Y = g X}" using assms(1) by (auto simp: card_gt_0_iff)
  then show ?thesis unfolding lcls_def by simp
qed

lemma inv_class_sum:
  assumes fM: "finite M"
  shows "(\<Sum>X\<in>M. 1 / real (card {Y\<in>M. g Y = g X})) = real (card (g ` M))"
proof -
  have "(\<Sum>X\<in>M. 1 / real (card {Y\<in>M. g Y = g X}))
      = (\<Sum>v\<in>g ` M. \<Sum>X\<in>{X\<in>M. g X = v}. 1 / real (card {Y\<in>M. g Y = g X}))"
    by (rule sum.image_gen[OF fM])
  also have "\<dots> = (\<Sum>v\<in>g ` M. (1::real))"
  proof (rule sum.cong[OF refl])
    fix v assume "v \<in> g ` M"
    then have pos: "0 < card {X\<in>M. g X = v}" using fM by (auto simp: card_gt_0_iff)
    have "(\<Sum>X\<in>{X\<in>M. g X = v}. 1 / real (card {Y\<in>M. g Y = g X}))
        = (\<Sum>X\<in>{X\<in>M. g X = v}. 1 / real (card {Y\<in>M. g Y = v}))"
      by (rule sum.cong) auto
    also have "\<dots> = 1" using pos by simp
    finally show "(\<Sum>X\<in>{X\<in>M. g X = v}. 1 / real (card {Y\<in>M. g Y = g X})) = 1" .
  qed
  also have "\<dots> = real (card (g ` M))" by simp
  finally show ?thesis .
qed

theorem group_bound:
  fixes f :: "'a set \<Rightarrow> 'c" and g :: "'a set \<Rightarrow> 'b"
  assumes fin: "finite F" and det: "\<forall>X Y. g X = g Y \<longrightarrow> f X = f Y"
  shows "lent F g \<le> lent F f + (\<Sum>X\<in>F. ln (real (card (g ` {Y\<in>F. f Y = f X})))) / real (card F)"
proof (cases "F = {}")
  case True
  then show ?thesis unfolding lent_def by simp
next
  case False
  define cf where "cf X = real (lcls F f X)" for X
  define cg where "cg X = real (lcls F g X)" for X
  define s where "s X = real (card (g ` {Y\<in>F. f Y = f X}))" for X
  define M where "M u = {X\<in>F. f X = u}" for u
  have N: "0 < real (card F)" using False fin by (simp add: card_gt_0_iff)
  have spos: "0 < s X" if X: "X \<in> F" for X
  proof -
    have "g X \<in> g ` {Y\<in>F. f Y = f X}" using X by blast
    then show ?thesis unfolding s_def using fin by (auto simp: card_gt_0_iff)
  qed
  have pt: "ln (cf X) - ln (cg X) - ln (s X) \<le> cf X / (cg X * s X) - 1" if X: "X \<in> F" for X
  proof -
    have p: "0 < cf X" "0 < cg X" "0 < s X"
      unfolding cf_def cg_def using lcls_pos[OF fin X] spos[OF X] by auto
    have "ln (cf X / (cg X * s X)) = ln (cf X) - ln (cg X) - ln (s X)"
      using p by (simp add: ln_div ln_mult)
    moreover have "ln (cf X / (cg X * s X)) \<le> cf X / (cg X * s X) - 1"
      by (rule ln_le_minus_one) (use p in simp)
    ultimately show ?thesis by linarith
  qed
  have blk: "(\<Sum>X\<in>M u. cf X / (cg X * s X)) = real (card (M u))" for u
  proof -
    have fMu: "finite (M u)" unfolding M_def using fin by simp
    have e: "cf X / (cg X * s X)
        = (real (card (M u)) / real (card (g ` M u))) * (1 / real (card {Y\<in>M u. g Y = g X}))"
      if X: "X \<in> M u" for X
    proof -
      have XF: "X \<in> F" and fX: "f X = u" using X unfolding M_def by auto
      have "{Y\<in>F. f Y = f X} = M u" unfolding M_def fX ..
      then have es: "s X = real (card (g ` M u))" unfolding s_def by simp
      have ecf: "cf X = real (card (M u))" unfolding cf_def lcls_def M_def fX ..
      have dY: "f Y = u" if "g Y = g X" for Y
        using mp[OF spec[OF spec[OF det, of Y], of X] that] fX by simp
      have "{Y\<in>F. g Y = g X} = {Y\<in>M u. g Y = g X}" unfolding M_def using dY by blast
      then have ecg: "cg X = real (card {Y\<in>M u. g Y = g X})" unfolding cg_def lcls_def by simp
      show ?thesis unfolding es ecf ecg by simp
    qed
    have "(\<Sum>X\<in>M u. cf X / (cg X * s X))
        = (\<Sum>X\<in>M u. (real (card (M u)) / real (card (g ` M u))) * (1 / real (card {Y\<in>M u. g Y = g X})))"
      by (rule sum.cong[OF refl]) (rule e)
    also have "\<dots> = (real (card (M u)) / real (card (g ` M u))) * (\<Sum>X\<in>M u. 1 / real (card {Y\<in>M u. g Y = g X}))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (real (card (M u)) / real (card (g ` M u))) * real (card (g ` M u))"
      unfolding inv_class_sum[OF fMu] ..
    also have "\<dots> = real (card (M u))"
    proof (cases "M u = {}")
      case True
      then show ?thesis by simp
    next
      case False
      then have "0 < card (g ` M u)" using fMu by (auto simp: card_gt_0_iff)
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have tot: "(\<Sum>X\<in>F. cf X / (cg X * s X)) = real (card F)"
  proof -
    have "(\<Sum>X\<in>F. cf X / (cg X * s X)) = (\<Sum>u\<in>f ` F. \<Sum>X\<in>M u. cf X / (cg X * s X))"
      unfolding M_def by (rule sum.image_gen[OF fin])
    also have "\<dots> = (\<Sum>u\<in>f ` F. real (card (M u)))" by (simp only: blk)
    also have "\<dots> = (\<Sum>u\<in>f ` F. \<Sum>X\<in>M u. (1::real))" by simp
    also have "\<dots> = (\<Sum>X\<in>F. (1::real))" unfolding M_def by (rule sum.image_gen[OF fin, symmetric])
    finally show ?thesis by simp
  qed
  have "(\<Sum>X\<in>F. ln (cf X) - ln (cg X) - ln (s X)) \<le> (\<Sum>X\<in>F. cf X / (cg X * s X) - 1)"
    by (rule sum_mono) (rule pt)
  also have "\<dots> = 0" unfolding sum_subtractf tot by simp
  finally have key: "(\<Sum>X\<in>F. ln (cf X)) - (\<Sum>X\<in>F. ln (cg X)) \<le> (\<Sum>X\<in>F. ln (s X))"
    by (simp add: sum_subtractf)
  then have "((\<Sum>X\<in>F. ln (cf X)) - (\<Sum>X\<in>F. ln (cg X))) / real (card F) \<le> (\<Sum>X\<in>F. ln (s X)) / real (card F)"
    by (rule divide_right_mono) (use N in simp)
  then show ?thesis unfolding lent_def cf_def cg_def s_def by (simp add: diff_divide_distrib)
qed

lemma ent_count:
  assumes fin: "finite F" and fB: "finite B"
  shows "ent F B \<le> lent F (\<lambda>X. card (X \<inter> B))
           + (\<Sum>X\<in>F. ln (real (card B choose card (X \<inter> B)))) / real (card F)"
proof (cases "F = {}")
  case True
  then show ?thesis unfolding ent_def lent_def by simp
next
  case False
  have N: "0 < real (card F)" using False fin by (simp add: card_gt_0_iff)
  have g: "ent F B \<le> lent F (\<lambda>X. card (X \<inter> B))
      + (\<Sum>X\<in>F. ln (real (card ((\<lambda>X. X \<inter> B) ` {Y\<in>F. card (Y \<inter> B) = card (X \<inter> B)})))) / real (card F)"
    unfolding ent_lent by (rule group_bound[OF fin]) auto
  have "ln (real (card ((\<lambda>X. X \<inter> B) ` {Y\<in>F. card (Y \<inter> B) = card (X \<inter> B)})))
      \<le> ln (real (card B choose card (X \<inter> B)))" if X: "X \<in> F" for X
  proof -
    have sub: "(\<lambda>X. X \<inter> B) ` {Y\<in>F. card (Y \<inter> B) = card (X \<inter> B)} \<subseteq> {T. T \<subseteq> B \<and> card T = card (X \<inter> B)}"
      by auto
    have "card ((\<lambda>X. X \<inter> B) ` {Y\<in>F. card (Y \<inter> B) = card (X \<inter> B)}) \<le> card {T. T \<subseteq> B \<and> card T = card (X \<inter> B)}"
      by (rule card_mono[OF _ sub]) (use fB in simp)
    also have "\<dots> = card B choose card (X \<inter> B)" by (rule n_subsets[OF fB])
    finally have le: "card ((\<lambda>X. X \<inter> B) ` {Y\<in>F. card (Y \<inter> B) = card (X \<inter> B)}) \<le> card B choose card (X \<inter> B)" .
    have "X \<inter> B \<in> (\<lambda>X. X \<inter> B) ` {Y\<in>F. card (Y \<inter> B) = card (X \<inter> B)}" using X by blast
    then have "0 < card ((\<lambda>X. X \<inter> B) ` {Y\<in>F. card (Y \<inter> B) = card (X \<inter> B)})"
      using fin by (auto simp: card_gt_0_iff)
    then show ?thesis by (intro ln_mono) (use le in simp_all)
  qed
  then have "(\<Sum>X\<in>F. ln (real (card ((\<lambda>X. X \<inter> B) ` {Y\<in>F. card (Y \<inter> B) = card (X \<inter> B)}))))
      \<le> (\<Sum>X\<in>F. ln (real (card B choose card (X \<inter> B))))" by (rule sum_mono)
  then have "(\<Sum>X\<in>F. ln (real (card ((\<lambda>X. X \<inter> B) ` {Y\<in>F. card (Y \<inter> B) = card (X \<inter> B)})))) / real (card F)
      \<le> (\<Sum>X\<in>F. ln (real (card B choose card (X \<inter> B)))) / real (card F)"
    by (rule divide_right_mono) (use N in simp)
  then show ?thesis using g by linarith
qed

lemma ln_binom:
  assumes "j \<le> b"
  shows "ln (real (b choose j)) \<le> real b * ln 2 - ln ((3 * real b + 2) / 2) / 2"
proof -
  define c where "c = real (b choose (b div 2))"
  have cpos: "0 < c" unfolding c_def by simp
  have bj: "0 < real (b choose j)" using assms by simp
  have "real (b choose j) \<le> c" unfolding c_def using binomial_maximum[of b j] by simp
  then have l1: "ln (real (b choose j)) \<le> ln c" by (rule ln_mono) (rule bj)
  have r: "(3 * real b + 2) / 2 \<le> (2 ^ b / c)\<^sup>2" unfolding c_def by (rule central_ratio)
  have "ln ((3 * real b + 2) / 2) \<le> ln ((2 ^ b / c)\<^sup>2)" by (rule ln_mono[OF r]) simp
  also have "\<dots> = 2 * (real b * ln 2 - ln c)"
    using cpos by (simp add: ln_realpow ln_div)
  finally have r2: "ln ((3 * real b + 2) / 2) \<le> 2 * (real b * ln 2 - ln c)" .
  define L where "L = ln ((3 * real b + 2) / 2)"
  define T where "T = real b * ln (2::real)"
  define Lb where "Lb = ln (real (b choose j))"
  define Lc where "Lc = ln c"
  have "L \<le> 2 * (T - Lc)" using r2 unfolding L_def T_def Lc_def .
  moreover have "Lb \<le> Lc" using l1 unfolding Lb_def Lc_def .
  ultimately have "Lb \<le> T - L / 2" by argo
  then show ?thesis unfolding L_def T_def Lb_def .
qed

theorem shearer_conc:
  fixes w :: "nat set \<Rightarrow> real"
  assumes fin: "finite F" and ne: "F \<noteq> {}" and FV: "F \<subseteq> Pow {..<n}"
    and finB: "finite \<B>" and Bsub: "\<forall>B\<in>\<B>. B \<subseteq> {..<n}" and w0: "\<forall>B\<in>\<B>. 0 \<le> w B"
    and cover: "\<forall>i<n. 1 \<le> (\<Sum>B\<in>\<B>. if i \<in> B then w B else 0)"
  shows "ln (real (card F)) \<le> (\<Sum>B\<in>\<B>. w B *
      (real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2 + lent F (\<lambda>X. card (X \<inter> B))))"
proof -
  have N: "0 < real (card F)" using ne fin by (simp add: card_gt_0_iff)
  have one: "ent F B \<le> real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2
      + lent F (\<lambda>X. card (X \<inter> B))" if B: "B \<in> \<B>" for B
  proof -
    have fB: "finite B" using Bsub B finite_subset by blast
    define c where "c = real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2"
    have "(\<Sum>X\<in>F. ln (real (card B choose card (X \<inter> B)))) \<le> (\<Sum>X\<in>F. c)"
      unfolding c_def by (rule sum_mono, rule ln_binom, rule card_mono[OF fB]) auto
    also have "\<dots> = real (card F) * c" by simp
    finally have "(\<Sum>X\<in>F. ln (real (card B choose card (X \<inter> B)))) / real (card F) \<le> c"
      using N by (simp add: divide_le_eq mult.commute)
    then show ?thesis using ent_count[OF fin fB] unfolding c_def by linarith
  qed
  have "ln (real (card F)) \<le> (\<Sum>B\<in>\<B>. w B * ent F B)"
    by (rule shearer_ent[OF fin FV finB Bsub w0 cover])
  also have "\<dots> \<le> (\<Sum>B\<in>\<B>. w B *
      (real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2 + lent F (\<lambda>X. card (X \<inter> B))))"
    by (rule sum_mono) (use w0 one in \<open>auto intro: mult_left_mono\<close>)
  finally show ?thesis .
qed

end
