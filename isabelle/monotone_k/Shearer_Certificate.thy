theory Shearer_Certificate
  imports Shearer_Concentration
begin

text \<open>
  The sharpened certificate theorem of log \<section>6d, in nats. If every \<open>X \<in> F\<close> has
  \<open>|X \<inter> B| \<ge> t B\<close> on each block of a fractional cover, then for every \<open>0 < \<theta> < 1\<close>
  \<open>ln |F| \<le> \<Sum>\<^sub>B w B (|B| ln 2 - \<onehalf> ln ((3|B|+2)/2)) - W ln (1-\<theta>) - \<Delta> ln \<theta>\<close>
  (\<open>certificate\<close>), where \<open>W = \<Sum>\<^sub>B w B\<close> and \<open>\<Delta> = \<Sum>\<^sub>B w B E(|X \<inter> B| - t B)\<close> is the deficit.
  The choice \<open>\<theta> = \<Delta>/(W+\<Delta>)\<close> gives \<open>W h(\<Delta>/W)\<close>. The integer-entropy step is Gibbs'
  inequality against a geometric distribution (\<open>gibbs\<close>, \<open>int_entropy\<close>), so no concavity is needed.
\<close>

lemma weighted_class_sum:
  assumes fin: "finite F"
  shows "(\<Sum>X\<in>F. q (f X) / real (lcls F f X)) = (\<Sum>v\<in>f ` F. q v)"
proof -
  have "(\<Sum>X\<in>F. q (f X) / real (lcls F f X))
      = (\<Sum>v\<in>f ` F. \<Sum>X\<in>{X\<in>F. f X = v}. q (f X) / real (lcls F f X))"
    by (rule sum.image_gen[OF fin])
  also have "\<dots> = (\<Sum>v\<in>f ` F. q v)"
  proof (rule sum.cong[OF refl])
    fix v assume "v \<in> f ` F"
    then have pos: "0 < card {X\<in>F. f X = v}" using fin by (auto simp: card_gt_0_iff)
    have "(\<Sum>X\<in>{X\<in>F. f X = v}. q (f X) / real (lcls F f X))
        = (\<Sum>X\<in>{X\<in>F. f X = v}. q v / real (card {Y\<in>F. f Y = v}))"
      by (rule sum.cong) (auto simp: lcls_def)
    also have "\<dots> = q v" using pos by simp
    finally show "(\<Sum>X\<in>{X\<in>F. f X = v}. q (f X) / real (lcls F f X)) = q v" .
  qed
  finally show ?thesis .
qed

theorem gibbs:
  assumes fin: "finite F" and ne: "F \<noteq> {}"
    and qpos: "\<forall>v\<in>f ` F. 0 < q v" and qsum: "(\<Sum>v\<in>f ` F. q v) \<le> 1"
  shows "lent F f \<le> (\<Sum>X\<in>F. - ln (q (f X))) / real (card F)"
proof -
  define N where "N = real (card F)"
  define c where "c X = real (lcls F f X)" for X
  have N0: "0 < N" unfolding N_def using fin ne by (simp add: card_gt_0_iff)
  have pt: "ln N + ln (q (f X)) - ln (c X) \<le> N * q (f X) / c X - 1" if X: "X \<in> F" for X
  proof -
    have p: "0 < c X" "0 < q (f X)" unfolding c_def using lcls_pos[OF fin X] qpos X by auto
    have "ln (N * q (f X) / c X) = ln N + ln (q (f X)) - ln (c X)"
      using p N0 by (simp add: ln_div ln_mult)
    moreover have "ln (N * q (f X) / c X) \<le> N * q (f X) / c X - 1"
      by (rule ln_le_minus_one) (use p N0 in simp)
    ultimately show ?thesis by linarith
  qed
  have "(\<Sum>X\<in>F. N * q (f X) / c X) = N * (\<Sum>X\<in>F. q (f X) / c X)"
    by (simp add: sum_distrib_left)
  also have "(\<Sum>X\<in>F. q (f X) / c X) = (\<Sum>v\<in>f ` F. q v)"
    unfolding c_def by (rule weighted_class_sum[OF fin])
  finally have tot: "(\<Sum>X\<in>F. N * q (f X) / c X) \<le> N" using qsum N0 by simp
  have "(\<Sum>X\<in>F. ln N + ln (q (f X)) - ln (c X)) \<le> (\<Sum>X\<in>F. N * q (f X) / c X - 1)"
    by (rule sum_mono) (rule pt)
  also have "\<dots> = (\<Sum>X\<in>F. N * q (f X) / c X) - N" unfolding N_def by (simp add: sum_subtractf)
  finally have s: "(\<Sum>X\<in>F. ln N + ln (q (f X)) - ln (c X)) \<le> 0" using tot by linarith
  have s2: "(\<Sum>X\<in>F. ln N + ln (q (f X)) - ln (c X))
      = N * ln N + (\<Sum>X\<in>F. ln (q (f X))) - (\<Sum>X\<in>F. ln (c X))"
    unfolding N_def by (simp add: sum_subtractf sum.distrib)
  have key: "N * ln N - (\<Sum>X\<in>F. ln (c X)) \<le> (\<Sum>X\<in>F. - ln (q (f X)))"
    using s s2 by (simp add: sum_negf)
  have "N * lent F f = N * ln N - (\<Sum>X\<in>F. ln (c X))"
    unfolding lent_def c_def N_def using N0 unfolding N_def by (simp add: right_diff_distrib)
  then have "N * lent F f \<le> (\<Sum>X\<in>F. - ln (q (f X)))" using key by simp
  then show ?thesis using N0 unfolding N_def by (simp add: le_divide_eq mult.commute)
qed

lemma geom_sum:
  fixes \<theta> :: real
  assumes th: "0 \<le> \<theta>" "\<theta> < 1" and fJ: "finite J"
  shows "(\<Sum>j\<in>J. (1 - \<theta>) * \<theta> ^ j) \<le> 1"
proof -
  define m where "m = Suc (Max (insert 0 J))"
  have Jm: "J \<subseteq> {..<m}" unfolding m_def using fJ by (auto simp: less_Suc_eq_le)
  have "(\<Sum>j\<in>J. (1 - \<theta>) * \<theta> ^ j) \<le> (\<Sum>j<m. (1 - \<theta>) * \<theta> ^ j)"
    by (rule sum_mono2) (use Jm th in auto)
  also have "\<dots> = (1 - \<theta>) * (\<Sum>j<m. \<theta> ^ j)" by (simp add: sum_distrib_left)
  also have "\<dots> = 1 - \<theta> ^ m" by (rule one_diff_power_eq[symmetric])
  also have "\<dots> \<le> 1" using th by simp
  finally show ?thesis .
qed

theorem int_entropy:
  fixes f :: "'a set \<Rightarrow> nat" and \<theta> :: real
  assumes fin: "finite F" and ne: "F \<noteq> {}" and t: "\<forall>X\<in>F. t \<le> f X"
    and th: "0 < \<theta>" "\<theta> < 1"
  shows "lent F f \<le> - ln (1 - \<theta>) - ln \<theta> * ((\<Sum>X\<in>F. real (f X - t)) / real (card F))"
proof -
  define q where "q v = (1 - \<theta>) * \<theta> ^ (v - t)" for v
  have qpos: "\<forall>v\<in>f ` F. 0 < q v" unfolding q_def using th by simp
  have inj: "inj_on (\<lambda>v. v - t) (f ` F)"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> f ` F" and y: "y \<in> f ` F" and e: "x - t = y - t"
    obtain X where X: "X \<in> F" "x = f X" using x by blast
    obtain Y where Y: "Y \<in> F" "y = f Y" using y by blast
    have "t \<le> x" unfolding X(2) by (rule bspec[OF t X(1)])
    moreover have "t \<le> y" unfolding Y(2) by (rule bspec[OF t Y(1)])
    ultimately show "x = y" using e by arith
  qed
  have "(\<Sum>v\<in>f ` F. q v) = (\<Sum>j\<in>(\<lambda>v. v - t) ` f ` F. (1 - \<theta>) * \<theta> ^ j)"
    unfolding q_def by (simp add: sum.reindex[OF inj])
  also have "\<dots> \<le> 1" by (rule geom_sum) (use th fin in auto)
  finally have qsum: "(\<Sum>v\<in>f ` F. q v) \<le> 1" .
  have lq: "- ln (q (f X)) = - ln (1 - \<theta>) - ln \<theta> * real (f X - t)" for X
    unfolding q_def using th by (simp add: ln_mult ln_realpow)
  have N0: "0 < real (card F)" using fin ne by (simp add: card_gt_0_iff)
  have "(\<Sum>X\<in>F. - ln (q (f X))) = real (card F) * (- ln (1 - \<theta>)) - ln \<theta> * (\<Sum>X\<in>F. real (f X - t))"
    unfolding lq by (simp add: sum_subtractf sum_distrib_left)
  then have "(\<Sum>X\<in>F. - ln (q (f X))) / real (card F)
      = - ln (1 - \<theta>) - ln \<theta> * ((\<Sum>X\<in>F. real (f X - t)) / real (card F))"
    using N0 by (simp add: diff_divide_distrib)
  then show ?thesis using gibbs[OF fin ne qpos qsum] by simp
qed

theorem certificate:
  fixes w :: "nat set \<Rightarrow> real" and t :: "nat set \<Rightarrow> nat" and \<theta> :: real
  assumes fin: "finite F" and ne: "F \<noteq> {}" and FV: "F \<subseteq> Pow {..<n}"
    and finB: "finite \<B>" and Bsub: "\<forall>B\<in>\<B>. B \<subseteq> {..<n}" and w0: "\<forall>B\<in>\<B>. 0 \<le> w B"
    and cover: "\<forall>i<n. 1 \<le> (\<Sum>B\<in>\<B>. if i \<in> B then w B else 0)"
    and t: "\<forall>B\<in>\<B>. \<forall>X\<in>F. t B \<le> card (X \<inter> B)"
    and th: "0 < \<theta>" "\<theta> < 1"
  shows "ln (real (card F)) \<le> (\<Sum>B\<in>\<B>. w B * (real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2))
           - (\<Sum>B\<in>\<B>. w B) * ln (1 - \<theta>)
           - (\<Sum>B\<in>\<B>. w B * ((\<Sum>X\<in>F. real (card (X \<inter> B) - t B)) / real (card F))) * ln \<theta>"
proof -
  define a where "a B = real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2" for B :: "nat set"
  define e where "e B = (\<Sum>X\<in>F. real (card (X \<inter> B) - t B)) / real (card F)" for B :: "nat set"
  have one: "lent F (\<lambda>X. card (X \<inter> B)) \<le> - ln (1 - \<theta>) - ln \<theta> * e B" if B: "B \<in> \<B>" for B
    unfolding e_def by (rule int_entropy[OF fin ne _ th]) (use t B in blast)
  have "ln (real (card F)) \<le> (\<Sum>B\<in>\<B>. w B * (a B + lent F (\<lambda>X. card (X \<inter> B))))"
    unfolding a_def by (rule shearer_conc[OF fin ne FV finB Bsub w0 cover])
  also have "\<dots> \<le> (\<Sum>B\<in>\<B>. w B * (a B + (- ln (1 - \<theta>) - ln \<theta> * e B)))"
    by (rule sum_mono) (use w0 one in \<open>auto intro: mult_left_mono\<close>)
  also have "\<dots> = (\<Sum>B\<in>\<B>. w B * a B) - (\<Sum>B\<in>\<B>. w B) * ln (1 - \<theta>) - (\<Sum>B\<in>\<B>. w B * e B) * ln \<theta>"
    by (simp add: algebra_simps sum.distrib sum_subtractf sum_distrib_left sum_distrib_right)
  finally show ?thesis unfolding a_def e_def .
qed

end
