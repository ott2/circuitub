theory Shearer_Typical
  imports Shearer_Certificate
begin

text \<open>
  Typical lower bounds (log \<section>6e): the certificate theorem when the lower bound \<open>t B\<close> on
  \<open>|X \<inter> B|\<close> may fail on part of \<open>F\<close>. With \<open>p\<close> the fraction of \<open>F\<close> where \<open>f X < t\<close> and any
  \<open>0 < r < 1\<close>, the integer entropy is at most
  \<open>(1-p)(-ln(1-r) - ln(1-\<theta>)) + p(ln t - ln r) - ln \<theta> E(f X - t)\<close> (\<open>int_entropy_typ\<close>).
  The choice \<open>r = p\<close> gives the cost \<open>h(p) + p ln t\<close> of the rare deficient events. The proof is
  \<open>gibbs\<close> against a mixture: mass \<open>r\<close> spread uniformly below \<open>t\<close>, and \<open>1-r\<close> geometric above.
  \<open>certificate_typ\<close> is the resulting certificate theorem.
\<close>

theorem int_entropy_typ:
  fixes f :: "'a set \<Rightarrow> nat" and \<theta> r :: real
  assumes fin: "finite F" and ne: "F \<noteq> {}"
    and th: "0 < \<theta>" "\<theta> < 1" and r: "0 < r" "r < 1"
    and p: "p = real (card {X\<in>F. f X < t}) / real (card F)"
  shows "lent F f \<le> (1 - p) * (- ln (1 - r) - ln (1 - \<theta>)) + p * (ln (real t) - ln r)
           - ln \<theta> * ((\<Sum>X\<in>F. real (f X - t)) / real (card F))"
proof -
  define q where "q v = (if v < t then r / real t else (1 - r) * ((1 - \<theta>) * \<theta> ^ (v - t)))" for v
  have qpos: "\<forall>v\<in>f ` F. 0 < q v" unfolding q_def using th r by auto
  have fI: "finite (f ` F)" using fin by simp
  have split: "(\<Sum>v\<in>f ` F. q v) = (\<Sum>v\<in>{v\<in>f ` F. v < t}. q v) + (\<Sum>v\<in>{v\<in>f ` F. \<not> v < t}. q v)"
    by (rule sum_split_pred[OF fI])
  have low: "(\<Sum>v\<in>{v\<in>f ` F. v < t}. q v) \<le> r"
  proof -
    have "(\<Sum>v\<in>{v\<in>f ` F. v < t}. q v) = (\<Sum>v\<in>{v\<in>f ` F. v < t}. r / real t)"
      unfolding q_def by (rule sum.cong) auto
    also have "\<dots> \<le> (\<Sum>v\<in>{..<t}. r / real t)"
      by (rule sum_mono2) (use r in auto)
    also have "\<dots> \<le> r"
    proof (cases "t = 0")
      case True
      then show ?thesis using r by simp
    next
      case False
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have high: "(\<Sum>v\<in>{v\<in>f ` F. \<not> v < t}. q v) \<le> 1 - r"
  proof -
    define J where "J = {v\<in>f ` F. \<not> v < t}"
    have fJ: "finite J" unfolding J_def using fI by simp
    have inj: "inj_on (\<lambda>v. v - t) J"
      by (rule inj_onI) (auto simp: J_def)
    have "(\<Sum>v\<in>J. q v) = (\<Sum>v\<in>J. (1 - r) * ((1 - \<theta>) * \<theta> ^ (v - t)))"
      unfolding q_def J_def by (rule sum.cong) auto
    also have "\<dots> = (1 - r) * (\<Sum>j\<in>(\<lambda>v. v - t) ` J. (1 - \<theta>) * \<theta> ^ j)"
      by (simp add: sum_distrib_left sum.reindex[OF inj])
    also have "\<dots> \<le> (1 - r) * 1"
      by (rule mult_left_mono, rule geom_sum) (use th r fJ in auto)
    finally show ?thesis unfolding J_def by simp
  qed
  have qsum: "(\<Sum>v\<in>f ` F. q v) \<le> 1" using split low high by linarith
  have g: "lent F f \<le> (\<Sum>X\<in>F. - ln (q (f X))) / real (card F)"
    by (rule gibbs[OF fin ne qpos qsum])
  define A where "A = ln (real t) - ln r"
  define C where "C = - ln (1 - r) - ln (1 - \<theta>)"
  define Bad where "Bad = {X\<in>F. f X < t}"
  define Good where "Good = {X\<in>F. \<not> f X < t}"
  have lbad: "- ln (q (f X)) = A" if X: "X \<in> Bad" for X
  proof -
    have lt: "f X < t" using X unfolding Bad_def by simp
    then have "0 < real t" by simp
    then show ?thesis unfolding q_def A_def using lt r by (simp add: ln_div)
  qed
  have lgood: "- ln (q (f X)) = C - ln \<theta> * real (f X - t)" if X: "X \<in> Good" for X
  proof -
    have ge: "\<not> f X < t" using X unfolding Good_def by simp
    have "ln ((1 - r) * ((1 - \<theta>) * \<theta> ^ (f X - t))) = ln (1 - r) + (ln (1 - \<theta>) + real (f X - t) * ln \<theta>)"
      using th r by (simp add: ln_mult ln_realpow)
    then show ?thesis unfolding q_def C_def using ge by simp
  qed
  have s1: "(\<Sum>X\<in>F. - ln (q (f X))) = (\<Sum>X\<in>Bad. - ln (q (f X))) + (\<Sum>X\<in>Good. - ln (q (f X)))"
    unfolding Bad_def Good_def by (rule sum_split_pred[OF fin])
  have s2: "(\<Sum>X\<in>Bad. - ln (q (f X))) = real (card Bad) * A"
    using lbad by simp
  have s3: "(\<Sum>X\<in>Good. - ln (q (f X))) = real (card Good) * C - ln \<theta> * (\<Sum>X\<in>Good. real (f X - t))"
    using lgood by (simp add: sum_subtractf sum_distrib_left)
  have d1: "(\<Sum>X\<in>F. real (f X - t)) = (\<Sum>X\<in>Bad. real (f X - t)) + (\<Sum>X\<in>Good. real (f X - t))"
    unfolding Bad_def Good_def by (rule sum_split_pred[OF fin])
  have d2: "(\<Sum>X\<in>Bad. real (f X - t)) = 0" unfolding Bad_def by simp
  have c1: "(\<Sum>X\<in>F. (1::real)) = (\<Sum>X\<in>Bad. 1) + (\<Sum>X\<in>Good. 1)"
    unfolding Bad_def Good_def by (rule sum_split_pred[OF fin])
  then have cN: "real (card F) = real (card Bad) + real (card Good)" by simp
  define N where "N = real (card F)"
  define D where "D = (\<Sum>X\<in>F. real (f X - t))"
  define nb where "nb = real (card Bad)"
  have N0: "0 < N" unfolding N_def using fin ne by (simp add: card_gt_0_iff)
  have pnb: "p = nb / N" unfolding p N_def nb_def Bad_def ..
  have tot: "(\<Sum>X\<in>F. - ln (q (f X))) = nb * A + (N - nb) * C - ln \<theta> * D"
    unfolding s1 s2 s3 D_def d1 d2 nb_def N_def cN by simp
  have "(nb * A + (N - nb) * C - ln \<theta> * D) / N = (1 - p) * C + p * A - ln \<theta> * (D / N)"
    unfolding pnb using N0 by (simp add: field_simps)
  then show ?thesis using g unfolding tot A_def C_def D_def N_def by simp
qed

theorem certificate_typ:
  fixes w :: "nat set \<Rightarrow> real" and t :: "nat set \<Rightarrow> nat" and r :: "nat set \<Rightarrow> real" and \<theta> :: real
  assumes fin: "finite F" and ne: "F \<noteq> {}" and FV: "F \<subseteq> Pow {..<n}"
    and finB: "finite \<B>" and Bsub: "\<forall>B\<in>\<B>. B \<subseteq> {..<n}" and w0: "\<forall>B\<in>\<B>. 0 \<le> w B"
    and cover: "\<forall>i<n. 1 \<le> (\<Sum>B\<in>\<B>. if i \<in> B then w B else 0)"
    and th: "0 < \<theta>" "\<theta> < 1" and r: "\<forall>B\<in>\<B>. 0 < r B \<and> r B < 1"
    and p: "\<forall>B. p B = real (card {X\<in>F. card (X \<inter> B) < t B}) / real (card F)"
  shows "ln (real (card F)) \<le> (\<Sum>B\<in>\<B>. w B * (real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2
           + ((1 - p B) * (- ln (1 - r B) - ln (1 - \<theta>)) + p B * (ln (real (t B)) - ln (r B))
           - ln \<theta> * ((\<Sum>X\<in>F. real (card (X \<inter> B) - t B)) / real (card F)))))"
proof -
  define a where "a B = real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2" for B :: "nat set"
  define c where "c B = (1 - p B) * (- ln (1 - r B) - ln (1 - \<theta>)) + p B * (ln (real (t B)) - ln (r B))
           - ln \<theta> * ((\<Sum>X\<in>F. real (card (X \<inter> B) - t B)) / real (card F))" for B
  have one: "lent F (\<lambda>X. card (X \<inter> B)) \<le> c B" if B: "B \<in> \<B>" for B
  proof -
    have rB: "0 < r B" "r B < 1" using r B by auto
    show ?thesis unfolding c_def by (rule int_entropy_typ[OF fin ne th rB spec[OF p, of B]])
  qed
  have "ln (real (card F)) \<le> (\<Sum>B\<in>\<B>. w B * (a B + lent F (\<lambda>X. card (X \<inter> B))))"
    unfolding a_def by (rule shearer_conc[OF fin ne FV finB Bsub w0 cover])
  also have "\<dots> \<le> (\<Sum>B\<in>\<B>. w B * (a B + c B))"
    by (rule sum_mono) (use w0 one in \<open>auto intro: mult_left_mono\<close>)
  finally show ?thesis unfolding a_def c_def .
qed

end
