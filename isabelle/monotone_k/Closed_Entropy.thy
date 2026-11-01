theory Closed_Entropy
  imports Closed_Blocks Shearer_Conditional
begin

text \<open>The entropy form of \<open>closed_bound\<close>. The label "set of closed blocks" costs its entropy,
  and by subadditivity (\<open>lent_pair\<close>, from \<open>gibbs\<close> against a product distribution) at most the
  sum of the binary entropies of the events "block \<open>i\<close> is closed". A block that is almost always
  or almost never closed costs almost nothing.\<close>

definition bent :: "real \<Rightarrow> real" where
  "bent p = - p * ln p - (1 - p) * ln (1 - p)"

lemma lent_explicit:
  assumes fin: "finite F" and ne: "F \<noteq> {}"
  shows "lent F g = (\<Sum>X\<in>F. - ln (real (lcls F g X) / real (card F))) / real (card F)"
proof -
  define N where "N = real (card F)"
  have N: "0 < N" unfolding N_def using fin ne by (simp add: card_gt_0_iff)
  have pt: "- ln (real (lcls F g X) / N) = ln N - ln (real (lcls F g X))" if "X \<in> F" for X
    using ln_divide_pos[OF lcls_pos[OF fin that, of g] N] by simp
  have "(\<Sum>X\<in>F. - ln (real (lcls F g X) / N)) = (\<Sum>X\<in>F. ln N - ln (real (lcls F g X)))"
    by (rule sum.cong[OF refl]) (rule pt)
  also have "\<dots> = N * ln N - (\<Sum>X\<in>F. ln (real (lcls F g X)))"
    unfolding N_def by (simp add: sum_subtractf)
  finally have "(\<Sum>X\<in>F. - ln (real (lcls F g X) / N)) / N = ln N - (\<Sum>X\<in>F. ln (real (lcls F g X))) / N"
    using N by (simp add: field_simps)
  then show ?thesis unfolding lent_def N_def by simp
qed

lemma card_by_image:
  assumes fin: "finite F"
  shows "(\<Sum>a\<in>g ` F. real (card {Y\<in>F. g Y = a})) = real (card F)"
proof -
  have "real (card F) = (\<Sum>X\<in>F. (1::real))" by simp
  also have "\<dots> = (\<Sum>a\<in>g ` F. \<Sum>X\<in>{X\<in>F. g X = a}. (1::real))" by (rule sum.image_gen[OF fin])
  also have "\<dots> = (\<Sum>a\<in>g ` F. real (card {Y\<in>F. g Y = a}))" by simp
  finally show ?thesis by simp
qed

theorem lent_pair:
  assumes fin: "finite F" and ne: "F \<noteq> {}"
  shows "lent F (\<lambda>X. (g X, h X)) \<le> lent F g + lent F h"
proof -
  define N where "N = real (card F)"
  have N: "0 < N" unfolding N_def using fin ne by (simp add: card_gt_0_iff)
  define pg where "pg a = real (card {Y\<in>F. g Y = a}) / N" for a
  define ph where "ph b = real (card {Y\<in>F. h Y = b}) / N" for b
  define q where "q v = pg (fst v) * ph (snd v)" for v
  have pgX: "pg (g X) = real (lcls F g X) / N" for X unfolding pg_def lcls_def ..
  have phX: "ph (h X) = real (lcls F h X) / N" for X unfolding ph_def lcls_def ..
  have pgpos: "0 < pg (g X)" if "X \<in> F" for X unfolding pgX by (rule divide_pos_pos[OF lcls_pos[OF fin that] N])
  have phpos: "0 < ph (h X)" if "X \<in> F" for X unfolding phX by (rule divide_pos_pos[OF lcls_pos[OF fin that] N])
  have qpos: "\<forall>v\<in>(\<lambda>X. (g X, h X)) ` F. 0 < q v" unfolding q_def using pgpos phpos by auto
  have qnn: "0 \<le> q v" for v unfolding q_def pg_def ph_def using N by simp
  have qsum: "(\<Sum>v\<in>(\<lambda>X. (g X, h X)) ` F. q v) \<le> 1"
  proof -
    have sub: "(\<lambda>X. (g X, h X)) ` F \<subseteq> g ` F \<times> h ` F" by blast
    have "(\<Sum>v\<in>(\<lambda>X. (g X, h X)) ` F. q v) \<le> (\<Sum>v\<in>g ` F \<times> h ` F. q v)"
      by (rule sum_mono2) (use fin sub qnn in auto)
    also have "\<dots> = (\<Sum>a\<in>g ` F. pg a) * (\<Sum>b\<in>h ` F. ph b)"
      unfolding q_def by (simp add: sum_product sum.cartesian_product case_prod_beta)
    also have "(\<Sum>a\<in>g ` F. pg a) = 1"
      unfolding pg_def using card_by_image[OF fin, of g] N by (simp add: sum_divide_distrib[symmetric] N_def)
    also have "(\<Sum>b\<in>h ` F. ph b) = 1"
      unfolding ph_def using card_by_image[OF fin, of h] N by (simp add: sum_divide_distrib[symmetric] N_def)
    finally show ?thesis by simp
  qed
  have "lent F (\<lambda>X. (g X, h X)) \<le> (\<Sum>X\<in>F. - ln (q ((\<lambda>X. (g X, h X)) X))) / real (card F)"
    by (rule gibbs[OF fin ne qpos qsum])
  also have "(\<Sum>X\<in>F. - ln (q ((\<lambda>X. (g X, h X)) X)))
      = (\<Sum>X\<in>F. - ln (real (lcls F g X) / N)) + (\<Sum>X\<in>F. - ln (real (lcls F h X) / N))"
  proof -
    have "- ln (q (g X, h X)) = - ln (pg (g X)) + - ln (ph (h X))" if "X \<in> F" for X
      using ln_mult_pos[OF pgpos[OF that] phpos[OF that]] unfolding q_def by simp
    then show ?thesis unfolding pgX phX by (simp add: sum.distrib[symmetric])
  qed
  also have "\<dots> / real (card F) = lent F g + lent F h"
    unfolding lent_explicit[OF fin ne, of g] lent_explicit[OF fin ne, of h] N_def by (simp add: add_divide_distrib)
  finally show ?thesis .
qed

lemma lent_cong:
  assumes "\<forall>X\<in>F. \<forall>Y\<in>F. (g X = g Y) = (g' X = g' Y)"
  shows "lent F g = lent F g'"
proof -
  have "lcls F g X = lcls F g' X" if "X \<in> F" for X
  proof -
    have "{Y\<in>F. g Y = g X} = {Y\<in>F. g' Y = g' X}" using assms that by blast
    then show ?thesis unfolding lcls_def by simp
  qed
  then show ?thesis unfolding lent_def by (simp cong: sum.cong)
qed

lemma lent_const:
  assumes fin: "finite F" and ne: "F \<noteq> {}"
  shows "lent F (\<lambda>X. c) = 0"
proof -
  have "lcls F (\<lambda>X. c) X = card F" for X unfolding lcls_def by simp
  then show ?thesis unfolding lent_def using fin ne by (simp add: card_gt_0_iff)
qed

theorem lent_bits:
  fixes N :: nat
  assumes fin: "finite F" and ne: "F \<noteq> {}" and TN: "\<forall>X\<in>F. T X \<subseteq> {..<N}"
  shows "lent F T \<le> (\<Sum>i<N. lent F (\<lambda>X. i \<in> T X))"
proof -
  have step: "lent F (\<lambda>X. T X \<inter> {..<j}) \<le> (\<Sum>i<j. lent F (\<lambda>X. i \<in> T X))" for j :: nat
  proof (induction j)
    case 0 then show ?case using lent_const[OF fin ne, of "{}::nat set"] by simp
  next
    case (Suc j)
    have "lent F (\<lambda>X. T X \<inter> {..<Suc j}) = lent F (\<lambda>X. (T X \<inter> {..<j}, j \<in> T X))"
    proof (rule lent_cong, intro ballI)
      fix X Y
      have "{..<Suc j} = insert j {..<j}" by auto
      then show "(T X \<inter> {..<Suc j} = T Y \<inter> {..<Suc j}) = ((T X \<inter> {..<j}, j \<in> T X) = (T Y \<inter> {..<j}, j \<in> T Y))"
        by auto
    qed
    also have "\<dots> \<le> lent F (\<lambda>X. T X \<inter> {..<j}) + lent F (\<lambda>X. j \<in> T X)" by (rule lent_pair[OF fin ne])
    also have "\<dots> \<le> (\<Sum>i<j. lent F (\<lambda>X. i \<in> T X)) + lent F (\<lambda>X. j \<in> T X)" using Suc.IH by simp
    also have "\<dots> = (\<Sum>i<Suc j. lent F (\<lambda>X. i \<in> T X))" by simp
    finally show ?case .
  qed
  have "lent F T = lent F (\<lambda>X. T X \<inter> {..<N})"
    by (rule lent_cong) (use TN in \<open>auto simp: Int_absorb2\<close>)
  then show ?thesis using step[of N] by simp
qed

theorem lent_bool:
  assumes fin: "finite F" and ne: "F \<noteq> {}"
  shows "lent F P = bent (real (card {X\<in>F. P X}) / real (card F))"
proof -
  define N where "N = real (card F)"
  define A where "A = real (card {X\<in>F. P X})"
  define B where "B = real (card {X\<in>F. \<not> P X})"
  have N: "0 < N" unfolding N_def using fin ne by (simp add: card_gt_0_iff)
  have AB: "A + B = N"
  proof -
    have "card F = card {X\<in>F. P X} + card {X\<in>F. \<not> P X}"
      using sum_split_pred[OF fin, of "\<lambda>_. (1::nat)" P] by simp
    then show ?thesis unfolding A_def B_def N_def by simp
  qed
  have A0: "0 \<le> A" and B0: "0 \<le> B" unfolding A_def B_def by simp_all
  have lP: "lcls F P X = card {X\<in>F. P X}" if "P X" for X
    unfolding lcls_def using that by (metis (full_types))
  have lN: "lcls F P X = card {X\<in>F. \<not> P X}" if "\<not> P X" for X
    unfolding lcls_def using that by (metis (full_types))
  have S: "(\<Sum>X\<in>F. ln (real (lcls F P X))) = A * ln A + B * ln B"
  proof -
    have "(\<Sum>X\<in>F. ln (real (lcls F P X)))
        = (\<Sum>X\<in>{X\<in>F. P X}. ln (real (lcls F P X))) + (\<Sum>X\<in>{X\<in>F. \<not> P X}. ln (real (lcls F P X)))"
      by (rule sum_split_pred[OF fin])
    also have "(\<Sum>X\<in>{X\<in>F. P X}. ln (real (lcls F P X))) = A * ln A"
      unfolding A_def using lP by simp
    also have "(\<Sum>X\<in>{X\<in>F. \<not> P X}. ln (real (lcls F P X))) = B * ln B"
      unfolding B_def using lN by simp
    finally show ?thesis .
  qed
  have lent: "lent F P = ln N - (A * ln A + B * ln B) / N" unfolding lent_def S N_def ..
  have oneA: "1 - A / N = B / N" using AB N by (simp add: field_simps)
  have tA: "A / N * ln (A / N) = A / N * ln A - A / N * ln N"
  proof (cases "A = 0")
    case True then show ?thesis by simp
  next
    case False then have "0 < A" using A0 by simp
    then show ?thesis using N by (simp add: ln_div right_diff_distrib)
  qed
  have tB: "B / N * ln (B / N) = B / N * ln B - B / N * ln N"
  proof (cases "B = 0")
    case True then show ?thesis by simp
  next
    case False then have "0 < B" using B0 by simp
    then show ?thesis using N by (simp add: ln_div right_diff_distrib)
  qed
  have "bent (A / N) = - (A / N * ln (A / N)) - B / N * ln (B / N)" unfolding bent_def oneA by simp
  also have "\<dots> = (A + B) / N * ln N - (A * ln A + B * ln B) / N" unfolding tA tB using N by (simp add: field_simps)
  also have "\<dots> = ln N - (A * ln A + B * ln B) / N" using AB N by simp
  finally show ?thesis unfolding lent A_def N_def by simp
qed

lemma lent_max:
  assumes fin: "finite F" and ne: "F \<noteq> {}" and M: "\<forall>X\<in>F. real (lcls F g X) \<le> M"
  shows "ln (real (card F)) \<le> lent F g + ln M"
proof -
  define N where "N = real (card F)"
  have N: "0 < N" unfolding N_def using fin ne by (simp add: card_gt_0_iff)
  have "(\<Sum>X\<in>F. ln (real (lcls F g X))) \<le> (\<Sum>X\<in>F. ln M)"
    by (rule sum_mono, rule ln_mono) (use M lcls_pos[OF fin] in auto)
  also have "\<dots> = N * ln M" unfolding N_def by simp
  finally have "(\<Sum>X\<in>F. ln (real (lcls F g X))) / N \<le> ln M" using N by (simp add: field_simps)
  then show ?thesis unfolding lent_def N_def[symmetric] by simp
qed

theorem closed_entropy:
  fixes N :: nat
  assumes finF: "finite F" and ne: "F \<noteq> {}" and finV: "finite V"
    and tr: "\<forall>X\<in>F. \<forall>e\<in>H. e \<inter> X \<noteq> {}"
    and BV: "\<forall>i<N. B i \<subseteq> V" and Bm: "\<forall>i<N. card (B i) \<le> m" and m: "0 < m"
    and cov: "\<forall>X\<in>F. \<forall>v\<in>X. \<exists>i<N. v \<in> B i \<and> bclosed H X (B i)"
  shows "ln (real (card F)) \<le> (\<Sum>i<N. bent (real (card {X\<in>F. bclosed H X (B i)}) / real (card F)))
    + real (card V) * (ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m))"
proof -
  define c where "c = ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m)"
  define g where "g = closedset H B N"
  have finB: "\<forall>i<N. finite (B i)" using BV finV finite_subset by blast
  have M: "\<forall>X\<in>F. real (lcls F g X) \<le> exp (real (card V) * c)"
  proof
    fix X assume X: "X \<in> F"
    define T where "T = g X"
    define G where "G = {Y\<in>F. closedset H B N Y = T}"
    have TN: "T \<subseteq> {..<N}" unfolding T_def g_def closedset_def by blast
    have "card G \<le> (\<Prod>i\<in>T. card (part B T i) choose (card (part B T i) div 2))"
    proof (rule closed_fixed[OF _ _ _ _ _ TN])
      show "finite G" using finF unfolding G_def by simp
      show "\<forall>X\<in>G. \<forall>e\<in>H. e \<inter> X \<noteq> {}" using tr unfolding G_def by blast
      show "\<forall>X\<in>G. \<forall>i\<in>T. bclosed H X (B i)" unfolding G_def closedset_def by blast
      show "\<forall>X\<in>G. X \<subseteq> \<Union>(B ` T)"
      proof (intro ballI subsetI)
        fix Y v assume Y: "Y \<in> G" and v: "v \<in> Y"
        obtain i where "i < N" "v \<in> B i" "bclosed H Y (B i)" using cov Y v unfolding G_def by blast
        then have "i \<in> T" using Y unfolding G_def closedset_def by blast
        then show "v \<in> \<Union>(B ` T)" using \<open>v \<in> B i\<close> by blast
      qed
      show "\<forall>i\<in>T. finite (B i)" using finB TN by blast
    qed
    moreover have "lcls F g X = card G" unfolding lcls_def G_def T_def g_def by (simp add: eq_commute)
    ultimately have "lcls F g X \<le> (\<Prod>i\<in>T. card (part B T i) choose (card (part B T i) div 2))" by simp
    then have "real (lcls F g X) \<le> real (\<Prod>i\<in>T. card (part B T i) choose (card (part B T i) div 2))" by (rule of_nat_mono)
    also have "\<dots> \<le> exp (real (card V) * c)"
      unfolding c_def by (rule prod_bound[OF finV BV Bm m]) (use TN in blast)
    finally show "real (lcls F g X) \<le> exp (real (card V) * c)" .
  qed
  have "ln (real (card F)) \<le> lent F g + ln (exp (real (card V) * c))" by (rule lent_max[OF finF ne M])
  also have "ln (exp (real (card V) * c)) = real (card V) * c" by simp
  also have "lent F g \<le> (\<Sum>i<N. lent F (\<lambda>X. i \<in> g X))"
    by (rule lent_bits[OF finF ne]) (simp add: g_def closedset_def subset_iff)
  also have "(\<Sum>i<N. lent F (\<lambda>X. i \<in> g X)) = (\<Sum>i<N. bent (real (card {X\<in>F. bclosed H X (B i)}) / real (card F)))"
  proof (rule sum.cong[OF refl])
    fix i assume "i \<in> {..<N}"
    then have "(\<lambda>X. i \<in> g X) = (\<lambda>X. bclosed H X (B i))" unfolding g_def closedset_def by auto
    then show "lent F (\<lambda>X. i \<in> g X) = bent (real (card {X\<in>F. bclosed H X (B i)}) / real (card F))"
      using lent_bool[OF finF ne, of "\<lambda>X. bclosed H X (B i)"] by simp
  qed
  finally show ?thesis unfolding c_def by simp
qed

corollary clique_entropy:
  fixes N :: nat
  assumes finV: "finite V" and BV: "\<forall>i<N. B i \<subseteq> V" and Bm: "\<forall>i<N. card (B i) \<le> m" and m: "0 < m"
    and inside: "\<forall>e\<in>H. \<exists>i<N. e \<subseteq> B i \<and> card e = Suc (c i)"
    and full: "\<forall>i<N. \<forall>e. e \<subseteq> B i \<and> card e = Suc (c i) \<longrightarrow> e \<in> H"
    and ne: "{X. X \<subseteq> V \<and> mtr H X} \<noteq> {}"
  shows "ln (real (card {X. X \<subseteq> V \<and> mtr H X}))
    \<le> (\<Sum>i<N. bent (real (card {X\<in>{X. X \<subseteq> V \<and> mtr H X}. bclosed H X (B i)}) / real (card {X. X \<subseteq> V \<and> mtr H X})))
      + real (card V) * (ln 2 - ln ((3 * real m + 2) / 2) / (2 * real m))"
proof (rule closed_entropy[OF _ ne finV _ BV Bm m])
  have finB: "\<forall>i<N. finite (B i)" using BV finV finite_subset by blast
  show "finite {X. X \<subseteq> V \<and> mtr H X}" by (rule finite_subset[of _ "Pow V"]) (use finV in auto)
  show "\<forall>X\<in>{X. X \<subseteq> V \<and> mtr H X}. \<forall>e\<in>H. e \<inter> X \<noteq> {}" unfolding mtr_def tr_def by blast
  show "\<forall>X\<in>{X. X \<subseteq> V \<and> mtr H X}. \<forall>v\<in>X. \<exists>i<N. v \<in> B i \<and> bclosed H X (B i)"
    using clique_closed[OF finB inside full] by blast
qed

end
