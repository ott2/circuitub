theory Shearer_Sub
  imports Complex_Main
begin

text \<open>
  Shearer's inequality for submodular set functions (the form of Madiman and Tetali): if
  \<open>h\<close> on subsets of \<open>{..<n}\<close> has \<open>h {} = 0\<close>, nonnegative increments along the prefixes, and
  diminishing increments when adding \<open>i\<close> to subsets of the prefix \<open>{..<i}\<close>, then every
  fractional cover (\<open>\<Sum>\<^sub>B\<^sub>\<ni>\<^sub>i w B \<ge> 1\<close>) has \<open>h {..<n} \<le> \<Sum>\<^sub>B w B * h B\<close>. With \<open>h B = H(X\<^sub>B)\<close> this is
  Shearer's lemma; the entropy instance is a separate step (log \<section>6c, \<section>6f).
\<close>

lemma telescope_set:
  fixes h :: "nat set \<Rightarrow> real"
  assumes "B \<subseteq> {..<n}"
  shows "h B - h {} = (\<Sum>i<n. h (B \<inter> {..<Suc i}) - h (B \<inter> {..<i}))"
proof -
  have "(\<Sum>i<n. h (B \<inter> {..<Suc i}) - h (B \<inter> {..<i})) = h (B \<inter> {..<n}) - h (B \<inter> {..<0})"
    by (rule sum_lessThan_telescope[of "\<lambda>i. h (B \<inter> {..<i})" n])
  moreover have "B \<inter> {..<n} = B" using assms by blast
  moreover have "B \<inter> {..<0} = {}" by simp
  ultimately show ?thesis by simp
qed

theorem shearer_sub:
  fixes h w :: "nat set \<Rightarrow> real"
  assumes h0: "h {} = 0"
    and mono: "\<forall>i<n. h {..<i} \<le> h {..<Suc i}"
    and sub: "\<forall>A i. A \<subseteq> {..<i} \<longrightarrow> i < n \<longrightarrow>
                h (insert i {..<i}) - h {..<i} \<le> h (insert i A) - h A"
    and fin: "finite \<B>" and Bsub: "\<forall>B\<in>\<B>. B \<subseteq> {..<n}" and w0: "\<forall>B\<in>\<B>. 0 \<le> w B"
    and cover: "\<forall>i<n. 1 \<le> (\<Sum>B\<in>\<B>. if i \<in> B then w B else 0)"
  shows "h {..<n} \<le> (\<Sum>B\<in>\<B>. w B * h B)"
proof -
  define D where "D i = h {..<Suc i} - h {..<i}" for i
  have D0: "0 \<le> D i" if "i < n" for i using mono that unfolding D_def by auto
  have step: "(if i \<in> B then D i else 0) \<le> h (B \<inter> {..<Suc i}) - h (B \<inter> {..<i})"
    if i: "i < n" for B i
  proof (cases "i \<in> B")
    case True
    have e1: "B \<inter> {..<Suc i} = insert i (B \<inter> {..<i})" using True by auto
    have e2: "{..<Suc i} = insert i {..<i}" by auto
    have Bi: "B \<inter> {..<i} \<subseteq> {..<i}" by blast
    have "h (insert i {..<i}) - h {..<i} \<le> h (insert i (B \<inter> {..<i})) - h (B \<inter> {..<i})"
      using spec[OF spec[OF sub, of "B \<inter> {..<i}"], of i] Bi i by blast
    then show ?thesis using True unfolding D_def e1 e2 by simp
  next
    case False
    then have "B \<inter> {..<Suc i} = B \<inter> {..<i}" by (auto simp: less_Suc_eq)
    then show ?thesis using False by simp
  qed
  have hB: "(\<Sum>i<n. if i \<in> B then D i else 0) \<le> h B" if B: "B \<subseteq> {..<n}" for B
  proof -
    have "(\<Sum>i<n. if i \<in> B then D i else 0) \<le> (\<Sum>i<n. h (B \<inter> {..<Suc i}) - h (B \<inter> {..<i}))"
      by (rule sum_mono) (use step in auto)
    also have "\<dots> = h B - h {}" by (rule telescope_set[OF B, symmetric])
    finally show ?thesis using h0 by simp
  qed
  have "h {..<n} = h {..<n} - h {..<0}" using h0 by simp
  also have "\<dots> = (\<Sum>i<n. D i)" unfolding D_def by (rule sum_lessThan_telescope[symmetric])
  also have "\<dots> \<le> (\<Sum>i<n. D i * (\<Sum>B\<in>\<B>. if i \<in> B then w B else 0))"
  proof (rule sum_mono)
    fix i assume "i \<in> {..<n}"
    then have "i < n" by simp
    then have "D i * 1 \<le> D i * (\<Sum>B\<in>\<B>. if i \<in> B then w B else 0)"
      using D0 cover by (intro mult_left_mono) auto
    then show "D i \<le> D i * (\<Sum>B\<in>\<B>. if i \<in> B then w B else 0)" by simp
  qed
  also have "\<dots> = (\<Sum>i<n. \<Sum>B\<in>\<B>. w B * (if i \<in> B then D i else 0))"
  proof (rule sum.cong[OF refl])
    fix i
    have pt: "D i * (if i \<in> B then w B else 0) = w B * (if i \<in> B then D i else 0)" for B
      by simp
    show "D i * (\<Sum>B\<in>\<B>. if i \<in> B then w B else 0) = (\<Sum>B\<in>\<B>. w B * (if i \<in> B then D i else 0))"
      unfolding sum_distrib_left pt ..
  qed
  also have "\<dots> = (\<Sum>B\<in>\<B>. \<Sum>i<n. w B * (if i \<in> B then D i else 0))" by (rule sum.swap)
  also have "\<dots> = (\<Sum>B\<in>\<B>. w B * (\<Sum>i<n. if i \<in> B then D i else 0))"
    by (simp add: sum_distrib_left)
  also have "\<dots> \<le> (\<Sum>B\<in>\<B>. w B * h B)"
    by (rule sum_mono) (use w0 Bsub hB in \<open>auto intro: mult_left_mono\<close>)
  finally show ?thesis .
qed

end
