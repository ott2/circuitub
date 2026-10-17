theory Shearer_Conditional
  imports Shearer_Typical
begin

text \<open>
  The conditional certificate (log \<section>6g): the fractional cover, the centres and \<open>\<theta>\<close> may depend
  on a label \<open>g X\<close>, at the cost of the label's entropy. Since \<open>X\<close> is uniform on each class
  \<open>{Y \<in> F. g Y = g X}\<close>, \<open>ln |F| = H(g) + E ln |class|\<close> (the definition of \<open>lent\<close>), and each class
  is bounded by \<open>certificate_dev\<close> (\<open>certificate_cond\<close>). \<open>lent_image\<close>: \<open>H(g) \<le> ln |g ` F|\<close>.
\<close>

definition cbound :: "nat set set \<Rightarrow> real \<Rightarrow> nat set set \<Rightarrow> (nat set \<Rightarrow> real) \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> real" where
  "cbound G \<theta> \<B> w c = (\<Sum>B\<in>\<B>. w B * (real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2
     + (ln ((1 + \<theta>) / (1 - \<theta>)) - ln \<theta> * ((\<Sum>X\<in>G. \<bar>real (card (X \<inter> B)) - real (c B)\<bar>) / real (card G)))))"

lemma lent_image:
  assumes fin: "finite F" and ne: "F \<noteq> {}"
  shows "lent F g \<le> ln (real (card (g ` F)))"
proof -
  define M where "M = real (card (g ` F))"
  have M0: "0 < M" unfolding M_def using fin ne by (simp add: card_gt_0_iff)
  have qpos: "\<forall>v\<in>g ` F. 0 < (\<lambda>v. 1 / M) v" using M0 by simp
  have qsum: "(\<Sum>v\<in>g ` F. (\<lambda>v. 1 / M) v) \<le> 1" using M0 unfolding M_def by simp
  have "lent F g \<le> (\<Sum>X\<in>F. - ln ((\<lambda>v. 1 / M) (g X))) / real (card F)"
    by (rule gibbs[OF fin ne qpos qsum])
  also have "\<dots> = ln M"
    using M0 fin ne by (simp add: ln_div card_gt_0_iff)
  finally show ?thesis unfolding M_def .
qed

theorem certificate_cond:
  fixes g :: "nat set \<Rightarrow> 'u" and \<B> :: "'u \<Rightarrow> nat set set" and w :: "'u \<Rightarrow> nat set \<Rightarrow> real"
    and c :: "'u \<Rightarrow> nat set \<Rightarrow> nat" and \<theta> :: "'u \<Rightarrow> real"
  assumes fin: "finite F" and ne: "F \<noteq> {}" and FV: "F \<subseteq> Pow {..<n}"
    and finB: "\<forall>u\<in>g ` F. finite (\<B> u)" and Bsub: "\<forall>u\<in>g ` F. \<forall>B\<in>\<B> u. B \<subseteq> {..<n}"
    and w0: "\<forall>u\<in>g ` F. \<forall>B\<in>\<B> u. 0 \<le> w u B"
    and cover: "\<forall>u\<in>g ` F. \<forall>i<n. 1 \<le> (\<Sum>B\<in>\<B> u. if i \<in> B then w u B else 0)"
    and th: "\<forall>u\<in>g ` F. 0 < \<theta> u \<and> \<theta> u < 1"
  shows "ln (real (card F)) \<le> lent F g
           + (\<Sum>X\<in>F. cbound {Y\<in>F. g Y = g X} (\<theta> (g X)) (\<B> (g X)) (w (g X)) (c (g X))) / real (card F)"
proof -
  define N where "N = real (card F)"
  have N0: "0 < N" unfolding N_def using fin ne by (simp add: card_gt_0_iff)
  have key: "ln N = lent F g + (\<Sum>X\<in>F. ln (real (lcls F g X))) / N"
    unfolding lent_def N_def by simp
  have each: "ln (real (lcls F g X))
      \<le> cbound {Y\<in>F. g Y = g X} (\<theta> (g X)) (\<B> (g X)) (w (g X)) (c (g X))" if X: "X \<in> F" for X
  proof -
    define G where "G = {Y\<in>F. g Y = g X}"
    define u where "u = g X"
    have u: "u \<in> g ` F" unfolding u_def using X by blast
    have finG: "finite G" unfolding G_def using fin by simp
    have neG: "G \<noteq> {}" unfolding G_def using X by blast
    have GV: "G \<subseteq> Pow {..<n}" unfolding G_def using FV by blast
    have thu: "0 < \<theta> u" "\<theta> u < 1" using th u by auto
    have "ln (real (card G)) \<le> (\<Sum>B\<in>\<B> u. w u B * (real (card B) * ln 2 - ln ((3 * real (card B) + 2) / 2) / 2
           + (ln ((1 + \<theta> u) / (1 - \<theta> u))
           - ln (\<theta> u) * ((\<Sum>Y\<in>G. \<bar>real (card (Y \<inter> B)) - real (c u B)\<bar>) / real (card G)))))"
      by (rule certificate_dev[OF finG neG GV])
        (use finB Bsub w0 cover u thu in auto)
    then show ?thesis unfolding cbound_def lcls_def G_def u_def .
  qed
  have "(\<Sum>X\<in>F. ln (real (lcls F g X)))
      \<le> (\<Sum>X\<in>F. cbound {Y\<in>F. g Y = g X} (\<theta> (g X)) (\<B> (g X)) (w (g X)) (c (g X)))"
    by (rule sum_mono) (rule each)
  then have "(\<Sum>X\<in>F. ln (real (lcls F g X))) / N
      \<le> (\<Sum>X\<in>F. cbound {Y\<in>F. g Y = g X} (\<theta> (g X)) (\<B> (g X)) (w (g X)) (c (g X))) / N"
    by (rule divide_right_mono) (use N0 in simp)
  then show ?thesis using key unfolding N_def by linarith
qed

end
