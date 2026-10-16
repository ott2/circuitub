theory Private_Design
  imports Main
begin

text \<open>
  The exact obstruction to selector mixtures (log \<section>6f). Switching needs each block
  \<open>C\<close> (the helpers outside \<open>X\<close> for one selector) to contain a private \<open>a\<close>-set, lying in no
  other block. If all \<open>a\<close>-sets of \<open>Y\<close> lie in equally many blocks, as in a \<open>t\<close>-design with
  \<open>t \<ge> a\<close>, then one private \<open>a\<close>-set makes every \<open>a\<close>-set lie in at most one block, so two blocks
  share fewer than \<open>a\<close> points (\<open>private_design\<close>). Three such blocks of size \<open>\<ge> |Y|/2\<close> then
  force \<open>|Y| < 6a\<close> (\<open>three_blocks\<close>).
\<close>

lemma private_design:
  assumes finY: "finite Y" and CY: "\<forall>C\<in>\<C>. C \<subseteq> Y"
    and reg: "\<forall>A B. A \<subseteq> Y \<longrightarrow> B \<subseteq> Y \<longrightarrow> card A = a \<longrightarrow> card B = a \<longrightarrow>
                card {C\<in>\<C>. A \<subseteq> C} = card {C\<in>\<C>. B \<subseteq> C}"
    and priv: "A0 \<subseteq> Y" "card A0 = a" "card {C\<in>\<C>. A0 \<subseteq> C} = 1"
    and C: "C \<in> \<C>" "C' \<in> \<C>" "C \<noteq> C'"
  shows "card (C \<inter> C') < a"
proof (rule ccontr)
  assume "\<not> card (C \<inter> C') < a"
  then have "a \<le> card (C \<inter> C')" by simp
  then obtain A where A: "A \<subseteq> C \<inter> C'" "card A = a" by (rule obtain_subset_with_card_n)
  have AY: "A \<subseteq> Y" using A(1) CY C(1) by blast
  have finC: "finite \<C>" by (rule finite_subset[of _ "Pow Y"]) (use CY finY in auto)
  have "{C, C'} \<subseteq> {D\<in>\<C>. A \<subseteq> D}" using A(1) C(1,2) by blast
  then have "card {C, C'} \<le> card {D\<in>\<C>. A \<subseteq> D}" by (rule card_mono[rotated]) (use finC in simp)
  moreover have "card {C, C'} = 2" using C(3) by simp
  moreover have "card {D\<in>\<C>. A \<subseteq> D} = card {D\<in>\<C>. A0 \<subseteq> D}"
    using reg AY priv(1) A(2) priv(2) by blast
  ultimately show False using priv(3) by simp
qed

lemma three_blocks:
  assumes finY: "finite Y" and sub: "C1 \<subseteq> Y" "C2 \<subseteq> Y" "C3 \<subseteq> Y"
    and small: "card (C1 \<inter> C2) < a" "card (C1 \<inter> C3) < a" "card (C2 \<inter> C3) < a"
  shows "card C1 + card C2 + card C3 < card Y + 3 * a"
proof -
  have f: "finite C1" "finite C2" "finite C3"
    using sub finY by (auto intro: finite_subset)
  have e1: "card (C1 \<union> C2) + card (C1 \<inter> C2) = card C1 + card C2"
    by (rule card_Un_Int[OF f(1,2), symmetric])
  have e2: "card (C1 \<union> C2 \<union> C3) + card ((C1 \<union> C2) \<inter> C3) = card (C1 \<union> C2) + card C3"
    by (rule card_Un_Int[symmetric]) (use f in auto)
  have "card ((C1 \<union> C2) \<inter> C3) = card ((C1 \<inter> C3) \<union> (C2 \<inter> C3))"
    by (simp only: Int_Un_distrib2)
  also have "\<dots> \<le> card (C1 \<inter> C3) + card (C2 \<inter> C3)" by (rule card_Un_le)
  finally have i: "card ((C1 \<union> C2) \<inter> C3) \<le> card (C1 \<inter> C3) + card (C2 \<inter> C3)" .
  have u: "card (C1 \<union> C2 \<union> C3) \<le> card Y" by (rule card_mono[OF finY]) (use sub in blast)
  show ?thesis using e1 e2 i u small by linarith
qed

corollary half_blocks:
  assumes "finite Y" "C1 \<subseteq> Y" "C2 \<subseteq> Y" "C3 \<subseteq> Y"
    and "card (C1 \<inter> C2) < a" "card (C1 \<inter> C3) < a" "card (C2 \<inter> C3) < a"
    and "card Y \<le> 2 * card C1" "card Y \<le> 2 * card C2" "card Y \<le> 2 * card C3"
  shows "card Y < 6 * a"
  using three_blocks[OF assms(1-7)] assms(8-10) by linarith

end
