theory Test
  imports Formula
begin

section \<open>Splitting the input into blocks\<close>

function chop :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "chop c xs = (if c = 0 \<or> xs = [] then [] else take c xs # chop c (drop c xs))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(c, xs). length xs)") auto

declare chop.simps [simp del]

lemma chop_Nil [simp]: "chop c [] = []"
  by (simp add: chop.simps)

lemma chop_0 [simp]: "chop 0 xs = []"
  by (simp add: chop.simps)

text \<open>Guarded unfolding: rewriting with \<open>chop.simps\<close> itself loops.\<close>

lemma chop_Cons: "c > 0 \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> chop c xs = take c xs # chop c (drop c xs)"
  by (subst chop.simps) simp

lemma concat_chop: "c > 0 \<Longrightarrow> concat (chop c xs) = xs"
proof (induction c xs rule: chop.induct)
  case (1 c xs)
  show ?case
  proof (cases "xs = []")
    case False
    with 1 have "concat (chop c (drop c xs)) = drop c xs" by simp
    with False 1(2) show ?thesis by (simp add: chop_Cons)
  qed simp
qed

lemma chop_lengths: "\<forall>ys \<in> set (chop c xs). length ys \<le> c"
proof (induction c xs rule: chop.induct)
  case (1 c xs)
  show ?case
  proof (cases "c = 0 \<or> xs = []")
    case True
    then show ?thesis by (auto simp: chop.simps)
  next
    case False
    with 1 have IH: "\<forall>ys \<in> set (chop c (drop c xs)). length ys \<le> c" by simp
    from False have "chop c xs = take c xs # chop c (drop c xs)" by (simp add: chop_Cons)
    with IH show ?thesis by auto
  qed
qed

lemma length_chop_le: "c > 0 \<Longrightarrow> length xs \<le> k * c \<Longrightarrow> length (chop c xs) \<le> k"
proof (induction c xs arbitrary: k rule: chop.induct)
  case (1 c xs)
  have c: "0 < c" using "1.prems" by simp
  have len: "length xs \<le> k * c" using "1.prems" by simp
  show ?case
  proof (cases "xs = []")
    case False
    have "0 < length xs" using False by simp
    from this len have "0 < k * c" by (rule less_le_trans)
    then have "0 < k" by auto
    then obtain k2 where k: "k = Suc k2" by (cases k) auto
    have d: "length (drop c xs) \<le> k2 * c" using len k by simp
    have "length (chop c (drop c xs)) \<le> k2"
      using "1.IH" False c d by simp
    with False c k show ?thesis by (simp add: chop_Cons)
  qed simp
qed

text \<open>
  \<open>blocks k L\<close> splits \<open>L\<close> into exactly \<open>k\<close> blocks, each of length at most \<open>\<lceil>|L|/k\<rceil>\<close>,
  padding with empty blocks if the chunks do not fill all \<open>k\<close> slots.
\<close>

definition bsize :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bsize k n = (n + k - 1) div k"

definition blocks :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "blocks k L = chop (bsize k (length L)) L
                  @ replicate (k - length (chop (bsize k (length L)) L)) []"

lemma bsize_bound:
  assumes k: "k > 0" shows "n \<le> k * bsize k n"
proof -
  obtain k2 where ksuc: "k = Suc k2" using k by (cases k) auto
  have b: "k * bsize k n = k * ((n + k2) div k)" using ksuc by (simp add: bsize_def)
  have m: "k * ((n + k2) div k) + (n + k2) mod k = n + k2"
    by (simp add: mult_div_mod_eq)
  have r: "(n + k2) mod k < k" using k by simp
  from b m r ksuc show ?thesis by linarith
qed

lemma bsize_pos:
  assumes "k > 0" "n > 0" shows "bsize k n > 0"
proof -
  obtain k2 where k2: "k = Suc k2" using assms by (cases k) auto
  have "k \<le> n + k2" using assms k2 by simp
  then show ?thesis using assms k2 by (simp add: bsize_def div_greater_zero_iff)
qed

lemma concat_replicate_Nil [simp]: "concat (replicate m []) = []"
  by (induction m) auto

lemma concat_blocks:
  assumes k: "k > 0" shows "concat (blocks k L) = L"
proof (cases "L = []")
  case False
  with k have "bsize k (length L) > 0" by (simp add: bsize_pos)
  then show ?thesis by (simp add: blocks_def concat_chop)
qed (simp add: blocks_def)

lemma length_blocks:
  assumes k: "k > 0" shows "length (blocks k L) = k"
proof (cases "L = []")
  case False
  with k have c: "bsize k (length L) > 0" by (simp add: bsize_pos)
  from k have "length L \<le> k * bsize k (length L)" by (rule bsize_bound)
  with c have "length (chop (bsize k (length L)) L) \<le> k" by (rule length_chop_le)
  then show ?thesis by (simp add: blocks_def)
qed (simp add: blocks_def)

lemma blocks_lengths: "\<forall>B \<in> set (blocks k L). length B \<le> bsize k (length L)"
  using chop_lengths[of "bsize k (length L)" L]
  by (auto simp: blocks_def in_set_replicate)

section \<open>The test predicate\<close>

text \<open>
  The paper's test (Section 3): given blocks \<open>Bs\<close> and shifts \<open>ss\<close>, the test passes iff the
  shifted block weights \<open>w\<^sub>i + s\<^sub>i\<close> are pairwise distinct modulo \<open>k\<close>.
\<close>

definition shifted :: "nat \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v lit list list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "shifted k \<sigma> Bs ss = map (\<lambda>p. (cnt \<sigma> (fst p) + snd p) mod k) (zip Bs ss)"

definition passes :: "nat \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v lit list list \<Rightarrow> nat list \<Rightarrow> bool" where
  "passes k \<sigma> Bs ss = distinct (shifted k \<sigma> Bs ss)"

text \<open>The admissibility constraint on the shifts, eq. (3) of the paper:
  \<open>\<Sum> s\<^sub>i \<equiv> \<binom>k 2 - t\<close>, stated without subtraction as \<open>\<Sum> s\<^sub>i + t \<equiv> \<binom>k 2\<close>.\<close>

definition adm :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "adm k t ss = ((sum_list ss + t) mod k = (\<Sum>i<k. i) mod k)"

subsection \<open>Arithmetic groundwork\<close>

lemma mod_add_cancel_nat:
  fixes a b s k :: nat
  assumes k: "k > 0" and eq: "(a + s) mod k = (b + s) mod k"
  shows "a mod k = b mod k"
proof -
  have sk: "s + s * (k - 1) = s * k" using k by (cases k) (auto simp: algebra_simps)
  have "(a + s + s * (k - 1)) mod k = ((a + s) mod k + s * (k - 1)) mod k"
    by (simp add: mod_add_left_eq)
  also have "\<dots> = ((b + s) mod k + s * (k - 1)) mod k" using eq by simp
  also have "\<dots> = (b + s + s * (k - 1)) mod k" by (simp add: mod_add_left_eq)
  finally have star: "(a + s + s * (k - 1)) mod k = (b + s + s * (k - 1)) mod k" .
  have e1: "a + s + s * (k - 1) = a + s * k" by (simp only: add.assoc sk)
  have e2: "b + s + s * (k - 1) = b + s * k" by (simp only: add.assoc sk)
  from star have "(a + s * k) mod k = (b + s * k) mod k" by (simp only: e1 e2)
  then show ?thesis by simp
qed

lemma mod_add_right_cong:
  fixes a b x k :: nat
  assumes "a mod k = b mod k" shows "(x + a) mod k = (x + b) mod k"
proof -
  have "(x + a) mod k = (x + a mod k) mod k" by (simp add: mod_add_right_eq)
  also have "\<dots> = (x + b mod k) mod k" using assms by simp
  also have "\<dots> = (x + b) mod k" by (simp add: mod_add_right_eq)
  finally show ?thesis .
qed

lemma sum_list_mod:
  fixes f :: "'a \<Rightarrow> nat"
  shows "sum_list (map (\<lambda>x. f x mod k) xs) mod k = sum_list (map f xs) mod k"
proof (induction xs)
  case (Cons a xs)
  have "sum_list (map (\<lambda>x. f x mod k) (a # xs)) mod k
      = (f a mod k + sum_list (map (\<lambda>x. f x mod k) xs)) mod k" by simp
  also have "\<dots> = (f a mod k + sum_list (map f xs)) mod k"
    using Cons.IH by (rule mod_add_right_cong)
  also have "\<dots> = (f a + sum_list (map f xs)) mod k" by (simp add: mod_add_left_eq)
  finally show ?case by simp
qed simp

lemma sum_list_zip_add:
  fixes h :: "'a \<Rightarrow> nat" and ss :: "nat list"
  assumes "length Bs = length ss"
  shows "sum_list (map (\<lambda>p. h (fst p) + snd p) (zip Bs ss)) = sum_list (map h Bs) + sum_list ss"
proof -
  have "sum_list (map (\<lambda>p. h (fst p) + snd p) (zip Bs ss))
      = sum_list (map (\<lambda>p. h (fst p)) (zip Bs ss)) + sum_list (map snd (zip Bs ss))"
    by (simp add: sum_list_addf)
  moreover have "map (\<lambda>p. h (fst p)) (zip Bs ss) = map h (map fst (zip Bs ss))" by simp
  moreover have "map fst (zip Bs ss) = Bs" using assms by simp
  moreover have "map snd (zip Bs ss) = ss" using assms by simp
  ultimately show ?thesis by simp
qed

lemma sum_shifted:
  assumes "length Bs = length ss"
  shows "sum_list (shifted k \<sigma> Bs ss) mod k = (cnt \<sigma> (concat Bs) + sum_list ss) mod k"
proof -
  have "sum_list (shifted k \<sigma> Bs ss) mod k
      = sum_list (map (\<lambda>p. cnt \<sigma> (fst p) + snd p) (zip Bs ss)) mod k"
    unfolding shifted_def
    by (rule sum_list_mod[of "\<lambda>p. cnt \<sigma> (fst p) + snd p"])
  also have "\<dots> = (sum_list (map (cnt \<sigma>) Bs) + sum_list ss) mod k"
    using assms by (simp add: sum_list_zip_add)
  finally show ?thesis by (simp add: cnt_concat)
qed

text \<open>A distinct list of \<open>k\<close> residues mod \<open>k\<close> is a permutation of \<open>[0 ..< k]\<close>, so its sum
  is \<open>\<binom>k 2\<close>.  This is the paper's \<open>0 + 1 + \<dots> + (k-1) \<equiv> \<binom>k 2\<close> step.\<close>

lemma sum_list_distinct_residues:
  assumes "length xs = k" "distinct xs" "set xs \<subseteq> {..<k}"
  shows "sum_list xs = (\<Sum>i<k. i)"
proof -
  have c: "card (set xs) = k" using assms by (simp add: distinct_card)
  have eq: "set xs = {..<k}"
  proof (rule card_subset_eq)
    show "finite {..<k}" by simp
    show "set xs \<subseteq> {..<k}" by (rule assms(3))
    show "card (set xs) = card {..<k}" using c by simp
  qed
  have "sum_list xs = sum_list (map (\<lambda>x. x) xs)" by simp
  also have "\<dots> = sum (\<lambda>x. x) (set xs)"
    using assms(2) by (rule sum_list_distinct_conv_sum_set)
  also have "\<dots> = (\<Sum>i<k. i)" using eq by simp
  finally show ?thesis .
qed

lemma passes_sum:
  assumes "length Bs = k" "length ss = k" "k > 0" "passes k \<sigma> Bs ss"
  shows "sum_list (shifted k \<sigma> Bs ss) = (\<Sum>i<k. i)"
proof (rule sum_list_distinct_residues)
  show "length (shifted k \<sigma> Bs ss) = k" using assms by (simp add: shifted_def)
  show "distinct (shifted k \<sigma> Bs ss)" using assms by (simp add: passes_def)
  show "set (shifted k \<sigma> Bs ss) \<subseteq> {..<k}" using \<open>k > 0\<close> by (auto simp: shifted_def)
qed

subsection \<open>Soundness: passing the test certifies the weight mod \<open>k\<close>\<close>

theorem test_sound:
  assumes "length Bs = k" "length ss = k" "k > 0"
    and "adm k t ss" and "passes k \<sigma> Bs ss"
  shows "cnt \<sigma> (concat Bs) mod k = t mod k"
proof -
  have A: "sum_list (shifted k \<sigma> Bs ss) = (\<Sum>i<k. i)"
    using assms(1,2,3,5) by (rule passes_sum)
  have B: "sum_list (shifted k \<sigma> Bs ss) mod k = (cnt \<sigma> (concat Bs) + sum_list ss) mod k"
    using assms(1,2) by (simp add: sum_shifted)
  from A B have "(\<Sum>i<k. i) mod k = (cnt \<sigma> (concat Bs) + sum_list ss) mod k" by simp
  with assms(4) have "(sum_list ss + t) mod k = (cnt \<sigma> (concat Bs) + sum_list ss) mod k"
    by (simp add: adm_def)
  then have "(t + sum_list ss) mod k = (cnt \<sigma> (concat Bs) + sum_list ss) mod k"
    by (simp add: add.commute)
  then have "t mod k = cnt \<sigma> (concat Bs) mod k"
    using \<open>k > 0\<close> by (rule mod_add_cancel_nat[rotated])
  then show ?thesis by simp
qed

subsection \<open>Admissibility is implied, for an input of the right weight\<close>

text \<open>
  We sample shifts from all of \<open>{0..<k}\<^sup>k\<close> rather than from the admissible subspace of
  size \<open>k\<^sup>k\<^sup>-\<^sup>1\<close>.  Nothing is lost: if a shift vector accepts an input whose weight is
  already \<open>t\<close> mod \<open>k\<close>, that shift vector is automatically admissible.
\<close>

theorem passes_imp_adm:
  assumes "length Bs = k" "length ss = k" "k > 0"
    and "cnt \<sigma> (concat Bs) mod k = t mod k" and "passes k \<sigma> Bs ss"
  shows "adm k t ss"
proof -
  have A: "sum_list (shifted k \<sigma> Bs ss) = (\<Sum>i<k. i)"
    using assms(1,2,3,5) by (rule passes_sum)
  have B: "sum_list (shifted k \<sigma> Bs ss) mod k = (cnt \<sigma> (concat Bs) + sum_list ss) mod k"
    using assms(1,2) by (simp add: sum_shifted)
  have C: "(cnt \<sigma> (concat Bs) + sum_list ss) mod k = (t + sum_list ss) mod k"
  proof -
    have "(cnt \<sigma> (concat Bs) + sum_list ss) mod k
        = (cnt \<sigma> (concat Bs) mod k + sum_list ss) mod k"
      by (simp add: mod_add_left_eq)
    also have "\<dots> = (t mod k + sum_list ss) mod k" using assms(4) by simp
    also have "\<dots> = (t + sum_list ss) mod k" by (simp add: mod_add_left_eq)
    finally show ?thesis .
  qed
  from A B C have "(\<Sum>i<k. i) mod k = (t + sum_list ss) mod k" by simp
  then show ?thesis by (simp add: adm_def add.commute)
qed

end
