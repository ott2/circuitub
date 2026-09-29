theory Formula
  imports Main
begin

section \<open>Unbounded fan-in AND/OR formulas over literals\<close>

text \<open>
  The circuit model of the paper (Section 2): inputs are literals \<open>x\<^sub>i\<close> or \<open>\<not>x\<^sub>i\<close>,
  gates are AND/OR of unbounded fan-in, circuits are layered and alternate, size is the
  number of gates.  We work with \<^emph>\<open>formulas\<close> (trees): every formula is in particular a
  circuit with the same number of gates, so upper bounds for formulas are upper bounds
  for circuits.  A literal \<open>Lit v b\<close> is true under \<open>\<sigma>\<close> iff \<open>\<sigma> v = b\<close>.
\<close>

datatype 'v form = Lit 'v bool | And "'v form list" | Or "'v form list"

fun eval :: "('v \<Rightarrow> bool) \<Rightarrow> 'v form \<Rightarrow> bool" where
  "eval \<sigma> (Lit v b) = (\<sigma> v = b)"
| "eval \<sigma> (And fs) = (\<forall>f\<in>set fs. eval \<sigma> f)"
| "eval \<sigma> (Or fs) = (\<exists>f\<in>set fs. eval \<sigma> f)"

text \<open>Size = number of AND/OR gates (literals are inputs, not gates).\<close>

fun gates :: "'v form \<Rightarrow> nat" where
  "gates (Lit v b) = 0"
| "gates (And fs) = Suc (sum_list (map gates fs))"
| "gates (Or fs) = Suc (sum_list (map gates fs))"

text \<open>
  Strictly layered alternating classes: \<open>sig d\<close> (\<open>\<Sigma>\<^sub>d\<close>, output gate OR) and
  \<open>pi d\<close> (\<open>\<Pi>\<^sub>d\<close>, output gate AND) of depth exactly \<open>d\<close>; depth 0 is a single literal.
  In particular \<open>sig 2\<close> formulas are DNFs and \<open>pi 2\<close> formulas are CNFs.
\<close>

fun sig :: "nat \<Rightarrow> 'v form \<Rightarrow> bool" and pi :: "nat \<Rightarrow> 'v form \<Rightarrow> bool" where
  "sig 0 f = (case f of Lit _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
| "sig (Suc d) f = (case f of Or fs \<Rightarrow> (\<forall>g\<in>set fs. pi d g) | _ \<Rightarrow> False)"
| "pi 0 f = (case f of Lit _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
| "pi (Suc d) f = (case f of And fs \<Rightarrow> (\<forall>g\<in>set fs. sig d g) | _ \<Rightarrow> False)"

section \<open>Symmetric functions of a list of literals\<close>

type_synonym 'v lit = "'v \<times> bool"

definition litval :: "('v \<Rightarrow> bool) \<Rightarrow> 'v lit \<Rightarrow> bool" where
  "litval \<sigma> l = (\<sigma> (fst l) = snd l)"

text \<open>Number of true literals in \<open>L\<close> under \<open>\<sigma>\<close>: the Hamming weight of the literal vector.\<close>

definition cnt :: "('v \<Rightarrow> bool) \<Rightarrow> 'v lit list \<Rightarrow> nat" where
  "cnt \<sigma> L = length (filter (litval \<sigma>) L)"

definition neg :: "'v lit \<Rightarrow> 'v lit" where
  "neg l = (fst l, \<not> snd l)"

lemma cnt_Nil [simp]: "cnt \<sigma> [] = 0"
  by (simp add: cnt_def)

lemma cnt_append [simp]: "cnt \<sigma> (xs @ ys) = cnt \<sigma> xs + cnt \<sigma> ys"
  by (simp add: cnt_def)

lemma cnt_le_length: "cnt \<sigma> L \<le> length L"
  by (simp add: cnt_def)

lemma cnt_concat: "cnt \<sigma> (concat xss) = sum_list (map (cnt \<sigma>) xss)"
  by (induction xss) auto

lemma cnt_map_neg: "cnt \<sigma> (map neg L) = length L - cnt \<sigma> L"
proof -
  have "length (filter (litval \<sigma>) L) + length (filter (\<lambda>l. \<not> litval \<sigma> l) L) = length L"
    by (rule sum_length_filter_compl)
  moreover have "filter (litval \<sigma>) (map neg L) = map neg (filter (\<lambda>l. \<not> litval \<sigma> l) L)"
    by (induction L) (auto simp: litval_def neg_def)
  ultimately show ?thesis
    by (simp add: cnt_def)
qed

section \<open>Negation (De Morgan dual)\<close>

fun dual :: "'v form \<Rightarrow> 'v form" where
  "dual (Lit v b) = Lit v (\<not> b)"
| "dual (And fs) = Or (map dual fs)"
| "dual (Or fs) = And (map dual fs)"

lemma eval_dual [simp]: "eval \<sigma> (dual f) = (\<not> eval \<sigma> f)"
  by (induction f) auto

lemma gates_dual [simp]: "gates (dual f) = gates f"
proof (induction f)
  case (And fs)
  then show ?case by (simp add: comp_def cong: map_cong)
next
  case (Or fs)
  then show ?case by (simp add: comp_def cong: map_cong)
qed simp

lemma sig_pi_dual: "(sig d f \<longrightarrow> pi d (dual f)) \<and> (pi d f \<longrightarrow> sig d (dual f))"
proof (induction d arbitrary: f)
  case 0
  then show ?case by (cases f) auto
next
  case (Suc d)
  then show ?case by (cases f) auto
qed

lemma pi_dual: "sig d f \<Longrightarrow> pi d (dual f)"
  and sig_dual: "pi d f \<Longrightarrow> sig d (dual f)"
  using sig_pi_dual by blast+

section \<open>Merging top gates\<close>

fun kids :: "'v form \<Rightarrow> 'v form list" where
  "kids (And fs) = fs"
| "kids (Or fs) = fs"
| "kids (Lit v b) = [Lit v b]"

definition andflat :: "'v form list \<Rightarrow> 'v form" where
  "andflat fs = And (concat (map kids fs))"

definition orflat :: "'v form list \<Rightarrow> 'v form" where
  "orflat fs = Or (concat (map kids fs))"

lemma pi_Suc_And: "pi (Suc d) f \<longleftrightarrow> (\<exists>fs. f = And fs \<and> (\<forall>g\<in>set fs. sig d g))"
  by (cases f) auto

lemma sig_Suc_Or: "sig (Suc d) f \<longleftrightarrow> (\<exists>fs. f = Or fs \<and> (\<forall>g\<in>set fs. pi d g))"
  by (cases f) auto

lemma andflat_pi:
  assumes "\<forall>f\<in>set fs. pi (Suc d) f" shows "pi (Suc d) (andflat fs)"
  using assms
proof (induction fs)
  case (Cons f fs)
  have "pi (Suc d) f" using Cons.prems by simp
  then obtain gs where "f = And gs" "\<forall>g\<in>set gs. sig d g" unfolding pi_Suc_And by blast
  with Cons show ?case by (auto simp: andflat_def)
qed (simp add: andflat_def)

lemma orflat_sig:
  assumes "\<forall>f\<in>set fs. sig (Suc d) f" shows "sig (Suc d) (orflat fs)"
  using assms
proof (induction fs)
  case (Cons f fs)
  have "sig (Suc d) f" using Cons.prems by simp
  then obtain gs where "f = Or gs" "\<forall>g\<in>set gs. pi d g" unfolding sig_Suc_Or by blast
  with Cons show ?case by (auto simp: orflat_def)
qed (simp add: orflat_def)

lemma eval_andflat:
  assumes "\<forall>f\<in>set fs. \<exists>gs. f = And gs"
  shows "eval \<sigma> (andflat fs) = (\<forall>f\<in>set fs. eval \<sigma> f)"
  using assms
proof (induction fs)
  case (Cons f fs)
  then obtain gs where "f = And gs" by auto
  with Cons show ?case by (auto simp: andflat_def)
qed (simp add: andflat_def)

lemma eval_orflat:
  assumes "\<forall>f\<in>set fs. \<exists>gs. f = Or gs"
  shows "eval \<sigma> (orflat fs) = (\<exists>f\<in>set fs. eval \<sigma> f)"
  using assms
proof (induction fs)
  case (Cons f fs)
  then obtain gs where "f = Or gs" by auto
  with Cons show ?case by (auto simp: orflat_def)
qed (simp add: orflat_def)

lemma gates_kids: "sum_list (map gates (kids f)) \<le> gates f"
  by (cases f) auto

lemma gates_andflat: "gates (andflat fs) \<le> Suc (sum_list (map gates fs))"
proof -
  have "sum_list (map gates (concat (map kids fs))) = sum_list (map (\<lambda>f. sum_list (map gates (kids f))) fs)"
    by (induction fs) auto
  also have "\<dots> \<le> sum_list (map gates fs)"
    by (rule sum_list_mono) (rule gates_kids)
  finally show ?thesis by (simp add: andflat_def)
qed

lemma gates_orflat: "gates (orflat fs) \<le> Suc (sum_list (map gates fs))"
proof -
  have "sum_list (map gates (concat (map kids fs))) = sum_list (map (\<lambda>f. sum_list (map gates (kids f))) fs)"
    by (induction fs) auto
  also have "\<dots> \<le> sum_list (map gates fs)"
    by (rule sum_list_mono) (rule gates_kids)
  finally show ?thesis by (simp add: orflat_def)
qed

lemma sum_list_le_const:
  assumes "\<forall>x\<in>set xs. f x \<le> (c::nat)" shows "sum_list (map f xs) \<le> length xs * c"
  using assms by (induction xs) auto

section \<open>Base case: every symmetric function has a DNF of size \<open>2\<^sup>m + 1\<close>\<close>

definition minterm :: "'v lit list \<Rightarrow> bool list \<Rightarrow> 'v form" where
  "minterm L ys = And (map (\<lambda>(l, y). Lit (fst l) (snd l = y)) (zip L ys))"

lemma eval_minterm:
  "length ys = length L \<Longrightarrow> eval \<sigma> (minterm L ys) = (map (litval \<sigma>) L = ys)"
proof (induction L arbitrary: ys)
  case Nil
  then show ?case by (simp add: minterm_def)
next
  case (Cons l L)
  then obtain y ys' where ys: "ys = y # ys'" "length ys' = length L"
    by (cases ys) auto
  with Cons.IH[of ys'] show ?case
    by (cases l) (auto simp: minterm_def litval_def)
qed

definition dnf :: "'v lit list \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'v form" where
  "dnf L g = Or (map (minterm L)
      (filter (\<lambda>ys. g (length (filter id ys))) (List.n_lists (length L) [True, False])))"

lemma eval_dnf: "eval \<sigma> (dnf L g) = g (cnt \<sigma> L)"
proof -
  have len: "length (filter id (map (litval \<sigma>) L)) = cnt \<sigma> L"
    by (simp add: cnt_def filter_map comp_def)
  have mem: "map (litval \<sigma>) L \<in> set (List.n_lists (length L) [True, False])"
    by (auto simp: set_n_lists)
  show ?thesis
  proof
    assume "eval \<sigma> (dnf L g)"
    then obtain ys where "ys \<in> set (List.n_lists (length L) [True, False])"
      "g (length (filter id ys))" "eval \<sigma> (minterm L ys)"
      by (auto simp: dnf_def)
    then show "g (cnt \<sigma> L)"
      using len by (auto simp: set_n_lists eval_minterm)
  next
    assume "g (cnt \<sigma> L)"
    then show "eval \<sigma> (dnf L g)"
      using mem len by (auto simp: dnf_def eval_minterm intro!: bexI[of _ "map (litval \<sigma>) L"])
  qed
qed

lemma sig2_dnf: "sig 2 (dnf L g)"
  by (auto simp: dnf_def minterm_def numeral_2_eq_2 split: prod.splits)

lemma gates_dnf: "gates (dnf L g) \<le> Suc (2 ^ length L)"
proof -
  let ?Y = "filter (\<lambda>ys. g (length (filter id ys))) (List.n_lists (length L) [True, False])"
  have "gates (dnf L g) = Suc (sum_list (map (\<lambda>ys. gates (minterm L ys)) ?Y))"
    by (simp add: dnf_def comp_def)
  also have "sum_list (map (\<lambda>ys. gates (minterm L ys)) ?Y) = length ?Y"
    by (simp add: minterm_def comp_def sum_list_triv split_def)
  also have "length ?Y \<le> length (List.n_lists (length L) [True, False])"
    by (rule length_filter_le)
  also have "\<dots> = 2 ^ length L"
    by (simp add: length_n_lists numeral_2_eq_2)
  finally show ?thesis by simp
qed

theorem base_case:
  assumes "length L \<le> k"
  shows "\<exists>f. sig 2 f \<and> gates f \<le> 2 ^ (k + 1) \<and> (\<forall>\<sigma>. eval \<sigma> f = g (cnt \<sigma> L))"
proof (intro exI conjI allI)
  have a: "(2::nat) ^ length L \<le> 2 ^ k" using assms by simp
  have b: "(1::nat) \<le> 2 ^ k" by simp
  have "Suc (2 ^ length L) \<le> 2 * 2 ^ k" using a b by linarith
  then show "gates (dnf L g) \<le> 2 ^ (k + 1)"
    using gates_dnf[of L g] by simp
qed (auto simp: sig2_dnf eval_dnf)

end
