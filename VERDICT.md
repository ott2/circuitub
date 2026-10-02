# Verdict on arXiv:2609.34029v1, "Optimal Shallow Circuits for Majority"

**The paper's main theorem is correct.** I proved it in Isabelle/HOL (Isabelle2025-2)
with no `sorry`, no `quick_and_dirty`, and an enforced audit showing that the headline
theorems depend on **no oracles**.

> **Theorem 1 (paper).** For any constant d ≥ 2, every symmetric function on n
> variables has depth-d circuits of size 2^{O(n^{1/(d-1)})}.

In particular, Majority has depth-d circuits of size 2^{O(n^{1/(d-1)})}, which matches
Håstad's 2^{Ω(n^{1/(d-1)})} lower bound. For depth 3 that is 2^{O(√n)}. Håstad's lower
bound is classical and was **not** formalized here; the new upper bound was.

## What is machine-checked

From `isabelle/Majority_Circuits.thy`:

```isabelle
theorem symmetric_functions_big_O:
  assumes d: "2 ≤ d"
  shows "∃C. ∀n ≥ 1. ∀g. ∃f. SIG d f
           ∧ real (gates f) ≤ 2 powr (C * real n powr (1 / real (d - 1)))
           ∧ (∀σ. eval σ f = g (weight n σ))"

corollary majority_circuits:   (* same bound, with g := Majority *)
corollary majority_depth3:     (* SIG 3, size ≤ 2 powr (C * sqrt n) *)
```

The trusted base, which a reader must check matches the paper's model, is ~40 lines at
the top of `Formula.thy` and `Majority_Circuits.thy`:

| Isabelle | Meaning |
|---|---|
| `datatype 'v form = Lit 'v bool \| And (form list) \| Or (form list)` | unbounded fan-in AND/OR over literals `x_v` / `¬x_v` |
| `eval σ f` | standard semantics; `Lit v b` is true iff `σ v = b` |
| `gates f` | number of AND/OR gates (literals are free), i.e. the paper's size |
| `SIG d f` / `PI d f` | strictly layered, alternating, depth exactly `d`, top gate OR / AND |
| `weight n σ = card {i. i < n ∧ σ i}` | Hamming weight of `x_0 … x_{n-1}` |
| `majority n σ ⟷ n ≤ 2 * weight n σ` | the paper's `1[|x| ≥ n/2]` |

Quantifier order is `∃C ∀n ∀g ∃f`: one constant (depending only on `d`) works for every
`n` and every symmetric function. We bound **formula** (tree) size, which is at least
circuit (DAG) size, so the result is slightly stronger than the paper's claim.

## Correspondence with the paper's proof

| Paper step | Theory / lemma |
|---|---|
| Tests: shifted block weights pairwise distinct mod k ⇒ `|x| ≡ t (mod k)` | `Test.thy`: `test_sound` |
| A valid input passes for ≥ k! shift vectors | `Count.thy`: `card_accepting_shifts` |
| k!/k^{k-1} ≥ e^{-k} | `Count.thy`: `pow_le_3pow_fact` (kᵏ ≤ 3ᵏ·k!) |
| Probabilistic covering: 2^{O(k)} tests cover every valid input | `Cover.thy`: `cover` (greedy / double counting) |
| Coprime moduli of size Θ(n^{1/(d-1)}), CRT pins down the weight | `Moduli.thy`: `modq_coprime`, `crt_eq` |
| Pair check is symmetric in (block i, ¬block j) ⇒ recursion | `Construction.thy`: `pairF_facts`, `collide_iff` |
| Depth-2 base case (DNF of size 2ⁿ) | `Formula.thy`: `base_case` |
| Size accounting, induction on d | `Construction.thy`: `symF_bnd`, `depth_step`, `symmetric_upper_bound` |

## Deliberate, inessential deviations from the paper

None of these touches the paper's argument; each simplified the formalization.

1. **Moduli.** The paper uses the smallest power of the i-th prime above n^{1/(d-1)}. I use
   Gödel-β moduli `1 + (i+1)·D!·(k+1)`. They are pairwise coprime and lie in
   `[k+1, (D·D!+1)(k+1)]`, which is all the argument needs.
2. **Sampling space.** The paper samples shifts from the admissible subspace (size
   k^{k-1}). I sample from all of `{0..k-1}^k`. `passes_imp_adm` proves that any shift
   vector accepting a valid input is automatically admissible, so the ≥ k! count carries
   over. This gives the bound k!/kᵏ instead of k!/k^{k-1}; the lost factor k is irrelevant.
3. **Covering.** The expectation argument `2ⁿ(1-p)^T < 1` is replaced by the equivalent
   greedy/averaging argument, which gives the same bound and needs no measure theory.
   Also, the universe covered is the finite set of *block-weight tuples*, not {0,1}ⁿ.
4. **Parametrisation.** The induction is stated as "|L| ≤ k^{d-1} ⇒ size ≤ 2^{C(k+1)}"
   over arbitrary literal lists, which makes the (block i, ¬block j) recursion literal.
   The n^{1/(d-1)} form is derived at the end with `k = ⌈n^{1/(d-1)}⌉`.
5. **Constant gates.** `And []` / `Or []` (fan-in 0) appear only for degenerate weights.
   They can be replaced by fan-in-2 gadgets at O(1) cost.

## Minor remarks on the paper's text (no mathematical errors found)

- §3: the paper counts shift vectors that accept a valid input by constructing them
  "in order". The cleaner view, used here, is a bijection with the k! arrangements of
  residues. Every such vector satisfies the sum constraint automatically when
  |x| ≡ t (mod k).
- §4 needs moduli that are pairwise coprime, each > n^{1/(d-1)} and O(n^{1/(d-1)}). The
  prime-power choice satisfies this with constant p_{d-1}. Any such family works.

## Reproduce

```sh
python3 -m venv .venv && .venv/bin/pip install isabelle-watchdog isabelle-query
WALL_TIMEOUT=120 .venv/bin/isabelle-build -- -c        # session Majority_AC0, ~10 s
.venv/bin/isabelle-query -R isabelle sorry              # -> "No sorries."
WALL_TIMEOUT=40 .venv/bin/isabelle-build --no-record --session Oracle_Control --dir control
```

`Audit.thy` runs `Thm_Deps.all_oracles` on the headline theorems and **fails the build**
unless the oracle set is empty. `control/Oracle_Control.thy` is the positive control: the
same check, applied to a lemma proved by `sorry`, does detect the oracle.

Size: 11 theories, ~2800 lines.

## Addendum: Remark 1 of v2 (local enumeration)

v2 of the paper adds Remark 1: the depth-3 construction refutes the
Σ₃ᵏ lower bound 2^{Ω(n log k/k)} for Majority that Gurumukhani, Paturi, Pudlák, Saks
and Talebanfard (CCC 2024) derive from a hypothetical local enumeration algorithm. This
is formalized in `isabelle/Bounded_Width.thy` and covered by the audit:

| Theorem | Statement |
|---|---|
| `symmetric_or_of_cnfs` | k² ≥ n ⇒ every symmetric g is an OR of ≤ 2^{Ck} CNFs of clause width `width n k` = 2⌈n/k⌉ |
| `symmetric_or_of_cnfs_width`, `majority_or_of_cnfs` | if also k ≤ n: ≤ 2^{C·n/k′} such CNFs, with k′ = `width n k` |
| `enum_output_lower_bound` | for t ≤ n, some k′-CNF F accepts only weight-t inputs, and C(n,t) ≤ 2^{C·n/k′} · #{weight-t inputs accepted by F} |

The last theorem is a lower bound on the *output size* of Enum(k′, t), so it holds
whatever is assumed about SSETH. The construction reuses `Construction.thy`, with the
induction hypothesis instantiated to the explicit DNF (locale `step3`).

## Beyond the paper

`isabelle/Block_Local.thy` proves results that go beyond the paper: what block structure the
construction needs, and a lower bound for tests built from one-block pieces. These are
covered by the audit. They are described in
[`extensions/locality-and-monotonicity.md`](extensions/locality-and-monotonicity.md), together
with an analysis of whether the construction can be made monotone.
