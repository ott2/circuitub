# Optimal shallow circuits for symmetric functions, in Isabelle/HOL

A machine-checked proof of the main theorem of

> Victor Lecomte and Prasanna Ramakrishnan, *Optimal Shallow Circuits for Majority*,
> [arXiv:2609.34029](https://arxiv.org/abs/2609.34029) (2026).

**Theorem.** For every constant d ≥ 2, every symmetric Boolean function on n variables
has depth-d AND/OR formulas, with negations only on inputs, of size 2^{O(n^{1/(d-1)})}.
The constant depends only on d.

In particular, Majority has depth-d circuits of size 2^{O(n^{1/(d-1)})}, matching
Håstad's lower bound. For depth 3, that is 2^{O(√n)}. The lower bound is not formalized
here.

The Isabelle statement (`isabelle/Majority_Circuits.thy`) is slightly stronger than the
paper's claim. It bounds formula (tree) size rather than circuit size, and the formulas
are strictly layered: alternating, with an OR at the top and every literal at depth
exactly d. No `sorry` is used, and the build fails unless the headline theorems depend
on no oracles.

`isabelle/Bounded_Width.thy` also formalizes Remark 1 of the paper's v2. For every k with
k² ≥ n, every symmetric function, and in particular Majority, is an OR of 2^{O(k)}
CNFs with clauses of width k′ = 2⌈n/k⌉. For k ≤ n this is 2^{O(n/k′)} CNFs. By
pigeonhole, for every t ≤ n some k′-CNF in the cover accepts only inputs of weight t,
and accepts at least C(n,t)/2^{O(n/k′)} of them (`enum_output_lower_bound`). Any
algorithm for the local enumeration problem Enum(k′, t) of Gurumukhani et al.
(CCC 2024) must list all of them. So the hypothetical algorithm with running time
2^{(1−Ω(log k/k))n} cannot exist.

A second document,
[`extensions/locality-and-monotonicity.md`](extensions/locality-and-monotonicity.md), takes
the work in new directions. It asks which restricted circuit classes can still reach
2^{O(√n)}. It has two parts.

The first part, `isabelle/Block_Local.thy`, records which structure the construction needs:
- **Two blocks suffice.** Every clause of those CNFs reads variables from at most two blocks
  of one of two fixed partitions into consecutive blocks of size at most ⌈n/k⌉
  (`symmetric_or_of_cnfs_local`).
- **One block does not.** Consider a formula for Majority that is an OR of tests, where
  each test is an AND of subformulas that each read a single block of one fixed partition.
  It needs at least one test per block-weight vector of total weight n/2
  (`one_block_tests`). That is at least (b+1)^{m/2} tests for m blocks of size b
  (`one_block_tests_equal`), or 2^{Ω(√n log n)} when b = m = √n.

The second part asks whether the construction can be made monotone. The class it studies
is tests that are ANDs of monotone functions of two block weights. Its formal part is
`isabelle/Monotone_Pairs.thy`:
- **Theorem B** (`sharp_bounds`): with k blocks of size b, every such test covers at most a
  2^{k+1}·(πb/2)^{−k/4}·√(2n) fraction of the Majority slice. The proof is a block-level
  analogue of the PPZ satisfiability coding lemma. It improves an earlier
  (k−1)^k·b^{−k/4} bound (Theorem A: `pairwise_count`, `pairwise_weight`).
- **Tightness** (`matching_valid`, `matching_card`, `matching_weight`): pairing the blocks
  with complementary weights achieves b^{−k/4}.

`isabelle/Monotone_Cost.thy` adds two finite ingredients:
- **The cost of a test** (`clause_per_maxfalse`, `test_cost`): a monotone CNF needs one
  clause per maximal false point. So a test covering a point with a block of weight w has
  a pair CNF with at least C(b, w−1) clauses.
- **The number of tests** (`tests_needed`): covering the slice needs at least C(kb, kb/2)
  divided by the bound of Theorem B.

With some binomial estimates on paper, these give Theorem C: monotone formulas of this
shape need size 2^{Θ(√(n log n))}.

`isabelle/Monotone_Mixed.thy` extends this to tests that mix two partitions, as the L-R
tests do:
- **Tight coordinates compress** (`tight_compress`): Theorem B's decoding works for the
  tight coordinates of any accepted weight vector, without a validity assumption.
- **Every one is in a tight block** (`mixed_tight`, `mixed_cover`): in a sound mixed test,
  each one of a covered input lies in a tight block of one of the partitions. So one
  partition compresses, and coverage stays b^{−Ω(k)}.
- **Tight coordinates cost clauses** (`tight_cost`).

On paper, this gives Theorem D: monotone formulas whose tests mix m partitions need
2^{Ω(√(n log n / m))}. So the construction cannot be made monotone without changing its
shape. In this shape, the negations account for the whole √(log n) saving over KPPY.

## Contents

| Path | |
|---|---|
| `isabelle/` | Session `Majority_AC0`: 14 theories, about 4600 lines |
| `isabelle/Bounded_Width.thy` | Remark 1 (OR of narrow CNFs) and the Enum output-size bound |
| `isabelle/Block_Local.thy` | Clauses read two blocks; tests built from one-block pieces need 2^{Ω(√n log n)} |
| `isabelle/Monotone_Pairs.thy` | Monotone pairwise tests: exchange and determination lemmas, Theorems A and B (counting and weighted), tightness via matching tests |
| `isabelle/Monotone_Cost.thy` | One clause per maximal false point; the cost of a test; the number of tests needed to cover the slice |
| `isabelle/Monotone_Mixed.thy` | Tests mixing two partitions: tight coordinates compress, every one lies in a tight block, coverage of a mixed test, cost of a tight coordinate |
| `isabelle/Audit.thy` | Oracle audit of the headline theorems (fails the build if any oracle is used) |
| `control/` | Positive control: the same audit detects a `sorry` |
| `extensions/` | Beyond the paper: block locality (formalized) and the monotone case (analysis) |
| `VERDICT.md` | The verdict, the trusted definitions, and a step-by-step correspondence with the paper |
| `writeup/main.pdf` | Short exposition, including how the formal proof differs from the paper's |

## Building

Requires [Isabelle2025-2](https://isabelle.in.tum.de/). The session depends only on
HOL-Library.

```sh
isabelle build -d isabelle Majority_AC0
isabelle build -d control Oracle_Control   # positive control for the oracle audit
```

The main session builds in a few seconds.

## Differences from the paper's proof

The argument is the paper's, but several parts were adapted to make the formalization
simpler:
- Gödel-β moduli instead of prime powers.
- Shifts sampled from the full cube.
- A greedy covering argument instead of the probabilistic method.
- A single induction on depth over arbitrary literal lists.

See `VERDICT.md` and `writeup/main.pdf` for details.

## Attribution

Claude Opus 5.5 (Anthropic, model `claude-opus-5-5`), working in Claude Code, did the
following in September–October 2026:
- the Isabelle formalization;
- the review of the paper and the verdict in `VERDICT.md`;
- the write-up in `writeup/`.

András Salamon acted as editor: setting the task and the working constraints, and
reviewing the results.

The development was built with Isabelle2025-2 and with
[isabelle-watchdog](https://pypi.org/project/isabelle-watchdog/) and
[isabelle-query](https://pypi.org/project/isabelle-query/).

The mathematics is Lecomte and Ramakrishnan's. Any errors in the formalization or its
exposition are ours.
