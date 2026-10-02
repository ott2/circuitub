# Locality and monotonicity in the Lecomte–Ramakrishnan construction

This document is separate from the verification of Lecomte and Ramakrishnan,
*Optimal Shallow Circuits for Majority* (arXiv:2609.34029). It asks how much of the
construction's structure is needed, and whether a more restricted class of circuits could
still reach the 2^{O(√n)} bound for depth-3 Majority.

Status:

| Part | Formalized in | Contents |
|---|---|---|
| Part 1: block locality | `isabelle/Block_Local.thy` | Formalized and covered by the oracle audit |
| Part 2: monotone tests | `isabelle/Monotone_Pairs.thy` | Formalized results are marked **[F]**; the rest is pen and paper. Part 2 ends with an open conjecture |

Notation:
- n is the number of variables, N = n/2, and Majority means weight ≥ n/2.
- A *test* is a middle-level AND gate of a Σ₃ formula, i.e. one disjunct of the top-level OR.

## Part 1. Block locality (formalized)

### 1.1 Two blocks suffice

`symmetric_or_of_cnfs_local` strengthens Remark 1 of the paper's v2. Suppose k² ≥ n.
Then every symmetric function is an OR of at most 2^{Ck} CNFs of clause width 2⌈n/k⌉.
Moreover, there are block sizes s₀, s₁ ≤ ⌈n/k⌉ such that **every clause reads variables
from at most two blocks {v : v div s_l = i} of a single partition l ∈ {0, 1}**.

The two partitions correspond to the construction's two moduli. Each clause comes from
one pair check: a symmetric function of block_i ∪ ¬block_j.

### 1.2 One block does not suffice (for a single partition)

`one_block_tests` assumes the following:
- `Or ts` computes Majority on n variables, with n even.
- There is a fixed map `blk` from variables to blocks.
- Every test in `ts` is an AND of subformulas, of any depth or shape, each of which reads
  variables from a single block.

Then `length ts` is at least the number of block-weight vectors (w_p)_p of inputs of
weight n/2.

*Proof idea.* Suppose one test accepts two weight-n/2 inputs σ and σ′ with different block
weights. Build τ by taking σ on the blocks where it is lighter and σ′ elsewhere.
- Every conjunct sees a single block, so the test accepts τ.
- τ has weight Σ_p min(w_p, w′_p) < n/2.
- That contradicts the test implying Majority.

`one_block_tests_equal` applies this to m blocks of b consecutive variables, with m even.
There are then at least (b+1)^{m/2} tests. For b = m = √n this is 2^{Ω(√n log n)}.

**What the comparison shows.** At the same block size, the construction needs only
2^{O(√n)} tests, and its tests read two blocks. So the √(log n) improvement of L-R over
divide-and-conquer (Klawe–Paul–Pippenger–Yannakakis, KPPY84) comes from tests that read
two blocks.

**Caveats.**
- The lower bound fixes the block size. If blocks may be large, a single block is the whole
  input, and the bound says nothing.
- It assumes a single partition. The construction uses two, and whether one-block tests
  over two partitions can do better is open.

## Part 2. Can the construction be made monotone?

### 2.1 Literature

Majority is monotone, but the L-R construction uses negations essentially. The authors say
so in their introduction: the construction "uses non-monotone circuits and allows the
bottom fan-in to grow with n".

| Bound for depth-3 Majority | Source |
|---|---|
| Monotone upper bound 2^{O(√(n log n))} (still the best known) | KPPY, STOC 1984 |
| Lower bound 2^{Ω(√n)}, monotone | Boppana, JCSS 1986 |
| Lower bound 2^{(d−o(1))√n} with d = 1/√(ln 4) ≈ 0.849, general circuits | Håstad–Jukna–Pudlák, Comput. Complexity 1995 |
| Bottom fan-in 3, monotone: exactly (2/6^{1/4})^{n±o(n)} ≈ 1.27785ⁿ | Gurumukhani et al., arXiv:2601.04072 (2026) |

**Amano (ISAAC 2023).** This paper compares Σ₃ circuits whose bottom clauses have at most
k positive and ℓ negative literals with monotone ones.

| Bottom fan-in k | Non-monotone (with negations) | Best monotone |
|---|---|---|
| k ≤ 2 | same as monotone | — |
| 3 | O(1.2768ⁿ) | 1.2779ⁿ |
| 4 | O(1.2040ⁿ) | O(1.2093ⁿ) |
| 5 | O(1.1751ⁿ) | O(1.1760ⁿ) |

- For k ≤ 2, negations do not help.
- For k = 3, 4, 5 they help, but only by a small margin. At k = 3 the non-monotone bound
  1.2768ⁿ is just below the exact monotone optimum 1.27785ⁿ.
- Amano's constructions also use a fixed partition. Each block gets a target weight
  proportional to the global threshold. **No test couples two blocks.**

So the bounded-fan-in evidence says negations help only slightly at small fan-in.
L-R show that, with unbounded fan-in, negations plus pairwise coupling remove a √(log n)
factor from the exponent.

### 2.2 The class

Fix a partition into k blocks of size b, so n = kb. The class consists of **monotone,
block-symmetric, pairwise** tests. Each is an AND of monotone functions that each read at
most two blocks and depend only on the two block weights. This is the shape of the L-R
pair tests, without the negations.

**Weight-vector form.** A test corresponds to
W = {w ∈ [0,b]^k : (w_i, w_j) ∈ P_ij for all i ≠ j},
where each P_ij is up-closed. The test is sound iff W ⊆ {Σw ≥ N}.

**Coverage.** The test covers H = W ∩ {Σw = N}. Each weight vector w stands for
∏_i C(b, w_i) inputs. The fraction of the Majority slice that the test covers is

  ν(H) = Σ_{w∈H} ∏_i C(b, w_i) / C(n, N).

For comparison, L-R's non-monotone tests reach ν(H) ≥ e^{−O(k)}.

### 2.3 Exact reformulation [F]

**Lemma 1 (`test_valid`, `valid_test`).** Let
cl(H) = {z : every pair (i, j) is dominated, on coordinates i and j, by some h ∈ H}.
Then H is the covered set of a sound test iff cl(H) ∩ {Σ < N} = ∅. Isabelle calls this
property `valid k N H`.

The best possible test coverage is therefore
  Q(k,b) = max { ν(H) : H valid }.

**Lemma 2 (`exchange`).** For valid H, every p ∈ H and every coordinate ℓ have a *witness*
i ≠ ℓ: no h ∈ H has h_ℓ < p_ℓ and h_i ≤ p_i.

*Proof.* Suppose not. For each i ≠ ℓ, pick a counterexample h⁽ⁱ⁾. Lower p_ℓ to
max_i h⁽ⁱ⁾_ℓ. The resulting point lies in cl(H) but has weight below N. ∎

**Lemma 3 (`determination`).** If i is a witness for (p, ℓ), then p_ℓ = μ_iℓ(p_i), where
μ_iℓ(x) = min{h_ℓ : h ∈ H, h_i ≤ x} is a non-increasing function that depends only on H.

**An equivalent form** (pen and paper). Write each up-closed P_ℓj as
{(x, y) : x ≥ φ_ℓj(y)}, with φ_ℓj non-increasing. Then:
- W = {z : z ≥ T(z)}, where T(z)_ℓ = max(0, max_{j≠ℓ} φ_ℓj(z_j)).
- The minimal elements of W are exactly the fixed points of T.
- T is antitone, i.e. order-reversing, so its fixed points form an antichain.

So **Q(k,b) is the largest slice mass of the fixed points of an antitone "max of unary
maps" network on [0,b]^k whose up-set lies above the hyperplane.** This links the problem
to fixed points of Boolean and q-ary networks. Bounds there in terms of feedback vertex
sets (Aracena and others; recalled, not checked here) give only (b+1)^{k−1} for complete
interaction graphs. The max structure is what brings this down to k/2 per pattern
(Theorem A).

### 2.4 Theorem A and its tightness [F]

Theorem A comes in two forms, both for valid H ⊆ {..<k} →ₑ {..b} with k ≥ 2:

| Theorem | Statement |
|---|---|
| `pairwise_count` | \|H\| ≤ (k−1)^k (b+1)^{⌊k/2⌋} |
| `pairwise_weight` | Σ_{p∈H} ∏_i C(b, p_i) ≤ (k−1)^k · (2^b)^{⌊k/2⌋} · C(b, ⌊b/2⌋)^{⌈k/2⌉} |

Dividing the weighted form by C(kb, kb/2) gives
ν(H) ≤ (k−1)^k · (πb/2)^{−k/4} · O(√n).

*Proof.*
1. Choose a witness for every coordinate of p. This gives a map f_p with no fixed points.
2. By Lemma 3, p is determined by f_p together with its values on R. Here R is the smaller
   of the descent set {ℓ : f(ℓ) < ℓ} and the ascent set {ℓ : ℓ < f(ℓ)}. Both sets meet every
   cycle of f, and the smaller has at most k/2 elements.
3. For the weighted form, sum the binomial weights freely over R, and bound every other
   factor by C(b, b/2). ∎

The proof only uses the witness maps (`count_via`, `weight_via`). In particular:

| Theorem | Statement |
|---|---|
| `graph_weight` | If the witnesses can always be chosen along a fixed digraph of out-degree ≤ D, then (k−1)^k improves to D^k, in both forms |
| `three_blocks` | For k = 3, \|H\| ≤ 2(b+1). Each point is determined by its witness coordinate |

**Tightness.** The *matching test* pairs up the blocks and requires
w_{2q−1} + w_{2q} ≥ b for each pair.

| Theorem | Statement |
|---|---|
| `matching_valid` | The matching test is valid |
| `matching_card` | It covers (b+1)^{k/2} weight vectors |
| `matching_weight` | It covers at least C(2b,b)^{k/2} inputs, i.e. ν ≈ (πb)^{−k/4} √(πkb/2) |

So the counting and weighted forms of Theorem A are both tight up to (k−1)^k · O(1)^k.
The matching test is divide-and-conquer over blocks of size 2b.

**Small groups cannot beat matching** (pen and paper).
- Split the blocks into groups of g, each with its own valid test, and fix each group's sum.
- Fixing a group sum costs a factor about b^{−1/2}. By Theorem A, the best within-group
  coverage is about g^g b^{−(g/4 − 1/2)}.
- The cost per block is then b^{−1/4}, the same as matching, for every bounded g.

With b = 1 (blocks are single variables), Q(k,1) is the monotone 2-CNF case. There the
matching (2^{n/2} minimum vertex covers) is optimal at threshold n/2. This is the k = 2
case resolved by Gurumukhani, Künnemann and Paturi (arXiv:2412.20493). At other
thresholds, Moon–Moser-type triangle constructions win: for example, at threshold 2n/3
there are 3^{n/3} minimum vertex covers. So the matching's optimality is specific to
Majority.

### 2.5 Cost of a test

**Lemma 4 (monotone only; not yet formalized).** A monotone CNF needs a distinct clause for
every maximal false point. Two such points cannot share a clause, because their join would
also falsify it.

**Consequence.** Let a test cover p, with p_ℓ near b/2.
- p − e_ℓ has weight N − 1, so it must be rejected, by some P_ℓj.
- So P_ℓj has a maximal false point with first coordinate p_ℓ − 1.
- Therefore it needs at least C(b, p_ℓ − 1) ≥ 2^b/poly(b) clauses.

Up to polynomial factors, every formula in the class has size at least

  min over b of  max( 2^b, 1/Q(n/b, b) ).   (★)

### 2.6 Where the argument stops

In the regime that decides the question, b ≈ k ≈ √n, Theorem A says nothing. The (k−1)^k
factor counts witness patterns, and it beats the (πb/2)^{−k/4} gain unless b ≳ k^{4+ε}.
In that regime, the 2^b term in (★) already dominates.

The obstruction is real:
- The local consequence of Lemmas 2–3 is that each coordinate is a decreasing function of
  some other coordinate. When k ≫ √b, most of the slice has that property.
- Any proof must therefore use the *global* exchange condition: a single witness must
  work against all of H.
- Every construction we tried that let witnesses vary from point to point fell back to a
  fixed matching or a one-parameter family:
  - sorted complementary pairing;
  - linear constraints w_i + w_j ≥ c_ij on denser graphs;
  - complete bipartite sum structures;
  - "every coordinate is complemented by its minimum partner". With complete-graph
    complements, this leaves one point.

`graph_weight` reduces the conjecture to a structural statement about witness patterns
(Section 2.8).

### 2.7 Conjecture

**Conjecture Q.** Q(k,b) ≤ C^k · b^{−k/4} · poly(n). That is, matching tests are optimal up
to C^k, for all k and b. A weaker form, (cb)^{−c′k}, suffices for the consequences below.

- **Known cases:**
  - Theorem A proves it when b ≥ k^{4+ε}.
  - Section 2.4 proves it for product tests over groups of bounded size.
  - For b = 1 it follows from the k = 2 result of Gurumukhani–Künnemann–Paturi, as
    summarized; we have not checked their proof.
- **If true:** by (★), monotone, block-symmetric, pairwise Σ₃ formulas over a fixed
  partition need size 2^{Ω(√(n log n))}. KPPY is then optimal in this class, and the L-R
  construction cannot be made monotone without changing its shape.
- **If false:** a monotone pairwise test family with coverage e^{−O(k)} at b ≈ k would
  give monotone depth-3 Majority formulas of size 2^{O(√n)}. That would close the monotone
  gap from above.

**Outside the scope of this conjecture:**
- pair functions that are not block-symmetric;
- several partitions;
- tests that read more than two blocks.

Counting tests can produce sum constraints, e.g. "the sorted block weights dominate a fixed
profile". Pairwise tests cannot: they cannot count.

### 2.8 Next steps

1. **Sparsify witnesses.** Show that any valid H loses only a 2^{O(k)} factor in ν when its
   witnesses are restricted to one digraph of bounded out-degree D. By `graph_weight`, this
   would prove Conjecture Q.
   - The fixed-point form (Section 2.3) suggests a candidate: keep, for each ℓ, the partners
     j whose φ_ℓj is not dominated on the bulk window [b/2 − C√b, b/2 + C√b].
2. **Cost lemma.** Formalize Lemma 4 and the bound (★).
3. **Beyond block symmetry.** Remove the assumption by symmetrizing pair functions over
   permutations inside each block. Monotonicity is preserved, but the AND of the
   symmetrized functions may not be sound.
4. **Small cases.** Exact values of Q(k,b) for small k, b would need a search over antichains.
   We have not done this, preferring proofs to experiments.
