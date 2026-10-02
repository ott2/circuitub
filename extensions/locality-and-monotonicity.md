# Locality and monotonicity in the Lecomte–Ramakrishnan construction

This document is separate from the verification of Lecomte and Ramakrishnan,
*Optimal Shallow Circuits for Majority* (arXiv:2609.34029). It asks how much of the
construction's structure is needed, and whether a more restricted class of circuits could
still reach the 2^{O(√n)} bound for depth-3 Majority.

- **Part 1** is machine-checked (`isabelle/Block_Local.thy`, covered by the oracle audit).
- **Part 2** is a pen-and-paper analysis of the monotone case. It proves some partial
  results and ends with a conjecture. **None of Part 2 is formalized.**

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

## Part 2. Can the construction be made monotone? (analysis, not formalized)

### 2.1 Literature

Majority is monotone, but the L-R construction uses negations essentially. The authors say
so in their introduction: the construction "uses non-monotone circuits and allows the
bottom fan-in to grow with n".

| Bound for monotone depth-3 Majority | Source |
|---|---|
| Upper bound 2^{O(√(n log n))} | KPPY, STOC 1984 |
| Lower bound 2^{Ω(√n)} | Boppana, JCSS 1986 (monotone); Håstad–Jukna–Pudlák, Comput. Complexity 1995 (general) |
| Bottom fan-in 3: exactly (2/6^{1/4})^{n±o(n)} ≈ 1.277ⁿ | Gurumukhani et al., arXiv:2601.04072 (2026) |

As far as we found, the gap between the first two bounds is open. Nobody has made the L-R
construction monotone.

Amano (ISAAC 2023) reportedly shows that negations reduce Σ₃ size for bottom fan-in 3–5.
We have not read that paper.

### 2.2 The class

Fix a partition into k blocks of size b, so n = kb. The class consists of **monotone,
block-symmetric, pairwise** tests. Each is an AND of monotone functions that each read at
most two blocks and depend only on the two block weights. This is the shape of the L-R
pair tests, without the negations.

**Weight-vector form.** A test corresponds to
W = {w ∈ [0,b]^k : (w_i, w_j) ∈ P_ij for all i < j},
where each P_ij is up-closed. The test is sound iff W ⊆ {Σw ≥ N}.

**Coverage.** The test covers H = W ∩ {Σw = N}. We measure H by the fraction of
weight-N inputs it contains:
ν(w) = ∏_i C(b, w_i) / C(n, N).

For comparison, L-R's non-monotone tests reach ν(H) ≥ e^{−O(k)}.

### 2.3 Exact reformulation

**Lemma 1 (closure).** W contains
cl(H) = {z : every pair (i, j) is dominated, on coordinates i and j, by some h ∈ H}.
Conversely, letting each P_ij be the up-closure of the projection proj_ij(H) gives
W = cl(H).
- So H is the covered set of a sound test iff cl(H) ∩ {Σ < N} = ∅.
- The best possible test coverage is therefore
  Q(k,b) = max { ν(H) : H ⊆ {Σ = N}, cl(H) ∩ {Σ < N} = ∅ }.

**Lemma 2 (exchange).** For valid H, every p ∈ H and every coordinate ℓ have a *witness*
i ≠ ℓ: no h ∈ H has h_ℓ < p_ℓ and h_i ≤ p_i.

*Proof.* Suppose not. For each i ≠ ℓ, pick a counterexample h⁽ⁱ⁾. Lower p_ℓ to
max_i h⁽ⁱ⁾_ℓ. The resulting point lies in cl(H) but has weight below N. ∎

**Lemma 3 (determination).** If i is a witness for (p, ℓ), then p_ℓ = μ_iℓ(p_i), where
μ_iℓ(x) = min{h_ℓ : h ∈ H, h_i ≤ x} is a non-increasing function determined by H.
Equivalently, p's projection onto (ℓ, i) lies on the lower-left Pareto staircase of
proj_ℓi(H).

### 2.4 Bounded number of blocks

**Theorem A.** For valid H,
- |H| ≤ (k−1)^k (b+1)^{⌊k/2⌋}, and
- ν(H) ≤ (k−1)^k (πb/2)^{−k/4} √(2n).

*Proof.*
1. Choose a witness for every coordinate of p. This gives a function f_p : [k] → [k] with
   no fixed points.
2. By Lemma 3, p is determined by f_p together with one value on each cycle of f_p.
3. Every cycle has length at least 2, so there are at most k/2 cycles.
4. For the weighted bound, sum the binomial weights freely over the cycle
   representatives, and bound every other factor by C(b, b/2). ∎

**k = 3, sharper.** Here |H| ≤ 2(b+1) and ν(H) = O(b^{−1/2}). Each point of H is unique in
its row or unique in its column of the (w₁, w₂) plane. This rules out more than corners, so
the bound is linear rather than of Behrend type.

**The b^{−k/4} decay is tight.** The *matching test* pairs up the blocks and requires
w_{2q−1} + w_{2q} ≥ b for each pair. It achieves
ν(H) = C(2b,b)^{k/2}/C(kb,kb/2) ≈ (πb)^{−k/4} √(πkb/2).
This test is just divide-and-conquer over blocks of size 2b. So for a bounded number of
blocks, monotone pairwise tests cannot beat KPPY.

### 2.5 Cost of a test

**Lemma 4 (monotone only).** A monotone CNF needs a distinct clause for every maximal false
point. Two such points cannot share a clause, because their join would also falsify it.

**Consequence.** Let a test cover p, with p_ℓ near b/2.
- p − e_ℓ has weight N − 1, so it must be rejected, by some P_ℓj.
- So P_ℓj has a maximal false point with first coordinate p_ℓ − 1.
- Therefore it needs at least C(b, p_ℓ − 1) ≥ 2^b/poly(b) clauses.

Up to polynomial factors, every formula in the class has size at least

  min over b of  max( 2^b, 1/Q(n/b, b) ).   (★)

### 2.6 Where the argument stops

Theorem A's (k−1)^k factor comes from naming each coordinate's witness. The bound is
useful only when b ≳ k^{4+ε}, and there the 2^b term in (★) already dominates. So the
decisive regime, b ≈ k ≈ √n, is untouched.

This is not just a weakness of the proof:
- The local consequence of Lemmas 2–3 is that each coordinate is a decreasing function of
  some other coordinate. When k ≫ √b, most of the slice has that property.
- Any proof must therefore use the *global* exchange condition: a single witness must
  work against all of H.
- Every construction we tried that let witnesses vary from point to point fell back to a
  fixed matching or a one-parameter family:
  - sorted complementary pairing;
  - linear constraints w_i + w_j ≥ c_ij on denser graphs;
  - complete bipartite sum structures.

### 2.7 Conjecture

**Conjecture Q.** Q(k,b) ≤ (c·b)^{−c′k} for absolute constants c, c′ > 0. That is,
matching tests are optimal up to the constant in the exponent.

- **If true:** by (★), monotone, block-symmetric, pairwise Σ₃ formulas over a fixed
  partition need size 2^{Ω(√(n log n))}. KPPY is then optimal in this class, and the L-R
  construction cannot be made monotone without changing its shape. Theorem A proves this
  for bounded k.
- **If false:** a monotone pairwise test family with coverage e^{−O(k)} at b ≈ k would
  give monotone depth-3 Majority formulas of size 2^{O(√n)}. That would close the monotone
  gap from above.

**Outside the scope of this conjecture:**
- pair functions that are not block-symmetric;
- several partitions;
- tests that read more than two blocks.

### 2.8 Next steps

1. **Compute small cases.** Compute Q(k,b) exactly for small k and b with a SAT/ILP
   encoding of the condition cl(H) ∩ {Σ < N} = ∅. Then compare against e^{−O(k)} at b ≈ k.
2. **Bounded-degree witness graphs.** Can a valid H always be replaced, at a 2^{−O(k)} loss
   in coverage, by one whose witness pairs form a graph of bounded degree D? If so, the
   (k−1)^k in Theorem A becomes D^k, and the conjecture follows for b ≫ D⁴.
3. **Formalize.** Lemmas 1–3, Theorem A and the k = 3 bound are elementary enough for
   Isabelle.
