# Locality and monotonicity in the Lecomte–Ramakrishnan construction

This document is separate from the verification of Lecomte and Ramakrishnan,
*Optimal Shallow Circuits for Majority* (arXiv:2609.34029). It asks how much of the
construction's structure is needed, and whether a more restricted class of circuits could
still reach the 2^{O(√n)} bound for depth-3 Majority.

Status:

| Part | Formalized in | Contents |
|---|---|---|
| Part 1: block locality | `isabelle/Block_Local.thy` | Formalized and covered by the oracle audit |
| Part 2: monotone tests | `isabelle/Monotone_Pairs.thy`, `Monotone_Cost.thy`, `Monotone_Mixed.thy` | Formalized results are marked **[F]**; the rest is pen and paper. The main results are Theorems C and D: in the shape of the L-R tests, including tests that mix two partitions, monotone formulas need 2^{Θ(√(n log n))} |

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
interaction graphs. The max structure is what brings this down to (b+1)^{k/2}, up to a
2^{O(k)} factor (Theorem B).

### 2.4 Theorems A and B, and tightness [F]

Both theorems hold for valid H ⊆ {..<k} →ₑ {..b} with k ≥ 2.

**Theorem A** (`pairwise_count`, `pairwise_weight`) is the first version:

| Theorem | Statement |
|---|---|
| `pairwise_count` | \|H\| ≤ (k−1)^k (b+1)^{⌊k/2⌋} |
| `pairwise_weight` | Σ_{p∈H} ∏_i C(b, p_i) ≤ (k−1)^k · (2^b)^{⌊k/2⌋} · C(b, ⌊b/2⌋)^{⌈k/2⌉} |

*Proof.* Choose a witness for every coordinate of p. This gives a fixed-point-free map f_p.
By Lemma 3, p is determined by f_p and its values on the smaller of the descent and ascent
sets of f_p, which has at most k/2 elements. Recording f_p costs the factor (k−1)^k. ∎

The factor (k−1)^k made Theorem A vacuous in the decisive regime b ≈ k. Theorem B removes it.

**Theorem B** (`sharp_bounds`):

| Part | Statement |
|---|---|
| (1) | \|H\| ≤ 2^{k+1} (b+1)^{⌊k/2⌋} |
| (2) | Σ_{p∈H} ∏_i C(b, p_i) ≤ 2^{k+1} · (2^b)^{⌊k/2⌋} · C(b, ⌊b/2⌋)^{⌈k/2⌉} |

*Proof.* The point is that the decoder does not need to know which coordinate is the
witness.
1. For every p ∈ H and all j ≠ ℓ, μ_jℓ(p_j) ≤ p_ℓ (take h = p in the definition of μ).
   Equality holds when j is a witness (Lemma 3).
2. Fix an order on the coordinates. Call ℓ *free* for p if every witness of (p, ℓ) comes
   after ℓ. Otherwise some witness comes earlier, and then p_ℓ = max_{j earlier} μ_jℓ(p_j).
3. So p is determined by its free set S and its values on S (`free_determined`). The proof
   is by induction along the order.
4. No coordinate is free both for an order and for its reverse, since every coordinate has
   a witness (Lemma 2). So for one of the two orders, |S| ≤ k/2 (`free_small`).
5. That gives at most 2 · 2^k classes (order, S), each determined by at most k/2 values.
   For the weighted form, sum the binomial weights freely over S and bound the rest by
   C(b, b/2). ∎

Both theorems are instances of one counting lemma, `classes`.

**Coverage.** Take b and k even, and use C(b, b/2) ≤ 2^b/√(πb/2) and C(n, n/2) ≥ 2^n/√(2n).
Theorem B then gives, for every sound test,

  ν(H) ≤ 2^{k+1} · (πb/2)^{−k/4} · √(2n).   (B)

So Q(k,b) ≤ C^k · b^{−k/4} · poly(n) with C = 2·(2/π)^{1/4} ≈ 1.79. An earlier version of
this document stated this bound as an open conjecture ("Conjecture Q").

**Three blocks** (`three_blocks`). For k = 3, |H| ≤ 2(b+1): each point is determined by
its witness coordinate.

**Tightness.** The *matching test* pairs up the blocks and requires
w_{2q−1} + w_{2q} ≥ b for each pair.

| Theorem | Statement |
|---|---|
| `matching_valid` | The matching test is valid |
| `matching_card` | It covers (b+1)^{k/2} weight vectors |
| `matching_weight` | It covers at least C(2b,b)^{k/2} inputs, i.e. ν ≈ (πb)^{−k/4} √(πkb/2) |

So Theorem B is tight up to a factor 2^{O(k)}, in both forms. Matching tests are optimal
monotone pairwise tests, up to C^k.

**Connection to PPZ.** Theorem B is a block-level version of the satisfiability coding
lemma of Paturi, Pudlák and Zane. There, a solution of a k-CNF that is isolated in many
directions is encoded by writing bits in a random order and skipping the bits forced by a
clause. Here, coordinates are skipped when an earlier coordinate witnesses them. Two
features are specific to this setting:
- The forcing value is computed as a maximum, so the witness need not be named.
- An order and its reverse suffice; no random order is needed.

With b = 1 (blocks are single variables), H is a set of minimal satisfying assignments of a
monotone 2-CNF, and the matching (2^{n/2} minimum vertex covers) is optimal at threshold
n/2. This is the k = 2 case of Gurumukhani, Künnemann and Paturi (arXiv:2412.20493). At
other thresholds, Moon–Moser-type triangle constructions win: for example, at threshold
2n/3 there are 3^{n/3} minimum vertex covers. Theorem B's factor 2^{k+1} is too large to
see this difference.

### 2.5 The cost of a test, and the class lower bound

The finite ingredients are formalized in `isabelle/Monotone_Cost.thy`.

**Lemma 4 (`clause_per_maxfalse`) [F].** A monotone CNF needs a distinct clause for every
maximal false point. Two such points cannot share a clause, because their join would also
falsify it.

**Consequence (`pair_cost`, `test_cost`) [F].** Suppose a sound test covers p, and
1 ≤ p_ℓ.
- p − e_ℓ has weight N − 1, so the test rejects it. Some pair function involving ℓ changes
  value there (`test_boundary`).
- Going up in the other coordinate, that pair function has a maximal false weight pair
  (p_ℓ − 1, t) (`boundary`). As a Boolean function on 2b variables, it has at least
  C(b, p_ℓ − 1) maximal false points, namely the inputs with these block weights
  (`pair_maxfalse`).
- So one pair CNF of the test has at least C(b, p_ℓ − 1) clauses.

**Number of tests (`tests_needed`) [F].** A family of sound tests that accepts every
weight vector of the slice has at least

  C(kb, N) / (2^{k+1} · (2^b)^{⌊k/2⌋} · C(b, ⌊b/2⌋)^{⌈k/2⌉})

members. The proof combines Theorem B with `slice_count`: the slice's weight vectors account
for all C(kb, N) inputs of weight N. Only the inequality is needed, and it avoids the
Vandermonde identity.

**Theorem C (pen and paper, from the formalized ingredients above).** Let F be a monotone Σ₃ formula (an OR of monotone CNFs) for
Majority on n variables. Fix a partition of the variables into k blocks of size b. Suppose
each test's clauses can be grouped by pairs of blocks, so that each group computes a
block-symmetric function of its two blocks. Then F has size 2^{Ω(√(n log n))}. Formulas
in this class of size 2^{O(√(n log n))} exist, so the class has complexity
2^{Θ(√(n log n))}.

*Proof of the lower bound.* Let b₀ be a suitable absolute constant.
- **Small blocks, b ≤ b₀.**
  - Every clause has width at most 2b.
  - An input of weight N accepted by a sound test is *isolated* in N directions: each of
    its N neighbours of weight N − 1 is rejected.
  - By the PPZ coding lemma, a CNF of width 2b accepts at most 2^{n − N/(2b)} such inputs.
  - The slice has C(n, N) ≥ 2^n/(n+1) points, so F has at least 2^{n/(4b)}/(n+1) tests.
    That is 2^{Ω(n)}.
- **Large blocks, b > b₀.** Call a test *expensive* if it covers a point p with some
  coordinate p_ℓ such that b/4 ≤ p_ℓ − 1 ≤ 3b/4.
  - **Each expensive test is large.** By the consequence of Lemma 4, it has at least
    C(b, ⌈b/4⌉) ≥ 2^{0.81b}/(b+1) clauses.
  - **Cheap tests cover little.** The other tests cover only points whose coordinates all
    satisfy |p_ℓ − b/2| ≥ b/4 − 1. By Hoeffding, at most 2^{b+1} e^{−2(b/4−1)²/b}
    subsets of one block have such a weight. So these points are at most a
    (n+1) · (2 e^{−2(b/4−1)²/b})^k ≤ (n+1) e^{−n/10} fraction of the slice. That is
    below 1/2 for large n.
  - **So there are many expensive tests.** The expensive tests cover at least half the
    slice, and by (B) each covers at most 2^{k+1}(πb/2)^{−k/4}√(2n) of it.
  - **Combining.** Writing k = n/b,

      log₂ size(F) ≥ 0.81 b + (n/b) · (¼ log₂(πb/2) − 1) − O(log n).

  - **Optimizing over b.** For b > b₀, the bracket is at least ⅛ log₂ b. If b ≥ √(n log n),
    the first term is Ω(√(n log n)). Otherwise, since log b / b decreases, the second term
    is at least (n/(8b)) log₂ b ≥ Ω(√(n log n)). ∎

*Upper bound inside the class.*
- **The tests.** Pair up the blocks. For every profile c with Σ_q c_q = N, take the test
  ⋀_q [w_{2q−1} + w_{2q} ≥ c_q]. Every slice point passes the test given by its own pair
  sums, so the OR of these tests computes Majority.
- **Size.** Each conjunct is a threshold function of 2b variables, with at most 4^b
  clauses. There are at most (2b+1)^{k/2} profiles.
- **Choice of b.** Take b = √(n log n). The size is then 2^{O((n/b) log b + b)} =
  2^{O(√(n log n))}. This is essentially KPPY's divide-and-conquer.

### 2.6 What this says about the L-R construction

The L-R tests have this shape, with negations: each clause reads two blocks of one of two
partitions (Part 1), through block-symmetric pair checks. Theorem C, extended to tests that
mix two partitions by Theorem D (§2.8), says that without negations the same shape cannot
beat KPPY. So **in this shape, the negations are responsible for the entire √(log n)
saving**. Amano's results point the same way at
bounded fan-in: negations help there too, but only slightly.

Theorem C does not settle the monotone depth-3 complexity of Majority: the gap between
2^{Ω(√n)} and 2^{O(√(n log n))} remains open. Theorem C rules out one route to closing it.
Section 2.7 shows how far the class can be widened.

### 2.7 Widening the class (pen and paper)

**(i) Each test may choose its own partition.** The proof of Theorem C works test by test.
Let test t use a partition into blocks of size b_t.
- **Few tests suffice for the bound.** If there are at least 2^{n/(8b₀)} tests, the size is
  already 2^{Ω(n)}. So assume there are fewer.
- **Small-block and cheap tests cover little.** Tests with b_t ≤ b₀ cover at most
  (n+1)·2^{−n/(4b₀)} of the slice each (PPZ). Cheap tests cover at most (n+1)·e^{−n/10}
  each. With fewer than 2^{n/(8b₀)} tests, together they cover less than half the slice.
- **So expensive tests pay.** The expensive tests cover the rest. Each pays at least
  2^{Ω(√(n log n))} clauses per unit of coverage, whatever its b_t.

So the fixed partition is not needed. The argument above still uses a single partition per
*test*. The L-R tests are not of this kind: one test contains pair checks for both moduli,
i.e. for both partitions. Section 2.8 handles that case.

**(ii) Clauses may read r blocks.** Let each test be an AND of monotone block-symmetric
functions of r block weights. The proof of Theorem B generalizes as follows:
- **Validity.** Validity now asks every r-set of coordinates to be dominated.
- **Exchange.** Every coordinate ℓ of p ∈ H has a witness *set* E of r − 1 other
  coordinates: no h ∈ H has h_ℓ < p_ℓ and h_E ≤ p_E. The proof is as for Lemma 2: lower
  p_ℓ to the maximum over the counterexamples.
- **Determination.** p_ℓ = μ_E(p_E), and μ_{E′}(p_{E′}) ≤ p_ℓ for every E′. So
  coordinate ℓ is determined once some witness set lies entirely before it.
- **Free coordinates.** In a uniformly random order, ℓ is free with probability at most
  1 − 1/r (ℓ comes last among E ∪ {ℓ} with probability 1/r).
- **Averaging.** For each fixed order σ, Σ_p wt(p)·ρ^{−|F_σ(p)|} ≤ 2^k C(b, b/2)^k, where
  ρ = 2^b/C(b, b/2). Average over σ and apply Jensen. This gives

  ν(H) ≤ 2^k · (πb/2)^{−k/(2r)} · √(2n).

  Grouping the blocks r at a time, with a threshold on each group's weight, shows this is
  tight up to 2^{O(k)}.

The cost lemma is unchanged: some r-ary constraint has a maximal false point with
ℓ-coordinate p_ℓ − 1, so it has at least C(b, p_ℓ − 1) clauses. Optimizing as before gives
size 2^{Ω(√(n log n / r))}.
- For constant r, the class still has complexity 2^{Θ(√(n log n))}.
- At r ≈ log n the bound reaches 2^{Ω(√n)}, the known general lower bound. So
  block-symmetric tests that read about log n blocks are not excluded by this argument.

**(iii) Block symmetry cannot simply be dropped.** Without it, take k = 2 blocks of size
n/2. Then every clause reads at most two blocks, so every monotone Σ₃ formula is in the
class. A meaningful version must bound the block size. For example, with b ≤ √n and
arbitrary monotone pair functions, the cost lemma fails: a pair function can have few
clauses. Only the PPZ bound 2^{Ω(n/b)} = 2^{Ω(√n)} remains.

**Summary** (including §2.8). Any monotone Σ₃ formula for Majority of size 2^{O(√n)} must
do at least one of the following:
- mix about log n or more partitions inside one test (two, as in L-R, is not enough);
- use block-symmetric constraints on about log n or more blocks;
- give up block symmetry.

### 2.8 Tests that mix partitions [F]

The L-R tests contain pair checks for two partitions at once. Section 2.7 (i) allows each
test its own partition, but not several partitions within one test. This section removes
that restriction. The finite part is formalized in `isabelle/Monotone_Mixed.thy`.

**The model.** A test now has two partitions:
- A, into k_A blocks of size a;
- B, into k_B blocks of size b.

It accepts x iff the A-weight vector u of x passes up-closed pair constraints P and the
B-weight vector v of x passes up-closed pair constraints Q. The two weight vectors are
linked through x, so the slice reformulation of §2.3 does not apply. The argument below
works with the constraints directly.

**Tight coordinates.** Let u be accepted. Call coordinate ℓ *tight* if lowering u_ℓ by one
violates a constraint between ℓ and some i, its *witness*.
- Let th_ℓi(y) be the least x such that (x, y) passes both constraints between ℓ and i.
  Then u_ℓ = th_ℓi(u_i) for a witness i (`th_eq`), and th_ℓj(u_j) ≤ u_ℓ for every j
  (`th_le`). These are Lemma 3 and the first step of Theorem B, with the test in place of H.
- So Theorem B's decoding applies to the tight coordinates of *any* accepted vector. The
  decoder records the non-tight coordinates and the tight coordinates that are free for
  the order (`tfree_determined`). A tight coordinate is not free both in an order and in
  its reverse (`tfree_small`).

**Lemma 5 (`tight_compress`) [F].** Take any up-closed pair constraints on k blocks of size
b, and t ≤ k. The inputs whose weight vector is accepted and has at least t tight
coordinates number at most

  2^{k+1} · (2^b)^{k−⌈t/2⌉} · C(b, ⌊b/2⌋)^{⌈t/2⌉}.

Soundness is not assumed. This is the weighted Theorem B with "every coordinate" replaced
by "the tight coordinates".

**Lemma 6 (`mixed_tight`, `mixed_weight`) [F].** Let the test be sound and accept x of
weight N. Then every one of x lies in a tight A-block or a tight B-block. Hence
N ≤ |T_A|·a + |T_B|·b, where T_A and T_B are the sets of tight coordinates.

*Proof.* Suppose a one e of x lies in a non-tight A-block and a non-tight B-block. Then
x − e still passes both families of constraints (`lower_nontight`), and it has weight
N − 1. That contradicts soundness. ∎

**Theorem (`mixed_cover`) [F].** Suppose (t_A − 1)·a + (t_B − 1)·b < N. Then a sound test
accepts at most

  2^{k_A+1}(2^a)^{k_A−⌈t_A/2⌉}C(a,⌊a/2⌋)^{⌈t_A/2⌉} + 2^{k_B+1}(2^b)^{k_B−⌈t_B/2⌉}C(b,⌊b/2⌋)^{⌈t_B/2⌉}

inputs of weight N. Take t_A = ⌈k_A/4⌉ and t_B = ⌈k_B/4⌉. Then the test covers at most

  ν ≤ (2^{k_A+1}(πa/2)^{−k_A/16} + 2^{k_B+1}(πb/2)^{−k_B/16}) · √(2n)   (D)

of the slice. **Mixing two partitions does not improve coverage beyond constants in the
exponent**: it is still b^{−Ω(k)}.

**Lemma 7 (`tight_cost`) [F].** If coordinate ℓ of an accepted vector u is tight, one pair
CNF of the test has at least C(b, u_ℓ − 1) clauses. This is the cost lemma of §2.5, again
without soundness.

**Theorem D (pen and paper, from the formalized ingredients).** Fix m. Let F be a monotone
Σ₃ formula for Majority with the following structure:
- each test chooses at most m partitions of the variables, each into blocks of equal size;
- each test is an AND of monotone block-symmetric pair functions, each reading two blocks of
  one of its partitions.

Then F has size 2^{Ω(√(n log n / m))}.

*Proof sketch.* The proof follows Theorem C and §2.7 (i), with Lemma 6 in place of "every
coordinate is tight".
- **Split.** Lemma 6 extends to m partitions. So for a covered x, some partition q of the
  test has at least N/m ones in its tight blocks, and therefore at least k_q/(2m) tight
  blocks. Assign x to such a q. This splits the coverage of each test into at most m
  parts.
- **Coverage of a part.** Let the part's partition have block size s, so k = n/s.
  - By Lemma 5 with t = ⌈k/(2m)⌉, the part covers at most 2^{k+1}(πs/2)^{−k/(8m)}√(2n) of
    the slice.
  - For small s, use PPZ instead. Each of the N/m ones in tight blocks has a critical clause
    of width at most 2s. So the part covers at most (n+1)·2^{−N/(2ms)}.
- **Cost of a part.** Suppose the part contains a point with a tight block of weight w,
  where s/4 ≤ w − 1 ≤ 3s/4. Then by Lemma 7 the test has at least
  C(s, ⌈s/4⌉) ≥ 2^{0.81s}/(s+1) clauses.
- **Atypical points.** Otherwise, every point in the part has at least k/(2m) tight blocks,
  all of weight outside the window. By Hoeffding, these points are at most a
  2^k (2e^{−2(s/4−1)²/s})^{k/(2m)}·(n+1) fraction of the slice. That is 2^{−Ω(n/m)} once s
  exceeds a constant.
- **Combining**, as in Theorem C. Either F has 2^{Ω(n/m)} tests, or the typical parts with
  large s cover half the slice. Each such part pays 2^{0.81s} clauses for at most
  2^{−c(n/s) log s / m} coverage. Optimizing over s gives 2^{Ω(√(n log n / m))}. ∎

For m = 2, which is the L-R shape, the class has complexity 2^{Θ(√(n log n))}. The upper
bound is the KPPY-style construction of §2.5, which uses a single partition.

**What m measures.** If m is unbounded, the class contains every monotone Σ₃ formula
with clause width at most 2b. Each clause can be given its own partition, with the clause's
variables in two blocks. Then only the PPZ bound 2^{Ω(n/b)} remains. At m ≈ log n,
Theorem D gives 2^{Ω(√n)}, the known general bound.

**Caveat.** Both the formal model and Theorem D assume equal block sizes within each
partition. In L-R, the last block of a partition can be shorter. Extending the weighted
counting to unequal sizes should only change constants, but this has not been checked.

### 2.9 Next steps

1. **Many partitions or wide constraints.** The monotone class is now pinned down whenever
   both m (partitions per test) and r (blocks per constraint) are bounded. Is there a
   monotone Σ₃ formula for Majority of size 2^{O(√n)} with m or r about log n? Or does a
   different argument give 2^{ω(√n)} there? This is where the monotone question now sits.
2. **Formalize (ii).** Generalize Theorem B to r-ary constraints. The averaging over all
   orders needs a convexity argument; for r = 2 an order and its reverse suffice.
3. **The rest of Theorems C and D.** The parts still on paper:
   - the Hoeffding estimates for cheap tests and atypical points;
   - the binomial estimates that turn (B) and (D) into powers of b;
   - the PPZ case for small b;
   - the optimization over b.
   Formalizing them would need real analysis rather than counting.
4. **The fixed-point form.** Formalize the reformulation in Section 2.3. It is no longer
   needed for Theorem B, but it links the problem to fixed points of networks.

