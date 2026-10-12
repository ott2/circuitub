# Locality and monotonicity in the Lecomte–Ramakrishnan construction

This document is separate from the verification of Lecomte and Ramakrishnan,
*Optimal Shallow Circuits for Majority* (arXiv:2609.34029). It asks how much of the
construction's structure is needed, and whether a more restricted class of circuits could
still reach the $2^{O(\sqrt n)}$ bound for depth-3 Majority.

Status:

| Part | Formalized in | Contents |
|---|---|---|
| Part 1: block locality | `isabelle/Block_Local.thy` | Formalized and covered by the oracle audit |
| Part 2: monotone tests | `isabelle/Monotone_Pairs.thy`, `Monotone_Cost.thy`, `Monotone_Mixed.thy`, `Monotone_Hyper.thy`, `Monotone_Wide.thy`, `Monotone_Kraft.thy`, `Binomial_Estimates.thy`, `Monotone_Formula.thy` | Formalized results are marked **[F]**; the rest is pen and paper. The finite part of Theorem E′ is formal end to end (`majority_wide_tests`). The main results are Theorems C, D, E and E′: in the shape of the L-R tests, including tests that mix two partitions, monotone formulas need $2^{\Theta(\sqrt{n \log n})}$; so do block-symmetric tests of any scope once blocks have size $\ge n^{1/3+\varepsilon}$ |

Notation:
- $n$ is the number of variables, $N = n/2$, and Majority means weight $\ge n/2$.
- A *test* is a middle-level AND gate of a $\Sigma_3$ formula, i.e. one disjunct of the
  top-level OR.

## Part 1. Block locality (formalized)

### 1.1 Two blocks suffice

`symmetric_or_of_cnfs_local` strengthens Remark 1 of the paper's v2. Suppose $k^2 \ge n$.
Then every symmetric function is an OR of at most $2^{Ck}$ CNFs of clause width
$2\lceil n/k \rceil$. Moreover, there are block sizes $s_0, s_1 \le \lceil n/k \rceil$ such that
**every clause reads variables from at most two blocks $\lbrace v : v \mathbin{\mathrm{div}} s_l = i\rbrace$
of a single partition $l \in \lbrace 0, 1\rbrace$**.

The two partitions correspond to the construction's two moduli. Each clause comes from
one pair check: a symmetric function of $\mathrm{block}_i \cup \neg\,\mathrm{block}_j$.

### 1.2 One block does not suffice (for a single partition)

`one_block_tests` assumes the following:
- `Or ts` computes Majority on $n$ variables, with $n$ even.
- There is a fixed map `blk` from variables to blocks.
- Every test in `ts` is an AND of subformulas, of any depth or shape, each of which reads
  variables from a single block.

Then `length ts` is at least the number of block-weight vectors $(w_p)_p$ of inputs of
weight $n/2$.

*Proof idea.* Suppose one test accepts two weight-$n/2$ inputs $\sigma$ and $\sigma'$ with
different block weights. Build $\tau$ by taking $\sigma$ on the blocks where it is lighter
and $\sigma'$ elsewhere.
- Every conjunct sees a single block, so the test accepts $\tau$.
- $\tau$ has weight $\sum_p \min(w_p, w'_p) < n/2$.
- That contradicts the test implying Majority.

`one_block_tests_equal` applies this to $m$ blocks of $b$ consecutive variables, with $m$
even. There are then at least $(b+1)^{m/2}$ tests. For $b = m = \sqrt n$ this is
$2^{\Omega(\sqrt n \log n)}$.

**What the comparison shows.** At the same block size, the construction needs only
$2^{O(\sqrt n)}$ tests, and its tests read two blocks. So the $\sqrt{\log n}$ improvement of
L-R over divide-and-conquer (Klawe–Paul–Pippenger–Yannakakis, KPPY84) comes from tests
that read two blocks.

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
| Monotone upper bound $2^{O(\sqrt{n \log n})}$ (still the best known) | KPPY, STOC 1984 |
| Lower bound $2^{\Omega(\sqrt n)}$, monotone | Boppana, JCSS 1986 |
| Lower bound $2^{(d-o(1))\sqrt n}$ with $d = 1/\sqrt{\ln 4} \approx 0.849$, general circuits | Håstad–Jukna–Pudlák, Comput. Complexity 1995 |
| Bottom fan-in 3, monotone: exactly $(2/6^{1/4})^{n \pm o(n)} \approx 1.27785^n$ | Gurumukhani et al., arXiv:2601.04072 (2026); the upper bound on transversals and the resulting lower bound for Majority are formally checked, with six gaps in the proof repaired ([`monotone-3cnf.md`](monotone-3cnf.md)) |

**Amano (ISAAC 2023).** This paper compares $\Sigma_3$ circuits whose bottom clauses have at
most $k$ positive and $\ell$ negative literals with monotone ones.

| Bottom fan-in $k$ | Non-monotone (with negations) | Best monotone |
|---|---|---|
| $k \le 2$ | same as monotone | — |
| 3 | $O(1.2768^n)$ | $1.2779^n$ |
| 4 | $O(1.2040^n)$ | $O(1.2093^n)$ |
| 5 | $O(1.1751^n)$ | $O(1.1760^n)$ |

- For $k \le 2$, negations do not help.
- For $k = 3, 4, 5$ they help, but only by a small margin. At $k = 3$ the non-monotone bound
  $1.2768^n$ is just below the exact monotone optimum $1.27785^n$.
- Amano's constructions also use a fixed partition. Each block gets a target weight
  proportional to the global threshold. **No test couples two blocks.**

So the bounded-fan-in evidence says negations help only slightly at small fan-in.
L-R show that, with unbounded fan-in, negations plus pairwise coupling remove a
$\sqrt{\log n}$ factor from the exponent.

**Beyond the parity barrier: other functions.** By L-R, no symmetric function needs
depth-$d$ circuits larger than $2^{O(n^{1/(d-1)})}$. Two recent papers beat this bound with
non-symmetric explicit functions.
- OpenAI (Sept 2026) gives a function in P that needs OR–AND–OR circuits of size
  $2^{\omega(\sqrt n)}$.
- Chukhin (ECCC TR26-248) shows that every depth-$d$ circuit, $d \ge 3$, for the
  Goldreich–Tal trilinear function $\sum_{i,j} a_{i+j}x_iy_j \bmod 2$ needs
  $2^{\Omega((n\log n/\log\log n)^{1/(d-1)})}$ gates. At depth 3 this is $2^{\tilde\Omega(\sqrt{n \log n})}$,
  about the size of the monotone KPPY formulas for Majority.
  - The proof is the HJP95 top-down argument with correlations instead of counts. A
    restriction lemma bounds the expected $\mathrm{size}_b$ of a restricted wide CNF by $1$,
    and a disjoint sparsification lemma does the rest. The method stops at
    $(n\log n)^{1/(d-1)}$.

This does not change the questions here. Their answers concern Majority, which is
symmetric, and for monotone formulas Majority's depth-3 complexity is still between
$2^{\Omega(\sqrt n)}$ and $2^{O(\sqrt{n\log n})}$. Two reasons the new technique does not
transfer:
- Random restrictions push Majority's threshold outside the window of the live variables.
- The restriction lemma writes $H_\rho$ as a signed sum of narrow CNFs. That loses the
  monotone count ("few accepted points of weight $n/2$") on which our covering bounds rest.

It does change the context: since L-R, the open question for Majority is a
monotone/non-monotone separation, not a route past the parity barrier.

### 2.2 The class

Fix a partition into $k$ blocks of size $b$, so $n = kb$. The class consists of **monotone,
block-symmetric, pairwise** tests. Each is an AND of monotone functions that each read at
most two blocks and depend only on the two block weights. This is the shape of the L-R
pair tests, without the negations.

**Weight-vector form.** A test corresponds to

$$W = \lbrace w \in [0,b]^k : (w_i, w_j) \in P_{ij} \text{ for all } i \ne j\rbrace,$$

where each $P_{ij}$ is up-closed. The test is sound iff $W \subseteq \lbrace \textstyle\sum w \ge N\rbrace$.

**Coverage.** The test covers $H = W \cap \lbrace \sum w = N\rbrace$. Each weight vector $w$
stands for $\prod_i \binom{b}{w_i}$ inputs. The fraction of the Majority slice that the test
covers is

$$\nu(H) = \frac{\sum_{w \in H} \prod_i \binom{b}{w_i}}{\binom{n}{N}}.$$

For comparison, L-R's non-monotone tests reach $\nu(H) \ge e^{-O(k)}$.

### 2.3 Exact reformulation [F]

**Lemma 1 (`test_valid`, `valid_test`).** Let $\mathrm{cl}(H)$ be the set of $z$ such that
every pair $(i, j)$ is dominated, on coordinates $i$ and $j$, by some $h \in H$. Then $H$ is
the covered set of a sound test iff $\mathrm{cl}(H) \cap \lbrace \sum < N\rbrace = \emptyset$.
Isabelle calls this property `valid k N H`.

The best possible test coverage is therefore

$$Q(k,b) = \max\lbrace \nu(H) : H \text{ valid}\rbrace.$$

**Lemma 2 (`exchange`).** For valid $H$, every $p \in H$ and every coordinate $\ell$ have a
*witness* $i \ne \ell$: no $h \in H$ has $h_\ell < p_\ell$ and $h_i \le p_i$.

*Proof.* Suppose not. For each $i \ne \ell$, pick a counterexample $h^{(i)}$. Lower $p_\ell$
to $\max_i h^{(i)}_\ell$. The resulting point lies in $\mathrm{cl}(H)$ but has weight below
$N$. ∎

**Lemma 3 (`determination`).** If $i$ is a witness for $(p, \ell)$, then
$p_\ell = \mu_{i\ell}(p_i)$, where $\mu_{i\ell}(x) = \min\lbrace h_\ell : h \in H,\ h_i \le x\rbrace$
is a non-increasing function that depends only on $H$.

**An equivalent form** (pen and paper). Write each up-closed $P_{\ell j}$ as
$\lbrace (x, y) : x \ge \varphi_{\ell j}(y)\rbrace$, with $\varphi_{\ell j}$ non-increasing. Then:
- $W = \lbrace z : z \ge T(z)\rbrace$, where $T(z)_\ell = \max(0, \max_{j \ne \ell} \varphi_{\ell j}(z_j))$.
- The minimal elements of $W$ are exactly the fixed points of $T$.
- $T$ is antitone, i.e. order-reversing, so its fixed points form an antichain.

So **$Q(k,b)$ is the largest slice mass of the fixed points of an antitone "max of unary
maps" network on $[0,b]^k$ whose up-set lies above the hyperplane.** This links the problem
to fixed points of Boolean and $q$-ary networks. Bounds there in terms of feedback vertex
sets (Aracena and others; recalled, not checked here) give only $(b+1)^{k-1}$ for complete
interaction graphs. The max structure is what brings this down to $(b+1)^{k/2}$, up to a
$2^{O(k)}$ factor (Theorem B).

### 2.4 Theorems A and B, and tightness [F]

Both theorems hold for valid `H ⊆ {..<k} →E {..b}` with $k \ge 2$.

**Theorem A** (`pairwise_count`, `pairwise_weight`) is the first version:

| Theorem | Statement |
|---|---|
| `pairwise_count` | $\lvert H\rvert \le (k-1)^k (b+1)^{\lfloor k/2\rfloor}$ |
| `pairwise_weight` | $\sum_{p \in H} \prod_i \binom{b}{p_i} \le (k-1)^k (2^b)^{\lfloor k/2\rfloor} \binom{b}{\lfloor b/2\rfloor}^{\lceil k/2\rceil}$ |

*Proof.* Choose a witness for every coordinate of $p$. This gives a fixed-point-free map
$f_p$. By Lemma 3, $p$ is determined by $f_p$ and its values on the smaller of the descent
and ascent sets of $f_p$, which has at most $k/2$ elements. Recording $f_p$ costs the factor
$(k-1)^k$. ∎

The factor $(k-1)^k$ made Theorem A vacuous in the decisive regime $b \approx k$. Theorem B
removes it.

**Theorem B** (`sharp_bounds`):

| Part | Statement |
|---|---|
| (1) | $\lvert H\rvert \le 2^{k+1} (b+1)^{\lfloor k/2\rfloor}$ |
| (2) | $\sum_{p \in H} \prod_i \binom{b}{p_i} \le 2^{k+1} (2^b)^{\lfloor k/2\rfloor} \binom{b}{\lfloor b/2\rfloor}^{\lceil k/2\rceil}$ |

*Proof.* The point is that the decoder does not need to know which coordinate is the
witness.
1. For every $p \in H$ and all $j \ne \ell$, $\mu_{j\ell}(p_j) \le p_\ell$ (take $h = p$ in the
   definition of $\mu$). Equality holds when $j$ is a witness (Lemma 3).
2. Fix an order on the coordinates. Call $\ell$ *free* for $p$ if every witness of
   $(p, \ell)$ comes after $\ell$. Otherwise some witness comes earlier, and then
   $p_\ell = \max_{j \text{ earlier}} \mu_{j\ell}(p_j)$.
3. So $p$ is determined by its free set $S$ and its values on $S$ (`free_determined`). The
   proof is by induction along the order.
4. No coordinate is free both for an order and for its reverse, since every coordinate has
   a witness (Lemma 2). So for one of the two orders, $\lvert S\rvert \le k/2$ (`free_small`).
5. That gives at most $2 \cdot 2^k$ classes (order, $S$), each determined by at most $k/2$
   values. For the weighted form, sum the binomial weights freely over $S$ and bound the
   rest by $\binom{b}{b/2}$. ∎

Both theorems are instances of one counting lemma, `classes`.

**Coverage.** Take $b$ and $k$ even, and use $\binom{b}{b/2} \le 2^b/\sqrt{\pi b/2}$ and
$\binom{n}{n/2} \ge 2^n/\sqrt{2n}$. Theorem B then gives, for every sound test,

$$\nu(H) \le 2^{k+1} \cdot (\pi b/2)^{-k/4} \cdot \sqrt{2n}. \tag{B}$$

So $Q(k,b) \le C^k \cdot b^{-k/4} \cdot \mathrm{poly}(n)$ with
$C = 2\,(2/\pi)^{1/4} \approx 1.79$. An earlier version of this document stated this bound as
an open conjecture ("Conjecture Q").

**Three blocks** (`three_blocks`). For $k = 3$, $\lvert H\rvert \le 2(b+1)$: each point is
determined by its witness coordinate.

**Tightness.** The *matching test* pairs up the blocks and requires
$w_{2q-1} + w_{2q} \ge b$ for each pair.

| Theorem | Statement |
|---|---|
| `matching_valid` | The matching test is valid |
| `matching_card` | It covers $(b+1)^{k/2}$ weight vectors |
| `matching_weight` | It covers at least $\binom{2b}{b}^{k/2}$ inputs, i.e. $\nu \approx (\pi b)^{-k/4} \sqrt{\pi k b/2}$ |

So Theorem B is tight up to a factor $2^{O(k)}$, in both forms. Matching tests are optimal
monotone pairwise tests, up to $C^k$.

**Connection to PPZ.** Theorem B is a block-level version of the satisfiability coding
lemma of Paturi, Pudlák and Zane. There, a solution of a $k$-CNF that is isolated in many
directions is encoded by writing bits in a random order and skipping the bits forced by a
clause. Here, coordinates are skipped when an earlier coordinate witnesses them. Two
features are specific to this setting:
- The forcing value is computed as a maximum, so the witness need not be named.
- An order and its reverse suffice; no random order is needed.

With $b = 1$ (blocks are single variables), $H$ is a set of minimal satisfying assignments
of a monotone 2-CNF, and the matching ($2^{n/2}$ minimum vertex covers) is optimal at
threshold $n/2$. This is the $k = 2$ case of Gurumukhani, Künnemann and Paturi
(arXiv:2412.20493). At other thresholds, Moon–Moser-type triangle constructions win: for
example, at threshold $2n/3$ there are $3^{n/3}$ minimum vertex covers. Theorem B's factor
$2^{k+1}$ is too large to see this difference.

### 2.5 The cost of a test, and the class lower bound

The finite ingredients are formalized in `isabelle/Monotone_Cost.thy`.

**Lemma 4 (`clause_per_maxfalse`) [F].** A monotone CNF needs a distinct clause for every
maximal false point. Two such points cannot share a clause, because their join would also
falsify it.

**Consequence (`pair_cost`, `test_cost`) [F].** Suppose a sound test covers $p$, and
$1 \le p_\ell$.
- $p - e_\ell$ has weight $N - 1$, so the test rejects it. Some pair function involving
  $\ell$ changes value there (`test_boundary`).
- Going up in the other coordinate, that pair function has a maximal false weight pair
  $(p_\ell - 1, t)$ (`boundary`). As a Boolean function on $2b$ variables, it has at least
  $\binom{b}{p_\ell - 1}$ maximal false points, namely the inputs with these block weights
  (`pair_maxfalse`).
- So one pair CNF of the test has at least $\binom{b}{p_\ell - 1}$ clauses.

**Number of tests (`tests_needed`) [F].** A family of sound tests that accepts every
weight vector of the slice has at least

$$\frac{\binom{kb}{N}}{2^{k+1} \cdot (2^b)^{\lfloor k/2\rfloor} \cdot \binom{b}{\lfloor b/2\rfloor}^{\lceil k/2\rceil}}$$

members. The proof combines Theorem B with `slice_count`: the slice's weight vectors
account for all $\binom{kb}{N}$ inputs of weight $N$. Only the inequality is needed, and it
avoids the Vandermonde identity.

**Theorem C (pen and paper, from the formalized ingredients above).** Let $F$ be a monotone
$\Sigma_3$ formula (an OR of monotone CNFs) for Majority on $n$ variables. Fix a partition of
the variables into $k$ blocks of size $b$. Suppose each test's clauses can be grouped by
pairs of blocks, so that each group computes a block-symmetric function of its two blocks.
Then $F$ has size $2^{\Omega(\sqrt{n \log n})}$. Formulas in this class of size
$2^{O(\sqrt{n \log n})}$ exist, so the class has complexity $2^{\Theta(\sqrt{n \log n})}$.

*Proof of the lower bound.* Let $b_0$ be a suitable absolute constant.
- **Small blocks, $b \le b_0$.**
  - Every clause has width at most $2b$.
  - An input of weight $N$ accepted by a sound test is *isolated* in $N$ directions: each of
    its $N$ neighbours of weight $N - 1$ is rejected.
  - By the PPZ coding lemma, a CNF of width $2b$ accepts at most $2^{n - N/(2b)}$ such
    inputs.
  - The slice has $\binom{n}{N} \ge 2^n/(n+1)$ points, so $F$ has at least
    $2^{n/(4b)}/(n+1)$ tests. That is $2^{\Omega(n)}$.
- **Large blocks, $b > b_0$.** Call a test *expensive* if it covers a point $p$ with some
  coordinate $p_\ell$ such that $b/4 \le p_\ell - 1 \le 3b/4$.
  - **Each expensive test is large.** By the consequence of Lemma 4, it has at least
    $\binom{b}{\lceil b/4\rceil} \ge 2^{0.81b}/(b+1)$ clauses.
  - **Cheap tests cover little.** The other tests cover only points whose coordinates all
    satisfy $\lvert p_\ell - b/2\rvert \ge b/4 - 1$. By Hoeffding, at most
    $2^{b+1} e^{-2(b/4-1)^2/b}$ subsets of one block have such a weight. So these points are
    at most a $(n+1) \cdot (2 e^{-2(b/4-1)^2/b})^k \le (n+1) e^{-n/10}$ fraction of the
    slice. That is below $1/2$ for large $n$.
  - **So there are many expensive tests.** The expensive tests cover at least half the
    slice, and by (B) each covers at most $2^{k+1}(\pi b/2)^{-k/4}\sqrt{2n}$ of it.
  - **Combining.** Writing $k = n/b$,

    $$\log_2 \mathrm{size}(F) \ge 0.81\, b + \frac{n}{b} \left(\tfrac14 \log_2(\pi b/2) - 1\right) - O(\log n).$$

  - **Optimizing over $b$.** For $b > b_0$, the bracket is at least $\frac18 \log_2 b$. If
    $b \ge \sqrt{n \log n}$, the first term is $\Omega(\sqrt{n \log n})$. Otherwise, since
    $\log b / b$ decreases, the second term is at least
    $\frac{n}{8b} \log_2 b \ge \Omega(\sqrt{n \log n})$. ∎

*Upper bound inside the class.*
- **The tests.** Pair up the blocks. For every profile $c$ with $\sum_q c_q = N$, take the
  test $\bigwedge_q [w_{2q-1} + w_{2q} \ge c_q]$. Every slice point passes the test given by
  its own pair sums, so the OR of these tests computes Majority.
- **Size.** Each conjunct is a threshold function of $2b$ variables, with at most $4^b$
  clauses. There are at most $(2b+1)^{k/2}$ profiles.
- **Choice of $b$.** Take $b = \sqrt{n \log n}$. The size is then
  $2^{O((n/b) \log b + b)} = 2^{O(\sqrt{n \log n})}$. This is essentially KPPY's
  divide-and-conquer.

### 2.6 What this says about the L-R construction

The L-R tests have this shape, with negations: each clause reads two blocks of one of two
partitions (Part 1), through block-symmetric pair checks. Theorem C, extended to tests that
mix two partitions by Theorem D (§2.8), says that without negations the same shape cannot
beat KPPY. So **in this shape, the negations are responsible for the entire
$\sqrt{\log n}$ saving**. Amano's results point the same way at bounded fan-in: negations
help there too, but only slightly.

Theorem C does not settle the monotone depth-3 complexity of Majority: the gap between
$2^{\Omega(\sqrt n)}$ and $2^{O(\sqrt{n \log n})}$ remains open. Theorem C rules out one
route to closing it. Section 2.7 shows how far the class can be widened.

### 2.7 Widening the class (pen and paper)

**(i) Each test may choose its own partition.** The proof of Theorem C works test by test.
Let test $t$ use a partition into blocks of size $b_t$.
- **Few tests suffice for the bound.** If there are at least $2^{n/(8b_0)}$ tests, the size
  is already $2^{\Omega(n)}$. So assume there are fewer.
- **Small-block and cheap tests cover little.** Tests with $b_t \le b_0$ cover at most
  $(n+1) \cdot 2^{-n/(4b_0)}$ of the slice each (PPZ). Cheap tests cover at most
  $(n+1) \cdot e^{-n/10}$ each. With fewer than $2^{n/(8b_0)}$ tests, together they cover
  less than half the slice.
- **So expensive tests pay.** The expensive tests cover the rest. Each pays at least
  $2^{\Omega(\sqrt{n \log n})}$ clauses per unit of coverage, whatever its $b_t$.

So the fixed partition is not needed. The argument above still uses a single partition per
*test*. The L-R tests are not of this kind: one test contains pair checks for both moduli,
i.e. for both partitions. Section 2.8 handles that case.

**(ii) Clauses may read $r$ blocks.** Let each test be an AND of monotone block-symmetric
functions of $r$ block weights. The proof of Theorem B generalizes as follows:
- **Validity.** Validity now asks every $r$-set of coordinates to be dominated.
- **Exchange.** Every coordinate $\ell$ of $p \in H$ has a witness *set* $E$ of $r - 1$ other
  coordinates: no $h \in H$ has $h_\ell < p_\ell$ and $h_E \le p_E$. The proof is as for
  Lemma 2: lower $p_\ell$ to the maximum over the counterexamples.
- **Determination.** $p_\ell = \mu_E(p_E)$, and $\mu_{E'}(p_{E'}) \le p_\ell$ for every $E'$.
  So coordinate $\ell$ is determined once some witness set lies entirely before it.
- **Free coordinates.** In a uniformly random order, $\ell$ is free with probability at most
  $1 - 1/r$ ($\ell$ comes last among $E \cup \lbrace \ell\rbrace$ with probability $1/r$).
- **Averaging.** For each fixed order $\sigma$,
  $\sum_p \mathrm{wt}(p)\, \rho^{-\lvert F_\sigma(p)\rvert} \le 2^k \binom{b}{b/2}^k$, where
  $\rho = 2^b/\binom{b}{b/2}$. Average over $\sigma$ and apply Jensen. This gives

  $$\nu(H) \le 2^k \cdot (\pi b/2)^{-k/(2r)} \cdot \sqrt{2n}.$$

  Grouping the blocks $r$ at a time, with a threshold on each group's weight, shows this is
  tight up to $2^{O(k)}$.

**Formal version (`isabelle/Monotone_Hyper.thy`) [F].** The formal proof avoids Jensen. It
works with the test directly, as in §2.8, and uses tight coordinates and thresholds for
constraints with arbitrary scopes of at most $r$ blocks.
- **Colourings instead of a random order.** Order the coordinates by a colouring
  $c : \lbrace 0, \dots, k-1\rbrace \to \lbrace 0, \dots, r-1\rbrace$, breaking ties by index.
- **Each tight coordinate is often decoded.** A tight coordinate $\ell$ is decoded whenever
  its witness scope gets strictly smaller colours than $\ell$. Giving $\ell$ the top colour
  and the rest of the scope lower colours already accounts for
  $(r-1)^{r-1} r^{k-r}$ of the $r^k$ colourings (`good_colorings`).
- **So some colouring leaves few free coordinates.** Integer averaging (`average_free`)
  gives a colouring with at most $k - \lfloor t(r-1)^{r-1}/r^r\rfloor$ free coordinates,
  where $t$ is the number of tight coordinates. Note $(r-1)^{r-1}/r^r \ge 1/(er)$.
- **The count (`hyper_compress`).** The inputs whose weight vector is accepted and has at
  least $t$ tight coordinates number at most

  $$(2r)^k \cdot (2^b)^{k-y} \cdot \binom{b}{\lfloor b/2\rfloor}^y, \qquad y = \left\lfloor \frac{t(r-1)^{r-1}}{r^r} \right\rfloor.$$

- **Soundness gives tightness (`hyper_sound_tight`).** For a sound test, every positive
  coordinate of a slice point is tight.

For a sound test, $t$ is about $k$, so the coverage is at most
$(2r)^k (\pi b/2)^{-y/2}$ with $y/2 \approx k/(2er)$. The exponent is smaller than the
pen-and-paper $k/(2r)$ by the factor $(1 - 1/r)^{r-1} \ge 1/e$, and recording the colouring
costs $(2r)^k$. That is enough for $2^{\Omega(\sqrt{n \log n / r})}$ only while
$r \log r = o(\log n)$.

**Without the overhead (`hyper_kraft`) [F].** The Kraft and Jensen argument of §2.9 applies
unchanged. Both `wide_kraft` and `hyper_kraft` are instances of one lemma, `kraft_count`.
It needs only a family of free sets that determines the input and leaves each of $t$
coordinates decoded under a $(r-1)^{r-1}/r^r$ fraction of the colourings. With
$\delta = 1/(r+1)$, a sound test covers at most

$$e^{k/r} \left(\frac{r}{\sqrt{\pi b/2}}\right)^{t(r-1)^{r-1}/r^r} \sqrt{2n}$$

of the slice. A decoded block now gains $\frac12 \log_2 (\pi b/2) - \log_2 r$ bits, and the
only other loss is $\log_2 e$ bits per $r$ blocks. The gain beats that loss once
$\pi b/(2r^2) > e^{2e}$, and the coverage is a power of $b$ once $b \ge r^{2+\varepsilon}$.
In the optimization, $b \approx \sqrt{n \log n / r}$, so the formal ingredients now give
$2^{\Omega(\sqrt{n \log n / r})}$ for all $r \le n^{1/5 - \varepsilon}$. That includes the
whole range $r \lesssim \log n$ where the bound beats $2^{\sqrt n}$. The exponent of $b$ is
still smaller than in the pen-and-paper version by the factor $(1 - 1/r)^{r-1}$, at worst
$1/e$. That factor comes from colourings rather than random orders.

The cost lemma is unchanged: some $r$-ary constraint has a maximal false point with
$\ell$-coordinate $p_\ell - 1$, so it has at least $\binom{b}{p_\ell - 1}$ clauses. Optimizing
as before gives size $2^{\Omega(\sqrt{n \log n / r})}$.
- For constant $r$, the class still has complexity $2^{\Theta(\sqrt{n \log n})}$.
- At $r \approx \log n$ the bound reaches $2^{\Omega(\sqrt n)}$, the known general lower
  bound. So block-symmetric tests that read about $\log n$ blocks are not excluded by this
  argument.

**(iii) Block symmetry cannot simply be dropped.** Without it, take $k = 2$ blocks of size
$n/2$. Then every clause reads at most two blocks, so every monotone $\Sigma_3$ formula is in
the class. A meaningful version must bound the block size. For example, with
$b \le \sqrt n$ and arbitrary monotone pair functions, the cost lemma fails: a pair function
can have few clauses. Only the PPZ bound $2^{\Omega(n/b)} = 2^{\Omega(\sqrt n)}$ remains.

**Summary** (including §2.8 and §2.9). Any monotone $\Sigma_3$ formula for Majority of size
$2^{O(\sqrt n)}$ must do at least one of the following:
- mix about $\log n$ or more partitions inside one test (two, as in L-R, is not enough);
- use block-symmetric constraints on about $\log n$ or more blocks of size at most about
  $(n \log n)^{1/3}$ (with blocks of size $\ge n^{1/3+\varepsilon}$, wide constraints do not
  help, §2.9);
- give up block symmetry.

### 2.8 Tests that mix partitions [F]

The L-R tests contain pair checks for two partitions at once. Section 2.7 (i) allows each
test its own partition, but not several partitions within one test. This section removes
that restriction. The finite part is formalized in `isabelle/Monotone_Mixed.thy`.

**The model.** A test now has two partitions:
- $A$, into $k_A$ blocks of size $a$;
- $B$, into $k_B$ blocks of size $b$.

It accepts $x$ iff the $A$-weight vector $u$ of $x$ passes up-closed pair constraints $P$ and
the $B$-weight vector $v$ of $x$ passes up-closed pair constraints $Q$. The two weight
vectors are linked through $x$, so the slice reformulation of §2.3 does not apply. The
argument below works with the constraints directly.

**Tight coordinates.** Let $u$ be accepted. Call coordinate $\ell$ *tight* if lowering
$u_\ell$ by one violates a constraint between $\ell$ and some $i$, its *witness*.
- Let $\mathrm{th}_{\ell i}(y)$ be the least $x$ such that $(x, y)$ passes both constraints
  between $\ell$ and $i$. Then $u_\ell = \mathrm{th}_{\ell i}(u_i)$ for a witness $i$
  (`th_eq`), and $\mathrm{th}_{\ell j}(u_j) \le u_\ell$ for every $j$ (`th_le`). These are
  Lemma 3 and the first step of Theorem B, with the test in place of $H$.
- So Theorem B's decoding applies to the tight coordinates of *any* accepted vector. The
  decoder records the non-tight coordinates and the tight coordinates that are free for
  the order (`tfree_determined`). A tight coordinate is not free both in an order and in
  its reverse (`tfree_small`).

**Lemma 5 (`tight_compress`) [F].** Take any up-closed pair constraints on $k$ blocks of size
$b$, and $t \le k$. The inputs whose weight vector is accepted and has at least $t$ tight
coordinates number at most

$$2^{k+1} \cdot (2^b)^{k-\lceil t/2\rceil} \cdot \binom{b}{\lfloor b/2\rfloor}^{\lceil t/2\rceil}.$$

Soundness is not assumed. This is the weighted Theorem B with "every coordinate" replaced
by "the tight coordinates".

**Lemma 6 (`mixed_tight`, `mixed_weight`) [F].** Let the test be sound and accept $x$ of
weight $N$. Then every one of $x$ lies in a tight $A$-block or a tight $B$-block. Hence
$N \le \lvert T_A\rvert a + \lvert T_B\rvert b$, where $T_A$ and $T_B$ are the sets of tight
coordinates.

*Proof.* Suppose a one $e$ of $x$ lies in a non-tight $A$-block and a non-tight $B$-block.
Then $x - e$ still passes both families of constraints (`lower_nontight`), and it has
weight $N - 1$. That contradicts soundness. ∎

**Theorem (`mixed_cover`) [F].** Suppose $(t_A - 1) a + (t_B - 1) b < N$. Then a sound test
accepts at most

$$2^{k_A+1}(2^a)^{k_A-\lceil t_A/2\rceil}\binom{a}{\lfloor a/2\rfloor}^{\lceil t_A/2\rceil} + 2^{k_B+1}(2^b)^{k_B-\lceil t_B/2\rceil}\binom{b}{\lfloor b/2\rfloor}^{\lceil t_B/2\rceil}$$

inputs of weight $N$. Take $t_A = \lceil k_A/4\rceil$ and $t_B = \lceil k_B/4\rceil$. Then the
test covers at most

$$\nu \le \left(2^{k_A+1}(\pi a/2)^{-k_A/16} + 2^{k_B+1}(\pi b/2)^{-k_B/16}\right) \sqrt{2n} \tag{D}$$

of the slice. **Mixing two partitions does not improve coverage beyond constants in the
exponent**: it is still $b^{-\Omega(k)}$.

**Lemma 7 (`tight_cost`) [F].** If coordinate $\ell$ of an accepted vector $u$ is tight, one
pair CNF of the test has at least $\binom{b}{u_\ell - 1}$ clauses. This is the cost lemma of
§2.5, again without soundness.

**Theorem D (pen and paper, from the formalized ingredients).** Fix $m$. Let $F$ be a
monotone $\Sigma_3$ formula for Majority with the following structure:
- each test chooses at most $m$ partitions of the variables, each into blocks of equal size;
- each test is an AND of monotone block-symmetric pair functions, each reading two blocks of
  one of its partitions.

Then $F$ has size $2^{\Omega(\sqrt{n \log n / m})}$.

*Proof sketch.* The proof follows Theorem C and §2.7 (i), with Lemma 6 in place of "every
coordinate is tight".
- **Split.** Lemma 6 extends to $m$ partitions. So for a covered $x$, some partition $q$ of
  the test has at least $N/m$ ones in its tight blocks, and therefore at least $k_q/(2m)$
  tight blocks. Assign $x$ to such a $q$. This splits the coverage of each test into at most
  $m$ parts.
- **Coverage of a part.** Let the part's partition have block size $s$, so $k = n/s$.
  - By Lemma 5 with $t = \lceil k/(2m)\rceil$, the part covers at most
    $2^{k+1}(\pi s/2)^{-k/(8m)}\sqrt{2n}$ of the slice.
  - For small $s$, use PPZ instead. Each of the $N/m$ ones in tight blocks has a critical
    clause of width at most $2s$. So the part covers at most $(n+1) \cdot 2^{-N/(2ms)}$.
- **Cost of a part.** Suppose the part contains a point with a tight block of weight $w$,
  where $s/4 \le w - 1 \le 3s/4$. Then by Lemma 7 the test has at least
  $\binom{s}{\lceil s/4\rceil} \ge 2^{0.81s}/(s+1)$ clauses.
- **Atypical points.** Otherwise, every point in the part has at least $k/(2m)$ tight
  blocks, all of weight outside the window. By Hoeffding, these points are at most a
  $2^k (2e^{-2(s/4-1)^2/s})^{k/(2m)} (n+1)$ fraction of the slice. That is
  $2^{-\Omega(n/m)}$ once $s$ exceeds a constant.
- **Combining**, as in Theorem C. Either $F$ has $2^{\Omega(n/m)}$ tests, or the typical
  parts with large $s$ cover half the slice. Each such part pays $2^{0.81s}$ clauses for at
  most $2^{-c(n/s) \log s / m}$ coverage. Optimizing over $s$ gives
  $2^{\Omega(\sqrt{n \log n / m})}$. ∎

For $m = 2$, which is the L-R shape, the class has complexity $2^{\Theta(\sqrt{n \log n})}$.
The upper bound is the KPPY-style construction of §2.5, which uses a single partition.

**What $m$ measures.** If $m$ is unbounded, the class contains every monotone $\Sigma_3$
formula with clause width at most $2b$. Each clause can be given its own partition, with
the clause's variables in two blocks. Then only the PPZ bound $2^{\Omega(n/b)}$ remains. At
$m \approx \log n$, Theorem D gives $2^{\Omega(\sqrt n)}$, the known general bound.

**Caveat.** Both the formal model and Theorem D assume equal block sizes within each
partition. In L-R, the last block of a partition can be shorter. Extending the weighted
counting to unequal sizes should only change constants, but this has not been checked.

### 2.9 Unbounded scope, large blocks [F]

Section 2.7 (ii) loses a factor $r$ in the exponent, and at $r \approx \log n$ it reaches
only the general bound $2^{\Omega(\sqrt n)}$. With blocks of size 1, wide constraints are
arbitrary clauses, so some restriction is needed. This section shows that **block size
alone is enough**: once $b \ge n^{1/3+\varepsilon}$, the number of blocks a constraint reads
does not matter. The finite part is formalized in `isabelle/Monotone_Wide.thy` and
`isabelle/Monotone_Kraft.thy`.

**The model.** A test is any monotone CNF that is invariant under permuting the variables
inside each block. Equivalently, it is a monotone predicate $G$ of the block-weight vector,
and it may read all $k$ blocks at once. Every class in §2.2–2.7 (one partition per test) is
a special case.

**The idea.** In Theorem B, a coordinate $\ell$ is decoded once its whole witness scope is
known. That is wasteful for wide constraints.
- **The witness.** Let $p$ be accepted and $\ell$ tight. Take a maximal false weight vector
  $v$ above $p - e_\ell$ (`max_false`). Then $v_\ell = p_\ell - 1$ and $v_i \ge p_i$ for
  $i \ne \ell$.
- **Filling unknowns.** Fix a window $[\mathrm{lo}, \mathrm{hi}]$ of typical weights. The
  decoder fills every unknown typical coordinate with $\mathrm{hi}$, then takes the least
  $x$ such that $G$ accepts.
  - This never overshoots, because the fill lies above $p$.
  - It is exact as soon as every typical $i$ with $v_i < \mathrm{hi}$ is known (`wdec_eq`).
  - These are the *light* coordinates of the witness. Atypical coordinates are recorded
    explicitly.
- **Determination (`wfree_determined`).** Order the coordinates. Then $p$ is determined by
  its free set and its values there, as in Theorem B.
- **Light coordinates are expensive (`wide_maxfalse`, `wide_cost`).** Every input with block
  weights exactly $v$ is a maximal false point of the CNF. So the CNF has at least
  $\prod_i \binom{b}{v_i}$ clauses.
  - $\ell$ itself and each light coordinate $i$ have $v_i \in [\mathrm{lo} - 1, \mathrm{hi})$.
    So each contributes a factor
    $\beta = \min_{\mathrm{lo}-1 \le x < \mathrm{hi}} \binom{b}{x}$.
  - A CNF with fewer than $\beta^{w+1}$ clauses therefore has witnesses with fewer than $w$
    light coordinates.
  - Blocks that the clause reads "cheaply" are those with $v_i \ge \mathrm{hi}$, i.e. above
    the typical cap. Those need not be decoded.
- **The count (`wide_compress`, `wide_cover`).** Average over the $w^k$ colourings as in
  §2.7 (ii). Suppose a sound test's CNF has fewer than $\beta^{w+1}$ clauses. Then it
  accepts at most

  $$(2w)^k \cdot (2^b)^{k-y} \cdot \binom{b}{\lfloor b/2\rfloor}^y, \qquad y = \left\lfloor \frac{(k-a)(w-1)^{w-1}}{w^w} \right\rfloor \ge \left\lfloor \frac{k-a}{ew} \right\rfloor$$

  inputs of weight $N$ with at most $a$ atypical blocks.

**Theorem E (pen and paper, from `wide_cover`).** Let $F$ be a monotone $\Sigma_3$ formula
for Majority on $n$ variables. Suppose every test of $F$ is a monotone CNF invariant under
permutations inside the blocks of a partition into $k$ blocks of size $b \ge \sqrt n$. The
number of blocks a clause reads is unrestricted. Then $F$ has size
$2^{\Omega(\sqrt{n \log n})}$.

For $\sqrt n \le b \le \sqrt{n \log n}$, the KPPY construction of §2.5 lies in the class. So
the class has complexity exactly $2^{\Theta(\sqrt{n \log n})}$.

*Proof sketch.* Let $F$ have size $2^z$.
- **Window.** Take $[\mathrm{lo}, \mathrm{hi}] = [b/2 - \sqrt{2b},\ b/2 + \sqrt{2b}]$.
  - Since $H(\frac12 + x) \ge 1 - 4x^2$, we get $\log_2 \beta \ge b - \log_2(b+1) - 9$.
  - By Hoeffding, a block of a uniformly random input is atypical with probability at most
    $2e^{-4}$. So the inputs with more than $k/2$ atypical blocks are at most a
    $(n+1) \cdot 2^k \cdot (2e^{-4})^{k/2} \le (n+1)e^{-k/2}$ fraction of the slice.
  - So at least half of the slice has at most $a = k/2$ atypical blocks.
- **Cost.** A test covering such a point has a typical tight block, whose witness alone
  costs $\beta$ clauses. So $z \ge \log_2 \beta \approx b$. Put
  $w = \lfloor z / \log_2 \beta\rfloor \ge 1$; every test has fewer than $\beta^{w+1}$
  clauses.
- **Coverage.** By `wide_cover` and $\binom{b}{b/2} \le 2^b/\sqrt{\pi b/2}$, each test covers
  at most $(n+1)(2w)^k(\pi b/2)^{-y/2}$ of the slice, where $y \ge k/(2ew) - 1$. Hence

  $$z \ge \frac{y}{2} \log_2(\pi b/2) - k \log_2(2w) - \log_2(2(n+1)).$$

- **Optimizing.** Suppose $z \le c\sqrt{n \log n}$ with $c$ small.
  - Then $b \le 2z$, $w \le 2z/b$ and $y \ge n/(4ez) - 1$.
  - Since $b \ge \sqrt n$, the first term is at least $(1 - o(1))\, n \log_2 n/(16ez)$.
  - The overhead is $k \log_2(2w) \le \sqrt n \log_2(4c\sqrt{\log_2 n}) = o(n \log n / z)$.
  - So $z^2 \ge (1 - o(1))\, n \log_2 n/(16e)$, which contradicts $c < 1/7$. ∎

**Where this proof stops.** The proof uses $b \ge \sqrt n$ twice: $\log b \ge \frac12 \log n$,
and the colouring overhead $k \log w$ must be $o(n \log b / z)$. The second condition holds
down to $b \approx \sqrt{n/\log n} \cdot \log\log n$. Below that, the gain of
$\frac12 \log b$ bits per decoded block no longer pays for recording the colouring.

**Averaging instead of choosing [F].** The overhead is an artefact. `wide_compress` picks a
good colouring for each accepted vector and records it, paying $(2w)^k$.
`Monotone_Kraft.thy` records nothing.
- **Kraft (`kraft_partial`).** Fix a colouring $c$. The map
  $u \mapsto (\text{decoded, or } u_i)_i$ is injective on accepted vectors
  (`wfree_determined`). Weight a decoded coordinate by $\delta$ and a free coordinate of
  value $x$ by $(1 - \delta)\binom{b}{x}/2^b$. The weights per coordinate sum to 1, so the
  weights of the accepted vectors sum to at most 1.
- **Cost of a decoded coordinate.** Comparing with the true input count
  $\prod_i \binom{b}{u_i}$, a free coordinate costs a factor $2^b/(1 - \delta)$. A decoded one
  costs $\delta 2^b/(1 - \delta)$ divided by
  $\lambda = \delta 2^b / \bigl((1 - \delta)\binom{b}{\lfloor b/2\rfloor}\bigr)$.
- **Jensen (`power_average`).** Average over all $w^k$ colourings. By `free_sum`, a tight
  coordinate is decoded under at least a $(w-1)^{w-1}/w^w \ge 1/(ew)$ fraction of them.
  Since $\lambda^D$ is convex in $D$, the average of $\lambda^D$ is at least $\lambda^y$. The
  proof of Jensen used here is just $e^x \ge 1 + x$.
- **Result (`wide_kraft`, `wide_cover_kraft`).** If a sound test's CNF has fewer than
  $\beta^{w+1}$ clauses, the inputs of weight $N$ with at most $a$ atypical blocks that it
  accepts number at most

  $$\left(\frac{2^b}{1 - \delta}\right)^k \lambda^{-y}, \qquad y = \frac{(k-a)(w-1)^{w-1}}{w^w}.$$

  With $\delta = 1/(w+1)$ and $\binom{b}{\lfloor b/2\rfloor} \le 2^b/\sqrt{\pi b/2}$, this is
  $2^n e^{k/w} \bigl(w/\sqrt{\pi b/2}\bigr)^y$. A decoded block now gains
  $\frac12 \log b - \log w$ bits, and nothing is paid per block except $e^{1/w}$.

**Theorem E′ (pen and paper, from `wide_cover_kraft`).** Fix $\alpha > 1/3$. In Theorem E,
assume only $b \ge n^\alpha$. Then $F$ has size $2^{\Omega(\sqrt{(3\alpha - 1)\, n \log n})}$.
For $n^\alpha \le b \le \sqrt{n \log n}$ the class therefore has complexity exactly
$2^{\Theta(\sqrt{n \log n})}$. The upper bound is the construction of §2.5 with groups of
about $\sqrt{n \log n}/b$ whole blocks in place of pairs. A threshold on a union of blocks
is block-symmetric, and the scope is unrestricted.

*Proof sketch.* The window, the Hoeffding step ($a = k/2$) and the choice of $w$ are as in
Theorem E. If $F$ has size $2^z$, the number of tests is at least
$\frac12 \binom{n}{N} / \max\lvert S\rvert$ with $\binom{n}{N} \ge 2^n/\sqrt{2n}$. So

$$z \ge \frac{k}{2ew}\left(\tfrac12 \log_2 b - \log_2 w - 8\right) - \tfrac12 \log_2(8n).$$

Suppose $z \le c\sqrt{n \log_2 n}$. Then $w \le \max(1, 2z/b)$, so
$\log_2 w \le (\frac12 - \alpha) \log_2 n + O(\log\log n)$, and the bracket is at least
$\frac{3\alpha - 1}{2} \log_2 n - O(\log\log n)$. Also $k/(2ew) \ge n/(4ez)$. Hence
$z^2 \ge (1 - o(1))(3\alpha - 1)\, n \log_2 n/(8e)$, a contradiction once
$c^2 < (3\alpha - 1)/(8e)$. ∎

At $\alpha = \frac12$ the constant matches Theorem E. The point is the range: the argument
now works whenever $\sqrt b \gg w$, i.e. $b^{3/2} \gg \sqrt{n \log n}$.

**The finite part, formally (`majority_wide_tests`) [F].** Everything above the
optimization over $n$ is now formal, starting from the formula itself:
- **The formula.** `Monotone_Formula.thy` takes a set of tests, each a monotone CNF (a set
  of clauses) whose value depends only on the block weights. The formula is required to
  compute Majority with threshold $\lfloor n/2\rfloor$.
- **Tests as weight predicates.** Each test is turned into a monotone predicate on weight
  vectors (`tw`, `tw_cnf`, `tw_sound`), so `wide_cover_kraft` applies to it. Summing over
  the tests gives `formula_kraft`.
- **The estimates** are in `Binomial_Estimates.thy`, in elementary form:
  - $\binom{b}{\lfloor b/2\rfloor}^2(3b+2) \le 2 \cdot 4^b$ (`central_binomial`), in place of
    $\binom{b}{\lfloor b/2\rfloor} \le 2^b/\sqrt{\pi b/2}$;
  - $2^n \le (n+1)\binom{n}{\lfloor n/2\rfloor}$ (`slice_lower`), in place of $2^n/\sqrt{2n}$;
  - Chebyshev's inequality for block weights, from
    $\sum_x \binom{b}{x}(2x-b)^2 = b\,2^b$ (`binomial_moment`, `chebyshev_window`), in place
    of Hoeffding. So the window is $[m - d, m + d]$ with $d^2 \ge 4b$ instead of
    $\sqrt{2b}$;
  - $\binom{b}{m-j} \ge \binom{b}{m} e^{-2j(j+1)/m}$ for $4j \le m$ (`window_lower`,
    `window_beta`). So $\log_2 \beta \ge b - \log_2(b+1) - O(1)$ for $d \approx 2\sqrt b$;
  - $(w-1)^{w-1}/w^w \ge 1/(ew)$ and $(1 + 1/w)^k \le e^{k/w}$.
- **Half the slice is typical (`atypical_count`, `typical_half`).**

The result: if every test has fewer than $\beta^{w+1}$ clauses, where
$\beta = \binom{b}{m-d-1}$ is the smallest coefficient in the window, then the number $T$
of tests satisfies

$$\log_2 T \ge \frac{k}{2ew}\left(\tfrac12 \log_2\frac{3b+2}{2} - \log_2 w - 2e\log_2 e\right) - \log_2\bigl(2(n+1)\bigr).$$

Here $2e \log_2 e < 7.85$ and $\frac12\log_2\frac32 > 0.29$. So the bracket is at least the
paper's $\frac12 \log_2 b - \log_2 w - 8$. The additive term is $\log_2(2(n+1))$ instead of
$\frac12 \log_2(8n)$, because the slice bound is cruder; this does not affect the asymptotics.

The formal statement makes three side conditions explicit, which the sketch above used
silently:
- $2(n+1) \le 2^k$. This is what makes half of the slice typical; the sketch needed
  $(n+1)e^{-k/2} \le \frac12$.
- $w \binom{b}{\lfloor b/2\rfloor} \le 2^b$, i.e. $\lambda \ge 1$, so roughly $w \le \sqrt b$.
  Jensen's step needs it. When it fails, the bracket is negative and the bound says nothing
  anyway. In the optimization, $w \le 2z/b$, and $2z/b \le \sqrt b$ holds exactly when
  $\alpha > 1/3$, the same threshold.
- The window lies inside $[2, b-2]$ and $d^2 \ge 4b$. This needs $b$ above a small constant.

All three hold in the regime of the contradiction argument.

**In terms of the size alone (`majority_wide_size`, `majority_wide_explicit`) [F].** The step
from $w$ to $z$ is formal too.
- If the formula has at most $2^z$ tests, each with at most $2^z$ clauses, take
  $w = \lfloor z/\log_2\beta\rfloor + 1$. Then every test has fewer than $\beta^w$ clauses,
  and the bound of `majority_wide_tests` holds with $W = z/\log_2\beta + 1$ in place of $w$.
- The condition $\lambda \ge 1$ disappears: when it fails, the bracket is negative and the
  bound is trivial.
- For $b \ge 300$ a window with $d \approx 2\sqrt b$ exists (`window_d`), and then
  $\log_2\beta \ge b/2$ (`beta_half`, from `beta_log`). With $Z = \max(z, b)$ this gives one
  explicit inequality, with no further side conditions except $2(n+1) \le 2^k$:

  $$n\left(\tfrac12\log_2\frac{3b+2}{2} - \log_2\frac{3Z}{b} - 2e\log_2 e\right) \le 6e\,Z\bigl(Z + \log_2(2(n+1))\bigr).$$

Only solving this for $Z$ is left on paper. With $b \ge n^\alpha$ and
$Z \le C\sqrt{n \log_2 n}$, the bracket is at least
$\frac{3\alpha-1}{2}\log_2 n - O(\log\log n)$, so
$Z^2 \ge (1 - o(1))\frac{3\alpha-1}{12e}\, n\log_2 n$. For
$b \le c\sqrt{n\log_2 n}$ with $c^2 < \frac{3\alpha-1}{12e}$ this means $Z = z$. The constant is
$12e$ rather than the sketch's $8e$, because the formal proof bounds $W \le 3Z/b$. For larger
$b$, the cost of one tight typical block, $z \ge \log_2\beta \ge b/2$, gives the bound.

**Where it stops now.** At $b \approx (n \log n)^{1/3}$ the bracket vanishes. A block is
decoded only under about a $1/w$ fraction of the orders, and identifying the decoded blocks
costs about $\log w$ bits each. With $w \approx \sqrt{n \log n}/b$ this matches the
$\frac12 \log b$ bits a decoded block saves. Below $n^{1/3}$, a different kind of argument is
needed. With $b = 1$ the class is everything (§2.10).

**Why this is natural.** In a block-symmetric CNF, a clause that ties $\ell$ to a typical
block $i$ contains all $\binom{b}{v_i} \approx 2^b$ ways of choosing the zeros of $i$. So wide
coupling costs about $b$ bits of size per coupled block. That is exactly the exchange rate
of the KPPY threshold groups: tying $r$ blocks costs $2^{rb}$ and buys coverage
$b^{-k/(2r)}$. Theorem E says nothing beats that rate.

### 2.10 Next steps

1. **Small blocks with wide constraints, or many partitions.** Theorems C–E pin down the
   monotone class whenever either
   - blocks are large ($b \ge n^{1/3+\varepsilon}$, any scope: Theorems E and E′), or
   - both $m$ (partitions per test) and $r$ (blocks per constraint) are bounded
     (Theorems C, D).

   What remains is small blocks with wide constraints, or many partitions per test. There
   the block-symmetric classes stop being restrictions:
   - with blocks of size 1, an $r$-ary block-symmetric constraint is just a monotone clause
     of width $r$, so the $r$-ary class contains every monotone $\Sigma_3$ formula of bottom
     fan-in $r$;
   - with unbounded $m$, the class contains every monotone $\Sigma_3$ formula of clause width
     $2b$ (§2.8).

   By PPZ, a monotone $\Sigma_3$ formula of size $2^{O(\sqrt n)}$ must have clauses of width
   $\Omega(\sqrt n)$. So for $r$ or $m$ around $\sqrt n$, the question "is there a formula of
   size $2^{O(\sqrt n)}$ in the class?" is the general open question of the monotone depth-3
   complexity of Majority.

   The gap between Theorem E′ ($b \gg (n \log n)^{1/3}$) and $b = 1$ is the natural next
   target. There the decoding argument breaks even: a decoded block saves $\frac12 \log b$
   bits, but finding out which blocks are decoded costs $\log w \approx \log(\sqrt n/b)$ bits
   each. Going below $n^{1/3}$ needs either a cheaper way to locate decodable blocks, or a
   different exchange rate.
2. **Sharper formal constants for (ii).** Done in part: `hyper_kraft` removes the $(2r)^k$
   overhead (§2.7). Its exponent is $k(1 - 1/r)^{r-1}/(2r) \ge k/(2er)$; reaching the
   pen-and-paper $k/(2r)$ needs random orders instead of colourings. That means averaging
   over the $k!$ permutations, where $\ell$ comes after its $r - 1$ witnesses with probability
   exactly $1/r$. Since `kraft_count` only uses the colourings through `free_sum`, swapping in
   permutations should mostly be a matter of counting them.
3. **The rest of Theorems C and D.** For Theorem E′ the finite part is formal
   (`majority_wide_tests`, §2.9). The same tools cover most of what C and D still need on
   paper:
   - Chebyshev (`chebyshev_window`, `atypical_count`) can replace Hoeffding for atypical
     points;
   - `central_binomial` turns (B) and (D) into powers of $b$.

   The PPZ case for small $b$ is now formal as well: `ppz_count` in
   `isabelle/Depth3_Lower.thy` bounds a CNF in which every one of every accepted point has a
   critical clause with at most $r - 1$ other variables. With $r = 2b$ it gives
   $2^{n - N(r-1)^{r-1}/r^r} \le 2^{n - N/(2eb)}$ accepted points, instead of
   $2^{n - N/(2b)}$; the factor $e$ comes from colourings in place of permutations (item 2).
   The same file proves the depth-3 lower bound for Majority itself
   (`majority_depth3_sqrt`), so the paper's optimality claim is now checked at depth 3.
   Still missing are the cheap-test split of Theorem C and the optimizations over $b$ and $n$. The last is calculus with $o(1)$ terms; an explicit-constant
   version for fixed $\alpha$ would be the natural formal target.
4. **The fixed-point form.** Formalize the reformulation in Section 2.3. It is no longer
   needed for Theorem B, but it links the problem to fixed points of networks.
