# Optimal shallow circuits for symmetric functions, in Isabelle/HOL

A machine-checked proof of the main theorem of

> Victor Lecomte and Prasanna Ramakrishnan, *Optimal Shallow Circuits for Majority*,
> [arXiv:2609.34029](https://arxiv.org/abs/2609.34029) (2026).

**Theorem.** For every constant $d \ge 2$, every symmetric Boolean function on $n$
variables has depth-$d$ AND/OR formulas, with negations only on inputs, of size
$2^{O(n^{1/(d-1)})}$. The constant depends only on $d$.

In particular, Majority has depth-$d$ circuits of size $2^{O(n^{1/(d-1)})}$, matching
Håstad's lower bound. For depth 3, that is $2^{O(\sqrt n)}$.

At depth 3 the matching lower bound is formalized too (`isabelle/Depth3_Lower.thy`). Every
$\Sigma_3$ or $\Pi_3$ formula for Majority on $n \ge 1$ variables has at least
$2^{\sqrt n/4}/((n+1)(n+2))$ gates (`majority_depth3_sqrt`). So depth-3 Majority is
$2^{\Theta(\sqrt n)}$, with both directions machine-checked. The proof is the elementary
argument of Håstad, Jukna and Pudlák and of Paturi, Pudlák and Zane:
- In a CNF of the formula that accepts a point of the middle slice, every one of the point
  has a *critical clause*: a clause whose only true literal at the point is that one.
- **Narrow critical clauses** force their variable in a random order of the variables, and
  forced variables need not be recorded (`ppz_count`). The Kraft inequality is proved with
  disjoint cylinders (`forced_kraft`), and the random order is a random colouring, as in
  `Monotone_Hyper`.
- **Wide critical clauses** are critical for few points (`crit_count`).

The general statement (`sigma3_threshold`) holds for every threshold. Lower bounds for
depth $d > 3$ need the switching lemma and are not formalized. The constant $1/4$ is
weaker than the best known, $0.849$ (Håstad, Jukna and Pudlák); only the order
$\sqrt n$ matters for the optimality claim.

The Isabelle statement (`isabelle/Majority_Circuits.thy`) is slightly stronger than the
paper's claim. It bounds formula (tree) size rather than circuit size, and the formulas
are strictly layered: alternating, with an OR at the top and every literal at depth
exactly $d$. No `sorry` is used, and the build fails unless the headline theorems depend
on no oracles.

`isabelle/Bounded_Width.thy` also formalizes Remark 1 of the paper's v2. For every $k$
with $k^2 \ge n$, every symmetric function, and in particular Majority, is an OR of
$2^{O(k)}$ CNFs with clauses of width $k' = 2\lceil n/k \rceil$. For $k \le n$ this is
$2^{O(n/k')}$ CNFs. This is tight: by PPZ, any OR of width-$w$ CNFs for Majority has at least
$2^{n/(2ew)}/(n+1)$ CNFs (`majority_cnfs_lower_e` in `isabelle/Depth3_Lower.thy`). So for
$w \le 2\sqrt n$ the number of width-$w$ CNFs needed is $2^{\Theta(n/w)}$, with both directions
formal. The statement is about growing $w$. For fixed small $w$ the constants matter, and ours
are far from the best known. For $w = 3$ the bound gives about $1.043^n$, whereas
Gurumukhani, Paturi, Pudlák, Saks and Talebanfard (CCC 2024) prove $1.251^n$ for general
circuits. Gurumukhani, Kleber, Paturi, Rosin, Saks and Talebanfard
([arXiv:2601.04072](https://arxiv.org/abs/2601.04072)) determine the monotone case exactly,
$(2/6^{1/4})^{n \pm o(n)} \approx 1.278^n$. We have checked their upper bound formally:
see [`extensions/monotone-3cnf.md`](extensions/monotone-3cnf.md). The theorem holds, and six
gaps in its proof have repairs. By pigeonhole, for every $t \le n$ some $k'$-CNF in the cover accepts
only inputs of weight $t$, and accepts at least $\binom{n}{t}/2^{O(n/k')}$ of them
(`enum_output_lower_bound`). Any algorithm for the local enumeration problem
$\mathrm{Enum}(k', t)$ of Gurumukhani et al. (CCC 2024) must list all of them. So the
hypothetical algorithm with running time $2^{(1-\Omega(\log k/k))n}$ cannot exist.

A second document,
[`extensions/locality-and-monotonicity.md`](extensions/locality-and-monotonicity.md), takes
the work in new directions. It asks which restricted circuit classes can still reach
$2^{O(\sqrt n)}$. It has two parts.

The first part, `isabelle/Block_Local.thy`, records which structure the construction needs:
- **Two blocks suffice.** Every clause of those CNFs reads variables from at most two blocks
  of one of two fixed partitions into consecutive blocks of size at most $\lceil n/k \rceil$
  (`symmetric_or_of_cnfs_local`).
- **One block does not.** Consider a formula for Majority that is an OR of tests, where
  each test is an AND of subformulas that each read a single block of one fixed partition.
  It needs at least one test per block-weight vector of total weight $n/2$
  (`one_block_tests`). That is at least $(b+1)^{m/2}$ tests for $m$ blocks of size $b$
  (`one_block_tests_equal`), or $2^{\Omega(\sqrt n \log n)}$ when $b = m = \sqrt n$.

The second part asks whether the construction can be made monotone. The class it studies
is tests that are ANDs of monotone functions of two block weights. Its formal part is
`isabelle/Monotone_Pairs.thy`:
- **Theorem B** (`sharp_bounds`): with $k$ blocks of size $b$, every such test covers at
  most a $2^{k+1} (\pi b/2)^{-k/4} \sqrt{2n}$ fraction of the Majority slice. The proof is a
  block-level analogue of the PPZ satisfiability coding lemma. It improves an earlier
  $(k-1)^k b^{-k/4}$ bound (Theorem A: `pairwise_count`, `pairwise_weight`).
- **Tightness** (`matching_valid`, `matching_card`, `matching_weight`): pairing the blocks
  with complementary weights achieves $b^{-k/4}$.

`isabelle/Monotone_Cost.thy` adds two finite ingredients:
- **The cost of a test** (`clause_per_maxfalse`, `test_cost`): a monotone CNF needs one
  clause per maximal false point. So a test covering a point with a block of weight $w$
  has a pair CNF with at least $\binom{b}{w-1}$ clauses.
- **The number of tests** (`tests_needed`): covering the slice needs at least
  $\binom{kb}{kb/2}$ divided by the bound of Theorem B.

With some binomial estimates on paper, these give Theorem C: monotone formulas of this
shape need size $2^{\Theta(\sqrt{n \log n})}$.

`isabelle/Monotone_Mixed.thy` extends this to tests that mix two partitions, as the L-R
tests do:
- **Tight coordinates compress** (`tight_compress`): Theorem B's decoding works for the
  tight coordinates of any accepted weight vector, without a validity assumption.
- **Every one is in a tight block** (`mixed_tight`, `mixed_cover`): in a sound mixed test,
  each one of a covered input lies in a tight block of one of the partitions. So one
  partition compresses, and coverage stays $b^{-\Omega(k)}$.
- **Tight coordinates cost clauses** (`tight_cost`).

`isabelle/Monotone_Hyper.thy` formalizes the version for constraints that read $r$ blocks
(`hyper_compress`). It averages over colourings of the blocks instead of using a random
order and Jensen's inequality.

On paper, this gives Theorem D: monotone formulas whose tests mix $m$ partitions need
$2^{\Omega(\sqrt{n \log n / m})}$. So the construction cannot be made monotone without
changing its shape. In this shape, the negations account for the whole $\sqrt{\log n}$
saving over KPPY.

`isabelle/Monotone_Wide.thy` removes the bound on the scope when blocks are large. A test
may be any block-symmetric monotone CNF:
- **Only light blocks need decoding** (`wdec_eq`, `wfree_determined`). Unknown blocks are
  filled with the top of a typical window.
- **Light blocks are expensive** (`wide_cost`). Each typical block that a witness ties to
  the decoded one multiplies the clause count by about $2^b$.
- **The count** (`wide_cover`).

On paper, this gives Theorem E: with blocks of size at least $\sqrt n$, such formulas need
$2^{\Omega(\sqrt{n \log n})}$, however many blocks a clause reads.

`isabelle/Monotone_Kraft.thy` averages over the orders instead of choosing one per input
(`wide_kraft`, `wide_cover_kraft`). It uses a Kraft inequality for partial encodings and
Jensen's inequality, proved from $e^x \ge 1 + x$. This removes a $(2w)^k$ overhead. On
paper it gives Theorem E′: the same bound holds for blocks of size $n^{1/3+\varepsilon}$. So
the class is $2^{\Theta(\sqrt{n \log n})}$ for
$n^{1/3+\varepsilon} \le b \le \sqrt{n \log n}$.

The same argument, packaged as one lemma (`kraft_count`), also removes the $(2r)^k$
overhead from `hyper_compress` (`hyper_kraft`). So the formal ingredients of the
$2^{\Omega(\sqrt{n \log n / r})}$ bound for constraints on $r$ blocks now cover every
$r \le n^{1/5-\varepsilon}$. Before, they covered only $r \log r = o(\log n)$.

`isabelle/Monotone_Formula.thy` and `isabelle/Binomial_Estimates.thy` make the finite part
of Theorem E′ formal end to end (`majority_wide_tests`). They start from an actual formula:
an OR of block-symmetric monotone CNFs that computes Majority. The statement is: if every
test has fewer than $\beta^{w+1}$ clauses, then the number $T$ of tests satisfies

$$\log_2 T \ge \frac{k}{2ew}\left(\tfrac12 \log_2\frac{3b+2}{2} - \log_2 w - 2e\log_2 e\right) - \log_2\bigl(2(n+1)\bigr).$$

The binomial estimates are elementary: a central binomial bound, Chebyshev for block
weights, and a lower bound for the binomials in the window. In terms of the formula size
alone, with $Z = \max(z, b)$ for a formula of at most $2^z$ tests of at most $2^z$ clauses
each and $b \ge 300$ (`majority_wide_explicit`):

$$n\left(\tfrac12\log_2\frac{3b+2}{2} - \log_2\frac{3Z}{b} - 2e\log_2 e\right) \le 6e\,Z\bigl(Z + \log_2(2(n+1))\bigr).$$

Only solving this for $Z$ remains on paper.

## Contents

| Path | |
|---|---|
| `isabelle/` | Session `Majority_AC0`: 20 theories, about 7950 lines |
| `isabelle/Bounded_Width.thy` | Remark 1 (OR of narrow CNFs) and the Enum output-size bound |
| `isabelle/Block_Local.thy` | Clauses read two blocks; tests built from one-block pieces need $2^{\Omega(\sqrt n \log n)}$ |
| `isabelle/Monotone_Pairs.thy` | Monotone pairwise tests: exchange and determination lemmas, Theorems A and B (counting and weighted), tightness via matching tests |
| `isabelle/Monotone_Cost.thy` | One clause per maximal false point; the cost of a test; the number of tests needed to cover the slice |
| `isabelle/Monotone_Mixed.thy` | Tests mixing two partitions: tight coordinates compress, every one lies in a tight block, coverage of a mixed test, cost of a tight coordinate |
| `isabelle/Monotone_Hyper.thy` | Constraints on $r$ blocks: Theorem B by averaging over colourings |
| `isabelle/Monotone_Wide.thy` | Block-symmetric tests of any scope: decoding waits only for light blocks, which cost about $2^b$ clauses each |
| `isabelle/Monotone_Kraft.thy` | The counts of `Monotone_Hyper` and `Monotone_Wide` by Kraft and Jensen over all colourings, without the $(2r)^k$ and $(2w)^k$ overheads |
| `isabelle/Binomial_Estimates.thy` | Central binomial bound, slice size, Chebyshev for block weights, binomials in the window |
| `isabelle/Monotone_Formula.thy` | Theorem E′ in finite form, from a formula of block-symmetric CNF tests for Majority to an explicit bound on the number of tests |
| `isabelle/Depth3_Lower.thy` | The matching depth-3 lower bound: $\Sigma_3$ and $\Pi_3$ formulas for Majority need $2^{\Omega(\sqrt n)}$ gates (PPZ with critical clauses) |
| `isabelle/Audit.thy` | Oracle audit of the headline theorems (fails the build if any oracle is used) |
| `isabelle/gkprst/Monotone_3CNF.thy` | Session `Monotone_Sigma3`: the theorem of Gurumukhani et al. (arXiv:2601.04072), at most $6^{n/4}$ transversals of size $n/2$ in a monotone 3-CNF with no smaller transversal |
| `isabelle/gkprst/majority/` | Session `GKPRST_Majority`: hence a monotone OR of 3-CNFs for Majority needs $\binom{n}{n/2}/6^{n/4}$ CNFs, and for $4 \mid n$ at most $n+1$ times that (plus one) suffice; with an oracle audit |
| `tools/watermark.py` | Stamps Markdown files with an invisible TeX provenance line (repository, path, current commit); re-run to update |
| `control/` | Positive control: the same audit detects a `sorry` |
| `extensions/` | Beyond the paper: block locality (formalized), the monotone case (analysis), and the formal check of Gurumukhani et al. (`monotone-3cnf.md`) |
| `VERDICT.md` | The verdict, the trusted definitions, and a step-by-step correspondence with the paper |
| `writeup/main.pdf` | Short exposition, including how the formal proof differs from the paper's |

## Building

Requires [Isabelle2025-2](https://isabelle.in.tum.de/). The session depends only on
HOL-Library.

```sh
isabelle build -d isabelle Majority_AC0
isabelle build -d isabelle Monotone_Sigma3   # Gurumukhani et al., about 20 s
isabelle build -d isabelle GKPRST_Majority   # its Majority consequence and audit
isabelle build -d control Oracle_Control   # positive control for the oracle audit
```

The main session builds in a few seconds.

## Differences from the paper's proof

The argument is the paper's, but several parts were adapted to make the formalization
simpler:
- Gödel-$\beta$ moduli instead of prime powers.
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
