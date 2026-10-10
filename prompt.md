# Handoff: monotone tests for Majority, after Theorems B and C

## Context

This repo (github.com:ott2/circuitub, public) formalizes in Isabelle2025-2 the main theorem of
Lecomte–Ramakrishnan, *Optimal Shallow Circuits for Majority* (arXiv:2609.34029). That
verification is finished, and `VERDICT.md` is **frozen**: do not edit it.

We are now extending the ideas in new directions. The live document is
`extensions/locality-and-monotonicity.md`; read it first. Its formal backing:

- `isabelle/Block_Local.thy`: clauses of the L-R construction read at most two blocks.
  Tests built from one-block pieces of a fixed partition need $\ge (b+1)^{m/2}$ tests.
- `isabelle/Monotone_Pairs.thy`: the block-weight model of monotone, block-symmetric,
  pairwise tests.
  - `valid k N H`: the closure condition characterizing covered sets
    (`test_valid`, `valid_test`).
  - `exchange` and `determination`.
  - The generic counting lemma `classes`.
  - Theorem A (`pairwise_count`, `pairwise_weight`), with the $(k-1)^k$ factor.
  - **Theorem B** (`sharp_bounds`): $\lvert H\rvert \le 2^{k+1}(b+1)^{k/2}$, and the weighted form. Decode
    in a fixed order, so the witness map need not be recorded (`free_determined`). An
    order and its reverse have disjoint free sets (`free_small`).
  - The matching test, which shows tightness (`matching_valid`, `matching_card`,
    `matching_weight`).
- `isabelle/Monotone_Cost.thy`:
  - `clause_per_maxfalse` (Lemma 4).
  - `pair_cost` and `test_cost`: a sound test covering $p$ with $p_l \ge 1$ has a pair CNF
    with $\binom{b}{p_l - 1}$ clauses.
  - `tests_needed`: covering the slice needs $\binom{kb}{N}$ / (Theorem B bound) tests.
  - `boundary_cost`, `fib_card`, `inputs_count`: reusable pieces.
- `isabelle/Monotone_Mixed.thy`: tests mixing two partitions.
  - `tight`, `th`, `tfree`: tight coordinates, thresholds, and free sets, defined from the
    test's constraints.
  - `tight_compress` (Lemma 5): Theorem B for the tight coordinates of any accepted vector.
    No validity is assumed.
  - `mixed_tight` and `mixed_weight` (Lemma 6): every one lies in a tight block of one of
    the two partitions.
  - `mixed_cover`: coverage of a sound mixed test.
  - `tight_cost` (Lemma 7).
- `isabelle/Monotone_Hyper.thy`: constraints whose scopes have at most $r$ blocks.
  - `hyper`, `hacc`, `htight`, `hfree`: generic local monotone constraints, given by
    scopes `S j` and predicates `G j`.
  - `hfree_determined`: decoding needs no injectivity.
  - `good_colorings` and `average_free`: averaging over the $r^k$ colourings, Jensen-free.
  - `hyper_good`: a tight coordinate is decoded under a $(r-1)^{r-1}/r^r$ fraction of
    colourings.
  - `hyper_compress`: the count, coverage $(2r)^k (\pi b/2)^{-y/2}$ with $y \approx k/(er)$.
  - `hyper_sound_tight`, `hyper_lower_nontight`.
- `isabelle/Monotone_Wide.thy`: a test is any monotone predicate `G` of the block weights
  (a block-symmetric monotone CNF), with no scope bound.
  - `atyp` (blocks outside a window $[\mathrm{lo}, \mathrm{hi}]$), `wtight`, `wdec`, `wfree`, `wfill`.
  - `wdec_eq`, `wfree_determined`: decoding fills unknowns with `hi`, so only *light*
    coordinates (typical, with witness value below `hi`) must come earlier.
  - `max_false`, `wide_maxfalse`, `wide_cost`: a maximal false weight vector $v$ forces
    $\prod_i \binom{b}{v_i}$ clauses.
  - `wide_compress`, `wide_cover`: the count with $w$ colours, when the CNF has fewer than
    $\beta^{w+1}$ clauses.
  - `wide_good`: a tight coordinate is decoded under a $(w-1)^{w-1}/w^w$ fraction of
    colourings.
  - `wide_cnf_cost`, `wide_sound_tight`: the CNF-size and soundness steps of `wide_cover`.
  - Pitfall: `max_false[OF …]` looped in unification; instantiate with `of` first.
- `isabelle/Monotone_Kraft.thy` (imports `Complex_Main`): the same count with real weights.
  - `kraft_partial`: Kraft inequality for injective encodings into `{..<k} →E Opt`.
  - `exp_average`, `power_average`: Jensen for $\lambda^D$, from $e^x \ge 1 + x$.
  - `kraft_count`: the generic count. Given free sets `F c u` that determine `u` (`det`) and
    $t$ coordinates decoded under a $(r-1)^{r-1}/r^r$ fraction of colourings (`good`),
    $\lvert S\rvert \lambda^y \le (2^b/(1-\delta))^k$, with
    $\lambda = \delta 2^b/((1-\delta)\binom{b}{\lfloor b/2\rfloor})$ and
    $y = t(r-1)^{r-1}/r^r$.
  - Instances: `wide_kraft`, `wide_cover_kraft` (no $(2w)^k$ overhead) and `hyper_kraft`
    (no $(2r)^k$ overhead). `inputs_in` is the step from weight vectors to inputs.
  - Pitfall: `blast` looped on `∃T. T ⊆ … ∧ t ≤ card T ∧ (∀l∈T. …)`; use
    `intro exI[of _ "…"] conjI` with the named facts.
  - `free_sum` in `Monotone_Hyper` is the summed form of `average_free`.
  - Pitfalls: `o` is composition, so don't use it as a bound variable. Instantiate
    `kraft_partial` with `where enc = … and Opt = … and wo = …`.

- `isabelle/Binomial_Estimates.thy` (imports `Complex_Main` only): elementary analytic
  estimates.
  - `central_binomial`: $\binom{b}{\lfloor b/2\rfloor}^2 (3b+2) \le 2 \cdot 4^b$;
    `central_ratio`: the real form $(3b+2)/2 \le (2^b/\binom{b}{\lfloor b/2\rfloor})^2$.
  - `slice_lower`: $2^n \le (n+1)\binom{n}{\lfloor n/2\rfloor}$.
  - `binomial_moment`, `chebyshev_window`: Chebyshev for block weights, window
    $[m-d, m+d]$ with $m = \lfloor b/2\rfloor$.
  - `window_range`, `window_lower`, `window_beta`: the binomials in the window.
  - `decoded_fraction`: $(w-1)^{w-1}/w^w \ge 1/(ew)$; `one_plus_power`.
- `isabelle/Monotone_Formula.thy`: Theorem E′ from an actual formula.
  - `tw`, `tw_mono`, `tw_cnf`, `tw_sound`: a block-symmetric monotone CNF as a monotone
    predicate on weight vectors (the up-closure; `sub_with_weights` realizes smaller
    weights inside an input).
  - `formula_kraft`: `wide_cover_kraft` summed over the tests of a threshold formula.
  - `atypical_count`, `typical_half`: half the slice has at most $k/2$ atypical blocks.
  - `majority_wide_tests`: the explicit bound
    $\log_2 T \ge \frac{k}{2ew}(\frac12\log_2\frac{3b+2}{2} - \log_2 w - 2e\log_2 e) - \log_2(2(n+1))$.
  - Pitfalls met: simp unfolds `Suc n choose Suc k` (`binomial_Suc_Suc`) and pushes `int`
    or `real` through sums before your rewrite fires; use `unfolding` first, then
    `simp only: ac_simps`. For nonlinear cancellations, AC-normalize to atoms and use
    `linarith`. Give `log_mono` and `mult_left_mono` explicitly rather than via simp.

- `isabelle/Depth3_Lower.thy`: the matching depth-3 lower bound for Majority.
  - `lv`, `csat`, `forced`: points are subsets of `{..<n}`, a CNF is a set of literal sets,
    and coordinate `i` is forced in the order `p` if a clause has every other literal false
    and earlier (and `i` with one sign only).
  - `forced_kraft`: $\sum_X 2^{\#\mathrm{forced}} \le 2^n$, via disjoint cylinders
    (`cyl_disjoint`: at the first coordinate where two points differ, both forced and
    unforced lead to a contradiction). No injectivity of `p` is needed, so colourings serve
    as orders directly.
  - `ppz_count`: narrow critical clauses, averaged over colourings with `good_colorings`,
    `free_sum` and `power_average`. `crit_count`: a clause with $w$ other variables is
    critical for at most $2^{n-w-1}$ points.
  - `sigma3_slice` (sets of CNFs), `sigma3_threshold` (formulas, any threshold),
    `majority_slices` (Σ3 directly; Π3 via `dual` and `cflip`, which complements the
    variables below $n$), `majority_depth3_lower` (explicit in $r$), and
    `majority_depth3_sqrt`: $2^{\sqrt n/4} \le (n+1)(n+2)\cdot\mathrm{gates}$.
  - Pitfalls met: blast/fastforce loop on `pi_Suc_And`/`sig_Suc_Or` unfolding and on
    disjointness goals; obtain the witness explicitly. To keep casts of products intact use
    `simp only: of_nat_le_iff of_nat_mult[symmetric]`. There is no `exp 1 ≤ 3` in the
    library; `exp_one_le_4` is proved from $e^{-1/2} \ge 1/2$.

The session is `Majority_AC0` (20 theories, ~7950 lines). `isabelle/Audit.thy` lists every
headline theorem and fails the build if any depends on an oracle. Add new headline
theorems there.

Literature summaries written by subagents are in `notes/summaries/`, which is git-ignored
and kept uncommitted.

## State of the mathematics

- **Conjecture Q is proved** (Theorem B, with $C \approx 1.79$).
- **Theorem C** (pen and paper, from the formal ingredients): monotone $\Sigma_3$ formulas
  for Majority whose tests are ANDs of block-symmetric pair functions over one partition
  have size $2^{\Theta(\sqrt{n \log n})}$. The upper bound is KPPY-style matching tests. So
  in the L-R shape, negations account for the whole $\sqrt{\log n}$ saving.
- **Widening (§2.7, pen and paper):**
  - Each test may use its own partition.
  - Constraints on $r$ blocks give $2^{\Omega(\sqrt{n \log n / r})}$.
  - Block symmetry cannot simply be dropped.
- **Mixed partitions (§2.8):**
  - A sound test mixing two partitions still covers only $b^{-\Omega(k)}$ of the slice
    (`mixed_cover`, formal).
  - **Theorem D** (pen and paper): if tests mix $m$ partitions, the size is
    $2^{\Omega(\sqrt{n \log n / m})}$. So the L-R shape ($m = 2$) without negations is
    $2^{\Theta(\sqrt{n \log n})}$.
- **Unbounded scope (§2.9):** **Theorem E** (pen and paper, from `wide_cover`): if every
  test is a block-symmetric monotone CNF with blocks of size $b \ge \sqrt n$, the size is
  $2^{\Omega(\sqrt{n \log n})}$, whatever the scopes.
- **Theorem E′** (pen and paper, from `wide_cover_kraft`): the same for $b \ge n^\alpha$,
  $\alpha > 1/3$, with exponent $\Omega(\sqrt{(3\alpha-1)\, n \log n})$. With groups of whole
  blocks, KPPY is in the class, so it is $2^{\Theta(\sqrt{n \log n})}$ for
  $n^{1/3+\varepsilon} \le b \le \sqrt{n \log n}$. The argument breaks even at
  $b \approx (n \log n)^{1/3}$: a decoded block saves $\frac12 \log b$ bits, and locating it
  costs $\log w \approx \log(\sqrt n/b)$ bits.
- **Theorem E′, finite part, is formal** (`majority_wide_tests`). The side conditions it makes
  explicit are $2(n+1) \le 2^k$, $w\binom{b}{\lfloor b/2\rfloor} \le 2^b$ ($\lambda \ge 1$),
  and a window $[m-d, m+d] \subseteq [2, b-2]$ with $d^2 \ge 4b$. All hold in the regime of
  the paper's contradiction argument. Only the step $w \le z/\log_2\beta + 1$ and the
  optimization over $n$ remain on paper.
- **The depth-3 lower bound is formal** (`majority_depth3_sqrt`): so the paper's optimality
  claim is checked at depth 3, and depth-3 Majority is $2^{\Theta(\sqrt n)}$ in Isabelle.
  `ppz_count` also covers the small-$b$ case of Theorem C, with a factor $e$ lost to
  colourings.
- **Errors found so far by formalizing:** the documents said `hyper_compress` has exponent
  $k/(4er)$; it is $k/(2er)$. Nothing wrong was found in Theorem E′.

## Suggested next steps (§2.10 of the document)

1. **Small blocks with wide constraints, or many partitions.** For $b = 1$ the class is
   everything, so this is the general open monotone question. Theorems E and E′ settle
   $b \ge n^{1/3+\varepsilon}$. The natural target is the gap between $b \approx n^{1/3}$ and
   $b = 1$. It needs a cheaper way to locate decodable blocks, or a different exchange rate.
2. **Sharper constants for $r$-block constraints:** `hyper_kraft` removed the $(2r)^k$
   overhead, so the formal ingredients cover $r \le n^{1/5-\varepsilon}$. The exponent is
   still $k(1-1/r)^{r-1}/(2r)$ rather than $k/(2r)$. Getting rid of the factor
   $(1-1/r)^{r-1}$ needs random orders (permutations) instead of colourings in `free_sum`.
3. **The analytic rest:** Theorem E′ is done up to the optimization over $n$. An
   explicit-constant corollary for fixed $\alpha$ (choose $w = \lfloor z/\log_2\beta\rfloor + 1$,
   use `window_beta`) would close it. For Theorems C and D, `chebyshev_window` and
   `central_binomial` replace Hoeffding and $\sqrt{\pi b/2}$, and `ppz_count` is the small-$b$
   case. Still missing: the cheap-test split.
4. **The fixed-point form** (§2.3).

## Working rules

The user's preferences are also stored in Claude memory.

- **Building:** `.venv/bin/isabelle-build -m "diagnosis: …; change: …; expect: ok|fail — why"`
  with `WALL_TIMEOUT=60 WATCHDOG_TIMEOUT=20`.
  - Do not pipe the output through `tail`.
  - Full errors: `sed -n '/full error/,$p' t/logs/last-build.log`.
  - Slow commands: `grep "running for" t/logs/last-build.log`.
  - Sorry check: `.venv/bin/isabelle-query -R isabelle sorry`.
- **Proof style:** no exhaustive or brute-force searches (Python or otherwise) to test
  circuit claims. Prove by hand, then formalize.
- **Tool use:** Edit/Write for file changes, simple one-line Bash, nothing in `/tmp`.
- **Isabelle pitfalls met so far:**
  - Annotate types of existentially bound functions and of index variables, e.g.
    `fixes k :: nat`, when nothing else forces them.
  - `finite_subset by blast` and `auto` with maximality facts can loop; use
    `by (rule finite_subset) simp` and explicit facts.
  - Avoid `auto dest: PiE_mem` and guessed `metis` calls; they looped.
  - Supply higher-order instances explicitly with `spec[OF …, of "λw. …"]`.
  - `rule_format` reorders variables.
- **Git:**
  - Commit every verified step without asking. Push only when the user says so.
  - End commit messages with `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.
  - Never stage `scrub-*.sh`, `notes/`, `paper-v2/`, the root PDFs, or `*.bib` files.
  - History rewrites are done by the user, not by you.
- **Summaries:** subagent paper summaries go to `notes/summaries/`, uncommitted.
- **Writing:** the user's pronouns are not stated; use they/them.
- **Mathematics in Markdown:** use `$…$` and `$$…$$` TeX, which GitHub renders, not
  hand-rolled Unicode notation. In tables write `\lvert…\rvert` instead of `|`. Use
  `\lbrace`/`\rbrace` for set braces. `VERDICT.md` stays as it is (frozen).
