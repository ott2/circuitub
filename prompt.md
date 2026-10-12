# Handoff: formalizing Gurumukhani et al., monotone Σ₃³ for Majority (arXiv:2601.04072)

## The task, and where it stands

The task is to formalize in Isabelle the main theorem of Gurumukhani, Kleber, Paturi, Rosin,
Saks and Talebanfard, *Optimal Monotone Depth-Three Circuit Lower Bounds for Majority*
(arXiv:2601.04072v2). The point is to check a recent proof formally and report any gaps, as
with the Lecomte–Ramakrishnan verification described below.

**Status: the paper's main theorem is formally proved, with no `sorry`.** Two results:

- **`theorem gkprst_bound`.** Let $F$ be a monotone CNF over $V$ with clauses of size
  $\le 3$, with no transversal of size $< t$, and let $s = 3t-n$. Then $F$ has at most
  `bound T0 s t` transversals of size $t$: $(2/3)^{s/2}3^t$ for even $s$, and
  $\tfrac79(2/3)^{(s-1)/2}3^t$ for odd $s$.
- **`corollary gkprst_half`.** For $n = 2t$ the bound is at most $6^{n/4}$.
- **`theorem majority_mcnfs`** (session `GKPRST_Majority`). A monotone OR of 3-CNFs for
  Majority on even $n$ needs $\binom{n}{n/2}/6^{n/4}$ CNFs. All are oracle-audited.

**The paper's proof has six genuine gaps.** Each is repaired within the same induction,
and no constant changes. The details, with counterexamples, are in `gkprst26/NOTES.md`
(committed); keep it current.

1. **P0.4:** the table misses the row $a=b=c=0$ (the prism is a counterexample).
2. **2d coverage:** it misses CNFs in which $a$'s and $b$'s further clauses are 2-clauses.
   The repair is to prove 2o first and assume $\neg$2o.
3. **2o coverage:** it misses the case where $b$ and $c$ share one clause and $c$ has no other
   clause. The repair is a new table, `p2o5_gap`, with sum exactly 1.
4. **P3p.1:** the table is wrong. Its claim "$a=1$ forces $b=0$" fails, for example in
   $\lbrace ab,bc,cd,axy,duv\rbrace$. The repair is to split on $c$; the sum is 1.
5. **P3ie.2:** a claimed type-1 row is only of type 0 in two subcases (sum $43/42$). The
   repairs are a type-2o row (`p3i_e3a`, `p3i_e3b`) and the new table `p3i_eG`.
6. **Type 4 for even $s$:** stars (a variable in three or more 2-clauses) are not covered.
   The repair is two new tables, `p4_e4` and `p4_e3`.

The paper also has many unnecessary assumptions and over-complicated case splits; they are
listed in NOTES.md.

**Sources** (none of these may be staged): the LaTeX is in `notes/gkprst26-src/`
(the cases are under `UpperBounds/`), the PDF is `2601.04072v2.pdf`, and the summary is
`notes/summaries/2601.04072-GKPRST26.md`.

### The formal development: `isabelle/gkprst/Monotone_3CNF.thy` (about 5,400 lines)

The session is **`Monotone_Sigma3`**, declared in `isabelle/ROOT` as `in "gkprst"` with parent
`HOL-Library`. The theory imports only `Complex_Main`. Build with:

    WALL_TIMEOUT=120 WATCHDOG_TIMEOUT=30 .venv/bin/isabelle-build --session Monotone_Sigma3 -m "…"

It takes about 15–20 s. If another session's build loads the machine (`uptime` shows load
around 15), raise the limits instead of hunting for a slow step.

**Structure:**
- **Definitions.**
  - `cnf V F`: every clause is a subset of $V$ of size $\le 3$, and $V$ is finite.
  - `hits F X`: $X$ meets every clause of $F$.
  - `trans V F t`: the transversals of size $t$.
  - `thr V F t`: no transversal of size $< t$.
  - `restr F J E`: the CNF with $J$ set to 1 and $E$ set to 0.
  - `twos F`: the 2-clauses.
  - `npair F`: no pair of variables lies in three clauses.
  - `fam`: the families $T0 | T1 | T2o | T2d | T3 | T4$, with membership `infam`.
  - The bounds: `coef`, `bound`, `ratio`, and the lemma `bound_shift`.
- **Domination.**
  - `fam_le k' k`: the bound for $k'$ is at most that for $k$. The families form a chain,
    $4 \le 3 \le 2o \le 2d \le 1 \le 0$.
  - `fam_ok k G`: $G$ is in family $k$, has a clause of size $\le 1$, or is in a family
    dominated by $k$.
- **The induction hypothesis** `IH m` quantifies over every CNF with fewer than $m$
  variables, in any family or with a clause of size $\le 1$.
- **`locale core`** collects the normalized situation: every clause has 2 or 3 variables, no
  clause contains another, every variable occurs in some clause, $t \ge 1$, and `IH (card V)`
  holds. It provides `table` (rows `(J,E,family)`), `rows_ok_ConsI`, and the critical-clause
  helpers.
- **`locale core0`** adds that every clause has 3 variables (type 0).
- **The coverage theorems**, one per family:
  - `type0` (in `core0`) and `type1`;
  - `type2o`, which assumes $\neg$T3 and $\neg$T4;
  - `type2d`, which assumes $\neg$2o;
  - `type3`, and `type4`, which uses `type3`.
- **Combining them.** `full2o` and `full2d` handle the dominating families, and `full_bound`
  combines everything.
- **The reductions** (`step`):
  - $t=0$;
  - an empty clause;
  - a 1-clause, which is forced;
  - subsumed clauses, by keeping only the minimal clauses;
  - unused variables.
- **`IH_all`, then `gkprst_bound` and `gkprst_half`.**

### The Majority bound and the audit (done)

Session **`GKPRST_Majority`** (`isabelle/gkprst/majority/`, parent `Majority_AC0`, with
`sessions Monotone_Sigma3`). It needs its own directory, because Isabelle rejects two
sessions sharing one. Build it with `--session GKPRST_Majority`, in about 20 s once the
`Majority_AC0` heap exists.
- **`Majority_3CNF.thy`:**
  - `MCNF w f`: an AND of ORs of at most $w$ positive literals.
  - `pclause`, `pcnf`: the clause sets restricted below $n$.
  - `eval_pcnf`, the bridge to `hits`, and `pcnf_cnf`.
  - `majority_mcnfs`: $\binom{n}{n/2} \le L \cdot 6^{n/4}$ for even $n$.
  - `majority_mcnfs_exp`: $(2/6^{1/4})^n \le (n+1)L$.
  - `majority_mcnf_formula`: both bounds with the gates of `Or gs`.
- **`Audit_GKPRST.thy`:** the oracle check for `gkprst_bound`, `gkprst_half`, `IH_all` and
  the three Majority theorems. The `type*` theorems are local to the locales, so they have
  no global names; they are covered through `gkprst_bound`.

### Next steps

1. **Done: odd $n$ and the matching upper bound.**
   - `gkprst_half_odd` and `majority_mcnfs_odd`/`_any`/`_exp_any` handle odd $n$.
   - `Majority_3CNF_Upper.thy` gives $L \le (n+1)\binom{n}{n/2}/6^{n/4}+1$ for $4 \mid n$
     (`majority_mcnfs_upper`), with the two-sided `majority_mcnfs_tight`. Its main lemma,
     `threshold_cover`, works for any threshold CNF.
   - Open there: the other residues of $n$ mod 4, which need the paper's other extremal blocks.
   - The audit is one long `ML` command, and under heavy machine load it trips the watchdog's
     loop heuristic. Use `LOOP_PROGRESS_THRESHOLD=20` then; it is not a loop.
2. **The writeup is drafted:** `gkprst26/gaps-for-authors.md`. Every counterexample and every
   repaired table was re-checked by hand against the paper's LaTeX. Ask the user before
   sending anything externally.
3. **Watermarks.** Run `tools/watermark.py FILE.md …` to restamp documents with the current
   commit, and use `--check` to see what would change. Never run it on `VERDICT.md`.
4. Then return to the open directions below. For example, monotone $\Sigma_3^k$ for $k \ge 4$
   (§2.10, item 5).

Prove by hand, then formalize. No brute-force or exhaustive search.

### Proof-engineering hints

The full list is in memory (`ndtht-isabelle-tips.md`) and in
`~/projects/watchdog/docs/proof-hints.md`. Before a second tactic attempt, search
`~/projects/ndtht/bin/kb KEYWORD`. The ones that mattered most here:

- Give automation literal facts, never set equations. This includes equations like
  $\lbrace a,b\rbrace = \lbrace b,a\rbrace$, and equations chained in through `then`.
- Use `rule …[OF …]`, never a guessed `metis`. Consume `obtains` lemmas with `rule` on an
  explicit instance, not `blast`.
- `OF` cannot fill a `⋀x. … ⟹ False` premise with a rule-shaped fact (insights/116).
  Pass plain `∀…` or `¬(∃…)` formulas instead.
- After `rule X[OF …]` with rule-shaped facts in the `OF`, pass the remaining facts by name
  in the `OF` too; chaining them in fails.
- Inside `obtain … using …`, `that` means the obtain's own continuation. Name the `have … if`
  assumptions.
- `simp` won't flip $a \ne c$ into $c \ne a$, so give it flipped facts. For example,
  `card {c,b}` needs `c ≠ b`.
- `rule two_mem[OF K(1)] two_mem[OF K(2)]` always picks the first rule. Write one subgoal
  per rule.
- Act on the build summary; when a step loops, check `grep "running for"` in the log.

### Documents

- **The results document is `extensions/monotone-3cnf.md`.** It is linked from `README.md` and
  from §2.1 of `extensions/locality-and-monotonicity.md`. Update it as work lands; for
  example, move the Majority bound and the audit to "formal" when they are done.
- GitHub's math renderer rejects `\operatorname`. Use `\mathrm`, or `\mathbin{\mathrm{…}}`
  for binary operators. Write braces as `\lbrace`/`\rbrace`.
- The ndtht insights and the watchdog proof hints have been taken up by those projects.

Uncommitted, by design: `notes/summaries/chukhin-tr26-248.md` (a hand-checked summary of
ECCC TR26-248).

## Background: the previous work (Lecomte–Ramakrishnan and its extensions)

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
  the paper's contradiction argument. The step to the formula size is formal too
  (`majority_wide_size`; `majority_wide_explicit` for $b \ge 300$, with $Z = \max(z,b)$:
  $n(\frac12\log_2\frac{3b+2}{2} - \log_2\frac{3Z}{b} - 2e\log_2 e) \le 6eZ(Z + \log_2(2(n+1)))$).
  Only solving this for $Z$ remains on paper; it gives the constant $(3\alpha-1)/(12e)$.
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
3. **The analytic rest:** Theorem E′ is formal up to solving one explicit quadratic
   inequality (`majority_wide_explicit`). For Theorems C and D, `chebyshev_window` and
   `central_binomial` replace Hoeffding and $\sqrt{\pi b/2}$, and `ppz_count` is the small-$b$
   case. Still missing: the cheap-test split.
4. **The fixed-point form** (§2.3).
5. **Monotone $\Sigma_3^k$ for $k \ge 4$ (open, per the literature check in
   `notes/summaries/depth3-thresholds-and-monotone-k.md`).** Only $k = 2$ and monotone $k = 3$
   (GKPRST26) are settled. The conjecture $2^{\Omega(n\log k/k)}$, i.e. that a monotone $k$-CNF
   with no satisfying point below weight $n/2$ accepts at most $2^n k^{-\Omega(n/k)}$ points
   of weight $n/2$, would give monotone depth-3 Majority $\ge 2^{\Omega(\sqrt{n\log n})}$:
   a monotone/non-monotone separation at depth 3, given L-R. PPZ (`ppz_count`) loses the
   $\log k$ factor even on the extremal block example (blocks of $2k-2$, all $k$-sets): it
   saves 1 bit per block where the truth is $\frac12\log_2 k$. Theorem B's block decoding is
   the analogue that does gain $\frac12\log b$.

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
