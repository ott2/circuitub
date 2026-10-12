# Handoff: formalizing Gurumukhani et al., monotone Σ₃³ for Majority (arXiv:2601.04072)

## The task, and where it stands

Formalize in Isabelle the main theorem of Gurumukhani, Kleber, Paturi, Rosin, Saks and
Talebanfard, *Optimal Monotone Depth-Three Circuit Lower Bounds for Majority*
(arXiv:2601.04072v2). As with the Lecomte–Ramakrishnan verification below, the point is to
check a recent proof formally and report any gaps.

**Claim.** A monotone 3-CNF with no transversal of size $< n/2$ has at most $6^{n/4}$
transversals of size $\lfloor n/2\rfloor$. Hence a monotone OR of 3-CNFs computing Majority
needs $\binom{n}{n/2}/6^{n/4} \approx 1.278^{n-o(n)}$ CNFs. The paper writes $n = 3t - s$
and proves $N_i(s,t) \le c_i(2/3)^{s/2}3^t$ (even $s$) or $c'_i(2/3)^{(s-1)/2}3^t$ (odd $s$),
for six families $i$, by an induction that uses 58 branching tables.

**Sources** (none of these may be staged):
- LaTeX: `notes/gkprst26-src/`.
- PDF: `2601.04072v2.pdf`.
- Summary: `notes/summaries/2601.04072-GKPRST26.md`.
- Ignore `archive/` directories.
- Map of the sources:
  - `UpperBounds/upperbounds.tex`: the theorem and the outline.
  - `upper-bound-head.tex`: the configurations.
  - The cases: `phi0.tex`, `oneclause/phi1.tex`, `twooverlapping/phi2o.tex` (17 tables),
    `twodisjoint/phi2d.tex` (8), `threeclause/*.tex` (23).
  - The property macros are in `setup/cases.tex`.

**Findings so far** are in `gkprst26/NOTES.md` (committed); keep it up to date.
- The main one is **a gap in P0.4 (triangle)**: the table omits $a=b=c=0$. The prism is a
  counterexample to the table's coverage.
- The repair: $d,e,f$ are distinct because P0.3 fails, so three rows fix 5 variables, not 4.
  With the missing row added the sums are $103/108$ and $1$.
- Everything else checked so far is correct, apart from some unnecessary assumptions.

### The formal development: `isabelle/gkprst/Monotone_3CNF.thy`

The session is **`Monotone_Sigma3`**, in `isabelle/ROOT` as `in "gkprst"`, with parent
`HOL-Library`, so it is separate from `Majority_AC0`. Build with:

    WALL_TIMEOUT=60 WATCHDOG_TIMEOUT=20 .venv/bin/isabelle-build --session Monotone_Sigma3 -m "…"

It currently takes about 6 s. There is no `sorry`.

- **Definitions.**
  - `cnf V F`: clauses $\subseteq V$, of size $\le 3$, $V$ finite.
  - `hits F X`.
  - `trans V F t`: the $t$-transversals.
  - `thr V F t`: no smaller transversal.
  - `restr F J E = (λC. C - E) ` {C∈F. C ∩ J = {}}`: $J$ set to 1, $E$ set to 0.
  - `twos F`: the 2-clauses.
  - `npair F`: no pair of variables in 3 clauses.
  - `datatype fam = T0 | T1 | T2o | T2d | T3 | T4`, with `infam`. For T3, "no three
    2-clauses share a variable" is `card {C∈twos F. x ∈ C} ≤ 2`.
  - `coef`, `bound i s t = coef i (even s) * (2/3) powi (s div 2) * 3^t` (with `s :: int`), and
    `ratio k j e i p`, the closed-form ratio for a row with $j$ ones, $e$ zeros and restricted
    family $k$ (lemma `bound_shift`).
  - `bound_mono`: the bound decreases in $s$.
- **Induction.**
  - `IH m`: the bound holds for every CNF with fewer than $m$ variables, in family $i$
    **or with a clause of size $\le 1$**. That disjunct absorbs restrictions that create
    1-clauses.
  - The induction is on $\lvert V\rvert$ alone; every row fixes a variable.
- **`locale core V F t`.** Assumptions: `cnf`, `thr`, `IH (card V)`, every clause has size
  2 or 3, an antichain (`anti`), `⋃F = V`, `1 ≤ t`. It provides `s`, `critical` (the critical
  clause), `row`, and **`table`**.
- **`locale core0 = core +`** every clause has size 3. All type-0 tables live here.
- **How to state a table** (copy `p05` or `p06_both`):

      proof (rule table[where rs = "[({J…},{E…},Tk), …]"], goal_cases)
        case 1: rows_ok    — restricted families via two_mem / del_two / infam_2d, npair_restr
        case 2: coverage   — prove a disjunction of literal facts (a ∈ X ∧ b ∉ X ∨ …) for
                             X ∈ trans V F t, then `show ?case by auto`
        case 3: the sum    — `by (cases "even s") (simp_all add: ratio_simps)`

  Coverage helpers:
  - `hit`.
  - `forced_out`: $a$ always with $b$ forces $b \notin X$.
  - `two_only`: degree $\le 2$ means the clauses of $x$ are exactly $C_1, C_2$.
  - `crit_other` / `crit_other'` / `crit_excl`: the other clause is critical, so its other
    two variables are out.
  - `only_clause`, `single_out`, `excl3`.
  - Configuration extraction: `three_form`, `card2_obtain`, `card3_obtain`.
- **Done (type 0):** `p01` (from `¬ npair F`; uses `p01_with`, `p01_sep`), `p02` (uses
  `del_type3`), `p03`, `p04` (corrected), `p05`, `p06_both`, `p06_one`, and the coverage
  theorem `type0` (uses `three_elems`, `tri`, `meet_tri`).

### Next steps, in order

1. **Done:** the type-0 coverage lemma, `theorem type0` (in `core0`): `bound T0 s t`. The
   formal version follows this plan exactly:
   - `¬ npair` → `p01`.
   - Some $a$ in $\ge 3$ clauses → `p02`.
   - A pair in two clauses → `p03`. Extract with `card2_obtain` and `three_form`.
   - Otherwise every variable is in $\le 2$ clauses and every pair in $\le 1$ clause. Prove
     `meet_tri`: if $\lbrace a,b,c\rbrace \in F$, $D_1 \ni b$, $D_2 \ni c$ are other clauses
     and $D_1 \cap D_2 \ne \emptyset$, then a triangle with 6 distinct variables exists. Write
     $D_1 = \lbrace b,x,u\rbrace$, $D_2 = \lbrace c,x,v\rbrace$; the triangle is $(b,c,x)$ with
     $d=a$, $e=v$, $f=u$. ($u \ne v$ by the pair condition.) If a triangle exists → `p04`.
   - Otherwise, if some variable lies in exactly one clause $\lbrace a,b,c\rbrace$: if $b$ and
     $c$ both lie in other clauses, these are disjoint by `meet_tri`, giving `p06_both`;
     otherwise `p06_one`, swapping $b$ and $c$ if needed.
   - Else every variable is in exactly 2 clauses ($F \ne \emptyset$ since $t \ge 1$). Take any
     clause; its three other clauses are pairwise disjoint by `meet_tri`, giving an E
     configuration → `p05`.
2. **Done:** type 1 (`phi1.tex`, 2 tables): `p11`, `p12`, and `theorem type1` (in `core`,
   with the hypothesis `infam T1 F`).
   - In P1.2, $a$'s second clause may be a 2-clause $\lbrace a,c\rbrace$. Then the restriction
     has the 1-clause $\lbrace c\rbrace$, which is covered by the size-$\le 1$ disjunct.
3. **Types 2o, 2d, 3, 4** (48 tables). **2d and 2o are done.**
   - `theorem type2d` assumes `¬ infam T2o F`.
   - `theorem type2o` assumes `¬ infam T3 F` and `¬ infam T4 F`.
   - Both have coverage gaps, now repaired; see NOTES.md.
   - **Types 3 and 4 are done too** (`theorem type3`, `theorem type4`, which uses `type3`).
     So all six families have formal tables and coverage. At each $n$ the order is 3, 4, 2o,
     2d, 1, 0.
   - The gaps found are listed in NOTES.md:
     - P0.4;
     - P2d coverage;
     - P2o coverage;
     - P3p.1 (a wrong table);
     - P3ie.2;
     - type 4 for even $s$. Rows may use dominated families (`fam_ok`,
   `t3_or_t4`, `infam_2`); state the rows with `rows_ok_ConsI`. Read each table's prose
   coverage claim critically. The likely errors:
   - coverage;
   - the family of each restricted CNF (`npair` is inherited by `npair_restr`; "no 3
     two-clauses with a common variable" is *not* inherited);
   - variables that may coincide ($n'$ uncertain: use `bound_mono`);
   - 1-clauses.
   Commit after each verified table.
4. **The reductions and main theorem**, by strong induction on `card V`:
   - $t = 0$: count $\le 1$, and 0 outside T0.
   - An empty clause gives 0. A 1-clause: force it, giving $\le \tfrac12$ `bound T0`
     $\le$ `bound i`.
   - Remove subsumed clauses (same $V$; family preserved).
   - Remove unused variables (via `bound_mono`).
   - At a fixed $n$, prove the families with 2-clauses before T0. A T0 CNF with a 2-clause
     uses the T1 bound, since `bound T1 ≤ bound T0`.
5. **Corollary** with $s = t = \lfloor n/2\rfloor$: $6^{n/4}$. Then the Majority size bound.
   `slice_lower` lives in `Majority_AC0`, so put the corollary in a theory or session that
   can import both.
   - Add the headline theorems to an audit, as `Audit.thy` does.
6. Keep `gkprst26/NOTES.md` current. Never edit `VERDICT.md`.

Prove by hand, then formalize. No brute-force or exhaustive search.

### Proof-engineering hints

They are in memory (`ndtht-isabelle-tips.md`) and in `~/projects/watchdog/docs/proof-hints.md`.
Before a second tactic attempt, search `~/projects/ndtht/bin/kb KEYWORD`. The ones that
mattered most here:
- Give automation literal facts, never set equations.
- Use `rule …[OF …]`, not guessed `metis`/`elim`.
- `simp` won't flip $a \ne c$ into $c \ne a$; use `auto` for such side goals.
- No `case_prod` bounded quantifiers.
- Give `finite_subset[OF …]` explicitly.
- Keep `moreover` chains contiguous.
- Act on the build summary; read the full log only when the summary truncates what is
  needed.

### Left uncommitted in other repos (the user's call)

- `~/projects/ndtht/insights/361.md`: a `have` breaking a `moreover` chain.
- `~/projects/ndtht/insights/362.md`: negative `powi`.
- `~/projects/watchdog/docs/proof-hints.md`.

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
