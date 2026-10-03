# Handoff: monotone tests for Majority, after Theorems B and C

## Context

This repo (github.com:ott2/circuitub, public) formalizes in Isabelle2025-2 the main theorem of
Lecomte–Ramakrishnan, *Optimal Shallow Circuits for Majority* (arXiv:2609.34029). That
verification is finished, and `VERDICT.md` is **frozen**: do not edit it.

We are now extending the ideas in new directions. The live document is
`extensions/locality-and-monotonicity.md`; read it first. Its formal backing:

- `isabelle/Block_Local.thy`: clauses of the L-R construction read at most two blocks.
  Tests built from one-block pieces of a fixed partition need ≥ (b+1)^{m/2} tests.
- `isabelle/Monotone_Pairs.thy`: the block-weight model of monotone, block-symmetric,
  pairwise tests.
  - `valid k N H`: the closure condition characterizing covered sets
    (`test_valid`, `valid_test`).
  - `exchange` and `determination`.
  - The generic counting lemma `classes`.
  - Theorem A (`pairwise_count`, `pairwise_weight`), with the (k−1)^k factor.
  - **Theorem B** (`sharp_bounds`): |H| ≤ 2^{k+1}(b+1)^{k/2}, and the weighted form. Decode
    in a fixed order, so the witness map need not be recorded (`free_determined`). An
    order and its reverse have disjoint free sets (`free_small`).
  - The matching test, which shows tightness (`matching_valid`, `matching_card`,
    `matching_weight`).
- `isabelle/Monotone_Cost.thy`:
  - `clause_per_maxfalse` (Lemma 4).
  - `pair_cost` and `test_cost`: a sound test covering p with p_l ≥ 1 has a pair CNF with
    C(b, p_l − 1) clauses.
  - `tests_needed`: covering the slice needs C(kb, N) / (Theorem B bound) tests.
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
- `isabelle/Monotone_Hyper.thy`: constraints whose scopes have at most r blocks.
  - `hyper`, `hacc`, `htight`, `hfree`: generic local monotone constraints, given by
    scopes `S j` and predicates `G j`.
  - `hfree_determined`: decoding needs no injectivity.
  - `good_colorings` and `average_free`: averaging over the r^k colourings, Jensen-free.
  - `hyper_compress`: the count, with exponent about k/(4er).
  - `hyper_sound_tight`, `hyper_lower_nontight`.
- `isabelle/Monotone_Wide.thy`: a test is any monotone predicate `G` of the block weights
  (a block-symmetric monotone CNF), with no scope bound.
  - `atyp` (blocks outside a window [lo, hi]), `wtight`, `wdec`, `wfree`, `wfill`.
  - `wdec_eq`, `wfree_determined`: decoding fills unknowns with `hi`, so only *light*
    coordinates (typical, with witness value below `hi`) must come earlier.
  - `max_false`, `wide_maxfalse`, `wide_cost`: a maximal false weight vector v forces
    ∏ C(b, v_i) clauses.
  - `wide_compress`, `wide_cover`: the count with w colours, when the CNF has fewer than
    β^(w+1) clauses.
  - `wide_good`: a tight coordinate is decoded under a (w−1)^{w−1}/w^w fraction of colourings.
  - `wide_cnf_cost`, `wide_sound_tight`: the CNF-size and soundness steps of `wide_cover`.
  - Pitfall: `max_false[OF …]` looped in unification; instantiate with `of` first.
- `isabelle/Monotone_Kraft.thy` (imports `Complex_Main`): the same count with real weights.
  - `kraft_partial`: Kraft inequality for injective encodings into {..<k} →E Opt.
  - `exp_average`, `power_average`: Jensen for λ^D, from exp x ≥ 1 + x.
  - `wide_kraft`, `wide_cover_kraft`: #S · λ^y ≤ (2^b/(1−δ))^k, with
    λ = δ2^b/((1−δ)C(b,b/2)). There is no (2w)^k overhead.
  - `free_sum` in `Monotone_Hyper` is the summed form of `average_free`.
  - Pitfalls: `o` is composition, so don't use it as a bound variable. Instantiate
    `kraft_partial` with `where enc = … and Opt = … and wo = …`.

The session is `Majority_AC0` (17 theories, ~6100 lines). `isabelle/Audit.thy` lists every
headline theorem and fails the build if any depends on an oracle. Add new headline
theorems there.

Literature summaries written by subagents are in `notes/summaries/`, which is git-ignored
and kept uncommitted.

## State of the mathematics

- **Conjecture Q is proved** (Theorem B, with C ≈ 1.79).
- **Theorem C** (pen and paper, from the formal ingredients): monotone Σ₃ formulas for
  Majority whose tests are ANDs of block-symmetric pair functions over one partition have
  size 2^{Θ(√(n log n))}. The upper bound is KPPY-style matching tests. So in the L-R
  shape, negations account for the whole √(log n) saving.
- **Widening (§2.7, pen and paper):**
  - Each test may use its own partition.
  - Constraints on r blocks give 2^{Ω(√(n log n / r))}.
  - Block symmetry cannot simply be dropped.
- **Mixed partitions (§2.8):**
  - A sound test mixing two partitions still covers only b^{−Ω(k)} of the slice
    (`mixed_cover`, formal).
  - **Theorem D** (pen and paper): if tests mix m partitions, the size is
    2^{Ω(√(n log n / m))}. So the L-R shape (m = 2) without negations is
    2^{Θ(√(n log n))}.
- **Unbounded scope (§2.9):** **Theorem E** (pen and paper, from `wide_cover`): if every
  test is a block-symmetric monotone CNF with blocks of size b ≥ √n, the size is
  2^{Ω(√(n log n))}, whatever the scopes.
- **Theorem E′** (pen and paper, from `wide_cover_kraft`): the same for b ≥ n^α, α > 1/3,
  with exponent Ω(√((3α−1) n log n)). With groups of whole blocks, KPPY is in the class, so
  it is 2^{Θ(√(n log n))} for n^{1/3+ε} ≤ b ≤ √(n log n). The argument breaks even at
  b ≈ (n log n)^{1/3}: a decoded block saves ½ log b bits, and locating it costs log w ≈
  log(√n/b) bits.

## Suggested next steps (§2.10 of the document)

1. **Small blocks with wide constraints, or many partitions.** For b = 1 the class is
   everything, so this is the general open monotone question. Theorems E and E′ settle
   b ≥ n^{1/3+ε}. The natural target is the gap between b ≈ n^{1/3} and b = 1. It needs a
   cheaper way to locate decodable blocks, or a different exchange rate.
2. **Sharper constants in `hyper_compress`:** k/(2r) instead of k/(4er). Running it through
   `kraft_partial` and `power_average` removes the (2r)^k overhead. Getting rid of the factor
   e needs random orders instead of colourings.
3. **The analytic rest of Theorems C and D:** Hoeffding, binomial estimates, PPZ for
   small b.
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
