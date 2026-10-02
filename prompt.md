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

The session is `Majority_AC0` (14 theories, ~4600 lines). `isabelle/Audit.thy` lists every
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

## Suggested next steps (§2.9 of the document)

1. **Many partitions or wide constraints.** Is there a monotone Σ₃ formula for Majority of
   size 2^{O(√n)} with about log n partitions per test, or with constraints on about log n
   blocks? Or is there a lower bound of 2^{ω(√n)} in that regime?
2. **Formalize the r-ary generalization of Theorem B.** This needs averaging over all orders,
   i.e. convexity.
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
