# Handoff: continue work on Conjecture Q (monotone pairwise tests for Majority)

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
  - Theorem A: `pairwise_count`, `pairwise_weight`, and the general forms `count_via`,
    `weight_via`, `graph_weight`.
  - `three_blocks`.
  - The matching test: `matching_valid`, `matching_card`, `matching_weight`.

The session is `Majority_AC0` (12 theories, ~3500 lines). `isabelle/Audit.thy` lists every
headline theorem and fails the build if any depends on an oracle. Add new headline
theorems there.

Literature summaries written by subagents are in `notes/summaries/`, which is git-ignored
and kept uncommitted:
- `monotone-depth3-majority.md`
- `2601.04072-GKPRST26.md`
- `gppst24-ccc2024.md`
- `amano-isaac2023.md`

Local PDFs in the repo root, also ignored: the L-R paper (v1, v2), GPPST24
(LIPIcs.CCC.2024.17.pdf), Amano 2023 (LIPIcs.ISAAC.2023.7.pdf), and Ja'Ja' 1983
(2402.2403.pdf). The v2 LaTeX source is in `paper-v2/`, also ignored.

## The open problem

**Conjecture Q.** Q(k,b) ≤ C^k · b^{−k/4} · poly(n), where Q(k,b) is the largest fraction of
the Majority slice covered by one valid H (block-weight vectors in [0,b]^k, weighted by
∏ C(b, w_i)).

- **What is proved:** Theorem A gives (k−1)^k · b^{−k/4}, which is tight up to (k−1)^k
  (matching test).
- **Why that is not enough:** the bound is vacuous in the decisive regime b ≈ k ≈ √n.
- **The reduction:** `graph_weight` shows it suffices to restrict witnesses to one digraph
  of bounded out-degree, at a cost of 2^{O(k)}.

## Suggested next steps

See §2.8 of the extensions document.

1. **Sparsify witnesses.** Use the fixed-point form: covered points are the slice fixed
   points of the antitone map T(z)_ℓ = max_j φ_ℓj(z_j). Candidate: for each ℓ, keep only the
   partners whose φ_ℓj is not dominated on the bulk window. Prove the 2^{O(k)} loss, or find
   a counterexample. A counterexample, i.e. a monotone pairwise family with coverage
   e^{−O(k)} at b ≈ k, would give monotone depth-3 Majority of size 2^{O(√n)}.
2. **Formalize the fixed-point reformulation.** Prove that the minimal elements of W are
   exactly the fixed points of T.
3. **Formalize the cost lemma.** A monotone CNF needs one clause per maximal false point.
   Combined with Q, this gives the size bound (★).
4. **Remove block symmetry,** or handle two partitions (the L-R construction uses two).

## Working rules

The user's preferences are also stored in Claude memory.

- **Building:** `.venv/bin/isabelle-build -m "diagnosis: …; change: …; expect: ok|fail — why"`
  with `WALL_TIMEOUT=60 WATCHDOG_TIMEOUT=20`.
  - Do not pipe the output through `tail`.
  - Full errors: `sed -n '/full error/,$p' t/logs/last-build.log`.
  - Sorry check: `.venv/bin/isabelle-query -R isabelle sorry`.
- **Proof style:** no exhaustive or brute-force searches (Python or otherwise) to test
  circuit claims. Prove by hand, then formalize.
- **Tool use:** Edit/Write for file changes, simple one-line Bash, nothing in `/tmp`.
- **Isabelle pitfalls met so far:**
  - Annotate types of existentially bound functions, e.g. `(s :: nat ⇒ nat)`.
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
