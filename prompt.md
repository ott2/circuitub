# Handoff: monotone Σ₃ᵏ for Majority, k ≥ 4 (after formalizing Gurumukhani et al.)

$\tiny\color{transparent}\text{provenance: github.com/ott2/circuitub, prompt.md, on top of commit e0daa17e1b06b55a452933d15d0c1128ec8615a6 (2026-10-17)}$

## Current focus: the $\log k$ question (session `Monotone_K`)

The GKPRST26 formalization below is finished. We are now doing research on monotone
$\Sigma_3^k$ for $k \ge 4$. The user chose the $\log k$ question over the factor-2
"Conjecture A", and is open to narrowing the gap in either direction. The user asked to
**co-develop formal proofs with the informal reasoning**, so that each established rung is
formal before we build on it.

**Read first:** `extensions/monotone-k.md`, the research log:
- §1: the literature status.
- §6, §6a: the cluster and Harris rungs.
- **§6b:** `shadow_branch`, the exact shadow identity, and the barriers.
- **§6c:** local certificates and the certificate conjecture.
- **§6d:** the sharpened (concentration) form, the rigid model case, and the deficit
  conjecture.
- **§6e:** deep payments, which refute the deficit conjecture; typical lower bounds;
  condition (R) and the code-like question.
- **§6f:** links (the code-like question is the conjecture at size $m$), the conditional
  form (R$_Y$), and selector mixtures analysed as set systems: Bollobás set pairs, private
  subsets, König, and the intersection attack.
- **§6g:** typical and deviation forms [F], the test cases redone, and the size condition (D).
- **§6h:** the conditional certificate [F], mirror payments [F in part], witness components and
  the component route with its four failure modes.
- §7: Question C.
- §8: the next steps.

**The problem.** Let $S_k(n)$ be the largest number of minimum transversals of a hypergraph
on $n$ vertices with edges of size $\le k$ and $\tau = n/2$. Monotone $\Sigma_3^k$ Majority
size is $\binom{n}{n/2}/S_k(n)$ up to a factor $n+1$.
- **Known upper bound:** PPZ, $2^{n - n/(2k)}$.
- **Best construction:** disjoint blocks $K_{2k-2}^{(k)}$, $2^{n - \Theta(n\log k/k)}$.
- **Conjecture:** $2^n k^{-\Omega(n/k)}$. It is open for $k \ge 4$; the literature was checked
  on 2026-10-11 and again on 2026-10-13.
- **What it would give:** a monotone/non-monotone separation at depth 3. Lecomte–Ramakrishnan
  refute the non-monotone version, so monotonicity must enter essentially.

**The key insight so far.** The $\log k$ is exactly PPZ's Jensen loss. Summing
`forced_kraft` over colourings gives
$\sum_{X} \mathbb E_c\, 2^{F_c(X)} \le 2^n$; PPZ then replaces $\mathbb E\, 2^F$ by
$2^{\mathbb E F}$. When ones share a critical zero set, they share the same maximum colour,
and $2^F$ is heavy-tailed. In the blocks this gives $\mathbb E\, 2^F \approx \tfrac12\sqrt{\pi k}$
per block.

**Where things stand (2026-10-17).**
- **Newest (2026-10-17, §6h): structure.**
  - `certificate_cond` [F] (`Shearer_Conditional.thy`): the cover may depend on a label
    $g(X)$ at cost $H(g)$; `lent_image`: $H(g) \le \ln\lvert g(F)\rvert$.
  - **Witness components** $\mathcal K(X)$: components of the graph joining each one to the
    zeros of its critical edges. *Component route* (by hand from `certificate_cond`): if the
    components have sizes in $[k^c, Ck]$, their sizes are concentrated given $\mathcal K(X)$,
    and $H(\mathcal K) = o(n\log k/k)$, then the conjecture's bound holds. Balance is not
    needed. Four failure modes: small or large components, spread inside components, or
    high-entropy components (the last is §6f's selector question, sharpened).
  - **Mirror payments** [F in part] (`Mirror_Payment.thy`): $\tau = n/2$ (`mp_tau`), every
    deficiency level occurs in a minimum transversal (`mp_deficient`), the one-block trace
    has $\ge 2^{2k-4}$ patterns (`mp_trace`), and the count is within a bit per block of
    extremal (`mp_count`). By hand: deficient events have probability about $4\pi k\,4^{-k}$, so
    the entropy form saves fully on single blocks. The trace form needs unions of $C$ blocks
    and loses a boundary block. Its components are $B_i$, or $B_i\cup B_{\pi(i)} - r_{\pi(i)}$.
- **Earlier (2026-10-17, §6g):**
  - `certificate_typ` (bounds $t_B$ failing on a fraction $p_B$, cost $h(p_B) + p_B\ln t_B$)
    and `certificate_dev` (only $D = \sum_B w_B\mathbb E\lvert\,\lvert X\cap B\rvert - c_B\rvert$
    enters) are formal, in `Shearer_Typical.thy`.
  - **Correction:** in deep payments *every* minimum transversal has exactly $k-1$ in each
    block, so deficient blocks never occur, and the worst-case `certificate` (and even the
    trace form) already gives the full saving. §6e's "rare by $4^{-k}$" and "trace fails"
    were wrong and are marked corrected.
  - The rigid model has total deviation $D = k-1$, so `certificate_dev` gives the full saving.
    The worst-case trace form also saves there (isolated vertices are never in $X$). No example
    yet separates trace from entropy.
  - **New main line: the size condition (D)** of §6g. It implies the conjecture and (R).
    $O(k)$-scale flexibility is absorbed by merging blocks; spread at scale $\gg k$ is the
    code-like case.
- **Earlier on 2026-10-17:**
  - **The certificate theorem is formal.** `certificate` (`Shearer_Certificate.thy`) states:
    for any finite family $F$, any fractional cover, any lower bounds
    $t_B \le \lvert X\cap B\rvert$, and every $0<\theta<1$,
    $\ln\lvert F\rvert \le \sum_B w_B(\lvert B\rvert\ln 2 - \frac12\ln\frac{3\lvert B\rvert+2}{2}) - W\ln(1-\theta) - \Delta\ln\theta$.
    Shearer's lemma itself is formal (`shearer_ent`), so §6c and §6d no longer depend on hand
    proofs.
  - **Selector mixtures are parked** (§6f). Every natural mixture so far fails in the
    direction that favours (R):
    - exact designs cannot switch (`private_design`);
    - with few selectors the helpers are visibly low-entropy;
    - the intersection attack plus König forces the helper-only edges to be code-like
      themselves.
    The only open route is pair-specific edges. Mixing only passes code-likeness down, so a
    counterexample to (R) needs an *intrinsically* code-like part.
- **Three one-level methods stop at $\Theta(n/k)$:** PPZ, Scheder–Tan's Harris form
  (`harris_ppz`), and shadow-branching (`shadow_branch`).
  - All share the leading constant $\frac{1}{2\ln 2}\cdot\frac nk$.
  - All are tight when each one has a private critical edge, so that the residuals are
    perfect $k$-matchings.
  - `shadow_branch` does not even use monotonicity, so by Lecomte–Ramakrishnan it cannot give
    $\log k$.
- **The blocks' $\log k$ lies entirely in the shadow** (§6b). A random set of
  $(1-\frac{1}{k-1})t$ vertices almost never lies inside a minimum transversal. Each block's
  deviation is pinned to an $O(1)$ window, which costs about $1/\sqrt k$ per block.
- **Local certificates** (§6c; formal since 2026-10-17, see above).
  - A fractional partition into $O(k)$-sets whose local $\tau$'s sum to $\tau(H)$, up to a
    deficit $\varepsilon n/k$, gives $2^n k^{-\Omega(n/k)}$.
  - For disjoint blocks it is exact.
  - Open half: **globally rigid hypergraphs have few minimum transversals.** These are the
    hypergraphs with no near-tight local certificate.
- **Sharpened (2026-10-15, §6d).**
  - $\log_2\lvert\mathcal X\rvert \le n - \sum_B w_B(\frac12\log_2\frac{\pi\lvert B\rvert}2 - H(\lvert X\cap B\rvert))$
    for a uniform minimum transversal $X$, so concentrated block sizes are what count.
  - The deficit may be as large as $n k^{-1/2-\eta}$, not just $\varepsilon n/k$.
  - At $\tau = n/2$ the deficit is $\sum_B w_B(\lvert B\rvert/2 - \tau_B)$.
  - $K_{t+1}$ plus isolated vertices is now inside the range. The real rigid model is
    $K_m^{(k)}$ plus isolated vertices: its shortfall is $\approx (k-1)/2$ per block, and its
    concentration comes from global minimality.
  - **Deficit conjecture:** $\log_2\lvert\mathcal X\rvert \le n - \lambda_k\Delta_b$ with
    $\lambda_k \ge k^{-1/2+2\eta}$. It would imply the conjecture.
- **Deep payments (2026-10-16, §6e): the deficit conjecture is false.**
  - Blocks of size $2k-2$ have inside edges all $k$-sets not inside $R_i$, with
    $\lvert R_i\rvert = k-1+s$ and $s = k/4$. A missed $(k-1)$-subset of $R_i$ forces the
    whole next block along a cycle.
  - It has the blocks' count, yet every set of size $\le b$ falls short by
    $\ge \frac{s}{4b}\lvert B\rvert$, so $\Delta_b = \Theta(n)$ for $b = O(k)$.
  - So local-$\tau$ certificates cannot be the mechanism. What pins $\lvert X\cap B\rvert$ is a
    *global* lower bound: a deficient block would force a larger excess elsewhere, so it never
    occurs in a minimum transversal (§6g corrects §6e's "rare by $4^{-k}$").
  - Its $\tau$ and count claims are formal (`Deep_Payment.thy`).
- **What any Shearer-type proof needs (§6e, condition (R)).** Every $H$ must have an
  $O(k)$-partition with local entropy deficit
  $\sum_B w_B(\lvert B\rvert - H(X_B)) \ge c\,n\log k/k$.
  - The trace (worst-case) version does *not* fail on deep payments (corrected in §6g).
  - The obstacle is a *code-like* family: locally near-uniform, constrained globally.
  - Equivalently, a cheap rank-$k$ gadget, with few helper vertices, forcing "exactly half" on
    a group much larger than $k$. If its helpers were few, disjoint copies would refute the
    conjecture.
- **Links (2026-10-16, §6f): the code-like question is the problem itself.**
  - Given $X\cap Y = S$, the set $X - Y$ is a uniform minimum transversal of the link
    $H_S = \lbrace e - Y : e\cap S = \emptyset\rbrace$. So the loss is the selectors' deficit
    plus the average link loss.
  - `link_count` [F]: an "exactly half" gadget with $h$ helpers on $m$ vertices needs
    $2^h S_k(m) \gtrsim \binom{m}{m/2}$. Its helper configurations are the CNFs of a
    $\Sigma_3^k$ cover. So cheap gadgets exist iff the conjecture fails at size $m$.
  - For the proof route: mixing over selectors washes out local deficits, so (R) may fail
    for reasons unrelated to the count. The fix is (R$_Y$): Shearer per link, with a partition
    $w^S$ that may depend on $S$, and the deficit taken from the link part only.

**Formal so far** (`isabelle/monotone_k/Cluster_PPZ.thy`, about 530 lines, plus
`Audit_K.thy`; parent `Majority_AC0`, which imports `Depth3_Lower`):
- `mcnf`, `csat_mcnf`, `forced_mcnf`: monotone hypergraphs as literal CNFs for
  `forced_kraft`.
- `sum_PiE_split`, `sum_PiE_mult`: sums over colourings split over disjoint coordinates.
- `sum_PiE_prod_ge`: independence. Factors on disjoint coordinate sets multiply.
- `inner_sum`, `step_pow`, `pow_telescope`, `pt_bound`, `count_bound`, `term_bound`, and
  `cluster_sum`: one $z$-cluster gives $\mathbb E\, 2^N \ge 1 + q/8$ with $q^2 \le z$ and
  $r = 4z$ colours.
- **`cluster_count`.** If every transversal in a family $A$ has $m$ disjoint $z$-clusters,
  then $\lvert A\rvert\,(1+q/8)^m \le 2^n$. A $z$-cluster is $z$ ones $G$ and $z$ zeros $Z$
  such that each $v \in G$ lies in an edge $\subseteq Z \cup \lbrace v\rbrace$. There is no
  condition on edge size or $\tau$.
- **`Harris_PPZ.thy`** (about 700 lines; log §6a):
  - `harris`, `harris_prod`: the Harris inequality on $\lbrace 0..r-1\rbrace^I$, with the
    order reversed on a set $P$.
  - `harris_count`: groups of ones with disjoint ones and arbitrary, overlapping zero sets.
  - `cluster_count_overlap`: `cluster_count` without disjoint zero sets.
  - `harris_ppz`: at most $2^n/(1+1/k)^t$ transversals. This is Scheder–Tan 2013's FKG form of
    PPZ, not new. The corollary $S_k(n) \le 2^n(1+1/k)^{-n/2}$ was not found stated anywhere.
  - Hand sketch (log §6a): one-forcing per $X$ is capped near $(1+1/k)^t$, using the design
    example, so the zeros or a cross-$X$ argument must supply the $\log k$.
- **`Shadow_Branch.thy`** (about 180 lines; imports only `Main`; log §6b):
  - `tr`, `mtr`, `ext`: transversals, minimal transversals, and minimal extensions of $P$.
  - `minimal_branch`: at most $k^j$ minimal transversals of size $\lvert P\rvert + j$
    containing $P$.
  - `shadow_branch`: if $\tau \ge t$, then
    $\lvert\mathcal X\rvert\binom tj \le \binom{n}{t-j}k^j$ for every $j \le t$.
  - At $n=2t$ this gives $S_k(n) \lesssim \binom{n}{n/2}(1-1/k)^{n/2}$, on paper.
  - Provenance: it composes two lemmas of Håstad–Jukna–Pudlák 1995, and GKP24 Theorem 21
    has $j=1$. The general-$j$ statement was not found stated anywhere.
- **`Deep_Payment.thy`** (log §6e):
  - `dp_forces`, `dp_tau`: $\tau \ge N(k-1)$ for the deep-payment hypergraph.
  - `dp_normal`, `dp_count`: at least $\lvert\mathrm{good}\rvert^N$ transversals of size $N(k-1)$.
  - The tail estimate of $\lvert\mathrm{good}\rvert$ and the shortfall bound are by hand.
- **`Link_Gadget.thy`** (log §6f): `mint` (minimum transversals within $V$), `link`,
  `link_rank`, `link_tr`, `link_back`, `link_mint`, `proj_slack` (helper parts are
  near-minimum transversals of the helper-only edges), and `link_count`
  ($\le 2^{\lvert Y\rvert}M$ minimum transversals with $\lvert X - Y\rvert = j$). The link
  identity (uniform conditionals) is by hand.
- **`Shearer_Sub.thy`, `Shearer_Entropy.thy`** (log §6c, 2026-10-17): `shearer_sub` (Shearer for
  monotone submodular set functions), `cls`/`ent` (trace entropy under a uniform finite family,
  by class counts), `ent_sub` (submodularity), `shearer_ent`
  ($\ln\lvert F\rvert \le \sum_B w_B H(X_B)$).
- **`Shearer_Concentration.thy`, `Shearer_Certificate.thy`** (log §6d): `group_bound`, `ent_count`,
  `ln_binom`, `shearer_conc` (the concentration form, with $(3b+2)/2$ for $\pi b/2$); `gibbs`,
  `int_entropy`, and **`certificate`**, the sharpened certificate theorem with free $\theta$ and
  any lower bounds $t_B$. So §6c and §6d are now fully formal.
  - **`Shearer_Typical.thy`** (log §6g): `int_entropy_typ`, `certificate_typ` (Gibbs against
    uniform mass $r$ below $t$ and geometric mass above), `int_entropy_dev`, `certificate_dev`
    (two-sided geometric around any centre).
  - **`Shearer_Conditional.thy`** (log §6h): `cbound`, `lent_image`, `certificate_cond`.
  - **`Mirror_Payment.thy`** (log §6h, imports `Deep_Payment`): `mp`, `mp_forces`, `mp_mirror`,
    `mp_tau`, `mp_glue_tr` (a sufficient condition for glued choices to be transversals),
    `mp_deficient`, `half_subsets`, `mp_trace`, `mp_count`.
    Pitfalls met: `card_Diff_subset` gives `card {..<m} - card Z`, so finish with `simp`;
    `force` looped on an image goal with a set equation, so use `image_eqI[OF _ mem]` and
    `simp only:`; simp unfolds `S (nxt N i)` along with `S i`, so prove the wanted disjunct
    by cases; nat goals like `2*k-2 + (N-2)*(k-1) = N*(k-1)` need `add_mult_distrib` by hand.
  - Pitfalls met: `ln_mult` and `ln_realpow` are unconditional here (`ln_mult` has an `if`),
    so use `ln_mult_pos[OF p1 p2]` and plain `rule ln_realpow`. simp rewrites `c - v - 1` to
    `c - Suc v` before `sum.reindex` fires; use `simp only: sum.reindex[OF inj] comp_def`.
    A closing simp over a large AC-reshaped sum was slow; state the theorem with the same
    parenthesization as the proof (`a B + c B`) and finish with `.`.
  - Pitfall met: `linarith` failed on a purely linear goal over `define`d atoms, and `argo`
    closed it. Earlier, `ln_le_cancel_iff` (a simp rule) rewrote `ln x ≤ ln c` hypotheses
    during preprocessing. Use `ln_mono` as an exact rule.
- **`Private_Design.thy`** (log §6f, imports `Main`): `private_design` (if $a$-sets are
  equally popular and one is private, two blocks share $< a$ points), `three_blocks`,
  `half_blocks` (three blocks of size $\ge \lvert Y\rvert/2$ force $\lvert Y\rvert < 6a$).
- **Build:**
  `WALL_TIMEOUT=120 WATCHDOG_TIMEOUT=20 isabelle-build --session Monotone_K -m "…"`. It takes
  a few seconds.

**Next (from §8 of the log):**
0. **The size condition (D): the main line** (§6g). Formal side done (`certificate_typ`,
   `certificate_dev`); the test cases are done by hand (blocks and deep payments $D = 0$,
   rigid model $D = k-1$ in total). The structural candidate is now the witness-component
   route of §6h (`certificate_cond`). Next:
   - Failure mode 2: inside a fixed component structure, can $\lvert X\cap K\rvert$ spread by
     $\sqrt{\lvert K\rvert}$? Every one in $K$ shares critical zeros with others, which
     should pin the size. Try to prove this, starting with components in which all ones
     share one zero set (the blocks, the rigid clique).
   - Prove the route's hypotheses for a natural class, such as hypergraphs whose components
     are unions of blocks of one fixed partition, up to rare events.
   - Failure mode 3 is §6f's selector question, sharpened: the component structure must
     carry $\Omega(\log k)$ bits per block, with no coarser $O(k)$-partition absorbing it.
   - A fully separating trace/entropy example is still open. Mirror payments separate only up
     to merging $O(1)$ blocks; deep payments with $R_i = B_i$ is rigid.
0″. **Selector mixtures (parked)** (§6f, end). The code-like question itself is settled: it is
   the conjecture at size $m$.
   - Either realize a hypergraph whose links $H_S$ are block-structured on *different*
     partitions $\pi_S$ of $G$, or show the monotonicity ($S \subseteq S'$ implies
     $H_S \supseteq H_{S'}$) and the rank bound prevent it.
   - If one exists, check that (R) fails on it but (R$_Y$) holds. That would confirm (R$_Y$)
     as the right target.
   - Progress (§6f, 2026-10-17):
     - Switching is a Bollobás set-pair condition; in complement form, each block has a
       private $a$-set.
     - Exact $t$-wise uniform selectors with $t \ge a$ cannot switch (`private_design`).
     - The "all on" attack forces self-similarity: partition $p$'s helper sets need
       $\tau \ge m/2$.
     - Open: the entropic (approximate-design) version, where a private set leaks only about
       $2^{-a}$ bits. Literature summary: `notes/summaries/private-subsets-and-designs.md`.
       Nothing in the literature treats it.
     - Dichotomy (by hand): with $P \le 2^{a+1}$ selectors, the helpers' blocks are visibly
       deficient. With more selectors, each private set costs $\gtrsim 2^{-2a}$ (Pinsker),
       which Han's inequality sums over $Y$. A middle range of $P$ is open.
     - The direct divergence estimate gives about $0.22\cdot 2^{-a}$ bits per private set. Han
       over $a$-sets then certifies (R) only for $a \lesssim \log_2 k$.
     - Intersection attack plus König: two block partitions with the same even block size
       have a common half-transversal. So the helper-only edges $E_Y$ carry an "exactly half"
       instance on every $S_p\triangle S_q$ (`proj_slack` is the formal slack version).
       The cheapest $E_Y$, a perfect matching, is visible to (R). So a mixture evading (R)
       needs a code-like $E_Y$: the regress, made concrete.
     - Escape route found by trying to break the attack: pair-specific edges, whose helper
       parts meet both halves of $S_p\triangle S_q$ and avoid $S_p\cap S_q$. Whether about
       $P^2$ such families fit within rank $k$ is open.
     - If resumed: settle pair-specific edges, or look for *intrinsically* code-like
       families.
     - Mixing only passes code-likeness down. A counterexample to (R) needs a part of $V$
       whose projected family is locally uniform with no selector explaining it.
0'. **Typical lower bounds, by hand** (§6e).
   - Find a rule that names $\ell_B$ from the structure of $H$, together with a switching
     argument ("a deficient $X$ maps to many normal ones") showing that
     $\lvert X\cap B\rvert < \ell_B$ is rare. With the escape clause, the concentration
     conjecture of §6e is only equivalent to the main conjecture; naming $\ell_B$ in advance
     is what would make it a reduction.
   - Test cases: the deep-payment example and the rigid model $K_m^{(k)}$ plus isolated vertices.
   - Be wary: two conjectures (union lemma, deficit conjecture) fell to explicit
     constructions within a day. Try to break each new statement before building on it.
   - The union lemma ($\le k\tau$ vertices in minimum transversals) is **false** for $k \ge 3$
     and true for graphs (§6d). It is not needed any more.
   - When something survives by hand, formalize it. The Shearer toolkit is in place:
     `shearer_ent`, `group_bound`, `gibbs`, `int_entropy`, `certificate`.
1. **Question C, by hand** (secondary now). If $\tau = n/2$ and there are many minimum transversals, do most
   of them have $\Omega(n/k)$ disjoint $O(k)$-clusters? Known so far:
   - A cluster-free minimum transversal can exist (the linear-design example in §7), but
     there it was unique, and all its swap neighbours are cluster-rich.
   - A swap $X - v + u$ makes $v$ a shared critical zero.
   - Test whether swaps at far-apart places commute.
   - Zero sets may now overlap (`cluster_count_overlap`).
   - A naive swap charging loses by a constant: locating a swap costs about $\log_2 k$ bits,
     and a cluster gains about $\frac12\log_2 k$. So the swaps must be located canonically
     (log §7).
2. **If so, formalize** the charging
   $\lvert\text{bad}\rvert \le \gamma^{1-\varepsilon}\lvert\text{good}\rvert$ on top of
   `cluster_count_overlap`. Here $\gamma$ is the gain per good transversal.
3. **Fallback:** Conjecture A, $S_k(n) \le 2^{(1-1/k)n}$, which doubles PPZ's exponent.

**Rules here:**
- Prove by hand first, and no brute-force or exhaustive search. The user prefers attempts at
  proving the result or a variant, and analysis of the obstacles, over experiments: the
  numbers grow too fast for useful data (2026-10-14).
- Check novelty with a background literature agent before presenting a bound as new. Twice
  this session the idea turned out to be known: Scheder–Tan for Harris, and HJP95/GKP24 for
  shadow-branching.
- Never patch Markdown with Python heredocs: non-raw strings turn TeX escapes into control
  characters. Use Edit.
- Keep the log honest: label every claim proved [F], proved by hand, or heuristic.
- Routine research progress needs no approval (2026-10-17): record results, formalize hand
  proofs, and launch literature agents without asking, then report. Pushes and anything
  outward-facing still wait for the user.
- Run `isabelle-query -R isabelle sorry` from the repo root, or `-R .` from `isabelle/`. A
  scan of the whole repo also finds `control/Oracle_Control.thy`, the deliberate positive
  control for the audit.
- Constructions that would beat the blocks are the other direction. Note from §4 that disjoint
  cliques can't beat $K_{2k-2}^{(k)}$.

## The GKPRST26 formalization (finished)

The task is to formalize in Isabelle the main theorem of Gurumukhani, Kleber, Paturi, Rosin,
Saks and Talebanfard, *Optimal Monotone Depth-Three Circuit Lower Bounds for Majority*
(arXiv:2601.04072v2). The point is to check a recent proof formally and report any gaps, as
with the Lecomte–Ramakrishnan verification described below.

**Status: the paper's main theorem, its Majority consequence, and the matching upper bound
(for $4 \mid n$) are formally proved, with no `sorry`. All are oracle-audited.**

- **`theorem gkprst_bound`.** Let $F$ be a monotone CNF over $V$ with clauses of size
  $\le 3$, with no transversal of size $< t$, and let $s = 3t-n$. Then $F$ has at most
  `bound T0 s t` transversals of size $t$: $(2/3)^{s/2}3^t$ for even $s$, and
  $\tfrac79(2/3)^{(s-1)/2}3^t$ for odd $s$.
- **`gkprst_half`, `gkprst_half_odd`.** For $n = 2t$ the bound is at most $6^{n/4}$; for
  $n = 2t-1$ it is at most $6^{(n+1)/4}$.
- **`majority_mcnfs`, `majority_mcnfs_any`** (session `GKPRST_Majority`). A monotone OR of
  3-CNFs for Majority needs $\binom{n}{n/2}/6^{n/4}$ CNFs for even $n$, and
  $\binom{n}{\lfloor n/2\rfloor}/6^{(n+1)/4}$ for every $n$.
- **`majority_mcnfs_upper`, `majority_mcnfs_tight`.** For $4 \mid n$,
  $(n+1)\binom{n}{n/2}/6^{n/4} + 1$ CNFs suffice, each with $n+1$ gates. So the minimum is
  pinned down up to a factor $n+1$. The paper only cites this direction (GKP24); here it is
  proved.
- **`majority_mcnfs_upper_any`, `majority_mcnfs_tight_any`** (`Majority_3CNF_Any.thy`). For
  every $n$, $6^{1/4}(n+1)\binom{n}{\lfloor n/2\rfloor}/6^{n/4} + 1$ CNFs suffice, within
  $\sqrt6\,(n+1)$ of `majority_mcnfs_any`. So the paper's theorem and its Majority
  consequence are now settled formally in both directions.

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

    WALL_TIMEOUT=120 WATCHDOG_TIMEOUT=30 isabelle-build --session Monotone_Sigma3 -m "…"

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

### Session `GKPRST_Majority` (done)

The session lives in `isabelle/gkprst/majority/`. Its parent is `Majority_AC0`, with
`sessions Monotone_Sigma3 "HOL-Combinatorics"`. It needs its own directory, because Isabelle
rejects two sessions sharing one.
- **Build** with
  `LOOP_PROGRESS_THRESHOLD=20 WALL_TIMEOUT=600 WATCHDOG_TIMEOUT=120 isabelle-build --session GKPRST_Majority -m "…"`.
  It takes 20–40 s.
- **Why the loop threshold.** The audit is one long `ML` command. Under machine load (another
  session's builds, load around 18) it trips the default loop heuristic of three warnings
  without actually looping. Check first that the other theories reached 100%.
- **The venv is now active,** so `isabelle-build` and `isabelle-query` are on `PATH`.

The theories:
- **`Majority_3CNF.thy`** (about 290 lines), the lower bounds:
  - `MCNF w f`: an AND of ORs of at most $w$ positive literals.
  - `pclause`, `pcnf`, `eval_pcnf`, `pcnf_cnf`: the bridge from formulas to `hits`.
  - `majority_mcnfs_slice`: the generic count. For $n \le 2t \le n+1$ and a bound $B$ on
    every threshold-$t$ CNF, $\binom{n}{t} \le L B$.
  - From it: `majority_mcnfs` (even $n$), `majority_mcnfs_odd`, `majority_mcnfs_any`,
    `majority_mcnfs_exp`, `majority_mcnfs_exp_any` and `majority_mcnf_formula` (gates).
- **`Majority_3CNF_Upper.thy`** (about 840 lines), the matching upper bound:
  - `pmap`: permuted CNFs keep cnf, thr and transversals.
  - `slice`, `perm_exists`, `fiber_card`, `fiber_ratio`. The fibres $\lbrace p : pX = Y\rbrace$
    are cosets, so $pX$ is uniform on the slice; no factorials are needed.
  - `good_perm` (averaging), then `greedy` and `greedy_cover`: $kT \ge (n+1)N$ copies cover
    the slice.
  - `cform`, `fform`, `MCNF_fform`, `gates_fform`: from clause sets to formulas.
  - `threshold_cover`: for any threshold-$t$ CNF with $T$ transversals, an OR of
    $(n+1)N/T + 1$ copies computes "weight $\ge t$".
  - `blk`, `K4`, `Q4`, `K4_thr`, `K4_trans`, `Q4_card`: the extremal CNF, $n/4$ disjoint
    $K_4^{(3)}$ blocks with $6^{n/4}$ transversals.
  - `majority_mcnfs_upper`, `majority_mcnfs_tight`.
- **`Majority_3CNF_Any.thy`** (about 360 lines), every $n = 4m + r$:
  - `union_cnf`, `union_thr`, `union_trans`, `union_trans_card`: for CNFs on disjoint variable
    sets, thresholds add and minimum transversals multiply.
  - `KC B k` (all $k$-subsets of $B$), `hits_KC` ($\lvert B\setminus X\rvert < k$), `KC_thr`,
    `KC_trans_card`.
  - `XF m r`: $m$ blocks of $K_4^{(3)}$ plus `KC` of size `kg r` on the last $r$ variables;
    threshold $2m + \lceil r/2\rceil$, $6^m\binom{r}{\lceil r/2\rceil}$ transversals.
  - `quarter_bound`: that count is $\ge 6^{(n-1)/4}$, via $q = 6^{1/4}$, $q \le 2$, $q^2 \le 3$.
  - `majority_mcnfs_upper_any`, `majority_mcnfs_tight_any`.
- **`Audit_GKPRST.thy`:** the oracle check for all of the above. The `type*` theorems are
  local to the locales, so they have no global names; they are covered through
  `gkprst_bound`.

### Next steps

1. **Done: the upper bound for every $n$** (`Majority_3CNF_Any`). Small cliques sufficed
   instead of the paper's necklace; the necklace would only improve the constant
   ($c_2 = 2$ to $14/6$).
2. **The writeup:** `gkprst26/gaps-for-authors.md`. Every counterexample and every repaired
   table was re-checked by hand against the v2 LaTeX, which is byte-identical to the arXiv v2
   tarball. There was still no v3 on 2026-10-17 (arXiv listing checked).
   - On 2026-10-17 the note's "draft" header was removed and an Attribution section added
     (Claude Opus 5.5 did the formalization and the note; the user edited).
   - `main` was pushed the same day, so the note and the Isabelle sources are public.
   - The user planned a short email to the submitting author, Navid Talebanfard. It
     discloses the LLM assistance and points to the note and to `isabelle/gkprst`.
   - Whether it was sent, and any reply, is the user's to report. Never send anything
     externally yourself.
3. **Watermarks.** Run `tools/watermark.py FILE.md …` to restamp documents with the current
   commit, and use `--check` to see what would change. Run it before committing document
   edits. Never run it on `VERDICT.md`.
4. **In progress: monotone $\Sigma_3^k$ for $k \ge 4$.** See "Current focus" at the top.

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
- With quantified premises like `∀σ. … ⟷ majority n σ`, give the instance:
  `spec[OF maj, of "λv. v ∈ X"]`. `blast` loops trying to instantiate them higher-order.
- `blast` also loops on conditional equivalences such as `finite C ⟹ eval … ⟷ …`. Use
  `ball_cong` and apply the lemma with `rule`.
- `simp` unfolds `∘` before `image_comp` fires. Write the step as
  `(f ∘ g) ` X = f ` (g ` X)` and use `simp only: image_comp`.
- `simp` splits `real (n + 1)` and `(n + 1) * N`, and then the facts no longer match.
  `define M = (n + 1) * N` keeps an atom, and `simp only: of_nat_mult` casts it.
- Use `exp_of_nat_mult` with `simp only:` or as an exact `rule` instance. Plain `simp`
  normalizes it away.
- `simp` won't evaluate `4 choose 2`. Use `simp add: numeral_eq_Suc`.
- After `intro exI` the witness is schematic, and a later `show` fails to match it. Give the
  witness: `rule exI[of _ "…"]`.
- Annotate `fix i j :: nat` when nothing else forces the type. Also annotate
  `fix c :: "nat ⇒ nat"` in sums over colourings: otherwise `c :: nat ⇒ 'a`, and you get a
  type clash.
- **Dependency equations loop.** With a premise like `∀c. f c = f (restrict c S)`, `simp`,
  `auto` and `blast` rewrite it forever. Use exact instances: `spec[OF bspec[OF prem insertI1]]`,
  and `ball_insertD` (in `Cluster_PPZ`) to pass from `insert x K` to `K`.
- When `of` instantiates the wrong variable, or `OF` reports "multiple unifiers" with
  higher-order `f`, use `where f = "…" and g = …`.
- **Alternating loops escape the watchdog.** The loop check needs three warnings on one line,
  so two looping commands interleaving are only caught by the wall clock. Keep
  `WALL_TIMEOUT` short (120).
- Finish real-arithmetic chains with `define` atoms (`P = R^(2z-1)`, `T = Σ…`) and named
  equations, then `unfolding … by simp` or `linarith`. `simp add: algebra_simps` on
  mixed powers and casts fails.
- `sum.inter_filter`: apply it as `rule sum.inter_filter[symmetric]`, because `simp` reshapes
  `{i∈{..<q}. P i}` first.

### Documents

- **The monotone-$k$ research log is `extensions/monotone-k.md`.** It is linked from the README
  row for `isabelle/monotone_k/`. Add the new theorem names to `Audit_K.thy`.
- **The results document is `extensions/monotone-3cnf.md`.** It is linked from `README.md` and
  from §2.1 of `extensions/locality-and-monotonicity.md`. Update its status table, §1 and
  §5–6 as work lands. `gkprst26/NOTES.md` keeps the case-by-case record.
- No HTML markup in Markdown: the user is concerned it may trip ML toolchains. Hidden
  provenance goes in TeX via `tools/watermark.py`. Don't use paper-private LaTeX macros
  (`\prop`, `\ntrnz`, …) in Markdown either; write P0.4, $N_{2o}$ and so on.
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
