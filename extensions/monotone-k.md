# Monotone $\Sigma_3^k$ for Majority, $k \ge 4$: research log

$\tiny\color{transparent}\text{provenance: github.com/ott2/circuitub, extensions/monotone-k.md, on top of commit 3fefb0bf0c0e63f93896a9016702d24c657b6d40 (2026-10-20)}$

Status: **open problem. Formal rungs (session `Monotone_K`): `cluster_count` (§6) and the Harris inequality with its consequences (§6a), `shadow_branch` (§6b), and the Shearer certificate theorems, including typical and deviation forms (§6c, §6d, §6g), and the witness-antichain bound `witness_bound` (§6i). The rest is pen and paper. The deficit conjecture of §6d is refuted in §6e; the main line is now the size condition (D) of §6g and the witness-component route of §6h.**

## 1. The question, and what is known

A monotone $\Sigma_3^k$ circuit for Majority is an OR of monotone $k$-CNFs. By the counting
lemma (`majority_mcnfs_slice`, and the covering argument `threshold_cover`), its least size is
$\binom{n}{n/2}/S_k(n)$ up to a factor $n+1$. Here $S_k(n)$ is the largest number of minimum
transversals in a hypergraph $H$ on $n$ vertices with edges of size $\le k$ and transversal
number $\tau(H) = n/2$.

| $k$ | Upper bound on $S_k(n)$ | Best construction | Source |
|---|---|---|---|
| 2 | $2^{n/2}$ | $2^{n/2}$ (perfect matching) | GKP24, Theorem 12 |
| 3 | $6^{n/4} \approx 2^{0.646n}$ | the same | GKPRST26 (formal here) |
| $\ge 4$ | $2^{(1 - 1/(2k))n}$ (critical clauses, PPZ) | $\binom{2k-2}{k-1}^{n/(2k-2)} \approx 2^{n - \frac{n}{4k}\log_2(\pi k)}$ | blocks of $K_{2k-2}^{(k)}$ |

- The conjecture (GPPST24, GKP24) is $S_k(n) \le 2^n k^{-\Omega(n/k)}$. It would give monotone
  depth-3 Majority size $2^{\Omega(\sqrt{n\log n})}$. Together with Lecomte–Ramakrishnan's
  $2^{O(\sqrt n)}$ non-monotone circuits, that would be a monotone/non-monotone separation
  at depth 3.
- Lecomte–Ramakrishnan refute the non-monotone version for $k$ up to about $\sqrt n$. So any
  proof of the $\log k$ factor must use monotonicity in an essential way. PPZ-type arguments,
  which apply equally to non-monotone CNFs, cannot give it for large $k$.
- GKPRST26: "It is perhaps more challenging to extend the current techniques for $\Sigma_3^k$
  for $k \ge 4$."
- The literature check of 2026-10-11 was repeated on 2026-10-13 and found nothing newer. The
  nearest results bound *minimal* transversals of rank-$k$ hypergraphs. For rank 4 the best
  is $O(1.8863^n)$, weaker than the PPZ bound $2^{7n/8} \approx 1.834^n$. For $k \ge 4$, PPZ is
  the best monotone bound we know of.

## 2. Ideal forcing: an exact identity

Let $\mathcal X$ be the minimum transversals, all of size $t = \tau(H)$, and fix an order
$\pi$ of the vertices. Reveal the indicator of $X \in \mathcal X$ in the order $\pi$. Call a
vertex *forced* for $X$ if every $X' \in \mathcal X$ that agrees with $X$ on the earlier
vertices also agrees with it there. Let $F_\pi(X)$ be the number of forced vertices.

**Identity.** $\sum_{X \in \mathcal X} 2^{F_\pi(X)} = 2^n$ for every $\pi$.

The decision tree splits weight in half at each unforced vertex, and passes it on at each
forced one. The leaves are the elements of $\mathcal X$, at weight $2^{-(n - F_\pi(X))}$, and
the weights sum to 1. By Jensen, over $X$ and then over a random $\pi$,

$$\lvert\mathcal X\rvert \le 2^{\,n - \mathbb E_{X,\pi} F_\pi(X)}.$$

PPZ is the special case in which only critical clauses are used: a vertex $v \in X$ is forced
once the other $\le k-1$ vertices of an edge $e$ with $e \cap X = \lbrace v\rbrace$ have been
revealed. That happens with probability $\ge 1/k$, so $\mathbb E F \ge t/k = n/(2k)$.

**Residuals.** Write $P$ for the revealed vertices. Conditioning on $X \cap P$ leaves
$X \setminus P$ uniform over the minimum transversals of the residual hypergraph
$\lbrace e \setminus P : e \cap X \cap P = \emptyset\rbrace$. Its transversal number is exactly
$\lvert X \setminus P\rvert$. A vertex is forced to 1 when it lies in every minimum
transversal of the residual, and forced to 0 when it lies in none. Isolated vertices of the
residual are always forced to 0.

## 3. Blocks: exactly $n/k$ forced

Take the clique $K_b^{(k)}$, all $k$-subsets of $b$ vertices. Its minimum transversals are all
sets of $m_1 = b-k+1$ vertices, so $m_0 = k-1$ vertices are zeros. A vertex is forced exactly
when the rest of the block is monochromatic, so $F$ is the length of the final monochromatic
run, and

$$\mathbb E F = \frac{m_1}{m_0+1} + \frac{m_0}{m_1+1}.$$

Each one comes after all the zeros with probability $1/(m_0+1)$, and each zero after all
the ones with probability $1/(m_1+1)$. The final run consists of exactly these vertices. In disjoint unions, forcing
adds over the components.

- **The extremal blocks** $K_{2k-2}^{(k)}$ have $m_0 = m_1 = k-1$, so $\mathbb E F = 2(k-1)/k$
  per $2k-2$ vertices. That is **exactly $n/k$**, for every $k$. For $k = 3$ this is $4/3$ per
  $K_4^{(3)}$; for $k = 2$ it is $1$ per edge.
- **For $k = 2$** the bound $2^{n - n/k}$ is $2^{n/2}$, the true value.

## 4. The intermediate target

**Conjecture A.** If $\tau(H) = n/2$ and the edges have size $\le k$, then
$\mathbb E_{X,\pi} F_\pi(X) \ge n/k$. Hence $S_k(n) \le 2^{(1 - 1/k)n}$, and monotone
$\Sigma_3^k$ Majority circuits need $2^{n/k - O(\log n)}$ CNFs.

- This doubles the PPZ exponent $n/(2k)$. It is exact for $k = 2$. For $k = 3$ it is weaker than
  GKPRST26 (exponent $0.333n$ against $0.354n$). For $k \ge 4$ it would be new.
- It does not give the $\log k$, and no argument through $\mathbb E F$ can: the blocks have
  only $n/k$ forced vertices, while their count is $2^{n - \Theta(n\log k/k)}$. The gap is
  Jensen's, and §6 shows that forcing *without* Jensen recovers it.
- Ones contribute $\ge t/k = n/(2k)$ (PPZ). The missing half must come from zeros. In the
  blocks a zero is forced once all $k-1$ ones of its block are revealed, a "dual critical
  set" of size $k-1$.

**A version for all $\tau$ (Conjecture B).** $\mathbb E F \ge 2(n-\tau)/k$, twice the number
of zeros over $k$. At $\tau = n/2$ this is Conjecture A.
- For every clique $K_b^{(k)}$, $\frac{m_1}{m_0+1} + \frac{m_0}{m_1+1} \ge \frac{2m_0}{m_0+1}$,
  with equality exactly at $m_1 \in \lbrace m_0 - 1, m_0\rbrace$, i.e. $b \in \lbrace 2k-3, 2k-2\rbrace$.
  So B holds for all disjoint unions of cliques.
- The symmetric form "$\ge n/k$ for every $\tau$" is false. $K_{2k}^{(k)}$ has
  $\mathbb E F = 2 + \frac1k - \frac{3}{k+2} < 2$.

## 5. Obstacles found so far

- **Zeros need not have small dual critical sets.** In $K_{t+1}$ plus $t-1$ isolated vertices
  ($k = 2$), the zero of the clique is forced only after all $t$ ones. The isolated zeros are
  always forced, and they compensate. So a proof must charge globally, not per vertex.
- **The simple sufficient rules are not enough, even for $k = 2$.** The rules are: a one is
  forced after a critical edge, and a zero once all its edges are hit by revealed ones. Take
  the bipartite graph with $X = \lbrace v_1,\dots,v_4\rbrace$, $Y = \lbrace u_1,\dots,u_4\rbrace$, edges
  $v_1u_1$, $v_2u_2$, and $v_3, v_4$ each joined to $u_3, u_4$, with $v_3u_1$ and $v_4u_2$
  as well. For the cover $X$, the rules guarantee only
  $4 - \sum_{v}\frac{1}{d_v+1} + \sum_{u}\frac{1}{d_u+1} = 4 - \frac32 + \frac43 \approx 3.83$
  forced vertices in expectation, below the $n/k = 4$ the conjecture needs on average. Yet
  the graph has only 5 minimum covers, so ideal forcing does better.
- **No single potential $a n + c\tau$ supports a one-step induction.** Cliques have no vertex
  that is constant across the minimum transversals, so all their forcing happens late.

## 6. The $\log k$ is PPZ's Jensen loss [F]

Average `forced_kraft` over colourings $c$ *without* Jensen. For any family $\mathcal A$ of
transversals and any sound forcing rule,

$$\sum_{X \in \mathcal A} \mathbb E_c\, 2^{F_c(X)} \le 2^n, \qquad\text{so}\qquad
\lvert\mathcal A\rvert \le 2^n \big/ \min_{X \in \mathcal A} \mathbb E_c\, 2^{F_c(X)}.$$

PPZ replaces $\mathbb E\, 2^F$ by $2^{\mathbb E F}$. For a fixed $X$, the ones are forced
independently once the zeros' colours are known. A one $v$ is forced with probability
$1 - \mu_v$, where $\mu_v$ is the least, over its critical zero sets, of the largest colour
in the set. So $\mathbb E\, 2^F = \mathbb E \prod_{v\in X}(2 - \mu_v)$. When several ones
share one critical zero set, they share the same $\mu$, and the product is heavy-tailed.

**Clusters.** A *$z$-cluster* of $X$ is a set $G \subseteq X$ of $z$ ones and a set
$Z \subseteq V \setminus X$ of $z$ zeros such that every $v \in G$ lies in an edge inside
$Z \cup \lbrace v\rbrace$. Let $N$ be the number of $v \in G$ coloured above all of $Z$. With
$r = 4z$ colours,

$$\mathbb E\, 2^N = r^{-z} \sum_{a \in [r]^Z} \bigl(1 + \mathrm{cnt}(a)/r\bigr)^z \ge 1 + \lfloor\sqrt z\rfloor/8,$$

where $\mathrm{cnt}(a)$ is the number of colours above $\max a$. Lower $\mathrm{cnt}$ by
$\min(\mathrm{cnt}, q)$ with $q = \lfloor\sqrt z\rfloor$, and telescope. In each term,
$(r+i)^{z-1}(r-i-1)^z$, the first-order terms cancel: $(r+i)(r-i-1) \ge r^2(1 - 5/(16z))$.
Bernoulli then gives each of the $q$ terms $\ge z r^{2z-1}/2$. By contrast $2^{\mathbb E N}$
stays below $2$.

**Theorem (`cluster_count`, formal, session `Monotone_K`).** Let $\mathcal A$ be any family of
transversals of any hypergraph on $n$ vertices. If every $X \in \mathcal A$ has $m$
$z$-clusters on pairwise disjoint vertex sets, then
$\lvert\mathcal A\rvert\,(1 + \lfloor\sqrt z\rfloor/8)^m \le 2^n$.

- Neither the edge size nor $\tau$ appears. The edges inside a cluster have size $\le z+1$
  automatically.
- Clusters on disjoint vertices are independent under a random colouring
  (`sum_PiE_prod_ge`). This is why the colourings of `Depth3_Lower` are used rather than
  permutations.
- **Sanity check.** In disjoint blocks $K_{2k-2}^{(k)}$, every minimum transversal has
  $n/(2k-2)$ clusters with $z = k-1$. The theorem then gives $2^n k^{-\Omega(n/k)}$, the
  conjectured order. It is weaker than PPZ for small $k$ (the constant $1/8$), and stronger
  once $\lfloor\sqrt z\rfloor/8$ is large.

## 6a. Harris instead of Jensen, and overlapping clusters [F]

**The inequality is not new.** Scheder and Tan (*On the average sensitivity and density of
$k$-CNF formulas*, APPROX/RANDOM 2013, Lemma 4, DOI 10.1007/978-3-642-40328-6_47) observed
that for monotone CNFs, PPZ's Jensen step can be replaced by the FKG inequality. Here it is
formal, in the discrete form we need.

**Why it applies.** Fix $X$ and colour every vertex independently. The event "$v \in X$ is
coloured above every zero of a critical set $C$" is increasing in the colours of the ones and
decreasing in the colours of the zeros. Reverse the order on the coordinates in $X$. Then all
such events, and all products of $2^{N}$ over groups of ones, decrease in the same product
order, so they are positively correlated however their zero sets overlap.

**Formal statements** (`isabelle/monotone_k/Harris_PPZ.thy`):

- **`harris`.** On $\lbrace 0..r-1\rbrace^I$ with the order reversed on a set $P$, two
  decreasing functions satisfy $\sum f \cdot \sum g \le r^{\lvert I\rvert} \sum fg$. The proof
  is by induction on $I$, using Chebyshev's sum inequality for one coordinate.
- **`harris_prod`.** The same for any finite product of nonnegative decreasing functions.
- **`harris_count`.** Let each $X \in \mathcal A$ have groups $(G_i, Z_i)$ with the $G_i$
  pairwise disjoint, and every $v \in G_i$ in an edge inside $Z_i \cup \lbrace v\rbrace$. Then
  $\lvert\mathcal A\rvert \cdot \min_X \prod_i \mathrm{gav}(G_i,Z_i) \le 2^n$, where
  $\mathrm{gav}$ is the average of $2^N$ for the group alone.
- **`cluster_count_overlap`.** `cluster_count` with only the ones of the clusters disjoint.
  The zero sets $Z_i$ may overlap arbitrarily.
- **`gav_single`, `harris_ppz`.** A single one with a critical set of size $s$ has
  $\mathrm{gav} \ge 1 + 1/(s+1)$ in the limit $r \to \infty$. Hence: transversals of size
  $\ge t$ whose ones all have critical edges of size $\le k$ number at most
  $2^n/(1+1/k)^t$.

**The consequence for $S_k(n)$, a corollary we did not find stated anywhere** (literature check of 2026-10-13):

$$S_k(n) \le 2^n\,(1+1/k)^{-n/2} = 2^{\,n - \frac n2\log_2(1+1/k)}.$$

- The PPZ exponent $n/(2k)$ improves by the factor $k\log_2(1+1/k)$: $1.29$ at $k = 4$,
  tending to $1/\ln 2 \approx 1.44$.
- So monotone $\Sigma_3^k$ Majority needs $\binom{n}{n/2}(1+1/k)^{n/2}/2^n$ CNFs, for example
  $1.118^n$ at $k = 4$ instead of PPZ's $1.0905^n$. The bridge from formulas is only formal
  for width 3 (`majority_mcnfs_slice`), so this last step is on paper.
- This is still $\Theta(n/k)$, not the conjectured $\Theta(n\log k/k)$. It is weaker than
  Conjecture A ($\log_2(1+1/k) < 2/k$).

**One-forcing alone cannot do much better (heuristic, a hand sketch).** In the linear-design example of
§7, every one has a single critical set of size $k-1$, and these sets pairwise share at most
one zero. A large deviation of $\sum_v (1 - \max_{C_v} c)$ requires whole sets $C_v$ to be
coloured low, which costs about $k$ low zeros per set gained. So
$\mathbb E\, 2^N = (1+1/k + o(1/k))^t$ for that $X$. Any argument that bounds each $X$
separately using only critical edges of ones is therefore capped at about
$(1+1/k)^{t}$. Beating it needs zeros, or an argument across many $X$ (Question C).

## 6b. Shadows and branching [F], and where the blocks' $\log k$ lives

**Theorem (`shadow_branch`, formal).** Let $H$ have edges of size $\le k$ on $n$ vertices,
with no transversal of size $< t$, and let $\mathcal X$ be its transversals of size $t$. Then
for every $0 \le j \le t$,

$$\lvert\mathcal X\rvert \binom{t}{j} \le \binom{n}{t-j}\, k^j.$$

*Proof.* Count the pairs $(X, Y)$ with $X \in \mathcal X$, $Y \subseteq X$ and
$\lvert Y\rvert = t-j$. For a fixed $Y$, each extension is $X = Y \cup J$, where $J$ is a
transversal of size $j$ of the edges that $Y$ misses. $J$ is *minimal*, because a smaller $J$
would give a transversal of $H$ of size $< t$. A rank-$k$ hypergraph has at most $k^j$
minimal transversals of size $j$ containing a given set, by branching on an unhit edge
(`minimal_branch`). $\square$

**Provenance** (literature check of 2026-10-14). The technique is not new.
- It composes two lemmas of Håstad–Jukna–Pudlák 1995: the $k^s$ branching bound (Lemma 3.4)
  and the averaging step of Lemma 3.1. For Majority they used only the pure branching step.
- GKP24 (arXiv 2412.20493, Theorem 21) proves the case $j = 1$, and their Lemma 9 is the
  single-block equality case.
- We found the general-$j$ inequality and its $t = n/2$ corollary stated nowhere (about 70%
  confidence).
- At $k = 3$ it is weaker than GPPST24 ($1.598^n$) and GKPRST26 ($6^{n/4}$). For $k \ge 4$ it
  only shifts $k$ to $k-1$ in the Scheder–Tan constant.
- **The proof never uses monotonicity.** It holds for the satisfying assignments of weight $t$
  of any $k$-CNF with none of smaller weight. By Lecomte–Ramakrishnan, no argument of this
  kind can give the $\log k$. That is a third reason, besides the two barriers below, that the
  monotone content must enter through the shadow.

**Consequences (on paper).**
- At $n = 2t$, the best $j$ is about $t/(k-1)$, where the $j$ residual edges would exactly
  form a perfect $k$-matching on the $t + j$ remaining vertices. It gives
  $$S_k(n) \le \binom{n}{n/2}\Bigl(1 - \frac1k\Bigr)^{n/2} O(\sqrt{n/k}) \approx 2^{\,n - \frac n2\log_2\frac{k}{k-1}}.$$
- This beats Scheder–Tan's $2^n(1+1/k)^{-n/2}$ (§6a), since $\frac{k}{k-1} > \frac{k+1}{k}$.
  The leading constant $\frac{1}{2\ln 2}\cdot\frac nk$ is the same.
- For $k=2$ it is tight: $j = t$ gives $2^{n/2}$, the GKP24 bound.
- For $k=3$ it gives $(8/3)^{n/2} \approx 2^{0.7075n}$, against the true $6^{n/4} \approx 2^{0.646n}$.
- For $k=4$ it gives $1.732^n$. So monotone $\Sigma_3^4$ Majority needs about $1.155^n$ CNFs,
  against $1.118^n$ (§6a) and PPZ's $1.0905^n$.
- For a single block $K_{2k-2}^{(k)}$ the inequality is an equality at $j = 1$.

**The exact identity behind it.** The proof's first step is an equality:
$$\lvert\mathcal X\rvert\binom tj = \sum_{Y \in \partial_{t-j}\mathcal X} \mathrm{ext}(Y).$$
Here $\partial_{t-j}\mathcal X$ is the lower shadow (the $(t-j)$-sets contained in some
$X \in \mathcal X$), and $\mathrm{ext}(Y)$ is the number of $X \supseteq Y$. The theorem
bounds the two factors separately: $\mathrm{ext}(Y) \le k^j$ and
$\lvert\partial_{t-j}\mathcal X\rvert \le \binom{n}{t-j}$.

**Where the blocks' $\log k$ lives (hand computation).** Take disjoint $K_{2k-2}^{(k)}$ blocks
and $j = t/(k-1)$, so each block has one free one on average.
- *The extension count is tight up to $O(1)$ per block.* A $Y$ in the shadow has
  $\lvert Y\cap B\rvert = k-1-j_B$ with $j_B \ge 0$ and $\sum_B j_B = j$. Then
  $\mathrm{ext}(Y) = \prod_B \binom{k-1+j_B}{j_B} \approx k^j / \prod_B j_B!$.
- *The shadow carries the whole $\frac12\log_2 k$ per block.* A $(t-j)$-set $Y$ is in the shadow
  exactly when $\lvert Y \cap B\rvert \le k-1$ for every block. The mean is $k-2$ and the
  standard deviation about $\sqrt k$. Because the total is fixed, the deviations are at most 1
  and sum to zero, so almost all of them are pinned to an $O(1)$ window. That costs about
  $1/\sqrt k$ per block: $\lvert\partial\rvert/\binom{n}{t-j} \approx (c/\sqrt k)^{n/(2k-2)}$.

So for the extremal examples, the missing $\log k$ is entirely a *shadow* phenomenon. A
random set of $(1 - \frac1{k-1})t$ vertices is very unlikely to lie inside any minimum
transversal.

**Shadow target.** Show that for $\tau = n/2$ and $j = \lceil t/(k-1)\rceil$,
$$\Pr_{\lvert Y\rvert = t-j}\bigl[\,Y \subseteq X \text{ for some } X \in \mathcal X\,\bigr] \le k^{-ct/k}.$$
With `shadow_branch` this gives the conjecture.
- It is sufficient, not necessary. It could fail for hypergraphs with few minimum transversals
  whose shadow is still large. A version weighted by $\mathrm{ext}$ is both necessary and
  sufficient.
- **Sequential form (exact).** Being extendable is closed under subsets, so if $Y$ is built
  from a random order of the vertices,
  $$\Pr[Y \text{ extendable}] = \mathbb E \prod_{s < t-j} \Bigl(1 - \frac{\lvert F(Y_s)\rvert}{n-s}\Bigr).$$
  Here $F(Y)$ is the set of *forbidden* vertices: zeros of every minimum transversal
  containing $Y$. The shadow target asks for forbidden mass of order $\frac{\log k}{k}\, n$
  on average along the way.
- In the blocks, the forbidden vertices are the rest of each saturated block.

**Two barriers, recorded so they are not rediscovered.**
- *Both one-level methods meet the same local extremal structure.* `harris_ppz` (§6a) and
  `shadow_branch` share the leading constant $\frac{1}{2\ln 2}$. Both are tight when each
  residual is a perfect $k$-matching, that is, each one has a private critical edge. An
  improvement must show that this local picture cannot be typical when $\tau = n/2$.
- *The exchange recursion is too weak by itself.* Fix $X \in \mathcal X$. Every minimum
  transversal is $(X \setminus D) \cup W$ with $\lvert W\rvert = \lvert D\rvert$, where $W$
  covers $L_D = \lbrace e \setminus X : \emptyset \ne e \cap X \subseteq D\rbrace$. Minimality
  of $\tau$ gives the Hall-type condition $\tau(L_D) \ge \lvert D\rvert$ for every $D$. The
  resulting recursion
  $M_k(N,s) \le \sum_d \binom sd M_{k-1}(N-s,d)$
  is exact for $k=2$. But bounding each $L_D$ by the worst rank-$(k-1)$ hypergraph separately
  halves the $\log k$ loss at every level, and with only trivial inputs it gives $k^{s}$. The
  family $D \mapsto L_D$ is monotone and satisfies Hall's condition for all $D$ at once; any
  use of the recursion has to exploit that joint structure.

## 6c. Local certificates: a sufficient condition (proved by hand)

**Local lower bound for $\tau$.** Let $\lbrace w_B\rbrace$ be a fractional partition of $V$
($w_B \ge 0$ and $\sum_{B \ni v} w_B = 1$ for every $v$). Write $\tau_B = \tau(H[B])$, where
$H[B]$ has the edges inside $B$. Each $X \cap B$ is a transversal of $H[B]$, so

$$\lvert X\rvert = \sum_B w_B \lvert X \cap B\rvert \ge \sum_B w_B\,\tau_B, \qquad\text{hence}\qquad \tau(H) \ge \sum_B w_B\,\tau_B.$$

Call $\Delta = \tau(H) - \sum_B w_B \tau_B \ge 0$ the *deficit* of the certificate, and
$W = \sum_B w_B$ its *weight*.

**Theorem (local certificates, by hand; any rank).** Suppose $\Delta = \varepsilon W$ and every
$\lvert B\rvert \le b$. Then the number of minimum transversals is at most

$$2^{\,n - W\left(\frac12\log_2\frac{\pi b}{2} \,-\, \varepsilon\log_2\frac{e}{\varepsilon} \,-\, O(\varepsilon)\right)}$$

when the blocks have size about $b$. In general, each block saves
$\frac12\log_2\frac{\pi\lvert B\rvert}{2}$.

*Proof sketch.* Let $X$ be a uniform minimum transversal and $e_B = \lvert X\cap B\rvert - \tau_B \ge 0$.
1. Since $\lvert X\rvert = \tau(H)$, $\sum_B w_B e_B = \Delta$.
2. By Shearer's lemma for the fractional cover, $H(X) \le \sum_B w_B H(X_B)$.
3. Each term splits as $H(X_B) \le H(e_B) + \mathbb E\log_2\binom{\lvert B\rvert}{\tau_B + e_B}$, and
   $\log_2\binom{m}{i} \le m - \frac12\log_2\frac{\pi m}{2}$.
4. The entropy of a nonnegative integer with mean $\mu$ is at most $\mu\log_2(e/\mu) + O(\mu)$
   for small $\mu$. By concavity, $\sum_B w_B H(e_B) \le W \varepsilon \log_2(e/\varepsilon) + O(\varepsilon W)$.
   $\square$

**Checks.**
- For disjoint blocks $K_{2k-2}^{(k)}$, the blocks themselves are a certificate with
  $\Delta = 0$, $W = n/(2k-2)$ and $b = 2k-2$. The bound is then exactly the blocks' count,
  because Shearer's lemma for a partition is the product formula.
- Regular overlapping covers by cliques $K_{2k-2}^{(k)}$ have $w_B = 1/r$ and $\Delta = 0$.
  So among them the disjoint blocks are optimal, as in §4.
- The rank does not appear. It enters only through the existence of a certificate with
  $b = O(k)$: blocks of size $k^{C}$ would save only $W\log k \approx (n/k^C)\log k$.

**So the conjecture reduces to a structural dichotomy.**

> **Certificate conjecture.** If $\tau(H) = n/2$, the rank is $k$, and $H$ has at least
> $2^{\,n - \delta n\log k/k}$ minimum transversals, then $H$ has a fractional partition into
> sets of size $O(k)$ with deficit at most $\varepsilon n/k$.

By the theorem this implies $S_k(n) \le 2^n k^{-\Omega(n/k)}$.

- **It is the right shape.** Blocks satisfy it with $\Delta = 0$. Local count rigidity, which is
  the $\frac12\log k$ per block of §6b, is exactly the equality case of the local bound.
- **The boundary case** (superseded by §6d: this graph is inside the sharpened range, and the
  real rigid model is $K_m^{(k)}$ plus isolated vertices). The graph $K_{t+1}$ plus $t-1$ isolated vertices ($k=2$, §5) has
  $\tau = n/2$ for a *global* reason. Its best local certificates have deficit about
  $t/b = n/(2b)$, just outside the theorem's range. Its count is only $t+1$, so the remaining
  case is "globally rigid hypergraphs have few minimum transversals". That half is where a
  proof has to do real work, and it is a cleaner question than Question C.
- **Formalization.** Shearer's lemma is now formal (2026-10-17), in two parts.
  - `Shearer_Sub.thy`: `shearer_sub`, Shearer for any set function on subsets of
    $\lbrace 0,\dots,n-1\rbrace$ with $h(\emptyset) = 0$, nonnegative prefix increments and
    diminishing increments (the Madiman–Tetali form). The proof is prefix telescoping.
  - `Shearer_Entropy.thy`: `ent F B` is the entropy (in nats) of the trace $X\cap B$ for $X$
    uniform on a finite family $F$, defined by class counts.
    - `ent_sub`: submodularity. It follows from $\ln y \le y-1$ and the class-counting bound
      `count_bound`, which groups by the trace on $A'$ and splits on $i$.
    - `shearer_ent`: $\ln\lvert F\rvert \le \sum_B w_B\, H(X_B)$ for every fractional cover.
  - The trace (combinatorial) form was expected not to do, because the gain comes from the
    distribution of $\lvert X\cap B\rvert$, which traces cannot see. No example yet confirms
    this (§6g): in the blocks, deep payments and the rigid model, the trace already saves.
  - Steps 3 and 4 are formal too (`Shearer_Concentration.thy`, `Shearer_Certificate.thy`,
    2026-10-17). So the whole theorem, in its sharpened §6d form, is formal; see §6d.

## 6d. The certificate theorem sharpened, and the rigid model cases (by hand, 2026-10-15)

**Concentration form.** Let $X$ be a uniform minimum transversal and $\lbrace w_B\rbrace$ a
fractional partition of $V$. Shearer's lemma, the chain rule
$H(X_B) \le H(\lvert X\cap B\rvert) + \mathbb E\log_2\binom{\lvert B\rvert}{\lvert X\cap B\rvert}$
and $\log_2\binom mi \le m - \frac12\log_2\frac{\pi m}{2}$ (valid for all $m \ge 1$) give
$$\log_2\lvert\mathcal X\rvert \le n - \sum_B w_B\Bigl(\tfrac12\log_2\tfrac{\pi\lvert B\rvert}{2} - H(\lvert X\cap B\rvert)\Bigr).$$
No $\tau_B$ appears. The count is small as soon as the block sizes $\lvert X\cap B\rvert$ are
concentrated, to entropy below $\frac12\log_2\lvert B\rvert$, on a fractional partition into
$O(k)$-sets. Local transversal numbers are one reason for concentration; global minimality can
be another.

**[F] (2026-10-17), in nats, for any finite family and any fractional cover.** `shearer_conc`
in `Shearer_Concentration.thy` states:
$$\ln\lvert F\rvert \le \sum_B w_B\Bigl(\lvert B\rvert\ln 2 - \tfrac12\ln\tfrac{3\lvert B\rvert+2}{2} + H(\lvert X\cap B\rvert)\Bigr).$$
- The constant $\frac{3b+2}{2}$ replaces $\frac{\pi b}{2}$; it comes from `central_ratio` in
  `Binomial_Estimates`.
- The chain-rule step is `group_bound`: if a labelling $g$ determines $f$, then
  $H(g) \le H(f) + \mathbb E\ln(\#g\text{-values in the }f\text{-class})$. The instance
  `ent_count` bounds the count by $\binom{\lvert B\rvert}{\lvert X\cap B\rvert}$.
- For a fractional partition, $\sum_B w_B\lvert B\rvert = n$, and this is the display above.
- The family need not consist of minimum transversals. Any $F$ works, which is what (R)
  and (R$_Y$) need.

**[F] The sharpened certificate theorem (2026-10-17).** `certificate` in
`Shearer_Certificate.thy`: suppose every $X \in F$ has $\lvert X\cap B\rvert \ge t_B$ on each
block of a fractional cover. Then for every $0 < \theta < 1$,
$$\ln\lvert F\rvert \le \sum_B w_B\Bigl(\lvert B\rvert\ln 2 - \tfrac12\ln\tfrac{3\lvert B\rvert+2}{2}\Bigr) - W\ln(1-\theta) - \Delta\ln\theta,$$
with $W = \sum_B w_B$ and $\Delta = \sum_B w_B\,\mathbb E(\lvert X\cap B\rvert - t_B)$.
- The integer-entropy step is Gibbs' inequality against the geometric distribution
  $(1-\theta)\theta^{j}$ (`gibbs`, `int_entropy`). With one $\theta$ for all blocks, no concavity
  argument is needed.
- $\theta = \Delta/(W+\Delta)$ gives $-W\ln(1-\theta) - \Delta\ln\theta = W h(\Delta/W)$ (in nats),
  the display below.
- $t_B$ can be any lower bound, not just $\tau(H[B])$. Bounds that fail on a small part of
  $F$, and the two-sided deviation form, are formal too (§6g).

**Certificate form, sharpened.** Write $e_B = \lvert X\cap B\rvert - \tau_B \ge 0$, so that
$H(\lvert X\cap B\rvert) = H(e_B)$ and $\sum_B w_B\,\mathbb E e_B = \Delta$. A nonnegative
integer with mean $\mu$ has entropy at most
$h(\mu) = (\mu+1)\log_2(\mu+1) - \mu\log_2\mu \le \log_2(e(\mu+1))$. By concavity,
$$\log_2\lvert\mathcal X\rvert \le n - \sum_B w_B\,\tfrac12\log_2\tfrac{\pi\lvert B\rvert}{2} + W\,h(\Delta/W).$$
- For $\Delta = \varepsilon W$ with $\varepsilon$ small this is the §6c theorem. But
  $\varepsilon$ need not be small. With blocks of size $b$ the saving stays positive while
  $1 + \Delta/W < \sqrt{\pi b/2}/e$.
- With $b = \Theta(k)$ and $W = \Theta(n/k)$, any deficit $\Delta \le n\,k^{-1/2-\eta}$ still
  gives a saving of $\Omega(\eta\, n\log k/k)$. The §6c requirement $\Delta \le \varepsilon n/k$
  was much stronger than needed.
- **At $\tau = n/2$ the deficit is a local shortfall.** Since $\sum_B w_B\lvert B\rvert = n = 2\tau$,
  $$\Delta = \sum_B w_B\, s_B, \qquad s_B = \tfrac12\lvert B\rvert - \tau_B.$$
  So the certificate conjecture asks for a fractional partition into $O(k)$-sets $B$ whose local
  transversal numbers are, on weighted average, within $k^{1/2-\eta}$ of $\lvert B\rvert/2$.

**Boundary cases, revisited.**
- *$K_{t+1}$ plus $t-1$ isolated vertices* ($k = 2$) is **not** a boundary case. Blocks with half
  of their vertices in the clique have $s_B = 1$, so $\Delta/W \approx 1$, inside the sharpened range.
  §6c called it "just outside the range" only because it stated the small-$\varepsilon$ form.
- *$K_m^{(k)}$ plus $m-2k+2$ isolated vertices* ($k \ge 3$, $m \to \infty$) has $\tau = m-k+1 = n/2$
  and only $\binom{m}{k-1}$ minimum transversals. It **is** the rigid model case. A block with $a$
  clique vertices has $\tau_B = \max(0, a-k+1)$, so $s_B \ge \frac{p_B - a_B}2 + \min(a_B, k-1)$,
  where $p_B$ is its number of isolated vertices. Summing, and using $\min(a, k-1) \ge a(k-1)/b$,
  every certificate into $b$-sets has $\Delta \ge (k-1)(m/b - 1)$. That is a shortfall of about
  $(k-1)/2$ per block, against the $\sqrt b$ the theorem tolerates; only $b \gtrsim k^2$ would
  certify it, with a negligible saving. The concentration form does see it: $V \setminus X$ is
  the padding plus a random $(k-1)$-subset of the clique, so $\lvert X\cap B\rvert$ is nearly
  deterministic for most blocks. Here concentration comes from global minimality.
- *A test case where $\tau = n/2$ is reached non-locally* (cycle of payments). Take blocks
  $B_1,\dots,B_N$ of size $2k-2$. Let $H[B_i] = K_{2k-2}^{(k)} - e_i$, so $\tau_{B_i} = k-2$,
  attained only by $B_i \setminus e_i$. Fix $A_i \subset e_i$ with $\lvert A_i\rvert = k-1$, a
  cyclic permutation $\pi$, and a $k$-set $G_i \subseteq B_{\pi(i)}$. Add the edges
  $A_i \cup \lbrace g\rbrace$ for $g \in G_i$.
  - *$\tau = N(k-1) = n/2$.* A block with $\lvert X\cap B_i\rvert = k-2$ misses $A_i$, so
    $X \supseteq G_i$ and $B_{\pi(i)}$ carries an excess. Since $\pi$ is injective, the excesses
    pay for the deficiencies.
  - *The count is that of the blocks, up to a factor $(1 - 1/\binom{2k-2}{k-1})^N$.* Every choice
    of $(k-1)$-sets $S_i$ with $S_i \cap A_i \ne \emptyset$ is a minimum transversal.
  - *What certifies it.* Each block alone has $s_B = 1$, so $\Delta/W = 1$. The sharpened theorem
    certifies it (for $k$ large enough that $\frac12\log_2(\pi(k-1)) > h(1) = 2$), but the
    small-$\varepsilon$ form of §6c does not.

**The certificate conjecture must be read with $\delta$ below the true constant.** Mix disjoint
blocks $K_{2k-2}^{(k)}$ with copies of the rigid model case on a fraction $\alpha$ of the vertices.
The count is $2^{\,n - \frac{n}{4k}\log_2 k\,(1+o(1)) - \alpha n}$, and every $b$-certificate has
$\Delta \gtrsim \alpha n (k-1)/(2b)$.
- With $\alpha = \Theta(1/k)$ this is a hypergraph with near-extremal count and deficit
  $\Theta(n/k)$. So the conjecture's hypothesis "$\ge 2^{\,n-\delta n\log k/k}$" is only
  meaningful for $\delta$ below the constant of the blocks.
- At the *sharpened* threshold $\Delta \approx n k^{-1/2-\eta}$, however, the rigid part needs
  $\alpha \gtrsim C k^{-1/2-\eta}$ and costs $\alpha n \gg n\log k/k$ bits. In every example so far,
  deficit costs at least a constant number of bits per unit. ($\Delta \approx m/C$ costs about
  $2m$ bits in the rigid model with $b = Ck$.)

> **Deficit conjecture** (refuted in §6e). For rank $k$, $\tau = n/2$ and $b = Ck$, let $\Delta_b$ be the least
> deficit of a fractional partition into $b$-sets. Then
> $\log_2\lvert\mathcal X\rvert \le n - \lambda_k\,\Delta_b$ with $\lambda_k \ge k^{-1/2+2\eta}$.

With the sharpened theorem this gives $S_k(n) \le 2^n k^{-\Omega(n/k)}$: either
$\Delta_b \le n k^{-1/2-\eta}$, and Shearer saves $\Omega(\eta\, n\log k/k)$, or the deficit term
saves $n k^{\eta}/k$. The examples suggest $\lambda_k = \Theta(1)$, far more than needed. Unlike
the certificate conjecture, it is additive: rigid regions pay for themselves wherever they are.

**The union lemma of §8 is false for $k \ge 3$.**
- *Reduction.* Deleting an edge that does not lower $\tau$ keeps every minimum transversal a
  minimum transversal. So the union $U(H)$ of the minimum transversals lies inside the vertex set
  of a $\tau$-critical subhypergraph with the same $\tau$.
- *Counterexample* (standard; see the provenance below). Add $k-2$ private new vertices to each edge of $K_{t+1}$. The result $H$ has
  rank $k$ and $\tau(H) = t$: replacing private vertices by clique vertices turns a smaller
  transversal into a vertex cover of $K_{t+1}$ of size $< t$. It is $\tau$-critical. Every
  private vertex of $uv$ lies in a minimum transversal: take it together with the $t-1$ clique
  vertices other than $u, v$. So $\lvert U(H)\rvert = t+1 + (k-2)\binom{t+1}{2}$, which exceeds
  $k\tau$ already at $k = 3$, $t = 3$.
- *For graphs it holds* ($\lvert U\rvert \le 2\tau$). Fix a minimum cover $C$ and $I = V\setminus C$.
  Any other minimum cover is $(C\setminus D)\cup W$ with $D$ independent, $W \subseteq I$,
  $W \supseteq N_I(D)$ and $\lvert W\rvert = \lvert D\rvert$. Minimality gives
  $\lvert N_I(D)\rvert \ge \lvert D\rvert$ for independent $D$, so $W = N_I(D)$ with $D$ *tight*.
  Submodularity of $N_I$, with Hall applied to the independent set $D_1\cap D_2$, shows that a union
  $S$ of tight sets has $\lvert N_I(S)\rvert \le \lvert S\rvert \le \tau$. Hence
  $\lvert U\rvert \le 2\tau$, that is $\lvert\mathrm{core}\rvert \ge \alpha - \tau$.
- *Provenance* (literature check of 2026-10-15; the notes are kept uncommitted).
  - The graph bound is classical. It follows from Erdős–Gallai 1961 ($\tau$-critical graphs
    without isolated vertices have $\le 2\tau$ vertices) and from the Hajnal–Folkman lemma.
    Boros–Golumbic–Levit (DAM 124, 2002) prove the stronger
    $\lvert\mathrm{core}\rvert \ge \alpha - \mu + 1$ for connected $G$ with $\alpha > \mu$.
  - For rank $r$, the largest union is the largest order $v_{\max}(r,\tau)$ of a $\tau$-critical
    hypergraph, which is $\Theta(\tau^{r-1})$ (Gyárfás–Lehel–Tuza, JCTB 1982).
  - The counterexample at $k = 3$ has $\binom{t+2}{2}$ vertices. That is the standard
    construction, conjectured extremal by Szemerédi–Petruska (1972) and asymptotically confirmed
    by Kézdy–Lehel (2023). Damaschke–Molokov (2009) bound unions of minimal hitting sets directly.
  - The concentration form (Shearer plus the chain rule on $\lvert X\cap B\rvert$) uses standard
    ingredients. It was not found applied to counting minimum transversals (about 65%
    confidence); a referee would likely call it routine.
- In the sequential form of §6b, the non-forbidden vertices are $U(H_Y)$ for the residual $H_Y$.
  The counterexample shows $\lvert U(H_Y)\rvert$ can grow like $\tau(H_Y)^2$, so this route
  bounds $F(Y)$ only when very few ones remain free.

## 6e. Deep payments: the deficit conjecture is false [F in part], 2026-10-16

*Formal* (`Deep_Payment.thy`, audited):
- `dp_forces`: a deficient block forces the next one.
- `dp_tau`: every finite transversal has $\ge N(k-1)$ vertices.
- `dp_normal`, `dp_count`: at least $\lvert\mathrm{good}\rvert^N$ transversals of size $N(k-1)$.

*By hand:* the Hoeffding estimate of $\lvert\mathrm{good}\rvert$ and the shortfall bound for small sets.

**Construction.** Let $k$ be large, $s = \lfloor k/4\rfloor$, and $N > b$. Take blocks
$B_1,\dots,B_N$ of size $2k-2$, a cyclic permutation $\pi$ of $[N]$, and sets $R_i \subseteq B_i$
with $\lvert R_i\rvert = k-1+s$. The edges are:
- *inside $B_i$:* every $k$-subset of $B_i$ not contained in $R_i$;
- *payments:* $A \cup \lbrace g\rbrace$ for every $(k-1)$-subset $A \subseteq R_i$ and every $g \in B_{\pi(i)}$.

The rank is $k$ and $n = N(2k-2)$.

**$\tau = N(k-1) = n/2$.**
- If $\lvert X\cap B_i\rvert < k-1$, the complement $B_i \setminus X$ has $\ge k$ vertices and
  contains no inside edge, so it lies in $R_i$. It contains a $(k-1)$-set $A \subseteq R_i$ that
  $X$ misses. The payment edges then force $X \supseteq B_{\pi(i)}$, an excess of $k-1$ there.
  The deficiency of $B_i$ is at most $s \le k-1$, and $\pi$ is injective, so
  $\lvert X\rvert \ge N(k-1)$.
- Conversely, every choice of $(k-1)$-sets $S_i \subseteq B_i$ with
  $\lvert S_i\cap R_i\rvert \ge s+1$ is a transversal. Its complement in $B_i$ has only $k-1$
  vertices, and $\lvert R_i\setminus S_i\rvert \le k-2$, so it meets every $A$.

**The count is that of the blocks.** $\lvert S\cap R_i\rvert$ is hypergeometric with mean
$(k-1+s)/2 \approx 5k/8$, so $\Pr[\lvert S\cap R_i\rvert \le s] \le e^{-ck}$ by Hoeffding. Hence
$$\lvert\mathcal X\rvert \ge \Bigl(\tbinom{2k-2}{k-1}(1 - e^{-ck})\Bigr)^N = 2^{\,n - \frac{n}{4k}\log_2 k\,(1+o(1))},$$
which is the count of disjoint $K_{2k-2}^{(k)}$ blocks to leading order.

**Every small set falls short by a lot: $s_B \ge \frac{s}{4b}\lvert B\rvert$ whenever $\lvert B\rvert \le b < N$.**
- *Reduction to paths.* Write $m_i = \lvert B\cap B_i\rvert$. $B$ meets fewer than $N$ blocks, so
  the blocks it meets form $\pi$-paths $i_1 \to \dots \to i_j$. $H[B]$ is a disjoint union over
  these paths, so it suffices to find, for each path $P$, a transversal of size
  $\le \lvert P\rvert/2 - \min(s/4, \lvert P\rvert/2)$.
- *Normal parts.* A part with a vertex outside $R$ can keep $\min(m, k-1)$ vertices out of $X$:
  at most $k-2$ in $R$, plus one outside. That meets its inside edges and every $(k-1)$-set
  $A \subseteq R$, so its outgoing payments are met. The part's shortfall is
  $\min(m,k-1) - m/2 \ge 0$. A part inside $R$ keeps $\min(m,k-2)$ out, with shortfall at least
  $\min(m/2, (k-3-s)/2) \ge 0$.
- *Small parts* ($m < s/2$). They have no inside edges, and no $A$, since $\lvert R\cap B\cap B_i\rvert < k-1$.
  They cost nothing and fall short by $m/2$.
- *The last non-small part* $q$, scanning back from the end of the path:
  - If $q$ is the end, its local optimum $\min(a, m-k+1)^+$, with $a = \lvert (B\cap B_q)\setminus R_q\rvert \le k-1-s$,
    falls short by at least $s/4$. For $m \ge k-1$, the two options average $(k-1-a)/2 \ge s/2$.
  - If $q$ is not the end and $m_q \le 2k-2-s$, the normal choice falls short by at least
    $\min(m_q/2, k-1-m_q/2) \ge s/4$. For a part inside $R$ the shortfall is
    $(k-3-s)/2 \ge s/4$.
  - If $q$ is not the end and $m_q > 2k-2-s$, make it deficient. Take $X_q = (B\cap B_q)\setminus R_q$,
    which falls short by $> s/2$, and pay with all of the small part $q+1$, which costs $< s/4$.
    Later parts are small, and their incoming payments are met because $R\cap B_{q+1} \subseteq X$.
  - If there is no non-small part, the whole path falls short by $\lvert P\rvert/2$.
- Summing over a fractional partition gives $\Delta_b \ge s n/(4b)$ for every $b < N$.

**Consequences.**
- *The deficit conjecture of §6d is false.* With $b = Ck$, $\Delta_b \ge n/(16C+o(1))$ is linear
  in $n$, yet $\log_2\lvert\mathcal X\rvert = n - \Theta(n\log k/k)$. So $\lambda_k = O(C\log k/k)$,
  not $\ge k^{-1/2+2\eta}$.
- *Local-$\tau$ certificates of any block size are off by about a factor $k$ here.* The sharpened
  theorem needs $\Delta/W \lesssim \sqrt b$, so $sn/(4b) \lesssim n/\sqrt b$, that is
  $b \gtrsim s^2 \approx k^2/16$. The resulting saving is $O(n\log k/k^2)$, against the true
  $\Theta(n\log k/k)$.
- *The certificate conjecture of §6c is not refuted.* Its hypothesis needs $\delta$ below the
  blocks' constant, and this count sits at that constant. But it cannot be the mechanism: a
  hypergraph can match the extremal count with no near-tight local certificate.
- *The concentration form does see it.* (Corrected 2026-10-17, §6g: deficient blocks do not
  merely occur rarely; they never occur.) In a minimum transversal, a block short by
  $d \le s$ forces a distinct full block, which is $k-1 > s$ over. The other blocks are not
  deficient, so a deficient block would make $\lvert X\rvert > N(k-1)$. Hence
  $\lvert X\cap B_i\rvert = k-1$ for *every* minimum transversal, and `certificate` with
  $t_{B_i} = k-1$ and $\Delta = 0$ gives the full saving. The lower bound $k-1$ is
  worst-case over $\mathcal X$, but it is global: it is not $\tau(H[B_i]) = k-1-s$.

**What survives: typical lower bounds.** In this example and in the rigid model of §6d,
$\lvert X\cap B\rvert$ is pinned *from below* not by $\tau_B$ but by a *typical* lower bound
$\ell_B$, with $\Pr[\lvert X\cap B\rvert < \ell_B]$ small. Deficient configurations are
possible, but they are rare because of what they force elsewhere. (Corrected in §6g: in this
example the bound is global but worst-case; only the rigid model needs the typical form.)
- Given such $\ell_B$ with $\sum_B w_B\ell_B \ge n/2 - \Delta'$, the identity
  $\sum_B w_B\lvert X\cap B\rvert = n/2$ caps the upward deviations too.
- The proof of §6d then goes through with $\Delta'$ in place of $\Delta$, plus an error term from
  the rare deficient events, of about $\sum_B w_B(\Pr[\lvert X\cap B\rvert<\ell_B]\log_2\lvert B\rvert + h_2(\Pr[\lvert X\cap B\rvert<\ell_B]))$,
  where $h_2$ is the binary entropy.

> **Concentration conjecture.** For rank $k$ and $\tau = n/2$, with $X$ a uniform minimum
> transversal, there is a fractional partition into $O(k)$-sets with
> $\sum_B w_B H(\lvert X\cap B\rvert) \le \sum_B w_B (\frac12 - \eta)\log_2\lvert B\rvert$,
> unless $\lvert\mathcal X\rvert \le 2^{\,n - \Omega(n\log k/k)}$ for other reasons.

With the escape clause this is *equivalent* to the conjecture (§6d gives one direction, and the
clause the other), so it is not a reduction. Its value is as a guide to the mechanism. It is a
statement about the distribution of $X$, so it invites switching or comparison arguments ("a
deficient $X$ maps to many normal ones"), which is how the counts in both examples are
explained. A genuine reduction would name the $\ell_B$ in advance, from the structure of $H$.

**What any Shearer-type proof needs.** Shearer bounds $\log_2\lvert\mathcal X\rvert$ by
$\sum_B w_B H(X_B)$. So such a proof works exactly when:

> **(R)** Every $H$ with rank $k$ and $\tau = n/2$ has a fractional partition into $O(k)$-sets
> with local entropy deficit $\sum_B w_B(\lvert B\rvert - H(X_B)) \ge c\,n\log k/k$.

- (R) is stronger than the conjecture. It would fail for a family of minimum transversals that
  looks locally uniform but is constrained globally, like a code.
- Monotonicity makes exact local uniformity impossible: $X$ meets every edge, so each edge
  forbids one pattern. But that pattern alone costs only about $2^{-k}$ bits.
- *The worst-case version* (corrected 2026-10-17, §6g). It was claimed here that the trace
  $\lbrace X\cap B : X \in \mathcal X\rbrace$ saves only about one bit per block on deep
  payments, because the excess patterns occur rarely. That is wrong: they never occur, so on
  the blocks $B_i$ the trace consists of $(k-1)$-sets and saves $\frac12\log_2 k$ per block.
  The trace form also suffices in the rigid model: isolated vertices are never in $X$, so a
  block with $a_B$ clique vertices has at most $2^{a_B}$ patterns. So no example yet separates
  the trace form from the entropy form (§6g).
- *Open, and worth settling first:* is there a monotone, "code-like" $H$ with $\tau = n/2$ and
  local entropy deficit $o(n\log k/k)$ for every $O(k)$-partition? If its count were large,
  it would refute the conjecture; if small, it would kill only the Shearer route. Both
  examples so far (blocks, deep payments) put their entire deficit inside $O(k)$-blocks.
  *Settled for constructions in §6f; for (R), reformulated there.*

## 6f. Links: the code-like question is the problem itself [F in part], 2026-10-16

**Links.** Split $V = G \sqcup Y$, where $Y$ is the set of *helpers*. For $S \subseteq Y$ let
the link be $H_S = \lbrace e - Y : e \in H,\ e\cap S = \emptyset\rbrace$, a hypergraph on $G$ of
rank $\le k$ (`link_rank`). Let $X$ be a minimum transversal and $S = X\cap Y$.
- $X - Y$ is a transversal of $H_S$ (`link_tr`).
- If $T$ is a transversal of $H_S$, then $S\cup T$ is a transversal of $H$ (`link_back`). So
  $X - Y$ is a *minimum* transversal of $H_S$ (`link_mint`).
- **Link count [F].** `link_count`: if every link has at most $M$ minimum transversals of size
  $j$, then at most $2^{\lvert Y\rvert}M$ minimum transversals of $H$ have
  $\lvert X - Y\rvert = j$. The map $X \mapsto (X\cap Y,\ X-Y)$ is injective.
- **Link identity (by hand).** Conversely, a minimum transversal $T$ of $H_S$ of size
  $\tau - \lvert S\rvert$ gives a transversal $S\cup T$ of size $\tau$, which is minimum. So,
  given $X\cap Y = S$, the set $X - Y$ is a *uniform* minimum transversal of $H_S$, and
  $$n - \log_2\lvert\mathcal X\rvert = \bigl(\lvert Y\rvert - H(X_Y)\bigr) + \mathbb E_S\bigl[\lvert G\rvert - \log_2\lvert\mathrm{mint}(H_S)\rvert\bigr].$$
  The loss is the selectors' entropy deficit plus the average loss of the links. The problem
  is closed under conditioning on helpers.

**Consequence for constructions: no cheap gadgets unless the conjecture already fails.**
Suppose a gadget on a group $G$ of size $m$, with $h$ helpers, puts a near-uniform
"exactly half" on $G$. Then its minimum transversals cover a constant fraction of the
$m/2$-subsets of $G$. By `link_count` with $j = m/2$, and since each link with such a minimum
transversal has $\tau = m/2$:
$$\binom{m}{m/2} \lesssim 2^h S_k(m), \quad\text{that is,}\quad h \gtrsim m - \log_2 S_k(m) - \tfrac12\log_2 m.$$
- The helper configurations are exactly the CNFs of a $\Sigma_3^k$ cover of the $m$-slice.
  So $h$ is at least the log of the depth-3 Majority size at $m$ variables, up to $O(\log m)$.
- More generally, by the identity, a gadget's total loss is at least the average loss of its
  links, so disjoint copies of a gadget never beat the best hypergraph on $m$ vertices.
- So the constructive branch of the code-like question of §6e *is* the conjecture at size
  $m$: the Majority lower bound in another guise, as anticipated. Nothing further to do there.

**Consequence for (R): mixtures, and the conditional form.**
- The identity shows how code-like families arise. $X_G$ is a *mixture* over $S$ of uniform
  minimum transversals of the links. Entropy is concave, so
  $H(X_B) \ge \mathbb E_S H(X_B \mid S)$: mixing *washes out* local deficits. If different
  selector values gave links with blocks on different partitions of $G$, then every
  $O(k)$-set of $G$ would look nearly uniform, while each link is block-structured.
- So (R) can fail for a reason that has nothing to do with the count. Whether such
  hypergraphs exist is not known: realizing them is constrained, since
  $S \subseteq S'$ implies $H_S \supseteq H_{S'}$.
- **(R$_Y$), conditional form.** Conditioning on the selectors undoes the mixing, *provided
  the partition may depend on the selector value*.
  - Apply Shearer to each link separately, with its own fractional partition $w^S$ of $G$.
    With the identity this gives
    $$n - \log_2\lvert\mathcal X\rvert \ \ge\ \bigl(\lvert Y\rvert - H(X_Y)\bigr) + \mathbb E_S \sum_B w^S_B\bigl(\lvert B\rvert - H(X_B \mid X_Y = S)\bigr).$$
  - For $Y = V$ this is the identity, a tautology. The selector term is the original problem on
    $Y$. So the route drops it (it is $\ge 0$) and needs some $Y$, and for each $S$ some
    $O(k)$-partition $w^S$, whose *link part* $\mathbb E_S\sum_B w^S_B(\dots)$ is
    $\ge c\,n\log k/k$.
  - For $Y = \emptyset$ this is (R).
  - It is weaker than (R), and it still implies the conjecture.
  - It is immune to selector mixtures, since $w^S$ can follow $\pi_S$. A *fixed* partition
    would not be: conditionally on $S$, a fixed $O(k)$-set still meets the blocks of $\pi_S$
    in a spread way, and still looks nearly uniform.
- **It is not a tautology.** The partition covers only $V - Y$, so
  $\lvert V - Y\rvert \ge c\,n\log k/k$ is needed.
  - Take $G = V - Y$ uniformly random of size $g$. Han's inequality gives
    $\mathbb E\, H(X_G \mid X_{V-G}) \le (g/n)\log_2\lvert\mathcal X\rvert$.
  - So $G$ *as a single block* has conditional deficit $\ge (g/n)(n - \log_2\lvert\mathcal X\rvert)$.
    That is only a $g/n$ fraction of the loss. An $O(k)$-partition of $G$ gives less, by
    subadditivity.
  - So the content lies in the $O(k)$ restriction together with a structural choice of $Y$.
- **Next test:** a selector-mixture hypergraph, if one can be realized. For blocks and deep
  payments, $Y = \emptyset$ already works.

**Selector mixtures as set systems (2026-10-17; exact part [F], rest heuristic).** The
model:
- There are $P$ partitions $\pi_p$ of $G$, each with blocks of rank $k-a$.
- A group edge $f$ of $\pi_q$ is realized as $f\cup A_f$, with $A_f \subseteq Y$ and
  $\lvert A_f\rvert \le a$.
- Selector $p$ is a helper configuration $S_p$. It should keep $\pi_p$ alive and kill the
  other partitions. Write $C_p = Y - S_p$.

Three constraints follow.
- **"All on" attack (by hand).** A helper in $X$ only satisfies edges, never creates them. So
  $S_p$ together with a transversal of $\lbrace A_f : f\in\pi_p\rbrace$ kills everything.
  - Hence the helper sets of $\pi_p$ need, as a rank-$a$ hypergraph on $C_p$, transversal
    number $\ge m/2$.
  - So the helper side must contain a copy of the group's difficulty (*self-similarity*), and
    in particular $h \gtrsim m$.
- **Switching is a Bollobás set-pair condition.** $A_f \cap S_q = \emptyset$, and
  $A_f\cap S_p \ne\emptyset$ for $p\ne q$. So $P \le \binom{a+s}{a}$ with $s = \lvert S_p\rvert$
  (Bollobás 1965; skew form: Frankl, Kalai, Lovász).
  - A random $A_f$ needs $a \gtrsim \log_2 P$. Structured ones need far fewer.
  - In complement form: each block $C_p$ has a *private* $a$-set (one inside $C_p$ and inside
    no other block). For $a = 2$ this is the graph version: each block spans exactly one
    designated edge, its own.
- **Exact local uniformity is a design condition, and it kills switching [F].**
  - If the selectors are exactly $t$-wise uniform, the $C_p$ form a $t$-design, so for
    $t \ge a$ all $a$-sets lie in equally many blocks.
  - `private_design`: then one private $a$-set makes every $a$-set lie in at most one block,
    so two blocks share fewer than $a$ points (a partial Steiner system).
  - `three_blocks`, `half_blocks`: three such blocks of size $\ge h/2$ force $h < 6a$.
  - So exact strength $t \ge a$ is incompatible with switching, beyond two selectors. The
    numerical bounds (Rao: $P \gtrsim \binom{h}{t/2}$; Bollobás) looked compatible, but the
    structure is not.
- **Why this does not settle (R).** (R) is entropic. A private $a$-set only makes one
  pattern on $A$ rare (probability $1/P$, not about $2^{-a}$), and that costs about $2^{-a}$
  bits: the same leak as one forbidden pattern per edge (§6e).
  - So approximate designs may carry private subsets almost for free.
  - An obstruction to (R) by this route must force *many* rare patterns at once, probably via
    self-similarity.
- **Open (heuristic):** is there a family of $h/2$-subsets that is entropically close to a
  $t$-design, with $t$ of order $k$, in which each block has a private $a$-subset ($a < k$), and
  whose helper sets satisfy the self-similarity constraint?
- **Literature (checked 2026-10-17).** Nothing treats near-uniform families in which every
  block has a private subset.
  - Ray-Chaudhuri–Wilson (1975) rules out private $a$-sets at exact strength $t \ge 2a$.
    `private_design` with `three_blocks` covers all $t \ge a$, with no appeal to Tits's
    theorem on Steiner systems.
  - Closest results: Pikhurko (J. Combin. Des. 2001) on minimal coverings, for fixed block
    size only; Horsley–Singh (arXiv:1706.06825), a Ray-Chaudhuri–Wilson bound for coverings;
    Kuperberg–Lovett–Peled (GAFA 2017) for designs with block size $h/2$.
  - No set-pair theorem imposes design or independence conditions on the second sets.
  - Balogh–Bollobás–Narayanan (JCTA 2021) note that no hypergraph analogue of Zhao's
    bipartite reduction is known. The conditioning of (R$_Y$) is in that gap.
- **The approximate case: a dichotomy (by hand).** Let the selectors be uniform over $P$
  values. A private $a$-set lies in a $1/P$ fraction of the blocks, against $p_a \approx 2^{-a}$
  for a uniform half-set. So its $a$-marginal is at total-variation distance
  $\ge p_a - 1/P$ from uniform.
  - *Few selectors:* $P \le 2^{a+1}$. Then every helper block of size $b$ has entropy
    $\le \log_2 P \le a+1$. For $b \ge 2a+2$ the deficit is $\ge b/2$ per block, and (R) holds
    through the helpers, which are at least half of $V$.
  - *Many selectors:* each private $a$-set's marginal is at distance $\gtrsim 2^{-a-1}$, so
    (Pinsker) it has deficit $\gtrsim 2^{-2a}$. Take the fractional partition of $Y$ into all
    its $a$-sets, with weight $1/\binom{h-1}{a-1}$ each. Han's inequality gives a helper
    deficit $\gtrsim (h/a)\,\rho\,2^{-2a}$, where $\rho$ is the fraction of $a$-subsets of $Y$
    that are private.
  - Self-similarity gives at least $Pm/2$ private sets, so $\rho \ge Pm/(2\binom{h}{a})$.
    Bollobás caps $P$ at about $\binom{h}{a}2^{-a}$, so $\rho$ is at most about $m2^{-a}$.
  - So (R) survives selector mixtures unless $P$ lies in a middle range: above $2^{a+1}$, but
    with private sets too sparse to show up after the $2^{-2a}$ discount. The literature leaves
    the same range open (total-variation distance $\gtrsim 2^{-a}$).
  - Pinsker is lossy here; a direct estimate does better (by hand).
    - Force one pattern of uniform probability $q = 2^{-a}$ down to $r \le q/2$. The closest
      distribution spreads the rest uniformly.
    - Its divergence from uniform is $r\ln\frac rq + (1-r)\ln\frac{1-r}{1-q} \approx q(1 - x + x\ln x)$,
      with $x = r/q$. That is $\ge 0.15\,q$ nats, about $0.22\cdot 2^{-a}$ bits.
  - **The direct estimate still does not close the gap, and that is informative.**
    - The helper deficit is now $\gtrsim (h/a)\,\rho\,2^{-a}$. For (R) we need
      $c\,n\log k/k$, with $h \ge n/2$.
    - That requires $\rho \gtrsim a\,2^{a}\log k/k$, which exceeds 1 once $a \gtrsim \log_2 k$.
    - So Han's inequality over private $a$-sets certifies (R) only for rank splits
      $a \lesssim \log_2 k$.
  - **Where an (R)-counterexample would have to live:** selector mixtures with rank split
    $a \gg \log k$ (for instance $a \approx k/2$, group blocks of rank $k/2$), and $P$ in the
    middle range. Such a counterexample needs no good count: it would only kill the
    unconditional Shearer route. (R$_Y$) would survive it.
- **Approximate uniformity is cheap.** Small-bias spaces (Naor–Naor) give nearly $b$-wise
  uniform families on $h$ coordinates with about $2^{O(b)}\log h$ members. So the Rao bound
  $P \gtrsim \binom{h}{b/2}$, valid for exact strength $b$, does not bind entropically.
  Bollobás allows $P$ up to about $(h/2a)^a$.

**Mixing transfers code-likeness; it does not create it (heuristic).**
- When selector $p$ is in force and $\lvert X\cap G\rvert \approx m/2$, the helper part is
  fixed: $X \cap Y = S_p$. So the projection $\lbrace X\cap Y\rbrace$ has entropy
  $\le \log_2 P$.
- By the "all on" attack $h \gtrsim m$, so helpers are at least half of $V$. For (R) to fail,
  the $O(k)$-blocks *of $Y$* must therefore also be nearly uniform.
- So the selector family is itself code-like: locally near-uniform, globally of low entropy.
  It is the projection of the *same* family $\mathcal X$ onto $Y \subsetneq V$, since
  $\min_S(\lvert S\rvert + \tau(H_S)) = \tau(H)$.
- So the regress descends in the vertex set, for one and the same family: code-likeness of
  $\mathcal X$ on $G$ is inherited from its projection on $Y$. That projection may be a
  mixture over a further split $Y = G' \sqcup Y'$, and so on.
- **Consequence for (R):** any failure of (R) bottoms out in a set $Y^*$ on which the
  projection of $\mathcal X$ is code-like *intrinsically*, not by mixing over a further helper
  set.
  - This is a reformulation, not a reduction: the base case is again the code-like question.
  - It does say where to look. A counterexample to (R) needs a part of $V$ whose projected
    family is locally uniform without any selector explaining it.

**The helper-only edges must do the selecting (2026-10-17).** Let
$E_Y = \lbrace e\in H : e\subseteq Y\rbrace$ be the helper-only edges.
- **Slack [F].** `proj_slack`: the helper part $X\cap Y$ of a minimum transversal is a
  transversal of $E_Y$, with $\lvert X\cap Y\rvert \le \lvert S'\rvert + \lvert G\rvert - \lvert X\cap G\rvert$
  for every transversal $S'$ of $E_Y$. So selectors are near-minimum transversals of $E_Y$, with
  additive slack about $m/2$. That alone is weak when $h \approx m$, but a sharper statement
  holds pairwise.
- **Two block structures cost no more than one (by hand, König).** Take partitions
  $\pi_p,\pi_q$ of $G$ into blocks of size $2r-2$, with all $r$-subsets of each block as
  edges.
  - Each element of $G$ is an edge between its $\pi_p$-block and its $\pi_q$-block. This
    gives a $(2r-2)$-regular bipartite multigraph, which splits into perfect matchings
    (König).
  - $r-1$ of these matchings give a set $Z$ of $m/2$ elements with exactly $r-1$ in every block
    of both partitions. $Z$ and its complement both meet every block in $r-1 < r$ elements,
    so $Z$ hits every edge. Hence $\tau(\pi_p\cup\pi_q) = m/2$.
  - For three partitions there is no such theorem, and a common half-set need not exist.
- **Intersection attack (by hand; one typicality assumption).** Assume that under
  $S_p \cap S_q$ only the partitions $p$ and $q$ survive. This holds when every edge of
  every other partition has $A_f \cap S_p\cap S_q \ne \emptyset$; for $\lvert A_f\rvert = a$ it
  is typical, but not automatic.
  - Let $T$ be a transversal of $E_Y$ with $S_p\cap S_q \subseteq T \subseteq S_p\cup S_q$.
    Then $T\cup Z$ is a transversal of $H$. Minimality ($\tau = \lvert S_p\rvert + m/2$) forces
    $\lvert T\rvert \ge \lvert S_p\rvert$.
  - Let $D = S_p\triangle S_q$, and let $E'$ consist of the sets $e\cap D$, for the
    $e\in E_Y$ that miss $S_p\cap S_q$. (Each such $e\cap D$ is nonempty, since $S_p$ hits $e$.)
    Then $\tau(E') = \lvert D\rvert/2$, and $S_p - S_q$, $S_q - S_p$ are complementary minimum
    transversals.
  - **So $E_Y$ carries an "exactly half" instance on every symmetric difference**
    $S_p\triangle S_q$. For locally uniform selectors these have size about $h/2$.
- **The cheapest such $E_Y$ is visible to (R).** A perfect matching on $Y$ satisfies all the
  sandwich conditions at once, for any selector family drawn from its $2^{h/2}$ minimum
  covers. But each matching edge is a 2-set with exactly one helper in $X$, a 1-bit deficit
  per edge, so (R) holds.
  - For a mixture to evade (R), $E_Y$ must have exactly-half structure on every
    $S_p\triangle S_q$ while its minimum covers look locally uniform: $E_Y$ must itself be
    code-like.
  - This is the regress of the previous paragraph, now concrete and without the slack
    problem: a selector mixture is a code-like $E_Y$ on $Y$ plus a group that copies it.
- **What would break the conclusion:** partitions other than $p, q$ surviving under
  $S_p\cap S_q$, which raises $\tau(H_{S_p\cap S_q})$ above $m/2$. The sandwich bound then
  weakens by the excess. Surviving edges need $A_f \subseteq Y - (S_p\cap S_q)$ for many
  pairs at once, which pulls against privacy.
  - **Pair-specific edges are a genuine escape route.** Take a group part $f'$ with a helper
    part $A'$ that meets both $S_p - S_q$ and $S_q - S_p$ and avoids $S_p\cap S_q$. Such an
    edge is dead under $S_p$ and under $S_q$, but alive under their intersection, so it can
    defeat the König set $Z$ without $E_Y$.
  - Every pair needs such edges, against the many König sets $Z$. Their helper parts are
    subsets of $S_p\triangle S_q$ that meet both halves: a "pair-private" condition in place
    of privacy.
  - Whether $P^2$ such families fit within rank $k$, with selectors that stay locally uniform,
    is the next question if this line is pursued.

## 6g. Typical lower bounds and the deviation form [F], 2026-10-17

*Formal* (`Shearer_Typical.thy`, audited). Both theorems hold for any finite family $F$, any
fractional cover and every $0 < \theta < 1$, and both are `gibbs` against a different reference
distribution.
- `int_entropy_typ`, `certificate_typ`: lower bounds $t_B$ that may fail. Let $p_B$ be the
  fraction of $F$ with $\lvert X\cap B\rvert < t_B$, and take any $0 < r_B < 1$. Then the term
  $-\ln(1-\theta) - \Delta_B\ln\theta$ of `certificate` becomes
  $$(1-p_B)\bigl(-\ln(1-r_B) - \ln(1-\theta)\bigr) + p_B(\ln t_B - \ln r_B) - \ln\theta\;\mathbb E(\lvert X\cap B\rvert - t_B)^+ .$$
  The reference puts mass $r_B$ uniformly below $t_B$ and $1-r_B$ geometrically above it. With
  $r_B = p_B$ the cost of the failures is $h(p_B) + p_B\ln t_B$, as predicted in §6e.
- `int_entropy_dev`, `certificate_dev`: the two-sided form. For any centres $c_B$, the reference
  $\frac{1-\theta}{1+\theta}\theta^{\lvert v-c_B\rvert}$ gives
  $$\ln\lvert F\rvert \le \sum_B w_B\Bigl(\lvert B\rvert\ln 2 - \tfrac12\ln\tfrac{3\lvert B\rvert+2}{2}\Bigr) + W\ln\tfrac{1+\theta}{1-\theta} - D\ln\theta, \qquad D = \sum_B w_B\,\mathbb E\bigl\lvert\,\lvert X\cap B\rvert - c_B\bigr\rvert .$$
  When the bounds hold everywhere ($c_B = t_B$), it costs an extra $W\ln(1+\theta)$ against
  `certificate`. But it charges a rare deficiency of depth $d$ and probability $p$ only $pd$
  in $D$, and it needs no lower bound at all. With $x = D/W$ and $\theta = x/(1+x)$, the cost
  is exactly $W\ln(1+2x) + Wx\ln(1+1/x) \le W(\ln(1+2x) + 1)$. So the per-block saving
  $\frac12\ln\frac{3b+2}{2}$ survives while $D/W \lesssim \sqrt b$. For small $x$ the cost is
  about $D(2 + \ln(W/D))$.

**The test cases, redone** (by hand, from the formal statements).
- *Blocks:* $c_B = k-1$, $D = 0$.
- *Deep payments:* $D = 0$ with $c_{B_i} = k-1$, because $\lvert X\cap B_i\rvert = k-1$ for
  every minimum transversal. A deficient block, short by $d \le s$, forces a distinct full
  block, $k-1 > s$ over. This corrects §6e, which said the deficient configurations are rare
  (they never occur) and that the trace form fails there (it does not).
- *Rigid model,* $K_m^{(k)}$ plus $m-2k+2$ isolated vertices. Here $X$ is the clique minus a
  uniform $(k-1)$-set $Z$. Take blocks of size $b$ with $a_B$ clique vertices, and $c_B = a_B$.
  Then $\mathbb E\lvert\,\lvert X\cap B\rvert - a_B\rvert = \mathbb E\lvert Z\cap B\rvert = a_B(k-1)/m$,
  so the *total* is $D = k-1$, while $W = n/b$. Hence
  $$\ln\lvert\mathcal X\rvert \le n\ln 2 - \tfrac nb\cdot\tfrac12\ln\tfrac{3b+2}{2} + (k-1)\Bigl(2 + \ln\tfrac{n}{b(k-1)}\Bigr) + o(1).$$
  The worst-case certificate ($t_B = a_B - (k-1)$) pays about $(k-1)/2$ per block instead.
  `certificate_typ` with $t_B = a_B$ works too: $p_B \le a_B(k-1)/m$, so the failures cost
  $O(k\log n)$ in total.
- *Caveat on the trace.* In all three examples, the worst-case trace form already saves. In
  the rigid model, the isolated vertices are never in $X$, so the trace on $B$ has at most
  $2^{a_B}$ patterns. An example where only the entropy form works needs rare *sizes* that
  carry many patterns each. The obvious attempt, deep payments with $R_i = B_i$, is rigid:
  its only minimum transversals alternate empty and full blocks.

**The size condition.** The deviation form turns the Shearer route into a statement about sizes
alone:

> **(D)** Every $H$ with rank $k$ and $\tau = n/2$, with $X$ a uniform minimum transversal, has a
> fractional partition into $b$-sets, $b = O(k)$, and centres $c_B$ with
> $\sum_B w_B\,\mathbb E\lvert\,\lvert X\cap B\rvert - c_B\rvert \le W b^{1/2-\eta}$.

- (D) implies the conjecture, by `certificate_dev` (proved). The chain rule shows that (D)
  implies (R), so (D) is at least as strong (proved).
- *Flexibility at scale $O(k)$ is harmless* (by hand). If blocks trade size with each other,
  as in "the sizes on $B\cup B'$ sum to $2k-2$", merge them: the union is still an $O(k)$-set
  with zero deviation.
- *Spread at scale $\gg k$ is the code-like case* (heuristic). A size that is spread like a
  binomial over every $O(k)$-set, on a family with many members, needs an "exactly half"
  constraint on groups of size $m \gg k$. By `link_count` (§6f), a cheap gadget of that kind
  exists only if the conjecture fails at size $m$. So (D) and (R) fail on the same kind of
  object, and (D) is the cleaner one to attack: one integer per block.
- *Still open:* a rule naming the partition and centres from the structure of $H$. The two
  mechanisms seen so far are *global payment* (deep payments: a deficit forces a larger
  excess elsewhere) and *spread rigidity* (rigid model: the freedom is a $(k-1)$-set spread
  over $m$ vertices, so each block sees almost none of it).

## 6h. Structure: witness components and the conditional certificate [F in part], 2026-10-17

*Formal* (audited):
- `Shearer_Conditional.thy`:
  - `certificate_cond`: the cover, the centres and $\theta$ may all depend on a label $g(X)$.
    Then $\ln\lvert F\rvert \le H(g) + \mathbb E_X\,\beta(X)$, where $\beta(X)$ is the bound of
    `certificate_dev` for the class of $X$, computed with that class's cover.
    The proof is one line: $\ln\lvert F\rvert = H(g) + \mathbb E\ln\lvert\text{class}\rvert$ is the
    definition of `lent`, and $X$ is uniform on its class.
  - `lent_image`: $H(g) \le \ln\lvert g(F)\rvert$.
- `Mirror_Payment.thy`, a new test case. It has blocks $B_i$ of size $2k-2$, special vertices
  $r_i$, $R_i = B_i - r_i$, and a copy map $\iota$ from $R_i$ onto $R_{\pi(i)}$. The edges are:
  - *inside:* the $k$-subsets of $B_i$ containing $r_i$;
  - *mirror payments:* $A\cup\lbrace\iota(a)\rbrace$ for every $(k-1)$-set $A \subseteq R_i$ and every $a \in A$.

  The theorems:
  - `mp_forces`, `mp_mirror`: a block short by $d$ forces the mirror image of its zeros into
    the next block, an excess of at least $d$.
  - `mp_tau`: $\tau = N(k-1) = n/2$.
  - `mp_deficient`: *every* deficiency level $0 \le d \le k-2$ occurs in a minimum transversal.
    Unlike deep payments, deficient blocks really occur.
  - `mp_trace`: hence the trace on one block has at least $2^{2k-4} = 2^{\lvert B\rvert - 2}$
    patterns.
  - `mp_count`: at least $\binom{2k-3}{k-1}^N$ minimum transversals, which is within one bit
    per block of the disjoint blocks.

**Mirror payments, by hand.**
- *Deficient events are rare.* In a minimum transversal all the accounting is tight. So a
  block of type $D_d$ ($r_i \in X$, zeros $Z' \subseteq R_i$, $\lvert Z'\rvert = k-1+d$)
  makes the next block exactly $\iota(Z')$. Replacing two free blocks
  ($\binom{2k-3}{k-1}^2 \approx 4^{2k-3}/(\pi k)$ choices) by a pair $(D, \iota(Z'))$
  ($2^{2k-4}$ choices) gives $\Pr[\text{block } i \text{ is deficient}] \approx 4\pi k\,4^{-k}$.
  This is a weight comparison, not yet a careful count of the constraints on the neighbours.
  So $D = N\cdot\mathrm{poly}(k)4^{-k}$ with centres $k-1$, and `certificate_dev` gives the full
  per-block saving.
- *The trace form needs merged blocks.* On one block the trace saves at most 2 bits
  (`mp_trace`). On a union of $C$ blocks that are consecutive along $\pi$, only the first block
  can receive from outside. The others are free ($\binom{2k-3}{k-1} = \Theta(4^{k}/\sqrt k)$ patterns each) or
  determined by their predecessor. So the trace saves about $\frac{C-1}{2}\log_2 k - O(C)$.
  This is a mild separation: the entropy form works on single blocks, while the trace form
  loses a boundary block per set. It is not a counterexample to the trace version of (R),
  since $C = O(1)$ is allowed.

**Witness components.** For $X \in \mathcal X$, each $v \in X$ has a *critical edge* $e$ with
$e\cap X = \lbrace v\rbrace$, by minimality. Let $\Gamma_X$ join $v$ to the zeros of its critical
edges. Its components $\mathcal K(X)$ partition $V$; a zero that lies in no critical edge is a
singleton, a *free zero*. Shared critical zeros are exactly what PPZ loses on (§6), so these
are the natural units. In the examples:

| example | components of $\Gamma_X$ | $\lvert X\cap K\rvert$ given $\mathcal K(X)$ | entropy of $\mathcal K(X)$ |
|---|---|---|---|
| blocks $K_{2k-2}^{(k)}$ | the blocks | fixed, $k-1$ (balanced) | $0$ |
| deep payments | the blocks | fixed, $k-1$ (balanced) | $0$ |
| mirror payments | $B_i$, or $B_i\cup B_{\pi(i)} - r_{\pi(i)}$ after a deficiency | fixed, $k-1$ or $2k-2$ (balanced within one) | $N\cdot\mathrm{poly}(k)4^{-k}$ |
| rigid model | the clique, plus free zeros | fixed, $m-k+1$ (unbalanced) | $0$ |

The mirror-payment row, by hand:
- In a free block, every one has the critical edge $r_i + v + (k-2 \text{ zeros})$.
- After a deficiency, $r_i$ is joined to $Z'$.
- Each $v \in R_i - Z'$ has the critical edge $A\cup\lbrace\iota(v)\rbrace$, with $A - v \subseteq Z'$.
- Each received $\iota(z)$ has critical edges back into $Z'$.
- For $d \ge 1$, $r_{\pi(i)}$ is in no critical edge, so it is a free zero.

With $g = \mathcal K$, `certificate_cond` turns this table into a proof route.

> **Component route.** Suppose that the witness components of a uniform minimum transversal
> have sizes in $[k^{c}, Ck]$, and that given $\mathcal K(X)$ their sizes are concentrated: for
> some centres $c_K$ (depending on the class), $\mathbb E\lvert\,\lvert X\cap K\rvert - c_K\rvert \le k^{c(1/2-\eta)}$
> on average over components. Suppose also that $H(\mathcal K(X)) = o(n\log k/k)$. Then
> $\lvert\mathcal X\rvert \le 2^{\,n-\Omega(c\eta\, n\log k/k)}$.

This follows from `certificate_cond` (assembled by hand). Use $g = \mathcal K$, take the
components of the class as the cover, and set $\theta = x/(1+x)$. Each component saves
$\frac12\ln\frac{3\lvert K\rvert+2}{2} \ge \frac c2\ln k$, and pays at most $\ln(1+2x)+1$ (§6g).
- *Balance is not needed.* The bound $\binom{b}{j} \le 2^b/\sqrt{(3b+2)/2}$ holds for every $j$,
  and unbalanced but concentrated components save more. Disjoint $K_b^{(k)}$ of mixed sizes,
  with $\tau = n/2$ overall, are unbalanced with zero deviation.
- *Small components are excluded on purpose:* a singleton (a free zero) saves nothing.
  *Corrected in §6i:* it saves $\frac12\ln\frac52$ here, and $\ln 2$ under `witness_bound`.
- Three of the four examples satisfy it outright.
- The rigid model fails it only through size: its one component is the whole clique. Its count
  is tiny anyway, and the fixed partition of §6g handles it ("spread rigidity": cut the clique
  into $O(k)$ pieces, padded with free zeros).
- The hypothesis can fail in four ways. Three of them match objects already studied
  (heuristic, not a proof):
  0. *Small components* (size $< k^{c}$). Here the ones have nearly private critical zeros,
     the local picture on which the one-level methods are tight (§6b), so the $\log k$ would
     have to come from elsewhere. Their vertices could be grouped into larger fixed sets as
     in §6g, but no rule for that is known.
  1. *Large components.* These are the rigid case (low count) or the code-like case (an
     "exactly half" constraint on $m \gg k$ vertices, which by `link_count` is the conjecture
     at size $m$).
  2. *Spread inside components.* Even given $\mathcal K(X)$, $\lvert X\cap K\rvert$ varies by
     about $\sqrt{\lvert K\rvert}$. No example has this. In all four, the component structure
     already fixes the sizes. This is (D) again, now inside a component, where every one
     shares critical zeros with the others. *Settled in §6i [F]:* within a class the traces
     form an antichain, so Sperner makes the sizes irrelevant.
  3. *High-entropy components*, with $\Omega(\log k)$ bits of component structure per block.
     This is the selector mixture of §6f, with the component partition playing the selector.
     The conditional certificate pays exactly that entropy, so the parked question returns
     with a sharper target. A mixture defeats the component route only if its component
     structure carries $\Omega(\log k)$ bits per block *and* no coarser $O(k)$-partition
     absorbs it.

**Two simple facts that the route uses** (by hand).
- *Deviations are shortfalls.* For an exact partition with $\sum_B c_B = n/2$, every $X$ has
  $\sum_B(\lvert X\cap B\rvert - c_B) = 0$. So $\sum_B\lvert\,\lvert X\cap B\rvert - c_B\rvert = 2\sum_B(c_B - \lvert X\cap B\rvert)^+$,
  and $D$ is twice the expected total shortfall. So (D) asks for *typical lower bounds* whose
  expected total shortfall is small, which ties §6g back to §6e.
- *Local gadgets are absorbed.* In a disjoint union of units, $\lvert X\cap U\rvert = \tau(U)$ for
  every minimum transversal, since the $\tau$'s add. So $D = 0$ with the units as blocks,
  however much the sizes vary inside a unit. More generally, any compensation inside an
  $O(k)$-region is invisible once that region is a block. A failure of (D) needs
  compensation across distances $\gg k$, *and* in a pattern that no low-entropy labelling
  tracks.

## 6i. Witness antichains: spread inside components does not matter [F], 2026-10-20

*Formal* (`Witness_Antichain.thy`, audited):
- `lym`: for an antichain $\mathcal A$ and a finite $U$,
  $\sum_{T\in\mathcal A,\,T\subseteq U}\lvert T\rvert!\,(\lvert U\rvert-\lvert T\rvert)! \le \lvert U\rvert!$.
  The proof is by induction on $\lvert U\rvert$ with no permutations. If $U\notin\mathcal A$, write
  $\lvert U\rvert - \lvert T\rvert$ as the number of $x\in U-T$, swap the sums, and apply the
  hypothesis to each $U-x$.
- `sperner`: an antichain of subsets of $U$ has at most $\binom{\lvert U\rvert}{\lfloor\lvert U\rvert/2\rfloor}$ members.
- `wclosed H X P`: every one $v\in X\cap K$, for $K\in P$, has a critical edge
  ($e\cap X = \lbrace v\rbrace$) with $e\subseteq K$.
- `class_antichain`: if every member of a family $G$ is a transversal and $P$ is `wclosed`
  for all of them, then $\lbrace Y\cap K : Y\in G\rbrace$ is an antichain for each $K\in P$.
  If $Y\cap K\subseteq Y'\cap K$ and $v\in Y'\cap K$, then $v$'s critical edge $e\subseteq K$
  is hit by $Y$ inside $K$, hence by $Y'$, so only at $v$.
- `witness_bound`: for any labelling $g$ such that each $g(X)$ covers $V$ and is `wclosed` for $X$,
  $$\ln\lvert F\rvert \le H(g) + \mathbb E_X\sum_{K\in g(X)}\ln\binom{\lvert K\rvert}{\lfloor\lvert K\rvert/2\rfloor}.$$
- `witness_partition`: if the parts are disjoint,
  $\ln\lvert F\rvert \le H(g) + \lvert V\rvert\ln 2 - \mathbb E_X\sum_{K\in g(X)}\frac12\ln\frac{3\lvert K\rvert+2}{2}$.

**What changes.**
- *Failure mode 2 of §6h is gone.* The witness components satisfy `wclosed`, since every
  critical edge of a one lies in that one's component. So no concentration of
  $\lvert X\cap K\rvert$ is needed. Inside a class, the traces on a part form an antichain, and
  Sperner charges the middle binomial whatever the sizes are. The component route becomes:
  $$\ln\lvert\mathcal X\rvert \le n\ln 2 - \Bigl(\mathbb E\,\Phi(X) - H(g)\Bigr),\qquad \Phi(X) = \sum_{K\in g(X)}\Bigl(\lvert K\rvert\ln 2 - \ln\tbinom{\lvert K\rvert}{\lfloor\lvert K\rvert/2\rfloor}\Bigr) \approx \sum_K \tfrac12\ln\tfrac{\pi\lvert K\rvert}{2}.$$
  The conjecture follows if some admissible labelling has $\mathbb E\Phi - H(g) \ge c\,n\log k/k$.
- *Failure mode 0 is not a failure of the bound.* Small parts save *more* per vertex. A free
  zero saves $\ln 2$ (its only trace is $\emptyset$), and a part of size 2 also saves $\ln 2$.
  *Correction to §6h:* "a singleton saves nothing" was wrong, and it was already wrong for
  `certificate_dev`, where a singleton block with zero deviation saves $\frac12\ln\frac52$.
  When parts are small, the cost is entirely in $H(g)$.
- *More freedom in the labelling.* `wclosed` needs only *one* critical edge per one inside
  its part. So one may pick a critical edge $e_v$ for each one and use the components of
  $\lbrace e_v\rbrace$, which are finer than the witness components. This saves more and may
  cost more entropy. Coarsening is also allowed.
- *What remains is one trade-off,* between part sizes and label entropy (failure modes 1
  and 3). A heuristic warning: each one has $\ge k-1$ critical zeros, and there are only
  $n/2$ zeros, so an unclustered witness graph has a giant component, and then
  $\Phi = O(\log n)$. The route needs the critical structure to cluster at scale $O(k)$. If
  it does not, a finer selection $e_v$ has to pay for itself in entropy.

**The route now proves a stronger statement** (by hand). `witness_bound` uses only that
each $X$ is a *minimal* transversal; $\tau$ never enters. Any proof along this route would
therefore bound the number of *all* minimal transversals of a rank-$k$ hypergraph:
> **(MT)** A hypergraph of rank $k$ on $n$ vertices has at most $2^{\,n-\Omega(n\log k/k)}$
> minimal transversals (equivalently, maximal independent sets).

- (MT) implies the conjecture, since minimum transversals are minimal.
- (MT) is open. The literature (see `notes/summaries/harris-ppz-novelty.md` and
  `private-subsets-and-designs.md`) has the lower bound $\binom{2k-1}{k}^{n/(2k-1)}$ from
  disjoint $K_{2k-1}^{(k)}$, which is $2^{n-\Theta(n\log k/k)}$. It also has branching upper
  bounds for small $k$ (Lonc–Truszczyński for rank 3; Cochefert–Couturier–Gaspers–Kratsch).
  Ilinca–Kahn count maximal independent sets by entropy for graphs.
- So the witness route cannot exploit $\tau = n/2$. That is a real restriction only if (MT)
  is false while the conjecture is true, and no example of that is known. To break (MT), one
  would look for many minimal transversals of *spread* sizes, none of them minimum.

## 6j. Beyond Majority: every monotone function with many minterms [F in part], 2026-10-20

The user asked whether the techniques extend to non-symmetric functions. They do, and the
reason is the observation of §6i that the counting never uses $\tau$.

*Formal* (`Minterm_Cover.thy`, audited). Let $f$ be any predicate on sets, and $H$ a monotone CNF
*below* $f$, meaning every transversal of $H$ satisfies $f$.
- `minterm_mtr`, `minterm_crit`: a minterm $X$ of $f$ (with $f(X)$ true and $f(X-v)$ false
  for every $v\in X$) that satisfies $H$ is a minimal transversal of $H$, and each $v\in X$
  has a critical edge. If $X-v$ satisfied $H$, it would satisfy $f$. No monotonicity of $f$ is
  used.
- `minterm_cover`: if an OR of CNFs $H_i$, $i\in I$, each below $f$, accepts every minterm
  in $M$, then $\lvert M\rvert \le \sum_i \#\mathrm{mtr}(H_i)$.
- `minterm_depth3`, with wide clauses: for minterms of size $\ge t$,
  $$\lvert M\rvert \le \lvert I\rvert\,\frac{2^n}{(1+1/k)^t} + \sum_{i\in I}\ \sum_{e\in H_i,\ \lvert e\rvert > k}\lvert e\rvert\, 2^{\,n-\lvert e\rvert}.$$
  A minterm whose critical edges are all narrow is counted by `harris_ppz`. Any other one has
  a wide critical edge $e$, and at most $2^{n-\lvert e\rvert}$ sets meet $e$ in a given single
  point (`single_hit`).

**Consequences** (by hand, from the formal statements).
- *Unconditional.* Suppose a monotone $\Sigma_3$ circuit of size $s$ computes $f$, and $f$ has
  at least $2^n/D$ minterms of size $\ge t$. The circuit has at most $s$ CNFs and $s$ clauses,
  so $2^n/D \le s\,2^n(1+1/k)^{-t} + s\,n\,2^{n-k-1}$ for every $k$. With $k = \lceil\sqrt t\rceil$
  and $(1+1/k)^t \ge e^{t/(2k)}$,
  $$s \ge 2^{\Omega(\sqrt t)}/(nD).$$
  For $\Pi_3$, apply this to the dual function and its maxterms. This is the classical
  $2^{\Omega(\sqrt n)}$ argument for Majority, in the form of the "isolated points" lower
  bounds of PPZ. It applies to every $f$ with $2^{n-o(\sqrt n)}$ minterms of linear size.
  The unconditional part is probably folklore; a literature check is pending.
- *Conditional on (MT).* In the first term, replace $(1+1/k)^{-t}$ by the minimal-transversal
  bound $k^{-cn/k}$. This counts only minimal transversals of the narrow part $H_i^{\le k}$:
  those minterms are minimal transversals of it, since their critical edges lie in it. Balancing
  $k^{cn/k}$ against $2^k$ gives $k \approx \sqrt{n\log n}$ and $s \ge 2^{\Omega(\sqrt{n\log n})}/(nD)$.
  So the $\log k$ program of this log is not about Majority. It is about the count (MT), and
  it serves every monotone function with nearly as many minterms as Majority.
- *The scope is narrow, but natural.* Counting needs an antichain of minterms of size
  $2^{n-o(\sqrt n)}$, essentially a positive fraction of the middle layers up to
  $2^{o(\sqrt n)}$. Functions such as clique or perfect matching have far fewer minterms and
  are out of reach.

**A non-symmetric class where both sides match up to the same question** (by hand).
Take linear threshold functions $f(x) = [\sum_i w_i x_i \ge \theta]$ with integer weights
$1 \le w_i \le w$, and $\theta$ near $\frac12\sum_i w_i$.
- *Lower bound.* Every set of weight exactly $\theta$ is a minterm. There are
  $2^n/O(\sqrt{w^2 n})$ of them by the local limit theorem, provided $\theta$ is reachable,
  for example when $\gcd_i w_i = 1$ and enough of the $w_i$ equal 1. At $w = 1$ it is the
  central binomial. These minterms have size $\ge \theta/w$, which is linear.
  So $s \ge 2^{\Omega(\sqrt n)}/\mathrm{poly}(n)$ unconditionally, and
  $2^{\Omega(\sqrt{n\log n})}$ under (MT).
- *Upper bound.* $f$ is a monotone projection of $\mathrm{Maj}_N$ with $N = \sum_i w_i \le wn$:
  repeat $x_i$ $w_i$ times, and pad with constants to move the threshold. So the monotone KPPY
  formulas give size $2^{O(\sqrt{wn\log(wn)})}$.
- For $w = O(1)$, monotone depth-3 complexity of these non-symmetric functions sits between
  $2^{\Omega(\sqrt n)}$ and $2^{O(\sqrt{n\log n})}$, exactly as for Majority, and (MT) would
  close the gap. Non-monotone depth 3 is not settled here: L-R's $2^{O(\sqrt n)}$ is for
  symmetric functions, and a projection from $\mathrm{Maj}_N$ gives $2^{O(\sqrt{wn})}$. So the
  separation question carries over too, for $w = O(1)$.
- Other members of the class are any monotone projections of Majority with $O(n)$ variables,
  and block-weighted thresholds.

**Questions this opens.**
- Is there a monotone $f$ with $2^{n-o(\sqrt n)}$ minterms whose monotone depth-3 complexity
  is far *above* $2^{\sqrt{n\log n}}$? The counting bound cannot give more than
  $2^n/\mathrm{MT}_k$ per CNF, so its limit is set by (MT) together with the cost of wide
  clauses.
- Upper bounds beyond projections of Majority: covering a non-symmetric antichain by CNFs
  below $f$, each with many minimal transversals, needs CNFs adapted to $f$. Random
  permutations (`threshold_cover`) only work for symmetric $f$.

## 7. The structural question

The conjecture now follows from a purely structural statement:

> **Question C.** If $\tau(H) = n/2$, the edges have size $\le k$, and $H$ has many minimum
> transversals, do most of them have $\Omega(n/k)$ $O(k)$-clusters with disjoint sets of ones?

Since §6a, the zero sets of the clusters may overlap.

The relevant definition of "most" comes from `cluster_count`. A minority with few clusters
must be bounded some other way. Note how weak "most" can be: if the good transversals gain a
factor $\gamma$ each, then $\lvert\text{bad}\rvert \le \gamma^{1-\varepsilon}\lvert\text{good}\rvert$
already gives $\lvert\mathcal X\rvert \le 2^{n+1}\gamma^{-\varepsilon}$.

- **Clusters can be absent.** Take ones $X$ with private critical zero sets $Z_v$ forming a
  linear design, and all pairs inside $X$ as edges. Then $\tau = t$, but $X$ has no clusters. Its
  forcing events are only weakly correlated, so heuristically
  $\mathbb E\, 2^F \approx (1 + 1/k)^t$ (not proved). This $H$ has just
  $1 + \sum_v \lvert Z_v\rvert$ minimum transversals, however. Every other one,
  $X - v + u$, has all $t-1$ remaining ones sharing the critical set $\lbrace v\rbrace$: one huge
  cluster. So the cluster-free transversal is rare.
- **Swaps create clusters.** If $v \in X$ has a unique critical edge, then each $X - v + u$
  with $u \in Z_v$ is again a minimum transversal. In $X - v + u$, every one $w$ whose only
  critical edge contains $u$ loses it. Since $\tau = t$, $w$ needs a new one, which must
  contain $v$. So $v$ becomes a shared critical zero.
- **Single swaps are not enough.** $\Omega(n/k)$ clusters need $\Omega(n/k)$ independent
  swaps. Whether far-apart swaps commute, so that a cluster-free $X$ sits at the corner of a
  large product of cluster-rich ones, is the next thing to test by hand.
- **A naive swap charging fails by a constant (hand count).** Map a bad $X$ to a good $X'$ by
  $s = \delta n/k$ swaps. Then a good $X'$ receives up to $\binom{O(nk)}{s} = k^{O(\delta n/k)}$
  charges, because the swap locations are not canonical. Each cluster gains only about
  $\frac12\log_2 k$ bits, and locating its swap costs about $\log_2 k$ bits. So the charging
  needs canonical swap locations, or clusters of quality better than one per swap.
- **A shared single zero is not a cluster.** If ones $w_1,\dots,w_g$ have critical sets
  $\lbrace u\rbrace \cup A_i$ with the $A_i$ disjoint of size $k-2$, then
  $\mathbb E\, 2^N \approx (1+1/k)^g$. The private parts $A_i$ already cap each forcing
  probability at about $1/k$. A swap $X - v + u$ makes $v$ a shared zero, but the new critical
  sets must also overlap in most of their other zeros to give a gain.

## 8. Next steps

0. **The shadow target (§6b), by hand.** Lower-bound the forbidden mass $\lvert F(Y)\rvert$ for
   extendable $Y$, or prove the shadow bound for a natural class first. One candidate is
   hypergraphs whose residuals are disjoint unions of cliques; that class contains the blocks
   and is closed under restriction.
   The lemma once suggested here, that the minimum transversals cover at most $k\tau$ vertices,
   is false for $k \ge 3$ and true for graphs (§6d).
   The deficit conjecture of §6d is false (§6e, deep payments). Local-$\tau$ certificates cannot
   be the mechanism in general.
   **Done (§6f):** the code-like question. A cheap rank-$k$ gadget forcing "exactly half" on
   a group of size $m$ exists only if the conjecture fails at size $m$ (`link_count`). For the
   proof route, (R) is replaced by its conditional form (R$_Y$).
   **Parked (§6f):** selector mixtures.
   - Exact designs are ruled out (`private_design`).
   - Few selectors, and the intersection attack plus König, both favour (R).
   - The open route is pair-specific edges.
   **Main line now (§6g):** the size condition (D). Typical lower bounds and the deviation form
   are formal (`certificate_typ`, `certificate_dev`), and all three test cases have total
   deviation $O(k)$. **Structure (§6h):** the witness components $\mathcal K(X)$, through
   `certificate_cond`, give a proof route with four failure modes: small or large
   components, sizes spread inside components, or high-entropy components. Mirror payments [F in part] are a fourth test case, with
   deficient blocks that do occur, and a mild trace/entropy separation. Next:
   - Prove the component route's hypotheses for a natural class. A candidate is hypergraphs
     whose minimum transversals all have components that are unions of blocks of one fixed
     partition, up to rare events.
   - **Done (§6i) [F]:** failure mode 2. The traces in a class form an antichain, so Sperner
     replaces size concentration (`witness_bound`). The route is now one trade-off,
     $\mathbb E\Phi - H(g) \ge c\,n\log k/k$, over labellings that contain one critical edge
     per one. It never uses $\tau$, so it would prove the stronger (MT): at most
     $2^{n-\Omega(n\log k/k)}$ minimal transversals at rank $k$.
   - Next: try to break (MT) (many minimal transversals of spread sizes), or prove the
     trade-off for a class in which the critical structure clusters. Choose the labelling
     well: one critical edge per one, picked canonically, for example the
     lexicographically first.
   - Failure mode 3 is the parked selector question of §6f, with a sharper target: the
     component structure must carry $\Omega(\log k)$ bits per block.
   - A fully separating trace/entropy example is still open. Mirror payments separate only up
     to merging $O(1)$ blocks.
1. Test Question C on small structures by hand, now with overlapping zero sets allowed. In
   particular, find out when swaps at disjoint places commute. Note also when the swaps can
   be located canonically, which the charging needs (§7).
2. If a cluster-free $X$ always has many cluster-rich neighbours, formalize the charging
   $\lvert\text{bad}\rvert \le \gamma^{1-\varepsilon}\lvert\text{good}\rvert$ on top of
   `cluster_count_overlap`.
3. Zeros. One-forcing per $X$ is capped near $(1+1/k)^t$ (§6a), so the zeros must
   contribute. Conjecture A (the factor 2 over PPZ) stays the fallback target. Zero-forcing
   events are monotone in the opposite direction, so Harris does not combine them with the
   ones for free.
4. Optional: generalize `majority_mcnfs_slice` from width 3 to width $k$, which would make
   the Majority form of §6a formal.
