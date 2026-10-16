# Monotone $\Sigma_3^k$ for Majority, $k \ge 4$: research log

$\tiny\color{transparent}\text{provenance: github.com/ott2/circuitub, extensions/monotone-k.md, on top of commit 24c70c071b8267b619410296b77528b629309335 (2026-10-17)}$

Status: **open problem. Formal rungs (session `Monotone_K`): `cluster_count` (§6) and the Harris inequality with its consequences (§6a), and `shadow_branch` (§6b). The rest is pen and paper. The deficit conjecture of §6d is refuted in §6e; the main line is now typical lower bounds (§6e).**

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
- **Formalization.** It would need entropy and Shearer's lemma, or the combinatorial
  Shearer lemma (Chung–Graham–Frankl–Shearer) with integer multiplicities. Neither is in
  this repository yet.

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
- *The concentration form does see it.* For the original blocks, $\lvert X\cap B_i\rvert = k-1$
  except with probability $e^{-\Omega(k)}$. A deficient block forces a full target block, so
  such configurations are rarer than normal ones by a factor of about $4^{-k}$. So
  $H(\lvert X\cap B_i\rvert) = o(1)$, and the bound of §6d gives the full saving.

**What survives: typical lower bounds.** In this example and in the rigid model of §6d,
$\lvert X\cap B\rvert$ is pinned *from below* not by $\tau_B$ but by a *typical* lower bound
$\ell_B$, with $\Pr[\lvert X\cap B\rvert < \ell_B]$ small. Deficient configurations are
possible, but they are rare because of what they force elsewhere.
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
- *The worst-case version fails.* Replacing $H(X_B)$ by $\log_2$ of the trace
  $\lbrace X\cap B : X \in \mathcal X\rbrace$ saves only about one bit per block on deep
  payments. The excess patterns (size $\ge k$) all occur, just rarely. So the typical
  (entropy) form is needed, not the trace.
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
  whose helper sets satisfy the self-similarity constraint? A literature check is in progress.
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
  It sits on $Y \subsetneq V$ and is enforced by $H$ through minimizing
  $\lvert S\rvert + \tau(H_S)$, a cousin of the original problem.
- The regress descends, since $Y$ is part of the same finite hypergraph. A mixture can only
  pass code-likeness down from its selectors to its group.
- **Consequence for (R):** any failure of (R) must bottom out in an *intrinsically* code-like
  family, one not explained by mixing.
  - To make this a theorem, the "cousin" problem must be shown to be an instance of the
    original, or (R) must be stated for the weighted problem $\min_S(\lvert S\rvert + \tau(H_S))$.
  - The latter is natural: it is (R) for hypergraphs with a cost on part of the vertex set.

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
   **Next by hand:** realize a selector-mixture hypergraph (links block-structured on
   different partitions), or show that the constraints of §6f prevent it. Exact designs are
   ruled out (`private_design`); the entropic version and partial switching are open. The
   self-similarity constraint is the most promising lever.
   **Main line now (§6e):** typical lower bounds. Find a structural rule that names $\ell_B$ in
   advance and a switching argument showing that $\lvert X\cap B\rvert < \ell_B$ is rare. Test it
   on the deep-payment example, where the switch is "a deficient block forces a full target".
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
