# Monotone $\Sigma_3^k$ for Majority, $k \ge 4$: research log

$\tiny\color{transparent}\text{provenance: github.com/ott2/circuitub, extensions/monotone-k.md, on top of commit cd99a17be617e3380cce73f2eac38c9df6c857ef (2026-10-15)}$

Status: **open problem. Formal rungs (session `Monotone_K`): `cluster_count` (§6) and the Harris inequality with its consequences (§6a), and `shadow_branch` (§6b). The rest is pen and paper; the current main line is the deficit conjecture of §6d.**

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

> **Deficit conjecture.** For rank $k$, $\tau = n/2$ and $b = Ck$, let $\Delta_b$ be the least
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
- *Counterexample.* Add $k-2$ private new vertices to each edge of $K_{t+1}$. The result $H$ has
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
  $\lvert U\rvert \le 2\tau$, that is $\lvert\mathrm{core}\rvert \ge \alpha - \tau$. Boros–Golumbic–Levit's
  $\alpha - \mu$ is stronger; the literature check is pending.
- In the sequential form of §6b, the non-forbidden vertices are $U(H_Y)$ for the residual $H_Y$.
  The counterexample shows $\lvert U(H_Y)\rvert$ can grow like $\tau(H_Y)^2$, so this route
  bounds $F(Y)$ only when very few ones remain free.

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
   **Main line now (§6d):** the deficit conjecture. Prove it first for the rigid model
   $K_m^{(k)}$ plus isolated vertices and its relatives (cliques glued along small sets), via the
   concentration form: show that global minimality makes $\lvert X\cap B\rvert$ concentrated.
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
