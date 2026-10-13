# Monotone $\Sigma_3^k$ for Majority, $k \ge 4$: research log

$\tiny\color{transparent}\text{provenance: github.com/ott2/circuitub, extensions/monotone-k.md, on top of commit 275734a53d5e64711011874338f4aa6d68665958 (2026-10-13)}$

Status: **open problem. One rung is formal: `cluster_count` (session `Monotone_K`, §6). The rest is pen and paper.**

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

## 7. The structural question

The conjecture now follows from a purely structural statement:

> **Question C.** If $\tau(H) = n/2$, the edges have size $\le k$, and $H$ has many minimum
> transversals, do most of them have $\Omega(n/k)$ disjoint $O(k)$-clusters?

The relevant definition of "most" comes from `cluster_count`. A minority with few clusters
must be bounded some other way.

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

## 8. Next steps

1. Test Question C on small structures by hand. In particular, find out when swaps at
   disjoint places commute.
2. If a cluster-free $X$ always has many cluster-rich neighbours, formalize the charging
   $\lvert\text{bad}\rvert \le C\,\lvert\text{good}\rvert$ on top of `cluster_count`.
3. Conjecture A (the factor 2 over PPZ) stays open as a fallback target.
