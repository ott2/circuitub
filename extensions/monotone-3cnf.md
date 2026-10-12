# Monotone 3-CNFs with no small transversal: a formal check of Gurumukhani et al.

$\tiny\color{transparent}\text{provenance: github.com/ott2/circuitub, extensions/monotone-3cnf.md, on top of commit 2914f680589cc0705774e787e6e5d4ad34bb4c1c (2026-10-13)}$

This document reports a formal verification, in Isabelle2025-2, of the main theorem of
Gurumukhani, Kleber, Paturi, Rosin, Saks and Talebanfard, *Optimal Monotone Depth-Three
Circuit Lower Bounds for Majority* ([arXiv:2601.04072v2](https://arxiv.org/abs/2601.04072)).

**Result.** The theorem is true and is now proved formally, with no `sorry`. The paper's
proof has six genuine gaps, and each has a repair within the same induction. No bound or
constant changes.

Status:

| Part | Formalized in | Contents |
|---|---|---|
| The main theorem and the $6^{n/4}$ corollary | `isabelle/gkprst/Monotone_3CNF.thy` (session `Monotone_Sigma3`) | Formal end to end |
| The Majority size bound $\binom{n}{n/2}/6^{n/4}$, and $\binom{n}{\lfloor n/2\rfloor}/6^{(n+1)/4}$ for every $n$ | `isabelle/gkprst/majority/Majority_3CNF.thy` (session `GKPRST_Majority`) | Formal |
| The matching upper bound: $(n+1)\binom{n}{n/2}/6^{n/4} + 1$ CNFs suffice for $4 \mid n$ | `isabelle/gkprst/majority/Majority_3CNF_Upper.thy` | Formal; the paper cites it rather than proving it |
| The upper bound for every $n$: $6^{1/4}(n+1)\binom{n}{\lfloor n/2\rfloor}/6^{n/4} + 1$ CNFs, within $\sqrt6\,(n+1)$ of the lower bound | `isabelle/gkprst/majority/Majority_3CNF_Any.thy` | Formal |
| Audit of the headline theorems | `isabelle/gkprst/majority/Audit_GKPRST.thy` | Formal: no oracles |

The working notes, case by case, are in `gkprst26/NOTES.md`.

## 1. The statement

A monotone CNF over a finite variable set $V$, $n = \lvert V\rvert$, is a set $F$ of clauses,
each a subset of $V$. A *transversal* is a set $X \subseteq V$ that meets every clause; these
are exactly the satisfying assignments. The CNF has *threshold* $t$ if it has no transversal
of size $< t$. Write $s = 3t - n$.

**Theorem** (`gkprst_bound`). If every clause has at most 3 variables and $F$ has threshold
$t$, then the number of transversals of size $t$ is at most

$$\mathrm{bound}_0(s,t) = \begin{cases} (2/3)^{s/2}\, 3^t & s \text{ even},\\ \tfrac79 (2/3)^{(s-1)/2}\, 3^t & s \text{ odd}.\end{cases}$$

**Corollary** (`gkprst_half`). If $n = 2t$, there are at most $6^{n/4}$ transversals of size
$n/2$.
- For $4 \mid n$ the bound is exactly $6^{n/4}$.
- For $n \equiv 2 \pmod 4$ it is $\tfrac73\, 6^{(n-2)/4} \le \sqrt6\, 6^{(n-2)/4}$.

**Corollary** (`gkprst_half_odd`). If $n = 2t - 1$, there are at most $6^{(n+1)/4}$
transversals of size $t$. Here $s = t + 1$, and the bound decreases in $s$ (`bound_mono`).

**Consequence for circuits** (`majority_mcnfs`, `majority_mcnfs_exp`,
`majority_mcnf_formula`). A monotone OR of 3-CNFs computing Majority on $n$ (even) variables
needs at least $\binom{n}{n/2}/6^{n/4}$ CNFs. Equivalently, with $L$ CNFs,

$$\left(\frac{2}{6^{1/4}}\right)^{n} \le (n+1)\, L, \qquad \frac{2}{6^{1/4}} > 1.2779.$$

The same bounds hold with $L$ replaced by the number of gates of the formula.
- Each CNF accepts only inputs of weight $\ge n/2$, so it has threshold $n/2$, and it accepts
  at most $6^{n/4}$ inputs of weight $n/2$.
- The CNFs together must accept all $\binom{n}{n/2}$ such inputs.
- The exponential form uses $2^n \le (n+1)\binom{n}{n/2}$ (`slice_lower`).
- **For every $n$** (`majority_mcnfs_odd`, `majority_mcnfs_any`, `majority_mcnfs_exp_any`), at
  least $\binom{n}{\lfloor n/2\rfloor}/6^{(n+1)/4}$ CNFs are needed, and
  $(2/6^{1/4})^n \le 6^{1/4}(n+1)L$. For odd $n$ the slice $(n+1)/2$ is used; it has the same
  size as the slice $\lfloor n/2\rfloor$.
- All cases go through one counting lemma, `majority_mcnfs_slice`: for any $t$ with
  $n \le 2t \le n+1$, if every threshold-$t$ CNF has at most $B$ transversals of size $t$,
  then $\binom{n}{t} \le L B$.

**Tightness** (`majority_mcnfs_upper`, `majority_mcnfs_tight`). For $4 \mid n$ there is a
monotone OR of 3-CNFs computing Majority with

$$L \le (n+1)\,\frac{\binom{n}{n/2}}{6^{n/4}} + 1$$

CNFs, each with $n+1$ gates. So the least $L$ is determined up to a factor $n+1$. The paper
cites this direction (Gurumukhani, Künnemann and Paturi 2024); it is proved here from
scratch.
- *The extremal CNF* (`K4`, `K4_thr`, `K4_trans`, `Q4_card`) is made of $n/4$ disjoint copies
  of $K_4^{(3)}$, all 3-subsets of a block of four. A set hits every 3-subset of a block
  exactly when it has $\ge 2$ elements there. So the threshold is $n/2$, and the minimum
  transversals take exactly two elements per block: $6^{n/4}$ of them.
- *Permuted copies* (`pmap_cnf`, `pmap_thr`, `pmap_trans`) keep the threshold and the
  transversal count.
- *Averaging* (`fiber_card`, `fiber_ratio`, `good_perm`). For a fixed $t$-set $X$, the image
  $pX$ under a random permutation $p$ is uniform on the slice: the fibres
  $\lbrace p : pX = Y\rbrace$ are cosets of the stabilizer of $X$. So some copy covers at
  least a $T/N$ fraction of any set of uncovered points, where $N = \binom{n}{t}$. No factorial
  counting is needed.
- *Greedy* (`greedy`, `greedy_cover`). After $k$ copies at most $N(1-T/N)^k \le N e^{-kT/N}$
  points are uncovered. With $kT \ge (n+1)N$ this is at most $2^n e^{-(n+1)} < 1$.
- *Correctness* (`threshold_cover`). The OR of the copies rejects weights below $t$, since
  each copy has threshold $t$. It accepts every weight-$t$ input, since the copies cover the
  slice, and so by monotonicity every heavier input too. This holds for any threshold-$t$
  monotone 3-CNF, not just $K_4^{(3)}$ blocks.

**Every $n$** (`majority_mcnfs_upper_any`, `majority_mcnfs_tight_any`). Write $n = 4m + r$
with $r < 4$. Add to the $m$ blocks of $K_4^{(3)}$ one small clique on the last $r$ variables:
all $k$-subsets of them, with $k = 1$ for $r \le 1$ and $k = 2$ otherwise.
- A set hits every clause of the small clique exactly when it misses fewer than $k$ of its
  variables (`hits_KC`). So its threshold is $r + 1 - k = \lceil r/2\rceil$, and it has
  $c_r = \binom{r}{\lceil r/2\rceil} = 1, 1, 2, 3$ minimum transversals (`KC_thr`,
  `KC_trans_card`).
- For CNFs on disjoint variable sets, thresholds add and minimum transversals multiply
  (`union_thr`, `union_trans_card`). The whole CNF therefore has threshold
  $2m + \lceil r/2\rceil = \lceil n/2\rceil$, at most $n$ clauses, and $6^m c_r$ minimum
  transversals (`XF`).
- With $q = 6^{1/4}$, $q^r \le q\,c_r$ for each $r < 4$: this is $1 \le q$, an equality,
  $q \le 2$ (that is, $6 \le 16$), and $q^2 \le 3$ (that is, $6 \le 9$). So
  $6^m c_r \ge 6^{(n-1)/4}$ (`quarter_bound`).

So `threshold_cover` gives, for every $n$,

$$L \le 6^{1/4}(n+1)\,\frac{\binom{n}{\lfloor n/2\rfloor}}{6^{n/4}} + 1,$$

with at most $n+1$ gates per CNF. With `majority_mcnfs_any`, the least $L$ is determined up
to a factor $\sqrt6\,(n+1)$ for every $n$. For odd $n$ the constant could be improved: the
lower bound counts against $6^{(n+1)/4}$, the construction offers only $6^m c_r$. The
paper's 6-variable necklace (threshold 3, 14 transversals) would raise $c_2$ to
$14/6 \approx 2.33$ for $n \equiv 2 \pmod 4$. Neither changes the factor $n+1$.

The formulas are those of `Formula.thy` in `Majority_AC0`. `MCNF 3 f` says that $f$ is an
AND of ORs of at most 3 positive literals, and `majority n σ` says that $n \le 2\,\mathrm{weight}$.
Variables $\ge n$ are false. The bridge `eval_pcnf` shows that a monotone CNF accepts an
input $X \subseteq \lbrace 0,\dots,n-1\rbrace$ exactly when $X$ is a transversal of its clause
sets restricted to $\lbrace 0,\dots,n-1\rbrace$.

**Trusted definitions.** The statement uses only these, in `Monotone_3CNF.thy`:

| Definition | Meaning |
|---|---|
| `cnf V F` | $V$ is finite and every clause is a subset of $V$ of size $\le 3$ |
| `hits F X` | $X$ meets every clause of $F$ |
| `trans V F t` | $\lbrace X \subseteq V : X \text{ hits } F,\ \lvert X\rvert = t\rbrace$ |
| `thr V F t` | every $X \subseteq V$ that hits $F$ has $\lvert X\rvert \ge t$ |
| `bound T0 s t` | $c\,(2/3)^{\lfloor s/2\rfloor}\,3^t$, with $c = 1$ for even $s$ and $c = 7/9$ for odd $s$ |

## 2. The proof, and how the formal version is organized

The paper proves bounds $N_i(s,t) \le c_i (2/3)^{s/2}3^t$ (even $s$) and
$c'_i (2/3)^{(s-1)/2}3^t$ (odd $s$) simultaneously for six families of CNFs. Each family is
defined by its 2-clauses.

| Family | Definition | $c_i$ (even) | $c'_i$ (odd) |
|---|---|---|---|
| 0 | any | $1$ | $7/9$ |
| 1 | a 2-clause | $5/6$ | $2/3$ |
| 2o | two 2-clauses that meet | $2/3$ | $5/9$ |
| 2d | two disjoint 2-clauses | $25/36$ | $5/9$ |
| 3 | $\ge 3$ 2-clauses, no variable in three of them | $7/12$ | $1/2$ |
| 4 | $\ge 4$ 2-clauses | $7/12$ | $17/36$ |

For families 2o–4, the paper also requires that no pair of variables lies in three clauses.

Each family is covered by a list of configurations. For each configuration, a *table* sets a
few variables and records the restricted CNF. Two things must then be checked:
- the rows cover every minimum transversal;
- the restricted bounds sum to at most 1.

There are 58 tables.

The formal proof follows this outline, with three changes of structure.

- **The induction is on $n$ alone.** Every row sets at least one variable.
  - The hypothesis also covers CNFs with a clause of size $\le 1$. Such a CNF obeys every
    bound: forcing the variable costs at most $14/17$ of the smallest bound.
  - This absorbs restrictions that create 1-clauses, which the paper overlooks in several
    places.
- **Domination.** A row may use any family whose coefficients are at most those of the
  family it claims (`fam_ok`). The families form a chain $4 \le 3 \le 2o \le 2d \le 1 \le 0$.
  - The paper relies on this informally, for example in "type 2", meaning 2o or 2d.
  - It is needed whenever a restriction keeps the other 2-clauses of $F$. A restriction the
    paper calls type 3 can have four 2-clauses, which is type 4.
- **The families are proved in a fixed order at each $n$: 3, 4, 2o, 2d, 1, 0.**
  - The coverage for 2o assumes the CNF is not of type 3 or 4.
  - The coverage for 2d assumes it is not of type 2o.
  - The proof for type 4, even $s$, uses type 3.
  - Each of these uses the bound of a more specific family at the same $n$, which is smaller.
    That is sound because every table row passes to fewer variables.

The reductions to the normalized situation (`step`) are also formal:
- $t = 0$;
- an empty clause;
- a 1-clause, which is forced;
- subsumed clauses, by keeping only the inclusion-minimal clauses, which changes neither the
  transversals nor the family;
- unused variables, which lie in no minimum transversal.

## 3. Gaps in the paper's proof

Each gap below is a place where the paper's table or coverage argument is wrong as written.

1. **P0.4 (triangle, type 0): a missing row.** The table has no row for $a = b = c = 0$, which
   forces $d = e = f = 1$.
   - *Counterexample:* the prism, with triangles $\lbrace a,b,d\rbrace,\lbrace b,c,e\rbrace,
     \lbrace a,c,f\rbrace$ and $\lbrace a',b',d\rbrace,\lbrace b',c',e\rbrace,\lbrace a',c',f\rbrace$,
     where $n = 9$, $t = 3$. Here $\lbrace d,e,f\rbrace$ is a minimum transversal that no row
     covers.
   - *Repair:* since P0.3 fails, $d,e,f$ are distinct. So the rows with two of $a,b,c$ set
     five variables, not four. With the missing row added, the sums are $103/108$ (even $s$)
     and $1$ (odd $s$).
2. **Type 2d: coverage.** The lemma before P2d.1 takes the further clauses of $a$ and $b$ to be
   3-clauses. They can be 2-clauses.
   - *Counterexample:* the 2-clauses $\lbrace a,b\rbrace,\lbrace a,e\rbrace,\lbrace b,e\rbrace$ and
     $\lbrace c,d\rbrace,\lbrace c,g\rbrace,\lbrace d,g\rbrace$ satisfy none of P2d.1–P2d.5.
   - *Repair:* a CNF with two 2-clauses that meet is of type 2o, and $N_{2o} \le N_{2d}$. So
     prove 2o first and assume $\neg$2o. Then every further clause is a 3-clause, and the
     paper's case analysis goes through.
3. **Type 2o: coverage.** The CNFs in question have 2-clauses $\lbrace a,b\rbrace$,
   $\lbrace a,c\rbrace$; $b$ and $c$ share exactly one clause $\lbrace b,c,d\rbrace$; $b$ has a
   further clause $\lbrace b,e,f\rbrace$; and $c$ has none. None of P2o.1–P2o.10 covers them.
   - The paper's remark "if one of $b$ or $c$ appears at least three times, one of
     P2o.1–P2o.8 holds" is false here.
   - *Repair:* there are two tables, depending on whether $d \in \lbrace e,f\rbrace$.
   - If $d \notin \lbrace e,f\rbrace$: setting $c = 1$, $b = 0$ forces $d = 0$, and the table sums
     to exactly 1.
   - If $d \in \lbrace e,f\rbrace$: the P2o.5 Case 2 table works with one row taken as type 0
     (sum $23/24$).
4. **P3p.1 (type 3, path $\lbrace a,b\rbrace,\lbrace b,c\rbrace,\lbrace c,d\rbrace$, with $b$ in no
   other clause): a wrong table.** The table claims that $a = 1$ forces $b = 0$. But
   $a = b = 1$, $c = 0$, $d = 1$ is possible.
   - *Counterexample:* $F = \lbrace ab, bc, cd, axy, duv\rbrace$ has $t = 3$, and
     $\lbrace a,b,d\rbrace$ is a minimum transversal that no row covers. Adding the row
     overshoots ($47/42$).
   - *Repair:* split on $c$. If $c = 0$, then $b = d = 1$. If $c = 1$, then either $b = 1$ and
     $a = 0$ (by $b$'s critical clause), or $b = 0$ and $a = 1$. Each row is $1/3$, so the table
     is tight for both parities.
5. **P3ie.2 (type 3, a 2-clause $\lbrace a,b\rbrace$ disjoint from $\lbrace c,d\rbrace$ and
   $\lbrace e,f\rbrace$, even $s$, $a$ in $\lbrace a,c,x\rbrace$).** The row $a = c = 0$ is
   claimed to be of type 1 via $\lbrace e,f\rbrace$. That fails when $x \in \lbrace e,f\rbrace$
   or $d \in \lbrace e,f\rbrace$; with type 0 the sum is $43/42$.
   - *Repair, if $\lbrace c,d\rbrace$ and $\lbrace e,f\rbrace$ meet:* the row $a = 1$ is of
     type 2o rather than 2d. The tables then sum to $1$ and $41/42$.
   - *Repair, if $a$'s only further clause is $\lbrace a,c,e\rbrace$:* a new four-row table,
     which also uses a further clause of $b$, sums to $39/42$.
6. **Type 4 for even $s$.** The paper says even $s$ "is handled by the three 2-clause case".
   That holds only if no variable lies in three 2-clauses, since type 3 excludes such stars.
   - *Repair:* if $a$ lies in four 2-clauses, the rows $a = 1$ and $a = 0$ sum to $79/84$. If
     $a$ lies in exactly three, another 2-clause avoids $a$, and the rows sum to $37/42$.

## 4. Simplifications

The following tables are correct, but they assume more than they use or split into more
cases than they need.

- **P0.1:** needs only a clause with $a$ but not $b$.
- **P0.6:** needs no "domination" step.
- **The coverage lemma for type 0.** The paper's `lemma:Egraph` has no proof, and the proof
  is short. A shared variable of two further clauses gives a triangle with six distinct
  variables.
- **P1.2 and P2d.2:** the further clause may be a 2-clause, which leaves a 1-clause.
- **P2d.3:** only $e$'s further clause is needed.
- **P2o.2:** its Case 2 cannot occur, since a common variable would put a pair in three
  clauses.
- **P2o.7:** the row $a = 1$, $b = c = 0$ always leaves four 2-clauses, so it is of type 4. One
  table covers all three of the paper's cases.
- **P3p.2:** only $b$'s further clause is needed.
- **P3ie.5 and P3ie.6:** they hold without their side conditions. Two further clauses of $a$
  always give a type-4 row.
- **The coverage for type 3:** any three 2-clauses with no common variable form a triangle,
  a path of length 3, or contain one disjoint from the other two. So the three-way case
  split needs no graph analysis.

## 5. Reproducing

```sh
isabelle build -d isabelle Monotone_Sigma3
isabelle build -d isabelle GKPRST_Majority
```

`Monotone_Sigma3` depends only on HOL-Library and builds in about 20 seconds; the theory has
about 5,400 lines. `GKPRST_Majority` builds on `Majority_AC0` and `Monotone_Sigma3`. It adds
the Majority bounds (about 300 lines), the matching upper bound (about 840 lines, using
`permutes` from HOL-Combinatorics), its extension to every $n$ (about 360 lines), and the
oracle audit `Audit_GKPRST`. The audit fails the
build if any headline theorem depends on an oracle such as `sorry`.

The theorem names:
- `gkprst_bound` and `gkprst_half`, the headline results;
- `type0`, `type1`, `type2o`, `type2d`, `type3`, `type4`, the coverage for each family;
- `step` and `IH_all`, the induction;
- `gkprst_half_odd`, the odd case;
- `majority_mcnfs`, `majority_mcnfs_odd`, `majority_mcnfs_any`, `majority_mcnfs_exp`,
  `majority_mcnfs_exp_any` and `majority_mcnf_formula`, the Majority lower bound;
- `threshold_cover`, `majority_mcnfs_upper` and `majority_mcnfs_tight`, the matching upper bound;
- `union_trans_card`, `KC_trans_card`, `XF`, `quarter_bound`, `majority_mcnfs_upper_any` and
  `majority_mcnfs_tight_any`, the upper bound for every $n$.

## 6. Next steps

1. A write-up of the six gaps for the authors is drafted in `gkprst26/gaps-for-authors.md`.
2. Monotone $\Sigma_3^k$ for $k \ge 4$ is open. See §2.10 of `locality-and-monotonicity.md`.
