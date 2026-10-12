# Six gaps in the upper-bound proof of arXiv:2601.04072, with repairs

$\tiny\color{transparent}\text{provenance: github.com/ott2/circuitub, gkprst26/gaps-for-authors.md, on top of commit 72643475558fc0d89ec6a869439561a5e837dceb (2026-10-12)}$

*Draft note for the authors of* Optimal Monotone Depth-Three Circuit Lower Bounds for Majority
*(Gurumukhani, Kleber, Paturi, Rosin, Saks, Talebanfard; arXiv:2601.04072v2). Not yet sent.*

## Summary

We formalized the upper bound of Section 4 (Theorem `thm:upperbounds`, for $N_0$) in the
proof assistant Isabelle/HOL. We also formalized its consequence for monotone depth-3 circuits
for Majority. **The theorem is true, with exactly the stated constants.** The formal statement:

> If $F$ is a monotone CNF on $n$ variables with clauses of size at most 3 and no transversal
> of size $< t$, and $s = 3t - n$, then $F$ has at most $(2/3)^{s/2}3^t$ transversals of size
> $t$ for even $s$, and at most $\tfrac79 (2/3)^{(s-1)/2}3^t$ for odd $s$.

For $n = 2t$ this gives at most $6^{n/4}$. Hence a monotone OR of 3-CNFs computing Majority on
$n$ (even) variables has at least $\binom{n}{n/2}/6^{n/4}$ CNFs.

The proof as written has six places where a table or a coverage claim is wrong. Each one can be
repaired inside the same induction, with no change to any bound. Below, each gap gives the
location, a counterexample or the failing computation, and the repair. Every repaired table has
been checked by machine.

All locations and quotations refer to the LaTeX source of v2 as posted on arXiv; file names
such as `phi0.tex` are those of that source.

Notation:
- A table row sets $j$ variables to 1 and $e$ variables to 0, so $n' = n - j - e$,
  $t' = t - j$ and $s' = s - 2j + e$.
- The entries are the ratio of the inductive bound to the target bound, as in the paper.
- "Ones" and "zeros" list the variables set to 1 and to 0, including forced ones.

The induction we checked is on $n$ alone. It needs one ordering remark (Gap 2), and it uses
the paper's convention that a restriction may be bounded by the bound of any family whose
coefficient is at least as large. The coefficients form a chain:

$$\mathrm{coef}_4 \le \mathrm{coef}_3 \le \mathrm{coef}_{2o} \le \mathrm{coef}_{2d} \le \mathrm{coef}_1 \le \mathrm{coef}_0$$

for both parities.

## Gap 1. P0.4 (triangle configuration): a missing row

**Location.** `phi0.tex`, P0.4. The table has rows in which exactly one of $a,b,c$ is 1,
and rows in which two of them are 1. It has no row with $a = b = c = 0$. That case forces
$d = e = f = 1$, which is consistent.

**Counterexample.** Take the "prism" on $n = 9$ variables:

$$\lbrace a,b,d\rbrace,\ \lbrace b,c,e\rbrace,\ \lbrace a,c,f\rbrace,\ \lbrace a',b',d\rbrace,\ \lbrace b',c',e\rbrace,\ \lbrace a',c',f\rbrace.$$

- Every variable lies in exactly two clauses, and no pair lies in two clauses. So
  P0.1–P0.3 fail and P0.4 applies.
- There are 6 clauses and each variable meets 2, so $t = 3$. Hence $s = 0$.
- $\lbrace d,e,f\rbrace$ is a minimum transversal with $a = b = c = 0$, and no row of the
  table covers it.

**Repair.** Since P0.3 fails, $d,e,f$ are pairwise distinct: $d = e$ would put
$\lbrace b,d\rbrace$ in two clauses. So the three rows with two of $a,b,c$ set to 1 fix five
variables. They give $n - 5$ and $s - 1$, not the cautious $n - 4$ and $s - 2$. The corrected
table:

| Ones | Zeros | Type | Even $s$ | Odd $s$ |
|---|---|---|---|---|
| $a,e$ | $b,c$ | 0 | $1/6$ | $1/6$ |
| $b,f$ | $a,c$ | 0 | $1/6$ | $1/6$ |
| $c,d$ | $a,b$ | 0 | $1/6$ | $1/6$ |
| $a,b$ | $c,e,f$ | 0 | $7/54$ | $1/7$ |
| $b,c$ | $a,d,f$ | 0 | $7/54$ | $1/7$ |
| $a,c$ | $b,d,e$ | 0 | $7/54$ | $1/7$ |
| $d,e,f$ | $a,b,c$ | 0 | $7/108$ | $1/14$ |
| **Total** | | | $103/108$ | $1$ |

## Gap 2. Type 2d: the coverage lemma

**Location.** `phi2d.tex`, the lemma before P2d.1. Its proof takes the further clauses
of $a$ and $b$ to be 3-clauses, $\lbrace a,e,f\rbrace$ and $\lbrace b,g,h\rbrace$. They can be
2-clauses, and then P2d.1–P2d.5 need not cover $F$. This contradicts the
claim in Section 4 that each $F \in \mathcal{F}_i$ satisfies one of the $P_{i,j}$.

**Counterexample.** Take the 2-clauses

$$\lbrace a,b\rbrace,\ \lbrace a,e\rbrace,\ \lbrace b,e\rbrace,\ \lbrace c,d\rbrace,\ \lbrace c,g\rbrace,\ \lbrace d,g\rbrace.$$

- This is of type 2d: it contains the disjoint 2-clauses $\lbrace a,b\rbrace$ and
  $\lbrace c,d\rbrace$, and no pair lies in three clauses.
- Each of $a,b,c,d$ appears exactly twice, so P2d.1 and P2d.4 fail.
- No clause meets both pairs, so P2d.2 fails.
- No pair lies in two clauses, so P2d.3 fails.
- The further clauses of $a$ and $b$ leave the same remainder $\lbrace e\rbrace$, so
  P2d.5 fails.

**Repair.** A CNF with two 2-clauses that meet in one variable is of type 2o, and
$N_{2o} \le N_{2d}$.
- So prove the type-2o bound before the type-2d bound for the same $n$.
- In the type-2d case, assume that $F$ is not of type 2o. Then every further clause through
  $a,b,c,d$ is a 3-clause, and the paper's case analysis goes through unchanged.
- This needs an order on the families at a fixed $n$, since the paper's induction hypothesis
  covers only smaller $3t-s$ or $t$. Inspecting the proofs, the families use one another at
  the same $n$ only as follows:
  - 2o assumes not 3 and not 4;
  - 2d assumes not 2o;
  - 4 uses 3 (see Gap 6).
- So the order 3, 4, 2o, 2d, 1, 0 works. All restrictions have fewer variables.

## Gap 3. Type 2o, even $s$: a configuration that is not covered

**Location.** `phi2o.tex`, the remark before the list of properties: "if at least one of $b$
or $c$ appears at least three times, then one of P2o.1, …, P2o.8 holds."

**Counterexample.** Take $F = \lbrace ab,\ ac,\ bcd,\ bef\rbrace$.
- Here $b$ appears three times.
- $a$ appears twice, $b$ does not appear four times, and $c$ appears twice. So
  P2o.1–P2o.3 fail.
- Only one clause contains both $b$ and $c$, so P2o.4 fails.
- P2o.5 needs a clause with $c$ but not $b$, and P2o.7 needs two.
- There is no clause $\lbrace c,d,e\rbrace$, so P2o.6 fails.
- Neither $b$ nor $c$ lies in three clauses without the other, so P2o.8 fails.
- $b$ is in three clauses, so P2o.9 and P2o.10 fail.

In general, the uncovered case is: $b$ and $c$ share exactly one clause
$\lbrace b,c,d\rbrace$, $b$ has a further clause $\lbrace b,e,f\rbrace$, and $c$ has no other
clause (or the same with $b$ and $c$ swapped).

**Repair, if $d \notin \lbrace e,f\rbrace$.** Use a new table. If $a = 1$, $b = 0$ and $c = 1$,
then $c$'s critical clause must be $\lbrace b,c,d\rbrace$, so $d = 0$. If $b = c = 1$, then
$a = 0$, since $a$ would have no critical clause. In the two type-1 rows, $\lbrace e,f\rbrace$
survives as a 2-clause.

| Ones | Zeros | Type | Even $s$ |
|---|---|---|---|
| $a,b$ | $c$ | 0 | $7/24$ |
| $a,c$ | $b,d$ | 1 | $5/24$ |
| $a,d$ | $b,c$ | 1 | $5/24$ |
| $b,c$ | $a$ | 0 | $7/24$ |
| **Total** | | | $1$ |

**Repair, if $d \in \lbrace e,f\rbrace$**, that is, $b$'s further clause is $\lbrace b,d,f\rbrace$.
Use the table of P2o.5, Case 2, with the row $b = 1$, $c = 0$ taken as type 0. With
$a = 1$ and $b = 0$, the clauses $\lbrace c,d\rbrace$ and $\lbrace d,f\rbrace$ overlap, which
gives type 2o.

| Ones | Zeros | Type | Even $s$ |
|---|---|---|---|
| $a,b$ | $c,d$ | 0 | $1/4$ |
| $b,c$ | $a$ | 0 | $7/24$ |
| $a$ | $b$ | 2o | $5/12$ |
| **Total** | | | $23/24$ |

## Gap 4. P3p.1 (path of three 2-clauses): a wrong table

**Location.** `phi3_path.tex`, P3p.1. The path is $\lbrace a,b\rbrace$,
$\lbrace b,c\rbrace$, $\lbrace c,d\rbrace$, and $b$ lies in no other clause. The first row
claims that $a = 1$ forces $b = 0$ and $c = 1$. In fact $a = b = 1$, $c = 0$, $d = 1$ is
possible, with $b$'s critical clause $\lbrace b,c\rbrace$.

**Counterexample.** Take $F = \lbrace ab,\ bc,\ cd,\ axy,\ duv\rbrace$, with $n = 8$.
- No two variables hit the path and both 3-clauses, so $t = 3$.
- $\lbrace a,b,d\rbrace$ is a minimum transversal, with critical clauses $axy$, $bc$ and $cd$.
- No row covers it.
- Adding the missing row ($a,b,d$ ones and $c$ zero, ratio $1/6$ for even $s$) gives the total
  $47/42 > 1$.

**Repair.** Split on $c$ instead of $a$.
- If $c = 0$, then $b = d = 1$, and $a = 0$, since $b$ needs a critical clause.
- If $c = 1$, then either $b = 1$ and $a = 0$, or $b = 0$ and $a = 1$.

| Ones | Zeros | Type | Even $s$ | Odd $s$ |
|---|---|---|---|---|
| $b,d$ | $c$ | 0 | $1/3$ | $1/3$ |
| $b,c$ | $a$ | 0 | $1/3$ | $1/3$ |
| $a,c$ | $b$ | 0 | $1/3$ | $1/3$ |
| **Total** | | | $1$ | $1$ |

## Gap 5. P3ie.2 (a 2-clause disjoint from two others, even $s$): a wrong type

**Location.** `phi3_isolated.tex`, P3ie.2, with $a$'s clause $\lbrace a,c,x\rbrace$.
The row $a = c = 0$ (forcing $b = d = x = 1$) is said to be of type 1, because of the 2-clause
$\lbrace e,f\rbrace$.

**Failure.** The property allows $\lbrace c,d\rbrace$ and $\lbrace e,f\rbrace$ to meet, and $x$
is unconstrained.
- If $x \in \lbrace e,f\rbrace$ or $d \in \lbrace e,f\rbrace$, then $\lbrace e,f\rbrace$ is
  satisfied in that row. The restriction need not contain a 2-clause.
- With type 0 that row is $1/7 = 6/42$ instead of $5/42$, and the total is $43/42 > 1$.

**Repair, if $\lbrace c,d\rbrace$ and $\lbrace e,f\rbrace$ meet**, say in $d$, with $f \ne c$.
Then the row $a = 1$ is of type 2o, not just type 2: $\lbrace c,d\rbrace$ and
$\lbrace d,f\rbrace$ survive and overlap.
- If $a$ has a further clause $D_a$ with $d \notin D_a$:

| Ones | Zeros | Type | Even $s$ |
|---|---|---|---|
| $a$ | — | 2o | $4/7$ |
| $b$ | $a$ | 3 | $3/7$ |
| **Total** | | | $1$ |

- If $a$'s further clause is $\lbrace a,d,x\rbrace$:

| Ones | Zeros | Type | Even $s$ |
|---|---|---|---|
| $a$ | — | 2o | $4/7$ |
| $b,d$ | $a$ | 0 | $1/3$ |
| $b,c,f,x$ | $a,d$ | 0 | $1/14$ |
| **Total** | | | $41/42$ |

**Repair, if the pairs are disjoint and $a$'s only further clause is $\lbrace a,c,e\rbrace$.**
Use a further clause of $b$, which exists because P3ie.1 fails. In the type-3 row,
$b$'s further clause leaves a third 2-clause.

| Ones | Zeros | Type | Even $s$ |
|---|---|---|---|
| $b,c$ | $a$ | 1 | $2/7$ |
| $b,d,e$ | $a,c$ | 0 | $1/7$ |
| $a$ | $b$ | 3 | $3/7$ |
| $a,b,d,f$ | $c,e$ | 0 | $1/14$ |
| **Total** | | | $39/42$ |

In the remaining subcase ($x$ avoids both pairs and the pairs are disjoint), the paper's table is
correct.

## Gap 6. Type 4, even $s$: stars

**Location.** `phi3_four2clause.tex`: "we only care about odd values of $s$, as even values are
handled by the three 2-clause case."

**Failure.** This holds only when no variable lies in three 2-clauses. Type 3 is the restricted
class that excludes such "stars", while type 4 does not exclude them.
- The type-4 bound for even $s$ is used in the induction. For example, the row $a = 1$,
  $b = c = 0$ of P2o.7 has $s' = s$.
- A star cannot be bounded through type 2o, since $\mathrm{coef}_4 = 7/12 < 2/3 = \mathrm{coef}_{2o}$.

**Repair, if $a$ lies in four 2-clauses** $\lbrace a,b\rbrace,\lbrace a,c\rbrace,\lbrace a,d\rbrace,\lbrace a,e\rbrace$:

| Ones | Zeros | Type | Even $s$ |
|---|---|---|---|
| $a$ | — | 0 | $6/7$ |
| $b,c,d,e$ | $a$ | 0 | $1/12$ |
| **Total** | | | $79/84$ |

**Repair, if $a$ lies in exactly three 2-clauses** $\lbrace a,b\rbrace,\lbrace a,c\rbrace,\lbrace a,d\rbrace$.
Since $F$ has at least four 2-clauses, some 2-clause $K$ avoids $a$. It survives $a = 1$.

| Ones | Zeros | Type | Even $s$ |
|---|---|---|---|
| $a$ | — | 1 | $5/7$ |
| $b,c,d$ | $a$ | 0 | $1/6$ |
| **Total** | | | $37/42$ |

## Smaller points

- **P0.4.** The proof needs only that P0.3 fails.
- **`lemma:Egraph`.** It is stated without proof, and needs only that P0.3 and
  P0.4 fail. A short proof: if further clauses $\lbrace b,x,u\rbrace$ and
  $\lbrace c,x,v\rbrace$ of two variables of a clause $\lbrace a,b,c\rbrace$ share $x$, they
  form a triangle with $\lbrace a,b,c\rbrace$. Its six variables are distinct because no pair
  lies in two clauses.
- **P2o.2.** Case 2 cannot occur: a common variable of $b$'s three further clauses
  would put a pair in three clauses.
- **P2o.7.** The row $a = 1$, $b = c = 0$ always leaves four distinct 2-clauses, so it is
  of type 4. Case 1's table covers all three cases. In the rows with $j = 2$, "$t-3$" should be
  "$t-2$".
- **P1.2** begins "Assume … satisfies P1.1", which presumably should be
  "does not satisfy".
- **Several tables, including P1.2, P2d.2, P2d.3 and
  P3io.3,** take a further clause to be a 3-clause. It may be a 2-clause. The row then
  leaves a 1-clause, which is harmless: forcing it costs a factor $\le 6/7$ of the smallest
  bound.
- **Some properties assume more than the tables use.** P0.1 needs only a clause with
  $a$ but not $b$. P3p.2 needs only a further clause of $b$. P2d.3, Case 3,
  needs only a further clause of $e$. P3ie.5 and P3ie.6 hold without their
  side conditions.
- **Three 2-clauses with no variable in all three** form a triangle, a path of length 3, or
  contain one 2-clause disjoint from the other two. So the three-way split of type 3 is
  exhaustive without further argument.

## The formal proof

- **Source.** The Isabelle/HOL sources are in the public repository `github.com/ott2/circuitub`:
  - `isabelle/gkprst/Monotone_3CNF.thy`: the theorem, as `gkprst_bound` and `gkprst_half`;
  - `isabelle/gkprst/majority/Majority_3CNF.thy`: the Majority consequence.
- **Lemma names.** Each repaired table above is a lemma of the same name in the source:
  - Gap 1: `p04`;
  - Gap 3: `p2o5_gap`, `p2o5_shared`;
  - Gap 4: `p3p1`;
  - Gap 5: `p3i_e3a`, `p3i_e3b`, `p3i_eG`;
  - Gap 6: `p4_e4`, `p4_e3`.
  - Gap 2 is the hypothesis `¬ infam T2o F` of `type2d`.
- **Audit.** An oracle check confirms that the headline theorems are derived without `sorry`
  or any other unchecked step.
