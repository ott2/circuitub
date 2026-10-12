# Formalizing GKPRST26 (arXiv:2601.04072): findings

Theory: `isabelle/gkprst/Monotone_3CNF.thy` (session `Monotone_Sigma3`).

## Framework

- The induction is on $n = \lvert V\rvert$ alone, for all $t$ at once: every row of every table
  fixes at least one variable.
- The paper's "facts used without proof" are facts about the bound functions themselves:
  - $N_i(s,t) \le N_i(s',t)$ for $s' \le s$ follows because $\mathrm{bound}_i$ decreases in $s$
    (`bound_mono`).
  - $N_{2o} \le N_{2d}$ follows from $2/3 \le 25/36$ and $5/9 \le 5/9$.
- A CNF with a clause of size $\le 1$ obeys every family's bound: forcing the variable gives
  $\tfrac12\,\mathrm{bound}_0$, at most $6/7$ of the smallest bound. So restrictions that
  create 1-clauses need no special care.
- "No pair in three clauses" is inherited by every restriction (`npair_restr`).

## Type 0

- **P0.1** (`p01_with`, `p01_sep`, `p01`): correct. The second table needs only a clause
  containing $a$ but not $b$. The paper also assumes a clause with $b$ but not $a$; it is
  not used.
- **P0.2** (`p02`, `del_type3`): correct, and tight (sums $1$, $1$). If $a$ lies in four or more
  clauses, the restriction has four or more 2-clauses. It is still of type 3 in the paper's
  restricted sense, because no variable can be in three of them.
- **P0.3** (`p03`): correct (sums $17/18$, $1$).
- **P0.4, gap** (`p04`): the table has no row for $a = b = c = 0$, which forces
  $d = e = f = 1$.
  - Such transversals exist. Take the prism: triangles
    $\lbrace a,b,d\rbrace,\lbrace b,c,e\rbrace,\lbrace a,c,f\rbrace$ and
    $\lbrace a',b',d\rbrace,\lbrace b',c',e\rbrace,\lbrace a',c',f\rbrace$, with $n = 9$, $t = 3$, $s = 0$.
    Every variable is in two clauses and no pair is in two clauses, so P0.4 applies. Yet
    $\lbrace d,e,f\rbrace$ is a minimum transversal, and no row covers it.
  - Repair: since P0.3 fails, $d, e, f$ are distinct ($d = e$ would put $\lbrace b,d\rbrace$ in two
    clauses). So the rows with two of $a,b,c$ set five variables ($n-5$, $s-1$, ratios
    $7/54$ and $1/7$), not the paper's cautious $n-4$, $s-2$ ($1/6$).
  - The missing row has ratios $7/108$ and $1/14$. The corrected sums are $103/108$ (even $s$)
    and $1$ (odd $s$), so the step still goes through, and is tight for odd $s$.
- **P0.5** (`p05`): correct (sums $103/108$, $187/189$). It needs the arms pairwise disjoint,
  which the paper's lemma `lemma:Egraph` supplies; the definition of the E configuration
  alone does not.
- **P0.6** (`p06_both`, `p06_one`): correct (sums $283/324$, $19/21$ and $1$, $1$). The
  "domination" remark in the second case is unnecessary: the type-0 bound covers $c$ lying
  in another clause directly.

- **Coverage** (`type0`, with `meet_tri`): correct; every type-0 CNF with $t \ge 1$ meets one of
  P0.1–P0.6.
  - The paper states `lemma:Egraph` without proof. The proof is short. Suppose the further
    clauses $D_1 = \lbrace b,x,u\rbrace$ and $D_2 = \lbrace c,x,v\rbrace$ of two variables of
    $\lbrace a,b,c\rbrace$ share $x$. Then $\lbrace b,x,u\rbrace,\lbrace x,c,v\rbrace,\lbrace b,c,a\rbrace$
    is a triangle, and its six variables are distinct because no pair is in two clauses.
  - The lemma needs only that P0.3 and P0.4 fail. The paper also assumes that P0.2 fails,
    which is not needed.
  - The E configuration needs a clause to exist, which follows from $t \ge 1$.

## Type 1

- **P1.1** (`p11`): correct (sums $14/15$, $1$).
- **P1.2** (`p12`): correct and tight (sums $1$, $1$), with two small omissions.
  - The paper takes $a$'s further clause to be a 3-clause $\lbrace a,c,d\rbrace$. It may be a
    2-clause $\lbrace a,c\rbrace$; then the row $a=0$, $b=1$ leaves the 1-clause
    $\lbrace c\rbrace$, which the size-$\le 1$ disjunct of the induction covers.
  - $b \notin D$ needs the antichain assumption, which the paper leaves implicit.
  - Typo: the paper's P1.2 begins "Assume … satisfies P1.1".
- **Coverage** (`type1`): immediate. Either $a$ or $b$ lies only in $\lbrace a,b\rbrace$ (P1.1,
  swapping if needed), or $b$ lies in a further clause (P1.2 with $a$ and $b$ swapped).

## Families: domination

- A row may use family $k$ when the restriction lies in any family $k'$ with
  $\mathrm{coef}_{k'} \le \mathrm{coef}_k$ (`fam_le`, `fam_ok`). The families form a chain:
  $4 \le 3 \le 2o \le 2d \le 1 \le 0$.
- This is needed in two places:
  - Rows whose restriction the paper calls type 3 can have four or more 2-clauses, since the
    other 2-clauses of $F$ survive. That is type 4 (`t3_or_t4`).
  - Where the paper says "type 2", the restriction is 2o or 2d (`infam_2`).

## Type 2d

- **Coverage gap: P2d.1–P2d.5 do not cover type 2d as stated.** The paper's lemma before
  P2d.1 takes the further clauses of $a$ and $b$ to be 3-clauses $\lbrace a,e,f\rbrace$,
  $\lbrace b,g,h\rbrace$. They can be 2-clauses.
  - Example: 2-clauses $\lbrace a,b\rbrace,\lbrace a,e\rbrace,\lbrace b,e\rbrace$ and
    $\lbrace c,d\rbrace,\lbrace c,g\rbrace,\lbrace d,g\rbrace$. Each of $a,b,c,d$ is in exactly two
    clauses, no clause meets both pairs, and no pair is in two 3-clauses. So none of
    P2d.1–P2d.4 holds, and P2d.5 fails because $\lbrace e\rbrace = \lbrace e\rbrace$.
  - Repair: a CNF with two 2-clauses that meet is of type 2o, and $N_{2o} \le N_{2d}$. So prove
    2o before 2d at each $n$, and in the 2d proof assume $\neg$2o (`type2d` has the
    hypothesis `¬ infam T2o F`). Then every further clause through $a,b,c,d$ is a 3-clause
    (`no2o_three`), and the paper's case analysis goes through.
- **P2d.1** (`p2d1_sep`, `p2d1_com`, `p2d1`): correct (sums $24/25$, $19/20$ and $47/50$, $23/24$).
  - In the first case the row $a=0$, $b=1$ is of type 3 only if $F$ has no other 2-clauses;
    otherwise it is of type 4.
  - In the second case the paper's "$e=f=d$" means that both further clauses contain $d$.
- **P2d.2** (`p2d2`): correct and tight (sums $1$, $1$). The clause through $a$ and $c$ may be
  the 2-clause $\lbrace a,c\rbrace$, which leaves a 1-clause.
- **P2d.3** (`p2d3_cross`, `p2d3_uniq`, `p2d3_other`): correct (sums $24/25$, $19/20$; $1$, $1$;
  $49/50$, $1$).
  - Case 3 needs only a further clause through $e$; the paper also assumes one through $f$.
    So the split is "$e$ is in no other clause" (Case 2) versus "$e$ is" (Case 3).
  - $e$'s further clause may be a 2-clause, which leaves a 1-clause.
- **P2d.4** (`p2d4`): correct (sums $24/25$, $1$).
- **P2d.5** (`p2d5`): correct (sums $24/25$, $1$). The row $a=b=1$ fixes three zeros, chosen as
  $e$, $f$ and a $g \notin \lbrace e,f\rbrace$, so its size is exactly 3.
- **Coverage** (`type2d`, assuming $\neg$2o): P2d.1 → P2d.2 → P2d.3 → P2d.4 → P2d.5, with the
  symmetries $a \leftrightarrow b$, $c \leftrightarrow d$, $\lbrace a,b\rbrace \leftrightarrow \lbrace c,d\rbrace$.

## Type 2o

The 2-clauses are $\lbrace a,b\rbrace$ and $\lbrace a,c\rbrace$. `type2o` assumes $\neg$T3 and $\neg$T4,
which are proved first at each $n$. Then every further clause through $b$ or $c$ is a 3-clause
(`no34_three`, `side3`).

- **Odd $s$** (`p2o_odd`): correct (sum $1$).
- **P2o.1** (`p2o1`): correct (sum $1$). $a$'s further clause may be a third 2-clause
  $\lbrace a,x\rbrace$, which leaves a 1-clause.
- **P2o.2** (`p2o2`): correct (sum $1$). Case 2 cannot occur: a variable common to $b$'s three
  further clauses would put a pair in three clauses, contradicting "no pair in three clauses".
- **P2o.3** (`p2o3`): correct (sum $7/8$).
- **P2o.4** (`p2o4`): correct (sum $1$).
- **P2o.5** (`p2o5_sep`, `p2o5_shared`): correct (sums $1$ and $23/24$; the paper's Case 2 total
  is $11/12$).
  - The split is "$d \in \lbrace e,f\rbrace$ or not", where $\lbrace b,e,f\rbrace$ is $b$'s further
    clause. The paper splits on $d \in \lbrace e,f,g,h\rbrace$.
  - In Case 2, the row $b=1$, $c=0$ may use type 0, which makes the table also cover the next
    point.
- **Coverage gap: P2o.1–P2o.10 miss the following CNFs.** $b$ and $c$ share exactly one clause
  $\lbrace b,c,d\rbrace$, $b$ has a further clause $\lbrace b,e,f\rbrace$, and $c$ has none, so
  $c$ lies only in $\lbrace a,c\rbrace$ and $\lbrace b,c,d\rbrace$ (or the same with $b$ and $c$
  swapped).
  - The paper's remark "if at least one of $b$ or $c$ appears at least three times, then one of
    P2o.1–P2o.8 holds" is false here. P2o.5 needs further clauses for both $b$ and $c$, and
    P2o.6–P2o.8 need no common clause.
  - Repair, if $d \notin \lbrace e,f\rbrace$ (`p2o5_gap`): $c=1$, $b=0$ forces $d=0$. Rows
    $(b,c) = (1,0)$: type 0, $7/24$; $(0,1)$: $d=0$, type 1, $5/24$; $(0,0)$: $d=1$, type 1,
    $5/24$; $(1,1)$: $7/24$. The sum is exactly $1$.
  - Repair, if $d \in \lbrace e,f\rbrace$: the P2o.5 Case 2 table with type 0 in the first row
    (`p2o5_shared`), sum $23/24$.
- **P2o.6** (`p2o6`): correct (sum $23/24$). The paper's type "2" row is 2o or 2d.
- **P2o.7** (`p2o7`): correct, and simpler than in the paper (sum $1$).
  - The row $a=1$, $b=c=0$ leaves four distinct 2-clauses, so it is of type 4 however they
    overlap.
  - So Case 1's table covers all cases, and Cases 2 and 3 are not needed.
  - The paper's "$t-3$" in the rows with $j=2$ is a typo for $t-2$.
- **P2o.8** (`p2o8_sep`, `p2o8_com`): correct (sums $35/36$, $47/48$). In Case 1 the row
  $a=1$, $b=0$, $c=0$ may be of type 4 rather than type 3.
- **P2o.9** (`p2o9_uniq`, `p2o9_other`): correct (sums $1$, $23/24$).
- **P2o.10** (`p2o10`): correct (sum $23/24$). Here $b$'s and $c$'s further pairs may meet or
  coincide; the row $a=b=1$ then leaves a clause of size $\le 1$.
- **Coverage** (`p2o_even`, `p2o_E5`, `p2o_E6`, `type2o`). The case split:
  1. $a$ in a third clause (P2o.1).
  2. $b$ or $c$ in $\ge 3$ further clauses (P2o.2).
  3. $b$ or $c$ in none (P2o.3).
  4. Two common clauses (P2o.4).
  5. One common clause: P2o.5, the missed case, or P2o.9.
  6. No common clause: P2o.6, P2o.7, P2o.8, or P2o.10.

## Type 3

Type 3 means at least three 2-clauses, with no variable in three of them. `type3` uses only the
induction hypothesis, so it holds whatever the number of 2-clauses. Three distinct such 2-clauses
always form one of three configurations: a triangle, a path of length 3, or one 2-clause
disjoint from the other two. So the paper's three-way split is exhaustive (`type3`).

- **Triangle** (`p3t1`, `p3t2`, `p3t3`, `p3_tri`): correct (sums $1$, $1$; $1$, $26/27$;
  $13/14$, $8/9$).
- **Path P3p.1 (`p3p1`): the table is wrong.** Here $b$ lies only in $\lbrace a,b\rbrace$ and
  $\lbrace b,c\rbrace$.
  - The paper claims that $a=1$ forces $b=0$, $c=1$. But $a=b=1$, $c=0$, $d=1$ is possible.
  - Counterexample: in $F = \lbrace ab, bc, cd, axy, duv\rbrace$ we have $t = 3$, and
    $\lbrace a,b,d\rbrace$ is a minimum transversal that no row covers.
  - Adding that row overshoots: $47/42$ for even $s$.
  - Repair: split on $c$. If $c=0$, then $b=d=1$. If $c=1$, then $b=1$, $a=0$ (by $b$'s
    critical clause) or $b=0$, $a=1$. The three rows are each $1/3$, so the table is tight:
    sums $1$, $1$.
- **Path P3p.2** (`p3p2`): correct (sums $1$, $17/18$). It needs only a further clause through
  $b$; the paper also assumes one through $c$.
- **Isolated 2-clause, odd $s$** (`p3i_o1`, `p3i_uniq`, `p3i_o3`): correct (sums $1$, $25/27$,
  $17/18$). In P3io.3, $a$'s further clause may be a 2-clause.
- **Isolated 2-clause, even $s$: P3ie.2 is wrong in two subcases, and the coverage is
  rebuilt** (`p3_iso`).
  - In P3ie.2 ($a$'s clause $\lbrace a,c,x\rbrace$), the row $a=c=0$ is claimed to be of type 1
    via $\lbrace e,f\rbrace$. That fails if $x \in \lbrace e,f\rbrace$ or if $d \in \lbrace e,f\rbrace$;
    with type 0 the sum is $43/42$.
    - The overlap case is covered with the type-2o row $a=1$ (`p3i_e3a`, `p3i_e3b`: sums $1$,
      $41/42$).
    - The case $a$'s only further clause is $\lbrace a,c,e\rbrace$ needs a new four-row table
      that also uses a further clause of $b$ (`p3i_eG`, sum $39/42$).
  - P3ie.6 holds without its side conditions. Two further clauses through $a$ make the row
    $a=0$, $b=1$ of type 4, however they meet (`p3i_e2`).
  - P3ie.5 likewise holds without its side conditions: it suffices that $D_c - \lbrace c\rbrace
    \ne D_a - \lbrace a\rbrace$ (`p3i_e6`).
  - The coverage lemma's final step goes through. If no case applies, then
    $D_v - \lbrace v\rbrace = D_a - \lbrace a\rbrace$ for $v = c,d$. That puts a pair in three
    clauses, or a variable in three 2-clauses.
  - The other tables: `p3i_uniq` (sum $20/21$), `p3i_e4` (sum $37/42$, $a$ in a 2-clause
    $\lbrace a,c\rbrace$), `p3i_e5` (sum $1$, P3ie.2 when $x$ avoids both pairs).

## Type 4

`type4` uses `type3` (for even $s$).

- **Odd $s$** (`p4_1`, `p4_2`, `p4_3`): correct (sums $16/17$, $16/17$, $1$).
- **Even $s$: a gap.** The paper says even $s$ "is handled by the three 2-clause case". That
  holds only when no variable lies in three 2-clauses: then $F$ is of type 3, and the bounds
  for types 3 and 4 coincide for even $s$ (`bound_T3_T4`).
  - With such a "star" at $a$, two new tables are needed. If $a$ lies in four 2-clauses: rows
    $a=1$ (type 0) and $a=0$, forcing four 1s; sum $79/84$ (`p4_e4`).
  - If $a$ lies in exactly three 2-clauses, some other 2-clause avoids $a$: rows $a=1$ (type 1)
    and $a=0$; sum $37/42$ (`p4_e3`).

## Order of the families at a fixed $n$

The coverage proofs use bounds for other families at the same $n$ only through domination:
- 2o assumes $\neg$3 and $\neg$4.
- 2d assumes $\neg$2o.
- 4 uses 3 for even $s$.

So the order is 3, 4, 2o, 2d, 1, 0. All restricted CNFs have fewer variables.

## The main theorem (formal)

- **`gkprst_bound`.** Let $F$ be a monotone CNF over $V$ with clauses of size $\le 3$
  (`cnf V F`) and no transversal of size $< t$ (`thr V F t`). Then it has at most
  $\mathrm{bound}_0(3t - n, t)$ transversals of size $t$: $(2/3)^{s/2}3^t$ for even $s$, and
  $\tfrac79(2/3)^{(s-1)/2}3^t$ for odd $s$.
- **`gkprst_half`.** For $n = 2t$ the bound is at most $6^{n/4}$. It is exact for $4 \mid n$;
  for $n \equiv 2 \pmod 4$ it is $\tfrac73 6^{(n-2)/4} \le \sqrt6\, 6^{(n-2)/4}$.
- **The reductions** (`step`), checked formally:
  - $t = 0$: at most one transversal, $\emptyset$, and only if $F = \emptyset$, which forces
    family 0 (`bound_T0_0`).
  - An empty clause gives no transversals.
  - A 1-clause is forced (ratio $\le 14/17$, `ratio_T0_1_0`).
  - Keeping only the inclusion-minimal clauses changes neither the transversals nor the
    family (`infam_mono`).
  - Unused variables lie in no minimum transversal, so they are dropped (`bound_mono`).
- **`IH_all`**: induction on $n$ alone.
- **Conclusion.** The paper's theorem is true. Every gap found has a repair within the same
  induction; no bound or constant changes.

## The Majority bound (formal)

- **Where:** session `GKPRST_Majority`, `isabelle/gkprst/majority/Majority_3CNF.thy`.
- **`majority_mcnfs`:** a list of monotone 3-CNFs (`MCNF 3`) whose OR is Majority on $n$
  (even) variables has length $\ge \binom{n}{n/2}/6^{n/4}$.
- **`majority_mcnfs_exp`:** $(2/6^{1/4})^n \le (n+1) L$.
- **`majority_mcnf_formula`:** the same two bounds for the gate count of the OR formula.
- **The bridge `eval_pcnf`:** on inputs inside $\lbrace 0,\dots,n-1\rbrace$, a monotone CNF
  accepts $X$ exactly when $X$ hits its clause sets restricted below $n$. Each CNF then has
  threshold $n/2$, so `gkprst_half` applies.
- **Audit:** `Audit_GKPRST.thy` fails the build if `gkprst_bound`, `gkprst_half`, `IH_all` or
  the Majority theorems depend on an oracle.
- Nothing in the paper's Majority corollary needed repair.

## Still to do

- Optional: the odd-$n$ Majority bound, from `gkprst_bound` with $t = (n+1)/2$.
