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

## Still to do

- Types 2o, 2d, 3, 4.
- The reductions (1-clauses, subsumed clauses, unused variables, $t = 0$).
- The main induction and the Majority corollary.
