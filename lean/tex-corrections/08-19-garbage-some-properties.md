# Gap in "The leftmost coarse step has at most one residual"

## Where

`\llem{leftmost_coarse_step_has_at_most_one_residual}` in
`../document/08-19-garbage-some-properties.tex` (lines 464–533). It is used in three places: the characterization of garbage-free
derivations (same file, lines 277 and 285), the sieving-trailing-garbage lemma (line 691),
and `../document/08-20-semilattices-of-garbage.tex` (line 72).

## The problem

The lemma says: if $R_0$ is the leftmost coarse step for $(\rho, t')$ and
$\sigma \sqsubseteq \rho$, then $`\#(R_0/\sigma) \le 1`$. The proof goes by induction on
$`\sigma = S\,\sigma_1`$. It shows that $R_0$ has a single residual $R_1$ after $S$, and then
applies the induction hypothesis to $R_1$ in $(\rho/S, t'/S)$.

The induction hypothesis is about the **leftmost** coarse step. The proof only checks that
$R_1$ is **coarse** for $(\rho/S, t'/S)$ (lines 511–530), not that it is leftmost. That
part is not automatic, because contracting $S$ changes the set of coarse steps:

- $S$ can create new redexes;
- residuals of steps in the argument of $S$ get copied;
- a step that was not coarse before can have a residual that is coarse after $S$.

There is also a typo at line 489: "$R$ is to the left of $S$" should be "$R_0$ is to the
left of $S$".

## The fix

Read "leftmost" as the pre-order $\prec$ on positions: ancestors first, then left to
right. This is the order of redexes by their first symbol. Then prove that the invariant
"$R_0 \prec S'$ for every other coarse step $S'$" survives contracting $S$. Let $S'$ be a
coarse step after $S$, other than $R_1$.

- **$S'$ is created by $S$.** By *garbage only creates garbage*, $S$ is not garbage, so $S$
  is coarse and $R_0 \prec S$. A created redex sits at or below $S$, or at the parent of
  $S$. The parent was not a redex before, because its left subterm $S$ is an application.
  In both cases $R_1 = R_0 \prec S'$.
- **$S'$ is a residual of some $T \ne S, R_0$.** Then $T$ is not garbage, by the cube
  lemma on names. There are two subcases:
  - $T$ is in the argument of $S$. Then $S$ is not garbage, so $R_0 \prec S \prec T$.
  - Otherwise, $S'$ is the only residual of $T$, so $T \sqsubseteq S(\rho/S) \equiv \rho$.
    Then $T$ is coarse, and $R_0 \prec T$.

  Contracting $S$ preserves $\prec$ in two situations: when $R_0 \prec S$, or when neither
  $R_0$ nor $T$ lies in the argument of $S$. The second holds whenever $S$ is garbage. So
  $R_1 \prec S'$.

The patch [`08-19-garbage-some-properties.tex.diff`](08-19-garbage-some-properties.tex.diff)
adds the definition of $\prec$, the two positional facts above, and this third item to
the inductive step. It also fixes the typo.

## In Lean

`Thesis/Chapter5FactorizationAppendix.lean`, section *Positional lemmas for the leftmost
coarse step*:

| Lean | Role |
| --- | --- |
| `PosLt` (with `trans`, `trichotomy`, `redexes_sorted`) | the pre-order $\prec$; `redexes t` is sorted by it, so the sieve's `find` picks the $\prec$-least coarse step |
| `residuals_card_one` | a step outside the argument of $S$ has exactly one residual |
| `order_preserved` | contraction preserves $\prec$ under the two conditions above |
| `created_position`, `not_isRedexAt_parent`, `PosLt.lt_parent` | where created redexes lie |
| `leftmost_least` | the lemma with the strengthened invariant (`hK`) |
| `sieve_least`, `sieve_garbageFree` | the uses in the sieve |

Lean proves the form the sieve actually uses, rather than "$`\#(R_0/\sigma) \le 1`$". If a
prefix $\sigma \sqsubseteq \rho$ already contracts every λ^dist-redex simulating $R_0$, then
$R_0 \sqsubseteq \sigma$. The induction and the invariant are the same as above.
