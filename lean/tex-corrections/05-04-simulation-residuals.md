# Gap in the generalized cube lemma

## Where

`\llem{generalized_cube_lemma}` in `../document/05-04-simulation-residuals.tex`
(proof at lines 353–407). It states that for coinitial derivations $\rho, \sigma$ and $t' \ltimes t$:

$$(\rho/t')/(\sigma/t') \equiv (\rho/\sigma)/(t'/\sigma).$$

Chapter 5 uses it throughout: sieving (`08-18`), the properties of garbage (`08-19`),
and the semilattices of garbage (`08-20`).

## The problem

The proof has two stages. First it proves a partial result (2), where $\rho$ is a single
step $R$, by induction on $\sigma$. Then it proves the general case by induction on
$\rho = R\rho'$, through a chain of seven equalities. Three steps in this do not hold up.

1. **The chain uses an unproved case of the lemma (line 6).** The step
   $$\tfrac{\rho'/(t'/R)}{(\sigma/R)/(t'/R)} \equiv \tfrac{\rho'/(t'/R)}{(\sigma/t')/(R/t')}$$
   is justified "by the partial result (2)". This needs
   $(\sigma/R)/(t'/R) \equiv (\sigma/t')/(R/t')$, where an arbitrary derivation $\sigma$ is
   projected over a single step. That is (2) with the roles swapped, a different case of the
   lemma itself, and neither (2) nor the induction hypothesis on $\rho'$ provides it.
2. **(2) is proved for one step but used for sets.** The proof of (2) applies the induction
   hypothesis to each residual $T \in R/S$ separately. It then reads the resulting family of
   derivations as "the set", i.e. as one development of the union of the residual sets, with no
   argument. The general case uses (2) with $R/\sigma$ in place of a step, which is a complete
   development of a set ("abusing notation"). The partial result is never stated for sets.
3. **One step cites the wrong result (line 4).** The rewrite
   $(t'/\sigma)/(R/\sigma) = (t'/R)/(\sigma/R)$ is cited "by (2)". It is an equation between
   terms and follows from item 1 of Compatibility, since $\sigma(R/\sigma) \equiv R(\sigma/R)$.
   This is a mislabel; the equation itself is true.

The underlying issue is the generalization. Projecting $R\rho'$ over a development $\tau$
leaves $\rho'$ to be projected over $\tau/R$. That is a development of a *set* of residuals,
even when $\tau$ is a single step. So an induction stated only for single steps does not close.

## The fix

Work with names. By *permutation equivalence in terms of names* and *names after a
projection*, the lemma is equivalent to

$$\textsf{names}((\rho/\sigma)/(t'/\sigma)) = \textsf{names}(\rho/t') \setminus \textsf{names}(\sigma/t'). \qquad (\ast)$$

Prove three claims in order:

1. **A step after a derivation.**
   $\textsf{names}((R/\tau)/(t'/\tau)) = \textsf{names}(R/t') \setminus \textsf{names}(\tau/t')$.
   This is by induction on $\tau$, using the basic cube lemma at each step.
2. **A derivation after a complete development.** If $\tau$ is a complete development of a
   set $\mathcal{M}$, then
   $\textsf{names}((\rho/\tau)/(t'/\tau)) = \textsf{names}(\rho/t') \setminus \textsf{names}(\mathcal{M}/t')$.
   This is by induction on $\rho$, **generalizing over $\mathcal{M}$ and $\tau$**. For
   $\rho = R\rho'$, the induction hypothesis is applied to the set $\mathcal{M}/R$ and its
   development $\tau/R$. The proof uses:
   - Claim 1;
   - *simulation residual of a development*, which gives
     $\textsf{names}(\tau/t') = \textsf{names}(\mathcal{M}/t')$;
   - item 1 of Compatibility, for the targets;
   - the basic cube lemma, for $\mathcal{M}/R$;
   - the fact that the names along $\rho/t'$ are pairwise distinct.
3. **$(\ast)$ itself.** This is by induction on $\sigma = S\sigma'$, using Claim 2 with
   $\mathcal{M} = \{S\}$.

Each claim uses only earlier claims and earlier results of the thesis, so there is no
circularity. The patch [`05-04-simulation-residuals.tex.diff`](05-04-simulation-residuals.tex.diff)
replaces the proof with this one. Compiled on its own with the thesis macros, the patched
section has no LaTeX errors. The full thesis was not rebuilt, because the local TeX install
lacks some of its packages.

## In Lean

`Thesis/Chapter4Simulation.lean`, section *Names of simulation residuals*:

| TeX | Lean |
| --- | --- |
| basic cube lemma, as an equation of name sets | `cube_sets` |
| Claim 1 | `cube_gen` |
| names of a complete development | `simNames_complete` (via `simDeriv_of_completeDevelopment`) |
| Claim 2 | `single_gen` |
| Claim 3, i.e. $(\ast)$ | `gen_names` |
| the lemma | `generalized_cube_lemma`, from `gen_names` and `distRS.permEq_iff_names` |
