# Fragile Points Around Subject Expansion and Backwards Simulation

## Verified status

The proof that **refinability characterizes head normalization** (`\lprop{has_hnf_has_refinement}` in `../document/05-03-hnf.tex`, appendices `../document/08-14-hnf-has-refinement.tex` and `../document/08-15-has-hnf-has-refinement.tex`, `has_hnf_iff_refinable` in `Thesis/Chapter4Simulation.lean`) is the most delicate part of the thesis, because expanding a β-step backwards in λ^dist interacts subtly with label uniqueness and sequentiality.

The **backwards-expansion gap is now closed in Lean**. Correctness and strong sequentiality
are proved for the reconstructed terms, including expansion inside arbitrary contexts and
sequential reconstruction of sibling arguments. The original `Correct`, typing rules,
reduction constructors (`DStep`), and `Refines` definitions have not been weakened or altered.

The principal results in `Thesis/Chapter4SimulationAppendix.lean` (and used in `Thesis/Chapter4Simulation.lean`) are
`subject_expansion_strong`, `refinement_substitution_inverse`,
`backwards_simulation_in_context`, `backwards_simulation`,
`backwards_multisimulation`, and `head_normalizing_has_strong_refinement`.
The last theorem proves the complete **$(3 \implies 2)$** implication independently of
forward simulation and residual theory. `hnf_has_refinement` in `Thesis/Chapter4Simulation.lean` is also proved.

Validation:
- Full `lake build` passes.
- An automated `#print axioms` dependency audit of 19 principal lemmas (including `subject_expansion`, `subject_expansion_strong`, `hnf_has_refinement`, and `head_normalizing_has_strong_refinement`) permits only `propext`, `Classical.choice`, and `Quot.sound`; **none depends on `sorryAx`**.
- The full `has_hnf_iff_refinable` equivalence is proved; its backward $(3 \implies 2)$ implication uses `head_normalizing_has_strong_refinement`.
- `../document/08-15-has-hnf-has-refinement.tex` itself is kept unchanged; the corresponding LaTeX prose patch (stating Controlled Subject Expansion explicitly and explaining exact cut tracking, freshness in the whole context, sequential sibling reconstruction, and the raw partition substitution convention for expansion) is stored in [`08-15-has-hnf-has-refinement.tex.diff`](08-15-has-hnf-has-refinement.tex.diff).
- No `sorry` remains anywhere in `Thesis/`.

---

## Blast-radius isolation (dependency map)

Even if Subject Expansion and Backwards Simulation were omitted altogether, almost nothing else in the thesis depends on them:

- `\llem{subject_expansion}`, `\llem{refinement_substitution_inverse}`, and `\llem{backwards_simulation}` appear **only** in `../document/08-15-has-hnf-has-refinement.tex` (with typing expansion invoked at lines 123, 295, and 379: abstraction decomposition, application decomposition, and the argument case of backwards simulation).
- They are used **exclusively** for the implication **$(3 \implies 2)$** (hence $(3 \implies 1)$: *every head-normalizing λ-term has a refinement*) of `\lprop{has_hnf_has_refinement}`.
- **Completely independent of Subject Expansion / Backwards Simulation:**
  - All of Chapter 2 (`../document/03-distributive.tex`, `Thesis/Chapter2DistLambdaCalc{Defs,Appendix,}.lean`): Unique Typing, Linearity, Subject Reduction, Strong Normalization, Strong Permutation, Confluence.
  - All of Chapter 3 (`../document/04-residual-theory.tex`, `Thesis/Chapter3ResidualTheory{Defs,Appendix,}.lean`): orthogonality of λ^dist, creation/stability, and $\mathbb{D}^{\mathtt{\#}}(t')$ being a distributive lattice and ring of sets.
  - Forward Simulation, Reverse Simulation (`../document/05-02-simulation.tex` — which projects $\to_{\mathtt{\#}}$ *forward* to $\to_\beta$, not backwards), $(1 \implies 3)$ of `has_hnf_has_refinement`, `hnf_has_refinement`, Cube Lemmas, Compatibility, and Algebraic Simulation (`Thesis/Chapter4Simulation{Defs,}.lean`).
  - All of Chapter 5 (`../document/06-factorization.tex`, `Thesis/Chapter5Factorization{Defs,Appendix,}.lean`): garbage, sieving, the garbage-free lattice $\mathcal{F}$, the lax 2-functor $\mathcal{G}$, and the Grothendieck Factorization Theorem $\mathbb{D}^\lambda(t) \simeq \int_{\mathcal{F}} \mathcal{G}$, which take a refinement $t' \ltimes t$ as an input hypothesis and only step $t'$ forward via $t'/\rho$.

---

## Fragility 1: $\to_{\mathtt{\#}}$-expansion breaks plain correctness (Closed in the thesis & Lean)

### Why naive Subject Expansion / Backwards Simulation fails

In λ^dist, every type ($\alpha^\ell$ or arrow $\mathcal{M} \xrightarrow{\ell} \tau$) has an external label $\ell$, and every $\lambda^\ell$ introduces an arrow $\xrightarrow{\ell}$ with its label (`../document/03-01-types.tex`, `../document/03-02-syntax.tex`).

Plain **correctness** (`\ldef{sequentiality_and_correctness}` in `../document/03-02-syntax.tex`, `Correct` in `Thesis/Chapter2DistLambdaCalcDefs.lean`) requires:
1. pairwise distinct $\lambda$-labels across the term, and
2. **sequentiality** within each *individual* multiset $[A_1, \dots, A_n]$ (in contexts $\Gamma(x)$ and in arrow domains $[A_1, \dots, A_n] \xrightarrow{\ell} B$, packaged as `Ty.Sequential` in `Thesis/Chapter2DistLambdaCalcAppendix.lean`): its elements must have pairwise distinct external labels.

Note that `Correct` does **not** require global uniqueness of all arrow labels inside type annotations: `correct_repeated_arrow_labels` (`Thesis/Chapter2DistLambdaCalcAppendix.lean`) proves that a single variable annotated with $[] \xrightarrow{7} [] \xrightarrow{7} \alpha^8$ is `Correct` (constructed via the compositional lemmas `Correct.var` and `Correct.app`).

Reduction ($\to_{\mathtt{\#}}$) splits elements of an already-sequential multiset apart, preserving correctness. Expansion ($\leftarrow_{\mathtt{\#}}$) does the opposite: it **gathers** disjoint subterms $s'_1, \dots, s'_n$ into a single argument list $(\lambda^\ell x.\, t')[s'_1, \dots, s'_n]$, merging their types into a single multiset $[\tau_1, \dots, \tau_n] \xrightarrow{\ell} \sigma$ (and $x : [\tau_1, \dots, \tau_n]$).

Plain correctness of the reduced term does **not** prevent two disjoint subterms from
having different types with the same external label. A typable example is obtained from
$u = f\,w$, with refinements
- $u'_1 = f^{[] \xrightarrow{5} \alpha^0}[] : \alpha^0$,
- $u'_2 = f^{[] \xrightarrow{6} \beta^0}[] : \beta^0$.

Let $Z = [\alpha^0] \xrightarrow{2} [\beta^0] \xrightarrow{3} \gamma^1$. Then
$$s' = z^Z[u'_1][u'_2]$$
is correct: the context for $f$ contains two types with distinct external labels 5 and 6,
each arrow domain in $Z$ is a singleton, and there are no lambdas. Expanding along
$$(\lambda x.\,z\,x\,x)\,(f\,w) \to_\beta z\,(f\,w)\,(f\,w)$$
gives the typable term
$$t' = (\lambda^4 x.\,z^Z[x^{\alpha^0}][x^{\beta^0}])[u'_1,u'_2].$$
Its new binder domain $[\alpha^0,\beta^0]$ is not sequential. The types are distinct,
so type-directed lookup selects the intended argument at each occurrence; the failure
also occurs for the existing `DStep`, independently of the partition relation.

This is proved in `Thesis/Chapter2DistLambdaCalcAppendix.lean` by
`correctness_subject_expansion_counterexample` and
`correctness_dStep_expansion_counterexample`. Notice that all old arrow labels
(2, 3, 5, 6) are distinct: distinct arrow labels alone do not prevent this failure.
(An earlier note used closed refinements of $(\lambda q.\,q\,q)(\lambda r.\,r)$ with claimed atomic result type, which were not typable as written because $\lambda^2 r.\,r^{\alpha^0}$ has type $[\alpha^0]\xrightarrow{2}\alpha^0$ rather than $[]\xrightarrow{2}\alpha^0$; the $f\,w$ witnesses above replace them.)

### How the thesis closes it

In git history, earlier drafts (prior to commit `59d860b`, April 22, 2018) stated `backwards_simulation` over $\mathcal{T}^{\mathtt{\#}}$ (correct terms) with a `\TODO`. Commit `59d860b` resolved this (`../document/05-03-hnf.tex` lines 85–86; `../document/08-15-has-hnf-has-refinement.tex` lines 34–83):
1. `\llem{subject_expansion}` is stated **only for raw typing** ($\Gamma \vdash \dots : \tau$), making no claim about correctness.
2. Correctness is strengthened to **strong sequentiality** (`../document/08-15-has-hnf-has-refinement.tex`, lines 60–66; `StronglySequential` in `Thesis/Chapter4SimulationAppendix.lean`, proved strictly stronger than `Correct` in `correct_not_stronglySequential`): in every subterm $s \in \mathsf{sub}(t)$, any two free subterms $s_1, s_2 \in \mathsf{sub}^\circ(s)$ at disjoint positions have distinct external labels.
3. The canonical refinement of an HNF (`../document/08-14-hnf-has-refinement.tex`) uses empty argument lists `[]` everywhere, so its subterm positions form a single linear chain with no disjoint pairs; hence it is vacuously strongly sequential.

---

## Fragility 2: Typing Subject Expansion vs. definitions of substitution (Closed in Lean)

`../document/08-15-has-hnf-has-refinement.tex` (lines 22–26) states:
> If $\Gamma \vdash \mathtt{C}\langle t\{x := \vec{s}\}\rangle : \tau$ is derivable, then $\Gamma \vdash \mathtt{C}\langle (\lambda^\ell x.\, t)\vec{s}\rangle : \tau$ is derivable.

Formalizing this uncovered three specification subtleties:

1. **Type-directed lookup fails Subject Expansion when $\vec{s}$ has duplicate types.**
   `../document/03-03-the-calculus.tex` defines both **partition-based** substitution $t\{x := \vec{s}\}$ (lines 21–43) and **type-directed ("alternative")** substitution $t\{\!\{x := \vec{s}\}\!\}$ (lines 96–117, `DTerm.subst` in `Thesis/Chapter2DistLambdaCalcDefs.lean`). Sequential argument labels guarantee agreement. Outside that domain agreement is not guaranteed.
   - Counterexample (`typeDirected_subject_expansion_counterexample` in `Thesis/Chapter2DistLambdaCalcAppendix.lean`): for $t = z^{[\tau]\to[\tau]\to\sigma}[x^\tau][x^\tau]$ and $\vec{s} = [a^\tau, b^\tau]$, we have $\mathtt{T}_x(t) = [\tau,\tau] = \mathtt{T}(\vec{s})$ and typable $t, a^\tau, b^\tau$, yet type-directed `DTerm.subst` selects $a^\tau$ for both occurrences of $x^\tau$, yielding $z[a^\tau][a^\tau]$ with context $\{z:\dots, a:[\tau,\tau]\}$. By `linearity` at the index of $b$, that context omits $b$, so it cannot type $(\lambda^\ell x.\, t)[a^\tau, b^\tau]$.
2. **Implicit resource-matching precondition $\mathtt{T}_x(t) = \mathtt{T}(\vec{s})$ (and typable arguments).**
   Unlike System $\mathcal{W}$ on pure λ-terms (where $(\lambda x.\, y) s$ can type an unused $s$ with $0$ premises), $(\lambda^\ell x.\, t)\vec{s}$ in λ^dist carries an explicit argument list $\vec{s}$ whose types must match the free occurrences of $x$ in $t$. In the thesis this is implicit in writing the partial operation $t\{x := \vec{s}\}$.
3. **Domain circularity with `Correct`.**
   `../document/03-03-the-calculus.tex` (line 23) formally defines $t\{x := \vec{s}\}$ only on *correct* terms, yet `refinement_substitution_inverse` (`../document/08-15-has-hnf-has-refinement.tex`) invokes `subject_expansion` *in order* to prove that $(\lambda^\ell x.\, t')\vec{s}'$ is typable/correct.

### How Lean closes it

The following Chapter 2 results (in `Thesis/Chapter2DistLambdaCalcDefs.lean`, `Thesis/Chapter2DistLambdaCalcAppendix.lean`, and `Thesis/Chapter2DistLambdaCalc.lean`) are proved without any `sorryAx` dependency:
- Syntactic typing determination without correctness assumptions: `hasType_ty`, `hasType_ctx`, `hasType_unique`, and `hasType_iff` (closing `unique_typing` in `Chapter2DistLambdaCalc.lean`).
- Context and multi-typing infrastructure: `Ctx.shift`, `Ctx.remove`, `Ctx.insert`, `HasType.shift`, and `HasTypeMulti.{append, perm, replace, types_eq, perm_types, split_types, partition}`.
- Mutual relations `PSubst` / `PSubstMulti` (`Chapter2DistLambdaCalcDefs.lean`) defining partition-based substitution directly on raw `DTerm`s, enforcing $\mathtt{T}_x(t) = \mathtt{T}(\vec{s})$ (`PSubst.occTypes`) and requiring consumed arguments to be typable at the occurrence's type (`var_eq` shifts the inserted argument by binder depth while keeping arguments unshifted in the relation).
- `PSubst.inverse` (reconstructing $\Theta$, $\vec{\Delta}$, $\vec{\sigma}$ from `HasType Γ u ρ`), `subject_expansion_beta`, `DCtx.typing_mono`, and `subject_expansion`, proving exact context- and type-preserving expansion under any capturing one-hole context `DCtx`:
  ```lean
  PSubst t 0 ss u → HasType Γ (C.plug u) τ →
    HasType Γ (C.plug (.app (.lam ℓ t) ss)) τ
  ```
- `PSubst.exists` constructing a raw partition witness from typed arguments and exact occurrence matching, giving `subject_expansion_typeDirected` without requiring a caller-supplied `PSubst` witness.
- `PSubst.eq_subst_of_subset` and `PSubst.eq_subst` proving `PSubst` agrees with `DTerm.subst` whenever `SeqMS (ss.map DTerm.ty)` holds, yielding `subject_expansion_subst` (which applies in the strongly sequential setting of `08-15`).

---

## Fragility 3: Freshness and proper free subterms (Closed in Lean)

### 3a. Finite freshness against the whole current term

In `Thesis/Chapter4SimulationAppendix.lean`, `DTerm.labelSupport` is finite and includes all lambda labels and all labels inside all subterm types, including variable annotations (`DTerm.allTypes` + `Ty.labels`). `exists_fresh_label` chooses a label outside this support and any externally forbidden finite set `avoid`. Avoiding this support is a sufficient, conservative freshness policy; it does not require existing type labels to be globally distinct.

### 3b. Exact tracking of disjoint families, and a contextual induction hypothesis

In `Thesis/Chapter4SimulationAppendix.lean`, `FreeCut` / `FreeCutMulti` record finite antichains of pairwise disjoint free subterm occurrences, retaining each selected occurrence's full typing context and type (`CutEntry := Ctx × Ty`). `FreeCut.lam` crosses a binder only if every selected context has an empty entry for its bound variable. Multisets retain multiplicity, so equal terms or types at different positions remain distinguished.

`StronglySequential` bundles the unchanged `Correct` predicate with `Separated` (distinct external labels in every `FreeCut` of every subterm). `correct_of_separated` reconstructs all original `Correct` conditions (including sequential contexts and new arrow domains) from `Separated`, inherited sequential variable annotations (`AnnotationsSequential`), typability, and unique lambda labels, and `PSubst.correct_parts` supplies correctness of the raw body and arguments without circular premises.

The controlled expansion and backwards-simulation development establishes:

1. `PSubst.lift_cut`: cuts of a reconstructed body survive substitution with unchanged selected types and surrounding-binder contexts.
2. `PSubst.compose_cut`: a body cut independent of the substituted variable combines with cuts of all arguments into a disjoint cut of the contractum, preserving exact contexts and types.
3. `PSubst.track_beta_cut`, `subject_expansion_correct_beta`, and `subject_expansion_strong_beta`: any free cut of the expanded redex tracks back to a cut of the contractum with identical contexts and types plus at most the fresh lambda itself, yielding correctness and strong sequentiality at the root.
4. `DCtx.track_cut` and `Separated.plug`: cut tracking is closed under arbitrary capturing contexts `DCtx`. Exact context equality handles binders; tracking antichains handles proper free subterms and disjointness across branches.
5. `subject_expansion_strong`: freshness against the **entire** contextual contractum `C.plug u` preserves both `Correct` and `StronglySequential` in `C.plug (.app (.lam ℓ t) ss)`.
6. `HasType.of_shift`, `Refines.unshift`, `refinement_substitution_decomposition`, and `refinement_substitution_inverse`: decompose a typed refinement of `LTerm.substAt 0 s t`, choose a fresh label $\ell$, and establish strong sequentiality of $(\lambda^\ell b)\vec{s}$ together with `u = b.subst 0 ss`.
7. `backwards_simulation_in_context`, `backwards_simulation` (using `LTerm.betaStep_iff_beta` proved in `Thesis/Chapter1PrelimAppendix.lean`), and `backwards_multisimulation`: use a context-parametric IH (`StronglySequential (C.plug u)`), processing sibling arguments sequentially so each recursive call chooses fresh labels against the *entire current term* (including previously reconstructed siblings). This eliminates cross-sibling label collisions directly without any implicit renaming convention, producing actual `CRed` derivations over `CTerm` under the original type-directed `DStep` (without relying on unfinished forward subject reduction).
8. `hnf_has_strong_refinement` and `head_normalizing_has_strong_refinement`: construct the empty-argument strongly sequential HNF refinement (closing `hnf_has_refinement` in `Thesis/Chapter4Simulation.lean`) and iterate backwards reconstruction to close **$(3 \implies 2)$** of `has_hnf_iff_refinable`.

The corresponding LaTeX write-up of Controlled Subject Expansion and the contextual backwards-simulation proof is available as a patch in [`08-15-has-hnf-has-refinement.tex.diff`](08-15-has-hnf-has-refinement.tex.diff).

### 3c. Separate cosmetic issues in the original LaTeX proofs

- `../document/08-14-hnf-has-refinement.tex`, line 84: states that when $x_1 = y$ and $x_1 \neq x_i$ ($i > 1$), $\ell$ is "the external label of $y$"; in fact $\ell$ decorates $\lambda^\ell x_1$ and should simply be chosen fresh in both subcases (as line 99 itself says).
- `../document/08-14-hnf-has-refinement.tex`, line 104: writes the premise context in subcase (b) as $\{y : \tau_1\}$, whereas when $y = x_i$ for some $i > 1$ the IH gives $\Gamma = \emptyset$. In both cases $x_1 \notin \dom(\Gamma)$, so $\Gamma \vdash \lambda^\ell x_1.\, s' : [] \xrightarrow{\ell} \tau$ holds uniformly.
- `../document/08-15-has-hnf-has-refinement.tex`, line 17: typo $s_1 \dots s_n$ for $s_1 \dots s_m$.
- `../document/08-15-has-hnf-has-refinement.tex`, line 407: cites `\rprop{simulation}` where `\rprop{reverse_simulation}` is actually being applied.
