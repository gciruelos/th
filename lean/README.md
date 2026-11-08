# Lean 4 Formalization of the Thesis

## Overview

- `../document/` holds the LaTeX source of Gonzalo Ciruelos' thesis (*A confluent non-idempotent intersection type system*): the distributive calculus $`\lambda^{\mathtt{\#}}`$, its residual theory, simulation of the pure $\lambda$-calculus, and the garbage / garbage-free factorization of derivation spaces via a Grothendieck construction. Full proofs are in the appendix files `../document/08-*.tex`.
- This directory (`lean/`) holds a Lean 4 + Mathlib formalization of the whole thesis. Every theorem is proved, with no `sorry`; the main results depend only on `propext`, `Classical.choice` and `Quot.sound`. The background result the thesis cites without proof (orthogonality of β-reduction) is proved too. Gaps found in the TeX proofs are documented in [`tex-corrections/`](tex-corrections/), each with a note and a TeX patch.

## Toolchain & building

- `elan` is installed in `~/.elan` (if not on `PATH`, run `export PATH="$HOME/.elan/bin:$PATH"`).
- Toolchain: `leanprover/lean4:v4.36.0-rc2`, with Mathlib at `v4.36.0-rc2` (cached in `.lake/`).
- Build from this directory with:
  ```bash
  lake build
  ```
  To check an individual module, run `lake env lean Thesis/Chapter1Prelim.lean`.
- `lakefile.toml` disables `weak.linter.mathlibStandardSet` to avoid Mathlib header/copyright linter noise.

## Module organization

In the compiled PDF the introduction is unnumbered front matter, so *Preliminaries* is Chapter 1. Each chapter `X` (`1..5`) is split into three files `Thesis/ChapterXName{Defs,Appendix,}.lean` forming an acyclic import chain `Defs → Appendix → Main`.
[`Chapter0.lean`](Thesis/Chapter0.lean), [`Chapter0Lambda.lean`](Thesis/Chapter0Lambda.lean), [`Chapter0Marked.lean`](Thesis/Chapter0Marked.lean) and [`Chapter0Bridge.lean`](Thesis/Chapter0Bridge.lean) prove the cited background result (orthogonality of β-reduction)
and support lemmas for pure λ-calculus residuals, using the definitions introduced in Chapter 1:

1. `ChapterXNameDefs.lean`: definitions directly appearing in the main text of Chapter `X` in `../document/`.
2. `ChapterXNameAppendix.lean`: auxiliary definitions and lemmas used in proofs (including results from `../document/08-*.tex` and proof-only helpers) that are not directly named in the main `.tex` chapter.
3. `ChapterXName.lean`: main-text lemmas, propositions, theorems, corollaries, and instances directly appearing in Chapter `X`, together with their proofs.

| Files (`Thesis/`) | Thesis chapter | Contents |
|---|---|---|
| `Chapter0{,Lambda,Marked,Bridge}.lean` | External background | Orthogonality of the λ-calculus (cited from Melliès in `02-preliminaries.tex`), proved via marked terms: substitution algebra, Huet's commutation theorem, Lévy's cube lemma, de Vrijer's finite developments, and the bridge to positional residuals |
| `Chapter1Prelim{Defs,Appendix,}.lean` | Ch. 1 (`02-preliminaries.tex`, plus lax 2-functors from Ch. 5) | `LaxFunctor` and the Grothendieck construction `Groth` (proved to be a poset); generic `ResidualSystem` (Melliès' axiomatic rewrite systems, canonical developments, projection `proj` via `projM`, `Prefix`, `PermEq`, `join`, `Orthogonal`); derivation spaces `DSpace` as `Antisymmetrization` with `SemilatticeSup` and `OrderBot`; pure $\lambda$-calculus `LTerm` (de Bruijn), positions, `residuals`, `dev`, `lambdaRS`, HNFs, `betaStep_iff_beta` |
| `Chapter2DistLambdaCalc{Defs,Appendix,}.lean` | Ch. 2 (`03-distributive.tex`, `08-01`..`08-07`) | $`\lambda^{\mathtt{\#}}`$: `Ty`, `DTerm` (nested via `List`, custom induction `DTerm.ind`), `Ctx = ℕ → Multiset Ty`, mutual `HasType`/`HasTypeMulti`, `Correct`, `CTerm`, type-directed `DTerm.subst`, partition-based `PSubst`/`PSubstMulti`, `unique_typing`, `PSubst.eq_subst`, `linearity`, typing `subject_expansion`, `DCtx`, `DStep`, `termination`, `strong_permutation`, `confluence` |
| `Chapter3ResidualTheory{Defs,Appendix,}.lean` | Ch. 3 (`04-residual-theory.tex`, `08-08`..`08-10`) | `hasRedex`, `contract`, `distRS` (over `CTerm`), `names`, `Belongs`, `prefix_iff_subset`, `CreationCase`/`creation`, `basic_stability`, `full_stability`, `meet`, `DistribLattice` on `DSpace distRS t`, and the ring-of-sets embedding `namesHom` |
| `Chapter4Simulation{Defs,Appendix,}.lean` | Ch. 4 (`05-simulation.tex`, `08-11`..`08-17`) | `Refines`, `simulation`, `reverse_simulation`, HNFs for $`\lambda^{\mathtt{\#}}`$, free cuts & `StronglySequential`, controlled subject expansion (`subject_expansion_strong`), contextual backwards simulation, `hnf_has_refinement`, `has_hnf_iff_refinable`, simulation residuals `simRes`/`simDeriv`/`simTgtDeriv`, cube lemmas, `compatibility`, `algebraicSimulation : SupBotHom` |
| `Chapter5Factorization{Defs,Appendix,}.lean` | Ch. 5 (`06-factorization.tex`, `08-18`..`08-21`) | `IsGarbage`, `GarbageFree`, `Coarse`, `sieve` (with fuel `|σ/t'|`), characterizations, `simple_factorization`, garbage-free lattice `GF`, garbage semilattice `GSpace`, lax 2-functor `laxG`, Grothendieck isomorphism `factorization : DSpaceLam t ≃o (laxG hr).Groth` |
| `Thesis.lean` | — | Root umbrella module importing Chapter 0 and all 15 chapter files |

## Key representation choices

- **de Bruijn indices** for both $\lambda$ (`LTerm`) and $`\lambda^{\mathtt{\#}}`$ (`DTerm`).
- **Steps** are represented by an object plus an address: a position (`Pos = List ℕ`) for $\lambda$, and a $\lambda$-label (`Label = ℕ`) for $`\lambda^{\mathtt{\#}}`$. Derivations are lists of addresses with a separate `Valid` predicate.
- **Projection** is defined structurally through projection after a multistep (`projM`) using a canonical complete development (`dev`): innermost-first for $\lambda$, and sorted label list for $`\lambda^{\mathtt{\#}}`$.
- **Multisets inside types** (`Ty.arrow`) use `List Ty` because Lean 4 cannot nest an inductive type through `Multiset` (a quotient). The `→I` rule (`HasType.lam`) produces the canonical listing `M.toList` and `→E` (`HasType.app`) matches argument types up to permutation, preserving syntactic uniqueness of types (`hasType_unique`).
- **Substitution in $`\lambda^{\mathtt{\#}}`$** is formalized both as the thesis' *type-directed* ("alternative") function `DTerm.subst` (classical/noncomputable, used in `DStep`) and as the raw *partition-based* relation `PSubst` (used for subject expansion and proved equal to `DTerm.subst` under sequentiality in `PSubst.eq_subst`).
- **`ResidualSystem` instances** (`lambdaRS`, `distRS`) are `abbrev` so typeclass search unfolds `Obj`, and orthogonality is carried as a `Fact` instance.

## Proof status overview

Every theorem in `Thesis/` is proved. `#print axioms` on the main results (for example
`factorization`, `Background.lambda_orthogonal`, `generalized_cube_lemma`,
`lambda_dspace_not_lattice`) reports only `propext`, `Classical.choice` and `Quot.sound`.

- **Chapter 0 (background):** orthogonality of β-reduction, which the thesis cites from
  Melliès (`Background.lambda_orthogonal`). Finite developments use de Vrijer's height measure
  and semantic orthogonality uses Lévy's cube lemma, both on marked terms
  ([`Chapter0Marked.lean`](Thesis/Chapter0Marked.lean)), connected to the positional residuals
  by [`Chapter0Bridge.lean`](Thesis/Chapter0Bridge.lean) (`resid_mark`). The development follows
  Huet's Coq formalization and Stark's Isabelle/AFP entry `ResiduatedTransitionSystem`.
- **Chapter 1:** the Grothendieck poset, the generic development and projection theory, the
  derivation-space semilattice, `LTerm.betaStep_iff_beta`, and Laneve's counterexample
  `lambda_dspace_not_lattice` (from `01-introduction.tex`).
- **Chapter 2:** unique typing, substitution, subject reduction with correctness, determinism
  by label, termination, strong permutation, and confluence, following `03-03-the-calculus.tex`
  and appendices `08-03`, `08-05`, `08-06`, `08-07`.
- **Chapter 3:** orthogonality of λ^#, finite developments, names, prefixes, creation,
  basic and full stability, meets, the distributive lattice structure, and the ring-of-sets
  embedding `namesHom`, following `04-01`..`04-04` and appendices `08-08`, `08-10`.
- **Chapter 4:** simulation and reverse simulation, controlled subject expansion and
  contextual backwards simulation, `has_hnf_iff_refinable`, the basic and generalized cube
  lemmas, compatibility, and algebraic simulation. The basic cube lemma strengthens the
  constructive simulation trace (`cube_trace`); the generalized cube lemma goes through name
  sets (`single_gen`, `gen_names`).
- **Chapter 5:** garbage and its characterizations, the sieve (`sieve_garbageFree`,
  `sieve_trailing_garbage`, `sieve_least`), `simple_factorization`, the lattice `GF`, the lax
  functor `laxG`, `groth_isLUB`, and the factorization isomorphism `factorization`. The
  leftmost-coarse-step lemma is proved with a stronger invariant, `leftmost_least`: the chosen
  step precedes every other coarse step in the pre-order on positions.

### TeX corrections

| Note | Patch | Issue |
|---|---|---|
| [`08-15-has-hnf-has-refinement.md`](tex-corrections/08-15-has-hnf-has-refinement.md) | [`.tex.diff`](tex-corrections/08-15-has-hnf-has-refinement.tex.diff) | Subject expansion needs strong sequentiality and partition-based substitution; backwards simulation made precise |
| [`05-04-simulation-residuals.md`](tex-corrections/05-04-simulation-residuals.md) | [`.tex.diff`](tex-corrections/05-04-simulation-residuals.tex.diff) | Generalized cube lemma: circular step and a single-step result used for sets |
| [`08-19-garbage-some-properties.md`](tex-corrections/08-19-garbage-some-properties.md) | [`.tex.diff`](tex-corrections/08-19-garbage-some-properties.tex.diff) | Leftmost coarse step: the induction only shows the residual is coarse, not leftmost |

An earlier Lean statement of Chapter 2's `subst_subst` was false: it allowed missing
lookups and inserted an extra shift incompatible with `DTerm.subst`'s binder convention.
The proved statement makes lookup definedness and argument type preservation explicit,
and uses unshifted second-substitution arguments. `DTerm.subst_commute_counterexamples`
checks both defects; `HasType.subst_ty` discharges type preservation from typing and
definedness. The typing rules, correctness predicate, and reduction relation are unchanged.

## Per-file statistics

<!-- BEGIN GENERATED FILE STATS -->

| Prefix | File | Lines | Statements | Defs | Types | `sorry`s | Max statement DAG (statement) | Max proof DAG (proof) | Theorems with `sorry` |
|:---|:---|---:|---:|---:|---:|---:|:---|:---|:---|
| **Chapter0** | [.lean](Thesis/Chapter0.lean) | 79 | 6 | 0 | 0 | 0 | 98 (<code>Background.lambda_semantic_orthogonality</code>) | 186 (<code>Background.lambda_autoerasure</code>) | — |
|  | [Lambda.lean](Thesis/Chapter0Lambda.lean) | 464 | 32 | 0 | 1 | 0 | 195 (<code>LTerm.app_phases</code>) | 4,729 (<code>LTerm.Ctx.residuals_in</code>) | — |
|  | [Marked.lean](Thesis/Chapter0Marked.lean) | 783 | 49 | 9 | 1 | 0 | 328 (<code>Marked.MT.resid.induct_unfolding</code>) | 16,888 (<code>Marked.MT.Cube_aux</code>) | — |
|  | [Bridge.lean](Thesis/Chapter0Bridge.lean) | 761 | 41 | 3 | 0 | 0 | 163 (<code>Bridge.dev_step_decreases._proof_1_13</code>) | 2,863 (<code>Bridge.resSet_root</code>) | — |
| **Chapter1Prelim** | [Defs.lean](Thesis/Chapter1PrelimDefs.lean) | 344 | 2 | 29 | 7 | 0 | 292 (<code>LaxFunctor.mk.injEq</code>) | 972 (<code>LaxFunctor.mk.injEq</code>) | — |
|  | [.lean](Thesis/Chapter1Prelim.lean) | 340 | 33 | 4 | 0 | 0 | 189 (<code>LaxFunctor.instPartialOrderGroth._proof_2</code>) | 942 (<code>LaxFunctor.instPartialOrderGroth._proof_4</code>) | — |
|  | [Appendix.lean](Thesis/Chapter1PrelimAppendix.lean) | 1,239 | 78 | 7 | 1 | 0 | 196 (<code>ResidualSystem.dev_bounded._proof_1_7</code>) | 4,209 (<code>ResidualSystem.completeDevelopment_unique</code>) | — |
| **Chapter2DistLambdaCalc** | [Defs.lean](Thesis/Chapter2DistLambdaCalcDefs.lean) | 313 | 8 | 24 | 11 | 0 | 193 (<code>DTerm.subst._unary.eq_def</code>) | 1,234 (<code>DTerm.subst._unary.eq_def</code>) | — |
|  | [.lean](Thesis/Chapter2DistLambdaCalc.lean) | 140 | 11 | 0 | 0 | 0 | 89 (<code>subst_hasType</code>) | 780 (<code>termination._proof_1_1</code>) | — |
|  | [Appendix.lean](Thesis/Chapter2DistLambdaCalcAppendix.lean) | 1,876 | 106 | 6 | 1 | 0 | 115 (<code>PSubst.inverse</code>) | 8,575 (<code>PSubst.inverse</code>) | — |
| **Chapter3ResidualTheory** | [Defs.lean](Thesis/Chapter3ResidualTheoryDefs.lean) | 255 | 7 | 9 | 1 | 0 | 159 (<code>DTerm.hasRedex.match_1._arg_pusher</code>) | 2,671 (<code>DStep.eq_contract</code>) | — |
|  | [.lean](Thesis/Chapter3ResidualTheory.lean) | 234 | 28 | 4 | 0 | 0 | 125 (<code>distRS.full_stability</code>) | 649 (<code>distRS.full_stability</code>) | — |
|  | [Appendix.lean](Thesis/Chapter3ResidualTheoryAppendix.lean) | 912 | 52 | 1 | 1 | 0 | 181 (<code>distRS.meetAux_names._proof_1_6</code>) | 5,658 (<code>DStep.creation_case</code>) | — |
| **Chapter4Simulation** | [Defs.lean](Thesis/Chapter4SimulationDefs.lean) | 72 | 0 | 4 | 5 | 0 | 36 (<code>Refines.brecOn</code>) | 150 (<code>Refines.brecOn</code>) | — |
|  | [.lean](Thesis/Chapter4Simulation.lean) | 570 | 26 | 3 | 0 | 0 | 113 (<code>algebraicSimulation_mono</code>) | 2,801 (<code>single_gen</code>) | — |
|  | [Appendix.lean](Thesis/Chapter4SimulationAppendix.lean) | 2,376 | 134 | 13 | 4 | 0 | 155 (<code>simRes.match_1.eq_6</code>) | 9,513 (<code>cube_trace</code>) | — |
| **Chapter5Factorization** | [Defs.lean](Thesis/Chapter5FactorizationDefs.lean) | 69 | 0 | 8 | 0 | 0 | 86 (<code>simTgtQ._proof_1</code>) | 114 (<code>simTgtQ._proof_1</code>) | — |
|  | [.lean](Thesis/Chapter5Factorization.lean) | 1,031 | 55 | 6 | 1 | 0 | 448 (<code>factorization</code>) | 4,026 (<code>groth_isLUB</code>) | — |
|  | [Appendix.lean](Thesis/Chapter5FactorizationAppendix.lean) | 1,259 | 64 | 2 | 0 | 0 | 128 (<code>order_preserved</code>) | 3,672 (<code>leftmost_least</code>) | — |
| **Thesis** | [.lean](Thesis.lean) | 50 | 0 | 0 | 0 | 0 | — | — | — |
| **Total / maximum** | | **13,167** | **732** | **132** | **34** | **0** | **448** (<code>factorization</code>) | **16,888** (<code>Marked.MT.Cube_aux</code>) | — |

<!-- END GENERATED FILE STATS -->

The shared **Prefix** is relative to `Thesis/`; append **File** to recover the filename.
Each chapter is ordered **Defs → .lean → Appendix**. The root `Thesis.lean` appears last.
The table excludes dependencies and the statistics tools.

- **Lines** includes blank lines and comments.
- **Statements** combines explicit `theorem`, `lemma`, and `instance` commands, including
  private declarations.
- **Defs** counts `def`, `abbrev`, and `opaque`; **Types** counts `inductive`, `structure`,
  and `class`. These source counts
  exclude generated declarations, constructors, fields, and local hypotheses.
- **`sorry`s** counts explicit, unquoted tokens, excluding nested block comments, line
  comments, strings, and quoted identifiers. Zero does not imply freedom from upstream
  `sorryAx` dependencies.
- **Max statement DAG (statement)** measures the largest elaborated theorem type, including
  its parameters and hypotheses, and names that theorem. **Max proof DAG (proof)** measures
  the largest theorem body and names that proof. Both include compiler-generated theorem
  declarations, so even a file with no explicit statements can have a nonzero maximum. Names
  omit the common `Thesis.` namespace and private-name mangling, preserving generated suffixes.
- **Theorems with `sorry`** enumerates all elaborated theorem declarations in the file that
  directly contain `sorryAx` in their proof or statement, omitting the `Thesis.` namespace.
  `—` indicates that no theorems in the module use `sorry`.

Both DAG measurements first maximize structural sharing with Lean's
`ShareCommon.shareCommon'`, then count unique `Expr` nodes with `Expr.numObjs`. Binder
types count; referenced declarations are not unfolded. Definitions and instances are not
measured unless Lean generates separate theorem declarations for them. `—` means the
module declares no theorems. The last row sums source counts and takes the maximum of
each DAG column (naming those declarations). Sizes depend on the pinned Lean and Mathlib versions and do not
indicate proof completeness.

To regenerate from `lean/` (Python 3.8+ and the configured Lean toolchain are required):

```bash
export PATH="$HOME/.elan/bin:$PATH"
python3 scripts/update_stats.py
```

The command builds the current modules, measures their compiled theorem bodies using
[`scripts/proof_stats.lean`](scripts/proof_stats.lean), and replaces only the marked table
in this README. To verify the table without modifying it:

```bash
python3 scripts/update_stats.py --check
```
