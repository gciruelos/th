/-
# Formalization of "A confluent non-idempotent intersection type system" (G. Ciruelos)

Each thesis chapter `X` is split into three modules (`ChapterXName{Defs,Appendix,}.lean`):

* `ChapterXNameDefs`      — definitions directly appearing in Chapter `X` of the thesis.
* `ChapterXNameAppendix`  — auxiliary definitions and lemmas used in proofs (including results from
                            `document/08-*.tex` and proof-only helpers) not directly named in the
                            main text of Chapter `X`.
* `ChapterXName`          — main-text lemmas, propositions, theorems, corollaries, and instances of
                            Chapter `X`, together with their proofs.

Chapters:
* `Chapter1Prelim{Defs,Appendix,}`          — order theory, lax 2-functors, the Grothendieck
                                              construction; axiomatic rewrite systems (Melliès) and
                                              derivation spaces; the pure λ-calculus (positions,
                                              residuals, developments).
* `Chapter2DistLambdaCalc{Defs,Appendix,}`  — λ^dist: types, terms, typing, correctness,
                                              substitution, reduction, termination, strong
                                              permutation, confluence.
* `Chapter3ResidualTheory{Defs,Appendix,}`  — residuals and names, belonging, prefixes as subsets,
                                              creation/stability, meets; `𝔻^dist(t)` is a
                                              distributive lattice representable as a ring of sets.
* `Chapter4Simulation{Defs,Appendix,}`      — refinements, (reverse) simulation, head normal forms,
                                              controlled subject expansion and backwards simulation,
                                              simulation residuals, cube lemmas, algebraic
                                              simulation.
* `Chapter5Factorization{Defs,Appendix,}`   — garbage, garbage-free derivations, sieving, and the
                                              factorization `𝔻_λ(t) ≅ ∫_𝔽 𝔾`.

Theorems whose proof is still `sorry` are stated faithfully but not yet proved.
-/
import Thesis.Chapter0
import Thesis.Chapter1PrelimDefs
import Thesis.Chapter1PrelimAppendix
import Thesis.Chapter1Prelim
import Thesis.Chapter2DistLambdaCalcDefs
import Thesis.Chapter2DistLambdaCalcAppendix
import Thesis.Chapter2DistLambdaCalc
import Thesis.Chapter3ResidualTheoryDefs
import Thesis.Chapter3ResidualTheoryAppendix
import Thesis.Chapter3ResidualTheory
import Thesis.Chapter4SimulationDefs
import Thesis.Chapter4SimulationAppendix
import Thesis.Chapter4Simulation
import Thesis.Chapter5FactorizationDefs
import Thesis.Chapter5FactorizationAppendix
import Thesis.Chapter0Marked
import Thesis.Chapter0Bridge
import Thesis.Chapter5Factorization
