/-
# Background results assumed by the thesis

This module records the external result the thesis cites without proof: orthogonality of
β-reduction (Melliès).  It is now proved: finite developments by de Vrijer's measure and
semantic orthogonality by Lévy's cube lemma, both on marked terms (`Chapter0Marked.lean`,
`Chapter0Bridge.lean`, following Huet's Coq development and Stark's Isabelle/AFP entry
`ResiduatedTransitionSystem`).
-/
import Thesis.Chapter1PrelimDefs
import Thesis.Chapter0Lambda
import Thesis.Chapter0Bridge

namespace Thesis.Background

open Thesis LTerm

/-! ## Orthogonality of β-reduction, split by axiom

The thesis cites Melliès for orthogonality of the λ-calculus in
`document/02-preliminaries.tex` (the paragraph beginning "The λ-calculus is an
example of an orthogonal axiomatic rewrite system"); it supplies no proof.
`lambdaRS.Orthogonal` packages five obligations, stated separately below so they can be
discharged independently. -/

/-- Residuals of a redex after contracting a coinitial redex are redexes of the target. -/
theorem lambda_res_isStep :
    ∀ t a b, lambdaRS.isStep t a → lambdaRS.isStep t b →
      ∀ c ∈ lambdaRS.res t b a, lambdaRS.isStep (lambdaRS.contract t b) c :=
  fun t a b ha hb => LTerm.residuals_isRedexAt t b a hb ha

/-- **Autoerasure**: `R / R = ∅`. -/
theorem lambda_autoerasure :
    ∀ t a, lambdaRS.isStep t a → lambdaRS.res t a a = ∅ := by
  intro t a _
  simp [residuals]

/-- **Finite Developments**: no infinite development of a finite set of coinitial redexes.

Source: Melliès thesis, Axiome FD (§2.2, p. 17) and Théorème 3.2 (FD+, §3.4). The thesis proves
FD abstractly from axioms A, B, C, fd-1..fd-4 (§3.3) over a nesting relation `<` and a
"grip" relation `<<`, using a multiset-of-heights measure (Lemmes 3.10, 3.15, Cor. 3.16). For λ
it only sketches the check (§3.6.1: fd-2 left to the reader), so the λ-specific
verification is not in the thesis. -/
theorem lambda_finite_developments :
    ∀ t (M : Finset Pos), (∀ a ∈ M, lambdaRS.isStep t a) →
      ¬ ∃ f : ℕ → Pos, ∀ n,
        lambdaRS.IsDevelopment t M (List.ofFn fun i : Fin n => f i) :=
  fun t M hM => Bridge.finite_developments t M hM

/-- **Semantic Orthogonality** (Melliès thesis, Axiome PERM, §2.3, p. 17ff; the thesis
does not prove it for λ and defers to the literature, e.g. Huet–Lévy for first-order systems
and Ch. 7 for CRS): the residual square closes up to complete
developments with equal targets and equal residuals of every third step. -/
theorem lambda_semantic_orthogonality :
    ∀ t a b, lambdaRS.isStep t a → lambdaRS.isStep t b →
      ∃ σ τ, lambdaRS.IsCompleteDevelopment (lambdaRS.contract t b) (lambdaRS.res t b a) σ ∧
        lambdaRS.IsCompleteDevelopment (lambdaRS.contract t a) (lambdaRS.res t a b) τ ∧
        lambdaRS.tgt (lambdaRS.contract t b) σ = lambdaRS.tgt (lambdaRS.contract t a) τ ∧
        ∀ c, lambdaRS.isStep t c →
          lambdaRS.resSetDeriv t {c} (a :: τ) = lambdaRS.resSetDeriv t {c} (b :: σ) :=
  fun t a b ha hb => Bridge.semantic_orthogonality t a b ha hb

/-- The chosen canonical development `dev` is a complete development. -/
theorem lambda_dev_complete :
    ∀ t (M : Finset Pos), (∀ a ∈ M, lambdaRS.isStep t a) →
      lambdaRS.IsCompleteDevelopment t M (lambdaRS.dev t M) :=
  fun t M hM => LTerm.dev_complete_aux t M hM

/-- Orthogonality of beta reduction with the positional residuals and canonical
developments used here, assembled from the five obligations above. -/
theorem lambda_orthogonal : lambdaRS.Orthogonal where
  res_isStep := lambda_res_isStep
  autoerasure := lambda_autoerasure
  finite_developments := lambda_finite_developments
  semantic_orthogonality := lambda_semantic_orthogonality
  dev_complete := lambda_dev_complete

end Thesis.Background
