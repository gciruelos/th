/-
# Chapter 4: Simulation of the λ-calculus — Definitions

Refinements (`Refines`), head normal forms of λ^dist (`IsHeadAppD`, `IsHNFD`, `IsEmptyHeadApp`,
`IsEmptyHNF`), and simulation residuals (`simRes`, `simTgt`, `simDeriv`, `simTgtDeriv`).
-/
import Thesis.Chapter3ResidualTheory

namespace Thesis

open LTerm DTerm

/-! ## 4.1 Refinements -/

/-- `t ⋉ t'`: the λ-term `t` is *refined* by the distributive term `t'`. -/
inductive Refines : LTerm → DTerm → Prop
  | var (n : ℕ) (τ : Ty) : Refines (.var n) (.var n τ)
  | lam {t : LTerm} {t' : DTerm} (ℓ : Label) : Refines t t' → Refines (.lam t) (.lam ℓ t')
  | app {t s : LTerm} {t' : DTerm} {ss : List DTerm} :
      Refines t t' → (∀ s' ∈ ss, Refines s s') → Refines (.app t s) (.app t' ss)

/-! ## 4.3 Head normal forms -/

/-- `y^τ s̄₁ … s̄ₘ`. -/
inductive IsHeadAppD : DTerm → Prop
  | var (n : ℕ) (τ : Ty) : IsHeadAppD (.var n τ)
  | app {t : DTerm} (ss : List DTerm) : IsHeadAppD t → IsHeadAppD (.app t ss)

/-- Head normal forms of λ^dist: `λ^ℓ₁x₁…λ^ℓₙxₙ. y^τ s̄₁ … s̄ₘ`. -/
inductive IsHNFD : DTerm → Prop
  | head {t : DTerm} : IsHeadAppD t → IsHNFD t
  | lam {t : DTerm} (ℓ : Label) : IsHNFD t → IsHNFD (.lam ℓ t)

/-- `y^τ [] … []`. -/
inductive IsEmptyHeadApp : DTerm → Prop
  | var (n : ℕ) (τ : Ty) : IsEmptyHeadApp (.var n τ)
  | app {t : DTerm} : IsEmptyHeadApp t → IsEmptyHeadApp (.app t [])

/-- `λ^ℓ₁x₁…λ^ℓₙxₙ. y^τ [] … []`. -/
inductive IsEmptyHNF : DTerm → Prop
  | head {t : DTerm} : IsEmptyHeadApp t → IsEmptyHNF t
  | lam {t : DTerm} (ℓ : Label) : IsEmptyHNF t → IsEmptyHNF (.lam ℓ t)

/-! ## 4.4 Simulation residuals -/

/-- `R/t'`: the *simulation residuals* of the β-step at position `p` after `t'` — the names of
the copies of that redex in `t'` (one per argument a sub-term is distributed to). -/
def simRes : DTerm → Pos → Finset Label
  | .app (.lam ℓ _) _, [] => {ℓ}
  | _, [] => ∅
  | .lam _ u, 0 :: p => simRes u p
  | .app u _, 0 :: p => simRes u p
  | .app _ ss, 1 :: p => (ss.map (simRes · p)).foldr (· ∪ ·) ∅
  | _, _ => ∅

/-- `t'/R`: the simulation residual of `t'` after the β-step at `p`, i.e. the common target of
the complete developments of `R/t'`. -/
def simTgt (t' : CTerm) (p : Pos) : CTerm :=
  distRS.tgt t' (distRS.dev t' (simRes t'.1 p))

/-- `σ/t'`: simulation residual of a λ-derivation, by `ε/t' = ε` and
`(Rσ)/t' = (R/t')(σ/(t'/R))`. -/
def simDeriv : CTerm → List Pos → List Label
  | _, [] => []
  | t', p :: σ => distRS.dev t' (simRes t'.1 p) ++ simDeriv (simTgt t' p) σ

/-- `t'/σ`: simulation residual of `t'` after a λ-derivation. -/
def simTgtDeriv : CTerm → List Pos → CTerm
  | t', [] => t'
  | t', p :: σ => simTgtDeriv (simTgt t' p) σ

end Thesis
