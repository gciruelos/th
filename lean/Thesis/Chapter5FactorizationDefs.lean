/-
# Chapter 5: Factorization of derivations — Definitions

Garbage (`IsGarbage`), garbage-freeness (`GarbageFree`), coarse steps (`Coarse`), sieving
(`sieveAux`, `sieve`), creation in the pure λ-calculus (`LCreates`), and quotient target maps
(`targetQ`, `simTgtQ`).
-/
import Thesis.Chapter4Simulation

namespace Thesis

open LTerm ResidualSystem

/-! ## 5.1 Garbage -/

/-- `σ` is `t'`-garbage: `σ/t' = ε`. -/
def IsGarbage (t' : CTerm) (σ : List Pos) : Prop := simDeriv t' σ = []

/-- `σ` is `t'`-*garbage-free*: for every `ρ ⊑ σ`, if `σ/ρ` is `(t'/ρ)`-garbage then
`σ/ρ = ε`. -/
def GarbageFree (t : LTerm) (t' : CTerm) (σ : List Pos) : Prop :=
  ∀ ρ, lambdaRS.Valid t ρ → lambdaRS.Prefix t ρ σ →
    IsGarbage (simTgtDeriv t' ρ) (lambdaRS.proj t σ ρ) → lambdaRS.proj t σ ρ = []

/-! ## 5.2 Sieving -/

/-- A step `R` (at position `p`) is *coarse* for `(σ, t')`: `R ⊑ σ` and `R/t' ≠ ∅`. -/
def Coarse (t : LTerm) (t' : CTerm) (σ : List Pos) (p : Pos) : Prop :=
  lambdaRS.isStep t p ∧ lambdaRS.Prefix t [p] σ ∧ (simRes t'.1 p).Nonempty

/-- Sieving, with explicit fuel. -/
def sieveAux : ℕ → LTerm → CTerm → List Pos → List Pos
  | 0, _, _, _ => []
  | fuel + 1, t, t', σ =>
    match (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧ (simRes t'.1 p).Nonempty))
    with
    | none => []
    | some p => p :: sieveAux fuel (contractAt t p) (simTgt t' p) (lambdaRS.proj t σ [p])

/-- **Sieve** `σ ⇂ t'`: if there are no coarse steps it is `ε`; otherwise, with `R₀` the leftmost
coarse step, `σ ⇂ t' = R₀ ((σ/R₀) ⇂ (t'/R₀))`. Recursion is well founded on `|σ/t'|`, which is
used as fuel (`sieving_is_well_defined`). -/
def sieve (t : LTerm) (t' : CTerm) (σ : List Pos) : List Pos :=
  sieveAux (simDeriv t' σ).length t t' σ

/-- The step at `p` creates the step at `q` (λ-calculus). -/
def LCreates (t : LTerm) (p q : Pos) : Prop :=
  lambdaRS.isStep t p ∧ lambdaRS.isStep (contractAt t p) q ∧
    ∀ a, lambdaRS.isStep t a → q ∉ lambdaRS.res t p a

/-! ## 5.5 Quotient target maps -/

section Factorization

variable {t : LTerm} {t' : CTerm} (hr : Refines t t'.1)

/-- The target, on permutation-equivalence classes. -/
noncomputable def targetQ : DSpaceLam t → LTerm :=
  Quotient.lift (fun σ : LDeriv t => lambdaRS.tgt t σ.1) fun σ τ h =>
    tgt_eq_of_permEq lambda_orthogonal σ.2 τ.2 h

/-- `t'/[σ]`, on permutation-equivalence classes. -/
def simTgtQ : DSpaceLam t → CTerm :=
  Quotient.lift (fun σ : LDeriv t => simTgtDeriv t' σ.1) fun σ τ h =>
    (compatibility hr σ.2 τ.2 h).1

end Factorization

end Thesis
