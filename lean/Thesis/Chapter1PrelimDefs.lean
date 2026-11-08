/-
# Chapter 1: Preliminaries — Definitions

## Order theory (§"Order theory"; Chapter 5, Grothendieck construction)

Mathlib already provides most of the order-theoretic vocabulary used in the thesis:

* upper semilattice with bottom   ↦ `SemilatticeSup α` + `OrderBot α`
* morphism of upper semilattices  ↦ `SupBotHom α β` (preserves `⊔` and `⊥`, hence monotone)
* (distributive) lattice          ↦ `Lattice α` / `DistribLattice α`
* morphism of lattices            ↦ `LatticeHom α β`

What is specific to the thesis is the notion of *lax 2-functor* from a poset into `Poset`
and the *Grothendieck construction* for posets (Chapter 5), together with axiomatic rewrite
systems (Melliès) and the pure λ-calculus.
-/
import Mathlib

namespace Thesis

universe u v

/-- A *lax 2-functor* `B : A → Poset` from a poset `A` (seen as a category) into the
2-category of posets (Chapter 5, Definition "Lax 2-functor", specialised to the case used in
the Grothendieck construction):

* for every `a ≤ b` a monotone map `B(b ↤ a) : B a → B b`;
* `B(a ↤ a) = id`;
* `B((c ↤ b) ∘ (b ↤ a)) ≤ B(c ↤ b) ∘ B(b ↤ a)` (a 2-cell). -/
structure LaxFunctor (A : Type u) [PartialOrder A] where
  /-- The poset associated to each object. -/
  obj : A → Type v
  [inst : ∀ a, PartialOrder (obj a)]
  /-- The action on morphisms `a ≤ b`. -/
  map : ∀ {a b : A}, a ≤ b → obj a → obj b
  map_mono : ∀ {a b : A} (h : a ≤ b), Monotone (map h)
  map_id : ∀ (a : A) (x : obj a), map (le_refl a) x = x
  map_comp : ∀ {a b c : A} (h₁ : a ≤ b) (h₂ : b ≤ c) (x : obj a),
    map (h₁.trans h₂) x ≤ map h₂ (map h₁ x)

attribute [instance] LaxFunctor.inst

namespace LaxFunctor

variable {A : Type u} [PartialOrder A] (B : LaxFunctor.{u, v} A)

/-- The *Grothendieck construction* `∫_A B` (Chapter 5): pairs `(a, b)` with `b ∈ B a`, ordered by
`(a, b) ≤ (a', b') ⟺ a ≤ a' ∧ B(a' ↤ a)(b) ≤ b'`. -/
def Groth : Type (max u v) := Σ a : A, B.obj a

end LaxFunctor

/-
## Axiomatic rewrite systems (Chapter 1, §"Rewriting theory")

The thesis works with Melliès' *axiomatic rewrite systems*: objects, steps, a residual
function, and the four axioms of orthogonality (Autoerasure, Finite Residuals,
Finite Developments, Semantic Orthogonality). Both the pure λ-calculus and λ^dist are instances.

## Representation

A step is determined by its source object together with an *address* inside it:
a position for the λ-calculus, a label for λ^dist. So a `ResidualSystem` provides

* `isStep t a`    — the address `a` denotes a step out of `t`;
* `contract t a`  — the target of that step;
* `res t b a`     — the (finite) set `a / b` of residuals of `a` after `b`, both coinitial at `t`
                    (the residuals are steps out of `contract t b`);
* `dev t M`       — a *canonical* complete development of the set `M` of coinitial steps.

A derivation out of `t` is a list of addresses, each a step of the term reached so far.

## Projection

The thesis (following Melliès) defines projection by
`ε/τ = ε` and `(Rσ)/τ = (R/τ)(σ/(τ/R))`, where `R/τ` abbreviates a canonical complete development.
To make this *structurally* recursive, we use the classical trick of projecting a derivation
after a *multistep* (a set of coinitial steps):

* `projM t τ M` : `τ / M`,       recursion on `τ`: `(Sτ')/M = (S/M)(τ'/(M/S))`;
* `proj t σ τ`  : `σ / τ`,       recursion on `σ`: `(Rσ')/τ = (R/τ)(σ'/(τ/{R}))`.
-/

/-- An axiomatic rewrite system with addressed steps and a chosen canonical complete development
of each finite set of coinitial steps. -/
structure ResidualSystem where
  /-- Objects (terms). -/
  Obj : Type
  /-- Addresses of steps inside an object (positions, labels, ...). -/
  Adr : Type
  [decEq : DecidableEq Adr]
  /-- `isStep t a` : `a` is the address of a step with source `t`. -/
  isStep : Obj → Adr → Prop
  /-- Target of the step `a` out of `t`. -/
  contract : Obj → Adr → Obj
  /-- `res t b a` is the set `a / b` of residuals of the step `a` after the coinitial step `b`. -/
  res : Obj → Adr → Adr → Finset Adr
  /-- A canonical complete development of a finite set of coinitial steps. -/
  dev : Obj → Finset Adr → List Adr

namespace ResidualSystem

attribute [instance] decEq

variable (R : ResidualSystem)

/-- The target of a derivation. -/
def tgt (t : R.Obj) (σ : List R.Adr) : R.Obj := σ.foldl R.contract t

/-- `σ` is a (composable) derivation out of `t`. -/
def Valid : R.Obj → List R.Adr → Prop
  | _, [] => True
  | t, a :: σ => R.isStep t a ∧ Valid (R.contract t a) σ

/-- Residuals of a set of steps after one step: `M / b`. -/
def resSet (t : R.Obj) (M : Finset R.Adr) (b : R.Adr) : Finset R.Adr :=
  M.biUnion (R.res t b)

/-- Residuals of a set of steps after a derivation: `M / τ`. -/
def resSetDeriv : R.Obj → Finset R.Adr → List R.Adr → Finset R.Adr
  | _, M, [] => M
  | t, M, b :: τ => resSetDeriv (R.contract t b) (R.resSet t M b) τ

/-- `σ` is a development of the set `M` of coinitial steps out of `t`: every step of `σ` is a
residual of some step in `M`. -/
def IsDevelopment : R.Obj → Finset R.Adr → List R.Adr → Prop
  | _, _, [] => True
  | t, M, a :: σ => R.isStep t a ∧ a ∈ M ∧ IsDevelopment (R.contract t a) (R.resSet t M a) σ

/-- A development is complete if no residual of `M` is left. -/
def IsCompleteDevelopment (t : R.Obj) (M : Finset R.Adr) (σ : List R.Adr) : Prop :=
  R.IsDevelopment t M σ ∧ R.resSetDeriv t M σ = ∅

/-- The four axioms of an *orthogonal* axiomatic rewrite system (Melliès), together with the
basic well-formedness of residuals and the specification of the canonical development `dev`. -/
structure Orthogonal : Prop where
  /-- Residuals are steps of the target. -/
  res_isStep : ∀ t a b, R.isStep t a → R.isStep t b → ∀ c ∈ R.res t b a, R.isStep (R.contract t b) c
  /-- **Autoerasure**: `R / R = ∅`. -/
  autoerasure : ∀ t a, R.isStep t a → R.res t a a = ∅
  /-- **Finite Residuals** holds by construction, since `res` is `Finset`-valued.
  **Finite Developments**: there is no infinite development of a finite set of coinitial steps. -/
  finite_developments : ∀ t (M : Finset R.Adr), (∀ a ∈ M, R.isStep t a) →
    ¬ ∃ f : ℕ → R.Adr, ∀ n, R.IsDevelopment t M (List.ofFn fun i : Fin n => f i)
  /-- **Semantic Orthogonality** (Axiome PERM). -/
  semantic_orthogonality : ∀ t a b, R.isStep t a → R.isStep t b →
    ∃ σ τ, R.IsCompleteDevelopment (R.contract t b) (R.res t b a) σ ∧
      R.IsCompleteDevelopment (R.contract t a) (R.res t a b) τ ∧
      R.tgt (R.contract t b) σ = R.tgt (R.contract t a) τ ∧
      ∀ c, R.isStep t c → R.resSetDeriv t {c} (a :: τ) = R.resSetDeriv t {c} (b :: σ)
  /-- The chosen development is a complete development. -/
  dev_complete : ∀ t (M : Finset R.Adr), (∀ a ∈ M, R.isStep t a) →
    R.IsCompleteDevelopment t M (R.dev t M)

/-- Projection of a derivation `τ` after a multistep `M` (both out of `t`): `τ / M`. -/
def projM : R.Obj → List R.Adr → Finset R.Adr → List R.Adr
  | _, [], _ => []
  | t, b :: τ, M =>
      R.dev (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M)) ++
        projM (R.contract t b) τ (R.resSet t M b)

/-- Projection of derivations: `σ / τ`, both out of `t`. -/
def proj : R.Obj → List R.Adr → List R.Adr → List R.Adr
  | _, [], _ => []
  | t, a :: σ, τ =>
      R.dev (R.tgt t τ) (R.resSetDeriv t {a} τ) ++ proj (R.contract t a) σ (R.projM t τ {a})

/-- Prefix order: `σ ⊑ τ` iff `σ / τ = ε`. -/
def Prefix (t : R.Obj) (σ τ : List R.Adr) : Prop := R.proj t σ τ = []

instance (t : R.Obj) (σ τ : List R.Adr) : Decidable (R.Prefix t σ τ) :=
  inferInstanceAs (Decidable (_ = _))

/-- Permutation equivalence: `σ ≡ τ` iff `σ ⊑ τ` and `τ ⊑ σ`. -/
def PermEq (t : R.Obj) (σ τ : List R.Adr) : Prop := R.Prefix t σ τ ∧ R.Prefix t τ σ

/-- Join of derivations: `σ ⊔ τ = σ(τ/σ)`. -/
def join (t : R.Obj) (σ τ : List R.Adr) : List R.Adr := σ ++ R.proj t τ σ

/-- Derivations out of `t`. -/
def DerivFrom (t : R.Obj) : Type := {σ : List R.Adr // R.Valid t σ}

end ResidualSystem

/-
## The pure λ-calculus (Chapter 1, §"Rewriting theory"; Chapter 4, head normal forms)

Terms use de Bruijn indices: `lam t` binds index `0` in `t`.

Steps are addressed by *positions* (sequences of `0`/`1`), exactly as in the thesis:
`pos(x) = {ε}`, `pos(t s) = 0·pos(t) ∪ 1·pos(s)`, `pos(λx.t) = 0·pos(t)`.
Residuals are defined via the thesis' notion of *descendant*.
-/

/-- Pure λ-terms, with de Bruijn indices. -/
inductive LTerm
  | var (n : ℕ)
  | lam (t : LTerm)
  | app (t s : LTerm)
  deriving DecidableEq, Repr

/-- Positions in a term. -/
abbrev Pos := List ℕ

namespace LTerm

/-- `shift d c t` adds `d` to every index `≥ c`. -/
def shift (d : ℕ) : ℕ → LTerm → LTerm
  | c, var n => if n < c then var n else var (n + d)
  | c, lam t => lam (shift d (c + 1) t)
  | c, app t s => app (shift d c t) (shift d c s)

/-- `substAt k s t = t[k := s]`, where `s` lives outside the `k` binders crossed so far.
Indices above `k` are decremented (the binder disappears). -/
def substAt : ℕ → LTerm → LTerm → LTerm
  | k, s, var n => if n < k then var n else if n = k then shift k 0 s else var (n - 1)
  | k, s, lam t => lam (substAt (k + 1) s t)
  | k, s, app t u => app (substAt k s t) (substAt k s u)

/-- The sub-term at a position, if any (`M|ₚ`). -/
def subAt : LTerm → Pos → Option LTerm
  | t, [] => some t
  | lam t, 0 :: p => subAt t p
  | app t _, 0 :: p => subAt t p
  | app _ s, 1 :: p => subAt s p
  | _, _ => none

/-- `t` is a β-redex `(λ.u) s`. -/
def isRedex : LTerm → Bool
  | app (lam _) _ => true
  | _ => false

/-- There is a β-redex at position `p`. -/
def isRedexAt (t : LTerm) (p : Pos) : Bool :=
  match subAt t p with
  | some u => isRedex u
  | none => false

/-- Contract the redex at position `p` (identity if there is none). -/
def contractAt : LTerm → Pos → LTerm
  | app (lam u) s, [] => substAt 0 s u
  | lam t, 0 :: p => lam (contractAt t p)
  | app t s, 0 :: p => app (contractAt t p) s
  | app t s, 1 :: p => app t (contractAt s p)
  | t, _ => t

/-- All redex positions, in *leftmost-outermost* order. -/
def redexes : LTerm → List Pos
  | var _ => []
  | lam t => (redexes t).map (0 :: ·)
  | app t s =>
      (if isRedex (app t s) then [[]] else []) ++ (redexes t).map (0 :: ·) ++
        (redexes s).map (1 :: ·)

/-- Positions of the free occurrences of the index `k` (shifted under binders). -/
def occs : LTerm → ℕ → List Pos
  | var n, k => if n = k then [[]] else []
  | lam t, k => (occs t (k + 1)).map (0 :: ·)
  | app t s, k => (occs t k).map (0 :: ·) ++ (occs s k).map (1 :: ·)

/-- **Residuals** (via descendants, Chapter 1): the set of residuals of the redex at `p` after
contracting the redex at `q` in `t`.

* if `p = q` the redex is erased;
* if `q` is a strict prefix of `p`, with `t|_q = (λ.u) s`:
  - `p = q·0·0·r` (inside the body): the unique descendant is `q·r`;
  - `p = q·1·r` (inside the argument): one descendant `q·o·r` per occurrence `o` of the bound
    variable in `u`;
* otherwise (disjoint, or `p` above `q`): the redex stays at `p`. -/
def residuals (t : LTerm) (q p : Pos) : Finset Pos :=
  if p = q then ∅
  else if q <+: p then
    match subAt t q, p.drop q.length with
    | some (app (lam _) _), 0 :: 0 :: r => {q ++ r}
    | some (app (lam u) _), 1 :: r => ((occs u 0).map fun o => q ++ o ++ r).toFinset
    | _, _ => ∅
  else {p}

/-- The positions of `P` below child `i`. -/
def subPos (P : Finset Pos) (i : ℕ) : Finset Pos :=
  P.filterMap (fun | j :: r => if j = i then some r else none | [] => none) (by
    rintro (_ | ⟨j, r⟩) (_ | ⟨j', r'⟩) b <;> simp; grind)

@[simp] theorem mem_subPos {P : Finset Pos} {i : ℕ} {r : Pos} : r ∈ subPos P i ↔ i :: r ∈ P := by
  simp only [subPos, Finset.mem_filterMap]
  constructor
  · rintro ⟨_ | ⟨j, r'⟩, h, he⟩ <;> simp_all
  · exact fun h => ⟨i :: r, h, by simp⟩

/-- A canonical complete development of a set `P` of redexes: *innermost first, left to right*.
Since inner redexes are contracted before the outer ones, nothing is duplicated, and each redex
of `P` is contracted exactly once. -/
def dev : LTerm → Finset Pos → List Pos
  | var _, _ => []
  | lam t, P => (dev t (subPos P 0)).map (0 :: ·)
  | app t s, P =>
      (dev t (subPos P 0)).map (0 :: ·) ++ (dev s (subPos P 1)).map (1 :: ·) ++
        (if [] ∈ P then [[]] else [])

/-! ### β-reduction -/

/-- A β-step `t →β u`. -/
def BetaStep (t u : LTerm) : Prop := ∃ p, isRedexAt t p = true ∧ contractAt t p = u

/-- The usual inductive presentation of β-reduction: the contextual closure of
`(λx.t)s →β t{x := s}`. -/
inductive Beta : LTerm → LTerm → Prop
  | beta (t s : LTerm) : Beta (app (lam t) s) (substAt 0 s t)
  | lam {t t'} : Beta t t' → Beta (lam t) (lam t')
  | appL {t t'} (s : LTerm) : Beta t t' → Beta (app t s) (app t' s)
  | appR (t : LTerm) {s s'} : Beta s s' → Beta (app t s) (app t s')

/-! ### Head normal forms (Chapter 4) -/

/-- `y t₁ … tₘ`. -/
inductive IsHeadApp : LTerm → Prop
  | var (n : ℕ) : IsHeadApp (var n)
  | app {t : LTerm} (s : LTerm) : IsHeadApp t → IsHeadApp (app t s)

/-- Head normal forms `λx₁…xₙ. y t₁ … tₘ`. -/
inductive IsHNF : LTerm → Prop
  | head {t : LTerm} : IsHeadApp t → IsHNF t
  | lam {t : LTerm} : IsHNF t → IsHNF (lam t)

/-- `t` has a head normal form. -/
def HasHNF (t : LTerm) : Prop := ∃ u, Relation.ReflTransGen BetaStep t u ∧ IsHNF u

end LTerm

open LTerm

/-- The λ-calculus as an axiomatic rewrite system. -/
abbrev lambdaRS : ResidualSystem where
  Obj := LTerm
  Adr := Pos
  isStep t p := isRedexAt t p = true
  contract := contractAt
  res := residuals
  dev := dev

/-- Derivations of the λ-calculus. -/
abbrev LDeriv (t : LTerm) : Type := lambdaRS.DerivFrom t

end Thesis
