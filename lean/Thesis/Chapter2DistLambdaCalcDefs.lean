/-
# Chapter 2: A distributive λ-calculus (λ^dist) — Definitions

## Representation choices

* **Binders** use de Bruijn indices: `lam ℓ t` binds index `0` in `t`, and the typing rule
  `Γ ⊕ x : M ⊢ t : σ` becomes `M :: Γ ⊢ t : σ` (see `Ctx.cons`).
* **Multisets inside types.** A type `M →ℓ σ` contains a multiset `M`. Lean can't nest an
  inductive type through `Multiset` (a quotient), so the domain is a `List Ty`. The typing rule
  `→I` always produces the *canonical* listing `Ty.canon M` of the multiset (sorted by a linear
  order on types, so it is computable), and `→E` matches arguments against the domain up to
  permutation. Hence every typable term has a unique type (`hasType_unique`), exactly as in the
  thesis, where types are built from multisets.
* **Typing contexts** really are multiset-valued: `Ctx = ℕ → Multiset Ty`.
* **Substitution** is defined both as the thesis' *partition-based* relation (`PSubst`) and its
  *type-directed* ("alternative") function (`DTerm.subst`), which agree under sequentiality.
-/
import Thesis.Chapter1Prelim

namespace Thesis

/-- Labels `ℒ`, a denumerable set. -/
abbrev Label := ℕ

/-! ## 2.1 Types -/

/-- Types: `τ ::= α^ℓ | M →ℓ τ`, where `M` is a (sequential, hence canonically listed) multiset. -/
inductive Ty
  | base (α : ℕ) (ℓ : Label)
  | arrow (dom : List Ty) (ℓ : Label) (cod : Ty)
  deriving Repr

namespace Ty

/-- The external label. -/
def label : Ty → Label
  | base _ ℓ => ℓ
  | arrow _ ℓ _ => ℓ

/-- `σ ⊴ τ`: `σ` occurs in `τ`. Reflexive–transitive closure of `τᵢ ⊴ [τ₁…τₙ] → σ` and
`σ ⊴ [τ₁…τₙ] → σ`. -/
inductive Occurs : Ty → Ty → Prop
  | refl (τ : Ty) : Occurs τ τ
  | dom {σ τ : Ty} {M : List Ty} {ℓ : Label} {ρ : Ty} : τ ∈ M → Occurs σ τ → Occurs σ (arrow M ℓ ρ)
  | cod {σ ρ : Ty} {M : List Ty} {ℓ : Label} : Occurs σ ρ → Occurs σ (arrow M ℓ ρ)

/-! ### A computable linear order on types

`deriving DecidableEq`/`Encodable` don't support nested inductives, so we serialize types
by hand. The order itself carries no meaning: it only picks a canonical listing of a multiset. -/

mutual
/-- Prefix-free serialization of a type. -/
def enc : Ty → List ℕ
  | base α ℓ => [0, α, ℓ]
  | arrow dom ℓ cod => [1, dom.length, ℓ] ++ encList dom ++ enc cod
/-- Serialization of a list of types (its length is stored by the enclosing `enc`). -/
def encList : List Ty → List ℕ
  | [] => []
  | d :: ds => enc d ++ encList ds
end

mutual
theorem enc_append_inj : ∀ (a b : Ty) (r r' : List ℕ), a.enc ++ r = b.enc ++ r' → a = b ∧ r = r'
  | base α ℓ, base β m, r, r', h => by simp_all [enc]
  | base _ _, arrow _ _ _, _, _, h => by simp [enc] at h
  | arrow _ _ _, base _ _, _, _, h => by simp [enc] at h
  | arrow ds ℓ c, arrow es m d, r, r', h => by
    simp only [enc, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
      true_and] at h
    obtain ⟨hlen, rfl, h⟩ := h
    obtain ⟨rfl, h⟩ := encList_append_inj ds es _ _ hlen h
    obtain ⟨rfl, rfl⟩ := enc_append_inj c d r r' (List.append_cancel_left h)
    exact ⟨rfl, rfl⟩
theorem encList_append_inj : ∀ (ds es : List Ty) (r r' : List ℕ), ds.length = es.length →
    encList ds ++ r = encList es ++ r' → ds = es ∧ r = r'
  | [], [], _, _, _, h => by simpa [encList] using h
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | d :: ds, e :: es, r, r', hl, h => by
    simp only [encList, List.append_assoc] at h
    obtain ⟨rfl, h⟩ := enc_append_inj d e _ _ h
    obtain ⟨rfl, rfl⟩ :=
      encList_append_inj ds es r r' (by simpa using hl) (List.append_cancel_left h)
    exact ⟨rfl, rfl⟩
end

theorem enc_injective : Function.Injective enc := fun a b h =>
  (enc_append_inj a b [] [] (by simpa using h)).1

/-- Types are linearly ordered (lexicographically on `enc`); this also gives `DecidableEq Ty`. -/
instance : LinearOrder Ty := LinearOrder.lift' enc enc_injective

/-- The canonical listing of a multiset of types: sorted. -/
def canon (M : Multiset Ty) : List Ty := M.sort (· ≤ ·)

@[simp] theorem coe_canon (M : Multiset Ty) : (canon M : Multiset Ty) = M := Multiset.sort_eq _ _

@[simp] theorem mem_canon {M : Multiset Ty} {τ : Ty} : τ ∈ canon M ↔ τ ∈ M := Multiset.mem_sort _

@[simp] theorem length_canon (M : Multiset Ty) : (canon M).length = Multiset.card M :=
  Multiset.length_sort _

@[simp] theorem canon_zero : canon 0 = [] := Multiset.sort_zero _

end Ty

/-- A multiset of types is *sequential*: external labels are pairwise distinct. -/
def SeqMS (M : Multiset Ty) : Prop := (M.map Ty.label).Nodup

/-! ## Typing contexts (Chapter 1, §"Typing") -/

/-- Typing contexts: total functions from (de Bruijn) variables to finite multisets of types.
Sum of contexts `Γ + Δ` is the pointwise sum (the `Pi` instance), `0` is the empty context. -/
abbrev Ctx := ℕ → Multiset Ty

namespace Ctx

/-- The context `x : M`. -/
def single (n : ℕ) (M : Multiset Ty) : Ctx := fun m => if m = n then M else 0

/-- `Γ ⊕ x : M` when `x` is the variable bound by a new binder: `M` at index `0`, `Γ` shifted. -/
def cons (M : Multiset Ty) (Γ : Ctx) : Ctx
  | 0 => M
  | n + 1 => Γ n

/-- A context is sequential if every `Γ(x)` is. -/
def Seq (Γ : Ctx) : Prop := ∀ n, SeqMS (Γ n)

/-- `σ ⊴ Γ`. -/
def Occurs (σ : Ty) (Γ : Ctx) : Prop := ∃ n, ∃ τ ∈ Γ n, Ty.Occurs σ τ

end Ctx

/-! ## 2.2 Syntax -/

/-- Distributive terms: `t ::= x^τ | λ^ℓ x. t | t [t₁, …, tₙ]`. -/
inductive DTerm
  | var (n : ℕ) (τ : Ty)
  | lam (ℓ : Label) (t : DTerm)
  | app (t : DTerm) (args : List DTerm)
  deriving Repr

namespace DTerm

/-- `s` is a sub-term of `t`. -/
inductive Sub : DTerm → DTerm → Prop
  | refl (t : DTerm) : Sub t t
  | lam {s t : DTerm} (ℓ : Label) : Sub s t → Sub s (.lam ℓ t)
  | fn {s t : DTerm} (ss : List DTerm) : Sub s t → Sub s (.app t ss)
  | arg {s u : DTerm} (t : DTerm) {ss : List DTerm} : u ∈ ss → Sub s u → Sub s (.app t ss)

/-- The labels decorating the λs of a term, one per λ (so repetitions are kept). -/
def lamLabels : DTerm → List Label
  | var _ _ => []
  | lam ℓ t => ℓ :: lamLabels t
  | app t ss => lamLabels t ++ ss.flatMap lamLabels

/-- The number of λs of a term, `d(t)` in the proof of termination. -/
def size : DTerm → ℕ
  | var _ _ => 0
  | lam _ t => size t + 1
  | app t ss => size t + (ss.map size).sum

/-- The types of the free occurrences of the variable `k`, `𝓜_x(t)`. -/
def occTypes : DTerm → ℕ → List Ty
  | var n τ, k => if n = k then [τ] else []
  | lam _ t, k => occTypes t (k + 1)
  | app t ss, k => occTypes t k ++ ss.flatMap (occTypes · k)

/-- The type of a term, computed syntactically. By `hasType_ty` this is *the* type of any
typable term. -/
def ty : DTerm → Ty
  | var _ τ => τ
  | lam ℓ t => .arrow (Ty.canon (occTypes t 0)) ℓ (ty t)
  | app t _ =>
    match ty t with
    | .arrow _ _ τ => τ
    | τ => τ

/-- The typing context of a term, computed syntactically (see `linearity`). -/
def ctx (t : DTerm) : Ctx := fun n => (t.occTypes n : Multiset Ty)

end DTerm

/-! ### Typing rules -/

mutual
/-- The distributive type system: rules `var`, `→I`, `→E`. -/
inductive HasType : Ctx → DTerm → Ty → Prop
  | var (n : ℕ) (τ : Ty) : HasType (Ctx.single n {τ}) (.var n τ) τ
  | lam {Γ : Ctx} {M : Multiset Ty} {σ : Ty} {t : DTerm} (ℓ : Label) :
      HasType (Ctx.cons M Γ) t σ → HasType Γ (.lam ℓ t) (.arrow (Ty.canon M) ℓ σ)
  | app {Γ : Ctx} {t : DTerm} {L : List Ty} {ℓ : Label} {τ : Ty}
      {Δs : List Ctx} {ss : List DTerm} {σs : List Ty} :
      HasType Γ t (.arrow L ℓ τ) → HasTypeMulti Δs ss σs → σs.Perm L →
      HasType (Γ + Δs.sum) (.app t ss) τ
/-- The judgment `[Γ₁, …, Γₙ] ⊢ [t₁, …, tₙ] : [τ₁, …, τₙ]` (rule `t-multi`). -/
inductive HasTypeMulti : List Ctx → List DTerm → List Ty → Prop
  | nil : HasTypeMulti [] [] []
  | cons {Γ : Ctx} {t : DTerm} {τ : Ty} {Δs ts τs} :
      HasType Γ t τ → HasTypeMulti Δs ts τs → HasTypeMulti (Γ :: Δs) (t :: ts) (τ :: τs)
end

namespace DTerm

/-- `t` is typable. -/
def Typable (t : DTerm) : Prop := ∃ Γ τ, HasType Γ t τ

end DTerm

/-! ### Correctness -/

/-- **Correct terms** (Definition "Correct term"): typable, plus
1. uniquely labeled lambdas;
2. sequential contexts;
3. sequential types. -/
structure Correct (t : DTerm) : Prop where
  typable : t.Typable
  uniquely_labeled : t.lamLabels.Nodup
  seq_ctx : ∀ s Γ τ, DTerm.Sub s t → HasType Γ s τ → Γ.Seq
  seq_ty : ∀ s Γ τ, DTerm.Sub s t → HasType Γ s τ → ∀ M ℓ ρ,
    (Ctx.Occurs (.arrow M ℓ ρ) Γ ∨ Ty.Occurs (.arrow M ℓ ρ) τ) → SeqMS (M : Multiset Ty)

/-- `𝒯^dist`: the set of correct terms. -/
def CTerm : Type := {t : DTerm // Correct t}

/-! ## 2.3 The calculus -/

namespace DTerm

/-- `shift d c t` adds `d` to every free index `≥ c`. -/
def shift (d : ℕ) : ℕ → DTerm → DTerm
  | c, var n τ => if n < c then var n τ else var (n + d) τ
  | c, lam ℓ t => lam ℓ (shift d (c + 1) t)
  | c, app t ss => app (shift d c t) (ss.map (shift d c))

/-- **Type-directed substitution** `t⟨k := s̄⟩` (the thesis' alternative definition): an
occurrence `k^τ` is replaced by the argument of `s̄` whose type is `τ`. The arguments live outside
the `k` binders crossed so far; indices above `k` are decremented. -/
def subst : DTerm → ℕ → List DTerm → DTerm
  | var n τ, k, ss =>
    if n < k then var n τ
    else if n = k then (((ss.find? fun s => decide (s.ty = τ))).map (shift k 0)).getD (var n τ)
    else var (n - 1) τ
  | lam ℓ t, k, ss => lam ℓ (subst t (k + 1) ss)
  | app t us, k, ss => app (subst t k ss) (us.map (subst · k ss))

end DTerm

mutual
/-- Resource-sensitive substitution, defined on raw terms. The application rule partitions
its arguments up to permutation; each argument is used exactly once. Unlike type-directed
lookup, this relation also handles repeated argument types. -/
inductive PSubst : DTerm → ℕ → List DTerm → DTerm → Prop
  | var_eq {s : DTerm} {Γ : Ctx} {τ : Ty} (k : ℕ) : HasType Γ s τ →
      PSubst (.var k τ) k [s] (s.shift k 0)
  | var_lt {n k : ℕ} (τ : Ty) : n < k → PSubst (.var n τ) k [] (.var n τ)
  | var_gt {n k : ℕ} (τ : Ty) : k < n → PSubst (.var n τ) k [] (.var (n - 1) τ)
  | lam {t u : DTerm} {k : ℕ} {ss : List DTerm} (ℓ : Label) :
      PSubst t (k + 1) ss u → PSubst (.lam ℓ t) k ss (.lam ℓ u)
  | app {t u : DTerm} {ts us ss ss₀ ss₁ : List DTerm} {k : ℕ} :
      PSubst t k ss₀ u → PSubstMulti ts k ss₁ us → (ss₀ ++ ss₁).Perm ss →
      PSubst (.app t ts) k ss (.app u us)
inductive PSubstMulti : List DTerm → ℕ → List DTerm → List DTerm → Prop
  | nil (k : ℕ) : PSubstMulti [] k [] []
  | cons {t u : DTerm} {ts us ss₀ ss₁ : List DTerm} {k : ℕ} :
      PSubst t k ss₀ u → PSubstMulti ts k ss₁ us →
      PSubstMulti (t :: ts) k (ss₀ ++ ss₁) (u :: us)
end

/-- One-hole contexts `C ::= □ | λ^ℓ x.C | C s̄ | t[s̄, C, ū]`. -/
inductive DCtx
  | hole
  | lam (ℓ : Label) (C : DCtx)
  | appL (C : DCtx) (ss : List DTerm)
  | appR (t : DTerm) (us : List DTerm) (C : DCtx) (vs : List DTerm)

namespace DCtx

/-- `C⟨t⟩` (capturing). -/
def plug : DCtx → DTerm → DTerm
  | hole, t => t
  | lam ℓ C, t => .lam ℓ (C.plug t)
  | appL C ss, t => .app (C.plug t) ss
  | appR t us C vs, s => .app t (us ++ C.plug s :: vs)

/-- Number of binders above the hole. -/
def depth : DCtx → ℕ
  | hole => 0
  | lam _ C => C.depth + 1
  | appL C _ => C.depth
  | appR _ _ C _ => C.depth

end DCtx

/-- The reduction relation `→ℓ` of λ^dist:
`C⟨(λ^ℓ x.t) s̄⟩ →ℓ C⟨t{x := s̄}⟩`. -/
inductive DStep : DTerm → Label → DTerm → Prop
  | beta (ℓ : Label) (t : DTerm) (ss : List DTerm) : DStep (.app (.lam ℓ t) ss) ℓ (t.subst 0 ss)
  | lam {t t' : DTerm} {ℓ : Label} (m : Label) : DStep t ℓ t' → DStep (.lam m t) ℓ (.lam m t')
  | appL {t t' : DTerm} {ℓ : Label} (ss : List DTerm) :
      DStep t ℓ t' → DStep (.app t ss) ℓ (.app t' ss)
  | appR {s s' : DTerm} {ℓ : Label} (t : DTerm) (us vs : List DTerm) :
      DStep s ℓ s' → DStep (.app t (us ++ s :: vs)) ℓ (.app t (us ++ s' :: vs))

/-- `→dist = ⋃ℓ →ℓ`. -/
def DRed (t u : DTerm) : Prop := ∃ ℓ, DStep t ℓ u

/-- Reduction restricted to correct terms. -/
def CRed (t u : CTerm) : Prop := DRed t.1 u.1

end Thesis
