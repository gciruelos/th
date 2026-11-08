/-
# Chapter 2: A distributive λ-calculus (λ^dist)

Main-text results of Chapter 2:
* Unique typing (`unique_typing`).
* Agreement of partition-based and type-directed substitution (`PSubst.eq_subst`), typing of
  substitution (`subst_hasType`), and the substitution lemma (`subst_subst`).
* Linearity (`linearity`) and subject reduction (`subject_reduction`, `correct_of_dStep`).
* Termination (`termination`) and the λ-count bound (`size_le_of_reduces`).
* Strong permutation (`strong_permutation`) and confluence (`confluence`).
-/
import Thesis.Chapter2DistLambdaCalcDefs
import Thesis.Chapter2DistLambdaCalcAppendix

namespace Thesis

/-! ## 2.2 Unique typing -/

/-- **Unique typing**: a correct term has a unique type and typing context. -/
theorem unique_typing {Γ Γ' : Ctx} {t : DTerm} {τ τ' : Ty} (_ht : Correct t)
    (h : HasType Γ t τ) (h' : HasType Γ' t τ') : Γ = Γ' ∧ τ = τ' :=
  hasType_unique h h'

/-! ## 2.3 Substitution -/

/-- **Alternative substitution**: sequential argument types suffice for agreement of
partition-based and type-directed substitution. -/
theorem PSubst.eq_subst {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) (hseq : SeqMS (ss.map DTerm.ty : Multiset Ty)) :
    u = t.subst k ss := by
  apply h.eq_subst_of_subset ss (fun _ h => h)
  exact List.Nodup.of_map (f := Ty.label) (by simpa [SeqMS] using hseq)

/-- **Substitution is well defined** (typing): if `Γ ⊕ x : [σ̄] ⊢ t : τ` and `Δ̄ ⊢ s̄ : σ̄`
(with `[σ̄]` sequential), then `Γ + ΣΔ̄ ⊢ t{x := s̄} : τ`. -/
theorem subst_hasType {Γ : Ctx} {t : DTerm} {τ : Ty} {Δs : List Ctx} {ss : List DTerm}
    {σs : List Ty} (ht : HasType (Ctx.cons (σs : Multiset Ty) Γ) t τ)
    (hs : HasTypeMulti Δs ss σs) (hseq : SeqMS (σs : Multiset Ty)) :
    HasType (Γ + Δs.sum) (t.subst 0 ss) τ := by
  obtain ⟨u, hp⟩ := PSubst.exists (t := t) (k := 0) hs (hasType_occTypes ht 0)
  have hn : (ss.map DTerm.ty).Nodup := List.Nodup.of_map (f := Ty.label)
    (by simpa only [← hs.types_eq, SeqMS, Multiset.map_coe, Multiset.coe_nodup] using hseq)
  have hc := congrArg List.sum hs.contexts_eq
  have hu := hp.typing ht
  simpa only [hp.eq_subst_of_subset ss (fun _ h => h) hn, hc, Ctx.shift_zero_cutoff,
    show (Ctx.cons (σs : Multiset Ty) Γ).remove 0 = Γ from rfl] using hu

/-- **Substitution lemma** for the alternative substitution (`03-03-the-calculus.tex`).
Lookup is defined on the body, and substitution in the arguments preserves their types.
Arguments of `DTerm.subst` live outside all crossed binders, so `us` needs no extra shift. -/
theorem subst_subst (t : DTerm) (k : ℕ) (ss us : List DTerm)
    (hd : t.SubstDefined 0 ss) (ht : ∀ s ∈ ss, (s.subst k us).ty = s.ty) :
    (t.subst 0 ss).subst k us =
      (t.subst (k + 1) us).subst 0 (ss.map (·.subst k us)) := by
  simpa only [Nat.zero_add] using t.subst_commute 0 k ss us hd ht

/-! ## 2.4 Basic properties -/

/-- **Linearity**: the typing context of a term records exactly the types of the free
occurrences of each variable, `Γ(x) = [τ₁, …, τₙ]`. (This holds for any typable term.) -/
theorem linearity {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ) (n : ℕ) :
    Γ n = (t.occTypes n : Multiset Ty) :=
  hasType_occTypes h n

/-- **Subject reduction**: types and contexts are preserved, and so is correctness. -/
theorem subject_reduction {Γ : Ctx} {t u : DTerm} {τ : Ty} {ℓ : Label}
    (ht : Correct t) (h : HasType Γ t τ) (hs : DStep t ℓ u) : HasType Γ u τ ∧ Correct u := by
  exact hs.subject_reduction ht h

theorem correct_of_dStep {t u : DTerm} {ℓ : Label} (ht : Correct t) (hs : DStep t ℓ u) :
    Correct u := by
  obtain ⟨Γ, τ, h⟩ := ht.typable
  exact (subject_reduction ht h hs).2

/-! ### Termination -/

/-- **Termination**: there is no infinite reduction sequence `t₀ → t₁ → t₂ → ⋯` from a correct
term. -/
theorem termination : ¬ ∃ f : ℕ → DTerm, Correct (f 0) ∧ ∀ n, DRed (f n) (f (n + 1)) := by
  rintro ⟨f, h0, hf⟩
  have hc : ∀ n, Correct (f n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => obtain ⟨ℓ, h⟩ := hf n; exact correct_of_dStep ih h
  have key : ∀ n, (f n).size + n = (f 0).size := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      obtain ⟨ℓ, h⟩ := hf n
      have := size_dStep (hc n) h
      omega
  have := key ((f 0).size + 1)
  omega

/-- Reduction never increases the number of λs. -/
theorem size_le_of_reduces {t u : DTerm} (ht : Correct t)
    (h : Relation.ReflTransGen DRed t u) : u.size ≤ t.size := by
  induction h with
  | refl => exact le_rfl
  | @tail b c hab hbc ih =>
    obtain ⟨ℓ, hs⟩ := hbc
    have hb : Correct b := by
      clear ih hs
      induction hab with
      | refl => exact ht
      | tail _ h ih' => obtain ⟨ℓ', h⟩ := h; exact correct_of_dStep ih' h
    have := size_dStep hb hs
    omega

/-! ### Confluence -/

/-- **Strong permutation** (diamond property): two different steps `t₀ →ℓ t₁` and `t₀ →ℓ' t₂`
can be closed by `t₁ →ℓ' t₃` and `t₂ →ℓ t₃`. -/
theorem strong_permutation {t₀ t₁ t₂ : DTerm} {ℓ ℓ' : Label} (h₀ : Correct t₀)
    (h₁ : DStep t₀ ℓ t₁) (h₂ : DStep t₀ ℓ' t₂) (hne : ℓ ≠ ℓ' ∨ t₁ ≠ t₂) :
    ∃ t₃, DStep t₁ ℓ' t₃ ∧ DStep t₂ ℓ t₃ := by
  rcases DStep.permutation h₀ h₁ h₂ with ⟨he, ht⟩ | h
  · exact False.elim (hne.elim (fun hn => hn he) (fun hn => hn ht))
  · exact h

/-- **Confluence** of λ^dist (a consequence of strong permutation, via sub-commutativity). -/
theorem confluence {t₀ t₁ t₂ : CTerm} (h₁ : Relation.ReflTransGen CRed t₀ t₁)
    (h₂ : Relation.ReflTransGen CRed t₀ t₂) :
    ∃ t₃, Relation.ReflTransGen CRed t₁ t₃ ∧ Relation.ReflTransGen CRed t₂ t₃ := by
  refine Relation.church_rosser (fun a b c hab hac => ?_) h₁ h₂
  obtain ⟨ℓ, hb⟩ := hab
  obtain ⟨ℓ', hc⟩ := hac
  by_cases hbc : ℓ ≠ ℓ' ∨ b.1 ≠ c.1
  · obtain ⟨d, hbd, hcd⟩ := strong_permutation a.2 hb hc hbc
    let d' : CTerm := ⟨d, correct_of_dStep b.2 hbd⟩
    exact ⟨d', Relation.ReflGen.single ⟨ℓ', hbd⟩, Relation.ReflTransGen.single ⟨ℓ, hcd⟩⟩
  · push Not at hbc
    obtain ⟨-, e⟩ := hbc
    have : b = c := Subtype.ext e
    subst this
    exact ⟨b, Relation.ReflGen.refl, Relation.ReflTransGen.refl⟩

end Thesis
