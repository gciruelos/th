/-
# Chapter 1: Preliminaries

Main-text results of Chapter 1:
* Poset structure on the Grothendieck construction `LaxFunctor.Groth`.
* Summary of properties of orthogonal axiomatic rewrite systems (Melliès) and the upper-semilattice
  with bottom structure on derivation spaces `DSpace`.
* Orthogonality of the pure λ-calculus (`lambda_orthogonal`) and Laneve's counterexample
  (`lambda_dspace_not_lattice`).
-/
import Thesis.Chapter1PrelimDefs
import Thesis.Chapter1PrelimAppendix
import Thesis.Chapter0

namespace Thesis

universe u v

namespace LaxFunctor

variable {A : Type u} [PartialOrder A] {B : LaxFunctor.{u, v} A}

instance : PartialOrder B.Groth where
  le p q := ∃ h : p.1 ≤ q.1, B.map h p.2 ≤ q.2
  le_refl p := ⟨le_refl _, by rw [B.map_id]⟩
  le_trans p q r := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
    exact ⟨h₁.trans h₂, (B.map_comp h₁ h₂ p.2).trans ((B.map_mono h₂ k₁).trans k₂)⟩
  le_antisymm := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
    obtain rfl : a = b := le_antisymm h₁ h₂
    simp only [B.map_id] at k₁ k₂
    rw [le_antisymm k₁ k₂]

theorem Groth.le_def {p q : B.Groth} : p ≤ q ↔ ∃ h : p.1 ≤ q.1, B.map h p.2 ≤ q.2 := Iff.rfl

end LaxFunctor

namespace ResidualSystem

variable (R : ResidualSystem)

@[simp] theorem proj_nil_left (t : R.Obj) (τ : List R.Adr) : R.proj t [] τ = [] := rfl

theorem prefix_nil_left (t : R.Obj) (τ : List R.Adr) : R.Prefix t [] τ := rfl

/-! ### Results of the theory of orthogonal axiomatic rewrite systems (Melliès)

These are the entries of the "summary of properties" table of Chapter 1. -/

section Mellies

variable {R} (hR : R.Orthogonal)
include hR

theorem proj_valid {t : R.Obj} {σ τ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ) :
    R.Valid (R.tgt t τ) (R.proj t σ τ) :=
  proj_valid_aux hR hσ hτ

/-- `σ (τ/σ)` and `τ (σ/τ)` are cofinal. -/
theorem tgt_join_comm {t : R.Obj} {σ τ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ) :
    R.tgt t (R.join t σ τ) = R.tgt t (R.join t τ σ) :=
  (permGen_join_comm hR hσ hτ).tgt_eq hR

/-- `σ / ε = σ`. -/
theorem proj_nil_right {t : R.Obj} {σ : List R.Adr} (hσ : R.Valid t σ) : R.proj t σ [] = σ :=
  proj_nil_right_aux hR hσ

/-- `σ / σ = ε`. -/
theorem proj_self {t : R.Obj} {σ : List R.Adr} (hσ : R.Valid t σ) : R.proj t σ σ = [] :=
  proj_self_aux hR hσ

/-- `σ / τρ ≡ (σ/τ)/ρ`. -/
theorem proj_append_right {t : R.Obj} {σ τ ρ : List R.Adr} (hσ : R.Valid t σ)
    (hτρ : R.Valid t (τ ++ ρ)) :
    R.PermEq (R.tgt t (τ ++ ρ)) (R.proj t σ (τ ++ ρ)) (R.proj (R.tgt t τ) (R.proj t σ τ) ρ) := by
  have h := permGen_proj_append_right hR hσ hτρ
  exact (permGen_iff_permEq hR (h.valid_left hR) (h.valid_right hR)).1 h

/-- `στ / ρ = (σ/ρ)(τ/(ρ/σ))`. -/
theorem proj_append_left {t : R.Obj} {σ τ ρ : List R.Adr} (hστ : R.Valid t (σ ++ τ))
    (hρ : R.Valid t ρ) :
    R.proj t (σ ++ τ) ρ = R.proj t σ ρ ++ R.proj (R.tgt t σ) τ (R.proj t ρ σ) :=
  proj_append_left_aux hR hστ hρ

theorem prefix_refl {t : R.Obj} {σ : List R.Adr} (hσ : R.Valid t σ) : R.Prefix t σ σ :=
  proj_self hR hσ

theorem prefix_trans {t : R.Obj} {σ τ ρ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ)
    (hρ : R.Valid t ρ) : R.Prefix t σ τ → R.Prefix t τ ρ → R.Prefix t σ ρ := by
  intro hστ hτρ
  unfold Prefix at hστ hτρ ⊢
  have hj : PermGen R t ρ (τ ++ R.proj t ρ τ) := by
    simpa [join, hτρ] using permGen_join_comm hR hρ hτ
  rw [proj_congr_permGen hR hσ hj]
  have hp := permGen_proj_append_right hR hσ (hj.valid_right hR)
  rw [hστ, proj_nil_left] at hp
  exact hp.eq_nil_of_right_nil hR

/-- `σ ≡ τ ⟹ ρ/σ = ρ/τ`. -/
theorem proj_congr_permEq {t : R.Obj} {σ τ ρ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ)
    (hρ : R.Valid t ρ) (h : R.PermEq t σ τ) : R.proj t ρ σ = R.proj t ρ τ :=
  proj_congr_permGen hR hρ ((permGen_iff_permEq hR hσ hτ).2 h)

/-- `σ ⊑ τ ⟺ ∃ ρ, σρ ≡ τ`. -/
theorem prefix_iff_exists {t : R.Obj} {σ τ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ) :
    R.Prefix t σ τ ↔ ∃ ρ, R.Valid (R.tgt t σ) ρ ∧ R.PermEq t (σ ++ ρ) τ := by
  constructor
  · intro h
    unfold Prefix at h
    refine ⟨R.proj t τ σ, proj_valid hR hτ hσ, ?_⟩
    have hj : PermGen R t (σ ++ R.proj t τ σ) τ := by
      simpa [join, h] using permGen_join_comm hR hσ hτ
    exact (permGen_iff_permEq hR (hj.valid_left hR) hτ).1 hj
  · rintro ⟨ρ, hρ, hperm⟩
    unfold Prefix
    have hστ : R.Valid t (σ ++ ρ) := (R.valid_append _ _ _).2 ⟨hσ, hρ⟩
    rw [← proj_congr_permEq hR hστ hτ hσ hperm]
    have hp := permGen_proj_append_right hR hσ hστ
    rw [proj_self hR hσ, proj_nil_left] at hp
    exact hp.eq_nil_of_right_nil hR

theorem prefix_join_left {t : R.Obj} {σ τ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ) :
    R.Prefix t σ (R.join t σ τ) := by
  have hj : R.Valid t (R.join t σ τ) := (R.valid_append _ _ _).2 ⟨hσ, proj_valid hR hτ hσ⟩
  exact (prefix_iff_exists hR hσ hj).2
    ⟨R.proj t τ σ, proj_valid hR hτ hσ, prefix_refl hR hj, prefix_refl hR hj⟩

theorem prefix_join_right {t : R.Obj} {σ τ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ) :
    R.Prefix t τ (R.join t σ τ) := by
  have hc := permGen_join_comm hR hτ hσ
  have hperm := (permGen_iff_permEq hR (hc.valid_left hR) (hc.valid_right hR)).1 hc
  exact (prefix_iff_exists hR hτ (hc.valid_right hR)).2 ⟨R.proj t σ τ, proj_valid hR hσ hτ, hperm⟩

theorem join_prefix {t : R.Obj} {σ τ ρ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ)
    (hρ : R.Valid t ρ) : R.Prefix t σ ρ → R.Prefix t τ ρ → R.Prefix t (R.join t σ τ) ρ := by
  intro h1 h2
  have hj : R.Valid t (R.join t σ τ) := (R.valid_append _ _ _).2 ⟨hσ, proj_valid hR hτ hσ⟩
  unfold Prefix join at *
  rw [proj_append_left hR hj hρ, h1, List.nil_append]
  have hcomm : PermGen R t (σ ++ R.proj t ρ σ) ρ := by
    simpa [join, h1] using permGen_join_comm hR hσ hρ
  have hp := (permGen_proj_append_right hR hτ (hcomm.valid_left hR)).symm
  rw [proj_congr_permGen hR hτ hcomm, h2] at hp
  exact hp.eq_nil_of_right_nil hR

/-- `σ ⊑ τ ⟹ σ/ρ ⊑ τ/ρ`. -/
theorem prefix_proj {t : R.Obj} {σ τ ρ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ)
    (hρ : R.Valid t ρ) (h : R.Prefix t σ τ) :
    R.Prefix (R.tgt t ρ) (R.proj t σ ρ) (R.proj t τ ρ) := by
  unfold Prefix at h ⊢
  have hρτ : R.Valid t (ρ ++ R.proj t τ ρ) :=
    (R.valid_append _ _ _).2 ⟨hρ, proj_valid hR hτ hρ⟩
  have hp1 := (permGen_proj_append_right hR hσ hρτ).symm
  have hc := permGen_join_comm hR hρ hτ
  have heq : R.proj t σ (ρ ++ R.proj t τ ρ) = R.proj t σ (τ ++ R.proj t ρ τ) :=
    proj_congr_permGen hR hσ hc
  have hτρ : R.Valid t (τ ++ R.proj t ρ τ) := hc.valid_right hR
  have hp2 := permGen_proj_append_right hR hσ hτρ
  rw [h, proj_nil_left] at hp2
  have hmid : R.proj t σ (ρ ++ R.proj t τ ρ) = [] := by
    rw [heq]
    exact hp2.eq_nil_of_right_nil hR
  rw [hmid] at hp1
  exact hp1.eq_nil_of_right_nil hR

/-- `σ ⊑ τ ⟺ ρσ ⊑ ρτ`. -/
theorem prefix_append_iff {t : R.Obj} {σ τ ρ : List R.Adr} (hρ : R.Valid t ρ)
    (hσ : R.Valid (R.tgt t ρ) σ) (hτ : R.Valid (R.tgt t ρ) τ) :
    R.Prefix (R.tgt t ρ) σ τ ↔ R.Prefix t (ρ ++ σ) (ρ ++ τ) := by
  have hρσ : R.Valid t (ρ ++ σ) := (R.valid_append _ _ _).2 ⟨hρ, hσ⟩
  have hρτ : R.Valid t (ρ ++ τ) := (R.valid_append _ _ _).2 ⟨hρ, hτ⟩
  have h1 : R.proj t ρ (ρ ++ τ) = [] :=
    (prefix_iff_exists hR hρ hρτ).2 ⟨τ, hτ, prefix_refl hR hρτ, prefix_refl hR hρτ⟩
  have h2 : R.proj t (ρ ++ τ) ρ = τ := by
    rw [proj_append_left hR hρτ hρ, proj_self hR hρ, List.nil_append, proj_nil_right hR hτ]
  unfold Prefix
  rw [proj_append_left hR hρσ hρτ, h1, h2, List.nil_append]

/-- `(σ ⊔ τ)/ρ ≡ (σ/ρ) ⊔ (τ/ρ)`. -/
theorem proj_join {t : R.Obj} {σ τ ρ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ)
    (hρ : R.Valid t ρ) :
    R.PermEq (R.tgt t ρ) (R.proj t (R.join t σ τ) ρ)
      (R.join (R.tgt t ρ) (R.proj t σ ρ) (R.proj t τ ρ)) := by
  have hj : R.Valid t (R.join t σ τ) := (R.valid_append _ _ _).2 ⟨hσ, proj_valid hR hτ hσ⟩
  have h1 : R.proj t (R.join t σ τ) ρ =
      R.proj t σ ρ ++ R.proj (R.tgt t σ) (R.proj t τ σ) (R.proj t ρ σ) :=
    proj_append_left hR hj hρ
  have hσρ : R.Valid t (σ ++ R.proj t ρ σ) :=
    (R.valid_append _ _ _).2 ⟨hσ, proj_valid hR hρ hσ⟩
  have hρσ : R.Valid t (ρ ++ R.proj t σ ρ) :=
    (R.valid_append _ _ _).2 ⟨hρ, proj_valid hR hσ hρ⟩
  have hp1 := (permGen_proj_append_right hR hτ hσρ).symm
  have hc := permGen_join_comm hR hσ hρ
  have heq_mid : R.proj t τ (σ ++ R.proj t ρ σ) = R.proj t τ (ρ ++ R.proj t σ ρ) :=
    proj_congr_permGen hR hτ hc
  have hp2 := permGen_proj_append_right hR hτ hρσ
  have htg_eq : R.tgt t (σ ++ R.proj t ρ σ) = R.tgt (R.tgt t ρ) (R.proj t σ ρ) := by
    have h := hc.tgt_eq hR
    unfold join at h
    rwa [R.tgt_append t ρ] at h
  have hp2' : PermGen R (R.tgt (R.tgt t ρ) (R.proj t σ ρ))
      (R.proj t τ (ρ ++ R.proj t σ ρ))
      (R.proj (R.tgt t ρ) (R.proj t τ ρ) (R.proj t σ ρ)) := by
    simpa [R.tgt_append t ρ] using hp2
  have hp1' : PermGen R (R.tgt (R.tgt t ρ) (R.proj t σ ρ))
      (R.proj (R.tgt t σ) (R.proj t τ σ) (R.proj t ρ σ))
      (R.proj t τ (ρ ++ R.proj t σ ρ)) := by
    rw [← heq_mid, ← htg_eq]
    exact hp1
  have hp_all : PermGen R (R.tgt t ρ) (R.proj t (R.join t σ τ) ρ)
      (R.join (R.tgt t ρ) (R.proj t σ ρ) (R.proj t τ ρ)) := by
    rw [h1]
    exact PermGen.append (PermGen.refl (proj_valid hR hσ hρ)) (hp1'.trans hp2')
  exact (permGen_iff_permEq hR (hp_all.valid_left hR) (hp_all.valid_right hR)).1 hp_all

/-- Permutation-equivalent derivations are cofinal. -/
theorem tgt_eq_of_permEq {t : R.Obj} {σ τ : List R.Adr} (hσ : R.Valid t σ) (hτ : R.Valid t τ)
    (h : R.PermEq t σ τ) : R.tgt t σ = R.tgt t τ :=
  ((permGen_iff_permEq hR hσ hτ).2 h).tgt_eq hR

end Mellies

/-! ### The derivation space `𝔻(t)` as an upper semilattice -/

variable {R}

instance DerivFrom.instPreorder [hR : Fact R.Orthogonal] (t : R.Obj) : Preorder (R.DerivFrom t) where
  le σ τ := R.Prefix t σ.1 τ.1
  le_refl σ := prefix_refl hR.out σ.2
  le_trans σ τ ρ := prefix_trans hR.out σ.2 τ.2 ρ.2

theorem DerivFrom.le_def [Fact R.Orthogonal] {t : R.Obj} {σ τ : R.DerivFrom t} :
    σ ≤ τ ↔ R.Prefix t σ.1 τ.1 := Iff.rfl

/-- The join of two derivations, as a derivation. -/
def DerivFrom.join [hR : Fact R.Orthogonal] {t : R.Obj} (σ τ : R.DerivFrom t) :
    R.DerivFrom t :=
  ⟨R.join t σ.1 τ.1, (R.valid_append _ _ _).2 ⟨σ.2, proj_valid hR.out τ.2 σ.2⟩⟩

variable (R)

/-- The *derivation space* `𝔻(t)`: derivations out of `t` modulo permutation equivalence. -/
def DSpace [Fact R.Orthogonal] (t : R.Obj) : Type :=
  Antisymmetrization (R.DerivFrom t) (· ≤ ·)

variable {R}

namespace DSpace

variable [hR : Fact R.Orthogonal] {t : R.Obj}

instance : PartialOrder (R.DSpace t) :=
  inferInstanceAs (PartialOrder (Antisymmetrization (R.DerivFrom t) (· ≤ ·)))

/-- The class `[σ]` of a derivation. -/
def mk (σ : R.DerivFrom t) : R.DSpace t := toAntisymmetrization (· ≤ ·) σ

theorem mk_le_mk {σ τ : R.DerivFrom t} : mk σ ≤ mk τ ↔ σ ≤ τ := Iff.rfl

theorem mk_eq_mk {σ τ : R.DerivFrom t} : mk σ = mk τ ↔ R.PermEq t σ.1 τ.1 :=
  (toAntisymmetrization_eq _ _ _).trans Iff.rfl

@[elab_as_elim]
theorem ind {P : R.DSpace t → Prop} (h : ∀ σ, P (mk σ)) : ∀ x, P x :=
  fun x => Quotient.inductionOn' x h

/-- **Melliès**: in an orthogonal axiomatic rewrite system, `𝔻(t)` is an upper semilattice
(with bottom, see below), the join being `[σ] ⊔ [τ] = [σ(τ/σ)]`. -/
instance : SemilatticeSup (R.DSpace t) where
  sup := Quotient.map₂ DerivFrom.join (by
    intro σ σ' hσ τ τ' hτ
    refine ⟨?_, ?_⟩
    · exact join_prefix hR.out σ.2 τ.2 (σ'.join τ').2
        (prefix_trans hR.out σ.2 σ'.2 (σ'.join τ').2 hσ.1 (prefix_join_left hR.out σ'.2 τ'.2))
        (prefix_trans hR.out τ.2 τ'.2 (σ'.join τ').2 hτ.1 (prefix_join_right hR.out σ'.2 τ'.2))
    · exact join_prefix hR.out σ'.2 τ'.2 (σ.join τ).2
        (prefix_trans hR.out σ'.2 σ.2 (σ.join τ).2 hσ.2 (prefix_join_left hR.out σ.2 τ.2))
        (prefix_trans hR.out τ'.2 τ.2 (σ.join τ).2 hτ.2 (prefix_join_right hR.out σ.2 τ.2)))
  le_sup_left := by
    refine ind fun σ => ind fun τ => ?_
    exact prefix_join_left hR.out σ.2 τ.2
  le_sup_right := by
    refine ind fun σ => ind fun τ => ?_
    exact prefix_join_right hR.out σ.2 τ.2
  sup_le := by
    refine ind fun σ => ind fun τ => ind fun ρ => ?_
    exact join_prefix hR.out σ.2 τ.2 ρ.2

theorem mk_sup_mk (σ τ : R.DerivFrom t) : mk σ ⊔ mk τ = mk (σ.join τ) := rfl

instance : OrderBot (R.DSpace t) where
  bot := mk ⟨[], trivial⟩
  bot_le := ind fun τ => R.prefix_nil_left t τ.1

end DSpace

end ResidualSystem

/-- The λ-calculus is an orthogonal axiomatic rewrite system [Melliès]. -/
theorem lambda_orthogonal : lambdaRS.Orthogonal := Background.lambda_orthogonal

instance : Fact lambdaRS.Orthogonal := ⟨lambda_orthogonal⟩

/-- The derivation space `𝔻_λ(t)`, an upper semilattice. -/
abbrev DSpaceLam (t : LTerm) : Type := lambdaRS.DSpace t

open LTerm ResidualSystem in
/-- Laneve's counterexample (Introduction / §3.4): derivation spaces of the λ-calculus are not
lattices in general. The witness is `(λx.(λy.a)(x Ω))(λz.b)` and the derivations `ST`, `R`. -/
theorem lambda_dspace_not_lattice :
    ∃ (t : LTerm) (a b : DSpaceLam t), ¬ ∃ c, IsGLB {a, b} c := by
  let r : lambdaRS.DerivFrom laneveTerm := ⟨laneveR, by
      unfold laneveR ResidualSystem.Valid
      exact ⟨by decide, trivial⟩⟩
  let st : lambdaRS.DerivFrom laneveTerm := ⟨laneveST, by
      unfold laneveST ResidualSystem.Valid
      exact ⟨by decide, by decide, trivial⟩⟩
  refine ⟨laneveTerm, DSpace.mk r, DSpace.mk st, ?_⟩
  rintro ⟨c, hc⟩
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep c
  have hR : lambdaRS.Prefix laneveTerm σ.val laneveR :=
    hc.1 (show DSpace.mk r ∈ {DSpace.mk r, DSpace.mk st} from Set.mem_insert _ _)
  have hST : lambdaRS.Prefix laneveTerm σ.val laneveST :=
    hc.1 (show DSpace.mk st ∈ {DSpace.mk r, DSpace.mk st} by simp)
  obtain ⟨n, hn⟩ := laneve_lower_shape σ.val σ.property hR hST
  let longer : lambdaRS.DerivFrom laneveTerm :=
    ⟨List.replicate (n + 1) laneveU, laneve_repeat_valid (n + 1)⟩
  have hlower : DSpace.mk longer ∈ lowerBounds {DSpace.mk r, DSpace.mk st} := by
    intro d hd
    rcases Set.mem_insert_iff.1 hd with rfl | hd
    · exact (laneve_repeat_lower (n + 1)).1
    · have hd' := Set.mem_singleton_iff.1 hd
      subst d
      exact (laneve_repeat_lower (n + 1)).2
  have hle : lambdaRS.Prefix laneveTerm (List.replicate (n + 1) laneveU) σ.val := hc.2 hlower
  rw [hn] at hle
  exact laneve_repeat_not_le lambda_orthogonal n hle

end Thesis
