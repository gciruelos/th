/-
# Chapter 3: Residual theory of λ^dist

Main-text results of Chapter 3:
* Residuals, finite developments, and orthogonality of `distRS` (`card_res`,
  `length_of_completeDevelopment`, `orthogonal`).
* Names, belonging, permanence, and prefixes as subsets (`permanence`,
  `characterization_of_belonging`, `names_append_disjoint`, `length_eq_card_names`,
  `names_proj`, `prefix_iff_subset`, `permEq_iff_names`).
* Creation and stability (`creation`, `basic_stability`, `full_stability`).
* Meets (`meet_isGLB`, `names_join`, `names_meet`), the `DistribLattice` structure on
  `DSpace distRS t`, and the ring-of-sets representation `namesHom`.
-/
import Thesis.Chapter3ResidualTheoryDefs
import Thesis.Chapter3ResidualTheoryAppendix

namespace Thesis

namespace distRS

variable {t : CTerm}

/-- **Cardinality of the set of residuals**: `#(R/S) = 0` if `R = S`, and `1` otherwise. -/
theorem card_res {ℓ m : Label} (hℓ : distRS.isStep t ℓ) (hm : distRS.isStep t m) :
    (distRS.res t m ℓ).card = if ℓ = m then 0 else 1 := by
  rw [res_formula hℓ hm]
  split_ifs <;> simp

theorem res_eq {ℓ m : Label} (hℓ : distRS.isStep t ℓ) (hm : distRS.isStep t m) :
    distRS.res t m ℓ = if ℓ = m then ∅ else {ℓ} := by
  have := card_res hℓ hm
  dsimp only [distRS] at this ⊢
  split_ifs at this ⊢ <;> simp_all

/-- **Finite developments**: every complete development of `M` has length `#M`. -/
theorem length_of_completeDevelopment {M : Finset Label} {σ : List Label}
    (hM : ∀ ℓ ∈ M, distRS.isStep t ℓ) (h : distRS.IsCompleteDevelopment t M σ) :
    σ.length = M.card := by
  have hv := ResidualSystem.isDevelopment_valid h.1
  have he : M = names σ := Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp ((residual_names hM hv).1.symm.trans h.2))
    (development_subset hM h.1)
  rw [he]
  exact (List.toFinset_card_of_nodup (nodup_of_valid hv)).symm

/-- **λ^dist is an orthogonal axiomatic rewrite system** in the sense of Melliès
(Autoerasure and Finite Residuals from `card_res`, Finite Developments from
`length_of_completeDevelopment`, Semantic Orthogonality from `strong_permutation`). -/
theorem orthogonal : distRS.Orthogonal := by
  exact orthogonal_core

instance : Fact distRS.Orthogonal := ⟨orthogonal⟩

/-! ## Names -/

/-- **Permanence**: if `R ∉ σ` then `R/σ` is a singleton (with the same name). -/
theorem permanence {ℓ : Label} {σ : List Label} (hℓ : distRS.isStep t ℓ) (hσ : distRS.Valid t σ)
    (h : ¬ Belongs t ℓ σ) : distRS.resSetDeriv t {ℓ} σ = {ℓ} := by
  have hn : ℓ ∉ names σ := fun hmem => h ((belongs_names hℓ hσ).mpr hmem)
  rw [(residual_names (M := {ℓ}) (fun a ha => (Finset.mem_singleton.mp ha) ▸ hℓ) hσ).1]
  simp [hn]

/-- **Characterization of belonging**: for coinitial `R` and `σ`,
`R ∈ σ ⟺ R ⊑ σ ⟺ name(R) ∈ names(σ)`. -/
theorem characterization_of_belonging {ℓ : Label} {σ : List Label} (hℓ : distRS.isStep t ℓ)
    (hσ : distRS.Valid t σ) :
    [Belongs t ℓ σ, distRS.Prefix t [ℓ] σ, ℓ ∈ names σ].TFAE := by
  have h₁ := belongs_names hℓ hσ
  have h₂ : distRS.Prefix t [ℓ] σ ↔ ℓ ∈ names σ := by
    rw [prefix_names (ResidualSystem.valid_singleton hℓ) hσ]
    simp [names]
  tfae_have 1 ↔ 3 := h₁
  tfae_have 2 ↔ 3 := h₂
  tfae_finish

theorem names_append (σ τ : List Label) : names (σ ++ τ) = names σ ∪ names τ := by
  simp [names, List.toFinset_append]

/-- `names(στ) = names(σ) ⊎ names(τ)`. -/
theorem names_append_disjoint {σ τ : List Label} (h : distRS.Valid t (σ ++ τ)) :
    Disjoint (names σ) (names τ) := by
  have := (List.nodup_append.1 (nodup_of_valid h))
  rw [names, names, List.disjoint_toFinset_iff_disjoint]
  intro a ha hb
  exact this.2.2 a ha a hb rfl

/-- **The length of a derivation equals the number of distinct names along it.** -/
theorem length_eq_card_names {σ : List Label} (hσ : distRS.Valid t σ) :
    σ.length = (names σ).card :=
  (List.toFinset_card_of_nodup (nodup_of_valid hσ)).symm

/-- **Names after a projection**: `names(σ/τ) = names(σ) ∖ names(τ)`. -/
theorem names_proj {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    names (distRS.proj t σ τ) = names σ \ names τ := by
  exact names_proj_core hσ hτ

/-- **Prefixes as subsets**: `σ ⊑ τ ⟺ names(σ) ⊆ names(τ)`. -/
theorem prefix_iff_subset {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    distRS.Prefix t σ τ ↔ names σ ⊆ names τ := by
  exact prefix_names hσ hτ

/-- **Permutation equivalence in terms of names**: `σ ≡ τ ⟺ names(σ) = names(τ)`. -/
theorem permEq_iff_names {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    distRS.PermEq t σ τ ↔ names σ = names τ := by
  rw [ResidualSystem.PermEq, prefix_iff_subset hσ hτ, prefix_iff_subset hτ hσ,
    Finset.Subset.antisymm_iff]

/-! ## Creation and stability -/

/-- **Creation**: there are exactly three creation cases in λ^dist. -/
theorem creation {m n : Label} (h : Creates t m n) : CreationCase t.1 m n := by
  exact creation_core h

/-- **Stability**: if `R ≠ S` are coinitial and `R` creates `T`, then `R/S` creates
`T/(S/R)`. (With names: the step named `m` still creates `n` after the step named `k`.) -/
theorem basic_stability {m k n : Label} (hmk : m ≠ k) (hk : distRS.isStep t k)
    (h : Creates t m n) : Creates (distRS.contract t k) m n := by
  exact basic_stability_core hmk hk h

/-- **Full stability**: if `ρ₁` (after `σ`) and `ρ₂` (after `τ`) have a common residual `ρ₃`
after `σ ⊔ τ`, with `names σ ∩ names τ = ∅`, then they have a common ancestor `ρ₀`. -/
theorem full_stability {σ τ : List Label} {n₁ n₂ n₃ : Label} (hσ : distRS.Valid t σ)
    (hτ : distRS.Valid t τ) (hdisj : Disjoint (names σ) (names τ))
    (h₁ : distRS.isStep (distRS.tgt t σ) n₁) (h₂ : distRS.isStep (distRS.tgt t τ) n₂)
    (h₁₃ : distRS.resSetDeriv (distRS.tgt t σ) {n₁} (distRS.proj t τ σ) = {n₃})
    (h₂₃ : distRS.resSetDeriv (distRS.tgt t τ) {n₂} (distRS.proj t σ τ) = {n₃}) :
    ∃ n₀, distRS.isStep t n₀ ∧ distRS.resSetDeriv t {n₀} σ = {n₁} ∧
      distRS.resSetDeriv t {n₀} τ = {n₂} := by
  have he₁ : n₃ = n₁ := Finset.mem_singleton.mp
    (residual_subset _ _ _ (h₁₃.symm ▸ Finset.mem_singleton_self n₃))
  have he₂ : n₃ = n₂ := Finset.mem_singleton.mp
    (residual_subset _ _ _ (h₂₃.symm ▸ Finset.mem_singleton_self n₃))
  subst n₁
  subst n₂
  have hn := disjoint_available basic_stability hσ hτ hdisj h₁ h₂
  refine ⟨n₃, hn, ?_, ?_⟩
  · rw [(residual_names (M := {n₃}) (fun a ha => (Finset.mem_singleton.mp ha) ▸ hn) hσ).1]
    simp [step_not_names hσ h₁]
  · rw [(residual_names (M := {n₃}) (fun a ha => (Finset.mem_singleton.mp ha) ▸ hn) hτ).1]
    simp [step_not_names hτ h₂]

/-! ## Meets -/

/-- **Meet of derivations**: `σ ⊓ τ` is a greatest lower bound for the prefix order. -/
theorem meet_isGLB {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    distRS.Prefix t (meet t σ τ) σ ∧ distRS.Prefix t (meet t σ τ) τ ∧
      ∀ ρ, distRS.Valid t ρ → distRS.Prefix t ρ σ → distRS.Prefix t ρ τ →
        distRS.Prefix t ρ (meet t σ τ) := by
  have hh := meetAux_spec σ.length hσ hτ le_rfl
  have hv := meet_valid hσ hτ
  refine ⟨(prefix_names hv hσ).mpr (fun a ha => (Finset.mem_inter.mp (hh.1 ha)).1),
    (prefix_names hv hτ).mpr (fun a ha => (Finset.mem_inter.mp (hh.1 ha)).2), ?_⟩
  intro ρ hρ hρσ hρτ
  apply (prefix_names hρ hv).mpr
  exact hh.2 ρ hρ (fun a ha => Finset.mem_inter.mpr
    ⟨(prefix_names hρ hσ).mp hρσ ha, (prefix_names hρ hτ).mp hρτ ha⟩)

/-- **Names of join and meet** (1): `names(σ ⊔ τ) = names(σ) ∪ names(τ)`. -/
theorem names_join {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    names (distRS.join t σ τ) = names σ ∪ names τ := by
  rw [ResidualSystem.join, names_append, names_proj hτ hσ, Finset.union_sdiff_self_eq_union]

/-- **Names of join and meet** (2): `names(σ ⊓ τ) = names(σ) ∩ names(τ)`. -/
theorem names_meet {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    names (meet t σ τ) = names σ ∩ names τ := by
  exact meetAux_names basic_stability σ.length hσ hτ le_rfl

/-! ## The derivation space of a correct term is a distributive lattice -/

/-- `names` on permutation-equivalence classes. -/
def namesQ : distRS.DSpace t → Finset Label :=
  Quotient.lift (fun σ : distRS.DerivFrom t => names σ.1) fun σ τ h =>
    (permEq_iff_names σ.2 τ.2).1 h

@[simp] theorem namesQ_mk (σ : distRS.DerivFrom t) :
    namesQ (ResidualSystem.DSpace.mk σ) = names σ.1 := rfl

theorem namesQ_injective : Function.Injective (namesQ (t := t)) := by
  refine ResidualSystem.DSpace.ind fun σ => ResidualSystem.DSpace.ind fun τ => ?_
  intro h
  exact ResidualSystem.DSpace.mk_eq_mk.2 ((permEq_iff_names σ.2 τ.2).2 h)

/-- The meet as a derivation. -/
noncomputable def DerivFrom.meet (σ τ : distRS.DerivFrom t) : distRS.DerivFrom t :=
  ⟨Thesis.distRS.meet t σ.1 τ.1, meet_valid σ.2 τ.2⟩

noncomputable instance : Min (distRS.DSpace t) where
  min := Quotient.map₂ DerivFrom.meet fun σ σ' hσ τ τ' hτ => by
    change distRS.PermEq t (meet t σ.1 τ.1) (meet t σ'.1 τ'.1)
    rw [permEq_iff_names (meet_valid σ.2 τ.2) (meet_valid σ'.2 τ'.2), names_meet σ.2 τ.2,
      names_meet σ'.2 τ'.2, (permEq_iff_names σ.2 σ'.2).1 hσ, (permEq_iff_names τ.2 τ'.2).1 hτ]

theorem namesQ_le_iff {x y : distRS.DSpace t} : namesQ x ⊆ namesQ y ↔ x ≤ y := by
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  exact (prefix_iff_subset σ.2 τ.2).symm

theorem namesQ_sup (x y : distRS.DSpace t) : namesQ (x ⊔ y) = namesQ x ∪ namesQ y := by
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  exact names_join σ.2 τ.2

theorem namesQ_inf (x y : distRS.DSpace t) : namesQ (x ⊓ y) = namesQ x ∩ namesQ y := by
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  exact names_meet σ.2 τ.2

/-- **Theorem (derivations modulo `≡` form a distributive lattice).** For a correct term `t`,
`𝔻^dist(t)` is a distributive lattice, with `[σ] ∧ [τ] = [σ ⊓ τ]` and `[σ] ∨ [τ] = [σ ⊔ τ]`. -/
noncomputable instance instDistribLattice : DistribLattice (distRS.DSpace t) :=
  Function.Injective.distribLattice namesQ namesQ_injective
    (fun {_ _} => namesQ_le_iff)
    (fun {x y} => by
      rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
      exact and_congr namesQ_le_iff (not_congr namesQ_le_iff))
    namesQ_sup namesQ_inf

/-- **Theorem (the lattice of derivations is representable as a ring of sets).**
`names : 𝔻^dist(t) → 𝒫(ℒ)` is a monomorphism of lattices. -/
def namesHom : LatticeHom (distRS.DSpace t) (Finset Label) where
  toFun := namesQ
  map_sup' := namesQ_sup
  map_inf' := namesQ_inf

theorem namesHom_injective : Function.Injective (namesHom (t := t)) := namesQ_injective

theorem namesHom_mono : Monotone (namesHom (t := t)) := fun _ _ h => namesQ_le_iff.2 h

end distRS

/-- The derivation space `𝔻^dist(t)` of a correct term. -/
abbrev DSpaceDist (t : CTerm) : Type := distRS.DSpace t

end Thesis
