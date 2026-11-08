/-
# Chapter 5: Factorization of derivations

Fix a refinement `t' ⋉ t`. A λ-derivation is *garbage* if it is erased by simulation, and
*garbage-free* if no non-empty part of it is garbage. Every derivation factorizes uniquely as a
garbage-free prefix followed by garbage, and this glues into an isomorphism
`𝔻_λ(t) ≅ ∫_F G` with a Grothendieck construction.
-/
import Thesis.Chapter5FactorizationDefs
import Thesis.Chapter5FactorizationAppendix

namespace Thesis

open LTerm ResidualSystem

/-! ## 5.1 Garbage -/

section Garbage

variable {t : LTerm} {t' : CTerm} (hr : Refines t t'.1)
include hr

/-- **Properties of garbage** (the `t'`-garbage derivations form an ideal of `𝔻_λ(t)`).
(1) downwards closed. -/
theorem isGarbage_of_prefix {σ τ : List Pos} (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ)
    (h : IsGarbage t' σ) (hle : lambdaRS.Prefix t τ σ) : IsGarbage t' τ := by
  exact garbage_prefix_core hr hσ hτ h hle

omit hr in
/-- (2) `στ` is `t'`-garbage iff `σ` is `t'`-garbage and `τ` is `(t'/σ)`-garbage. -/
theorem isGarbage_append (σ τ : List Pos) :
    IsGarbage t' (σ ++ τ) ↔ IsGarbage t' σ ∧ IsGarbage (simTgtDeriv t' σ) τ := by
  simp [IsGarbage, simDeriv_append]

/-- (3) If `σ` is `t'`-garbage then `σ/τ` is `(t'/τ)`-garbage. -/
theorem isGarbage_proj {σ τ : List Pos} (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ)
    (h : IsGarbage t' σ) : IsGarbage (simTgtDeriv t' τ) (lambdaRS.proj t σ τ) := by
  exact garbage_proj_core hr hσ hτ h

/-- (4) `σ ⊔ τ` is garbage iff `σ` and `τ` are. -/
theorem isGarbage_join {σ τ : List Pos} (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) :
    IsGarbage t' (lambdaRS.join t σ τ) ↔ IsGarbage t' σ ∧ IsGarbage t' τ := by
  exact garbage_join_core hr hσ hτ

/-- Garbage is well defined modulo permutation equivalence. -/
theorem isGarbage_congr {σ τ : List Pos} (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ)
    (h : lambdaRS.PermEq t σ τ) : IsGarbage t' σ ↔ IsGarbage t' τ := by
  exact garbage_congr_core hr hσ hτ h

end Garbage

/-- **Garbage-freeness is well defined modulo permutation equivalence.** -/
theorem garbageFree_congr {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) (h : lambdaRS.PermEq t σ τ) :
    GarbageFree t t' σ ↔ GarbageFree t t' τ := by
  have forward : ∀ σ τ, lambdaRS.Valid t σ → lambdaRS.Valid t τ →
      lambdaRS.PermEq t σ τ → GarbageFree t t' σ → GarbageFree t t' τ := by
    intro σ τ hσ hτ he hg ρ hρ hρτ hgar
    have hρσ := prefix_trans lambda_orthogonal hρ hτ hσ hρτ he.2
    have hh : lambdaRS.PermEq (lambdaRS.tgt t ρ) (lambdaRS.proj t σ ρ) (lambdaRS.proj t τ ρ) :=
      ⟨prefix_proj lambda_orthogonal hσ hτ hρ he.1,
        prefix_proj lambda_orthogonal hτ hσ hρ he.2⟩
    have hvσ := proj_valid lambda_orthogonal hσ hρ
    have hvτ := proj_valid lambda_orthogonal hτ hρ
    have hgs := (garbage_congr_core (simDeriv_valid hr hρ).2 hvσ hvτ hh).mpr hgar
    have hz := hg ρ hρ hρσ hgs
    have hp := hh.2
    unfold Prefix at hp
    rw [hz, proj_nil_right lambda_orthogonal hvτ] at hp
    exact hp
  exact ⟨forward σ τ hσ hτ h, forward τ σ hτ hσ ⟨h.2, h.1⟩⟩

/-! ## 5.2 Sieving -/

/-- **Sieving is well defined**: the measure `|σ/t'|` strictly decreases at each recursive call,
so any fuel `≥ |σ/t'|` gives the same result. -/
theorem sieving_is_well_defined {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (n : ℕ) (hn : (simDeriv t' σ).length ≤ n) :
    sieveAux n t t' σ = sieve t t' σ := by
  exact sieveAux_fuel_eq hr hσ n _ hn le_rfl

/-- **Sieving is compatible with permutation equivalence.** -/
theorem sieve_congr {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) (h : lambdaRS.PermEq t σ τ) :
    lambdaRS.PermEq t (sieve t t' σ) (sieve t t' τ) := by
  rw [sieve_eq_of_permEq hr hσ hτ h]
  exact ⟨prefix_refl lambda_orthogonal (sieve_valid hr hτ),
    prefix_refl lambda_orthogonal (sieve_valid hr hτ)⟩

/-! ## 5.3 Some properties -/

/-- **Garbage only creates garbage.** -/
theorem garbage_only_creates_garbage {t : LTerm} {t' : CTerm} {p q : Pos} (hr : Refines t t'.1)
    (hc : LCreates t p q) (hg : IsGarbage t' [p]) : IsGarbage (simTgt t' p) [q] := by
  exact garbage_creates_core hr hc hg

/-- **Garbage only duplicates garbage**: if `R` duplicates `S` (`#(S/R) > 1`) and `R` is
garbage, then `S` is garbage. -/
theorem garbage_only_duplicates_garbage {t : LTerm} {t' : CTerm} {p q : Pos}
    (hr : Refines t t'.1) (hp : lambdaRS.isStep t p) (hq : lambdaRS.isStep t q)
    (hdup : 1 < (lambdaRS.res t p q).card) (hg : IsGarbage t' [p]) : IsGarbage t' [q] := by
  exact garbage_duplicates_core hr hp hdup hg

/-- **Characterization of garbage**: TFAE `σ ⇂ t' = ε`; there are no coarse steps for `(σ, t')`;
`σ` is `t'`-garbage. -/
theorem characterization_of_garbage {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) :
    [sieve t t' σ = [], ∀ p, ¬ Coarse t t' σ p, IsGarbage t' σ].TFAE := by
  tfae_have 1 ↔ 2 := sieve_eq_nil_iff hr hσ
  tfae_have 2 → 3 := by
    intro h
    by_contra hg
    obtain ⟨a, ha⟩ := exists_coarse_of_not_garbage σ hr hσ hg
    exact h a ha
  tfae_have 3 → 2 := by
    intro hg p hp
    have h2 := (sim_singleton_garbage t' p).mp
      (garbage_prefix_core hr hσ (valid_singleton hp.1) hg hp.2.1)
    exact (Finset.nonempty_iff_ne_empty.mp hp.2.2) h2
  tfae_finish

/-- The sieve is a prefix. -/
theorem sieve_prefix {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) : lambdaRS.Prefix t (sieve t t' σ) σ :=
  sieveAux_prefix _ hr hσ

/-- **The sieve is garbage-free.**  The sieve is the least prefix covering all the names
(`sieve_least`, which rests on the positional invariant of `leftmost_least`). -/
theorem sieve_garbageFree {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) : GarbageFree t t' (sieve t t' σ) := by
  intro ρ hρ hpre hgar
  have hs := sieve_valid hr hσ
  have hle : lambdaRS.Prefix t ρ σ :=
    prefix_trans lambda_orthogonal hρ hs hσ hpre (sieve_prefix hr hσ)
  have e := gen_names ρ (sieve t t' σ) hr hs hρ
  have hemp : simDeriv (simTgtDeriv t' ρ) (lambdaRS.proj t (sieve t t' σ) ρ) = [] := hgar
  rw [hemp] at e
  have hsub : distRS.names (simDeriv t' (sieve t t' σ)) ⊆ distRS.names (simDeriv t' ρ) := by
    intro ℓ hℓ
    by_contra hn
    have : ℓ ∈ distRS.names (simDeriv t' (sieve t t' σ)) \ distRS.names (simDeriv t' ρ) :=
      Finset.mem_sdiff.mpr ⟨hℓ, hn⟩
    rw [← e] at this
    simp [distRS.names] at this
  exact sieve_least hr hσ hρ hle ((names_subset_sieve hr hσ).trans hsub)

/-- The projection after a sieve is garbage. -/
theorem projection_after_sieve_garbage {t : LTerm} {t' : CTerm} {σ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) :
    IsGarbage (simTgtDeriv t' (sieve t t' σ)) (lambdaRS.proj t σ (sieve t t' σ)) :=
  projection_after_sieveAux_garbage _ hr hσ le_rfl

/-- **Characterization of garbage-free derivations**: TFAE `σ` is `t'`-garbage-free;
`σ ≡ σ ⇂ t'`; `σ ≡ τ ⇂ t'` for some `τ`. -/
theorem characterization_of_garbageFree {t : LTerm} {t' : CTerm} {σ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) :
    [GarbageFree t t' σ, lambdaRS.PermEq t σ (sieve t t' σ),
     ∃ τ, lambdaRS.Valid t τ ∧ lambdaRS.PermEq t σ (sieve t t' τ)].TFAE := by
  tfae_have 1 → 2 := by
    intro hg
    have hs := sieve_valid hr hσ
    have hz := hg _ hs (sieve_prefix hr hσ) (projection_after_sieve_garbage hr hσ)
    exact ⟨hz, sieve_prefix hr hσ⟩
  tfae_have 2 → 3 := fun h => ⟨σ, hσ, h⟩
  tfae_have 3 → 1 := by
    rintro ⟨τ, hτ, h⟩
    exact (garbageFree_congr hr hσ (sieve_valid hr hτ) h).mpr (sieve_garbageFree hr hτ)
  tfae_finish

/-- **Properties of sieving.** -/
theorem properties_of_sieving {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) :
    (GarbageFree t t' (sieve t t' σ) ∧ lambdaRS.Prefix t (sieve t t' σ) σ) ∧
      IsGarbage (simTgtDeriv t' (sieve t t' σ)) (lambdaRS.proj t σ (sieve t t' σ)) ∧
      (IsGarbage t' σ ↔ sieve t t' σ = []) ∧
      (GarbageFree t t' σ ↔ lambdaRS.PermEq t (sieve t t' σ) σ) := by
  have h1 : IsGarbage t' σ ↔ sieve t t' σ = [] := (characterization_of_garbage hr hσ).out 3 1
  have h2 : GarbageFree t t' σ ↔ lambdaRS.PermEq t σ (sieve t t' σ) :=
    (characterization_of_garbageFree hr hσ).out 1 2
  refine ⟨⟨sieve_garbageFree hr hσ, sieve_prefix hr hσ⟩, projection_after_sieve_garbage hr hσ,
    h1, ?_⟩
  rw [h2]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ## 5.4 Factorization of garbage -/

/-- **Sieving trailing garbage** (up to permutation equivalence). -/
theorem sieve_trailing_garbage {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid (lambdaRS.tgt t σ) τ)
    (hg : IsGarbage (simTgtDeriv t' σ) τ) :
    lambdaRS.PermEq t (sieve t t' (σ ++ τ)) (sieve t t' σ) := by
  have hω : lambdaRS.Valid t (σ ++ τ) := (lambdaRS.valid_append _ _ _).2 ⟨hσ, hτ⟩
  have hs1 := sieve_valid hr hσ
  have hs2 := sieve_valid hr hω
  have hσω : lambdaRS.Prefix t σ (σ ++ τ) :=
    (prefix_iff_exists lambda_orthogonal hσ hω).2 ⟨τ, hτ, prefix_refl lambda_orthogonal hω,
      prefix_refl lambda_orthogonal hω⟩
  have hN : distRS.names (simDeriv t' (σ ++ τ)) = distRS.names (simDeriv t' σ) := by
    rw [simNames_append]
    have : simDeriv (simTgtDeriv t' σ) τ = [] := hg
    rw [this]
    simp [distRS.names]
  have h1 : lambdaRS.Prefix t (sieve t t' (σ ++ τ)) (sieve t t' σ) :=
    sieve_least hr hω hs1 (prefix_trans lambda_orthogonal hs1 hσ hω (sieve_prefix hr hσ) hσω)
      (by rw [hN]; exact names_subset_sieve hr hσ)
  have h2 : lambdaRS.Prefix t (sieve t t' (σ ++ τ)) σ :=
    sieve_least hr hω hσ hσω (by rw [hN])
  have h3 : lambdaRS.Prefix t (sieve t t' σ) (sieve t t' (σ ++ τ)) :=
    sieve_least hr hσ hs2 h2 (by rw [← hN]; exact names_subset_sieve hr hω)
  exact ⟨h1, h3⟩

/-- **Theorem (simple factorization of garbage).** Every `σ` factorizes as `σ ≡ σ₁σ₂` with `σ₁`
`t'`-garbage-free and `σ₂` `(t'/σ₁)`-garbage; the factorization is unique modulo `≡`, with
`σ₁ ≡ σ ⇂ t'` and `σ₂ ≡ σ/(σ ⇂ t')`. -/
theorem simple_factorization {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) :
    (∃ σ₁ σ₂, lambdaRS.Valid t σ₁ ∧ lambdaRS.Valid (lambdaRS.tgt t σ₁) σ₂ ∧
      lambdaRS.PermEq t σ (σ₁ ++ σ₂) ∧ GarbageFree t t' σ₁ ∧
      IsGarbage (simTgtDeriv t' σ₁) σ₂) ∧
    ∀ σ₁ σ₂, lambdaRS.Valid t σ₁ → lambdaRS.Valid (lambdaRS.tgt t σ₁) σ₂ →
      lambdaRS.PermEq t σ (σ₁ ++ σ₂) → GarbageFree t t' σ₁ →
      IsGarbage (simTgtDeriv t' σ₁) σ₂ →
      lambdaRS.PermEq t σ₁ (sieve t t' σ) ∧
        lambdaRS.PermEq (lambdaRS.tgt t σ₁) σ₂ (lambdaRS.proj t σ (sieve t t' σ)) := by
  have hs := sieve_valid hr hσ
  constructor
  · refine ⟨sieve t t' σ, lambdaRS.proj t σ (sieve t t' σ), hs,
      proj_valid lambda_orthogonal hσ hs, ?_, sieve_garbageFree hr hσ,
      projection_after_sieve_garbage hr hσ⟩
    have hh := permGen_join_comm lambda_orthogonal hs hσ
    have hle : lambdaRS.proj t (sieve t t' σ) σ = [] := sieve_prefix hr hσ
    simp only [ResidualSystem.join, hle, List.append_nil] at hh
    have := (permGen_iff_permEq lambda_orthogonal (hh.valid_left lambda_orthogonal)
      (hh.valid_right lambda_orthogonal)).mp hh
    exact ⟨this.2, this.1⟩
  · intro σ₁ σ₂ h1 h2 hperm hgf hgar
    have hτ : lambdaRS.Valid t (σ₁ ++ σ₂) := (lambdaRS.valid_append _ _ _).mpr ⟨h1, h2⟩
    have hseq : sieve t t' σ = sieve t t' (σ₁ ++ σ₂) := sieve_eq_of_permEq hr hσ hτ hperm
    have htr := sieve_trailing_garbage hr h1 h2 hgar
    have hA : lambdaRS.PermEq t σ₁ (sieve t t' σ) := by
      rw [hseq]
      have e := (characterization_of_garbageFree hr h1).out 1 2 |>.mp hgf
      exact permEq_trans' h1 (sieve_valid hr h1) (sieve_valid hr hτ) e ⟨htr.2, htr.1⟩
    refine ⟨hA, ?_⟩
    -- σ₂ ≡ (σ₁σ₂)/σ₁ and σ/σ₁ ≡ (σ₁σ₂)/σ₁
    have hp1 : lambdaRS.proj t (σ₁ ++ σ₂) σ₁ = σ₂ := by
      rw [proj_append_left lambda_orthogonal hτ h1, proj_self lambda_orthogonal h1,
        List.nil_append, proj_nil_right lambda_orthogonal h2]
    have hq : lambdaRS.PermEq (lambdaRS.tgt t σ₁) (lambdaRS.proj t σ σ₁)
        (lambdaRS.proj t (σ₁ ++ σ₂) σ₁) :=
      ⟨prefix_proj lambda_orthogonal hσ hτ h1 hperm.1, prefix_proj lambda_orthogonal hτ hσ h1 hperm.2⟩
    rw [hp1] at hq
    rw [← proj_congr_permEq lambda_orthogonal h1 hs hσ hA]
    exact ⟨hq.2, hq.1⟩

/-- Transitivity core of the order of `𝔽`: if `σ/τ` is `(t'/τ)`-garbage and `τ/ρ` is
`(t'/ρ)`-garbage then `σ/ρ` is `(t'/ρ)`-garbage. -/
theorem gf_le_trans_core {t : LTerm} {t' : CTerm} {σ τ ρ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) (hρ : lambdaRS.Valid t ρ)
    (h1 : IsGarbage (simTgtDeriv t' τ) (lambdaRS.proj t σ τ))
    (h2 : IsGarbage (simTgtDeriv t' ρ) (lambdaRS.proj t τ ρ)) :
    IsGarbage (simTgtDeriv t' ρ) (lambdaRS.proj t σ ρ) := by
  have hA : lambdaRS.Valid (lambdaRS.tgt t τ) (lambdaRS.proj t σ τ) :=
    proj_valid lambda_orthogonal hσ hτ
  have hC : lambdaRS.Valid (lambdaRS.tgt t τ) (lambdaRS.proj t ρ τ) :=
    proj_valid lambda_orthogonal hρ hτ
  have hB : lambdaRS.Valid (lambdaRS.tgt t ρ) (lambdaRS.proj t τ ρ) :=
    proj_valid lambda_orthogonal hτ hρ
  have hτA : lambdaRS.Valid t (τ ++ lambdaRS.proj t σ τ) := (lambdaRS.valid_append _ _ _).2 ⟨hτ, hA⟩
  have hρB : lambdaRS.Valid t (ρ ++ lambdaRS.proj t τ ρ) := (lambdaRS.valid_append _ _ _).2 ⟨hρ, hB⟩
  have hτC : lambdaRS.Valid t (τ ++ lambdaRS.proj t ρ τ) := (lambdaRS.valid_append _ _ _).2 ⟨hτ, hC⟩
  have hle : lambdaRS.Prefix t σ (τ ++ lambdaRS.proj t σ τ) :=
    prefix_join_right lambda_orthogonal hτ hσ
  have hpre := prefix_proj lambda_orthogonal hσ hτA hρ hle
  have hexp := proj_append_left lambda_orthogonal hτA hρ
  have hrρ : Refines (lambdaRS.tgt t ρ) (simTgtDeriv t' ρ).1 := (simDeriv_valid hr hρ).2
  have hrτ : Refines (lambdaRS.tgt t τ) (simTgtDeriv t' τ).1 := (simDeriv_valid hr hτ).2
  have hg3 := isGarbage_proj hrτ hA hC h1
  have hcomm := permGen_join_comm lambda_orthogonal hτ hρ
  have hperm := (permGen_iff_permEq lambda_orthogonal (hcomm.valid_left lambda_orthogonal)
    (hcomm.valid_right lambda_orthogonal)).1 hcomm
  have heq := (compatibility hr hτC hρB hperm).1
  rw [simTgtDeriv_append, simTgtDeriv_append] at heq
  have hgarb : IsGarbage (simTgtDeriv t' ρ)
      (lambdaRS.proj t τ ρ ++ lambdaRS.proj (lambdaRS.tgt t τ) (lambdaRS.proj t σ τ)
        (lambdaRS.proj t ρ τ)) :=
    (isGarbage_append _ _).2 ⟨h2, by rw [← heq]; exact hg3⟩
  rw [← hexp] at hgarb
  exact isGarbage_of_prefix hrρ (proj_valid lambda_orthogonal hτA hρ) (proj_valid lambda_orthogonal hσ hρ)
    hgarb hpre

/-- `[σ] ≤𝔽 [τ]` on garbage-free derivations with mutual garbage gives permutation equivalence. -/
theorem gf_antisymm_core {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) (hgσ : GarbageFree t t' σ)
    (hgτ : GarbageFree t t' τ)
    (h1 : IsGarbage (simTgtDeriv t' τ) (lambdaRS.proj t σ τ))
    (h2 : IsGarbage (simTgtDeriv t' σ) (lambdaRS.proj t τ σ)) : lambdaRS.PermEq t σ τ := by
  have e1 := ((characterization_of_garbageFree hr hσ).out 1 2).mp hgσ
  have e2 := ((characterization_of_garbageFree hr hτ).out 1 2).mp hgτ
  have hA : lambdaRS.Valid (lambdaRS.tgt t σ) (lambdaRS.proj t τ σ) :=
    proj_valid lambda_orthogonal hτ hσ
  have hB : lambdaRS.Valid (lambdaRS.tgt t τ) (lambdaRS.proj t σ τ) :=
    proj_valid lambda_orthogonal hσ hτ
  have hv1 : lambdaRS.Valid t (σ ++ lambdaRS.proj t τ σ) := (lambdaRS.valid_append _ _ _).2 ⟨hσ, hA⟩
  have hv2 : lambdaRS.Valid t (τ ++ lambdaRS.proj t σ τ) := (lambdaRS.valid_append _ _ _).2 ⟨hτ, hB⟩
  have hcomm := permGen_join_comm lambda_orthogonal hσ hτ
  have hperm := (permGen_iff_permEq lambda_orthogonal (hcomm.valid_left lambda_orthogonal)
    (hcomm.valid_right lambda_orthogonal)).1 hcomm
  have s1 := sieve_trailing_garbage hr hσ hA h2
  have s2 := sieve_trailing_garbage hr hτ hB h1
  have s3 := sieve_eq_of_permEq hr hv1 hv2 hperm
  have hvs1 := sieve_valid hr hσ
  have hvs2 := sieve_valid hr hτ
  rw [s3] at s1
  -- σ ≡ sieve σ ≡ sieve (τ ++ ·) ≡ sieve τ ≡ τ
  have hvs3 := sieve_valid hr hv2
  have hst : lambdaRS.PermEq t (sieve t t' σ) (sieve t t' τ) :=
    permEq_trans' hvs1 hvs3 hvs2 ⟨s1.2, s1.1⟩ s2
  have e1' := permEq_trans' hσ hvs1 hvs2 e1 hst
  exact permEq_trans' hσ hvs2 hτ e1' ⟨e2.2, e2.1⟩

/-! ## 5.5 Lattices: the factorization theorem -/

section Factorization

variable {t : LTerm} {t' : CTerm} (hr : Refines t t'.1)

/-- Garbage-freeness on classes. -/
def GarbageFreeQ : DSpaceLam t → Prop :=
  Quotient.lift (fun σ : LDeriv t => GarbageFree t t' σ.1) fun σ τ h =>
    propext (garbageFree_congr hr σ.2 τ.2 h)

/-- `𝔽 = 𝔽(t' ⋉ t)`: the garbage-free derivations modulo `≡`. -/
structure GF where
  val : DSpaceLam t
  garbageFree : GarbageFreeQ hr val

/-- The order of `𝔽`: `[σ] ≤𝔽 [τ]` iff `σ/τ` is `(t'/τ)`-garbage. -/
def GF.le (x y : GF hr) : Prop :=
  Quotient.lift₂ (fun σ τ : LDeriv t =>
      IsGarbage (simTgtDeriv t' τ.1) (lambdaRS.proj t σ.1 τ.1))
    (fun σ τ σ' τ' hσ hτ => by
      have hc := (compatibility hr τ.2 τ'.2 hτ).1
      have h1 : lambdaRS.proj t σ.1 τ.1 = lambdaRS.proj t σ.1 τ'.1 :=
        proj_congr_permEq lambda_orthogonal τ.2 τ'.2 σ.2 hτ
      have hh : lambdaRS.PermEq (lambdaRS.tgt t τ'.1) (lambdaRS.proj t σ.1 τ'.1)
          (lambdaRS.proj t σ'.1 τ'.1) :=
        ⟨prefix_proj lambda_orthogonal σ.2 σ'.2 τ'.2 hσ.1,
          prefix_proj lambda_orthogonal σ'.2 σ.2 τ'.2 hσ.2⟩
      apply propext
      rw [hc, h1]
      exact garbage_congr_core (simDeriv_valid hr τ'.2).2
        (proj_valid lambda_orthogonal σ.2 τ'.2) (proj_valid lambda_orthogonal σ'.2 τ'.2) hh) x.val y.val

/-- **Proposition (semilattices of garbage-free and garbage derivations)** (1): `𝔽` is a
finite lattice, with `[σ] ∨𝔽 [τ] = [(σ ⊔ τ) ⇂ t']`. (The partial-order laws are proved in the
appendix of the thesis via the properties of garbage and sieving.) -/
theorem GF.le_mk (σ τ : LDeriv t) (hσ hτ) :
    GF.le hr ⟨ResidualSystem.DSpace.mk σ, hσ⟩ ⟨ResidualSystem.DSpace.mk τ, hτ⟩ ↔
      IsGarbage (simTgtDeriv t' τ.1) (lambdaRS.proj t σ.1 τ.1) := Iff.rfl

instance GF.instPartialOrder : PartialOrder (GF hr) where
  le := GF.le hr
  le_refl := by
    rintro ⟨x, hx⟩
    induction x using ResidualSystem.DSpace.ind with | h σ => ?_
    refine (GF.le_mk hr σ σ hx hx).2 ?_
    rw [proj_self lambda_orthogonal σ.2]
    rfl
  le_trans := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    induction x using ResidualSystem.DSpace.ind with | h σ => ?_
    induction y using ResidualSystem.DSpace.ind with | h τ => ?_
    induction z using ResidualSystem.DSpace.ind with | h ρ => ?_
    intro h1 h2
    exact (GF.le_mk hr σ ρ hx hz).2 (gf_le_trans_core hr σ.2 τ.2 ρ.2
      ((GF.le_mk hr σ τ hx hy).1 h1) ((GF.le_mk hr τ ρ hy hz).1 h2))
  le_antisymm := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    induction x using ResidualSystem.DSpace.ind with | h σ => ?_
    induction y using ResidualSystem.DSpace.ind with | h τ => ?_
    intro h1 h2
    have := gf_antisymm_core hr σ.2 τ.2 hx hy ((GF.le_mk hr σ τ hx hy).1 h1)
      ((GF.le_mk hr τ σ hy hx).1 h2)
    have hm : ResidualSystem.DSpace.mk σ = ResidualSystem.DSpace.mk τ :=
      ResidualSystem.DSpace.mk_eq_mk.2 this
    exact (GF.mk.injEq _ _ _ _).mpr hm

theorem GF.finite : Finite (GF hr) := by
  let g : DSpaceLam t → List Pos :=
    Quotient.lift (fun σ : LDeriv t => sieve t t' σ.1) fun σ τ h => sieve_eq_of_permEq hr σ.2 τ.2 h
  have hg : ∀ x : DSpaceLam t, lambdaRS.Valid t (g x) ∧ (g x).length ≤ t'.1.size := by
    intro x
    induction x using ResidualSystem.DSpace.ind with | h σ => ?_
    refine ⟨sieve_valid hr σ.2, ?_⟩
    have h1 : (sieve t t' σ.1).length ≤ (simDeriv t' σ.1).length :=
      sieveAux_length_le _ hr σ.2
    have h2 := dist_length_add_size (simDeriv t' σ.1) t' (simDeriv_valid hr σ.2).1
    change (sieve t t' σ.1).length ≤ _
    omega
  have hfin := (valid_length_finite t'.1.size t).to_subtype
  refine Finite.of_injective
    (fun x : GF hr => (⟨g x.val, hg x.val⟩ : {s : List Pos | lambdaRS.Valid t s ∧
      s.length ≤ t'.1.size})) ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  have hxy' : g x = g y := congrArg Subtype.val hxy
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  have e1 := ((characterization_of_garbageFree hr σ.2).out 1 2).mp hx
  have e2 := ((characterization_of_garbageFree hr τ.2).out 1 2).mp hy
  change sieve t t' σ.1 = sieve t t' τ.1 at hxy'
  rw [hxy'] at e1
  have hm : ResidualSystem.DSpace.mk σ = ResidualSystem.DSpace.mk τ :=
    ResidualSystem.DSpace.mk_eq_mk.2
      ⟨prefix_trans lambda_orthogonal σ.2 (sieve_valid hr τ.2) τ.2 e1.1 e2.2,
       prefix_trans lambda_orthogonal τ.2 (sieve_valid hr τ.2) σ.2 e2.1 e1.2⟩
  exact (GF.mk.injEq _ _ _ _).mpr hm

theorem GF.isLUB_sieve (σ τ : LDeriv t) (hx : GarbageFreeQ hr (ResidualSystem.DSpace.mk σ))
    (hy : GarbageFreeQ hr (ResidualSystem.DSpace.mk τ)) :
    ∃ hz : GarbageFreeQ hr (ResidualSystem.DSpace.mk (⟨sieve t t' (lambdaRS.join t σ.1 τ.1),
        sieve_valid hr ((lambdaRS.valid_append _ _ _).2
          ⟨σ.2, proj_valid lambda_orthogonal τ.2 σ.2⟩)⟩ : LDeriv t)),
      IsLUB {(⟨ResidualSystem.DSpace.mk σ, hx⟩ : GF hr), ⟨ResidualSystem.DSpace.mk τ, hy⟩}
        (⟨ResidualSystem.DSpace.mk (⟨sieve t t' (lambdaRS.join t σ.1 τ.1),
          sieve_valid hr ((lambdaRS.valid_append _ _ _).2
            ⟨σ.2, proj_valid lambda_orthogonal τ.2 σ.2⟩)⟩ : LDeriv t), hz⟩ : GF hr) := by
  have hj : lambdaRS.Valid t (lambdaRS.join t σ.1 τ.1) :=
    (lambdaRS.valid_append _ _ _).2 ⟨σ.2, proj_valid lambda_orthogonal τ.2 σ.2⟩
  have hs := sieve_valid hr hj
  have hrs : Refines (lambdaRS.tgt t (sieve t t' (lambdaRS.join t σ.1 τ.1)))
      (simTgtDeriv t' (sieve t t' (lambdaRS.join t σ.1 τ.1))).1 := (simDeriv_valid hr hs).2
  have hgar := projection_after_sieve_garbage hr hj
  refine ⟨sieve_garbageFree hr hj, ?_, ?_⟩
  · rintro w (rfl | rfl)
    · refine (GF.le_mk hr _ _ _ _).2 ?_
      exact isGarbage_of_prefix hrs (proj_valid lambda_orthogonal hj hs)
        (proj_valid lambda_orthogonal σ.2 hs) hgar
        (prefix_proj lambda_orthogonal σ.2 hj hs (prefix_join_left lambda_orthogonal σ.2 τ.2))
    · refine (GF.le_mk hr _ _ _ _).2 ?_
      exact isGarbage_of_prefix hrs (proj_valid lambda_orthogonal hj hs)
        (proj_valid lambda_orthogonal τ.2 hs) hgar
        (prefix_proj lambda_orthogonal τ.2 hj hs (prefix_join_right lambda_orthogonal σ.2 τ.2))
  · rintro ⟨w, hw⟩ hub
    induction w using ResidualSystem.DSpace.ind with | h ρ => ?_
    have h1 := (GF.le_mk hr σ ρ hx hw).1 (hub (Set.mem_insert _ _))
    have h2 := (GF.le_mk hr τ ρ hy hw).1 (hub (Set.mem_insert_of_mem _ rfl))
    refine (GF.le_mk hr _ _ _ _).2 ?_
    have hrρ : Refines (lambdaRS.tgt t ρ.1) (simTgtDeriv t' ρ.1).1 := (simDeriv_valid hr ρ.2).2
    have hpσ := proj_valid lambda_orthogonal σ.2 ρ.2
    have hpτ := proj_valid lambda_orthogonal τ.2 ρ.2
    have hjg : IsGarbage (simTgtDeriv t' ρ.1) (lambdaRS.proj t (lambdaRS.join t σ.1 τ.1) ρ.1) := by
      have hpj := proj_join lambda_orthogonal σ.2 τ.2 ρ.2
      exact (isGarbage_congr hrρ (proj_valid lambda_orthogonal hj ρ.2)
        ((lambdaRS.valid_append _ _ _).2 ⟨hpσ, proj_valid lambda_orthogonal hpτ hpσ⟩) hpj).2
          ((isGarbage_join hrρ hpσ hpτ).2 ⟨h1, h2⟩)
    exact isGarbage_of_prefix hrρ (proj_valid lambda_orthogonal hj ρ.2)
      (proj_valid lambda_orthogonal hs ρ.2) hjg
      (prefix_proj lambda_orthogonal hs hj ρ.2 (sieve_prefix hr hj))

theorem GF.exists_sup (x y : GF hr) : ∃ z, IsLUB {x, y} z := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  obtain ⟨hz, h⟩ := GF.isLUB_sieve hr σ τ hx hy
  exact ⟨_, h⟩

noncomputable instance GF.instSemilatticeSup : SemilatticeSup (GF hr) where
  sup x y := Classical.choose (GF.exists_sup hr x y)
  le_sup_left x y := (Classical.choose_spec (GF.exists_sup hr x y)).1 (by simp)
  le_sup_right x y := (Classical.choose_spec (GF.exists_sup hr x y)).1 (by simp)
  sup_le x y z hx hy := (Classical.choose_spec (GF.exists_sup hr x y)).2 (by
    rintro w (rfl | rfl) <;> assumption)

/-- The bottom of `𝔽` is the class of the empty derivation. -/
instance GF.instOrderBot : OrderBot (GF hr) where
  bot := ⟨ResidualSystem.DSpace.mk (⟨[], trivial⟩ : LDeriv t),
    fun ρ _ _ _ => rfl⟩
  bot_le := by
    rintro ⟨x, hx⟩
    induction x using ResidualSystem.DSpace.ind with | h σ => ?_
    exact (GF.le_mk hr _ _ _ _).2 rfl

theorem GF.exists_inf (x y : GF hr) : ∃ z, IsGLB {x, y} z := by
  classical
  haveI : Finite (GF hr) := GF.finite hr
  let L : Set (GF hr) := {z | z ≤ x ∧ z ≤ y}
  have hLf : L.Finite := Set.toFinite L
  refine ⟨hLf.toFinset.sup id, ?_, ?_⟩
  · rintro c (rfl | rfl)
    · exact Finset.sup_le fun b hb => ((Set.Finite.mem_toFinset hLf).1 hb).1
    · exact Finset.sup_le fun b hb => ((Set.Finite.mem_toFinset hLf).1 hb).2
  · intro b hb
    exact Finset.le_sup (f := id)
      ((Set.Finite.mem_toFinset hLf).2 ⟨hb (Set.mem_insert _ _), hb (Set.mem_insert_of_mem _ rfl)⟩)

noncomputable instance GF.instLattice : Lattice (GF hr) :=
  { GF.instSemilatticeSup hr with
    inf := fun x y => Classical.choose (GF.exists_inf hr x y)
    inf_le_left := fun x y => (Classical.choose_spec (GF.exists_inf hr x y)).1 (by simp)
    inf_le_right := fun x y => (Classical.choose_spec (GF.exists_inf hr x y)).1 (by simp)
    le_inf := fun x y z hx hy => (Classical.choose_spec (GF.exists_inf hr y z)).2 (by
      rintro w (rfl | rfl) <;> assumption) }

/-- The join of `𝔽` is given by sieving the join. -/
theorem GF.sup_eq (σ τ : LDeriv t) (hσ hτ) :
    (⟨DSpace.mk σ, hσ⟩ ⊔ ⟨DSpace.mk τ, hτ⟩ : GF hr).val =
      DSpace.mk ⟨sieve t t' (lambdaRS.join t σ.1 τ.1), sieve_valid hr
        ((lambdaRS.valid_append _ _ _).2 ⟨σ.2, proj_valid lambda_orthogonal τ.2 σ.2⟩)⟩ := by
  obtain ⟨hz, h⟩ := GF.isLUB_sieve hr σ τ hσ hτ
  have h2 : IsLUB {(⟨DSpace.mk σ, hσ⟩ : GF hr), ⟨DSpace.mk τ, hτ⟩}
      (⟨DSpace.mk σ, hσ⟩ ⊔ ⟨DSpace.mk τ, hτ⟩ : GF hr) := by
    constructor
    · rintro w (rfl | rfl)
      · exact le_sup_left
      · exact le_sup_right
    · intro w hw
      exact sup_le (hw (Set.mem_insert _ _)) (hw (Set.mem_insert_of_mem _ rfl))
  exact congrArg GF.val (h2.unique h)

theorem rep_spec {u : LTerm} (x : DSpaceLam u) : DSpace.mk (rep x) = x := Quotient.out_eq x

/-- Garbage-ness on classes of derivations out of `u`. -/
def GarbageQ {u : LTerm} {u' : CTerm} (hu : Refines u u'.1) : DSpaceLam u → Prop :=
  Quotient.lift (fun σ : LDeriv u => IsGarbage u' σ.1)
    fun σ τ h => propext (isGarbage_congr hu σ.2 τ.2 h)

/-- `𝔾(u, u')`: the `u'`-garbage derivations out of `u`, modulo `≡`, with the order inherited
from `𝔻_λ(u)` (`Proposition` (2): an upper semilattice). -/
def GSpace {u : LTerm} {u' : CTerm} (hu : Refines u u'.1) : Type :=
  {x : DSpaceLam u // GarbageQ hu x}

noncomputable instance {u : LTerm} {u' : CTerm} (hu : Refines u u'.1) : PartialOrder (GSpace hu) :=
  inferInstanceAs (PartialOrder {x : DSpaceLam u // GarbageQ hu x})

theorem GarbageQ.sup {u : LTerm} {u' : CTerm} {hu : Refines u u'.1} {x y : DSpaceLam u}
    (hx : GarbageQ hu x) (hy : GarbageQ hu y) : GarbageQ hu (x ⊔ y) := by
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  rw [ResidualSystem.DSpace.mk_sup_mk]
  exact (isGarbage_join hu σ.2 τ.2).2 ⟨hx, hy⟩

/-- The garbage derivations form an upper semilattice. -/
noncomputable instance {u : LTerm} {u' : CTerm} (hu : Refines u u'.1) :
    SemilatticeSup (GSpace hu) where
  sup x y := ⟨x.1 ⊔ y.1, GarbageQ.sup x.2 y.2⟩
  le_sup_left x y := le_sup_left (a := x.1) (b := y.1)
  le_sup_right x y := le_sup_right (a := x.1) (b := y.1)
  sup_le x y z := sup_le (a := x.1) (b := y.1) (c := z.1)

theorem garbage_transport {u1 u2 : CTerm} (e : u1 = u2) {σ : List Pos} (h : IsGarbage u1 σ) :
    IsGarbage u2 σ := e ▸ h

theorem refines_simTgtQ (x : DSpaceLam t) : Refines (targetQ x) (simTgtQ hr x).1 := by
  rw [← rep_spec x]
  exact (simDeriv_valid hr (rep x).2).2

theorem simTgtQ_rep (x : DSpaceLam t) : simTgtQ hr x = simTgtDeriv t' (rep x).1 := by
  conv_lhs => rw [← rep_spec x]
  rfl

/-- The order of `𝔽` on representatives. -/
theorem GF.le_rep (a b : GF hr) :
    a ≤ b ↔ IsGarbage (simTgtDeriv t' (rep b.val).1) (lambdaRS.proj t (rep a.val).1 (rep b.val).1) := by
  obtain ⟨x, hx⟩ := a
  obtain ⟨y, hy⟩ := b
  have ex : x = ResidualSystem.DSpace.mk (rep x) := (rep_spec x).symm
  have ey : y = ResidualSystem.DSpace.mk (rep y) := (rep_spec y).symm
  change GF.le hr ⟨x, hx⟩ ⟨y, hy⟩ ↔ _
  generalize rep x = σ at ex ⊢
  generalize rep y = τ at ey ⊢
  subst ex ey
  exact GF.le_mk hr σ τ hx hy

/-- Garbage of the map `𝔾[σ] → 𝔾[τ]`. -/
theorem laxG_map_garbage {a b : GF hr} (h : a ≤ b) (α : GSpace (refines_simTgtQ hr a.val)) :
    IsGarbage (simTgtQ hr b.val)
      (lambdaRS.proj t ((rep a.val).1 ++ (rep α.1).1) (rep b.val).1) := by
  have h1 := (GF.le_rep hr a b).1 h
  have h2 : IsGarbage (simTgtDeriv t' (rep a.val).1) (rep α.1).1 := by
    have := α.2
    rw [← rep_spec α.1] at this
    exact garbage_transport (simTgtQ_rep hr a.val) this
  refine garbage_transport (simTgtQ_rep hr b.val).symm ?_
  set σ := (rep a.val).1 with hσdef
  set τ := (rep b.val).1
  set ρ := (rep α.1).1
  have hσ : lambdaRS.Valid t σ := (rep a.val).2
  have hτ : lambdaRS.Valid t τ := (rep b.val).2
  have hρ : lambdaRS.Valid (lambdaRS.tgt t σ) ρ := by
    rw [show lambdaRS.tgt t σ = targetQ a.val from tgt_rep a.val]; exact (rep α.1).2
  have hστρ : lambdaRS.Valid t (σ ++ ρ) := (lambdaRS.valid_append _ _ _).2 ⟨hσ, hρ⟩
  rw [proj_append_left lambda_orthogonal hστρ hτ]
  have hrτ : Refines (lambdaRS.tgt t τ) (simTgtDeriv t' τ).1 := (simDeriv_valid hr hτ).2
  have hrσ : Refines (lambdaRS.tgt t σ) (simTgtDeriv t' σ).1 := (simDeriv_valid hr hσ).2
  have hg2 := isGarbage_proj hrσ hρ (proj_valid lambda_orthogonal hτ hσ) h2
  have hcomm := permGen_join_comm lambda_orthogonal hσ hτ
  have hperm := (permGen_iff_permEq lambda_orthogonal (hcomm.valid_left lambda_orthogonal)
    (hcomm.valid_right lambda_orthogonal)).1 hcomm
  have heq := (compatibility hr ((lambdaRS.valid_append _ _ _).2
    ⟨hσ, proj_valid lambda_orthogonal hτ hσ⟩) ((lambdaRS.valid_append _ _ _).2
    ⟨hτ, proj_valid lambda_orthogonal hσ hτ⟩) hperm).1
  rw [simTgtDeriv_append, simTgtDeriv_append] at heq
  exact (isGarbage_append _ _).2 ⟨h1, by rw [← heq]; exact hg2⟩

theorem prefix_cast {u1 u2 : LTerm} (e : u1 = u2) {σ τ : List Pos}
    (h : lambdaRS.Prefix u1 σ τ) : lambdaRS.Prefix u2 σ τ := e ▸ h

theorem lax_prefix_core {σ τ ρ ρ' : List Pos} (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ)
    (hρ : lambdaRS.Valid (lambdaRS.tgt t σ) ρ) (hρ' : lambdaRS.Valid (lambdaRS.tgt t σ) ρ')
    (h : lambdaRS.Prefix (lambdaRS.tgt t σ) ρ ρ') :
    lambdaRS.Prefix (lambdaRS.tgt t τ) (lambdaRS.proj t (σ ++ ρ) τ) (lambdaRS.proj t (σ ++ ρ') τ) :=
  prefix_proj lambda_orthogonal ((lambdaRS.valid_append _ _ _).2 ⟨hσ, hρ⟩)
    ((lambdaRS.valid_append _ _ _).2 ⟨hσ, hρ'⟩) hτ
    ((prefix_append_iff lambda_orthogonal hσ hρ hρ').1 h)

/-- The derivation `σ ++ ρ` used by `laxG.map`, out of `t`. -/
theorem laxG_valid {a : GF hr} (α : GSpace (refines_simTgtQ hr a.val)) :
    lambdaRS.Valid t ((rep a.val).1 ++ (rep α.1).1) := by
  rw [lambdaRS.valid_append]
  exact ⟨(rep a.val).2, (tgt_rep a.val).symm ▸ (rep α.1).2⟩

/-- The lax 2-functor `𝔾 : 𝔽 → Poset`, `𝔾([σ]) = 𝔾(t'/σ, tgt σ)`, acting on morphisms
`[σ] ≤𝔽 [τ]` by `[α] ↦ [σα/τ]`. -/
noncomputable def laxG : LaxFunctor (GF hr) where
  obj a := GSpace (refines_simTgtQ hr a.val)
  map {a b} h α :=
    ⟨DSpace.mk ⟨lambdaRS.proj t ((rep a.val).1 ++ (rep α.1).1) (rep b.val).1, by
        rw [← tgt_rep b.val]
        exact proj_valid lambda_orthogonal (laxG_valid hr α) (rep b.val).2⟩,
      laxG_map_garbage hr h α⟩
  map_mono := by
    intro a b h α β hαβ
    have h' : α.1 ≤ β.1 := hαβ
    rw [← rep_spec α.1, ← rep_spec β.1] at h'
    have hpre : lambdaRS.Prefix (targetQ a.val) (rep α.1).1 (rep β.1).1 :=
      ResidualSystem.DSpace.mk_le_mk.1 h'
    have hpre' := prefix_cast (tgt_rep a.val).symm hpre
    have hα' : lambdaRS.Valid (lambdaRS.tgt t (rep a.val).1) (rep α.1).1 := by
      rw [tgt_rep]; exact (rep α.1).2
    have hβ' : lambdaRS.Valid (lambdaRS.tgt t (rep a.val).1) (rep β.1).1 := by
      rw [tgt_rep]; exact (rep β.1).2
    have hfinal := prefix_cast (tgt_rep b.val) (lax_prefix_core (t := t) (rep a.val).2 (rep b.val).2
      hα' hβ' hpre')
    exact ResidualSystem.DSpace.mk_le_mk.2 hfinal
  map_id := by
    intro a x
    refine Subtype.ext ?_
    refine Eq.trans ?_ (rep_spec x.1)
    show DSpace.mk _ = DSpace.mk (rep x.1)
    congr 1
    apply Subtype.ext
    have hσ := (rep a.val).2
    have hρ : lambdaRS.Valid (lambdaRS.tgt t (rep a.val).1) (rep x.1).1 := by
      rw [tgt_rep]; exact (rep x.1).2
    show lambdaRS.proj t ((rep a.val).1 ++ (rep x.1).1) (rep a.val).1 = (rep x.1).1
    rw [proj_append_left lambda_orthogonal ((lambdaRS.valid_append _ _ _).2 ⟨hσ, hρ⟩) hσ,
      proj_self lambda_orthogonal hσ]
    simp only [ResidualSystem.proj_nil_left, List.nil_append]
    exact proj_nil_right lambda_orthogonal hρ
  map_comp := by
    intro a b c h1 h2 x
    refine Subtype.mk_le_mk.2 ?_
    apply ResidualSystem.DSpace.mk_le_mk.2
    show lambdaRS.Prefix (targetQ c.val) _ _
    have hσ := (rep a.val).2
    have hτ := (rep b.val).2
    have hν := (rep c.val).2
    have hρ : lambdaRS.Valid (lambdaRS.tgt t (rep a.val).1) (rep x.1).1 := by
      rw [tgt_rep]; exact (rep x.1).2
    have hσρ : lambdaRS.Valid t ((rep a.val).1 ++ (rep x.1).1) :=
      (lambdaRS.valid_append _ _ _).2 ⟨hσ, hρ⟩
    have hPv : lambdaRS.Valid (targetQ b.val)
        (lambdaRS.proj t ((rep a.val).1 ++ (rep x.1).1) (rep b.val).1) := by
      rw [← tgt_rep b.val]; exact proj_valid lambda_orthogonal hσρ hτ
    have hκ := ResidualSystem.DSpace.mk_eq_mk.1 (rep_spec (ResidualSystem.DSpace.mk
      (⟨lambdaRS.proj t ((rep a.val).1 ++ (rep x.1).1) (rep b.val).1, hPv⟩ : LDeriv (targetQ b.val))))
    have hPκ := prefix_cast (tgt_rep b.val).symm hκ.2
    have hPv' : lambdaRS.Valid (lambdaRS.tgt t (rep b.val).1)
        (lambdaRS.proj t ((rep a.val).1 ++ (rep x.1).1) (rep b.val).1) := by
      rw [tgt_rep]; exact hPv
    have hκv : lambdaRS.Valid (lambdaRS.tgt t (rep b.val).1) (rep (ResidualSystem.DSpace.mk
      (⟨lambdaRS.proj t ((rep a.val).1 ++ (rep x.1).1) (rep b.val).1, hPv⟩ : LDeriv (targetQ b.val)))).1 := by
      rw [tgt_rep]; exact (rep _).2
    have hle1 : lambdaRS.Prefix t ((rep a.val).1 ++ (rep x.1).1)
        ((rep b.val).1 ++ lambdaRS.proj t ((rep a.val).1 ++ (rep x.1).1) (rep b.val).1) :=
      prefix_join_right lambda_orthogonal hτ hσρ
    have hle2 := (prefix_append_iff lambda_orthogonal hτ hPv' hκv).1 hPκ
    have hτP : lambdaRS.Valid t ((rep b.val).1 ++ lambdaRS.proj t ((rep a.val).1 ++ (rep x.1).1) (rep b.val).1) :=
      (lambdaRS.valid_append _ _ _).2 ⟨hτ, hPv'⟩
    have hτκ := (lambdaRS.valid_append _ _ _).2 ⟨hτ, hκv⟩
    have hle := prefix_trans lambda_orthogonal hσρ hτP hτκ hle1 hle2
    exact prefix_cast (tgt_rep c.val) (prefix_proj lambda_orthogonal hσρ hτκ hν hle)

/-- List-level core of the least-upper-bound property of the Grothendieck construction. -/
theorem groth_core {σ σ' ν β β' κ ρ γ : List Pos}
    (hσ : lambdaRS.Valid t σ) (hσ' : lambdaRS.Valid t σ')
    (hβ : lambdaRS.Valid (lambdaRS.tgt t σ) β) (hβ' : lambdaRS.Valid (lambdaRS.tgt t σ') β')
    (hν : lambdaRS.Valid t ν) (hκ : lambdaRS.Valid (lambdaRS.tgt t ν) κ)
    (hρ : lambdaRS.Valid t ρ)
    (hνle : lambdaRS.Prefix t ν (lambdaRS.join t σ σ'))
    (hκeq : lambdaRS.PermEq (lambdaRS.tgt t ν) κ
      (lambdaRS.join (lambdaRS.tgt t ν) (lambdaRS.proj t (σ ++ β) ν) (lambdaRS.proj t (σ' ++ β') ν)))
    (hp : lambdaRS.Prefix (lambdaRS.tgt t ρ) (lambdaRS.proj t (σ ++ β) ρ) γ)
    (hq : lambdaRS.Prefix (lambdaRS.tgt t ρ) (lambdaRS.proj t (σ' ++ β') ρ) γ)
    (hγ : lambdaRS.Valid (lambdaRS.tgt t ρ) γ) :
    lambdaRS.Prefix (lambdaRS.tgt t ρ) (lambdaRS.proj t (ν ++ κ) ρ) γ := by
  set X := σ ++ β with hXdef
  set Y := σ' ++ β' with hYdef
  have hX : lambdaRS.Valid t X := (lambdaRS.valid_append _ _ _).2 ⟨hσ, hβ⟩
  have hY : lambdaRS.Valid t Y := (lambdaRS.valid_append _ _ _).2 ⟨hσ', hβ'⟩
  have hJ : lambdaRS.Valid t (lambdaRS.join t X Y) :=
    (lambdaRS.valid_append _ _ _).2 ⟨hX, proj_valid lambda_orthogonal hY hX⟩
  have hjσ : lambdaRS.Valid t (lambdaRS.join t σ σ') :=
    (lambdaRS.valid_append _ _ _).2 ⟨hσ, proj_valid lambda_orthogonal hσ' hσ⟩
  -- (ii) proj of the join over ρ
  have hpq : lambdaRS.Prefix (lambdaRS.tgt t ρ)
      (lambdaRS.join (lambdaRS.tgt t ρ) (lambdaRS.proj t X ρ) (lambdaRS.proj t Y ρ)) γ :=
    join_prefix lambda_orthogonal (proj_valid lambda_orthogonal hX hρ)
      (proj_valid lambda_orthogonal hY hρ) hγ hp hq
  have hpj := proj_join lambda_orthogonal hX hY hρ
  have hJρ : lambdaRS.Prefix (lambdaRS.tgt t ρ) (lambdaRS.proj t (lambdaRS.join t X Y) ρ) γ :=
    prefix_trans lambda_orthogonal (proj_valid lambda_orthogonal hJ hρ)
      ((lambdaRS.valid_append _ _ _).2 ⟨proj_valid lambda_orthogonal hX hρ,
        proj_valid lambda_orthogonal (proj_valid lambda_orthogonal hY hρ)
          (proj_valid lambda_orthogonal hX hρ)⟩) hγ hpj.1 hpq
  -- (iii) ν ++ κ ≡ J
  have hσX : lambdaRS.Prefix t σ X :=
    (prefix_iff_exists lambda_orthogonal hσ hX).2 ⟨β, hβ, prefix_refl lambda_orthogonal hX,
      prefix_refl lambda_orthogonal hX⟩
  have hσ'Y : lambdaRS.Prefix t σ' Y :=
    (prefix_iff_exists lambda_orthogonal hσ' hY).2 ⟨β', hβ', prefix_refl lambda_orthogonal hY,
      prefix_refl lambda_orthogonal hY⟩
  have hσJ : lambdaRS.Prefix t σ (lambdaRS.join t X Y) :=
    prefix_trans lambda_orthogonal hσ hX hJ hσX (prefix_join_left lambda_orthogonal hX hY)
  have hσ'J : lambdaRS.Prefix t σ' (lambdaRS.join t X Y) :=
    prefix_trans lambda_orthogonal hσ' hY hJ hσ'Y (prefix_join_right lambda_orthogonal hX hY)
  have hjJ : lambdaRS.Prefix t (lambdaRS.join t σ σ') (lambdaRS.join t X Y) :=
    join_prefix lambda_orthogonal hσ hσ' hJ hσJ hσ'J
  have hνJ : lambdaRS.Prefix t ν (lambdaRS.join t X Y) :=
    prefix_trans lambda_orthogonal hν hjσ hJ hνle hjJ
  have hνκ : lambdaRS.Valid t (ν ++ κ) := (lambdaRS.valid_append _ _ _).2 ⟨hν, hκ⟩
  -- κ ≡ J/ν
  have hpjν := proj_join lambda_orthogonal hX hY hν
  have hκJ : lambdaRS.PermEq (lambdaRS.tgt t ν) κ (lambdaRS.proj t (lambdaRS.join t X Y) ν) :=
    ⟨prefix_trans lambda_orthogonal hκ
        ((lambdaRS.valid_append _ _ _).2 ⟨proj_valid lambda_orthogonal hX hν,
          proj_valid lambda_orthogonal (proj_valid lambda_orthogonal hY hν)
            (proj_valid lambda_orthogonal hX hν)⟩)
        (proj_valid lambda_orthogonal hJ hν) hκeq.1 hpjν.2,
     prefix_trans lambda_orthogonal (proj_valid lambda_orthogonal hJ hν)
        ((lambdaRS.valid_append _ _ _).2 ⟨proj_valid lambda_orthogonal hX hν,
          proj_valid lambda_orthogonal (proj_valid lambda_orthogonal hY hν)
            (proj_valid lambda_orthogonal hX hν)⟩) hκ hpjν.1 hκeq.2⟩
  have hg1 := (permGen_iff_permEq lambda_orthogonal hκ (proj_valid lambda_orthogonal hJ hν)).2 hκJ
  have hg2 : lambdaRS.PermGen t (ν ++ κ) (ν ++ lambdaRS.proj t (lambdaRS.join t X Y) ν) :=
    ResidualSystem.PermGen.append (ResidualSystem.PermGen.refl hν) hg1
  have hcomm := permGen_join_comm lambda_orthogonal hν hJ
  have hle0 : lambdaRS.proj t ν (X ++ lambdaRS.proj t Y X) = [] := hνJ
  unfold ResidualSystem.join at hcomm
  rw [hle0, List.append_nil] at hcomm
  -- hcomm : PermGen t (ν ++ proj J ν) J
  have hfin : lambdaRS.PermGen t (ν ++ κ) (lambdaRS.join t X Y) := hg2.trans hcomm
  have hperm := (permGen_iff_permEq lambda_orthogonal hνκ hJ).1 hfin
  have hpre : lambdaRS.Prefix t (ν ++ κ) (lambdaRS.join t X Y) := hperm.1
  have hz := prefix_proj lambda_orthogonal hνκ hJ hρ hpre
  exact prefix_trans lambda_orthogonal (proj_valid lambda_orthogonal hνκ hρ)
    (proj_valid lambda_orthogonal hJ hρ) hγ hz hJρ

theorem gspace_rep_garbage (a : GF hr) (α : GSpace (refines_simTgtQ hr a.val)) :
    IsGarbage (simTgtDeriv t' (rep a.val).1) (rep α.1).1 := by
  have := α.2
  rw [← rep_spec α.1] at this
  exact garbage_transport (simTgtQ_rep hr a.val) this

theorem proj_append_cancel {σ' β' : List Pos} (hσ' : lambdaRS.Valid t σ')
    (hβ' : lambdaRS.Valid (lambdaRS.tgt t σ') β') :
    lambdaRS.proj t (σ' ++ β') σ' = β' := by
  rw [proj_append_left lambda_orthogonal ((lambdaRS.valid_append _ _ _).2 ⟨hσ', hβ'⟩) hσ',
    proj_self lambda_orthogonal hσ']
  simp only [ResidualSystem.proj_nil_left, List.nil_append]
  exact proj_nil_right lambda_orthogonal hβ'

/-- `[σβ] ≤ [σ'β']` iff `(σβ)/σ' ⊑ β'`. -/
theorem psi_core {σ σ' β β' : List Pos} (hσ : lambdaRS.Valid t σ) (hσ' : lambdaRS.Valid t σ')
    (hβ : lambdaRS.Valid (lambdaRS.tgt t σ) β) (hβ' : lambdaRS.Valid (lambdaRS.tgt t σ') β') :
    lambdaRS.Prefix t (σ ++ β) (σ' ++ β') ↔
      lambdaRS.Prefix (lambdaRS.tgt t σ') (lambdaRS.proj t (σ ++ β) σ') β' := by
  have hX : lambdaRS.Valid t (σ ++ β) := (lambdaRS.valid_append _ _ _).2 ⟨hσ, hβ⟩
  have hY : lambdaRS.Valid t (σ' ++ β') := (lambdaRS.valid_append _ _ _).2 ⟨hσ', hβ'⟩
  constructor
  · intro h
    have := prefix_proj lambda_orthogonal hX hY hσ' h
    rwa [proj_append_cancel hσ' hβ'] at this
  · intro h
    have hpe := proj_append_right lambda_orthogonal (σ := σ ++ β) (τ := σ') (ρ := β') hX hY
    have hz : lambdaRS.proj (lambdaRS.tgt t σ') (lambdaRS.proj t (σ ++ β) σ') β' = [] := h
    rw [hz] at hpe
    have h0 := hpe.1
    unfold ResidualSystem.Prefix at h0 ⊢
    rwa [proj_nil_right lambda_orthogonal (proj_valid lambda_orthogonal hX hY)] at h0

theorem psi_garbage_core {σ σ' β β' : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hσ' : lambdaRS.Valid t σ')
    (hβ : lambdaRS.Valid (lambdaRS.tgt t σ) β) (hβ' : lambdaRS.Valid (lambdaRS.tgt t σ') β')
    (h : lambdaRS.Prefix t (σ ++ β) (σ' ++ β'))
    (hg : IsGarbage (simTgtDeriv t' σ') β') :
    IsGarbage (simTgtDeriv t' σ') (lambdaRS.proj t σ σ') := by
  have hX : lambdaRS.Valid t (σ ++ β) := (lambdaRS.valid_append _ _ _).2 ⟨hσ, hβ⟩
  have hY : lambdaRS.Valid t (σ' ++ β') := (lambdaRS.valid_append _ _ _).2 ⟨hσ', hβ'⟩
  have hσX : lambdaRS.Prefix t σ (σ ++ β) :=
    (prefix_iff_exists lambda_orthogonal hσ hX).2 ⟨β, hβ, prefix_refl lambda_orthogonal hX,
      prefix_refl lambda_orthogonal hX⟩
  have h1 := prefix_proj lambda_orthogonal hσ hY hσ'
    (prefix_trans lambda_orthogonal hσ hX hY hσX h)
  rw [proj_append_cancel hσ' hβ'] at h1
  exact isGarbage_of_prefix (simDeriv_valid hr hσ').2 hβ' (proj_valid lambda_orthogonal hσ hσ') hg h1

/-- The inverse of the factorization iso: `([σ], [τ]) ↦ [στ]`. -/
noncomputable def psi (p : (laxG hr).Groth) : DSpaceLam t :=
  DSpace.mk ⟨(rep p.1.val).1 ++ (rep p.2.1).1, by
    rw [lambdaRS.valid_append]
    exact ⟨(rep p.1.val).2, (tgt_rep p.1.val).symm ▸ (rep p.2.1).2⟩⟩

theorem psi_le_iff (p q : (laxG hr).Groth) : psi hr p ≤ psi hr q ↔ p ≤ q := by
  have hσ := (rep p.1.val).2
  have hσ' := (rep q.1.val).2
  have hβ : lambdaRS.Valid (lambdaRS.tgt t (rep p.1.val).1) (rep p.2.1).1 := by
    rw [tgt_rep]; exact (rep p.2.1).2
  have hβ' : lambdaRS.Valid (lambdaRS.tgt t (rep q.1.val).1) (rep q.2.1).1 := by
    rw [tgt_rep]; exact (rep q.2.1).2
  have hcore := psi_core (t := t) hσ hσ' hβ hβ'
  constructor
  · intro h
    have h' : lambdaRS.Prefix t ((rep p.1.val).1 ++ (rep p.2.1).1) ((rep q.1.val).1 ++ (rep q.2.1).1) :=
      ResidualSystem.DSpace.mk_le_mk.1 h
    have hg := gspace_rep_garbage hr q.1 q.2
    have hle : p.1 ≤ q.1 := (GF.le_rep hr p.1 q.1).2
      (psi_garbage_core hr hσ hσ' hβ hβ' h' hg)
    refine ⟨hle, ?_⟩
    refine Subtype.coe_le_coe.1 ?_
    refine le_of_le_of_eq ?_ (rep_spec q.2.1)
    exact ResidualSystem.DSpace.mk_le_mk.2 (prefix_cast (tgt_rep q.1.val) (hcore.1 h'))
  · rintro ⟨hle, hb⟩
    have hpr : lambdaRS.Prefix (lambdaRS.tgt t (rep q.1.val).1)
        (lambdaRS.proj t ((rep p.1.val).1 ++ (rep p.2.1).1) (rep q.1.val).1) (rep q.2.1).1 :=
      prefix_cast (tgt_rep q.1.val).symm
        (show lambdaRS.Prefix (targetQ q.1.val)
          (lambdaRS.proj t ((rep p.1.val).1 ++ (rep p.2.1).1) (rep q.1.val).1) (rep q.2.1).1 from
          ResidualSystem.DSpace.mk_le_mk.1
            ((show ((laxG hr).map hle p.2).1 ≤ q.2.1 from hb).trans
              (le_of_eq (rep_spec q.2.1).symm)))
    exact ResidualSystem.DSpace.mk_le_mk.2 (hcore.2 hpr)

theorem sieve_append_perm {σ : List Pos} (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) :
    lambdaRS.PermEq t (sieve t t' σ ++ lambdaRS.proj t σ (sieve t t' σ)) σ := by
  have hs := sieve_valid hr hσ
  have hh := permGen_join_comm lambda_orthogonal hs hσ
  have hle : lambdaRS.proj t (sieve t t' σ) σ = [] := sieve_prefix hr hσ
  simp only [ResidualSystem.join, hle, List.append_nil] at hh
  exact (permGen_iff_permEq lambda_orthogonal (hh.valid_left lambda_orthogonal)
    (hh.valid_right lambda_orthogonal)).mp hh

theorem psi_surj : Function.Surjective (psi hr) := by
  intro x
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  have hs := sieve_valid hr σ.2
  have hP : lambdaRS.Valid (lambdaRS.tgt t (sieve t t' σ.1)) (lambdaRS.proj t σ.1 (sieve t t' σ.1)) :=
    proj_valid lambda_orthogonal σ.2 hs
  let a : GF hr := ⟨ResidualSystem.DSpace.mk ⟨sieve t t' σ.1, hs⟩, sieve_garbageFree hr σ.2⟩
  let b : GSpace (refines_simTgtQ hr a.val) :=
    ⟨ResidualSystem.DSpace.mk ⟨lambdaRS.proj t σ.1 (sieve t t' σ.1), hP⟩,
      projection_after_sieve_garbage hr σ.2⟩
  refine ⟨⟨a, b⟩, ?_⟩
  show ResidualSystem.DSpace.mk _ = ResidualSystem.DSpace.mk σ
  apply ResidualSystem.DSpace.mk_eq_mk.2
  have ha := ResidualSystem.DSpace.mk_eq_mk.1 (rep_spec a.val)
  have hb := ResidualSystem.DSpace.mk_eq_mk.1 (rep_spec b.1)
  -- ha : PermEq t (rep a.val).1 (sieve σ), hb : PermEq (targetQ a.val) (rep b.1).1 (proj σ s)
  have hra := (rep a.val).2
  have hrb : lambdaRS.Valid (lambdaRS.tgt t (rep a.val).1) (rep b.1).1 := by
    rw [tgt_rep]; exact (rep b.1).2
  have hag := (permGen_iff_permEq lambda_orthogonal hra hs).2 ha
  have htg : lambdaRS.tgt t (rep a.val).1 = lambdaRS.tgt t (sieve t t' σ.1) := hag.tgt_eq lambda_orthogonal
  have hb' : lambdaRS.PermEq (lambdaRS.tgt t (rep a.val).1) (rep b.1).1
      (lambdaRS.proj t σ.1 (sieve t t' σ.1)) := by
    rw [htg]
    exact hb
  have hbg := (permGen_iff_permEq lambda_orthogonal hrb (htg ▸ hP)).2 hb'
  have hall := ResidualSystem.PermGen.append hag hbg
  have hperm := (permGen_iff_permEq lambda_orthogonal
    (hall.valid_left lambda_orthogonal) (hall.valid_right lambda_orthogonal)).1 hall
  have hsp := sieve_append_perm (t' := t') hr σ.2
  have hv1 := hall.valid_left lambda_orthogonal
  have hv2 := hall.valid_right lambda_orthogonal
  have hv3 : lambdaRS.Valid t (sieve t t' σ.1 ++ lambdaRS.proj t σ.1 (sieve t t' σ.1)) := hv2
  exact ⟨prefix_trans lambda_orthogonal hv1 hv3 σ.2 hperm.1 hsp.1,
    prefix_trans lambda_orthogonal σ.2 hv3 hv1 hsp.2 hperm.2⟩

/-- **Theorem (Factorization).** The Grothendieck construction `∫_𝔽 𝔾` is an upper semilattice
isomorphic to `𝔻_λ(t)`, via `[σ] ↦ ([σ ⇂ t'], [σ/(σ ⇂ t')])` and `([σ], [τ]) ↦ [στ]`. -/
theorem factorization :
    ∃ e : DSpaceLam t ≃o (laxG hr).Groth,
      (∀ σ : LDeriv t, (e (DSpace.mk σ)).1.val = DSpace.mk ⟨sieve t t' σ.1, sieve_valid hr σ.2⟩) ∧
      (∀ p : (laxG hr).Groth, e.symm p =
        DSpace.mk ⟨(rep p.1.val).1 ++ (rep p.2.1).1, by
          rw [lambdaRS.valid_append]
          exact ⟨(rep p.1.val).2, (tgt_rep p.1.val).symm ▸ (rep p.2.1).2⟩⟩) := by
  let emb : (laxG hr).Groth ↪o DSpaceLam t := OrderEmbedding.ofMapLEIff (psi hr) (psi_le_iff hr)
  let iso : (laxG hr).Groth ≃o DSpaceLam t := OrderIso.ofSurjective emb (psi_surj hr)
  refine ⟨iso.symm, ?_, fun p => rfl⟩
  intro σ
  have hp : psi hr (iso.symm (ResidualSystem.DSpace.mk σ)) = ResidualSystem.DSpace.mk σ :=
    iso.apply_symm_apply (ResidualSystem.DSpace.mk σ)
  set p := iso.symm (ResidualSystem.DSpace.mk σ) with hpdef
  have hperm : lambdaRS.PermEq t ((rep p.1.val).1 ++ (rep p.2.1).1) σ.1 :=
    ResidualSystem.DSpace.mk_eq_mk.1 hp
  have hra := (rep p.1.val).2
  have hrb : lambdaRS.Valid (lambdaRS.tgt t (rep p.1.val).1) (rep p.2.1).1 := by
    rw [tgt_rep]; exact (rep p.2.1).2
  have hgf : GarbageFree t t' (rep p.1.val).1 := by
    have := p.1.garbageFree
    rw [← rep_spec p.1.val] at this
    exact this
  have hgar := gspace_rep_garbage hr p.1 p.2
  have hfac := (simple_factorization hr σ.2).2 _ _ hra hrb ⟨hperm.2, hperm.1⟩ hgf hgar
  have hm : ResidualSystem.DSpace.mk (rep p.1.val) =
      ResidualSystem.DSpace.mk (⟨sieve t t' σ.1, sieve_valid hr σ.2⟩ : LDeriv t) :=
    ResidualSystem.DSpace.mk_eq_mk.2 hfac.1
  exact (rep_spec p.1.val).symm.trans hm

noncomputable instance (a : GF hr) : SemilatticeSup ((laxG hr).obj a) :=
  inferInstanceAs (SemilatticeSup (GSpace _))

/-- The join of the Grothendieck construction:
`(a, b) ∨ (a', b') = (a ∨𝔽 a', 𝔾(a ↦ a ∨𝔽 a')(b) ⊔ 𝔾(a' ↦ a ∨𝔽 a')(b'))`. -/
theorem permEq_cast_join {u1 u2 : LTerm} (e : u1 = u2) {κ P Q : List Pos}
    (h : lambdaRS.PermEq u1 κ (lambdaRS.join u1 P Q)) :
    lambdaRS.PermEq u2 κ (lambdaRS.join u2 P Q) := e ▸ h

theorem GF.sup_val (a a' : GF hr) :
    (a ⊔ a').val = DSpace.mk ⟨sieve t t' (lambdaRS.join t (rep a.val).1 (rep a'.val).1),
      sieve_valid hr ((lambdaRS.valid_append _ _ _).2
        ⟨(rep a.val).2, proj_valid lambda_orthogonal (rep a'.val).2 (rep a.val).2⟩)⟩ := by
  obtain ⟨v, hv⟩ := a
  obtain ⟨v', hv'⟩ := a'
  have ha : GarbageFreeQ hr (DSpace.mk (rep v)) := by rw [rep_spec]; exact hv
  have ha' : GarbageFreeQ hr (DSpace.mk (rep v')) := by rw [rep_spec]; exact hv'
  have h := GF.sup_eq hr (rep v) (rep v') ha ha'
  have e1 : (⟨DSpace.mk (rep v), ha⟩ : GF hr) = ⟨v, hv⟩ := (GF.mk.injEq _ _ _ _).mpr (rep_spec v)
  have e2 : (⟨DSpace.mk (rep v'), ha'⟩ : GF hr) = ⟨v', hv'⟩ := (GF.mk.injEq _ _ _ _).mpr (rep_spec v')
  rw [e1, e2] at h
  exact h

theorem groth_isLUB (p q : (laxG hr).Groth) :
    IsLUB {p, q} ⟨p.1 ⊔ q.1,
      (laxG hr).map (le_sup_left : p.1 ≤ p.1 ⊔ q.1) p.2 ⊔
        (laxG hr).map (le_sup_right : q.1 ≤ p.1 ⊔ q.1) q.2⟩ := by
  constructor
  · rintro w (rfl | rfl)
    · exact ⟨le_sup_left, le_sup_left⟩
    · exact ⟨le_sup_right, le_sup_right⟩
  · intro r hr'
    obtain ⟨h1, hb⟩ := hr' (Set.mem_insert _ _)
    obtain ⟨h2, hb'⟩ := hr' (Set.mem_insert_of_mem _ rfl)
    refine ⟨sup_le h1 h2, ?_⟩
    -- representatives
    have hσ := (rep p.1.val).2
    have hσ' := (rep q.1.val).2
    have hν := (rep (p.1 ⊔ q.1).val).2
    have hρ := (rep r.1.val).2
    have hβ : lambdaRS.Valid (lambdaRS.tgt t (rep p.1.val).1) (rep p.2.1).1 := by
      rw [tgt_rep]; exact (rep p.2.1).2
    have hβ' : lambdaRS.Valid (lambdaRS.tgt t (rep q.1.val).1) (rep q.2.1).1 := by
      rw [tgt_rep]; exact (rep q.2.1).2
    have hPv : lambdaRS.Valid (targetQ (p.1 ⊔ q.1).val)
        (lambdaRS.proj t ((rep p.1.val).1 ++ (rep p.2.1).1) (rep (p.1 ⊔ q.1).val).1) := by
      rw [← tgt_rep (p.1 ⊔ q.1).val]
      exact proj_valid lambda_orthogonal ((lambdaRS.valid_append _ _ _).2 ⟨hσ, hβ⟩) hν
    have hQv : lambdaRS.Valid (targetQ (p.1 ⊔ q.1).val)
        (lambdaRS.proj t ((rep q.1.val).1 ++ (rep q.2.1).1) (rep (p.1 ⊔ q.1).val).1) := by
      rw [← tgt_rep (p.1 ⊔ q.1).val]
      exact proj_valid lambda_orthogonal ((lambdaRS.valid_append _ _ _).2 ⟨hσ', hβ'⟩) hν
    set X := (laxG hr).map (le_sup_left : p.1 ≤ p.1 ⊔ q.1) p.2 with hXdef
    set Y := (laxG hr).map (le_sup_right : q.1 ≤ p.1 ⊔ q.1) q.2 with hYdef
    have hXY : X.1 ⊔ Y.1 = ResidualSystem.DSpace.mk (ResidualSystem.DerivFrom.join
        (⟨_, hPv⟩ : LDeriv (targetQ (p.1 ⊔ q.1).val)) ⟨_, hQv⟩) := rfl
    have hκ0 := ResidualSystem.DSpace.mk_eq_mk.1 ((rep_spec (X.1 ⊔ Y.1)).trans hXY)
    have hκeq : lambdaRS.PermEq (lambdaRS.tgt t (rep (p.1 ⊔ q.1).val).1) (rep (X.1 ⊔ Y.1)).1
        (lambdaRS.join (lambdaRS.tgt t (rep (p.1 ⊔ q.1).val).1)
          (lambdaRS.proj t ((rep p.1.val).1 ++ (rep p.2.1).1) (rep (p.1 ⊔ q.1).val).1)
          (lambdaRS.proj t ((rep q.1.val).1 ++ (rep q.2.1).1) (rep (p.1 ⊔ q.1).val).1)) :=
      permEq_cast_join (tgt_rep (p.1 ⊔ q.1).val).symm hκ0
    have hκv : lambdaRS.Valid (lambdaRS.tgt t (rep (p.1 ⊔ q.1).val).1) (rep (X.1 ⊔ Y.1)).1 := by
      rw [tgt_rep]; exact (rep _).2
    -- ν ⊑ join σ σ'
    have hνs := ResidualSystem.DSpace.mk_eq_mk.1 ((rep_spec (p.1 ⊔ q.1).val).trans
      (GF.sup_val hr p.1 q.1))
    have hjσ : lambdaRS.Valid t (lambdaRS.join t (rep p.1.val).1 (rep q.1.val).1) :=
      (lambdaRS.valid_append _ _ _).2 ⟨hσ, proj_valid lambda_orthogonal hσ' hσ⟩
    have hνle : lambdaRS.Prefix t (rep (p.1 ⊔ q.1).val).1
        (lambdaRS.join t (rep p.1.val).1 (rep q.1.val).1) :=
      prefix_trans lambda_orthogonal hν (sieve_valid hr hjσ) hjσ hνs.1 (sieve_prefix hr hjσ)
    -- the two hypotheses
    have hpr : lambdaRS.Prefix (lambdaRS.tgt t (rep r.1.val).1)
        (lambdaRS.proj t ((rep p.1.val).1 ++ (rep p.2.1).1) (rep r.1.val).1) (rep r.2.1).1 :=
      prefix_cast (tgt_rep r.1.val).symm
        (show lambdaRS.Prefix (targetQ r.1.val)
          (lambdaRS.proj t ((rep p.1.val).1 ++ (rep p.2.1).1) (rep r.1.val).1) (rep r.2.1).1 from
          ResidualSystem.DSpace.mk_le_mk.1
            ((show ((laxG hr).map h1 p.2).1 ≤ r.2.1 from hb).trans
              (le_of_eq (rep_spec r.2.1).symm)))
    have hqr : lambdaRS.Prefix (lambdaRS.tgt t (rep r.1.val).1)
        (lambdaRS.proj t ((rep q.1.val).1 ++ (rep q.2.1).1) (rep r.1.val).1) (rep r.2.1).1 :=
      prefix_cast (tgt_rep r.1.val).symm
        (show lambdaRS.Prefix (targetQ r.1.val)
          (lambdaRS.proj t ((rep q.1.val).1 ++ (rep q.2.1).1) (rep r.1.val).1) (rep r.2.1).1 from
          ResidualSystem.DSpace.mk_le_mk.1
            ((show ((laxG hr).map h2 q.2).1 ≤ r.2.1 from hb').trans
              (le_of_eq (rep_spec r.2.1).symm)))
    have hγ : lambdaRS.Valid (lambdaRS.tgt t (rep r.1.val).1) (rep r.2.1).1 := by
      rw [tgt_rep]; exact (rep _).2
    have key := groth_core (t := t) hσ hσ' hβ hβ' hν hκv hρ hνle hκeq hpr hqr hγ
    refine Subtype.coe_le_coe.1 ?_
    refine le_of_le_of_eq ?_ (rep_spec r.2.1)
    exact ResidualSystem.DSpace.mk_le_mk.2 (prefix_cast (tgt_rep r.1.val) key)

end Factorization

end Thesis
