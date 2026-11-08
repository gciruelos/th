/-
# Chapter 4: Simulation of the λ-calculus

Main-text results of Chapter 4:
* Refinements (`omega_not_refinable`).
* Simulation and reverse simulation (`simulation`, `reverse_simulation`).
* Head normal forms (`hnf_has_refinement`, `has_hnf_iff_refinable`).
* Simulation residuals, cube lemmas, compatibility, and algebraic simulation (`simRes_spec`,
  `simDeriv_valid`, `simTgtDeriv_append`, `simDeriv_append`, `basic_cube_lemma`,
  `simDeriv_of_completeDevelopment`, `compatibility`, `simDeriv_prefix`,
  `generalized_cube_lemma`, `algebraicSimulation`).
-/
import Thesis.Chapter4SimulationDefs
import Thesis.Chapter4SimulationAppendix

namespace Thesis

open LTerm DTerm

/-! ## 4.1 Refinements -/

/-- `Ω = (λx.xx)(λx.xx)` has no refinement. -/
theorem omega_not_refinable :
    ¬ ∃ t' : CTerm, Refines (.app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0))))
      t'.1 := by
  let δ : LTerm := .lam (.app (.var 0) (.var 0))
  let Ω : LTerm := .app δ δ
  have loop : ∀ s, BetaStep Ω s → s = Ω := by
    intro s hs
    dsimp [Ω, δ] at hs
    cases betaStep_iff_beta.mp hs with
    | beta => rfl
    | appL _ h =>
      cases h with
      | lam h =>
        cases h with
        | appL _ h => cases h
        | appR _ h => cases h
    | appR _ h =>
      cases h with
      | lam h =>
        cases h with
        | appL _ h => cases h
        | appR _ h => cases h
  rintro ⟨u, hr⟩
  obtain ⟨s, hp, hn⟩ := hr.hasHNF u.2
  have he : s = Ω := by
    clear hn
    induction hp with
    | refl => rfl
    | tail hp h ih => exact loop _ (ih ▸ h)
  subst s
  dsimp [Ω, δ] at hn
  cases hn with
  | head hh => cases hh with | app _ hh => cases hh

/-! ## 4.2 Simulation -/

/-- **Simulation**: if `t' ⋉ t →β s` then `t' ↠dist s'` for some `s' ⋉ s` (in fact by a
multistep). -/
theorem simulation {t s : LTerm} {t' : CTerm} (hr : Refines t t'.1) (h : BetaStep t s) :
    ∃ s' : CTerm, Relation.ReflTransGen CRed t' s' ∧ Refines s s'.1 := by
  obtain ⟨v, hp, hv⟩ := simulation_raw (betaStep_iff_beta.mp h) hr t'.2
  exact ⟨⟨v, DRed.correct_reduces t'.2 hp⟩, DRed.reduces_correct_terms hp _ _, hv⟩

/-- **Reverse simulation**: if `t ⋉ t' →dist s'` then `t →β s ⋉ s''` for some `s, s''`,
where the step `t' → s'` is contained in the multistep `t' ↠ s''`. -/
theorem reverse_simulation {t : LTerm} {t' s' : CTerm} {ℓ : Label} (hr : Refines t t'.1)
    (h : DStep t'.1 ℓ s'.1) :
    ∃ (s : LTerm) (s'' : CTerm) (M : Finset Label),
      BetaStep t s ∧ Refines s s''.1 ∧ ℓ ∈ M ∧ (∀ m ∈ M, distRS.isStep t' m) ∧
        distRS.tgt t' (distRS.dev t' M) = s'' := by
  obtain ⟨p, hp, hm⟩ := h.simulation_position hr
  exact ⟨contractAt t p, simTgt t' p, simRes t'.1 p, ⟨p, hp, rfl⟩,
    simulation_canonical hr hp, hm, fun _ ha => simRes_isStep ha, rfl⟩

/-! ## 4.3 Head normal forms -/

/-- Head normal forms are refinable. -/
theorem hnf_has_refinement {t : LTerm} (h : IsHNF t) : ∃ t' : CTerm, Refines t t'.1 := by
  obtain ⟨u, hr, hc, _⟩ := hnf_has_strong_refinement h
  exact ⟨⟨u, hc.correct⟩, hr⟩

/-- **Refinability characterizes head normalization.** The following are equivalent:
1. `t` has a refinement;
2. `t` has a refinement that reduces to `λ…λ. y^τ [] … []`;
3. `t` has a head normal form. -/
theorem has_hnf_iff_refinable (t : LTerm) :
    [∃ t' : CTerm, Refines t t'.1,
     ∃ t' : CTerm, Refines t t'.1 ∧
       ∃ u' : CTerm, Relation.ReflTransGen CRed t' u' ∧ IsEmptyHNF u'.1,
     t.HasHNF].TFAE := by
  tfae_have 1 → 3 := by
    rintro ⟨u, hr⟩
    exact hr.hasHNF u.2
  tfae_have 3 → 2 := by
    intro h
    obtain ⟨v, _, hr, n, hnf, hp⟩ := head_normalizing_has_strong_refinement h
    exact ⟨v, hr, n, hp, hnf⟩
  tfae_have 2 → 1 := by
    rintro ⟨v, hr, _⟩
    exact ⟨v, hr⟩
  tfae_finish

/-! ## 4.4 Simulation residuals -/

/-- The simulation residuals of a step are steps, and `t'/R ⋉ tgt(R)`. -/
theorem simRes_spec {t : LTerm} {t' : CTerm} {p : Pos} (hr : Refines t t'.1)
    (hp : lambdaRS.isStep t p) :
    (∀ ℓ ∈ simRes t'.1 p, distRS.isStep t' ℓ) ∧ Refines (contractAt t p) (simTgt t' p).1 := by
  exact ⟨fun _ hm => simRes_isStep hm, simulation_canonical hr hp⟩

theorem simDeriv_valid {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) :
    distRS.Valid t' (simDeriv t' σ) ∧ Refines (lambdaRS.tgt t σ) (simTgtDeriv t' σ).1 := by
  induction σ generalizing t t' with
  | nil => exact ⟨trivial, hr⟩
  | cons p σ ih =>
    obtain ⟨hp, hσ⟩ := hσ
    obtain ⟨hm, hs⟩ := simRes_spec hr hp
    have hd := (distRS.orthogonal.dev_complete t' (simRes t'.1 p) hm).1.valid
    obtain ⟨hv, hr'⟩ := ih hs hσ
    exact ⟨(distRS.valid_append _ _ _).2 ⟨hd, hv⟩, hr'⟩

/-- **Simulation residuals and composition** (1): `t'/στ = (t'/σ)/τ`. -/
theorem simTgtDeriv_append (t' : CTerm) (σ τ : List Pos) :
    simTgtDeriv t' (σ ++ τ) = simTgtDeriv (simTgtDeriv t' σ) τ := by
  induction σ generalizing t' with
  | nil => rfl
  | cons p σ ih => exact ih _

/-- **Simulation residuals and composition** (2): `στ/t' = (σ/t')(τ/(t'/σ))`. -/
theorem simDeriv_append (t' : CTerm) (σ τ : List Pos) :
    simDeriv t' (σ ++ τ) = simDeriv t' σ ++ simDeriv (simTgtDeriv t' σ) τ := by
  induction σ generalizing t' with
  | nil => rfl
  | cons p σ ih => simp [simDeriv, simTgtDeriv, ih]

/-- **Basic cube lemma for simulation residuals**:
`(R/t')/(S/t') = (R/S)/(t'/S)` as sets of coinitial λ^dist-steps. -/
theorem basic_cube_lemma {t : LTerm} {t' : CTerm} {p q : Pos} (hr : Refines t t'.1)
    (hp : lambdaRS.isStep t p) (hq : lambdaRS.isStep t q) :
    distRS.resSetDeriv t' (simRes t'.1 p) (distRS.dev t' (simRes t'.1 q)) =
      (lambdaRS.res t q p).biUnion fun p' => simRes (simTgt t' q).1 p' := by
  by_cases hpq : p = q
  · subst hpq
    have hm : ∀ ℓ ∈ simRes t'.1 p, distRS.isStep t' ℓ := fun _ h => simRes_isStep h
    have hd := (distRS.orthogonal.dev_complete t' (simRes t'.1 p) hm).2
    rw [hd]
    have ha : lambdaRS.res t p p = ∅ := lambda_orthogonal.autoerasure t p hp
    rw [ha, Finset.biUnion_empty]
  · obtain ⟨v, σ, ht, he, hv, -, hcube⟩ := cube_trace hr t'.2 hq
    have hv' : (simTgt t' q).1 = v := simTgt_eq_trace ht he
    have hM : ∀ b ∈ simRes t'.1 p, distRS.isStep t' b := fun _ h => simRes_isStep h
    have hN : ∀ b ∈ simRes t'.1 q, distRS.isStep t' b := fun _ h => simRes_isStep h
    have hvd := ResidualSystem.dev_valid distRS.orthogonal hN
    rw [(distRS.residual_names hM hvd).1, distRS.names_dev]
    have hdisj : simRes t'.1 p \ simRes t'.1 q = simRes t'.1 p := by
      apply Finset.sdiff_eq_self_of_disjoint
      rw [Finset.disjoint_left]
      intro ℓ hℓp hℓq
      exact hpq (simRes_position_unique t'.2 hℓp hℓq)
    rw [hdisj, hv']
    exact hcube p hp hpq

/-- **Simulation residual of a development**: if `σ` is a complete development of `𝓜` then
`σ/t'` is a complete development of `𝓜/t'`. -/
theorem simDeriv_of_completeDevelopment {t : LTerm} {t' : CTerm} {M : Finset Pos}
    {σ : List Pos} (hr : Refines t t'.1) (hM : ∀ p ∈ M, lambdaRS.isStep t p)
    (hσ : lambdaRS.IsCompleteDevelopment t M σ) :
    distRS.IsCompleteDevelopment t' (M.biUnion fun p => simRes t'.1 p) (simDeriv t' σ) := by
  induction σ generalizing t t' M with
  | nil =>
    have hM0 : M = ∅ := hσ.2
    subst hM0
    exact ⟨trivial, rfl⟩
  | cons a σ ih =>
    obtain ⟨⟨ha, haM, hdev⟩, hres⟩ := hσ
    have hM' : ∀ p ∈ lambdaRS.resSet t M a, lambdaRS.isStep (lambdaRS.contract t a) p := by
      intro p hp
      obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp hp
      exact lambda_orthogonal.res_isStep t m a (hM m hm) ha p hpm
    have hIH := ih (t := lambdaRS.contract t a) (t' := simTgt t' a)
      (M := lambdaRS.resSet t M a) (simulation_canonical hr ha) hM' ⟨hdev, hres⟩
    have hS : ∀ p ∈ M, ∀ ℓ ∈ simRes t'.1 p, distRS.isStep t' ℓ := fun _ _ _ h => simRes_isStep h
    have hU : ∀ ℓ ∈ M.biUnion (fun p => simRes t'.1 p), distRS.isStep t' ℓ := by
      intro ℓ hℓ
      obtain ⟨p, hp, hℓp⟩ := Finset.mem_biUnion.mp hℓ
      exact hS p hp ℓ hℓp
    have hdS := distRS.orthogonal.dev_complete t' (simRes t'.1 a) (hS a haM)
    have hresU : distRS.resSetDeriv t' (M.biUnion fun p => simRes t'.1 p)
        (distRS.dev t' (simRes t'.1 a)) =
        (lambdaRS.resSet t M a).biUnion fun p' => simRes (simTgt t' a).1 p' := by
      rw [ResidualSystem.resSetDeriv_biUnion]
      have : ∀ p ∈ M, distRS.resSetDeriv t' (simRes t'.1 p) (distRS.dev t' (simRes t'.1 a)) =
          (lambdaRS.res t a p).biUnion fun p' => simRes (simTgt t' a).1 p' :=
        fun p hp => basic_cube_lemma hr (hM p hp) ha
      rw [Finset.biUnion_congr rfl this]
      unfold ResidualSystem.resSet
      rw [Finset.biUnion_biUnion]
    have hN : distRS.IsCompleteDevelopment (distRS.tgt t' (distRS.dev t' (simRes t'.1 a)))
        (distRS.resSetDeriv t' (M.biUnion fun p => simRes t'.1 p)
          (distRS.dev t' (simRes t'.1 a))) (simDeriv (simTgt t' a) σ) := by
      rw [hresU]; exact hIH
    have hunion := ResidualSystem.completeDevelopment_union hdS hN
    have hsub : simRes t'.1 a ∪ M.biUnion (fun p => simRes t'.1 p) =
        M.biUnion (fun p => simRes t'.1 p) :=
      Finset.union_eq_right.mpr (Finset.subset_biUnion_of_mem (fun p => simRes t'.1 p) haM)
    rw [hsub] at hunion
    exact hunion

theorem compatibility_permGen {t : lambdaRS.Obj} {σ τ : List lambdaRS.Adr}
    (h : ResidualSystem.PermGen lambdaRS t σ τ) :
    ∀ {t' : CTerm} (hr : Refines t t'.1),
      simTgtDeriv t' σ = simTgtDeriv t' τ ∧ distRS.PermEq t' (simDeriv t' σ) (simDeriv t' τ) := by
  induction h with
  | refl hσ =>
    intro t' hr
    exact ⟨rfl, ResidualSystem.prefix_refl distRS.orthogonal (simDeriv_valid hr hσ).1,
      ResidualSystem.prefix_refl distRS.orthogonal (simDeriv_valid hr hσ).1⟩
  | symm h ih =>
    intro t' hr
    obtain ⟨ht, hp⟩ := ih hr
    exact ⟨ht.symm, hp.2, hp.1⟩
  | trans h1 h2 ih1 ih2 =>
    intro t' hr
    obtain ⟨ht1, hp1⟩ := ih1 hr
    obtain ⟨ht2, hp2⟩ := ih2 hr
    have hv1 := (simDeriv_valid hr (h1.valid_left lambda_orthogonal)).1
    have hv2 := (simDeriv_valid hr (h1.valid_right lambda_orthogonal)).1
    have hv3 := (simDeriv_valid hr (h2.valid_right lambda_orthogonal)).1
    exact ⟨ht1.trans ht2,
      ResidualSystem.prefix_trans distRS.orthogonal hv1 hv2 hv3 hp1.1 hp2.1,
      ResidualSystem.prefix_trans distRS.orthogonal hv3 hv2 hv1 hp2.2 hp1.2⟩
  | append h1 h2 ih1 ih2 =>
    intro t' hr
    obtain ⟨ht1, hp1⟩ := ih1 hr
    have hr' : Refines (lambdaRS.tgt _ _) (simTgtDeriv t' _).1 :=
      (simDeriv_valid hr (h1.valid_left lambda_orthogonal)).2
    obtain ⟨ht2, hp2⟩ := ih2 hr'
    rw [simTgtDeriv_append, simTgtDeriv_append, ← ht1, ht2]
    refine ⟨rfl, ?_⟩
    rw [simDeriv_append, simDeriv_append, ← ht1]
    have hs1 := (simDeriv_valid hr (h1.valid_left lambda_orthogonal)).1
    have hs2 := (simDeriv_valid hr (h1.valid_right lambda_orthogonal)).1
    have ht1' := (simDeriv_valid hr' (h2.valid_left lambda_orthogonal)).1
    have ht2' := (simDeriv_valid hr' (h2.valid_right lambda_orthogonal)).1
    rw [distRS.permEq_iff_names ((distRS.valid_append _ _ _).2 ⟨hs1, by rw [tgt_simDeriv]; exact ht1'⟩)
      ((distRS.valid_append _ _ _).2 ⟨hs2, by rw [tgt_simDeriv, ← ht1]; exact ht2'⟩)]
    rw [distRS.names_append, distRS.names_append]
    have hn1 := (distRS.permEq_iff_names hs1 hs2).1 hp1
    have hn2 := (distRS.permEq_iff_names ht1' ht2').1 hp2
    rw [hn1, hn2]
  | @swap t a b ha hb =>
    intro t' hr
    have hc1 := ResidualSystem.swap_isCompleteDevelopment lambda_orthogonal ha hb
    have hc2 := ResidualSystem.swap_isCompleteDevelopment lambda_orthogonal hb ha
    have heq : ({b} ∪ {a} : Finset Pos) = {a} ∪ {b} := Finset.union_comm {b} {a}
    rw [heq] at hc2
    have hMs : ∀ p ∈ ({a} ∪ {b} : Finset Pos), lambdaRS.isStep t p := by
      intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact (Finset.mem_singleton.mp h) ▸ ha
      · exact (Finset.mem_singleton.mp h) ▸ hb
    have hd1 := simDeriv_of_completeDevelopment hr hMs hc1
    have hd2 := simDeriv_of_completeDevelopment hr hMs hc2
    have hM : ∀ ℓ ∈ ({a} ∪ {b} : Finset Pos).biUnion (fun p => simRes t'.1 p), distRS.isStep t' ℓ := by
      intro ℓ hℓ
      obtain ⟨p, hp, hℓp⟩ := Finset.mem_biUnion.mp hℓ
      exact simRes_isStep hℓp
    have hpe := distRS_completeDevelopment_permEq hM hd1 hd2
    have htg := ResidualSystem.tgt_eq_of_permEq distRS.orthogonal
      (ResidualSystem.isDevelopment_valid hd1.1) (ResidualSystem.isDevelopment_valid hd2.1) hpe
    rw [tgt_simDeriv, tgt_simDeriv] at htg
    exact ⟨htg, hpe⟩

/-- **Compatibility**: if `σ ≡ τ` then `t'/σ = t'/τ` and `σ/t' ≡ τ/t'`. -/
theorem compatibility {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) (h : lambdaRS.PermEq t σ τ) :
    simTgtDeriv t' σ = simTgtDeriv t' τ ∧ distRS.PermEq t' (simDeriv t' σ) (simDeriv t' τ) :=
  compatibility_permGen ((ResidualSystem.permGen_iff_permEq lambda_orthogonal hσ hτ).2 h) hr

/-- **Simulation residuals and prefixes**: `σ ⊑ τ ⟹ σ/t' ⊑ τ/t'`. -/
theorem simDeriv_prefix {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) (h : lambdaRS.Prefix t σ τ) :
    distRS.Prefix t' (simDeriv t' σ) (simDeriv t' τ) := by
  obtain ⟨ρ, hρ, he⟩ := (ResidualSystem.prefix_iff_exists lambda_orthogonal hσ hτ).1 h
  have hs := simDeriv_valid hr hσ
  have ht := simDeriv_valid hr hτ
  have hρ' := (simDeriv_valid hs.2 hρ).1
  apply (ResidualSystem.prefix_iff_exists distRS.orthogonal hs.1 ht.1).2
  refine ⟨simDeriv (simTgtDeriv t' σ) ρ, by simpa only [tgt_simDeriv] using hρ', ?_⟩
  rw [← simDeriv_append]
  exact (compatibility hr ((lambdaRS.valid_append _ _ _).2 ⟨hσ, hρ⟩) hτ he).2

/-! ### Names of simulation residuals (towards the generalized cube lemma) -/

theorem simNames_cons (t' : CTerm) (p : Pos) (σ : List Pos) :
    distRS.names (simDeriv t' (p :: σ)) =
      simRes t'.1 p ∪ distRS.names (simDeriv (simTgt t' p) σ) := by
  simp only [simDeriv]
  rw [distRS.names_append, distRS.names_dev t' (simRes t'.1 p)]

theorem simNames_append (t' : CTerm) (σ τ : List Pos) :
    distRS.names (simDeriv t' (σ ++ τ)) =
      distRS.names (simDeriv t' σ) ∪ distRS.names (simDeriv (simTgtDeriv t' σ) τ) := by
  rw [simDeriv_append, distRS.names_append]

/-- The set form of the basic cube lemma. -/
theorem cube_sets {t : LTerm} {t' : CTerm} {p q : Pos} (hr : Refines t t'.1)
    (hp : lambdaRS.isStep t p) (hq : lambdaRS.isStep t q) :
    (lambdaRS.res t q p).biUnion (fun p' => simRes (simTgt t' q).1 p') =
      simRes t'.1 p \ simRes t'.1 q := by
  rw [← basic_cube_lemma hr hp hq]
  have hM : ∀ b ∈ simRes t'.1 p, distRS.isStep t' b := fun _ h => simRes_isStep h
  have hN : ∀ b ∈ simRes t'.1 q, distRS.isStep t' b := fun _ h => simRes_isStep h
  have hv := ResidualSystem.dev_valid distRS.orthogonal hN
  rw [(distRS.residual_names hM hv).1, distRS.names_dev]

/-- The cube lemma for an arbitrary derivation. -/
theorem cube_gen : ∀ (ρ : List Pos) (p : Pos) {t : LTerm} {t' : CTerm},
    Refines t t'.1 → lambdaRS.isStep t p → lambdaRS.Valid t ρ →
      (lambdaRS.resSetDeriv t {p} ρ).biUnion (fun y => simRes (simTgtDeriv t' ρ).1 y) =
        simRes t'.1 p \ distRS.names (simDeriv t' ρ) := by
  intro ρ
  induction ρ with
  | nil =>
    intro p t t' hr hp _
    simp [ResidualSystem.resSetDeriv, simDeriv, simTgtDeriv, distRS.names]
  | cons q ρ ih =>
    intro p t t' hr hp hv
    obtain ⟨hq, hρ⟩ := hv
    have hr' := simulation_canonical hr hq
    have hres : ∀ z ∈ lambdaRS.res t q p, lambdaRS.isStep (lambdaRS.contract t q) z :=
      lambda_orthogonal.res_isStep t p q hp hq
    rw [simNames_cons]
    change (lambdaRS.resSetDeriv (lambdaRS.contract t q) (lambdaRS.resSet t {p} q) ρ).biUnion
      (fun y => simRes (simTgtDeriv (simTgt t' q) ρ).1 y) = _
    rw [ResidualSystem.resSet_singleton, ResidualSystem.resSetDeriv_eq_biUnion,
      Finset.biUnion_biUnion]
    have h1 : ∀ z ∈ lambdaRS.res t q p,
        (lambdaRS.resSetDeriv (lambdaRS.contract t q) {z} ρ).biUnion
          (fun y => simRes (simTgtDeriv (simTgt t' q) ρ).1 y) =
        simRes (simTgt t' q).1 z \ distRS.names (simDeriv (simTgt t' q) ρ) :=
      fun z hz => ih z hr' (hres z hz) hρ
    rw [Finset.biUnion_congr rfl h1]
    ext ℓ
    have hc := cube_sets hr hp hq
    have hmem : ℓ ∈ simRes t'.1 p \ (simRes t'.1 q ∪ distRS.names (simDeriv (simTgt t' q) ρ)) ↔
        ℓ ∈ (lambdaRS.res t q p).biUnion (fun p' => simRes (simTgt t' q).1 p') ∧
          ℓ ∉ distRS.names (simDeriv (simTgt t' q) ρ) := by
      rw [hc]; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
    rw [hmem]
    simp only [Finset.mem_biUnion, Finset.mem_sdiff]
    constructor
    · rintro ⟨z, hz, hℓ, hn⟩; exact ⟨⟨z, hz, hℓ⟩, hn⟩
    · rintro ⟨⟨z, hz, hℓ⟩, hn⟩; exact ⟨z, hz, hℓ, hn⟩

theorem simNames_complete {t : LTerm} {t' : CTerm} {M : Finset Pos} {δ : List Pos}
    (hr : Refines t t'.1) (hM : ∀ x ∈ M, lambdaRS.isStep t x)
    (hδ : lambdaRS.IsCompleteDevelopment t M δ) :
    distRS.names (simDeriv t' δ) = M.biUnion (fun x => simRes t'.1 x) := by
  have h := simDeriv_of_completeDevelopment hr hM hδ
  exact distRS_completeDevelopment_names
    (fun ℓ hℓ => by
      obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hℓ
      exact simRes_isStep hx) h

/-- Names of the projection of a derivation over a complete development. -/
theorem single_gen : ∀ (σ : List Pos) {t : LTerm} {t' : CTerm} (M : Finset Pos) (δ : List Pos),
    Refines t t'.1 → lambdaRS.Valid t σ → (∀ x ∈ M, lambdaRS.isStep t x) →
    lambdaRS.IsCompleteDevelopment t M δ →
      distRS.names (simDeriv (simTgtDeriv t' δ) (lambdaRS.proj t σ δ)) =
        distRS.names (simDeriv t' σ) \ M.biUnion (fun x => simRes t'.1 x) := by
  intro σ
  induction σ with
  | nil =>
    intro t t' M δ _ _ _ _
    rw [ResidualSystem.proj_nil_left]
    simp [simDeriv, distRS.names]
  | cons p σ' ih =>
    intro t t' M δ hr hv hM hδ
    obtain ⟨hp, hσ'⟩ := hv
    have hvδ : lambdaRS.Valid t δ := ResidualSystem.isDevelopment_valid hδ.1
    have hvp : lambdaRS.Valid t [p] := ResidualSystem.valid_singleton hp
    rw [ResidualSystem.proj_cons_left lambda_orthogonal hp hσ' hvδ, simNames_append]
    -- part A
    have hA : distRS.names (simDeriv (simTgtDeriv t' δ) (lambdaRS.proj t [p] δ)) =
        simRes t'.1 p \ distRS.names (simDeriv t' δ) := by
      have hproj : lambdaRS.proj t [p] δ =
          lambdaRS.dev (lambdaRS.tgt t δ) (lambdaRS.resSetDeriv t {p} δ) := by
        simp [ResidualSystem.proj]
      rw [hproj]
      have hY : ∀ y ∈ lambdaRS.resSetDeriv t {p} δ, lambdaRS.isStep (lambdaRS.tgt t δ) y :=
        ResidualSystem.resSetDeriv_isStep lambda_orthogonal (by simpa using hp) hvδ
      have hrδ : Refines (lambdaRS.tgt t δ) (simTgtDeriv t' δ).1 := (simDeriv_valid hr hvδ).2
      rw [simNames_complete hrδ hY (lambda_orthogonal.dev_complete _ _ hY)]
      exact cube_gen δ p hr hp hvδ
    -- the names of the development
    have hU : distRS.names (simDeriv t' δ) = M.biUnion (fun x => simRes t'.1 x) :=
      simNames_complete hr hM hδ
    -- part B
    have hcomm := ResidualSystem.permGen_join_comm lambda_orthogonal hvδ hvp
    have hperm := (ResidualSystem.permGen_iff_permEq lambda_orthogonal (hcomm.valid_left lambda_orthogonal)
      (hcomm.valid_right lambda_orthogonal)).1 hcomm
    have htg := (compatibility hr (hcomm.valid_left lambda_orthogonal)
      (hcomm.valid_right lambda_orthogonal) hperm).1
    unfold ResidualSystem.join at htg
    rw [simTgtDeriv_append, simTgtDeriv_append] at htg
    have hr' := simulation_canonical hr hp
    have hcd : lambdaRS.IsCompleteDevelopment (lambdaRS.tgt t [p]) (lambdaRS.resSetDeriv t M [p])
        (lambdaRS.proj t δ [p]) :=
      ResidualSystem.proj_isCompleteDevelopment lambda_orthogonal hM hδ hvp
    have hM' : ∀ x ∈ lambdaRS.resSet t M p, lambdaRS.isStep (lambdaRS.contract t p) x := by
      intro x hx
      obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.mp hx
      exact lambda_orthogonal.res_isStep t m p (hM m hm) hp x hxm
    have hIH := ih (t := lambdaRS.contract t p) (t' := simTgt t' p) (lambdaRS.resSet t M p)
      (lambdaRS.proj t δ [p]) hr' hσ' hM' hcd
    rw [show simTgtDeriv (simTgtDeriv t' δ) (lambdaRS.proj t [p] δ) =
      simTgtDeriv (simTgt t' p) (lambdaRS.proj t δ [p]) from htg, hIH, hA, hU, simNames_cons]
    -- the union of simulated residuals
    have hU' : (lambdaRS.resSet t M p).biUnion (fun x => simRes (simTgt t' p).1 x) =
        M.biUnion (fun x => simRes t'.1 x) \ simRes t'.1 p := by
      ext ℓ
      simp only [ResidualSystem.resSet, Finset.mem_biUnion, Finset.mem_sdiff]
      constructor
      · rintro ⟨y, ⟨m, hm, hy⟩, hℓ⟩
        have := cube_sets (t' := t') hr (hM m hm) hp
        have hmem : ℓ ∈ simRes t'.1 m \ simRes t'.1 p := by
          rw [← this]; exact Finset.mem_biUnion.mpr ⟨y, hy, hℓ⟩
        rw [Finset.mem_sdiff] at hmem
        exact ⟨⟨m, hm, hmem.1⟩, hmem.2⟩
      · rintro ⟨⟨m, hm, hℓ⟩, hn⟩
        have := cube_sets (t' := t') hr (hM m hm) hp
        have hmem : ℓ ∈ (lambdaRS.res t p m).biUnion (fun x => simRes (simTgt t' p).1 x) := by
          rw [this]; exact Finset.mem_sdiff.mpr ⟨hℓ, hn⟩
        obtain ⟨y, hy, hℓy⟩ := Finset.mem_biUnion.mp hmem
        exact ⟨y, ⟨m, hm, hy⟩, hℓy⟩
    rw [hU']
    -- disjointness
    have hdis : Disjoint (simRes t'.1 p) (distRS.names (simDeriv (simTgt t' p) σ')) := by
      have hvs := (simDeriv_valid hr (show lambdaRS.Valid t (p :: σ') from ⟨hp, hσ'⟩)).1
      change distRS.Valid t' (distRS.dev t' (simRes t'.1 p) ++ simDeriv (simTgt t' p) σ') at hvs
      have := distRS.names_append_disjoint hvs
      rwa [distRS.names_dev] at this
    ext ℓ
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, fun h => h2 h⟩
      · refine ⟨Or.inr h1, fun h => h2 ⟨h, ?_⟩⟩
        intro hp'
        exact Finset.disjoint_left.mp hdis hp' h1
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, fun h => h2 h⟩
      · exact Or.inr ⟨h1, fun ⟨h, _⟩ => h2 h⟩

theorem gen_names : ∀ (τ : List Pos) {t : LTerm} {t' : CTerm} (σ : List Pos),
    Refines t t'.1 → lambdaRS.Valid t σ → lambdaRS.Valid t τ →
      distRS.names (simDeriv (simTgtDeriv t' τ) (lambdaRS.proj t σ τ)) =
        distRS.names (simDeriv t' σ) \ distRS.names (simDeriv t' τ) := by
  intro τ
  induction τ with
  | nil =>
    intro t t' σ hr hσ _
    rw [ResidualSystem.proj_nil_right lambda_orthogonal hσ]
    simp [simDeriv, distRS.names, simTgtDeriv]
  | cons q τ' ih =>
    intro t t' σ hr hσ hτ
    obtain ⟨hq, hτ'⟩ := hτ
    have hvq : lambdaRS.Valid t [q] := ResidualSystem.valid_singleton hq
    have hfull : lambdaRS.Valid t ([q] ++ τ') := ⟨hq, hτ'⟩
    have hpe := ResidualSystem.proj_append_right lambda_orthogonal (σ := σ) (τ := [q]) (ρ := τ')
      hσ hfull
    have hr' := simulation_canonical hr hq
    have hrb : Refines (lambdaRS.tgt t ([q] ++ τ')) (simTgtDeriv t' ([q] ++ τ')).1 :=
      (simDeriv_valid hr hfull).2
    have hv1 : lambdaRS.Valid (lambdaRS.tgt t ([q] ++ τ'))
        (lambdaRS.proj t σ ([q] ++ τ')) := ResidualSystem.proj_valid lambda_orthogonal hσ hfull
    have hv2 : lambdaRS.Valid (lambdaRS.tgt t ([q] ++ τ'))
        (lambdaRS.proj (lambdaRS.tgt t [q]) (lambdaRS.proj t σ [q]) τ') :=
      ResidualSystem.proj_valid lambda_orthogonal (ResidualSystem.proj_valid lambda_orthogonal hσ hvq) hτ'
    have hcomp := (compatibility hrb hv1 hv2 hpe).2
    have hn := (distRS.permEq_iff_names (simDeriv_valid hrb hv1).1 (simDeriv_valid hrb hv2).1).1 hcomp
    have hIH := ih (t := lambdaRS.contract t q) (t' := simTgt t' q) (lambdaRS.proj t σ [q]) hr'
      (ResidualSystem.proj_valid lambda_orthogonal hσ hvq) hτ'
    have hS := single_gen σ {q} [q] hr hσ (by simpa using hq)
      ((ResidualSystem.isCompleteDevelopment_singleton lambda_orthogonal hq).2 rfl)
    simp only [Finset.singleton_biUnion] at hS
    change distRS.names (simDeriv (simTgtDeriv t' ([q] ++ τ')) (lambdaRS.proj t σ ([q] ++ τ'))) = _
    rw [hn]
    change distRS.names (simDeriv (simTgtDeriv (simTgt t' q) τ')
      (lambdaRS.proj (lambdaRS.contract t q) (lambdaRS.proj t σ [q]) τ')) = _
    rw [hIH, simNames_cons]
    change distRS.names (simDeriv (simTgt t' q) (lambdaRS.proj t σ [q])) \ _ = _
    have hS' : distRS.names (simDeriv (simTgt t' q) (lambdaRS.proj t σ [q])) =
        distRS.names (simDeriv t' σ) \ simRes t'.1 q := hS
    rw [hS']
    ext ℓ
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto

/-- **Generalized cube lemma**: `(σ/t')/(τ/t') ≡ (σ/τ)/(t'/τ)`. -/
theorem generalized_cube_lemma {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) :
    distRS.PermEq (simTgtDeriv t' τ) (distRS.proj t' (simDeriv t' σ) (simDeriv t' τ))
      (simDeriv (simTgtDeriv t' τ) (lambdaRS.proj t σ τ)) := by
  have hvσ := (simDeriv_valid hr hσ).1
  have hvτ := (simDeriv_valid hr hτ).1
  have hv1 := ResidualSystem.proj_valid distRS.orthogonal hvσ hvτ
  have hpj := ResidualSystem.proj_valid lambda_orthogonal hσ hτ
  have hv2 := (simDeriv_valid (simDeriv_valid hr hτ).2 hpj).1
  rw [← tgt_simDeriv] at hv2 ⊢
  rw [distRS.permEq_iff_names hv1 hv2, distRS.names_proj hvσ hvτ, tgt_simDeriv]
  exact (gen_names τ σ hr hσ hτ).symm

/-! ### Algebraic simulation -/

section AlgebraicSimulation

variable {t : LTerm} {t' : CTerm} (hr : Refines t t'.1)

/-- `σ ↦ σ/t'` on derivations. -/
def simDerivFrom (σ : LDeriv t) : distRS.DerivFrom t' :=
  ⟨simDeriv t' σ.1, (simDeriv_valid hr σ.2).1⟩

/-- `[σ] ↦ [σ/t']`, well defined by compatibility. -/
def algSim : DSpaceLam t → DSpaceDist t' :=
  Quotient.map (simDerivFrom hr) fun σ τ h => (compatibility hr σ.2 τ.2 h).2

theorem algSim_mk (σ : LDeriv t) :
    algSim hr (ResidualSystem.DSpace.mk σ) = ResidualSystem.DSpace.mk (simDerivFrom hr σ) := rfl

theorem algSim_bot : algSim hr ⊥ = ⊥ := rfl

theorem algSim_sup (x y : DSpaceLam t) : algSim hr (x ⊔ y) = algSim hr x ⊔ algSim hr y := by
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  rw [ResidualSystem.DSpace.mk_sup_mk, algSim_mk, algSim_mk, algSim_mk,
    ResidualSystem.DSpace.mk_sup_mk, ResidualSystem.DSpace.mk_eq_mk]
  change distRS.PermEq t'
    (simDeriv t' (lambdaRS.join t σ.1 τ.1))
    (distRS.join t' (simDeriv t' σ.1) (simDeriv t' τ.1))
  rw [ResidualSystem.join, simDeriv_append, ResidualSystem.join]
  have hs := (simDeriv_valid hr σ.2).1
  have ht := (simDeriv_valid hr τ.2).1
  have hc := generalized_cube_lemma hr τ.2 σ.2
  rw [← tgt_simDeriv] at hc
  have hp := ResidualSystem.proj_valid distRS.orthogonal ht hs
  have hl := (simDeriv_valid (simDeriv_valid hr σ.2).2
    (ResidualSystem.proj_valid lambda_orthogonal τ.2 σ.2)).1
  rw [← tgt_simDeriv] at hl
  rw [← tgt_simDeriv t' σ.1]
  exact ⟨(ResidualSystem.prefix_append_iff distRS.orthogonal hs hl hp).1 hc.2,
    (ResidualSystem.prefix_append_iff distRS.orthogonal hs hp hl).1 hc.1⟩

/-- **Corollary (Algebraic simulation)**: for `t' ⋉ t`, the map `𝔻_λ(t) → 𝔻^dist(t')`,
`[σ] ↦ [σ/t']` is a morphism of upper semilattices (with bottom). -/
def algebraicSimulation : SupBotHom (DSpaceLam t) (DSpaceDist t') where
  toFun := algSim hr
  map_sup' := algSim_sup hr
  map_bot' := algSim_bot hr

theorem algebraicSimulation_mono : Monotone (algebraicSimulation hr) :=
  OrderHomClass.mono (algebraicSimulation hr)

end AlgebraicSimulation

end Thesis
