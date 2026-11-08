/-
# Chapter 5: Factorization of derivations — Appendix

Auxiliary definitions and lemmas for Chapter 5 (`08-18-sieving.tex` and quotient representative
helpers):
* Defining equation and validity of `sieve` (`sieve_eq_cons`, `sieve_valid`).
* Representatives of permutation-equivalence classes (`rep`, `tgt_rep`).
* The leftmost coarse step: the pre-order `PosLt` on positions, `leftmost_least`, and
  `sieve_least` (the sieve is below every prefix covering all the names).
-/
import Thesis.Chapter5FactorizationDefs

namespace Thesis

open LTerm ResidualSystem

/-- Permutation equivalence with the empty distributive trace forces literal emptiness. -/
theorem dist_perm_empty {u : CTerm} {σ : List Label} (hσ : distRS.Valid u σ)
    (h : distRS.PermEq u σ []) : σ = [] := by
  have hn := (distRS.permEq_iff_names hσ (by trivial)).mp h
  simpa [distRS.names] using hn

/-- The generalized cube transports garbage to every residual projection. -/
theorem garbage_proj_core {t : LTerm} {t' : CTerm} {σ τ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ)
    (hg : IsGarbage t' σ) : IsGarbage (simTgtDeriv t' τ) (lambdaRS.proj t σ τ) := by
  have hh := generalized_cube_lemma hr hσ hτ
  have hv := (simDeriv_valid (simDeriv_valid hr hτ).2
    (proj_valid lambda_orthogonal hσ hτ)).1
  rw [show simDeriv t' σ = [] from hg, proj_nil_left] at hh
  exact dist_perm_empty hv ⟨hh.2, hh.1⟩

/-- Garbage is downwards closed (`06-01-garbage.tex`). -/
theorem garbage_prefix_core {t : LTerm} {t' : CTerm} {σ τ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ)
    (hg : IsGarbage t' σ) (hle : lambdaRS.Prefix t τ σ) : IsGarbage t' τ := by
  have hp := simDeriv_prefix hr hτ hσ hle
  change simDeriv t' σ = [] at hg
  unfold Prefix at hp
  rw [hg, proj_nil_right distRS.orthogonal (simDeriv_valid hr hτ).1] at hp
  exact hp

/-- Permutation equivalence preserves the literal emptiness of simulation traces. -/
theorem garbage_congr_core {t : LTerm} {t' : CTerm} {σ τ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ)
    (h : lambdaRS.PermEq t σ τ) : IsGarbage t' σ ↔ IsGarbage t' τ := by
  exact ⟨fun hg => garbage_prefix_core hr hσ hτ hg h.2,
    fun hg => garbage_prefix_core hr hτ hσ hg h.1⟩

/-- Garbage is closed under joins. -/
theorem garbage_join_core {t : LTerm} {t' : CTerm} {σ τ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) :
    IsGarbage t' (lambdaRS.join t σ τ) ↔ IsGarbage t' σ ∧ IsGarbage t' τ := by
  have hv : lambdaRS.Valid t (lambdaRS.join t σ τ) :=
    (lambdaRS.valid_append _ _ _).mpr ⟨hσ, proj_valid lambda_orthogonal hτ hσ⟩
  constructor
  · intro hg
    exact ⟨garbage_prefix_core hr hv hσ hg (prefix_join_left lambda_orthogonal hσ hτ),
      garbage_prefix_core hr hv hτ hg (prefix_join_right lambda_orthogonal hσ hτ)⟩
  · rintro ⟨hs, ht⟩
    change simDeriv t' (σ ++ lambdaRS.proj t τ σ) = []
    rw [simDeriv_append, show simDeriv t' σ = [] from hs,
      show simDeriv (simTgtDeriv t' σ) (lambdaRS.proj t τ σ) = [] from
        garbage_proj_core hr hτ hσ ht]
    rfl

/-- The sieve's recursion always produces a composable derivation, regardless of fuel. -/
theorem sieveAux_valid (fuel : ℕ) {t : LTerm} {t' : CTerm} {σ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) :
    lambdaRS.Valid t (sieveAux fuel t t' σ) := by
  induction fuel generalizing t t' σ with
  | zero => trivial
  | succ fuel ih =>
    unfold sieveAux
    split
    · trivial
    · rename_i p hp
      have hm := List.mem_of_find?_eq_some hp
      have hstep := LTerm.mem_redexes.mp hm
      have hv := proj_valid lambda_orthogonal hσ (valid_singleton hstep)
      rw [show lambdaRS.tgt t [p] = contractAt t p from rfl] at hv
      exact ⟨hstep, ih (simulation_canonical hr hstep) hv⟩

@[simp] theorem names_sim_singleton (t' : CTerm) (p : Pos) :
    distRS.names (simDeriv t' [p]) = simRes t'.1 p := by
  simp only [simDeriv, List.append_nil]
  exact distRS.names_dev t' (simRes t'.1 p)

theorem sim_singleton_garbage (t' : CTerm) (p : Pos) :
    IsGarbage t' [p] ↔ simRes t'.1 p = ∅ := by
  change (simRes t'.1 p).sort (· ≤ ·) ++ [] = [] ↔ _
  rw [List.append_nil, ← List.length_eq_zero_iff, Finset.length_sort, Finset.card_eq_zero]

/-- The strict measure decrease from `08-18-sieving.tex`. -/
theorem coarse_measure_decreases {t : LTerm} {t' : CTerm} {σ : List Pos} {p : Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) (hp : Coarse t t' σ p) :
    (simDeriv (simTgt t' p) (lambdaRS.proj t σ [p])).length < (simDeriv t' σ).length := by
  have hvp := valid_singleton hp.1
  have hsimσ := (simDeriv_valid hr hσ).1
  have hsimp := (simDeriv_valid hr hvp).1
  have hsmall := (simDeriv_valid (simulation_canonical hr hp.1)
    (proj_valid lambda_orthogonal hσ hvp)).1
  have hpre := (distRS.prefix_iff_subset hsimp hsimσ).mp (simDeriv_prefix hr hvp hσ hp.2.1)
  rw [names_sim_singleton] at hpre
  have hc := Finset.card_lt_card (Finset.sdiff_ssubset hpre hp.2.2)
  have he := generalized_cube_lemma hr hσ hvp
  have hvproj := proj_valid distRS.orthogonal hsimσ hsimp
  rw [tgt_simDeriv] at hvproj
  have hn := (distRS.permEq_iff_names hvproj hsmall).mp he
  rw [distRS.names_proj hsimσ hsimp, names_sim_singleton] at hn
  rw [distRS.length_eq_card_names hsimσ, distRS.length_eq_card_names hsmall, ← hn]
  exact hc

/-- The redex selected by `find?` is coarse. -/
theorem find_coarse {t : LTerm} {t' : CTerm} {σ : List Pos} {p : Pos}
    (h : (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
      (simRes t'.1 p).Nonempty)) = some p) : Coarse t t' σ p := by
  exact ⟨LTerm.mem_redexes.mp (List.mem_of_find?_eq_some h), by
    simpa only [decide_eq_true_eq] using List.find?_some h⟩

/-- Any two sufficient fuel bounds produce the same sieve. -/
theorem sieveAux_fuel_eq {t : LTerm} {t' : CTerm} {σ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) (n m : ℕ)
    (hn : (simDeriv t' σ).length ≤ n) (hm : (simDeriv t' σ).length ≤ m) :
    sieveAux n t t' σ = sieveAux m t t' σ := by
  induction n generalizing t t' σ m with
  | zero =>
    have hnone : (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
        (simRes t'.1 p).Nonempty)) = none := by
      cases h : (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
          (simRes t'.1 p).Nonempty)) with
      | none => rfl
      | some p => have hh := coarse_measure_decreases hr hσ (find_coarse h); omega
    cases m <;> simp only [sieveAux, hnone]
  | succ n ih =>
    cases m with
    | zero =>
      have hnone : (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
          (simRes t'.1 p).Nonempty)) = none := by
        cases h : (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
            (simRes t'.1 p).Nonempty)) with
        | none => rfl
        | some p => have hh := coarse_measure_decreases hr hσ (find_coarse h); omega
      simp only [sieveAux, hnone]
    | succ m =>
      simp only [sieveAux]
      split
      · rfl
      · rename_i p hfind
        have hp := find_coarse hfind
        have hh := coarse_measure_decreases hr hσ hp
        have hv := proj_valid lambda_orthogonal hσ (valid_singleton hp.1)
        rw [show lambdaRS.tgt t [p] = contractAt t p from rfl] at hv
        exact congrArg (List.cons p) (ih (simulation_canonical hr hp.1) hv m (by omega) (by omega))

theorem find_leftmost {α : Type*} [DecidableEq α] {xs : List α} {p : α} {f : α → Bool}
    (hp : p ∈ xs) (hf : f p = true)
    (hleft : ∀ q ∈ xs.takeWhile (fun q => decide (q ≠ p)), f q = false) :
    xs.find? f = some p := by
  induction xs with
  | nil => simp at hp
  | cons q xs ih =>
    by_cases he : q = p
    · subst q; simp [hf]
    · have hleft' := hleft
      simp only [List.takeWhile_cons, decide_eq_true_eq, if_pos he, List.mem_cons,
        forall_eq_or_imp] at hleft'
      have hp' : p ∈ xs := (List.mem_cons.mp hp).resolve_left (Ne.symm he)
      have hq : f q = false := hleft q (by simp [he])
      have ht := hleft'.2
      simp only [List.find?_cons, hq, Bool.false_eq_true, ↓reduceIte]
      exact ih hp' ht

private theorem find_congr_mem {α : Type*} (xs : List α) (f g : α → Bool)
    (h : ∀ a ∈ xs, f a = g a) : xs.find? f = xs.find? g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

theorem sieveAux_congr (fuel : ℕ) {t : LTerm} {t' : CTerm} {σ τ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ)
    (h : lambdaRS.PermEq t σ τ) : sieveAux fuel t t' σ = sieveAux fuel t t' τ := by
  induction fuel generalizing t t' σ τ with
  | zero => rfl
  | succ fuel ih =>
    have he : (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
        (simRes t'.1 p).Nonempty)) =
      (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] τ ∧
        (simRes t'.1 p).Nonempty)) := by
      apply find_congr_mem
      intro p hp
      have hv := valid_singleton (R := lambdaRS) (t := t) (LTerm.mem_redexes.mp hp)
      have hh : lambdaRS.Prefix t [p] σ ↔ lambdaRS.Prefix t [p] τ :=
        ⟨fun hp => prefix_trans lambda_orthogonal hv hσ hτ hp h.1,
          fun hp => prefix_trans lambda_orthogonal hv hτ hσ hp h.2⟩
      simp only [hh]
    simp only [sieveAux]
    rw [← he]
    split
    · rename_i hfind; rw [hfind]
    · rename_i p hfind
      rw [hfind]
      dsimp only
      have hp := find_coarse hfind
      have hvs := proj_valid lambda_orthogonal hσ (valid_singleton hp.1)
      have hvt := proj_valid lambda_orthogonal hτ (valid_singleton hp.1)
      have hh : lambdaRS.PermEq (contractAt t p) (lambdaRS.proj t σ [p]) (lambdaRS.proj t τ [p]) :=
        ⟨prefix_proj lambda_orthogonal hσ hτ (valid_singleton hp.1) h.1,
          prefix_proj lambda_orthogonal hτ hσ (valid_singleton hp.1) h.2⟩
      exact congrArg (List.cons p) (ih (simulation_canonical hr hp.1) hvs hvt hh)

/-- With a deterministic choice, equivalent derivations have literally equal sieves. -/
theorem sieve_eq_of_permEq {t : LTerm} {t' : CTerm} {σ τ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ)
    (h : lambdaRS.PermEq t σ τ) : sieve t t' σ = sieve t t' τ := by
  let n := max (simDeriv t' σ).length (simDeriv t' τ).length
  exact (sieveAux_fuel_eq hr hσ n _ (le_max_left _ _) le_rfl).symm.trans
    ((sieveAux_congr n hr hσ hτ h).trans
      (sieveAux_fuel_eq hr hτ n _ (le_max_right _ _) le_rfl))

/-- Factoring off a prefix step gives the original derivation modulo permutation. -/
theorem prefix_step_factor {t : LTerm} {σ : List Pos} {p : Pos}
    (hσ : lambdaRS.Valid t σ) (hp : lambdaRS.isStep t p) (hle : lambdaRS.Prefix t [p] σ) :
    lambdaRS.PermEq t (p :: lambdaRS.proj t σ [p]) σ := by
  have hh := permGen_join_comm lambda_orthogonal (valid_singleton hp) hσ
  change lambdaRS.proj t [p] σ = [] at hle
  simp only [ResidualSystem.join, List.singleton_append, hle, List.append_nil] at hh
  exact (permGen_iff_permEq lambda_orthogonal (hh.valid_left lambda_orthogonal)
    (hh.valid_right lambda_orthogonal)).mp hh

/-- Every fuelled sieve is a prefix (`08-19`, sieve-is-prefix). -/
theorem sieveAux_prefix (fuel : ℕ) {t : LTerm} {t' : CTerm} {σ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) :
    lambdaRS.Prefix t (sieveAux fuel t t' σ) σ := by
  induction fuel generalizing t t' σ with
  | zero => rfl
  | succ fuel ih =>
    unfold sieveAux
    split
    · rfl
    · rename_i p hfind
      have hp := find_coarse hfind
      have hvp := valid_singleton hp.1
      have hproj := proj_valid lambda_orthogonal hσ hvp
      have hr' := simulation_canonical hr hp.1
      have hv := sieveAux_valid fuel hr' hproj
      have hi := ih hr' hproj
      have hh := (prefix_append_iff lambda_orthogonal hvp hv hproj).mp hi
      exact prefix_trans lambda_orthogonal
        ((lambdaRS.valid_append _ _ _).mpr ⟨hvp, hv⟩)
        ((lambdaRS.valid_append _ _ _).mpr ⟨hvp, hproj⟩) hσ hh (prefix_step_factor hσ hp.1 hp.2.1).1

/-- Garbage simulation leaves the annotated term literally unchanged. -/
theorem simTgt_eq_of_garbage {t' : CTerm} {p : Pos} (hg : IsGarbage t' [p]) : simTgt t' p = t' := by
  have he := (sim_singleton_garbage t' p).mp hg
  unfold simTgt
  rw [he, ResidualSystem.dev_empty distRS.orthogonal]
  rfl

/-- Garbage cannot create a represented redex: reverse simulation supplies its ancestor,
and the cube identifies its residual (`08-19`, creation cases). -/
theorem garbage_creates_core {t : LTerm} {t' : CTerm} {p q : Pos}
    (hr : Refines t t'.1) (hc : LCreates t p q) (hg : IsGarbage t' [p]) :
    IsGarbage (simTgt t' p) [q] := by
  apply (sim_singleton_garbage _ _).mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ℓ hℓ
  have ht := simTgt_eq_of_garbage hg
  have hℓ' : ℓ ∈ simRes t'.1 q := ht ▸ hℓ
  obtain ⟨v, hv⟩ := DTerm.hasRedex_iff_step.mp (simRes_isStep hℓ')
  obtain ⟨r, hrstep, hrimage⟩ := hv.simulation_position hr
  have hcube := basic_cube_lemma hr hrstep hc.1
  rw [(sim_singleton_garbage t' p).mp hg, ResidualSystem.dev_empty distRS.orthogonal] at hcube
  change simRes t'.1 r = _ at hcube
  have hm : ℓ ∈ (lambdaRS.res t p r).biUnion (fun r' => simRes (simTgt t' p).1 r') :=
    hcube ▸ hrimage
  obtain ⟨r', hr', hℓr⟩ := Finset.mem_biUnion.mp hm
  have he := simRes_position_unique (simTgt t' p).2 hℓr hℓ
  subst r'
  exact hc.2.2 r hrstep hr'

/-- If a redex of `t` is not simulated in `u`, then nothing below it is. -/
theorem simRes_empty_below {t : LTerm} {u : DTerm} (hr : Refines t u) :
    ∀ (p w : Pos), LTerm.isRedexAt t p = true → simRes u p = ∅ → simRes u (p ++ w) = ∅ := by
  induction hr with
  | var n τ =>
    intro p w hp _
    rcases p with _ | ⟨i, p⟩ <;> simp [LTerm.isRedexAt, LTerm.subAt, LTerm.isRedex] at hp
  | lam ℓ h ih =>
    intro p w hp hs
    rcases p with _ | ⟨i, p⟩
    · simp [LTerm.isRedexAt, LTerm.subAt, LTerm.isRedex] at hp
    · rcases i with _ | i
      · simp only [LTerm.isRedexAt_lam_zero] at hp
        simpa [simRes] using ih p w hp (by simpa [simRes] using hs)
      · simp at hp
  | @app t s t' ss ht hs iht ihs =>
    intro p w hp hz
    rcases p with _ | ⟨i, p⟩
    · cases ht <;> first
        | (simp [simRes] at hz; done)
        | (simp [LTerm.isRedexAt, LTerm.subAt, LTerm.isRedex] at hp; done)
    · rcases i with _ | _ | i
      · simp only [LTerm.isRedexAt_app_zero] at hp
        have hz' : simRes t' p = ∅ := by
          cases t' <;> simpa [simRes] using hz
        have := iht p w hp hz'
        cases t' <;> simpa [simRes] using this
      · replace hp : LTerm.isRedexAt s p = true := by simpa using hp
        have hall : ∀ s' ∈ ss, simRes s' p = ∅ := by
          intro s' hs'
          have h0 : (ss.map (simRes · p)).foldr (· ∪ ·) ∅ = ∅ := by simpa [simRes] using hz
          have : ∀ (l : List DTerm), (l.map (simRes · p)).foldr (· ∪ ·) ∅ = ∅ →
              ∀ s' ∈ l, simRes s' p = ∅ := by
            intro l
            induction l with
            | nil => simp
            | cons a l ih =>
              intro h s' hs'
              simp only [List.map_cons, List.foldr_cons, Finset.union_eq_empty] at h
              rcases List.mem_cons.mp hs' with rfl | hm
              · exact h.1
              · exact ih h.2 s' hm
          exact this ss h0 s' hs'
        have hall' : ∀ s' ∈ ss, simRes s' (p ++ w) = ∅ := fun s' hs' => ihs s' hs' p w hp (hall s' hs')
        show simRes (t'.app ss) (1 :: (p ++ w)) = ∅
        have e : simRes (t'.app ss) (1 :: (p ++ w)) =
            (ss.map (simRes · (p ++ w))).foldr (· ∪ ·) ∅ := by simp [simRes]
        rw [e, List.map_congr_left hall']
        have key : ∀ l : List DTerm,
            (l.map (fun _ => (∅ : Finset Label))).foldr (· ∪ ·) ∅ = ∅ := by
          intro l; induction l <;> simp_all
        exact key ss
      · simp at hp

/-- Garbage only duplicates garbage. -/
theorem garbage_duplicates_core {t : LTerm} {t' : CTerm} {p q : Pos}
    (hr : Refines t t'.1) (hp : lambdaRS.isStep t p)
    (hdup : 1 < (lambdaRS.res t p q).card) (hg : IsGarbage t' [p]) : IsGarbage t' [q] := by
  rw [sim_singleton_garbage] at hg ⊢
  have hres : lambdaRS.res t p q = residuals t p q := rfl
  rw [hres] at hdup
  unfold residuals at hdup
  by_cases h1 : q = p
  · simp [h1] at hdup
  by_cases h2 : p <+: q
  · obtain ⟨w, rfl⟩ := h2
    have hw : ∃ r, w = 1 :: r := by
      simp only [h1, ite_false, List.drop_left'] at hdup
      rw [if_pos (List.prefix_append p w)] at hdup
      rcases w with _ | ⟨i, w⟩
      · simp at h1
      rcases i with _ | _ | i
      · rcases w with _ | ⟨j, w⟩
        · simp at hdup
        · rcases j with _ | j <;> (rcases h : t.subAt p with _ | _ | _ | ⟨_ | _ | _, _⟩ <;> simp_all)
      · exact ⟨w, rfl⟩
      · rcases h : t.subAt p with _ | _ | _ | ⟨_ | _ | _, _⟩ <;> simp_all
    obtain ⟨r, rfl⟩ := hw
    exact simRes_empty_below hr p _ (by simpa using hp) hg
  · simp [h1, h2] at hdup

/-- A derivation that is not garbage has a coarse step (`08-19`, Characterization of garbage,
`2 ⟹ 3` contrapositive). -/
theorem exists_coarse_of_not_garbage : ∀ (σ : List Pos) {t : LTerm} {t' : CTerm},
    Refines t t'.1 → lambdaRS.Valid t σ → ¬ IsGarbage t' σ → ∃ a, Coarse t t' σ a := by
  intro σ
  induction σ with
  | nil => intro t t' _ _ hg; exact absurd rfl hg
  | cons p σ' ih =>
    intro t t' hr hσ hg
    obtain ⟨hp, hσ'⟩ := hσ
    have hvfull : lambdaRS.Valid t (p :: σ') := ⟨hp, hσ'⟩
    have hpre : lambdaRS.Prefix t [p] (p :: σ') :=
      (prefix_iff_exists lambda_orthogonal (valid_singleton hp) hvfull).2
        ⟨σ', hσ', prefix_refl lambda_orthogonal hvfull, prefix_refl lambda_orthogonal hvfull⟩
    by_cases hgp : IsGarbage t' [p]
    · have hT := simTgt_eq_of_garbage hgp
      have hr' : Refines (contractAt t p) (simTgt t' p).1 := simulation_canonical hr hp
      have hg' : ¬ IsGarbage (simTgt t' p) σ' := by
        intro h
        apply hg
        change simDeriv t' (p :: σ') = []
        rw [simDeriv, show simDeriv (simTgt t' p) σ' = [] from h,
          show distRS.dev t' (simRes t'.1 p) = [] by
            rw [(sim_singleton_garbage t' p).mp hgp, ResidualSystem.dev_empty distRS.orthogonal]]
        rfl
      obtain ⟨q, hqs, hqpre, hqne⟩ := ih hr' hσ' hg'
      by_cases hc : LCreates t p q
      · exfalso
        have := garbage_creates_core hr hc hgp
        rw [sim_singleton_garbage] at this
        exact (Finset.nonempty_iff_ne_empty.mp hqne) this
      · obtain ⟨a, ha, hqa⟩ : ∃ a, lambdaRS.isStep t a ∧ q ∈ lambdaRS.res t p a := by
          by_contra hne
          push Not at hne
          exact hc ⟨hp, hqs, fun a ha => hne a ha⟩
        have hcube := basic_cube_lemma hr ha hp
        rw [(sim_singleton_garbage t' p).mp hgp, ResidualSystem.dev_empty distRS.orthogonal] at hcube
        change simRes t'.1 a = _ at hcube
        have hne : (simRes t'.1 a).Nonempty := by
          rw [hcube]
          obtain ⟨ℓ, hℓ⟩ := hqne
          exact ⟨ℓ, Finset.mem_biUnion.mpr ⟨q, hqa, hℓ⟩⟩
        have hcard : (lambdaRS.res t p a).card ≤ 1 := by
          by_contra hlt
          push Not at hlt
          have := (sim_singleton_garbage t' a).mp (garbage_duplicates_core hr hp hlt hgp)
          exact (Finset.nonempty_iff_ne_empty.mp hne) this
        have hres : lambdaRS.res t p a = {q} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr ⟨hqa, fun x hx => ?_⟩
          exact Finset.card_le_one.mp hcard x hx q hqa
        refine ⟨a, ha, ?_, hne⟩
        have hv : lambdaRS.Valid t ([p] ++ σ') := ⟨hp, hσ'⟩
        have hpe := proj_append_right lambda_orthogonal (σ := [a]) (τ := [p]) (ρ := σ')
          ⟨ha, trivial⟩ hv
        have hproj : lambdaRS.proj t [a] [p] = [q] := by
          show lambdaRS.dev (lambdaRS.tgt t [p]) (lambdaRS.resSetDeriv t {a} [p]) ++
            lambdaRS.proj _ [] _ = [q]
          rw [show lambdaRS.resSetDeriv t {a} [p] = {q} by
            simp [ResidualSystem.resSetDeriv, ResidualSystem.resSet]; exact hres]
          show lambdaRS.dev (lambdaRS.contract t p) {q} ++ [] = [q]
          rw [ResidualSystem.dev_singleton lambda_orthogonal hqs]
          rfl
        rw [hproj] at hpe
        have h0 : lambdaRS.proj (lambdaRS.tgt t [p]) [q] σ' = [] := hqpre
        rw [h0] at hpe
        have hva := proj_valid lambda_orthogonal (valid_singleton ha) hv
        have := hpe.1
        unfold ResidualSystem.Prefix at this
        rw [proj_nil_right lambda_orthogonal hva] at this
        exact this
    · exact ⟨p, hp, hpre, Finset.nonempty_iff_ne_empty.mpr
        (fun h => hgp ((sim_singleton_garbage t' p).mpr h))⟩

/-- `σ ⇂ t' = ε` iff there are no coarse steps. -/
theorem sieve_eq_nil_iff {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) : sieve t t' σ = [] ↔ ∀ p, ¬ Coarse t t' σ p := by
  constructor
  · intro h p hp
    have hdec := coarse_measure_decreases hr hσ hp
    obtain ⟨n, hn⟩ : ∃ n, (simDeriv t' σ).length = n + 1 := ⟨(simDeriv t' σ).length - 1, by omega⟩
    have hfind : ∃ q, (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
        (simRes t'.1 p).Nonempty)) = some q := by
      cases hf : (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
        (simRes t'.1 p).Nonempty)) with
      | some q => exact ⟨q, rfl⟩
      | none =>
        have := List.find?_eq_none.mp hf p (LTerm.mem_redexes.mpr hp.1)
        simp only [decide_eq_true_eq] at this
        exact absurd ⟨hp.2.1, hp.2.2⟩ this
    obtain ⟨q, hq⟩ := hfind
    unfold sieve at h
    rw [hn, sieveAux, hq] at h
    simp at h
  · intro h
    unfold sieve
    have hnone : (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
        (simRes t'.1 p).Nonempty)) = none := by
      cases hf : (redexes t).find? (fun p => decide (lambdaRS.Prefix t [p] σ ∧
        (simRes t'.1 p).Nonempty)) with
      | none => rfl
      | some q => exact absurd (find_coarse hf) (h q)
    cases (simDeriv t' σ).length with
    | zero => rfl
    | succ n => rw [sieveAux, hnone]

/-- The defining equation of sieving when a coarse step exists. -/
theorem sieve_eq_cons {t : LTerm} {t' : CTerm} {σ : List Pos} {p : Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hp : Coarse t t' σ p)
    (hleft : ∀ q ∈ (redexes t).takeWhile (· ≠ p), ¬ Coarse t t' σ q) :
    sieve t t' σ = p :: sieve (contractAt t p) (simTgt t' p) (lambdaRS.proj t σ [p]) := by
  have hfind : (redexes t).find? (fun q => decide (lambdaRS.Prefix t [q] σ ∧
      (simRes t'.1 q).Nonempty)) = some p := by
    apply find_leftmost (LTerm.mem_redexes.mpr hp.1) (by simpa using hp.2)
    intro q hq
    apply decide_eq_false_iff_not.mpr
    intro hh
    exact hleft q hq ⟨LTerm.mem_redexes.mp
      ((List.takeWhile_subset (fun q => decide (q ≠ p))) hq), hh⟩
  have hdec := coarse_measure_decreases hr hσ hp
  obtain ⟨n, hn⟩ : ∃ n, (simDeriv t' σ).length = n + 1 := by
    exact ⟨(simDeriv t' σ).length - 1, by omega⟩
  unfold sieve
  rw [hn, sieveAux, hfind]
  dsimp only
  congr 1
  apply sieveAux_fuel_eq (simulation_canonical hr hp.1)
    (proj_valid lambda_orthogonal hσ (valid_singleton hp.1))
  · omega
  · exact le_rfl

theorem sieve_valid {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) : lambdaRS.Valid t (sieve t t' σ) := by
  exact sieveAux_valid _ hr hσ

/-- The projection after a (fuelled) sieve is garbage (`08-19`, projection after sieving). -/
theorem projection_after_sieveAux_garbage (n : ℕ) {t : LTerm} {t' : CTerm} {σ : List Pos}
    (hr : Refines t t'.1) (hσ : lambdaRS.Valid t σ) (hn : (simDeriv t' σ).length ≤ n) :
    IsGarbage (simTgtDeriv t' (sieveAux n t t' σ)) (lambdaRS.proj t σ (sieveAux n t t' σ)) := by
  induction n generalizing t t' σ with
  | zero =>
    have : IsGarbage t' σ := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
    simpa [sieveAux, proj_nil_right lambda_orthogonal hσ, simTgtDeriv] using this
  | succ n ih =>
    unfold sieveAux
    split
    · rename_i hnone
      have hno : ∀ p, ¬ Coarse t t' σ p := fun p hp => by
        have := List.find?_eq_none.mp hnone p (LTerm.mem_redexes.mpr hp.1)
        simp only [decide_eq_true_eq] at this
        exact this ⟨hp.2.1, hp.2.2⟩
      by_contra hng
      have hg : ¬ IsGarbage t' σ := by
        simpa [simTgtDeriv, proj_nil_right lambda_orthogonal hσ] using hng
      obtain ⟨a, ha⟩ := exists_coarse_of_not_garbage σ hr hσ hg
      exact hno a ha
    · rename_i p hfind
      have hp := find_coarse hfind
      have hvp := valid_singleton hp.1
      have hdec := coarse_measure_decreases hr hσ hp
      have hproj := proj_valid lambda_orthogonal hσ hvp
      have hr' := simulation_canonical hr hp.1
      have hih := ih hr' hproj (by omega)
      have hv := sieveAux_valid n hr' hproj
      have hfull : lambdaRS.Valid t ([p] ++ sieveAux n (contractAt t p) (simTgt t' p)
          (lambdaRS.proj t σ [p])) := (lambdaRS.valid_append _ _ _).mpr ⟨hvp, hv⟩
      have hpe := proj_append_right lambda_orthogonal (σ := σ) (τ := [p]) hσ hfull
      exact (garbage_congr_core (simDeriv_valid hr hfull).2
        (proj_valid lambda_orthogonal hσ hfull) (proj_valid lambda_orthogonal (t := lambdaRS.tgt t [p]) hproj hv) hpe).mpr hih

/-- A valid λ^dist derivation has length at most the number of λs of its source. -/
theorem dist_length_add_size : ∀ (ρ : List Label) (u : CTerm), distRS.Valid u ρ →
    ρ.length + (distRS.tgt u ρ).1.size = u.1.size := by
  intro ρ
  induction ρ with
  | nil => intro u _; rw [show distRS.tgt u [] = u from rfl]; simp
  | cons ℓ ρ ih =>
    intro u hv
    obtain ⟨hℓ, hv'⟩ := hv
    have hstep : DStep u.1 ℓ (u.1.contract ℓ) :=
      (dStep_iff_hasRedex u.2).2 ⟨hℓ, rfl⟩
    have h1 := size_dStep u.2 hstep
    have h2 := ih (distRS.contract u ℓ) hv'
    change ρ.length + (distRS.tgt (distRS.contract u ℓ) ρ).1.size = (u.1.contract ℓ).size at h2
    simp only [List.length_cons]
    rw [show distRS.tgt u (ℓ :: ρ) = distRS.tgt (distRS.contract u ℓ) ρ from rfl]
    omega

/-- The sieve is no longer than the simulation residual. -/
theorem sieveAux_length_le : ∀ (n : ℕ) {t : LTerm} {t' : CTerm} {σ : List Pos},
    Refines t t'.1 → lambdaRS.Valid t σ →
      (sieveAux n t t' σ).length ≤ (simDeriv t' σ).length := by
  intro n
  induction n with
  | zero => intros; simp [sieveAux]
  | succ n ih =>
    intro t t' σ hr hσ
    unfold sieveAux
    split
    · simp
    · rename_i p hfind
      have hp := find_coarse hfind
      have hdec := coarse_measure_decreases hr hσ hp
      have hproj := proj_valid lambda_orthogonal hσ (valid_singleton hp.1)
      have := ih (simulation_canonical hr hp.1) hproj
      simp only [List.length_cons]
      omega

/-- Valid derivations of bounded length out of `t` form a finite set. -/
theorem valid_length_finite : ∀ (B : ℕ) (t : LTerm),
    {s : List Pos | lambdaRS.Valid t s ∧ s.length ≤ B}.Finite := by
  intro B
  induction B with
  | zero =>
    intro t
    refine (Set.finite_singleton ([] : List Pos)).subset ?_
    rintro s ⟨-, hs⟩
    simpa using hs
  | succ B ih =>
    intro t
    have hfin : Set.Finite ({[]} ∪ ⋃ p ∈ (redexes t).toFinset,
        (List.cons p) '' {s : List Pos | lambdaRS.Valid (contractAt t p) s ∧ s.length ≤ B}) :=
      (Set.finite_singleton _).union
        (Set.Finite.biUnion (Finset.finite_toSet _) fun p _ => (ih _).image _)
    refine hfin.subset ?_
    rintro s ⟨hv, hl⟩
    cases s with
    | nil => exact Or.inl rfl
    | cons p s =>
      right
      refine Set.mem_biUnion (x := p) (by simpa using LTerm.mem_redexes.mpr hv.1) ?_
      exact ⟨s, ⟨hv.2, by simpa using hl⟩, rfl⟩

/-- A representative of a class. -/
noncomputable def rep {u : LTerm} (x : DSpaceLam u) : LDeriv u := Quotient.out x

theorem tgt_rep {u : LTerm} (x : DSpaceLam u) : lambdaRS.tgt u (rep x).1 = targetQ x := by
  conv_rhs => rw [← Quotient.out_eq x]
  rfl

/-! ## Positional lemmas for the leftmost coarse step

The thesis' lemma "the leftmost coarse step has at most one residual" is proved here by an
invariant that survives contraction: the chosen step precedes every other coarse step in the
pre-order on positions (ancestors first, then left to right).  This section collects the
positional ingredients (the order, residual positions, created redexes) and the consequences
`leftmost_least` and `sieve_least`. -/

/-- The pre-order on positions: ancestors come first, otherwise left to right. -/
def PosLt : Pos → Pos → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: x, b :: y => a < b ∨ (a = b ∧ PosLt x y)

namespace PosLt

theorem irrefl : ∀ x : Pos, ¬ PosLt x x
  | [] => by simp [PosLt]
  | a :: x => by
    simp only [PosLt]
    rintro (h | ⟨-, h⟩)
    · exact lt_irrefl _ h
    · exact irrefl x h

theorem trans : ∀ {x y z : Pos}, PosLt x y → PosLt y z → PosLt x z
  | [], [], _, h, _ => absurd h (by simp [PosLt])
  | [], _ :: _, [], _, h => absurd h (by simp [PosLt])
  | [], _ :: _, _ :: _, _, _ => by simp [PosLt]
  | _ :: _, [], _, h, _ => absurd h (by simp [PosLt])
  | _ :: _, _ :: _, [], _, h => absurd h (by simp [PosLt])
  | a :: x, b :: y, c :: z, h1, h2 => by
    simp only [PosLt] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl (h1.trans h2)
      · exact Or.inl h1
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨rfl, trans h1 h2⟩

theorem cons_cons_iff {a : ℕ} {x y : Pos} : PosLt (a :: x) (a :: y) ↔ PosLt x y := by
  simp [PosLt]

theorem append_right : ∀ {x y : Pos} (w : Pos), PosLt x y → PosLt x (y ++ w)
  | [], [], _, h => absurd h (by simp [PosLt])
  | [], _ :: _, _, _ => by simp [PosLt]
  | _ :: _, [], _, h => absurd h (by simp [PosLt])
  | a :: x, b :: y, w, h => by
    simp only [PosLt, List.cons_append] at h ⊢
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, append_right w h⟩

theorem self_append : ∀ (x : Pos) {w : Pos}, w ≠ [] → PosLt x (x ++ w)
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => by simp [PosLt]
  | a :: x, w, h => by
    rw [List.cons_append]
    exact Or.inr ⟨rfl, self_append x h⟩

theorem cons_zero_one (x y : Pos) : PosLt (0 :: x) (1 :: y) := by simp [PosLt]

theorem nil_cons (a : ℕ) (y : Pos) : PosLt [] (a :: y) := by simp [PosLt]

end PosLt

/-- `redexes t` is sorted by the pre-order. -/
theorem redexes_sorted : ∀ t : LTerm, (redexes t).Pairwise PosLt
  | .var _ => by simp [redexes]
  | .lam t => by
    simp only [redexes]
    exact (redexes_sorted t).map _ (fun a b h => Or.inr ⟨rfl, h⟩)
  | .app t s => by
    simp only [redexes]
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨?_, (redexes_sorted t).map _ (fun a b h => Or.inr ⟨rfl, h⟩), ?_⟩,
      (redexes_sorted s).map _ (fun a b h => Or.inr ⟨rfl, h⟩), ?_⟩
    · split <;> simp
    · intro a ha b hb
      split at ha
      · simp at ha; subst ha
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
        exact PosLt.nil_cons _ _
      · simp at ha
    · intro a ha b hb
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
      rcases List.mem_append.mp ha with ha | ha
      · split at ha
        · simp at ha; subst ha; exact PosLt.nil_cons _ _
        · simp at ha
      · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
        exact PosLt.cons_zero_one _ _

/-- The first element satisfying a predicate precedes all other elements satisfying it. -/
theorem find_first_lt {t : LTerm} {f : Pos → Bool} {p0 : Pos}
    (h : (redexes t).find? f = some p0) {q : Pos} (hq : q ∈ redexes t) (hf : f q = true)
    (hne : q ≠ p0) : PosLt p0 q := by
  obtain ⟨-, as, bs, hxs, has⟩ := List.find?_eq_some_iff_append.mp h
  have hsorted := redexes_sorted t
  rw [hxs] at hsorted hq
  rcases List.mem_append.mp hq with hq | hq
  · exact absurd hf (by simpa using has q hq)
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · exact (List.pairwise_append.mp hsorted).2.1 |> fun hh =>
        (List.pairwise_cons.mp hh).1 q hq

namespace PosLt

theorem append_left_iff : ∀ (r : Pos) {x y : Pos}, PosLt (r ++ x) (r ++ y) ↔ PosLt x y
  | [], x, y => by simp
  | a :: r, x, y => by
    simp only [List.cons_append]
    rw [cons_cons_iff]
    exact append_left_iff r

/-- If `p` precedes `r ++ w` without extending `r`, it precedes every extension of `r`. -/
theorem lt_append_of_not_prefix : ∀ {p r : Pos} (w w' : Pos), PosLt p (r ++ w) → ¬ r <+: p →
    PosLt p (r ++ w')
  | [], [], w, w', _, h => absurd (List.nil_prefix) h
  | [], _ :: _, w, w', _, _ => by simp [PosLt]
  | _ :: _, [], w, w', _, h => absurd (List.nil_prefix) h
  | a :: p, b :: r, w, w', h, hn => by
    simp only [List.cons_append, PosLt] at h ⊢
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨rfl, lt_append_of_not_prefix w w' h ?_⟩
      intro hp; exact hn (by simpa using hp)

/-- If `r ++ w` precedes `a` and `a` does not extend `r`, then every extension of `r` does. -/
theorem append_lt_of_not_prefix : ∀ {a r : Pos} (w w' : Pos), PosLt (r ++ w) a → ¬ r <+: a →
    PosLt (r ++ w') a
  | [], [], w, w', _, h => absurd (List.nil_prefix) h
  | [], _ :: _, w, w', h, _ => by
    simp only [List.cons_append, PosLt] at h
  | _ :: _, [], w, w', _, h => absurd (List.nil_prefix) h
  | a :: p, b :: r, w, w', h, hn => by
    simp only [List.cons_append, PosLt] at h ⊢
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨rfl, append_lt_of_not_prefix w w' h ?_⟩
      intro hp; exact hn (by simpa using hp)

theorem asymm {x y : Pos} (h : PosLt x y) : ¬ PosLt y x := fun h' => irrefl x (trans h h')

end PosLt

/-! ### Residual positions -/

theorem residuals_disjoint {t : LTerm} {q p : Pos} (hne : p ≠ q) (hnp : ¬ q <+: p) :
    residuals t q p = {p} := by
  simp [residuals, hne, hnp]

theorem residuals_body {t : LTerm} {q x : Pos} {u s : LTerm}
    (hs : subAt t q = some (app (lam u) s)) :
    residuals t q (q ++ 0 :: 0 :: x) = {q ++ x} := by
  have hne : q ++ 0 :: 0 :: x ≠ q := by
    intro h
    have := congrArg List.length h
    simp at this
  simp [residuals, hne, hs, List.drop_left']

theorem residuals_arg {t : LTerm} {q y : Pos} {u s : LTerm}
    (hs : subAt t q = some (app (lam u) s)) :
    residuals t q (q ++ 1 :: y) = ((occs u 0).map (fun o => q ++ o ++ y)).toFinset := by
  have hne : q ++ 1 :: y ≠ q := by
    intro h
    have := congrArg List.length h
    simp at this
  simp [residuals, hne, hs, List.drop_left']

/-- A redex strictly below a redex lies in its body or its argument. -/
theorem redex_below_classify {t : LTerm} {q p : Pos} (hq : isRedexAt t q = true)
    (hp : isRedexAt t p = true) (hqp : q <+: p) (hne : p ≠ q) :
    (∃ x, p = q ++ 0 :: 0 :: x) ∨ (∃ y, p = q ++ 1 :: y) := by
  obtain ⟨w, rfl⟩ := hqp
  obtain ⟨u, s, hs⟩ := (isRedexAt_iff t q).1 hq
  obtain ⟨v, hv, hpw⟩ := (isRedexAt_append t q w).1 hp
  rw [hs] at hv
  obtain rfl := Option.some.inj hv
  rcases w with _ | ⟨i, w⟩
  · exact absurd (List.append_nil q) hne
  rcases i with _ | _ | i
  · rcases w with _ | ⟨j, w⟩
    · simp [isRedexAt, subAt, isRedex] at hpw
    rcases j with _ | j
    · exact Or.inl ⟨w, rfl⟩
    · simp [isRedexAt, subAt] at hpw
  · exact Or.inr ⟨w, rfl⟩
  · simp [isRedexAt, subAt] at hpw

/-- A redex other than `r` has exactly one residual after `r`, unless it lies in the
argument of `r`. -/
theorem residuals_card_one {t : LTerm} {r p : Pos} (hr : isRedexAt t r = true)
    (hp : isRedexAt t p = true) (hne : p ≠ r) (harg : ¬ ∃ y, p = r ++ 1 :: y) :
    ∃ p1, residuals t r p = {p1} := by
  by_cases hpre : r <+: p
  · rcases redex_below_classify hr hp hpre hne with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨u, s, hs⟩ := (isRedexAt_iff t r).1 hr
      exact ⟨r ++ x, residuals_body hs⟩
    · exact absurd ⟨y, rfl⟩ harg
  · exact ⟨p, residuals_disjoint hne hpre⟩

/-- Contracting `r` preserves the pre-order between `p` and `a`, provided `p` precedes `r`, or
`p` lies in the body of `r` and neither `p` nor `a` lies in the argument of `r`. -/
theorem order_preserved {t : LTerm} {r p a p1 q' : Pos}
    (hr : isRedexAt t r = true) (hp : isRedexAt t p = true) (ha : isRedexAt t a = true)
    (hpr : p ≠ r) (har : a ≠ r) (hpa : PosLt p a)
    (hH : PosLt p r ∨ (PosLt r p ∧ (¬ ∃ y, p = r ++ 1 :: y) ∧ ¬ ∃ y, a = r ++ 1 :: y))
    (hp1 : p1 ∈ residuals t r p) (hq' : q' ∈ residuals t r a) : PosLt p1 q' := by
  obtain ⟨u, s, hs⟩ := (isRedexAt_iff t r).1 hr
  rcases hH with hprr | ⟨hrp, hnp, hna⟩
  · have hnpre : ¬ r <+: p := by
      rintro ⟨w, rfl⟩
      have hw : w ≠ [] := by rintro rfl; exact hpr (by simp)
      exact PosLt.asymm hprr (PosLt.self_append r hw)
    rw [residuals_disjoint hpr hnpre, Finset.mem_singleton] at hp1
    subst hp1
    by_cases hpre : r <+: a
    · rcases redex_below_classify hr ha hpre har with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · rw [residuals_body hs, Finset.mem_singleton] at hq'
        subst hq'; exact PosLt.append_right x hprr
      · rw [residuals_arg hs, List.mem_toFinset, List.mem_map] at hq'
        obtain ⟨o, _, rfl⟩ := hq'
        rw [List.append_assoc]; exact PosLt.append_right _ hprr
    · rw [residuals_disjoint har hpre, Finset.mem_singleton] at hq'
      subst hq'; exact hpa
  · by_cases hpre : r <+: p
    · rcases redex_below_classify hr hp hpre hpr with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · rw [residuals_body hs, Finset.mem_singleton] at hp1
        subst hp1
        by_cases hpre' : r <+: a
        · rcases redex_below_classify hr ha hpre' har with ⟨y, rfl⟩ | ⟨y, rfl⟩
          · rw [residuals_body hs, Finset.mem_singleton] at hq'
            subst hq'
            rw [PosLt.append_left_iff, PosLt.cons_cons_iff, PosLt.cons_cons_iff] at hpa
            exact (PosLt.append_left_iff r).2 hpa
          · exact absurd ⟨y, rfl⟩ hna
        · rw [residuals_disjoint har hpre', Finset.mem_singleton] at hq'
          subst hq'
          exact PosLt.append_lt_of_not_prefix (0 :: 0 :: x) x hpa hpre'
      · exact absurd ⟨y, rfl⟩ hnp
    · rw [residuals_disjoint hpr hpre, Finset.mem_singleton] at hp1
      subst hp1
      by_cases hpre' : r <+: a
      · rcases redex_below_classify hr ha hpre' har with ⟨y, rfl⟩ | ⟨y, rfl⟩
        · rw [residuals_body hs, Finset.mem_singleton] at hq'
          subst hq'
          exact PosLt.lt_append_of_not_prefix (0 :: 0 :: y) y hpa hpre
        · exact absurd ⟨y, rfl⟩ hna
      · rw [residuals_disjoint har hpre', Finset.mem_singleton] at hq'
        subst hq'; exact hpa

/-! ### Created redexes -/

theorem isRedexAt_app_nil_iff {X Y : LTerm} :
    isRedexAt (.app X Y) [] = true ↔ ∃ b, X = .lam b := by
  cases X <;> simp [isRedexAt, subAt, isRedex]

theorem lam_of_contractAt_lam {t1 : LTerm} {i : ℕ} {r' : Pos} {b : LTerm}
    (h : contractAt t1 (i :: r') = .lam b) : ∃ c, t1 = .lam c := by
  cases t1 with
  | var n => simp [contractAt] at h
  | lam c => exact ⟨c, rfl⟩
  | app a b' =>
    rcases i with _ | _ | i
    · simp at h
    · simp at h
    · simp [contractAt] at h

/-- A redex of the contractum that is neither an extension of the contracted position nor its
parent was already a redex of the source. -/
theorem isRedexAt_of_contractAt : ∀ (t : LTerm) (r q : Pos), isRedexAt t r = true →
    ¬ r <+: q → r ≠ q ++ [0] → isRedexAt (contractAt t r) q = true → isRedexAt t q = true := by
  intro t
  induction t with
  | var n => intro r q hr; simp at hr
  | lam t0 ih =>
    intro r q hr hn hq h
    rcases r with _ | ⟨i, r'⟩
    · simp [isRedexAt, subAt, isRedex] at hr
    rcases i with _ | i
    · simp only [isRedexAt_lam_zero] at hr
      have hc : contractAt (.lam t0) (0 :: r') = .lam (contractAt t0 r') := by simp [contractAt]
      rw [hc] at h
      rcases q with _ | ⟨j, q'⟩
      · simp [isRedexAt, subAt, isRedex] at h
      rcases j with _ | j
      · simp only [isRedexAt_lam_zero] at h ⊢
        refine ih r' q' hr ?_ ?_ h
        · intro hp; exact hn (by simpa using hp)
        · intro he; exact hq (by simp [he])
      · simp at h
    · simp at hr
  | app t1 s ih1 ih2 =>
    intro r q hr hn hq h
    rcases r with _ | ⟨i, r'⟩
    · exact absurd List.nil_prefix hn
    rcases i with _ | _ | i
    · simp only [isRedexAt_app_zero] at hr
      rw [LTerm.contractAt_app_zero] at h
      rcases q with _ | ⟨j, q'⟩
      · rw [isRedexAt_app_nil_iff] at h ⊢
        obtain ⟨b, hb⟩ := h
        rcases r' with _ | ⟨k, r''⟩
        · exact absurd (by simp) hq
        · exact lam_of_contractAt_lam hb
      rcases j with _ | _ | j
      · simp only [isRedexAt_app_zero] at h ⊢
        refine ih1 r' q' hr ?_ ?_ h
        · intro hp; exact hn (by simpa using hp)
        · intro he; exact hq (by simp [he])
      · simpa using h
      · simp at h
    · replace hr : isRedexAt s r' = true := by simpa using hr
      rw [LTerm.contractAt_app_one] at h
      rcases q with _ | ⟨j, q'⟩
      · simpa [isRedexAt_app_nil_iff] using h
      rcases j with _ | _ | j
      · simpa using h
      · have h' : isRedexAt (contractAt s r') q' = true := by simpa using h
        have := ih2 r' q' hr (by intro hp; exact hn (by simpa using hp))
          (by intro he; exact hq (by simp [he])) h'
        simpa using this
      · simp at h
    · simp at hr

/-- A created redex is an extension of the contracted position or its parent. -/
theorem created_position {t : LTerm} {r q : Pos} (hc : LCreates t r q) :
    r <+: q ∨ r = q ++ [0] := by
  obtain ⟨hr, hq, hnone⟩ := hc
  by_contra hcon
  push Not at hcon
  obtain ⟨hnp, hnq⟩ := hcon
  have hq' : isRedexAt (contractAt t r) q = true := hq
  have hold := isRedexAt_of_contractAt t r q hr hnp hnq hq'
  by_cases heq : q = r
  · exact hnp (heq ▸ List.prefix_refl _)
  · exact hnone q hold (by
      change q ∈ residuals t r q
      rw [residuals_disjoint heq hnp]; simp)

theorem PosLt.trichotomy : ∀ (x y : Pos), x = y ∨ PosLt x y ∨ PosLt y x
  | [], [] => Or.inl rfl
  | [], _ :: _ => Or.inr (Or.inl (by simp [PosLt]))
  | _ :: _, [] => Or.inr (Or.inr (by simp [PosLt]))
  | a :: x, b :: y => by
    rcases lt_trichotomy a b with h | rfl | h
    · exact Or.inr (Or.inl (Or.inl h))
    · rcases PosLt.trichotomy x y with rfl | h | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (Or.inr ⟨rfl, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inl h))

/-- Going up to the parent preserves "strictly before". -/
theorem PosLt.lt_parent {p q : Pos} (h : PosLt p (q ++ [0])) (hne : p ≠ q) : PosLt p q := by
  by_cases hq : q <+: p
  · obtain ⟨z, rfl⟩ := hq
    rw [PosLt.append_left_iff] at h
    rcases z with _ | ⟨c, z⟩
    · exact absurd (by simp) hne
    · simp only [PosLt] at h
      rcases h with h | ⟨rfl, h⟩
      · omega
      · rcases z with _ | _ <;> simp [PosLt] at h
  · simpa using PosLt.lt_append_of_not_prefix [0] [] h hq

/-- The parent of a redex is not a redex. -/
theorem not_isRedexAt_parent {t : LTerm} {q : Pos} (h : isRedexAt t (q ++ [0]) = true) :
    isRedexAt t q = false := by
  by_contra hq
  have hq' : isRedexAt t q = true := by simpa using hq
  obtain ⟨u, s, hs⟩ := (isRedexAt_iff t q).1 hq'
  obtain ⟨v, hv, hpw⟩ := (isRedexAt_append t q [0]).1 h
  rw [hs] at hv
  obtain rfl := Option.some.inj hv
  simp [isRedexAt, subAt, isRedex] at hpw

/-! ### Tracking the chosen step along a derivation -/

theorem simRes_disjoint {u : CTerm} {p r : Pos} (hne : p ≠ r) :
    Disjoint (simRes u.1 p) (simRes u.1 r) := by
  rw [Finset.disjoint_left]
  intro ℓ hp hr
  exact hne (simRes_position_unique u.2 hp hr)

/-- The projection of a step over another, when it has a single residual. -/
theorem proj_single_residual {t : LTerm} {a r q1 : Pos} (ha : lambdaRS.isStep t a)
    (hr : lambdaRS.isStep t r) (hres : lambdaRS.res t r a = {q1}) :
    lambdaRS.proj t [a] [r] = [q1] := by
  have hq1 : lambdaRS.isStep (lambdaRS.contract t r) q1 :=
    lambda_orthogonal.res_isStep t a r ha hr q1 (by rw [hres]; simp)
  show lambdaRS.dev (lambdaRS.tgt t [r]) (lambdaRS.resSetDeriv t {a} [r]) ++
    lambdaRS.proj _ [] _ = [q1]
  rw [show lambdaRS.resSetDeriv t {a} [r] = {q1} by
    simp [ResidualSystem.resSetDeriv, ResidualSystem.resSet]; exact hres]
  show lambdaRS.dev (lambdaRS.contract t r) {q1} ++ [] = [q1]
  rw [ResidualSystem.dev_singleton lambda_orthogonal hq1]
  rfl

/-- If the single residual of `a` after `r` is below `ω1`, then `a` is below `r ω1`. -/
theorem prefix_single_of_residual {t : LTerm} {a r q1 : Pos} {ω1 : List Pos}
    (ha : lambdaRS.isStep t a) (hr : lambdaRS.isStep t r) (hres : lambdaRS.res t r a = {q1})
    (hω1 : lambdaRS.Valid (lambdaRS.contract t r) ω1)
    (h : lambdaRS.Prefix (lambdaRS.contract t r) [q1] ω1) :
    lambdaRS.Prefix t [a] (r :: ω1) := by
  have hvr : lambdaRS.Valid t [r] := valid_singleton hr
  have hfull : lambdaRS.Valid t ([r] ++ ω1) := (lambdaRS.valid_append _ _ _).2 ⟨hvr, hω1⟩
  have hpe := proj_append_right lambda_orthogonal (σ := [a]) (τ := [r]) (ρ := ω1)
    (valid_singleton ha) hfull
  rw [proj_single_residual ha hr hres] at hpe
  have hz : lambdaRS.proj (lambdaRS.tgt t [r]) [q1] ω1 = [] := h
  rw [hz] at hpe
  have h0 := hpe.1
  unfold ResidualSystem.Prefix at h0 ⊢
  rwa [proj_nil_right lambda_orthogonal (proj_valid lambda_orthogonal (valid_singleton ha) hfull)] at h0

/-- **Key lemma (leftmost coarse step).**  Let `p` be a coarse step of `ω` preceding every other
coarse step in the pre-order.  If a prefix `ρ ⊑ ω` already contracts all the λ^dist-redexes
simulating `p`, then `p ⊑ ρ`. -/
theorem leftmost_least : ∀ (ρ : List Pos) {t : LTerm} {t' : CTerm} {ω : List Pos} {p : Pos},
    Refines t t'.1 → lambdaRS.Valid t ω → lambdaRS.Valid t ρ → lambdaRS.Prefix t ρ ω →
    Coarse t t' ω p → (∀ q, Coarse t t' ω q → q ≠ p → PosLt p q) →
    simRes t'.1 p ⊆ distRS.names (simDeriv t' ρ) → lambdaRS.Prefix t [p] ρ := by
  intro ρ
  induction ρ with
  | nil =>
    intro t t' ω p hr hω hρ hle hc hK hS
    exfalso
    obtain ⟨ℓ, hℓ⟩ := hc.2.2
    have := hS hℓ
    simp [simDeriv, distRS.names] at this
  | cons r ρ' ih =>
    intro t t' ω p hr hω hρ hle hc hK hS
    obtain ⟨hrs, hρ'⟩ := hρ
    have hvρ : lambdaRS.Valid t (r :: ρ') := ⟨hrs, hρ'⟩
    have hrr : lambdaRS.Prefix t [r] (r :: ρ') :=
      (prefix_iff_exists lambda_orthogonal (valid_singleton hrs) hvρ).2
        ⟨ρ', hρ', prefix_refl lambda_orthogonal hvρ, prefix_refl lambda_orthogonal hvρ⟩
    by_cases hrp : r = p
    · subst hrp; exact hrr
    have hp : lambdaRS.isStep t p := hc.1
    have hrω : lambdaRS.Prefix t [r] ω :=
      prefix_trans lambda_orthogonal (valid_singleton hrs) hvρ hω hrr hle
    have hpK : (simRes t'.1 r).Nonempty → PosLt p r := fun hne => hK r ⟨hrs, hrω, hne⟩ hrp
    have hargp : ¬ ∃ y, p = r ++ 1 :: y := by
      rintro ⟨y, hy⟩
      by_cases hne : (simRes t'.1 r).Nonempty
      · have := hpK hne
        rw [hy] at this
        exact PosLt.asymm this (PosLt.self_append r (by simp))
      · have hemp := Finset.not_nonempty_iff_eq_empty.mp hne
        have := simRes_empty_below hr r (1 :: y) hrs hemp
        rw [← hy] at this
        exact (Finset.nonempty_iff_ne_empty.mp hc.2.2) this
    obtain ⟨p1, hp1⟩ := residuals_card_one hrs hp (Ne.symm hrp) hargp
    have hp1' : lambdaRS.res t r p = {p1} := hp1
    have hp1mem : p1 ∈ residuals t r p := by rw [hp1]; simp
    have hr' := simulation_canonical hr hrs
    have hω1 : lambdaRS.Valid (lambdaRS.contract t r) (lambdaRS.proj t ω [r]) :=
      proj_valid lambda_orthogonal hω (valid_singleton hrs)
    have hfac := prefix_step_factor hω hrs hrω
    have hle1 : lambdaRS.Prefix (lambdaRS.contract t r) ρ' (lambdaRS.proj t ω [r]) := by
      have h1 : lambdaRS.Prefix t (r :: ρ') (r :: lambdaRS.proj t ω [r]) :=
        prefix_trans lambda_orthogonal hvρ hω ((lambdaRS.valid_append _ _ _).2
          ⟨valid_singleton hrs, hω1⟩) hle hfac.2
      exact (prefix_append_iff lambda_orthogonal (valid_singleton hrs) hρ' hω1).2 h1
    have hS1eq : simRes (simTgt t' r).1 p1 = simRes t'.1 p := by
      have := cube_sets hr hp hrs
      rw [hp1', Finset.singleton_biUnion] at this
      rw [this]
      exact Finset.sdiff_eq_self_of_disjoint (simRes_disjoint (Ne.symm hrp))
    have hc1 : Coarse (lambdaRS.contract t r) (simTgt t' r) (lambdaRS.proj t ω [r]) p1 := by
      refine ⟨lambda_orthogonal.res_isStep t p r hp hrs p1 hp1mem, ?_, ?_⟩
      · have := prefix_proj lambda_orthogonal (valid_singleton hp) hω (valid_singleton hrs) hc.2.1
        rw [proj_single_residual hp hrs hp1'] at this
        exact this
      · rw [hS1eq]; exact hc.2.2
    have hS1 : simRes (simTgt t' r).1 p1 ⊆ distRS.names (simDeriv (simTgt t' r) ρ') := by
      rw [hS1eq]
      intro ℓ hℓ
      have := hS hℓ
      rw [simNames_cons] at this
      rcases Finset.mem_union.mp this with h | h
      · exact absurd h (Finset.disjoint_left.mp (simRes_disjoint (Ne.symm hrp)) hℓ)
      · exact h
    have hK1 : ∀ q', Coarse (lambdaRS.contract t r) (simTgt t' r) (lambdaRS.proj t ω [r]) q' →
        q' ≠ p1 → PosLt p1 q' := by
      intro q' hq' hq'ne
      obtain ⟨hq'step, hq'pre, hq'S⟩ := hq'
      by_cases hcr : LCreates t r q'
      · have hSr : (simRes t'.1 r).Nonempty := by
          by_contra hne
          have hemp := Finset.not_nonempty_iff_eq_empty.mp hne
          have := garbage_creates_core hr hcr ((sim_singleton_garbage t' r).2 hemp)
          rw [sim_singleton_garbage] at this
          exact (Finset.nonempty_iff_ne_empty.mp hq'S) this
        have hPr := hpK hSr
        have hnpre : ¬ r <+: p := by
          rintro ⟨w, hw⟩
          have hw' : w ≠ [] := by rintro rfl; exact hrp (by simpa using hw)
          rw [← hw] at hPr
          exact PosLt.asymm hPr (PosLt.self_append r hw')
        have hdis : residuals t r p = {p} := residuals_disjoint (Ne.symm hrp) hnpre
        rw [hdis] at hp1
        have p1eq : p1 = p := (Finset.singleton_inj.mp hp1).symm
        rcases created_position hcr with ⟨w, rfl⟩ | hpar
        · rw [p1eq]; exact PosLt.append_right w hPr
        · have hnq' : isRedexAt t q' = false := not_isRedexAt_parent (by rw [← hpar]; exact hrs)
          have hpq' : p ≠ q' := by
            intro h
            rw [h] at hp
            simp [hnq'] at hp
          rw [p1eq]
          rw [hpar] at hPr
          exact PosLt.lt_parent hPr hpq'
      · obtain ⟨a, ha, hqa⟩ : ∃ a, lambdaRS.isStep t a ∧ q' ∈ lambdaRS.res t r a := by
          by_contra hne
          push Not at hne
          exact hcr ⟨hrs, hq'step, fun a ha => hne a ha⟩
        have har : a ≠ r := by
          rintro rfl
          rw [lambda_orthogonal.autoerasure t a ha] at hqa
          simp at hqa
        have hap : a ≠ p := by
          rintro rfl
          rw [hp1'] at hqa
          exact hq'ne (Finset.mem_singleton.mp hqa)
        have hSa : (simRes t'.1 a).Nonempty := by
          have := cube_sets hr ha hrs
          obtain ⟨ℓ, hℓ⟩ := hq'S
          have hmem : ℓ ∈ (lambdaRS.res t r a).biUnion (fun x => simRes (simTgt t' r).1 x) :=
            Finset.mem_biUnion.mpr ⟨q', hqa, hℓ⟩
          rw [this] at hmem
          exact ⟨ℓ, (Finset.mem_sdiff.mp hmem).1⟩
        have haArg : (∃ y, a = r ++ 1 :: y) → (simRes t'.1 r).Nonempty := by
          rintro ⟨y, hy⟩
          by_contra hne
          have hemp := Finset.not_nonempty_iff_eq_empty.mp hne
          have := simRes_empty_below hr r (1 :: y) hrs hemp
          rw [← hy] at this
          exact (Finset.nonempty_iff_ne_empty.mp hSa) this
        have hpa : PosLt p a := by
          by_cases hin : ∃ y, a = r ++ 1 :: y
          · obtain ⟨y, hy⟩ := hin
            rw [hy]; exact PosLt.append_right (1 :: y) (hpK (haArg ⟨y, hy⟩))
          · obtain ⟨q1, hq1⟩ := residuals_card_one hrs ha har hin
            have hres : lambdaRS.res t r a = {q1} := hq1
            have hq1' : q' = q1 := by
              rw [hres] at hqa; exact Finset.mem_singleton.mp hqa
            subst hq1'
            have hapre : lambdaRS.Prefix t [a] ω :=
              prefix_trans lambda_orthogonal (valid_singleton ha)
                ((lambdaRS.valid_append _ _ _).2 ⟨valid_singleton hrs, hω1⟩) hω
                (prefix_single_of_residual ha hrs hres hω1 hq'pre) hfac.1
            exact hK a ⟨ha, hapre, hSa⟩ hap
        have hH : PosLt p r ∨ (PosLt r p ∧ (¬ ∃ y, p = r ++ 1 :: y) ∧ ¬ ∃ y, a = r ++ 1 :: y) := by
          by_cases hSr : (simRes t'.1 r).Nonempty
          · exact Or.inl (hpK hSr)
          · rcases PosLt.trichotomy p r with h | h | h
            · exact absurd h.symm hrp
            · exact Or.inl h
            · exact Or.inr ⟨h, hargp, fun hin => hSr (haArg hin)⟩
        exact order_preserved hrs hp ha (Ne.symm hrp) har hpa hH hp1mem hqa
    have := ih hr' hω1 hρ' hle1 hc1 hK1 hS1
    exact prefix_single_of_residual hp hrs hp1' hρ' this

/-- The (fuelled) sieve is below every prefix that already covers all the names. -/
theorem sieveAux_least : ∀ (n : ℕ) {t : LTerm} {t' : CTerm} {ω ρ : List Pos},
    Refines t t'.1 → lambdaRS.Valid t ω → lambdaRS.Valid t ρ → lambdaRS.Prefix t ρ ω →
    (simDeriv t' ω).length ≤ n →
    distRS.names (simDeriv t' ω) ⊆ distRS.names (simDeriv t' ρ) →
    lambdaRS.Prefix t (sieveAux n t t' ω) ρ := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t t' ω ρ hr hω hρ hle hn hsub
    unfold sieveAux
    split
    · rfl
    · rename_i p0 hfind
      have hc := find_coarse hfind
      have hp0 := hc.1
      have hvp : lambdaRS.Valid t [p0] := valid_singleton hp0
      have hK : ∀ q, Coarse t t' ω q → q ≠ p0 → PosLt p0 q := by
        intro q hq hne
        exact find_first_lt hfind (LTerm.mem_redexes.mpr hq.1) (by
          simpa only [decide_eq_true_eq] using (⟨hq.2.1, hq.2.2⟩ : _ ∧ _)) hne
      have hS : simRes t'.1 p0 ⊆ distRS.names (simDeriv t' ρ) := by
        have h1 := (distRS.prefix_iff_subset (simDeriv_valid hr hvp).1 (simDeriv_valid hr hω).1).mp
          (simDeriv_prefix hr hvp hω hc.2.1)
        rw [names_sim_singleton] at h1
        exact h1.trans hsub
      have hp0ρ := leftmost_least ρ hr hω hρ hle hc hK hS
      have hfac := prefix_step_factor hρ hp0 hp0ρ
      have hr' := simulation_canonical hr hp0
      have hω1 : lambdaRS.Valid (lambdaRS.contract t p0) (lambdaRS.proj t ω [p0]) :=
        proj_valid lambda_orthogonal hω hvp
      have hρ1 : lambdaRS.Valid (lambdaRS.contract t p0) (lambdaRS.proj t ρ [p0]) :=
        proj_valid lambda_orthogonal hρ hvp
      have hle1 : lambdaRS.Prefix (lambdaRS.contract t p0) (lambdaRS.proj t ρ [p0])
          (lambdaRS.proj t ω [p0]) := prefix_proj lambda_orthogonal hρ hω hvp hle
      have hdec := coarse_measure_decreases hr hω hc
      have hnames : distRS.names (simDeriv (simTgt t' p0) (lambdaRS.proj t ω [p0])) ⊆
          distRS.names (simDeriv (simTgt t' p0) (lambdaRS.proj t ρ [p0])) := by
        have e1 := gen_names [p0] ω hr hω hvp
        have e2 := gen_names [p0] ρ hr hρ hvp
        change distRS.names (simDeriv (simTgt t' p0) (lambdaRS.proj t ω [p0])) = _ at e1
        change distRS.names (simDeriv (simTgt t' p0) (lambdaRS.proj t ρ [p0])) = _ at e2
        rw [e1, e2]
        intro ℓ hℓ
        rw [Finset.mem_sdiff] at hℓ ⊢
        exact ⟨hsub hℓ.1, hℓ.2⟩
      have hih := ih hr' hω1 hρ1 hle1 (by omega) hnames
      have hS0 := sieveAux_valid n hr' hω1
      have hfull : lambdaRS.Valid t (p0 :: sieveAux n (contractAt t p0) (simTgt t' p0)
          (lambdaRS.proj t ω [p0])) := ⟨hp0, hS0⟩
      have hmid : lambdaRS.Prefix t (p0 :: sieveAux n (contractAt t p0) (simTgt t' p0)
          (lambdaRS.proj t ω [p0])) (p0 :: lambdaRS.proj t ρ [p0]) :=
        (prefix_append_iff lambda_orthogonal hvp hS0 hρ1).1 hih
      exact prefix_trans lambda_orthogonal hfull
        (show lambdaRS.Valid t (p0 :: lambdaRS.proj t ρ [p0]) from ⟨hp0, hρ1⟩) hρ hmid hfac.1

theorem sieve_least {t : LTerm} {t' : CTerm} {ω ρ : List Pos} (hr : Refines t t'.1)
    (hω : lambdaRS.Valid t ω) (hρ : lambdaRS.Valid t ρ) (hle : lambdaRS.Prefix t ρ ω)
    (hsub : distRS.names (simDeriv t' ω) ⊆ distRS.names (simDeriv t' ρ)) :
    lambdaRS.Prefix t (sieve t t' ω) ρ :=
  sieveAux_least _ hr hω hρ hle le_rfl hsub

/-- Sieving does not lose any names. -/
theorem names_subset_sieve {t : LTerm} {t' : CTerm} {ω : List Pos} (hr : Refines t t'.1)
    (hω : lambdaRS.Valid t ω) :
    distRS.names (simDeriv t' ω) ⊆ distRS.names (simDeriv t' (sieve t t' ω)) := by
  have hs := sieve_valid hr hω
  have hgar := projection_after_sieveAux_garbage _ hr hω (le_refl _)
  have e := gen_names (sieve t t' ω) ω hr hω hs
  have hemp : simDeriv (simTgtDeriv t' (sieve t t' ω)) (lambdaRS.proj t ω (sieve t t' ω)) = [] :=
    hgar
  rw [hemp] at e
  intro ℓ hℓ
  by_contra hn
  have : ℓ ∈ distRS.names (simDeriv t' ω) \ distRS.names (simDeriv t' (sieve t t' ω)) :=
    Finset.mem_sdiff.mpr ⟨hℓ, hn⟩
  rw [← e] at this
  simp [distRS.names] at this

theorem permEq_trans' {t : LTerm} {a b c : List Pos} (ha : lambdaRS.Valid t a)
    (hb : lambdaRS.Valid t b) (hc : lambdaRS.Valid t c)
    (h1 : lambdaRS.PermEq t a b) (h2 : lambdaRS.PermEq t b c) : lambdaRS.PermEq t a c :=
  ⟨prefix_trans lambda_orthogonal ha hb hc h1.1 h2.1,
    prefix_trans lambda_orthogonal hc hb ha h2.2 h1.2⟩

end Thesis
