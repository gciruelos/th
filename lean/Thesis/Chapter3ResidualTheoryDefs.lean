/-
# Chapter 3: Residual theory of λ^dist — Definitions

Steps of λ^dist are addressed by their *name*: the label of the contracted λ. In a correct term
λ-labels are pairwise distinct, so a step is determined by its source and its name.
-/
import Thesis.Chapter2DistLambdaCalc

namespace Thesis

open DTerm

namespace DTerm

/-- `t` is a λ decorated with `ℓ`. -/
def isLamWith : DTerm → Label → Bool
  | lam m _, ℓ => m == ℓ
  | _, _ => false

/-- `t` contains a redex whose λ is decorated with `ℓ`. -/
def hasRedex : DTerm → Label → Bool
  | var _ _, _ => false
  | lam _ t, ℓ => hasRedex t ℓ
  | app t ss, ℓ => isLamWith t ℓ || hasRedex t ℓ || ss.any (hasRedex · ℓ)

/-- Contract the redex named `ℓ` (if any). -/
def contract : DTerm → Label → DTerm
  | var n τ, _ => var n τ
  | lam m t, ℓ => lam m (contract t ℓ)
  | app t ss, ℓ =>
    match t with
    | lam m b => if m = ℓ then b.subst 0 ss else app (lam m (contract b ℓ)) (ss.map (contract · ℓ))
    | t => app (contract t ℓ) (ss.map (contract · ℓ))

theorem hasRedex_iff_step {t : DTerm} {ℓ : Label} :
    t.hasRedex ℓ = true ↔ ∃ u, DStep t ℓ u := by
  constructor
  · intro h
    induction t using DTerm.ind with
    | var => simp [hasRedex] at h
    | lam m t ih =>
      obtain ⟨u, hu⟩ := ih (by simpa only [hasRedex] using h)
      exact ⟨_, .lam m hu⟩
    | app t ss ih ihs =>
      simp only [hasRedex, Bool.or_eq_true, List.any_eq_true] at h
      rcases h with (h | h) | ⟨s, hs, h⟩
      · cases t with
        | var => simp [isLamWith] at h
        | app => simp [isLamWith] at h
        | lam m b =>
          have he : m = ℓ := by simpa [isLamWith] using h
          subst m
          exact ⟨_, .beta ℓ b ss⟩
      · obtain ⟨u, hu⟩ := ih h
        exact ⟨_, .appL ss hu⟩
      · obtain ⟨v, hv⟩ := ihs s hs h
        obtain ⟨us, vs, rfl⟩ := List.mem_iff_append.mp hs
        exact ⟨_, .appR t us vs hv⟩
  · rintro ⟨u, h⟩
    induction h with
    | beta => simp [hasRedex, isLamWith]
    | lam _ _ ih => simpa only [hasRedex] using ih
    | appL _ _ ih => simp [hasRedex, ih]
    | appR _ _ _ _ ih => simp [hasRedex, ih]

theorem contract_absent {t : DTerm} {ℓ : Label} (ha : ℓ ∉ t.lamLabels) :
    t.contract ℓ = t := by
  induction t using DTerm.ind with
  | var => simp only [contract]
  | lam m b ih =>
    simp only [lamLabels, List.mem_cons, not_or] at ha
    simp only [contract, ih ha.2]
  | app t ss ih ihs =>
    simp only [lamLabels, List.mem_append, not_or] at ha
    have he : ss.map (contract · ℓ) = ss := by
      simpa using List.map_congr_left (fun s hs =>
        ihs s hs (fun hm => ha.2 (List.mem_flatMap.mpr ⟨s, hs, hm⟩)))
    have ht := ih ha.1
    cases t with
    | var => simp only [contract, he]
    | app => simp only [contract, ht, he]
    | lam m b =>
      have hne : m ≠ ℓ := fun hh => ha.1 (by simp [lamLabels, hh])
      simp only [contract] at ht
      simp only [contract, ite_eq_right hne, ht, he]

end DTerm

/-- A source lambda cannot have the label of a step strictly inside its body. -/
theorem DStep.label_ne_outer {b u : DTerm} {m ℓ : Label}
    (h : DStep (.lam m b) ℓ u) (hc : Correct (.lam m b)) : m ≠ ℓ := by
  cases h with
  | lam _ h =>
    intro he
    have hn := hc.uniquely_labeled
    rw [DTerm.lamLabels] at hn
    have hn' := List.nodup_cons.mp hn
    exact hn'.1 (he ▸ h.label_mem)

/-- The named contraction function computes any step of a correct term. -/
theorem DStep.eq_contract {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u)
    (hc : Correct t) : t.contract ℓ = u := by
  induction h with
  | beta => simp [contract]
  | lam m h ih => simp only [contract, ih (hc.sub (.lam m (.refl _)))]
  | @appL t t' ℓ ss h ih =>
    have hn := hc.uniquely_labeled
    rw [DTerm.lamLabels] at hn
    have hn := List.nodup_append.mp hn
    have he : ss.map (contract · ℓ) = ss := by
      simpa using List.map_congr_left (fun s hs =>
        DTerm.contract_absent (fun hm => hn.2.2 ℓ h.label_mem ℓ
          (List.mem_flatMap.mpr ⟨s, hs, hm⟩) rfl))
    have ht := ih (hc.sub (.fn ss (.refl _)))
    cases t with
    | var => cases h
    | app => simp only [contract, ht, he]
    | lam m b =>
      simp only [contract] at ht
      simp only [contract, ite_eq_right (h.label_ne_outer (hc.sub (.fn ss (.refl _)))), ht, he]
  | @appR s s' ℓ t us vs h ih =>
    have hn := hc.uniquely_labeled
    rw [DTerm.lamLabels] at hn
    have hn := List.nodup_append.mp hn
    have hm : ℓ ∈ (us ++ s :: vs).flatMap DTerm.lamLabels :=
      List.mem_flatMap (f := DTerm.lamLabels).mpr ⟨s, by simp, h.label_mem⟩
    have ht : ℓ ∉ t.lamLabels := fun hh => hn.2.2 ℓ hh ℓ hm rfl
    have hn' := List.nodup_append.mp (by
      simpa only [List.flatMap_append, List.flatMap_cons] using hn.2.1)
    have hn'' := List.nodup_append.mp hn'.2.1
    have hu : us.map (contract · ℓ) = us := by
      simpa using List.map_congr_left (fun a ha =>
        DTerm.contract_absent (fun hh => hn'.2.2 ℓ
          (List.mem_flatMap.mpr ⟨a, ha, hh⟩) ℓ (by simp [h.label_mem]) rfl))
    have hv : vs.map (contract · ℓ) = vs := by
      simpa using List.map_congr_left (fun a ha =>
        DTerm.contract_absent (fun hh => hn''.2.2 ℓ h.label_mem ℓ
          (List.mem_flatMap.mpr ⟨a, ha, hh⟩) rfl))
    have hs := ih (hc.sub (.arg t (by simp) (.refl s)))
    have he : (us ++ s :: vs).map (contract · ℓ) = us ++ s' :: vs := by
      simp only [List.map_append, List.map_cons, hu, hv, hs]
    have ht' := DTerm.contract_absent ht
    cases t with
    | var => simp only [contract, he]
    | app => simp only [contract, ht', he]
    | lam m b =>
      have hne : m ≠ ℓ := fun hh => ht (by simp [DTerm.lamLabels, hh])
      simp only [contract] at ht'
      simp only [contract, ite_eq_right hne, ht', he]

namespace DTerm

end DTerm

/-- In a correct term, `hasRedex t ℓ` holds iff there is a step `t →ℓ u`, and then `u` is
`contract t ℓ`. -/
theorem dStep_iff_hasRedex {t u : DTerm} {ℓ : Label} (ht : Correct t) :
    DStep t ℓ u ↔ t.hasRedex ℓ = true ∧ u = t.contract ℓ := by
  constructor
  · intro h
    exact ⟨DTerm.hasRedex_iff_step.mpr ⟨u, h⟩, (h.eq_contract ht).symm⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨v, hv⟩ := DTerm.hasRedex_iff_step.mp h
    exact (hv.eq_contract ht).symm ▸ hv

theorem contract_of_not_hasRedex {t : DTerm} {ℓ : Label} (h : t.hasRedex ℓ = false) :
    t.contract ℓ = t := by
  induction t using DTerm.ind with
  | var n τ => simp [contract]
  | lam m t ih => simp only [hasRedex] at h; simp [contract, ih h]
  | app t ss ih ihs =>
    simp only [hasRedex, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hss : ss.map (contract · ℓ) = ss := by
      conv_rhs => rw [← List.map_id ss]
      exact List.map_congr_left fun s hs => ihs s hs (h3 s hs)
    cases t with
    | lam m b =>
      have hm : m ≠ ℓ := by simpa [isLamWith] using h1
      have hb : b.contract ℓ = b := by simpa [contract] using ih h2
      simp [contract, hm, hb, hss]
    | var n τ => simp [contract, hss]
    | app u us => rw [contract, ih h2, hss]; simp

theorem correct_contract {t : DTerm} (ht : Correct t) (ℓ : Label) : Correct (t.contract ℓ) := by
  cases h : t.hasRedex ℓ
  · rwa [contract_of_not_hasRedex h]
  · exact correct_of_dStep ht ((dStep_iff_hasRedex ht).2 ⟨h, rfl⟩)

/-- λ^dist as an axiomatic rewrite system over correct terms.
**Residuals** (Definition "Residuals in the distributive λ-calculus"):
`R/S = {R' | src(R') = tgt(S) ∧ name(R') = name(R)}`. -/
abbrev distRS : ResidualSystem where
  Obj := CTerm
  Adr := Label
  isStep t ℓ := t.1.hasRedex ℓ = true
  contract t ℓ := ⟨t.1.contract ℓ, correct_contract t.2 ℓ⟩
  res t m ℓ := if (t.1.contract m).hasRedex ℓ then {ℓ} else ∅
  dev _ M := M.sort (· ≤ ·)

namespace distRS

/-! ## Names -/

/-- The set of names of a derivation. -/
def names (σ : List Label) : Finset Label := σ.toFinset

/-- `R ∈ σ`: some residual of `R` is contracted along `σ`. -/
def Belongs (t : CTerm) (ℓ : Label) (σ : List Label) : Prop :=
  ∃ σ₁ ℓ' σ₂, σ = σ₁ ++ ℓ' :: σ₂ ∧ ℓ' ∈ distRS.resSetDeriv t {ℓ} σ₁

/-! ## Creation and stability -/

/-- `R` (named `m`) *creates* the step `S` (named `n`, out of the target of `R`): `S` is not a
residual of any step coinitial with `R`. -/
def Creates (t : CTerm) (m n : Label) : Prop :=
  distRS.isStep t m ∧ distRS.isStep (distRS.contract t m) n ∧
    ∀ a, distRS.isStep t a → n ∉ distRS.res t m a

/-- The three ways in which a step `R` (named `ℓ`) of `t` can create a step named `ℓ'`. -/
inductive CreationCase : DTerm → Label → Label → Prop
  /-- **Case I.** `C⟨(λ^ℓ x.x^τ)[λ^ℓ' y.t] s̄⟩ → C⟨(λ^ℓ' y.t) s̄⟩ → ⋯` -/
  | I (C : DCtx) (ℓ ℓ' : Label) (τ : Ty) (b : DTerm) (ss : List DTerm) :
      CreationCase (C.plug (.app (.app (.lam ℓ (.var 0 τ)) [.lam ℓ' b]) ss)) ℓ ℓ'
  /-- **Case II.** `C⟨(λ^ℓ x.λ^ℓ' y.t) s̄ ū⟩ → C⟨(λ^ℓ' y.t') ū⟩ → ⋯` -/
  | II (C : DCtx) (ℓ ℓ' : Label) (b : DTerm) (ss us : List DTerm) :
      CreationCase (C.plug (.app (.app (.lam ℓ (.lam ℓ' b)) ss) us)) ℓ ℓ'
  /-- **Case III.** `C₁⟨(λ^ℓ x.C₂⟨x^τ ū⟩)[s̄₁, λ^ℓ' y.t, s̄₂]⟩ → C₁⟨C₂'⟨(λ^ℓ' y.t) ū'⟩⟩ → ⋯`,
  where the argument `λ^ℓ' y.t` is the one of type `τ`. -/
  | III (C₁ C₂ : DCtx) (ℓ ℓ' : Label) (τ : Ty) (us ss₁ ss₂ : List DTerm) (b : DTerm) :
      (DTerm.lam ℓ' b).ty = τ →
      CreationCase
        (C₁.plug (.app (.lam ℓ (C₂.plug (.app (.var C₂.depth τ) us))) (ss₁ ++ .lam ℓ' b :: ss₂)))
        ℓ ℓ'

/-! ## Meets -/

open Classical in
/-- The meet of derivations: repeatedly contract a step *common* to `σ` and `τ`
(the least such name, to make the choice deterministic). `fuel` bounds the recursion; `|σ|`
suffices since projections are decreasing. -/
noncomputable def meetAux : ℕ → CTerm → List Label → List Label → List Label
  | 0, _, _, _ => []
  | fuel + 1, t, σ, τ =>
    if h : ∃ a, distRS.isStep t a ∧ distRS.Prefix t [a] σ ∧ distRS.Prefix t [a] τ then
      let a := Nat.find h
      a :: meetAux fuel (distRS.contract t a) (distRS.proj t σ [a]) (distRS.proj t τ [a])
    else []

/-- `σ ⊓ τ`. -/
noncomputable def meet (t : CTerm) (σ τ : List Label) : List Label := meetAux σ.length t σ τ

end distRS

end Thesis
