/-
# Chapter 0 (support): position and substitution lemmas for λ-terms

Shared lemmas used to discharge the orthogonality axioms of `lambdaRS`
(see `Thesis.Chapter0`).
-/
import Thesis.Chapter1PrelimDefs
import Thesis.Chapter1PrelimAppendix

namespace Thesis
namespace LTerm

@[simp] theorem subAt_nil (t : LTerm) : subAt t [] = some t := by cases t <;> rfl

theorem subAt_append (t : LTerm) (q r : Pos) :
    subAt t (q ++ r) = (subAt t q).bind (fun v => subAt v r) := by
  induction q generalizing t with
  | nil => simp
  | cons i q ih =>
    rcases t with _ | t | ⟨t, s⟩ <;> rcases i with _ | _ | i <;> simp [subAt, ih]

theorem isRedexAt_iff (t : LTerm) (q : Pos) :
    isRedexAt t q = true ↔ ∃ u s, subAt t q = some (app (lam u) s) := by
  unfold isRedexAt
  cases h : subAt t q with
  | none => simp
  | some v => rcases v with _ | _ | ⟨_ | _ | _, _⟩ <;> simp [isRedex]

theorem isRedexAt_append (t : LTerm) (q r : Pos) :
    isRedexAt t (q ++ r) = true ↔ ∃ v, subAt t q = some v ∧ isRedexAt v r = true := by
  unfold isRedexAt
  rw [subAt_append]
  cases subAt t q <;> simp

@[simp] theorem isRedexAt_var (n : ℕ) (p : Pos) : isRedexAt (var n) p = false := by
  cases p <;> simp [isRedexAt, subAt, isRedex]

@[simp] theorem isRedexAt_lam_nil (t : LTerm) : isRedexAt (lam t) [] = false := by
  simp [isRedexAt, isRedex]

@[simp] theorem isRedexAt_lam_zero (t : LTerm) (p : Pos) :
    isRedexAt (lam t) (0 :: p) = isRedexAt t p := by simp [isRedexAt, subAt]

@[simp] theorem isRedexAt_lam_succ (t : LTerm) (i : ℕ) (p : Pos) :
    isRedexAt (lam t) ((i + 1) :: p) = false := by simp [isRedexAt, subAt]

@[simp] theorem isRedexAt_app_zero (t s : LTerm) (p : Pos) :
    isRedexAt (app t s) (0 :: p) = isRedexAt t p := by simp [isRedexAt, subAt]

@[simp] theorem isRedexAt_app_one (t s : LTerm) (p : Pos) :
    isRedexAt (app t s) (1 :: p) = isRedexAt s p := by simp [isRedexAt, subAt]

@[simp] theorem isRedexAt_app_succ_succ (t s : LTerm) (i : ℕ) (p : Pos) :
    isRedexAt (app t s) ((i + 2) :: p) = false := by simp [isRedexAt, subAt]

/-- Substitution preserves the redexes of the substituted-into term. -/
theorem isRedexAt_substAt : ∀ (u : LTerm) (k : ℕ) (s : LTerm) (r : Pos),
    isRedexAt u r = true → isRedexAt (substAt k s u) r = true
  | var n, k, s, r, h => by simp at h
  | lam t, k, s, [], h => by simp at h
  | lam t, k, s, 0 :: r, h => by
      simpa [substAt] using isRedexAt_substAt t (k + 1) s r (by simpa using h)
  | lam t, k, s, (i + 1) :: r, h => by simp at h
  | app t u, k, s, [], h => by
      rcases t with _ | _ | _ <;> simp_all [isRedexAt, subAt, isRedex, substAt]
  | app t u, k, s, 0 :: r, h => by
      simpa [substAt] using isRedexAt_substAt t k s r (by simpa using h)
  | app t u, k, s, 1 :: r, h => by
      simpa [substAt] using isRedexAt_substAt u k s r (by simpa using h)
  | app t u, k, s, (i + 2) :: r, h => by simp at h

/-- Shifting preserves redexes. -/
theorem isRedexAt_shift : ∀ (u : LTerm) (d c : ℕ) (r : Pos),
    isRedexAt u r = true → isRedexAt (shift d c u) r = true
  | var n, d, c, r, h => by simp at h
  | lam t, d, c, [], h => by simp at h
  | lam t, d, c, 0 :: r, h => by
      simpa [shift] using isRedexAt_shift t d (c + 1) r (by simpa using h)
  | lam t, d, c, (i + 1) :: r, h => by simp at h
  | app t u, d, c, [], h => by
      rcases t with _ | _ | _ <;> simp_all [isRedexAt, subAt, isRedex, shift]
  | app t u, d, c, 0 :: r, h => by
      simpa [shift] using isRedexAt_shift t d c r (by simpa using h)
  | app t u, d, c, 1 :: r, h => by
      simpa [shift] using isRedexAt_shift u d c r (by simpa using h)
  | app t u, d, c, (i + 2) :: r, h => by simp at h

/-- Each occurrence of the substituted variable carries a shifted copy of the argument. -/
theorem occs_subAt : ∀ (u : LTerm) (k : ℕ) (s : LTerm) (o : Pos), o ∈ occs u k →
    ∃ d, subAt (substAt k s u) o = some (shift d 0 s)
  | var n, k, s, o, h => by
      simp only [occs] at h
      split_ifs at h with hn
      · simp at h
        subst h hn
        exact ⟨n, by simp [substAt]⟩
      · simp at h
  | lam t, k, s, o, h => by
      simp only [occs, List.mem_map] at h
      obtain ⟨o', ho', rfl⟩ := h
      obtain ⟨d, hd⟩ := occs_subAt t (k + 1) s o' ho'
      exact ⟨d, by simpa [substAt, subAt] using hd⟩
  | app t u, k, s, o, h => by
      simp only [occs, List.mem_append, List.mem_map] at h
      rcases h with ⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩
      · obtain ⟨d, hd⟩ := occs_subAt t k s o' ho'
        exact ⟨d, by simpa [substAt, subAt] using hd⟩
      · obtain ⟨d, hd⟩ := occs_subAt u k s o' ho'
        exact ⟨d, by simpa [substAt, subAt] using hd⟩

/-- Contracting the redex at `q` leaves the contractum at `q`. -/
theorem subAt_contractAt : ∀ (t : LTerm) (q : Pos) (u s : LTerm),
    subAt t q = some (app (lam u) s) → subAt (contractAt t q) q = some (substAt 0 s u)
  | t, [], u, s, h => by
      simp at h; subst h; simp [contractAt]
  | var n, i :: q, u, s, h => by simp [subAt] at h
  | lam t, 0 :: q, u, s, h => by
      simpa [contractAt, subAt] using subAt_contractAt t q u s (by simpa [subAt] using h)
  | lam t, (i + 1) :: q, u, s, h => by simp [subAt] at h
  | app t t', 0 :: q, u, s, h => by
      simpa [contractAt, subAt] using subAt_contractAt t q u s (by simpa [subAt] using h)
  | app t t', 1 :: q, u, s, h => by
      simpa [contractAt, subAt] using subAt_contractAt t' q u s (by simpa [subAt] using h)
  | app t t', (i + 2) :: q, u, s, h => by simp [subAt] at h

/-- A redex not below the contracted one survives its contraction. -/
theorem isRedexAt_contractAt_of_not_prefix : ∀ (t : LTerm) (p q : Pos),
    isRedexAt t p = true → isRedexAt t q = true → ¬ q <+: p →
    isRedexAt (contractAt t q) p = true
  | var n, p, q, hp, hq, h => by simp at hp
  | lam t, p, [], hp, hq, h => by simp at hq
  | lam t, [], q, hp, hq, h => by simp at hp
  | lam t, 0 :: p, 0 :: q, hp, hq, h => by
      simp only [contractAt, isRedexAt_lam_zero] at hp hq ⊢
      exact isRedexAt_contractAt_of_not_prefix t p q hp hq (by simpa using h)
  | lam t, (i + 1) :: p, _, hp, hq, h => by simp at hp
  | lam t, _, (i + 1) :: q, hp, hq, h => by simp at hq
  | app t s, p, [], hp, hq, h => absurd (List.nil_prefix) h
  | app t s, [], 0 :: q, hp, hq, h => by
      have hq' : isRedexAt t q = true := by simpa using hq
      rcases t with _ | t | _
      · simp at hq'
      · rcases q with _ | ⟨_ | _, q⟩ <;> simp_all [contractAt, isRedexAt, subAt, isRedex]
      · simp_all [isRedexAt, subAt, isRedex]
  | app t s, [], 1 :: q, hp, hq, h => by
      simp only [contractAt]
      rcases t with _ | _ | _ <;> simp_all [isRedexAt, subAt, isRedex]
  | app t s, 0 :: p, 0 :: q, hp, hq, h => by
      simp only [contractAt, isRedexAt_app_zero] at hp hq ⊢
      exact isRedexAt_contractAt_of_not_prefix t p q hp hq (by simpa using h)
  | app t s, 0 :: p, 1 :: q, hp, hq, h => by simpa [contractAt] using hp
  | app t s, 1 :: p, 0 :: q, hp, hq, h => by simpa [contractAt] using hp
  | app t s, 1 :: p, 1 :: q, hp, hq, h => by
      simp only [contractAt, isRedexAt_app_one] at hp hq ⊢
      exact isRedexAt_contractAt_of_not_prefix s p q hp hq (by simpa using h)
  | app t s, (i + 2) :: p, _, hp, hq, h => by simp at hp
  | app t s, _, (i + 2) :: q, hp, hq, h => by simp at hq

/-- **Residuals are redexes of the contractum.** -/
theorem residuals_isRedexAt (t : LTerm) (q p : Pos)
    (hq : isRedexAt t q = true) (hp : isRedexAt t p = true) :
    ∀ c ∈ residuals t q p, isRedexAt (contractAt t q) c = true := by
  intro c hc
  by_cases hpq : p = q
  · simp [residuals, hpq] at hc
  by_cases hpre : q <+: p
  · obtain ⟨w, rfl⟩ := hpre
    obtain ⟨u, s, hsub⟩ := (isRedexAt_iff t q).1 hq
    obtain ⟨v, hv, hpw⟩ := (isRedexAt_append t q w).1 hp
    rw [hsub] at hv
    obtain rfl := Option.some.inj hv
    simp [residuals, hpq, hsub] at hc
    rcases w with _ | ⟨_ | _ | i, w⟩
    · exact absurd (List.append_nil q) hpq
    · rcases w with _ | ⟨_ | _ | j, r⟩
      · simp at hc
      · simp at hc hpw
        rw [hc]
        exact (isRedexAt_append _ q r).2
          ⟨substAt 0 s u, subAt_contractAt t q u s hsub, isRedexAt_substAt u 0 s r hpw⟩
      · simp at hpw
      · simp at hpw
    · simp at hc hpw
      obtain ⟨o, ho, rfl⟩ := hc
      obtain ⟨d, hd⟩ := occs_subAt u 0 s o ho
      refine (isRedexAt_append _ q _).2 ⟨substAt 0 s u, subAt_contractAt t q u s hsub, ?_⟩
      exact (isRedexAt_append _ o w).2 ⟨shift d 0 s, hd, isRedexAt_shift s d 0 w hpw⟩
    · simp at hc
  · simp [residuals, hpq, hpre] at hc
    rw [hc]
    exact isRedexAt_contractAt_of_not_prefix t p q hp hq hpre

/-! ### Term contexts

A context `C` with a hole at child `i` lifts positions, contractions, residuals and
developments from the subterm to `C t`. -/

/-- `C` is a one-hole context whose hole sits below child `i`. -/
structure Ctx (C : LTerm → LTerm) (i : ℕ) : Prop where
  sub : ∀ t p, subAt (C t) (i :: p) = subAt t p
  con : ∀ t p, contractAt (C t) (i :: p) = C (contractAt t p)

theorem ctx_lam : Ctx lam 0 := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
theorem ctx_appL (s : LTerm) : Ctx (fun t => app t s) 0 :=
  ⟨fun _ _ => rfl, fun t p => by simp [contractAt]⟩
theorem ctx_appR (t : LTerm) : Ctx (fun s => app t s) 1 :=
  ⟨fun _ _ => rfl, fun t p => by simp [contractAt]⟩

namespace Ctx
variable {C : LTerm → LTerm} {i : ℕ} (hC : Ctx C i)
include hC

theorem isRedexAt (t : LTerm) (p : Pos) :
    LTerm.isRedexAt (C t) (i :: p) = LTerm.isRedexAt t p := by
  simp [LTerm.isRedexAt, hC.sub]

theorem residuals_in (t : LTerm) (q p : Pos) :
    residuals (C t) (i :: q) (i :: p) = (residuals t q p).image (i :: ·) := by
  by_cases hpq : p = q
  · subst hpq; simp [residuals]
  by_cases hpre : q <+: p
  · have hpre' : (i :: q) <+: (i :: p) := by simpa using hpre
    have hne : ¬ i :: p = i :: q := by simpa using hpq
    simp only [residuals, hne, hpq, hpre, hpre', hC.sub, ite_true, ite_false, List.length_cons,
      List.drop_succ_cons]
    generalize subAt t q = x
    generalize p.drop q.length = w
    rcases x with _ | _ | _ | ⟨_ | _ | _, _⟩ <;> try simp
    rcases w with _ | ⟨_ | _ | _, _ | ⟨_ | _ | _, _⟩⟩ <;> simp <;> (ext; simp)
  · have hpre' : ¬ (i :: q) <+: (i :: p) := by simpa using hpre
    have hne : ¬ i :: p = i :: q := by simpa using hpq
    simp [residuals, hne, hpq, hpre, hpre']

omit hC in
theorem residuals_out (t : LTerm) (q p : Pos) (hp : ∀ p', p ≠ i :: p') :
    residuals (C t) (i :: q) p = {p} := by
  have h1 : p ≠ i :: q := hp q
  have h2 : ¬ (i :: q) <+: p := by
    intro h; obtain ⟨w, rfl⟩ := h; exact hp _ rfl
  simp [residuals, h1, h2]

theorem tgt_map (t : LTerm) (σ : List Pos) :
    lambdaRS.tgt (C t) (σ.map (i :: ·)) = C (lambdaRS.tgt t σ) := by
  induction σ generalizing t with
  | nil => rfl
  | cons a σ ih =>
    simp only [List.map_cons]
    show lambdaRS.tgt (LTerm.contractAt (C t) (i :: a)) _ = _
    rw [hC.con]; exact ih _

theorem resSet_in (A : Finset Pos) (t : LTerm) (a : Pos) :
    lambdaRS.resSet (C t) (A.image (i :: ·)) (i :: a) =
      (lambdaRS.resSet t A a).image (i :: ·) := by
  ext c
  simp only [ResidualSystem.resSet, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨m, ⟨x, hx, rfl⟩, hc⟩
    have : c ∈ residuals (C t) (i :: a) (i :: x) := hc
    rw [hC.residuals_in, Finset.mem_image] at this
    obtain ⟨c', hc', rfl⟩ := this
    exact ⟨c', ⟨x, hx, hc'⟩, rfl⟩
  · rintro ⟨c', ⟨m, hm, hc'⟩, rfl⟩
    refine ⟨i :: m, ⟨m, hm, rfl⟩, ?_⟩
    show _ ∈ residuals (C t) (i :: a) (i :: m)
    rw [hC.residuals_in]; exact Finset.mem_image_of_mem _ hc'

omit hC in
theorem resSet_out (E : Finset Pos) (hE : ∀ p ∈ E, ∀ p', p ≠ i :: p') (t : LTerm) (a : Pos) :
    lambdaRS.resSet (C t) E (i :: a) = E := by
  ext c
  simp only [ResidualSystem.resSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨m, hm, hc⟩
    have : c ∈ residuals (C t) (i :: a) m := hc
    rw [Ctx.residuals_out (C := C) (i := i) t a m (hE m hm)] at this
    simpa [(Finset.mem_singleton.1 this)] using hm
  · intro hc
    refine ⟨c, hc, ?_⟩
    show c ∈ residuals (C t) (i :: a) c
    rw [Ctx.residuals_out (C := C) (i := i) t a c (hE c hc)]; simp

theorem dev_in : ∀ (σ : List Pos) (t : LTerm) (A : Finset Pos),
    lambdaRS.IsDevelopment t A σ →
    lambdaRS.IsDevelopment (C t) (A.image (i :: ·)) (σ.map (i :: ·)) ∧
    lambdaRS.resSetDeriv (C t) (A.image (i :: ·)) (σ.map (i :: ·)) =
      (lambdaRS.resSetDeriv t A σ).image (i :: ·)
  | [], t, A, _ => ⟨trivial, rfl⟩
  | a :: σ, t, A, h => by
      obtain ⟨ha, haA, hrest⟩ := h
      obtain ⟨ih1, ih2⟩ := dev_in σ (LTerm.contractAt t a) (lambdaRS.resSet t A a) hrest
      have hc : LTerm.contractAt (C t) (i :: a) = C (LTerm.contractAt t a) := hC.con t a
      have hr := hC.resSet_in A t a
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · exact (isRedexAt hC t a).trans ha
      · exact Finset.mem_image_of_mem _ haA
      · show lambdaRS.IsDevelopment (LTerm.contractAt (C t) (i :: a)) _ _
        rw [hc, hr]; exact ih1
      · rw [List.map_cons, ResidualSystem.resSetDeriv_cons]
        show lambdaRS.resSetDeriv (LTerm.contractAt (C t) (i :: a)) _ _ = _
        rw [hc, hr, ih2]; rfl

omit hC in
theorem dev_out (E : Finset Pos) (hE : ∀ p ∈ E, ∀ p', p ≠ i :: p') (hC : Ctx C i) :
    ∀ (σ : List Pos) (t : LTerm), lambdaRS.resSetDeriv (C t) E (σ.map (i :: ·)) = E
  | [], t => rfl
  | a :: σ, t => by
      have hc : LTerm.contractAt (C t) (i :: a) = C (LTerm.contractAt t a) := hC.con t a
      rw [List.map_cons, ResidualSystem.resSetDeriv_cons]
      show lambdaRS.resSetDeriv (LTerm.contractAt (C t) (i :: a)) _ _ = _
      rw [hc, resSet_out E hE]
      exact dev_out E hE hC σ _

end Ctx

/-! ### Decomposing sets of redexes -/

theorem decomp_lam {t : LTerm} {M : Finset Pos} (h : ∀ a ∈ M, isRedexAt (lam t) a = true) :
    M = (subPos M 0).image (0 :: ·) := by
  ext a
  simp only [Finset.mem_image, mem_subPos]
  constructor
  · intro ha
    have := h a ha
    rcases a with _ | ⟨_ | i, p⟩
    · simp at this
    · exact ⟨p, ha, rfl⟩
    · simp at this
  · rintro ⟨p, hp, rfl⟩; exact hp

theorem decomp_app {t s : LTerm} {M : Finset Pos} (h : ∀ a ∈ M, isRedexAt (app t s) a = true) :
    M = (subPos M 0).image (0 :: ·) ∪ (subPos M 1).image (1 :: ·) ∪ M.filter (· = []) := by
  ext a
  simp only [Finset.mem_union, Finset.mem_image, mem_subPos, Finset.mem_filter]
  constructor
  · intro ha
    have := h a ha
    rcases a with _ | ⟨_ | _ | i, p⟩
    · right; exact ⟨ha, rfl⟩
    · left; left; exact ⟨p, ha, rfl⟩
    · left; right; exact ⟨p, ha, rfl⟩
    · simp at this
  · rintro ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨hp, rfl⟩) <;> assumption

/-! ### The canonical development is complete -/

/-- Developing the left then the right part of an application (before any root step). -/
theorem app_phases (t s : LTerm) (A B E : Finset Pos) (hE : ∀ p ∈ E, p = [])
    (σt σs : List Pos)
    (ht : lambdaRS.IsDevelopment t A σt ∧ lambdaRS.resSetDeriv t A σt = ∅)
    (hs : lambdaRS.IsDevelopment s B σs ∧ lambdaRS.resSetDeriv s B σs = ∅) :
    lambdaRS.IsDevelopment (app t s) (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ E)
        (σt.map (0 :: ·) ++ σs.map (1 :: ·)) ∧
    lambdaRS.resSetDeriv (app t s) (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ E)
        (σt.map (0 :: ·) ++ σs.map (1 :: ·)) = E ∧
    lambdaRS.tgt (app t s) (σt.map (0 :: ·) ++ σs.map (1 :: ·)) =
      app (lambdaRS.tgt t σt) (lambdaRS.tgt s σs) := by
  have c0 := ctx_appL s
  have c1 := ctx_appR (lambdaRS.tgt t σt)
  have hB1 : ∀ p ∈ B.image (1 :: ·), ∀ p', p ≠ 0 :: p' := by
    intro p hp p'; obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hp; simp
  have hE0 : ∀ p ∈ E, ∀ p', p ≠ 0 :: p' := by intro p hp p'; simp [hE p hp]
  have hE1 : ∀ p ∈ E, ∀ p', p ≠ 1 :: p' := by intro p hp p'; simp [hE p hp]
  have hBE : ∀ p ∈ B.image (1 :: ·) ∪ E, ∀ p', p ≠ 0 :: p' := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    exacts [hB1 p h, hE0 p h]
  have d1 := c0.dev_in σt t A ht.1
  have o1 : lambdaRS.resSetDeriv (app t s) (B.image (1 :: ·)) (σt.map (0 :: ·)) =
      B.image (1 :: ·) := Ctx.dev_out _ hB1 c0 σt t
  have o1' : lambdaRS.resSetDeriv (app t s) E (σt.map (0 :: ·)) = E :=
    Ctx.dev_out _ hE0 c0 σt t
  have res1 : lambdaRS.resSetDeriv (app t s) (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ E)
      (σt.map (0 :: ·)) = B.image (1 :: ·) ∪ E := by
    rw [ResidualSystem.resSetDeriv_union, ResidualSystem.resSetDeriv_union, o1, o1']
    have : lambdaRS.resSetDeriv (app t s) (A.image (0 :: ·)) (σt.map (0 :: ·)) = ∅ := by
      rw [show lambdaRS.resSetDeriv (app t s) (A.image (0 :: ·)) (σt.map (0 :: ·)) =
        (lambdaRS.resSetDeriv t A σt).image (0 :: ·) from d1.2, ht.2]; rfl
    rw [this]; simp
  have tgt1 : lambdaRS.tgt (app t s) (σt.map (0 :: ·)) = app (lambdaRS.tgt t σt) s :=
    c0.tgt_map t σt
  have d2 := c1.dev_in σs s B hs.1
  have o2 : lambdaRS.resSetDeriv (app (lambdaRS.tgt t σt) s) E (σs.map (1 :: ·)) = E :=
    Ctx.dev_out _ hE1 c1 σs s
  have res2 : lambdaRS.resSetDeriv (app (lambdaRS.tgt t σt) s) (B.image (1 :: ·) ∪ E)
      (σs.map (1 :: ·)) = E := by
    rw [ResidualSystem.resSetDeriv_union, o2]
    have : lambdaRS.resSetDeriv (app (lambdaRS.tgt t σt) s) (B.image (1 :: ·))
        (σs.map (1 :: ·)) = ∅ := by
      rw [show lambdaRS.resSetDeriv (app (lambdaRS.tgt t σt) s) (B.image (1 :: ·))
        (σs.map (1 :: ·)) = (lambdaRS.resSetDeriv s B σs).image (1 :: ·) from d2.2, hs.2]; rfl
    rw [this]; simp
  have tgt2 : lambdaRS.tgt (app (lambdaRS.tgt t σt) s) (σs.map (1 :: ·)) =
      app (lambdaRS.tgt t σt) (lambdaRS.tgt s σs) := c1.tgt_map s σs
  refine ⟨?_, ?_, ?_⟩
  · rw [ResidualSystem.isDevelopment_append]
    refine ⟨ResidualSystem.isDevelopment_mono (by
      intro x hx; simp only [Finset.mem_union]; left; left; exact hx) d1.1, ?_⟩
    rw [tgt1, res1]
    exact ResidualSystem.isDevelopment_mono (by
      intro x hx; simp only [Finset.mem_union]; left; exact hx) d2.1
  · rw [ResidualSystem.resSetDeriv_append, tgt1, res1, res2]
  · rw [ResidualSystem.tgt_append, tgt1, tgt2]

theorem dev_complete_aux : ∀ (t : LTerm) (M : Finset Pos),
    (∀ a ∈ M, isRedexAt t a = true) →
    lambdaRS.IsDevelopment t M (dev t M) ∧ lambdaRS.resSetDeriv t M (dev t M) = ∅
  | var n, M, h => by
      have : M = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using h a ha)
      subst this; exact ⟨trivial, rfl⟩
  | lam t, M, h => by
      have hM := decomp_lam h
      have ih := dev_complete_aux t (subPos M 0) (fun a ha => by
        simpa using h (0 :: a) (mem_subPos.1 ha))
      have key := ctx_lam.dev_in _ t _ ih.1
      rw [← hM] at key
      have hd : dev (lam t) M = (dev t (subPos M 0)).map (0 :: ·) := rfl
      rw [hd]
      refine ⟨key.1, ?_⟩
      rw [show lambdaRS.resSetDeriv (lam t) M ((dev t (subPos M 0)).map (0 :: ·)) =
        (lambdaRS.resSetDeriv t (subPos M 0) (dev t (subPos M 0))).image (0 :: ·) from key.2, ih.2]
      rfl
  | app t s, M, h => by
      have hM := decomp_app h
      have ihA := dev_complete_aux t (subPos M 0) (fun a ha => by
        simpa using h (0 :: a) (mem_subPos.1 ha))
      have ihB := dev_complete_aux s (subPos M 1) (fun a ha => by
        simpa using h (1 :: a) (mem_subPos.1 ha))
      have hE : ∀ p ∈ M.filter (· = []), p = [] := fun p hp => (Finset.mem_filter.1 hp).2
      obtain ⟨P1, P2, P3⟩ := app_phases t s _ _ _ hE _ _ ihA ihB
      rw [← hM] at P1 P2
      have hd : dev (app t s) M = (dev t (subPos M 0)).map (0 :: ·) ++
          (dev s (subPos M 1)).map (1 :: ·) ++ (if [] ∈ M then [[]] else []) := rfl
      rw [hd]
      by_cases h0 : [] ∈ M
      · simp only [h0, ↓reduceIte]
        have hE' : M.filter (· = []) = {[]} := by ext a; simp; intro ha; subst ha; exact h0
        rw [hE'] at P2
        -- the root is a redex, so `t` is an abstraction, and so is its development target
        obtain ⟨u, s', hu⟩ := (isRedexAt_iff _ _).1 (h [] h0)
        simp at hu
        obtain ⟨rfl, rfl⟩ := hu
        have hσ : dev (lam u) (subPos M 0) = (dev u (subPos (subPos M 0) 0)).map (0 :: ·) := rfl
        have hlam : lambdaRS.tgt (lam u) (dev (lam u) (subPos M 0)) =
            lam (lambdaRS.tgt u (dev u (subPos (subPos M 0) 0))) := by
          rw [hσ]; exact ctx_lam.tgt_map _ _
        rw [hlam] at P3
        refine ⟨?_, ?_⟩
        · rw [ResidualSystem.isDevelopment_append, P3, P2]
          refine ⟨P1, ?_, by simp, trivial⟩
          show isRedexAt (app _ _) [] = true
          simp [isRedexAt, subAt, isRedex]
        · rw [ResidualSystem.resSetDeriv_append, P3, P2]
          show lambdaRS.resSet _ _ [] = ∅
          ext c
          simp [ResidualSystem.resSet]
          simp [residuals]
      · simp only [h0, ↓reduceIte, List.append_nil]
        have hE' : M.filter (· = []) = ∅ := by
          ext a; simp; intro ha hne; subst hne; exact h0 ha
        rw [hE'] at P2
        exact ⟨P1, P2⟩

end LTerm
end Thesis
