/-
# Background: from positional residuals to marked terms

`mark t M` is the marked term obtained from `t` by marking the redexes at the positions of `M`.
Residuation of marked terms computes positional residuals:
`mark t M \ mark t {b} = mark (t contracted at b) (M / b)`.
-/
import Thesis.Chapter0Lambda
import Thesis.Chapter0Marked

namespace Thesis

open LTerm Marked Marked.MT

namespace Bridge

/-- The marked term with marks at the positions of `M`. -/
def mark : LTerm → Finset Pos → MT
  | .var n, _ => .var n
  | .lam t, M => .lam (mark t (subPos M 0))
  | .app (.lam u) s, M =>
      if [] ∈ M then .beta (mark u (subPos (subPos M 0) 0)) (mark s (subPos M 1))
      else .app (.lam (mark u (subPos (subPos M 0) 0))) (mark s (subPos M 1))
  | .app t s, M => .app (mark t (subPos M 0)) (mark s (subPos M 1))

/-- Unmarked terms. -/
abbrev ofL (t : LTerm) : MT := mark t ∅

@[simp] theorem subPos_empty (i : ℕ) : subPos (∅ : Finset Pos) i = ∅ := by
  ext; simp

theorem mark_app_of_not_mem {t s : LTerm} {M : Finset Pos} (h : [] ∉ M) :
    mark (.app t s) M = .app (mark t (subPos M 0)) (mark s (subPos M 1)) := by
  cases t <;> simp [mark, h]

theorem mark_app_nonlam {t s : LTerm} (ht : ∀ u, t ≠ .lam u) (M : Finset Pos) :
    mark (.app t s) M = .app (mark t (subPos M 0)) (mark s (subPos M 1)) := by
  cases t with
  | lam u => exact absurd rfl (ht u)
  | _ => rfl

theorem Src_mark : ∀ (t : LTerm) (M : Finset Pos), Src (mark t M) = ofL t
  | .var n, M => by simp [mark, Src]
  | .lam t, M => by simp [mark, Src, Src_mark t]
  | .app (.lam u) s, M => by
    by_cases h : [] ∈ M <;> simp [mark, h, Src, Src_mark u, Src_mark s]
  | .app (.var n) s, M => by
    unfold ofL
    rw [mark_app_nonlam (t := .var n) (by simp) M, mark_app_nonlam (t := .var n) (by simp) ∅]
    simp only [Src, Src_mark s, Src_mark (.var n), subPos_empty]
  | .app (.app a b) s, M => by
    unfold ofL
    rw [mark_app_nonlam (t := .app a b) (by simp) M, mark_app_nonlam (t := .app a b) (by simp) ∅]
    simp only [Src, Src_mark s, Src_mark (.app a b), subPos_empty]

theorem Arr_mark : ∀ (t : LTerm) (M : Finset Pos), Arr (mark t M)
  | .var n, M => by simp [mark, Arr]
  | .lam t, M => by simp [mark, Arr, Arr_mark t]
  | .app (.lam u) s, M => by
    by_cases h : [] ∈ M <;> simp [mark, h, Arr, Arr_mark u, Arr_mark s]
  | .app (.var n) s, M => by
    rw [mark_app_nonlam (t := .var n) (by simp)]; exact ⟨Arr_mark _ _, Arr_mark s _⟩
  | .app (.app a b) s, M => by
    rw [mark_app_nonlam (t := .app a b) (by simp)]; exact ⟨Arr_mark _ _, Arr_mark s _⟩

/-- Shifting indices commutes with marking. -/
theorem mark_shift : ∀ (s : LTerm) (d c : ℕ) (P : Finset Pos),
    mark (LTerm.shift d c s) P = Raise c d (mark s P)
  | .var n, d, c, P => by
    simp only [LTerm.shift]
    split_ifs with h <;> simp [mark] <;> omega
  | .lam t, d, c, P => by simp [LTerm.shift, mark, mark_shift t]
  | .app (.lam b) u, d, c, P => by
    by_cases h : [] ∈ P <;> simp [LTerm.shift, mark, h, mark_shift b, mark_shift u]
  | .app (.var n) u, d, c, P => by
    have h1 : ∀ x, LTerm.shift d c (.var n) ≠ .lam x := by
      intro x; simp only [LTerm.shift]; split_ifs <;> simp
    show mark (.app (LTerm.shift d c (.var n)) (LTerm.shift d c u)) P = _
    rw [mark_app_nonlam h1, mark_app_nonlam (t := .var n) (by simp), mark_shift (.var n),
      mark_shift u]
    rfl
  | .app (.app a b) u, d, c, P => by
    show mark (.app (LTerm.shift d c (.app a b)) (LTerm.shift d c u)) P = _
    rw [mark_app_nonlam (t := LTerm.shift d c (.app a b)) (by simp [LTerm.shift]),
      mark_app_nonlam (t := .app a b) (by simp), mark_shift (.app a b), mark_shift u]
    rfl

/-- Positions of the substituted term: marks of the body, and marks of the argument copied at
every occurrence of the substituted variable. -/
def substSet (u : LTerm) (k : ℕ) (R P : Finset Pos) : Finset Pos :=
  R ∪ ((occs u k).toFinset ×ˢ P).image (fun x => x.1 ++ x.2)

theorem mem_substSet {u : LTerm} {k : ℕ} {R P : Finset Pos} {x : Pos} :
    x ∈ substSet u k R P ↔ x ∈ R ∨ ∃ o ∈ occs u k, ∃ p ∈ P, x = o ++ p := by
  simp only [substSet, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    List.mem_toFinset, Prod.exists]
  constructor
  · rintro (h | ⟨o, p, ⟨ho, hp⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨o, ho, p, hp, rfl⟩
  · rintro (h | ⟨o, ho, p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨o, p, ⟨ho, hp⟩, rfl⟩

theorem subPos_substSet_lam (u0 : LTerm) (k : ℕ) (R P : Finset Pos) :
    subPos (substSet (.lam u0) k R P) 0 = substSet u0 (k + 1) (subPos R 0) P := by
  ext x
  simp only [mem_subPos, mem_substSet, occs, List.mem_map]
  constructor
  · rintro (h | ⟨o, ⟨o', ho', rfl⟩, p, hp, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨o', ho', p, hp, by simpa using he⟩
  · rintro (h | ⟨o, ho, p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨0 :: o, ⟨o, ho, rfl⟩, p, hp, rfl⟩

theorem subPos_substSet_app (u1 u2 : LTerm) (k : ℕ) (R P : Finset Pos) (i : ℕ) (hi : i = 0 ∨ i = 1) :
    subPos (substSet (.app u1 u2) k R P) i =
      substSet (if i = 0 then u1 else u2) k (subPos R i) P := by
  ext x
  simp only [mem_subPos, mem_substSet, occs, List.mem_append, List.mem_map]
  rcases hi with rfl | rfl
  · simp only [if_true]
    constructor
    · rintro (h | ⟨o, (⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩), p, hp, he⟩)
      · exact Or.inl h
      · exact Or.inr ⟨o', ho', p, hp, by simpa using he⟩
      · simp at he
    · rintro (h | ⟨o, ho, p, hp, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0 :: o, Or.inl ⟨o, ho, rfl⟩, p, hp, rfl⟩
  · simp only [show (1 : ℕ) ≠ 0 by omega, if_false]
    constructor
    · rintro (h | ⟨o, (⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩), p, hp, he⟩)
      · exact Or.inl h
      · simp at he
      · exact Or.inr ⟨o', ho', p, hp, by simpa using he⟩
    · rintro (h | ⟨o, ho, p, hp, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨1 :: o, Or.inr ⟨o, ho, rfl⟩, p, hp, rfl⟩

theorem nil_mem_substSet_app {u1 u2 : LTerm} {k : ℕ} {R P : Finset Pos} :
    [] ∈ substSet (.app u1 u2) k R P ↔ [] ∈ R := by
  rw [mem_substSet]
  constructor
  · rintro (h | ⟨o, ho, p, _, he⟩)
    · exact h
    · simp only [occs, List.mem_append, List.mem_map] at ho
      rcases ho with ⟨o', _, rfl⟩ | ⟨o', _, rfl⟩ <;> simp at he
  · exact Or.inl

theorem subPos_redexes {t : LTerm} {R : Finset Pos} {i : ℕ}
    (hR : ∀ r ∈ R, isRedexAt t r = true) (C : LTerm) (hC : ∀ p, isRedexAt t (i :: p) = isRedexAt C p) :
    ∀ r ∈ subPos R i, isRedexAt C r = true := by
  intro r hr
  rw [← hC]; exact hR _ (mem_subPos.mp hr)

/-- **Substitution and marking.** -/
theorem mark_substAt (s : LTerm) (P : Finset Pos) : ∀ (u : LTerm) (k : ℕ) (R : Finset Pos),
    (∀ r ∈ R, isRedexAt u r = true) →
    mark (substAt k s u) (substSet u k R P) = Subst k (mark s P) (mark u R)
  | .var n, k, R, hR => by
    have hR0 : R = ∅ := by
      ext r; simp only [Finset.notMem_empty, iff_false]; intro hr; simpa using hR r hr
    subst hR0
    by_cases hnk : n = k
    · subst hnk
      have : substSet (.var n) n ∅ P = P := by
        ext x; simp [mem_substSet, occs]
      rw [this]
      simp [substAt, mark, Subst, mark_shift]
    · have : substSet (.var n) k ∅ P = ∅ := by
        ext x; simp [mem_substSet, occs, hnk]
      rw [this]
      simp only [substAt, Subst, mark]
      split_ifs <;> first | omega | rfl
  | .lam u0, k, R, hR => by
    have hR' := subPos_redexes hR u0 (fun p => LTerm.isRedexAt_lam_zero u0 p)
    simp only [substAt, mark, Subst]
    rw [subPos_substSet_lam, mark_substAt s P u0 (k + 1) (subPos R 0) hR']
  | .app (.lam u1) u2, k, R, hR => by
    have hR0 := subPos_redexes hR (.lam u1) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hR00 := subPos_redexes hR0 u1 (fun p => LTerm.isRedexAt_lam_zero u1 p)
    have hR1 := subPos_redexes hR u2 (fun p => LTerm.isRedexAt_app_one _ _ p)
    have e1 := mark_substAt s P u1 (k + 1) _ hR00
    have e2 := mark_substAt s P u2 k _ hR1
    have q0 := subPos_substSet_app (.lam u1) u2 k R P 0 (Or.inl rfl)
    have q1 := subPos_substSet_app (.lam u1) u2 k R P 1 (Or.inr rfl)
    simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false] at q0 q1
    have q00 : subPos (subPos (substSet (.app (.lam u1) u2) k R P) 0) 0 =
        substSet u1 (k + 1) (subPos (subPos R 0) 0) P := by
      rw [q0, subPos_substSet_lam]
    by_cases h : [] ∈ R
    · have h' : [] ∈ substSet (.app (.lam u1) u2) k R P := nil_mem_substSet_app.2 h
      simp only [substAt, mark, h, h', if_true, Subst, q00, q1, e1, e2]
    · have h' : [] ∉ substSet (.app (.lam u1) u2) k R P := fun hh => h (nil_mem_substSet_app.1 hh)
      simp only [substAt, mark, h, h', if_false, Subst, q00, q1, e1, e2]
  | .app (.var n) u2, k, R, hR => by
    have h : [] ∉ R := fun hh => by simpa [isRedexAt, subAt, isRedex] using hR _ hh
    have h' : [] ∉ substSet (.app (.var n) u2) k R P := fun hh => h (nil_mem_substSet_app.1 hh)
    have hR0 := subPos_redexes hR (.var n) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hR1 := subPos_redexes hR u2 (fun p => LTerm.isRedexAt_app_one _ _ p)
    have q0 := subPos_substSet_app (.var n) u2 k R P 0 (Or.inl rfl)
    have q1 := subPos_substSet_app (.var n) u2 k R P 1 (Or.inr rfl)
    simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false] at q0 q1
    show mark (.app (substAt k s (.var n)) (substAt k s u2)) _ = _
    rw [mark_app_of_not_mem h', mark_app_nonlam (t := .var n) (by simp) R, q0, q1,
      mark_substAt s P (.var n) k _ hR0, mark_substAt s P u2 k _ hR1]
    rfl
  | .app (.app a b) u2, k, R, hR => by
    have h : [] ∉ R := fun hh => by simpa [isRedexAt, subAt, isRedex] using hR _ hh
    have h' : [] ∉ substSet (.app (.app a b) u2) k R P := fun hh => h (nil_mem_substSet_app.1 hh)
    have hR0 := subPos_redexes hR (.app a b) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hR1 := subPos_redexes hR u2 (fun p => LTerm.isRedexAt_app_one _ _ p)
    have q0 := subPos_substSet_app (.app a b) u2 k R P 0 (Or.inl rfl)
    have q1 := subPos_substSet_app (.app a b) u2 k R P 1 (Or.inr rfl)
    simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false] at q0 q1
    show mark (.app (substAt k s (.app a b)) (substAt k s u2)) _ = _
    rw [mark_app_of_not_mem h', mark_app_nonlam (t := .app a b) (by simp) R, q0, q1,
      mark_substAt s P (.app a b) k _ hR0, mark_substAt s P u2 k _ hR1]
    rfl

/-! ### Positional residual sets, decomposed -/

theorem resSet_root {u s : LTerm} {M : Finset Pos} :
    lambdaRS.resSet (.app (.lam u) s) M [] =
      substSet u 0 (subPos (subPos M 0) 0) (subPos M 1) := by
  ext x
  simp only [ResidualSystem.resSet, Finset.mem_biUnion, mem_substSet, mem_subPos]
  constructor
  · rintro ⟨m, hm, hx⟩
    change x ∈ residuals (.app (.lam u) s) [] m at hx
    rcases m with _ | ⟨i, m⟩
    · simp [residuals] at hx
    rcases i with _ | _ | i
    · rcases m with _ | ⟨j, m⟩
      · simp [residuals, subAt] at hx
      rcases j with _ | j
      · simp [residuals, subAt] at hx; subst hx; exact Or.inl hm
      · simp [residuals, subAt] at hx
    · simp [residuals, subAt] at hx
      obtain ⟨o, ho, rfl⟩ := hx
      exact Or.inr ⟨o, ho, m, hm, by simp⟩
    · simp [residuals, subAt] at hx
  · rintro (h | ⟨o, ho, p, hp, rfl⟩)
    · exact ⟨0 :: 0 :: x, h, by change x ∈ residuals _ [] _; simp [residuals, subAt]⟩
    · refine ⟨1 :: p, hp, ?_⟩
      change o ++ p ∈ residuals _ [] _
      simp only [residuals, subAt]
      simp
      first | exact ho | exact ⟨o, ho, rfl⟩

theorem resSet_lam {t0 : LTerm} {M : Finset Pos} (hM : ∀ a ∈ M, isRedexAt (.lam t0) a = true)
    (b : Pos) :
    lambdaRS.resSet (.lam t0) M (0 :: b) = (lambdaRS.resSet t0 (subPos M 0) b).image (0 :: ·) := by
  conv_lhs => rw [decomp_lam hM]
  exact ctx_lam.resSet_in _ t0 b

theorem resSet_app0 {t1 s : LTerm} {M : Finset Pos} (hM : ∀ a ∈ M, isRedexAt (.app t1 s) a = true)
    (b : Pos) :
    lambdaRS.resSet (.app t1 s) M (0 :: b) =
      (lambdaRS.resSet t1 (subPos M 0) b).image (0 :: ·) ∪ (subPos M 1).image (1 :: ·) ∪
        M.filter (· = []) := by
  conv_lhs => rw [decomp_app hM]
  rw [ResidualSystem.resSet_union, ResidualSystem.resSet_union, (ctx_appL s).resSet_in,
    Ctx.resSet_out (C := fun t => LTerm.app t s) (i := 0) _ (by simp) t1 b,
    Ctx.resSet_out (C := fun t => LTerm.app t s) (i := 0) _
      (by intro p hp p'; simp at hp; simp [hp.2]) t1 b]

theorem resSet_app1 {t1 s : LTerm} {M : Finset Pos} (hM : ∀ a ∈ M, isRedexAt (.app t1 s) a = true)
    (b : Pos) :
    lambdaRS.resSet (.app t1 s) M (1 :: b) =
      (subPos M 0).image (0 :: ·) ∪ (lambdaRS.resSet s (subPos M 1) b).image (1 :: ·) ∪
        M.filter (· = []) := by
  conv_lhs => rw [decomp_app hM]
  rw [ResidualSystem.resSet_union, ResidualSystem.resSet_union, (ctx_appR t1).resSet_in,
    Ctx.resSet_out (C := fun x => LTerm.app t1 x) (i := 1) _ (by simp) s b,
    Ctx.resSet_out (C := fun x => LTerm.app t1 x) (i := 1) _
      (by intro p hp p'; simp at hp; simp [hp.2]) s b]

theorem subPos_decomp (A B : Finset Pos) (M : Finset Pos) :
    subPos (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ M.filter (· = [])) 0 = A ∧
    subPos (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ M.filter (· = [])) 1 = B ∧
    ([] ∈ A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ M.filter (· = []) ↔ [] ∈ M) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x; simp
  · ext x; simp
  · simp

@[simp] theorem subPos_singleton_self (i : ℕ) (b : Pos) : subPos ({i :: b} : Finset Pos) i = {b} := by
  ext; simp
@[simp] theorem subPos_singleton_ne {i j : ℕ} (h : i ≠ j) (b : Pos) :
    subPos ({i :: b} : Finset Pos) j = ∅ := by
  ext x; simp only [mem_subPos, Finset.mem_singleton, List.cons.injEq, Finset.notMem_empty,
    iff_false, not_and]
  intro e; exact absurd e.symm h
@[simp] theorem subPos_singleton_nil (i : ℕ) : subPos ({[]} : Finset Pos) i = ∅ := by
  ext; simp
@[simp] theorem subPos_image_self (A : Finset Pos) (i : ℕ) : subPos (A.image (i :: ·)) i = A := by
  ext; simp

theorem mark_ne_nil (t : LTerm) (M : Finset Pos) : mark t M ≠ .nil := Arr_ne_nil (Arr_mark t M)

theorem resid_mark_ofL (t : LTerm) (M : Finset Pos) : resid (mark t M) (ofL t) = mark t M := by
  have := resid_Src _ (Arr_mark t M)
  rwa [Src_mark] at this

/-- **Bridge theorem**: residuation of marked terms computes positional residuals. -/
theorem resid_mark : ∀ (t : LTerm) (b : Pos) (M : Finset Pos), isRedexAt t b = true →
    (∀ a ∈ M, isRedexAt t a = true) →
    resid (mark t M) (mark t {b}) = mark (contractAt t b) (lambdaRS.resSet t M b)
  | .var n, b, M, hb, _ => by simp at hb
  | .lam t0, [], M, hb, _ => by simp [isRedexAt, subAt, isRedex] at hb
  | .lam t0, (i + 1) :: b, M, hb, _ => by simp at hb
  | .lam t0, 0 :: b, M, hb, hM => by
    have hb' : isRedexAt t0 b = true := by simpa using hb
    have hM0 := subPos_redexes hM t0 (fun p => LTerm.isRedexAt_lam_zero t0 p)
    have e := resid_mark t0 b (subPos M 0) hb' hM0
    rw [show contractAt (.lam t0) (0 :: b) = .lam (contractAt t0 b) from ctx_lam.con t0 b,
      resSet_lam hM]
    simp only [mark, subPos_singleton_self, subPos_image_self, resid, e, mark_ne_nil, ite_false]
  | .app (.lam u) s, [], M, _, hM => by
    have hM00 := subPos_redexes (subPos_redexes hM (.lam u)
      (fun p => LTerm.isRedexAt_app_zero _ _ p)) u (fun p => LTerm.isRedexAt_lam_zero u p)
    rw [resSet_root, show contractAt (.app (.lam u) s) [] = substAt 0 s u from rfl,
      mark_substAt s (subPos M 1) u 0 _ hM00]
    by_cases h : [] ∈ M <;>
      simp [mark, h, resid, resid_mark_ofL, mark_ne_nil]
  | .app (.var n) s, [], M, hb, _ => by simp [isRedexAt, subAt, isRedex] at hb
  | .app (.app a c) s, [], M, hb, _ => by simp [isRedexAt, subAt, isRedex] at hb
  | .app t1 s, 0 :: b, M, hb, hM => by
    have hb' : isRedexAt t1 b = true := by simpa using hb
    have hM0 := subPos_redexes hM t1 (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hM1 := subPos_redexes hM s (fun p => LTerm.isRedexAt_app_one _ _ p)
    rw [show contractAt (.app t1 s) (0 :: b) = .app (contractAt t1 b) s from (ctx_appL s).con t1 b,
      resSet_app0 hM]
    obtain ⟨d0, d1, dn⟩ := subPos_decomp (lambdaRS.resSet t1 (subPos M 0) b) (subPos M 1) M
    have hsb : mark (.app t1 s) {0 :: b} = .app (mark t1 {b}) (ofL s) := by
      rw [mark_app_of_not_mem (by simp)]; simp
    rw [hsb]
    by_cases hr : [] ∈ M
    · obtain ⟨u, rfl⟩ : ∃ u, t1 = .lam u := by
        have := hM _ hr
        cases t1 <;> simp_all [isRedexAt, subAt, isRedex]
      rcases b with _ | ⟨j, b⟩
      · simp [isRedexAt, subAt, isRedex] at hb'
      rcases j with _ | j
      · have hb'' : isRedexAt u b = true := by simpa using hb'
        have hM00 := subPos_redexes hM0 u (fun p => LTerm.isRedexAt_lam_zero u p)
        have e := resid_mark u b (subPos (subPos M 0) 0) hb'' hM00
        rw [show contractAt (.lam u) (0 :: b) = .lam (contractAt u b) from ctx_lam.con u b,
          resSet_lam hM0] at *
        simp only [mark, hr, ite_true, dn.mpr hr, d0, d1, subPos_singleton_self,
          subPos_image_self, resid, e, resid_mark_ofL, mark_ne_nil, or_self, ite_false]
      · simp at hb'
    · have e := resid_mark t1 b (subPos M 0) hb' hM0
      have hr' : [] ∉ (lambdaRS.resSet t1 (subPos M 0) b).image (0 :: ·) ∪
          (subPos M 1).image (1 :: ·) ∪ M.filter (· = []) := fun hh => hr (dn.mp hh)
      rw [mark_app_of_not_mem hr, mark_app_of_not_mem hr', d0, d1]
      simp only [resid, e, resid_mark_ofL, mark_ne_nil, or_self, ite_false]
  | .app t1 s, 1 :: b, M, hb, hM => by
    have hb' : isRedexAt s b = true := by simpa using hb
    have hM0 := subPos_redexes hM t1 (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hM1 := subPos_redexes hM s (fun p => LTerm.isRedexAt_app_one _ _ p)
    have e := resid_mark s b (subPos M 1) hb' hM1
    rw [show contractAt (.app t1 s) (1 :: b) = .app t1 (contractAt s b) from (ctx_appR t1).con s b,
      resSet_app1 hM]
    obtain ⟨d0, d1, dn⟩ := subPos_decomp (subPos M 0) (lambdaRS.resSet s (subPos M 1) b) M
    have hsb : mark (.app t1 s) {1 :: b} = .app (ofL t1) (mark s {b}) := by
      rw [mark_app_of_not_mem (by simp)]; simp
    rw [hsb]
    by_cases hr : [] ∈ M
    · obtain ⟨u, rfl⟩ : ∃ u, t1 = .lam u := by
        have := hM _ hr
        cases t1 <;> simp_all [isRedexAt, subAt, isRedex]
      simp only [mark, hr, ite_true, dn.mpr hr, d0, d1, subPos_empty, resid, e, resid_mark_ofL,
        mark_ne_nil, or_self, ite_false]
    · have hr' : [] ∉ (subPos M 0).image (0 :: ·) ∪
          (lambdaRS.resSet s (subPos M 1) b).image (1 :: ·) ∪ M.filter (· = []) :=
        fun hh => hr (dn.mp hh)
      rw [mark_app_of_not_mem hr, mark_app_of_not_mem hr', d0, d1]
      simp only [resid, e, resid_mark_ofL, mark_ne_nil, or_self, ite_false]
  | .app t1 s, (i + 2) :: b, M, hb, _ => by simp at hb

/-! ### Marked residuals along complete developments -/

theorem subPos_mono {P Q : Finset Pos} (h : P ⊆ Q) (i : ℕ) : subPos P i ⊆ subPos Q i := by
  intro x hx; rw [mem_subPos] at hx ⊢; exact h hx

/-- Residuating by a term with more marks leaves only the target. -/
theorem resid_mark_sub : ∀ (u : LTerm) (Q N : Finset Pos), Q ⊆ N →
    resid (mark u Q) (mark u N) = Trg (mark u N)
  | .var n, Q, N, _ => by simp [mark, resid, Trg]
  | .lam t, Q, N, h => by
    simp [mark, resid, Trg, resid_mark_sub t _ _ (subPos_mono h 0), mark_ne_nil,
      Arr_ne_nil (Arr_Trg _ (Arr_mark t (subPos N 0)))]
  | .app (.lam u) s, Q, N, h => by
    have e1 := resid_mark_sub u _ _ (subPos_mono (subPos_mono h 0) 0)
    have e2 := resid_mark_sub s _ _ (subPos_mono h 1)
    have n1 := Arr_ne_nil (Arr_Trg _ (Arr_mark u (subPos (subPos N 0) 0)))
    have n2 := Arr_ne_nil (Arr_Trg _ (Arr_mark s (subPos N 1)))
    by_cases hN : [] ∈ N <;> by_cases hQ : [] ∈ Q
    · simp [mark, hN, hQ, resid, Trg, e1, e2, n1, n2]
    · simp [mark, hN, hQ, resid, Trg, e1, e2, n1, n2]
    · exact absurd (h hQ) hN
    · simp [mark, hN, hQ, resid, Trg, e1, e2, n1, n2]
  | .app (.var n) s, Q, N, h => by
    rw [mark_app_nonlam (t := .var n) (by simp) Q, mark_app_nonlam (t := .var n) (by simp) N]
    have e2 := resid_mark_sub s _ _ (subPos_mono h 1)
    have n2 := Arr_ne_nil (Arr_Trg _ (Arr_mark s (subPos N 1)))
    simp [mark, resid, Trg, e2, n2]
  | .app (.app a c) s, Q, N, h => by
    rw [mark_app_nonlam (t := .app a c) (by simp) Q, mark_app_nonlam (t := .app a c) (by simp) N]
    have e1 := resid_mark_sub (.app a c) _ _ (subPos_mono h 0)
    have e2 := resid_mark_sub s _ _ (subPos_mono h 1)
    have n1 := Arr_ne_nil (Arr_Trg _ (Arr_mark (.app a c) (subPos N 0)))
    have n2 := Arr_ne_nil (Arr_Trg _ (Arr_mark s (subPos N 1)))
    simp only [resid, e1, e2, n1, n2, or_self, ite_false, Trg]

theorem resSet_redexes {u : LTerm} {P : Finset Pos} {c : Pos} (hc : isRedexAt u c = true)
    (hP : ∀ a ∈ P, isRedexAt u a = true) :
    ∀ a ∈ lambdaRS.resSet u P c, isRedexAt (contractAt u c) a = true := by
  intro a ha
  obtain ⟨m, hm, ham⟩ := Finset.mem_biUnion.mp ha
  exact residuals_isRedexAt u c m hc (hP m hm) a ham

theorem resSetDeriv_redexes : ∀ (σ : List Pos) {u : LTerm} {P : Finset Pos},
    lambdaRS.Valid u σ → (∀ a ∈ P, isRedexAt u a = true) →
    ∀ a ∈ lambdaRS.resSetDeriv u P σ, isRedexAt (lambdaRS.tgt u σ) a = true
  | [], u, P, _, hP => hP
  | c :: σ, u, P, ⟨hc, hσ⟩, hP => resSetDeriv_redexes σ hσ (resSet_redexes hc hP)

/-- Marked residuals along a complete development. -/
theorem mark_resSetDeriv : ∀ (σ : List Pos) {u : LTerm} {N P : Finset Pos},
    (∀ a ∈ N, isRedexAt u a = true) → (∀ a ∈ P, isRedexAt u a = true) →
    lambdaRS.IsCompleteDevelopment u N σ →
    mark (lambdaRS.tgt u σ) (lambdaRS.resSetDeriv u P σ) = resid (mark u P) (mark u N)
  | [], u, N, P, _, _, hσ => by
    have hN : N = ∅ := hσ.2
    subst hN
    exact (resid_mark_ofL u P).symm
  | c :: σ, u, N, P, hN, hP, hσ => by
    obtain ⟨⟨hc, hcN, hdev⟩, hcomp⟩ := hσ
    have ih := mark_resSetDeriv σ (resSet_redexes hc hN) (resSet_redexes hc hP) ⟨hdev, hcomp⟩
    change mark (lambdaRS.tgt (contractAt u c) σ)
      (lambdaRS.resSetDeriv (contractAt u c) (lambdaRS.resSet u P c) σ) = _
    rw [ih, ← resid_mark u c P hc hP, ← resid_mark u c N hc hN]
    have h1 : resid (mark u P) (mark u {c}) ≠ .nil :=
      Con_iff.2 ⟨Arr_mark _ _, Arr_mark _ _, by rw [Src_mark, Src_mark]⟩
    have h2 : resid (mark u N) (mark u {c}) ≠ .nil :=
      Con_iff.2 ⟨Arr_mark _ _, Arr_mark _ _, by rw [Src_mark, Src_mark]⟩
    rw [Cube (Con_resid_resid h1 h2), resid_mark_sub u {c} N (by simpa using hcN)]
    have h3 : resid (mark u P) (mark u N) ≠ .nil :=
      Con_iff.2 ⟨Arr_mark _ _, Arr_mark _ _, by rw [Src_mark, Src_mark]⟩
    rw [← Src_resid h3, resid_Src _ (Arr_resid h3)]

/-- The target of a complete development is the target of the marked term. -/
theorem ofL_tgt {σ : List Pos} {u : LTerm} {N : Finset Pos} (hN : ∀ a ∈ N, isRedexAt u a = true)
    (hσ : lambdaRS.IsCompleteDevelopment u N σ) :
    ofL (lambdaRS.tgt u σ) = Trg (mark u N) := by
  have := mark_resSetDeriv σ hN hN hσ
  rw [hσ.2, resid_self _ (Arr_mark u N)] at this
  exact this

theorem ofL_app (t s : LTerm) : ofL (.app t s) = MT.app (ofL t) (ofL s) := by
  show mark _ ∅ = _
  rw [mark_app_of_not_mem (by simp)]; simp

theorem ofL_lam (t : LTerm) : ofL (.lam t) = MT.lam (ofL t) := by
  show mark _ ∅ = _; simp [mark]

theorem ofL_var (n : ℕ) : ofL (.var n) = MT.var n := rfl

theorem ofL_inj : ∀ {t t' : LTerm}, ofL t = ofL t' → t = t' := by
  intro t
  induction t with
  | var n => intro t' h; cases t' <;> simp_all [ofL_var, ofL_lam, ofL_app]
  | lam t ih =>
    intro t' h
    cases t' with
    | lam t' => simp only [ofL_lam, MT.lam.injEq] at h; rw [ih h]
    | _ => simp [ofL_var, ofL_lam, ofL_app] at h
  | app t s iht ihs =>
    intro t' h
    cases t' with
    | app t' s' =>
      simp only [ofL_app, MT.app.injEq] at h; rw [iht h.1, ihs h.2]
    | _ => simp [ofL_var, ofL_lam, ofL_app] at h

theorem mark_inj_set : ∀ (u : LTerm) {P Q : Finset Pos}, (∀ a ∈ P, isRedexAt u a = true) →
    (∀ a ∈ Q, isRedexAt u a = true) → mark u P = mark u Q → P = Q
  | .var n, P, Q, hP, hQ, _ => by
    have h1 : P = ∅ := by
      ext r; simp only [Finset.notMem_empty, iff_false]; intro hr; simpa using hP r hr
    have h2 : Q = ∅ := by
      ext r; simp only [Finset.notMem_empty, iff_false]; intro hr; simpa using hQ r hr
    rw [h1, h2]
  | .lam t, P, Q, hP, hQ, h => by
    simp only [mark, MT.lam.injEq] at h
    have := mark_inj_set t (subPos_redexes hP t (fun p => LTerm.isRedexAt_lam_zero t p))
      (subPos_redexes hQ t (fun p => LTerm.isRedexAt_lam_zero t p)) h
    rw [decomp_lam hP, decomp_lam hQ, this]
  | .app (.lam u) s, P, Q, hP, hQ, h => by
    have hP0 := subPos_redexes hP (.lam u) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hQ0 := subPos_redexes hQ (.lam u) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hP00 := subPos_redexes hP0 u (fun p => LTerm.isRedexAt_lam_zero u p)
    have hQ00 := subPos_redexes hQ0 u (fun p => LTerm.isRedexAt_lam_zero u p)
    have hP1 := subPos_redexes hP s (fun p => LTerm.isRedexAt_app_one _ _ p)
    have hQ1 := subPos_redexes hQ s (fun p => LTerm.isRedexAt_app_one _ _ p)
    have key : ([] ∈ P ↔ [] ∈ Q) ∧ mark u (subPos (subPos P 0) 0) = mark u (subPos (subPos Q 0) 0) ∧
        mark s (subPos P 1) = mark s (subPos Q 1) := by
      by_cases h1 : [] ∈ P <;> by_cases h2 : [] ∈ Q <;> simp_all [mark]
    have e00 := mark_inj_set u hP00 hQ00 key.2.1
    have e1 := mark_inj_set s hP1 hQ1 key.2.2
    have e0 : subPos P 0 = subPos Q 0 := by
      rw [decomp_lam hP0, decomp_lam hQ0, e00]
    rw [decomp_app hP, decomp_app hQ, e0, e1]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, rfl⟩; exact ⟨key.1.mp hx, rfl⟩
    · rintro ⟨hx, rfl⟩; exact ⟨key.1.mpr hx, rfl⟩
  | .app (.var n) s, P, Q, hP, hQ, h => by
    have nP : [] ∉ P := fun hh => by simpa [isRedexAt, subAt, isRedex] using hP _ hh
    have nQ : [] ∉ Q := fun hh => by simpa [isRedexAt, subAt, isRedex] using hQ _ hh
    rw [mark_app_of_not_mem nP, mark_app_of_not_mem nQ, MT.app.injEq] at h
    have e0 := mark_inj_set (.var n) (subPos_redexes hP _ (fun p => LTerm.isRedexAt_app_zero _ _ p))
      (subPos_redexes hQ _ (fun p => LTerm.isRedexAt_app_zero _ _ p)) h.1
    have e1 := mark_inj_set s (subPos_redexes hP s (fun p => LTerm.isRedexAt_app_one _ _ p))
      (subPos_redexes hQ s (fun p => LTerm.isRedexAt_app_one _ _ p)) h.2
    rw [decomp_app hP, decomp_app hQ, e0, e1]
    congr 1
    ext x; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, rfl⟩; exact absurd hx nP
    · rintro ⟨hx, rfl⟩; exact absurd hx nQ
  | .app (.app a c) s, P, Q, hP, hQ, h => by
    have nP : [] ∉ P := fun hh => by simpa [isRedexAt, subAt, isRedex] using hP _ hh
    have nQ : [] ∉ Q := fun hh => by simpa [isRedexAt, subAt, isRedex] using hQ _ hh
    rw [mark_app_of_not_mem nP, mark_app_of_not_mem nQ, MT.app.injEq] at h
    have e0 := mark_inj_set (.app a c)
      (subPos_redexes hP _ (fun p => LTerm.isRedexAt_app_zero _ _ p))
      (subPos_redexes hQ _ (fun p => LTerm.isRedexAt_app_zero _ _ p)) h.1
    have e1 := mark_inj_set s (subPos_redexes hP s (fun p => LTerm.isRedexAt_app_one _ _ p))
      (subPos_redexes hQ s (fun p => LTerm.isRedexAt_app_one _ _ p)) h.2
    rw [decomp_app hP, decomp_app hQ, e0, e1]
    congr 1
    ext x; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, rfl⟩; exact absurd hx nP
    · rintro ⟨hx, rfl⟩; exact absurd hx nQ

theorem coinitial_marks (u : LTerm) (P Q : Finset Pos) : resid (mark u P) (mark u Q) ≠ .nil :=
  Con_iff.2 ⟨Arr_mark _ _, Arr_mark _ _, by rw [Src_mark, Src_mark]⟩

/-- **Semantic orthogonality** of β-reduction (Lévy's cube lemma, positional form). -/
theorem semantic_orthogonality (t : LTerm) (a b : Pos) (ha : isRedexAt t a = true)
    (hb : isRedexAt t b = true) :
    ∃ σ τ, lambdaRS.IsCompleteDevelopment (lambdaRS.contract t b) (lambdaRS.res t b a) σ ∧
      lambdaRS.IsCompleteDevelopment (lambdaRS.contract t a) (lambdaRS.res t a b) τ ∧
      lambdaRS.tgt (lambdaRS.contract t b) σ = lambdaRS.tgt (lambdaRS.contract t a) τ ∧
      ∀ c, lambdaRS.isStep t c →
        lambdaRS.resSetDeriv t {c} (a :: τ) = lambdaRS.resSetDeriv t {c} (b :: σ) := by
  have hNa : ∀ x ∈ lambdaRS.res t b a, isRedexAt (contractAt t b) x = true :=
    residuals_isRedexAt t b a hb ha
  have hNb : ∀ x ∈ lambdaRS.res t a b, isRedexAt (contractAt t a) x = true :=
    residuals_isRedexAt t a b ha hb
  have hσ := dev_complete_aux (contractAt t b) _ hNa
  have hτ := dev_complete_aux (contractAt t a) _ hNb
  have htgt : lambdaRS.tgt (lambdaRS.contract t b) (lambdaRS.dev (contractAt t b) (lambdaRS.res t b a)) =
      lambdaRS.tgt (lambdaRS.contract t a) (lambdaRS.dev (contractAt t a) (lambdaRS.res t a b)) := by
    have hsa : ∀ x ∈ ({a} : Finset Pos), isRedexAt t x = true := by simpa using ha
    have hsb : ∀ x ∈ ({b} : Finset Pos), isRedexAt t x = true := by simpa using hb
    have e1 := ofL_tgt hNa hσ
    have e2 := ofL_tgt hNb hτ
    have r1 := resid_mark t b {a} hb hsa
    have r2 := resid_mark t a {b} ha hsb
    rw [ResidualSystem.resSet_singleton] at r1 r2
    change ofL (lambdaRS.tgt (contractAt t b) _) = Trg (mark (contractAt t b) (residuals t b a)) at e1
    change ofL (lambdaRS.tgt (contractAt t a) _) = Trg (mark (contractAt t a) (residuals t a b)) at e2
    apply ofL_inj
    change ofL (lambdaRS.tgt (contractAt t b) _) = ofL (lambdaRS.tgt (contractAt t a) _)
    rw [e1, e2, ← r1, ← r2]
    have hc := Con_resid_resid (coinitial_marks t {b} {b}) (coinitial_marks t {a} {b})
    have hcube := Cube hc
    have s1 := Src_resid hc
    have s2 := Src_resid (hcube ▸ hc)
    rw [hcube] at s1
    rw [← s1, s2]
  refine ⟨_, _, hσ, hτ, htgt, ?_⟩
  · intro c hc
    have hsc : ∀ x ∈ ({c} : Finset Pos), isRedexAt t x = true := by simpa using hc
    have hPa : ∀ x ∈ lambdaRS.resSet t {c} a, isRedexAt (contractAt t a) x = true :=
      resSet_redexes ha hsc
    have hPb : ∀ x ∈ lambdaRS.resSet t {c} b, isRedexAt (contractAt t b) x = true :=
      resSet_redexes hb hsc
    have m1 := mark_resSetDeriv _ hNb hPa hτ
    have m2 := mark_resSetDeriv _ hNa hPb hσ
    have ra := resid_mark t a {c} ha hsc
    have rb := resid_mark t b {c} hb hsc
    have hsa : ∀ x ∈ ({a} : Finset Pos), isRedexAt t x = true := by simpa using ha
    have hsb : ∀ x ∈ ({b} : Finset Pos), isRedexAt t x = true := by simpa using hb
    have r1 := resid_mark t b {a} hb hsa
    have r2 := resid_mark t a {b} ha hsb
    rw [ResidualSystem.resSet_singleton] at r1 r2
    change mark _ _ = resid (mark (contractAt t a) (lambdaRS.resSet t {c} a))
      (mark (contractAt t a) (residuals t a b)) at m1
    change mark _ _ = resid (mark (contractAt t b) (lambdaRS.resSet t {c} b))
      (mark (contractAt t b) (residuals t b a)) at m2
    rw [← ra, ← r2] at m1
    rw [← rb, ← r1] at m2
    have hcube := Cube (Con_resid_resid (coinitial_marks t {c} {a}) (coinitial_marks t {b} {a}))
    rw [hcube, ← m2] at m1
    change lambdaRS.resSetDeriv (contractAt t a) (lambdaRS.resSet t {c} a) _ =
      lambdaRS.resSetDeriv (contractAt t b) (lambdaRS.resSet t {c} b) _
    have hX := resSetDeriv_redexes _ (ResidualSystem.isDevelopment_valid hτ.1) hPa
    have hY := resSetDeriv_redexes _ (ResidualSystem.isDevelopment_valid hσ.1) hPb
    change lambdaRS.tgt (contractAt t b) _ = lambdaRS.tgt (contractAt t a) _ at htgt
    rw [← htgt] at m1 hX
    exact mark_inj_set _ hX hY m1

/-! ### Finite developments (de Vrijer) -/

theorem beta_bounds {X Y Z W : MT} (hZ : hgt Z ≤ hgt X) (hW : hgt W ≤ hgt Y)
    (hm : ∀ x, mtp x Z ≤ mtp x X) (hm' : ∀ x, mtp x W ≤ mtp x Y) :
    hgt (.beta Z W) ≤ hgt (.beta X Y) ∧ ∀ x, mtp x (.beta Z W) ≤ mtp x (.beta X Y) := by
  have hmax : max 1 (mtp 0 Z) ≤ max 1 (mtp 0 X) := max_le_max le_rfl (hm 0)
  refine ⟨?_, fun x => ?_⟩
  · simp only [hgt]
    have := Nat.mul_le_mul hW hmax
    omega
  · simp only [mtp]
    have := Nat.mul_le_mul (hm' x) hmax
    have := hm (x + 1)
    omega

/-- One development step decreases the height and does not increase multiplicities. -/
theorem dev_step_decreases : ∀ (w : LTerm) (c : Pos) (N : Finset Pos), isRedexAt w c = true →
    (∀ a ∈ N, isRedexAt w a = true) → c ∈ N →
    hgt (resid (mark w N) (mark w {c})) < hgt (mark w N) ∧
      ∀ x, mtp x (resid (mark w N) (mark w {c})) ≤ mtp x (mark w N)
  | .var n, c, N, hc, _, _ => by simp at hc
  | .lam t0, [], N, hc, _, _ => by simp [isRedexAt, subAt, isRedex] at hc
  | .lam t0, (i + 1) :: b, N, hc, _, _ => by simp at hc
  | .lam t0, 0 :: b, N, hc, hN, hcN => by
    have hb : isRedexAt t0 b = true := by simpa using hc
    have hN0 := subPos_redexes hN t0 (fun p => LTerm.isRedexAt_lam_zero t0 p)
    obtain ⟨h1, h2⟩ := dev_step_decreases t0 b (subPos N 0) hb hN0 (by simpa using hcN)
    simp only [mark, subPos_singleton_self, resid, resid_mark t0 b _ hb hN0, mark_ne_nil,
      ite_false, hgt, mtp]
    rw [← resid_mark t0 b _ hb hN0]
    exact ⟨h1, fun x => h2 (x + 1)⟩
  | .app (.lam u) s, [], N, _, hN, hcN => by
    set X := mark u (subPos (subPos N 0) 0)
    set Y := mark s (subPos N 1)
    have hm : mark (.app (.lam u) s) {[]} = .beta (ofL u) (ofL s) := by simp [mark]
    have hX : mark (.app (.lam u) s) N = .beta X Y := by simp [mark, hcN, X, Y]
    have hr : resid (.beta X Y) (.beta (ofL u) (ofL s)) = Subst 0 Y X := by
      simp only [resid, X, Y, resid_mark_ofL, mark_ne_nil, or_self, ite_false]
    rw [hm, hX, hr]
    refine ⟨?_, fun x => ?_⟩
    · rw [hgt_Subst]
      simp only [hgt]
      have := Nat.mul_le_mul_left (hgt Y) (le_max_right 1 (mtp 0 X))
      omega
    · rcases x with _ | x
      · simpa [mtp] using mtp0_subst_le Y X
      · have := mtp_Subst' Y X x 0
        simp only [Nat.add_zero] at this
        rw [this]
        simp only [mtp]
        have := Nat.mul_le_mul_left (mtp (x + 1) Y) (le_max_right 1 (mtp 0 X))
        rw [show x + 1 + 1 = x + 2 by omega]
        omega
  | .app (.var n) s, [], N, hc, _, _ => by simp [isRedexAt, subAt, isRedex] at hc
  | .app (.app a c) s, [], N, hc, _, _ => by simp [isRedexAt, subAt, isRedex] at hc
  | .app t1 s, 0 :: b, N, hc, hN, hcN => by
    have hb : isRedexAt t1 b = true := by simpa using hc
    have hN0 := subPos_redexes hN t1 (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hsb : mark (.app t1 s) {0 :: b} = .app (mark t1 {b}) (ofL s) := by
      rw [mark_app_of_not_mem (by simp)]; simp
    rw [hsb]
    by_cases hr : [] ∈ N
    · obtain ⟨u, rfl⟩ : ∃ u, t1 = .lam u := by
        have := hN _ hr
        cases t1 <;> simp_all [isRedexAt, subAt, isRedex]
      rcases b with _ | ⟨j, b⟩
      · simp [isRedexAt, subAt, isRedex] at hb
      rcases j with _ | j
      · have hb' : isRedexAt u b = true := by simpa using hb
        have hN00 := subPos_redexes hN0 u (fun p => LTerm.isRedexAt_lam_zero u p)
        obtain ⟨h1, h2⟩ := dev_step_decreases u b _ hb' hN00 (by simpa using hcN)
        simp only [mark, hr, ite_true, subPos_singleton_self, resid, resid_mark_ofL,
          mark_ne_nil, resid_mark u b _ hb' hN00, or_self, ite_false]
        rw [← resid_mark u b _ hb' hN00]
        obtain ⟨g1, g2⟩ := beta_bounds h1.le le_rfl h2 (fun _ => le_rfl)
        refine ⟨?_, g2⟩
        simp only [hgt]
        have := Nat.mul_le_mul_left (hgt (mark s (subPos N 1)))
          (max_le_max (le_refl 1) (h2 0))
        omega
      · simp at hb
    · have hb2 := dev_step_decreases t1 b (subPos N 0) hb hN0 (by simpa using hcN)
      rw [mark_app_of_not_mem hr]
      simp only [resid, resid_mark_ofL, mark_ne_nil, resid_mark t1 b _ hb hN0, or_self, ite_false,
        hgt, mtp]
      rw [← resid_mark t1 b _ hb hN0]
      exact ⟨by have := hb2.1; omega, fun x => by have := hb2.2 x; omega⟩
  | .app t1 s, 1 :: b, N, hc, hN, hcN => by
    have hb : isRedexAt s b = true := by simpa using hc
    have hN1 := subPos_redexes hN s (fun p => LTerm.isRedexAt_app_one _ _ p)
    obtain ⟨h1, h2⟩ := dev_step_decreases s b (subPos N 1) hb hN1 (by simpa using hcN)
    have hsb : mark (.app t1 s) {1 :: b} = .app (ofL t1) (mark s {b}) := by
      rw [mark_app_of_not_mem (by simp)]; simp
    rw [hsb]
    by_cases hr : [] ∈ N
    · obtain ⟨u, rfl⟩ : ∃ u, t1 = .lam u := by
        have := hN _ hr
        cases t1 <;> simp_all [isRedexAt, subAt, isRedex]
      simp only [mark, hr, ite_true, subPos_empty, resid, resid_mark_ofL, mark_ne_nil,
        resid_mark s b _ hb hN1, or_self, ite_false]
      rw [← resid_mark s b _ hb hN1]
      set X := mark u (subPos (subPos N 0) 0)
      refine ⟨?_, fun x => ?_⟩
      · simp only [hgt]
        have hpos : 0 < max 1 (mtp 0 X) := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)
        have := Nat.mul_lt_mul_of_pos_right h1 hpos
        omega
      · simp only [mtp]
        have := Nat.mul_le_mul_right (max 1 (mtp 0 X)) (h2 x)
        omega
    · rw [mark_app_of_not_mem hr]
      simp only [resid, resid_mark_ofL, mark_ne_nil, resid_mark s b _ hb hN1, or_self, ite_false,
        hgt, mtp]
      rw [← resid_mark s b _ hb hN1]
      exact ⟨by omega, fun x => by have := h2 x; omega⟩
  | .app t1 s, (i + 2) :: b, N, hc, _, _ => by simp at hc

/-- Developments are bounded by the height of the marked term. -/
theorem dev_length_le : ∀ (σ : List Pos) {u : LTerm} {N : Finset Pos},
    (∀ a ∈ N, isRedexAt u a = true) → lambdaRS.IsDevelopment u N σ → σ.length ≤ hgt (mark u N)
  | [], _, _, _, _ => Nat.zero_le _
  | c :: σ, u, N, hN, ⟨hc, hcN, hdev⟩ => by
    have ih := dev_length_le σ (resSet_redexes hc hN) hdev
    have hdec := (dev_step_decreases u c N hc hN hcN).1
    rw [resid_mark u c N hc hN] at hdec
    change σ.length ≤ hgt (mark (contractAt u c) (lambdaRS.resSet u N c)) at ih
    simp only [List.length_cons]
    omega

/-- **Finite developments** for β-reduction. -/
theorem finite_developments (t : LTerm) (M : Finset Pos) (hM : ∀ a ∈ M, lambdaRS.isStep t a) :
    ¬ ∃ f : ℕ → Pos, ∀ n, lambdaRS.IsDevelopment t M (List.ofFn fun i : Fin n => f i) := by
  rintro ⟨f, hf⟩
  have := dev_length_le _ hM (hf (hgt (mark t M) + 1))
  simp at this

end Bridge

end Thesis
