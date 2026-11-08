/-
# Background: residuals of β-reduction via marked terms

A self-contained formalization of the residual theory of the pure λ-calculus (de Bruijn
indices), following Huet's "Residual theory in λ-calculus: a formal development" and its
adaptation in Stark's Isabelle/AFP entry `ResiduatedTransitionSystem` (theory `LambdaCalculus`).

Terms carry marked redexes (`beta t u` stands for a marked `(λ t) u`), and residuation is a partial
function on marked terms.  This file develops index raising, substitution, residuation, and
Lévy's cube lemma.
-/
import Mathlib

namespace Thesis.Marked

inductive MT
  | nil : MT
  | var : ℕ → MT
  | lam : MT → MT
  | app : MT → MT → MT
  | beta : MT → MT → MT
  deriving DecidableEq

namespace MT

/-- Raising indices of free variables (above depth `d`) by `n`. -/
def Raise : ℕ → ℕ → MT → MT
  | _, _, nil => nil
  | d, n, var i => if d ≤ i then var (i + n) else var i
  | d, n, lam t => lam (Raise (d + 1) n t)
  | d, n, app t u => app (Raise d n t) (Raise d n u)
  | d, n, beta t u => beta (Raise (d + 1) n t) (Raise d n u)

/-- `Subst n v t`: substitute `v` for the variable `n` in `t`. -/
def Subst : ℕ → MT → MT → MT
  | _, _, nil => nil
  | n, v, var i => if n < i then var (i - 1) else if n = i then Raise 0 n v else var i
  | n, v, lam t => lam (Subst (n + 1) v t)
  | n, v, app t u => app (Subst n v t) (Subst n v u)
  | n, v, beta t u => beta (Subst (n + 1) v t) (Subst n v u)

/-- Closing tactic for the arithmetic on variable cases. -/
macro "var_arith" : tactic =>
  `(tactic| (simp only [Raise]; split_ifs <;> (try simp only [Raise]) <;> (try split_ifs) <;>
    first | omega | (congr 1; omega) | (simp_all; omega) | rfl))

/-! ### Raising -/

theorem Raise_ne_nil {t : MT} (h : t ≠ nil) (d n : ℕ) : Raise d n t ≠ nil := by
  cases t <;> simp_all [Raise] <;> split <;> simp

theorem Raise_plus (t : MT) : ∀ d m n, Raise d (m + n) t = Raise (d + m) n (Raise d m t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro d m n
    var_arith
  | lam t ih =>
    intro d m n
    simp only [Raise]
    rw [ih (d + 1) m n, show d + 1 + m = d + m + 1 by omega]
  | app t u iht ihu => intro d m n; simp [Raise, iht, ihu]
  | beta t u iht ihu =>
    intro d m n
    simp only [Raise]
    rw [ihu d m n, iht (d + 1) m n, show d + 1 + m = d + m + 1 by omega]

theorem Raise_plus' (t : MT) : ∀ d d' m n, d' ≤ d + n → d ≤ d' →
    Raise d (m + n) t = Raise d' m (Raise d n t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro d d' m n h1 h2
    var_arith
  | lam t ih =>
    intro d d' m n h1 h2
    simp only [Raise]
    rw [ih (d + 1) (d' + 1) m n (by omega) (by omega)]
  | app t u iht ihu =>
    intro d d' m n h1 h2; simp [Raise, iht d d' m n h1 h2, ihu d d' m n h1 h2]
  | beta t u iht ihu =>
    intro d d' m n h1 h2
    simp only [Raise]
    rw [iht (d + 1) (d' + 1) m n (by omega) (by omega), ihu d d' m n h1 h2]

theorem Raise_Raise (t : MT) : ∀ i n p k, i ≤ n →
    Raise i p (Raise n k t) = Raise (p + n) k (Raise i p t) := by
  induction t with
  | nil => intros; rfl
  | var j =>
    intro i n p k h
    var_arith
  | lam t ih =>
    intro i n p k h
    simp only [Raise]
    rw [ih (i + 1) (n + 1) p k (by omega)]
    rfl
  | app t u iht ihu => intro i n p k h; simp [Raise, iht i n p k h, ihu i n p k h]
  | beta t u iht ihu =>
    intro i n p k h
    simp only [Raise]
    rw [iht (i + 1) (n + 1) p k (by omega), ihu i n p k h]
    rfl

/-! ### Substitution -/

theorem Subst_ne_nil {v : MT} (hv : v ≠ nil) : ∀ {t : MT}, t ≠ nil → ∀ n, Subst n v t ≠ nil := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | var i =>
    intro _ n
    simp only [Subst]
    split_ifs
    · simp
    · exact Raise_ne_nil hv _ _
    · simp
  | lam t ih => intro _ n; simp [Subst]
  | app t u _ _ => intro _ n; simp [Subst]
  | beta t u _ _ => intro _ n; simp [Subst]

/-- Closing tactic for variable cases involving `Subst` and `Raise`. -/
macro "sub_arith" : tactic =>
  `(tactic| (simp only [Raise, Subst]; split_ifs <;> (try simp only [Raise, Subst]) <;>
    (try split_ifs) <;>
    first | omega | (congr 1; omega) | (simp_all; omega) | rfl))

theorem Raise_Subst (t : MT) : ∀ (p n k : ℕ) (v : MT),
    Raise (p + n) k (Subst p v t) = Subst p (Raise n k v) (Raise (p + n + 1) k t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro p n k v
    by_cases h2 : p = i
    · subst h2
      have e := Raise_Raise v 0 n p k (Nat.zero_le _)
      simp only [Subst, Raise]
      split_ifs <;> (try simp only [Subst, Raise]) <;> (try split_ifs) <;>
        first | omega | (simp_all; done) | (rw [e]) | (rw [← e])
    · sub_arith
  | lam t ih =>
    intro p n k v
    simp only [Subst, Raise]
    have := ih (p + 1) n k v
    rw [show p + 1 + n = p + n + 1 by omega] at this
    rw [this]
  | app t u iht ihu => intro p n k v; simp only [Subst, Raise, iht, ihu]
  | beta t u iht ihu =>
    intro p n k v
    simp only [Subst, Raise]
    have := iht (p + 1) n k v
    rw [show p + 1 + n = p + n + 1 by omega] at this
    rw [this, ihu]

theorem Raise_Subst' {v : MT} (hv : v ≠ nil) (t : MT) : ∀ (k p n : ℕ), k ≤ n →
    Raise k p (Subst n v t) = Subst (p + n) v (Raise k p t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro k p n h
    have e := Raise_plus' v 0 k p n (by omega) (by omega)
    simp only [Subst, Raise]
    split_ifs <;> (try simp only [Subst, Raise]) <;> (try split_ifs) <;>
      first | omega | (simp_all; done) | (congr 1; omega) | (rw [e]) | (rw [← e]) | rfl
  | lam t ih =>
    intro k p n h
    simp only [Subst, Raise]
    rw [ih (k + 1) p (n + 1) (by omega), show p + (n + 1) = p + n + 1 by omega]
  | app t u iht ihu => intro k p n h; simp only [Subst, Raise, iht k p n h, ihu k p n h]
  | beta t u iht ihu =>
    intro k p n h
    simp only [Subst, Raise]
    rw [iht (k + 1) p (n + 1) (by omega), ihu k p n h, show p + (n + 1) = p + n + 1 by omega]

theorem Subst_Raise {v : MT} (t : MT) : ∀ (d m n : ℕ), d ≤ m → m ≤ n + d →
    Subst m v (Raise d (n + 1) t) = Raise d n t := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro d m n h1 h2
    simp only [Raise]
    split_ifs <;> (try simp only [Subst, Raise]) <;> (try split_ifs) <;>
      first | omega | (congr 1; omega) | (simp_all; omega) | rfl
  | lam t ih =>
    intro d m n h1 h2
    simp only [Raise, Subst]
    rw [ih (d + 1) (m + 1) n (by omega) (by omega)]
  | app t u iht ihu => intro d m n h1 h2; simp only [Raise, Subst, iht d m n h1 h2, ihu d m n h1 h2]
  | beta t u iht ihu =>
    intro d m n h1 h2
    simp only [Raise, Subst]
    rw [iht (d + 1) (m + 1) n (by omega) (by omega), ihu d m n h1 h2]

theorem Subst_Subst {v w : MT} (hv : v ≠ nil) (hw : w ≠ nil) (t : MT) : ∀ (m n : ℕ),
    Subst (m + n) w (Subst m v t) = Subst m (Subst n w v) (Subst (m + n + 1) w t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro m n
    have e1 := Raise_Subst' (v := w) hw v 0 m n (Nat.zero_le _)
    have e2 := Subst_Raise (v := Subst n w v) w 0 m (m + n) (Nat.zero_le _) (by omega)
    simp only [Subst]
    split_ifs <;> (try simp only [Subst]) <;> (try split_ifs) <;>
      first | omega | (simp_all; done) | (congr 1; omega) | (rw [← e1]) | (rw [e1]) | (rw [e2]) |
        (rw [← e2]) | rfl
  | lam t ih =>
    intro m n
    simp only [Subst]
    have := ih (m + 1) n
    rw [show m + 1 + n = m + n + 1 by omega] at this
    rw [this]
  | app t u iht ihu => intro m n; simp only [Subst, iht, ihu]
  | beta t u iht ihu =>
    intro m n
    simp only [Subst]
    have := iht (m + 1) n
    rw [show m + 1 + n = m + n + 1 by omega] at this
    rw [this, ihu]

theorem substitution_lemma {v w : MT} (hv : v ≠ nil) (hw : w ≠ nil) (t : MT) (n : ℕ) :
    Subst n v (Subst 0 w t) = Subst 0 (Subst n v w) (Subst (n + 1) v t) := by
  have := Subst_Subst hw hv t 0 n
  simpa using this

theorem Raise_subst (t v : MT) (n k : ℕ) :
    Raise n k (Subst 0 v t) = Subst 0 (Raise n k v) (Raise (n + 1) k t) := by
  have := Raise_Subst t 0 n k v
  simpa using this

theorem Raise_eq_nil_iff {t : MT} {d n : ℕ} : Raise d n t = nil ↔ t = nil := by
  constructor
  · intro h; by_contra hne; exact Raise_ne_nil hne d n h
  · rintro rfl; rfl

/-! ### Residuation -/

/-- Residuation of marked terms: `resid t u` is `t \ u` (or `nil` if undefined). -/
def resid : MT → MT → MT
  | var i, var j => if i = j then var i else nil
  | lam t, lam t' => if resid t t' = nil then nil else lam (resid t t')
  | app t u, app t' u' =>
      if resid t t' = nil ∨ resid u u' = nil then nil else app (resid t t') (resid u u')
  | beta t u, beta t' u' =>
      if resid t t' = nil ∨ resid u u' = nil then nil else Subst 0 (resid u u') (resid t t')
  | app (lam t) u, beta t' u' =>
      if resid t t' = nil ∨ resid u u' = nil then nil else Subst 0 (resid u u') (resid t t')
  | beta t u, app (lam t') u' =>
      if resid t t' = nil ∨ resid u u' = nil then nil else beta (resid t t') (resid u u')
  | _, _ => nil

@[simp] theorem resid_nil_left (u : MT) : resid nil u = nil := by cases u <;> rfl

/-- Size of a marked term (for well-founded induction). -/
def size : MT → ℕ
  | nil => 0
  | var _ => 1
  | lam t => size t + 1
  | app t u => size t + size u + 1
  | beta t u => size t + size u + 2

@[simp] theorem Raise_var' (d n i : ℕ) :
    Raise d n (var i) = var (if d ≤ i then i + n else i) := by
  simp only [Raise]; split_ifs <;> rfl

@[simp] theorem Raise_lam (d n : ℕ) (t : MT) : Raise d n (lam t) = lam (Raise (d + 1) n t) := rfl
@[simp] theorem Raise_app (d n : ℕ) (t u : MT) :
    Raise d n (app t u) = app (Raise d n t) (Raise d n u) := rfl
@[simp] theorem Raise_beta (d n : ℕ) (t u : MT) :
    Raise d n (beta t u) = beta (Raise (d + 1) n t) (Raise d n u) := rfl
@[simp] theorem Raise_nil' (d n : ℕ) : Raise d n nil = nil := rfl

@[simp] theorem resid_nil_right (t : MT) : resid t nil = nil := by cases t <;> rfl

/-- Raising commutes with residuation (stated right to left so the induction hypotheses rewrite). -/
theorem resid_Raise (t u : MT) (k n : ℕ) :
    resid (Raise k n t) (Raise k n u) = Raise k n (resid t u) := by
  induction t, u using resid.induct generalizing k
  case case13 t x h1 h2 h3 h4 h5 h6 =>
    cases t <;> cases x
    all_goals first
      | exact (h1 _ _ rfl rfl).elim | exact (h2 _ _ rfl rfl).elim | exact (h3 _ _ _ _ rfl rfl).elim
      | exact (h4 _ _ _ _ rfl rfl).elim | skip
    case app.beta a b c d => cases a <;> first | exact (h5 _ _ _ _ rfl rfl).elim | simp [resid]
    case beta.app a b c d => cases c <;> first | exact (h6 _ _ _ _ rfl rfl).elim | simp [resid]
    all_goals simp [resid]
  all_goals simp_all [resid, Raise_eq_nil_iff, Raise_subst]
  split_ifs <;> omega

theorem Raise_resid (t u : MT) (k n : ℕ) :
    Raise k n (resid t u) = resid (Raise k n t) (Raise k n u) :=
  (resid_Raise t u k n).symm

@[simp] theorem Subst_var_eq (n : ℕ) (v : MT) : Subst n v (var n) = Raise 0 n v := by
  simp [Subst]

/-- **Huet's commutation theorem**: substitution commutes with residuation. -/
theorem resid_Subst {t t' u u' : MT} (ht : resid t t' ≠ nil) (hu : resid u u' ≠ nil) (n : ℕ) :
    resid (Subst n t u) (Subst n t' u') = Subst n (resid t t') (resid u u') := by
  induction u, u' using resid.induct generalizing n <;> simp_all [Subst, resid, Subst_ne_nil]
  · split_ifs <;> simp [resid, Raise_resid]
  all_goals exact (substitution_lemma ht (by simp_all) _ n).symm

/-! ### Arrows, sources and targets -/

/-- Arrows: terms without `nil`. -/
def Arr : MT → Prop
  | nil => False
  | var _ => True
  | lam t => Arr t
  | app t u => Arr t ∧ Arr u
  | beta t u => Arr t ∧ Arr u

/-- Source: erase all marks. -/
def Src : MT → MT
  | nil => nil
  | var i => var i
  | lam t => lam (Src t)
  | app t u => app (Src t) (Src u)
  | beta t u => app (lam (Src t)) (Src u)

/-- Target: contract all marked redexes. -/
def Trg : MT → MT
  | nil => nil
  | var i => var i
  | lam t => lam (Trg t)
  | app t u => app (Trg t) (Trg u)
  | beta t u => Subst 0 (Trg u) (Trg t)

theorem Arr_ne_nil {t : MT} (h : Arr t) : t ≠ nil := by
  rintro rfl; exact h

theorem Arr_Raise (t : MT) : ∀ d n, Arr (Raise d n t) ↔ Arr t := by
  induction t with
  | nil => intros; rfl
  | var i => intro d n; simp [Arr]
  | lam t ih => intro d n; simp [Arr, ih]
  | app t u iht ihu => intro d n; simp [Arr, iht, ihu]
  | beta t u iht ihu => intro d n; simp [Arr, iht, ihu]

theorem Arr_Subst {v : MT} (hv : Arr v) (t : MT) : ∀ n, Arr t → Arr (Subst n v t) := by
  induction t with
  | nil => intro n h; exact h.elim
  | var i =>
    intro n _
    simp only [Subst]
    split_ifs
    · trivial
    · exact (Arr_Raise v 0 n).2 hv
    · trivial
  | lam t ih => intro n h; exact ih (n + 1) h
  | app t u iht ihu => intro n h; exact ⟨iht n h.1, ihu n h.2⟩
  | beta t u iht ihu => intro n h; exact ⟨iht (n + 1) h.1, ihu n h.2⟩

theorem Src_Raise (t : MT) : ∀ d n, Src (Raise d n t) = Raise d n (Src t) := by
  induction t with
  | nil => intros; rfl
  | var i => intro d n; simp [Src]
  | lam t ih => intro d n; simp [Src, ih]
  | app t u iht ihu => intro d n; simp [Src, iht, ihu]
  | beta t u iht ihu => intro d n; simp [Src, iht, ihu]

theorem Src_Subst {v : MT} (t : MT) : ∀ d, Src (Subst d v t) = Subst d (Src v) (Src t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro d
    simp only [Subst, Src]
    split_ifs <;> simp [Src, Src_Raise]
  | lam t ih => intro d; simp [Subst, Src, ih]
  | app t u iht ihu => intro d; simp [Subst, Src, iht, ihu]
  | beta t u iht ihu => intro d; simp [Subst, Src, iht, ihu]

theorem Arr_resid {t u : MT} (h : resid t u ≠ nil) : Arr (resid t u) := by
  fun_induction resid t u <;> simp_all [Arr, Arr_Subst]

/-- The leftover case of `resid.induct`: terms of non-matching shapes are not coinitial. -/
theorem not_coinitial_of_shape {t x : MT}
    (h1 : ∀ i j, t = var i → x = var j → False) (h2 : ∀ a b, t = lam a → x = lam b → False)
    (h3 : ∀ a b c d, t = app a b → x = app c d → False)
    (h4 : ∀ a b c d, t = beta a b → x = beta c d → False)
    (h5 : ∀ a b c d, t = app (lam a) b → x = beta c d → False)
    (h6 : ∀ a b c d, t = beta a b → x = app (lam c) d → False)
    (ht : Arr t) (hx : Arr x) (he : Src t = Src x) : False := by
  cases t <;> cases x <;> simp only [Arr, Src, reduceCtorEq, app.injEq, lam.injEq] at ht hx he
  all_goals first
    | exact h1 _ _ rfl rfl | exact h2 _ _ rfl rfl | exact h3 _ _ _ _ rfl rfl
    | exact h4 _ _ _ _ rfl rfl | skip
  case app.beta a b c d =>
    cases a <;> simp only [Src, reduceCtorEq, false_and] at he
    exact h5 _ _ _ _ rfl rfl
  case beta.app a b c d =>
    cases c <;> simp only [Src, reduceCtorEq, false_and] at he
    exact h6 _ _ _ _ rfl rfl

theorem Con_iff {t u : MT} : resid t u ≠ nil ↔ Arr t ∧ Arr u ∧ Src t = Src u := by
  constructor
  · intro h
    fun_induction resid t u <;> simp_all [Arr, Src]
  · rintro ⟨ht, hu, he⟩
    fun_induction resid t u <;> simp_all [Arr, Src, resid, Subst_ne_nil]
    exact not_coinitial_of_shape ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ht hu he

theorem Arr_Trg (t : MT) : Arr t → Arr (Trg t) := by
  induction t with
  | nil => intro h; exact h.elim
  | var i => intro _; trivial
  | lam t ih => intro h; exact ih h
  | app t u iht ihu => intro h; exact ⟨iht h.1, ihu h.2⟩
  | beta t u iht ihu => intro h; exact Arr_Subst (ihu h.2) _ 0 (iht h.1)

theorem resid_self (t : MT) : Arr t → resid t t = Trg t := by
  induction t with
  | nil => intro h; exact h.elim
  | var i => intro _; simp [resid, Trg]
  | lam t ih => intro h; simp [resid, Trg, ih h, Arr_ne_nil (Arr_Trg t h)]
  | app t u iht ihu =>
    intro h
    simp [resid, Trg, iht h.1, ihu h.2, Arr_ne_nil (Arr_Trg t h.1), Arr_ne_nil (Arr_Trg u h.2)]
  | beta t u iht ihu =>
    intro h
    simp [resid, Trg, iht h.1, ihu h.2, Arr_ne_nil (Arr_Trg t h.1), Arr_ne_nil (Arr_Trg u h.2)]

theorem Src_resid {t u : MT} (h : resid t u ≠ nil) : Src (resid t u) = Trg u := by
  fun_induction resid t u <;> simp_all [Src, Trg, Src_Subst]

/-- Residuals of coinitial terms along the same term are consistent. -/
theorem Con_resid_resid {t u v : MT} (h1 : resid t v ≠ nil) (h2 : resid u v ≠ nil) :
    resid (resid t v) (resid u v) ≠ nil :=
  Con_iff.2 ⟨Arr_resid h1, Arr_resid h2, by rw [Src_resid h1, Src_resid h2]⟩

theorem resid_ne_nil_parts {a b : MT} (h : resid a b ≠ nil) : a ≠ nil ∧ b ≠ nil :=
  ⟨fun e => by subst e; simp at h, fun e => by subst e; simp at h⟩

set_option maxHeartbeats 4000000 in
/-- **Lévy's cube lemma** for marked terms. -/
theorem Cube_aux : ∀ (s : ℕ) (t u v : MT), size t ≤ s → resid (resid v t) (resid u t) ≠ nil →
    resid (resid v t) (resid u t) = resid (resid v u) (resid t u) := by
  intro s
  induction s with
  | zero => intro t u v hs H; cases t <;> simp_all [size]
  | succ s ih =>
    intro t u v hs H
    have hv : resid v t ≠ nil := (resid_ne_nil_parts H).1
    have hu : resid u t ≠ nil := (resid_ne_nil_parts H).2
    -- the generic induction step for a pair of components
    have step : ∀ {t1 u1 v1 : MT}, size t1 ≤ s → resid v1 t1 ≠ nil → resid u1 t1 ≠ nil →
        resid (resid v1 t1) (resid u1 t1) = resid (resid v1 u1) (resid t1 u1) ∧
        resid (resid v1 t1) (resid u1 t1) ≠ nil ∧
        resid (resid v1 u1) (resid t1 u1) ≠ nil ∧ resid v1 u1 ≠ nil ∧ resid t1 u1 ≠ nil := by
      intro t1 u1 v1 hs1 h1 h2
      have hc := Con_resid_resid h1 h2
      have E := ih t1 u1 v1 hs1 hc
      have hR : resid (resid v1 u1) (resid t1 u1) ≠ nil := E ▸ hc
      exact ⟨E, hc, hR, (resid_ne_nil_parts hR).1, (resid_ne_nil_parts hR).2⟩
    cases t with
    | nil => simp at hv
    | var i =>
      cases v with
      | var j =>
        cases u with
        | var k => by_cases hij : j = i <;> by_cases hki : k = i <;> simp_all [resid]
        | _ => simp [resid] at hu
      | _ => simp [resid] at hv
    | lam t1 =>
      cases v with
      | lam v1 =>
        cases u with
        | lam u1 =>
          have hv1 : resid v1 t1 ≠ nil := by intro e; simp [resid, e] at hv
          have hu1 : resid u1 t1 ≠ nil := by intro e; simp [resid, e] at hu
          obtain ⟨E, hc, hR, h3, h4⟩ := step (by simp [size] at hs; omega) hv1 hu1
          simp only [resid, hv1, hu1, h3, h4, hc, hR, ite_false]
          rw [E]
        | _ => simp [resid] at hu
      | _ => simp [resid] at hv
    | app t1 t2 =>
      cases v with
      | app v1 v2 =>
        cases u with
        | app u1 u2 =>
          have hv1 : resid v1 t1 ≠ nil := by intro e; simp [resid, e] at hv
          have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
          have hu1 : resid u1 t1 ≠ nil := by intro e; simp [resid, e] at hu
          have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
          obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
          obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
          simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hc1, hc2, hR1, hR2, or_self,
            ite_false, reduceCtorEq, or_false, false_or]
          rw [E1, E2]
        | beta u1 u2 =>
          cases t1 with
          | lam t11 =>
            cases v1 with
            | lam v11 =>
              have hv1 : resid v11 t11 ≠ nil := by intro e; simp [resid, e] at hv
              have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
              have hu1 : resid u1 t11 ≠ nil := by intro e; simp [resid, e] at hu
              have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
              obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
              obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
              simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hc1, hc2, hR1, hR2, or_self,
                ite_false, reduceCtorEq, or_false, false_or]
              rw [resid_Subst hR2 hR1, E1, E2]
            | _ => simp [resid] at hv
          | _ => simp [resid] at hu
        | _ => simp [resid] at hu
      | beta v1 v2 =>
        cases t1 with
        | lam t11 =>
          cases u with
          | beta u1 u2 =>
            have hv1 : resid v1 t11 ≠ nil := by intro e; simp [resid, e] at hv
            have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
            have hu1 : resid u1 t11 ≠ nil := by intro e; simp [resid, e] at hu
            have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
            obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
            obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
            simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hc1, hc2, hR1, hR2, or_self,
              ite_false, reduceCtorEq, or_false, false_or]
            rw [resid_Subst hR2 hR1, E1, E2]
          | app u1 u2 =>
            cases u1 with
            | lam u11 =>
              have hv1 : resid v1 t11 ≠ nil := by intro e; simp [resid, e] at hv
              have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
              have hu1 : resid u11 t11 ≠ nil := by intro e; simp [resid, e] at hu
              have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
              obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
              obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
              simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hc1, hc2, hR1, hR2, or_self,
                ite_false, reduceCtorEq, or_false, false_or]
              rw [E1, E2]
            | _ => simp [resid] at hu
          | _ => simp [resid] at hu
        | _ => simp [resid] at hv
      | _ => simp [resid] at hv
    | beta t1 t2 =>
      cases v with
      | beta v1 v2 =>
        cases u with
        | beta u1 u2 =>
          have hv1 : resid v1 t1 ≠ nil := by intro e; simp [resid, e] at hv
          have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
          have hu1 : resid u1 t1 ≠ nil := by intro e; simp [resid, e] at hu
          have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
          obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
          obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
          simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, or_self, ite_false, reduceCtorEq, or_false, false_or]
          rw [resid_Subst hc2 hc1, resid_Subst hR2 hR1, E1, E2]
        | app u1 u2 =>
          cases u1 with
          | lam u11 =>
            have hv1 : resid v1 t1 ≠ nil := by intro e; simp [resid, e] at hv
            have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
            have hu1 : resid u11 t1 ≠ nil := by intro e; simp [resid, e] at hu
            have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
            obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
            obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
            simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hR1, hR2, or_self, ite_false, reduceCtorEq, or_false, false_or]
            rw [resid_Subst hc2 hc1, E1, E2]
          | _ => simp [resid] at hu
        | _ => simp [resid] at hu
      | app v1 v2 =>
        cases v1 with
        | lam v11 =>
          cases u with
          | beta u1 u2 =>
            have hv1 : resid v11 t1 ≠ nil := by intro e; simp [resid, e] at hv
            have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
            have hu1 : resid u1 t1 ≠ nil := by intro e; simp [resid, e] at hu
            have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
            obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
            obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
            simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, or_self, ite_false, reduceCtorEq, or_false, false_or]
            rw [resid_Subst hc2 hc1, resid_Subst hR2 hR1, E1, E2]
          | app u1 u2 =>
            cases u1 with
            | lam u11 =>
              have hv1 : resid v11 t1 ≠ nil := by intro e; simp [resid, e] at hv
              have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
              have hu1 : resid u11 t1 ≠ nil := by intro e; simp [resid, e] at hu
              have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
              obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
              obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
              simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hR1, hR2, or_self, ite_false, reduceCtorEq, or_false, false_or]
              rw [resid_Subst hc2 hc1, E1, E2]
            | _ => simp [resid] at hu
          | _ => simp [resid] at hu
        | _ => simp [resid] at hv
      | _ => simp [resid] at hv

theorem Cube {t u v : MT} (H : resid (resid v t) (resid u t) ≠ nil) :
    resid (resid v t) (resid u t) = resid (resid v u) (resid t u) :=
  Cube_aux _ t u v le_rfl H

theorem resid_Src (t : MT) : Arr t → resid t (Src t) = t := by
  induction t with
  | nil => intro h; exact h.elim
  | var i => intro _; simp [resid, Src]
  | lam t ih => intro h; simp [resid, Src, ih h, Arr_ne_nil (show Arr t from h)]
  | app t u iht ihu =>
    intro h
    simp [resid, Src, iht h.1, ihu h.2, Arr_ne_nil h.1, Arr_ne_nil h.2]
  | beta t u iht ihu =>
    intro h
    simp [resid, Src, iht h.1, ihu h.2, Arr_ne_nil h.1, Arr_ne_nil h.2]

/-! ### de Vrijer's measure for finite developments -/

/-- Multiplicity of the variable `x` (the maximal number of copies along developments). -/
def mtp : ℕ → MT → ℕ
  | _, nil => 0
  | x, var z => if z = x then 1 else 0
  | x, lam t => mtp (x + 1) t
  | x, app t u => mtp x t + mtp x u
  | x, beta t u => mtp (x + 1) t + mtp x u * max 1 (mtp 0 t)

/-- Height: a bound on the length of developments. -/
def hgt : MT → ℕ
  | nil => 0
  | var _ => 0
  | lam t => hgt t
  | app t u => hgt t + hgt u
  | beta t u => hgt t + hgt u * max 1 (mtp 0 t) + 1

theorem mtp_Raise_lt (t : MT) : ∀ x d k, x < d → mtp x (Raise d k t) = mtp x t := by
  induction t with
  | nil => intros; rfl
  | var z => intro x d k h; simp only [Raise_var', mtp]; split_ifs <;> omega
  | lam t ih => intro x d k h; simp [mtp, ih (x + 1) (d + 1) k (by omega)]
  | app t u iht ihu => intro x d k h; simp [mtp, iht x d k h, ihu x d k h]
  | beta t u iht ihu =>
    intro x d k h
    simp [mtp, iht (x + 1) (d + 1) k (by omega), ihu x d k h, iht 0 (d + 1) k (by omega)]

theorem mtp_Raise (t : MT) : ∀ x d l k, l ≤ d → mtp (x + d + k) (Raise l k t) = mtp (x + d) t := by
  induction t with
  | nil => intros; rfl
  | var z => intro x d l k h; simp only [Raise_var', mtp]; split_ifs <;> omega
  | lam t ih =>
    intro x d l k h
    simp only [Raise, mtp]
    have := ih x (d + 1) (l + 1) k (by omega)
    rw [show x + (d + 1) + k = x + d + k + 1 by omega, show x + (d + 1) = x + d + 1 by omega] at this
    exact this
  | app t u iht ihu => intro x d l k h; simp [mtp, iht x d l k h, ihu x d l k h]
  | beta t u iht ihu =>
    intro x d l k h
    simp only [Raise, mtp]
    have h1 := iht x (d + 1) (l + 1) k (by omega)
    rw [show x + (d + 1) + k = x + d + k + 1 by omega, show x + (d + 1) = x + d + 1 by omega] at h1
    rw [h1, ihu x d l k h, mtp_Raise_lt t 0 (l + 1) k (by omega)]

theorem mtp_Raise_zero (u : MT) (k : ℕ) : mtp k (Raise 0 k u) = mtp 0 u := by
  have := mtp_Raise u 0 0 0 k (le_refl _)
  simpa using this

theorem mtp_Raise_self (t : MT) : ∀ l k, mtp l (Raise l (k + 1) t) = 0 := by
  induction t with
  | nil => intros; rfl
  | var z => intro l k; simp only [Raise_var', mtp]; split_ifs <;> omega
  | lam t ih => intro l k; simp [mtp, ih (l + 1) k]
  | app t u iht ihu => intro l k; simp [mtp, iht l k, ihu l k]
  | beta t u iht ihu => intro l k; simp [mtp, iht (l + 1) k, ihu l k]

theorem mtp_Subst_cancel (u t : MT) : ∀ k d, mtp k (Subst (d + 1 + k) u t) = mtp k t := by
  induction t with
  | nil => intros; rfl
  | var z =>
    intro k d
    simp only [Subst]
    split_ifs with h1 h2
    · simp only [mtp]; split_ifs <;> omega
    · subst h2
      have e : Raise 0 (d + 1 + k) u = Raise k (d + 1) (Raise 0 k u) := by
        have := Raise_plus u 0 k (d + 1); simpa [Nat.add_comm] using this
      rw [e, mtp_Raise_self]
      simp only [mtp]; split_ifs <;> omega
    · rfl
  | lam t ih =>
    intro k d
    simp only [Subst, mtp]
    have := ih (k + 1) d
    rwa [show d + 1 + (k + 1) = d + 1 + k + 1 by omega] at this
  | app t1 t2 ih1 ih2 => intro k d; simp [Subst, mtp, ih1 k d, ih2 k d]
  | beta t1 t2 ih1 ih2 =>
    intro k d
    simp only [Subst, mtp]
    have h1 := ih1 (k + 1) d
    rw [show d + 1 + (k + 1) = d + 1 + k + 1 by omega] at h1
    have h0 := ih1 0 (d + k + 1)
    rw [show d + k + 1 + 1 + 0 = d + 1 + k + 1 by omega] at h0
    rw [h1, ih2 k d, h0]

theorem mtp_Subst' (u t : MT) : ∀ x d, mtp (x + d + 1) (Subst d u t) =
    mtp (x + d + 2) t + mtp (x + 1) u * mtp d t := by
  induction t with
  | nil => intros; simp [Subst, mtp]
  | var z =>
    intro x d
    simp only [Subst]
    split_ifs with h1 h2
    · simp only [mtp]; split_ifs <;> first | omega | simp_all <;> omega
    · subst h2
      have := mtp_Raise u (x + 1) 0 0 d (le_refl _)
      simp only [Nat.add_zero] at this
      rw [show x + d + 1 = x + 1 + d by omega, this]
      simp [mtp]; omega
    · simp only [mtp]; split_ifs <;> first | omega | simp_all <;> omega
  | lam t ih =>
    intro x d
    simp only [Subst, mtp]
    have := ih x (d + 1)
    rw [show x + (d + 1) + 1 = x + d + 1 + 1 by omega,
      show x + (d + 1) + 2 = x + d + 2 + 1 by omega] at this
    exact this
  | app t1 t2 ih1 ih2 => intro x d; simp [Subst, mtp, ih1 x d, ih2 x d]; ring
  | beta t1 t2 ih1 ih2 =>
    intro x d
    simp only [Subst, mtp]
    have h1 := ih1 x (d + 1)
    rw [show x + (d + 1) + 1 = x + d + 1 + 1 by omega,
      show x + (d + 1) + 2 = x + d + 2 + 1 by omega] at h1
    have h0 := mtp_Subst_cancel u t1 0 d
    simp only [Nat.add_zero] at h0
    rw [h1, ih2 x d, h0]
    ring

theorem mtp_Subst_self (u t : MT) : ∀ k, mtp k (Subst k u t) = mtp (k + 1) t + mtp 0 u * mtp k t := by
  induction t with
  | nil => intros; simp [Subst, mtp]
  | var z =>
    intro k
    simp only [Subst]
    split_ifs with h1 h2
    · simp only [mtp]; split_ifs <;> first | omega | simp_all <;> omega
    · subst h2; rw [mtp_Raise_zero]; simp [mtp]
    · simp only [mtp]; split_ifs <;> first | omega | simp_all <;> omega
  | lam t ih => intro k; simp only [Subst, mtp]; rw [ih (k + 1)]
  | app t1 t2 ih1 ih2 => intro k; simp [Subst, mtp, ih1 k, ih2 k]; ring
  | beta t1 t2 ih1 ih2 =>
    intro k
    simp only [Subst, mtp]
    have h0 := mtp_Subst_cancel u t1 0 k
    simp only [Nat.add_zero] at h0
    rw [ih1 (k + 1), ih2 k, h0]
    ring

theorem mtp0_subst_le (u t : MT) : mtp 0 (Subst 0 u t) ≤ mtp 1 t + mtp 0 u * max 1 (mtp 0 t) := by
  rw [mtp_Subst_self]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (le_max_right _ _)) _

theorem hgt_Raise (t : MT) : ∀ l k, hgt (Raise l k t) = hgt t := by
  induction t with
  | nil => intros; rfl
  | var z => intro l k; simp [hgt]
  | lam t ih => intro l k; simp [hgt, ih]
  | app t u iht ihu => intro l k; simp [hgt, iht, ihu]
  | beta t u iht ihu => intro l k; simp [hgt, iht, ihu, mtp_Raise_lt t 0 (l + 1) k (by omega)]

theorem hgt_Subst (u t : MT) : ∀ k, hgt (Subst k u t) = hgt t + hgt u * mtp k t := by
  induction t with
  | nil => intros; simp [Subst, hgt, mtp]
  | var z =>
    intro k
    simp only [Subst]
    split_ifs with h1 h2
    · simp [hgt, mtp]; omega
    · subst h2; simp [hgt, mtp, hgt_Raise]
    · simp [hgt, mtp]; omega
  | lam t ih => intro k; simp only [Subst, hgt, mtp]; rw [ih (k + 1)]
  | app t1 t2 ih1 ih2 => intro k; simp [Subst, hgt, mtp, ih1 k, ih2 k]; ring
  | beta t1 t2 ih1 ih2 =>
    intro k
    simp only [Subst, hgt, mtp]
    have h0 := mtp_Subst_cancel u t1 0 k
    simp only [Nat.add_zero] at h0
    rw [ih1 (k + 1), ih2 k, h0]
    ring

end MT

end Thesis.Marked
