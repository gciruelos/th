/-
# Chapter 1: Preliminaries — Appendix (Auxiliary Lemmas)

Structural helper lemmas for lax 2-functors, derivations in `ResidualSystem`, and equivalence
between position-based `BetaStep` and inductive `Beta`.
-/
import Thesis.Chapter1PrelimDefs

namespace Thesis

universe u v

namespace LaxFunctor

variable {A : Type u} [PartialOrder A] {B : LaxFunctor.{u, v} A}

theorem map_congr {a b : A} (h h' : a ≤ b) (x : B.obj a) : B.map h x = B.map h' x := rfl

end LaxFunctor

namespace ResidualSystem

variable (R : ResidualSystem)

@[simp] theorem tgt_nil (t : R.Obj) : R.tgt t [] = t := rfl
@[simp] theorem tgt_cons (t : R.Obj) (a σ) : R.tgt t (a :: σ) = R.tgt (R.contract t a) σ := rfl
theorem tgt_append (t : R.Obj) (σ τ : List R.Adr) : R.tgt t (σ ++ τ) = R.tgt (R.tgt t σ) τ := by
  simp [tgt, List.foldl_append]

@[simp] theorem valid_nil (t : R.Obj) : R.Valid t [] := trivial
@[simp] theorem valid_cons (t : R.Obj) (a σ) :
    R.Valid t (a :: σ) ↔ R.isStep t a ∧ R.Valid (R.contract t a) σ := Iff.rfl

theorem valid_append (t : R.Obj) (σ τ : List R.Adr) :
    R.Valid t (σ ++ τ) ↔ R.Valid t σ ∧ R.Valid (R.tgt t σ) τ := by
  induction σ generalizing t with
  | nil => simp
  | cons a σ ih => simp [ih, and_assoc]

theorem valid_singleton {R : ResidualSystem} {t : R.Obj} {a : R.Adr} (ha : R.isStep t a) :
    R.Valid t [a] := ⟨ha, trivial⟩

variable {R}

@[simp] theorem resSet_empty (t : R.Obj) (b : R.Adr) : R.resSet t ∅ b = ∅ := by
  simp [resSet]

theorem resSet_singleton (t : R.Obj) (a b : R.Adr) : R.resSet t {a} b = R.res t b a := by
  simp [resSet]

theorem resSet_union (t : R.Obj) (M N : Finset R.Adr) (b : R.Adr) :
    R.resSet t (M ∪ N) b = R.resSet t M b ∪ R.resSet t N b := by
  ext c
  simp [resSet, or_and_right, exists_or]

theorem resSet_mono {t : R.Obj} {M N : Finset R.Adr} {b : R.Adr} (h : M ⊆ N) :
    R.resSet t M b ⊆ R.resSet t N b :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem resSet_biUnion {α : Type*} [DecidableEq α] (t : R.Obj) (S : Finset α)
    (f : α → Finset R.Adr) (b : R.Adr) :
    R.resSet t (S.biUnion f) b = S.biUnion (fun x => R.resSet t (f x) b) := by
  ext c
  simp only [resSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ⟨x, hx, ha⟩, hc⟩
    exact ⟨x, hx, a, ha, hc⟩
  · rintro ⟨x, hx, a, ha, hc⟩
    exact ⟨a, ⟨x, hx, ha⟩, hc⟩

@[simp] theorem resSetDeriv_nil (t : R.Obj) (M : Finset R.Adr) : R.resSetDeriv t M [] = M := rfl

@[simp] theorem resSetDeriv_cons (t : R.Obj) (M : Finset R.Adr) (b : R.Adr) (τ : List R.Adr) :
    R.resSetDeriv t M (b :: τ) = R.resSetDeriv (R.contract t b) (R.resSet t M b) τ := rfl

@[simp] theorem resSetDeriv_empty (t : R.Obj) (τ : List R.Adr) : R.resSetDeriv t ∅ τ = ∅ := by
  induction τ generalizing t with
  | nil => rfl
  | cons b τ ih => simp [ih]

theorem resSetDeriv_append (t : R.Obj) (M : Finset R.Adr) (σ τ : List R.Adr) :
    R.resSetDeriv t M (σ ++ τ) = R.resSetDeriv (R.tgt t σ) (R.resSetDeriv t M σ) τ := by
  induction σ generalizing t M with
  | nil => rfl
  | cons a σ ih => exact ih _ _

theorem resSetDeriv_union (t : R.Obj) (M N : Finset R.Adr) (τ : List R.Adr) :
    R.resSetDeriv t (M ∪ N) τ = R.resSetDeriv t M τ ∪ R.resSetDeriv t N τ := by
  induction τ generalizing t M N with
  | nil => rfl
  | cons b τ ih => rw [resSetDeriv_cons, resSet_union, ih]; rfl

theorem resSetDeriv_biUnion {α : Type*} [DecidableEq α] (t : R.Obj) (S : Finset α)
    (f : α → Finset R.Adr) (τ : List R.Adr) :
    R.resSetDeriv t (S.biUnion f) τ = S.biUnion (fun x => R.resSetDeriv t (f x) τ) := by
  induction τ generalizing t f with
  | nil => rfl
  | cons b τ ih => rw [resSetDeriv_cons, resSet_biUnion, ih]; rfl

theorem resSetDeriv_eq_biUnion (t : R.Obj) (M : Finset R.Adr) (τ : List R.Adr) :
    R.resSetDeriv t M τ = M.biUnion (fun a => R.resSetDeriv t {a} τ) := by
  have hM : M = M.biUnion (fun a => {a}) := by ext c; simp
  conv_lhs => rw [hM]
  exact resSetDeriv_biUnion t M (fun a => {a}) τ

theorem isDevelopment_valid {t : R.Obj} {M : Finset R.Adr} {σ : List R.Adr}
    (h : R.IsDevelopment t M σ) : R.Valid t σ := by
  induction σ generalizing t M with
  | nil => trivial
  | cons a σ ih => exact ⟨h.1, ih h.2.2⟩

theorem isDevelopment_mono {t : R.Obj} {M N : Finset R.Adr} {σ : List R.Adr}
    (hsub : M ⊆ N) (h : R.IsDevelopment t M σ) : R.IsDevelopment t N σ := by
  induction σ generalizing t M N with
  | nil => trivial
  | cons a σ ih => exact ⟨h.1, hsub h.2.1, ih (resSet_mono hsub) h.2.2⟩

theorem isDevelopment_append {t : R.Obj} {M : Finset R.Adr} {σ τ : List R.Adr} :
    R.IsDevelopment t M (σ ++ τ) ↔
      R.IsDevelopment t M σ ∧ R.IsDevelopment (R.tgt t σ) (R.resSetDeriv t M σ) τ := by
  induction σ generalizing t M with
  | nil => simp [IsDevelopment]
  | cons a σ ih =>
    simp only [List.cons_append, IsDevelopment, tgt_cons, resSetDeriv_cons, ih, and_assoc]

@[simp] theorem isDevelopment_empty {t : R.Obj} {σ : List R.Adr} :
    R.IsDevelopment t ∅ σ ↔ σ = [] := by
  cases σ with
  | nil => simp [IsDevelopment]
  | cons a σ => simp [IsDevelopment]

section OrthogonalHelpers

variable (hR : R.Orthogonal)
include hR

theorem resSet_isStep {t : R.Obj} {M : Finset R.Adr} {b : R.Adr}
    (hM : ∀ a ∈ M, R.isStep t a) (hb : R.isStep t b) :
    ∀ c ∈ R.resSet t M b, R.isStep (R.contract t b) c := by
  intro c hc
  rcases Finset.mem_biUnion.1 hc with ⟨a, ha, hc⟩
  exact hR.res_isStep t a b (hM a ha) hb c hc

theorem resSetDeriv_isStep {t : R.Obj} {M : Finset R.Adr} {τ : List R.Adr}
    (hM : ∀ a ∈ M, R.isStep t a) (hτ : R.Valid t τ) :
    ∀ c ∈ R.resSetDeriv t M τ, R.isStep (R.tgt t τ) c := by
  induction τ generalizing t M with
  | nil => exact hM
  | cons b τ ih => exact ih (resSet_isStep hR hM hτ.1) hτ.2

theorem dev_empty (t : R.Obj) : R.dev t ∅ = [] := by
  have h := (hR.dev_complete t ∅ (by simp)).1
  exact isDevelopment_empty.1 h

theorem isCompleteDevelopment_singleton {t : R.Obj} {a : R.Adr} {σ : List R.Adr}
    (ha : R.isStep t a) : R.IsCompleteDevelopment t {a} σ ↔ σ = [a] := by
  constructor
  · rintro ⟨hd, hc⟩
    cases σ with
    | nil =>
      simp only [resSetDeriv_nil] at hc
      exact absurd (Finset.mem_singleton_self a) (by rw [hc]; simp)
    | cons b σ' =>
      obtain ⟨hb, hmem, hd'⟩ := hd
      obtain rfl : b = a := Finset.mem_singleton.1 hmem
      rw [resSet_singleton, hR.autoerasure t b hb, isDevelopment_empty] at hd'
      subst hd'
      rfl
  · rintro rfl
    refine ⟨⟨ha, Finset.mem_singleton_self a, ?_⟩, ?_⟩
    · simp [IsDevelopment]
    · simp [resSet_singleton, hR.autoerasure t a ha]

theorem dev_singleton {t : R.Obj} {a : R.Adr} (ha : R.isStep t a) : R.dev t {a} = [a] :=
  (isCompleteDevelopment_singleton hR ha).1 (hR.dev_complete t {a} (by simpa))

theorem dev_valid {t : R.Obj} {M : Finset R.Adr} (hM : ∀ a ∈ M, R.isStep t a) :
    R.Valid t (R.dev t M) :=
  isDevelopment_valid (hR.dev_complete t M hM).1

theorem projM_empty {t : R.Obj} {τ : List R.Adr} (hτ : R.Valid t τ) : R.projM t τ ∅ = τ := by
  induction τ generalizing t with
  | nil => rfl
  | cons b τ ih =>
    simp [projM, dev_empty hR, dev_singleton hR hτ.1, ih hτ.2]

theorem dev_bounded {t : R.Obj} {M : Finset R.Adr} (hM : ∀ a ∈ M, R.isStep t a) :
    ∃ B : ℕ, ∀ σ, R.IsDevelopment t M σ → σ.length ≤ B := by
  classical
  by_contra hunb
  let Unb (p : R.Obj × Finset R.Adr) : Prop :=
    (∀ a ∈ p.2, R.isStep p.1 a) ∧ ¬ ∃ B : ℕ, ∀ σ, R.IsDevelopment p.1 p.2 σ → σ.length ≤ B
  have hstep : ∀ p, Unb p → ∃ a ∈ p.2, Unb (R.contract p.1 a, R.resSet p.1 p.2 a) := by
    intro ⟨u, N⟩ ⟨hN, hu⟩
    by_contra hall
    push Not at hall
    have hbnd : ∀ x : {a // a ∈ N}, ∃ B : ℕ,
        ∀ σ, R.IsDevelopment (R.contract u x.1) (R.resSet u N x.1) σ → σ.length ≤ B := by
      intro ⟨a, ha⟩
      by_contra hnb
      exact hall a ha ⟨resSet_isStep hR hN (hN a ha), hnb⟩
    choose f hf using hbnd
    refine hu ⟨(N.attach.image f).sup id + 1, ?_⟩
    intro σ hσ
    cases σ with
    | nil => simp
    | cons a σ' =>
      obtain ⟨_, ha, hσ'⟩ := hσ
      have hle : σ'.length ≤ f ⟨a, ha⟩ := hf ⟨a, ha⟩ σ' hσ'
      have hsup : f ⟨a, ha⟩ ≤ (N.attach.image f).sup id :=
        Finset.le_sup (f := id) (Finset.mem_image_of_mem f (Finset.mem_attach N ⟨a, ha⟩))
      simp only [List.length_cons]
      omega
  let next (q : {p // Unb p}) : {p // Unb p} :=
    let h := hstep q.1 q.2
    ⟨(R.contract q.1.1 (Classical.choose h), R.resSet q.1.1 q.1.2 (Classical.choose h)),
      (Classical.choose_spec h).2⟩
  let seq : ℕ → {p // Unb p} := fun n => Nat.rec ⟨(t, M), ⟨hM, hunb⟩⟩ (fun _ q => next q) n
  have hseq_succ : ∀ n, seq (n + 1) = next (seq n) := fun _ => rfl
  let stepOf (q : {p // Unb p}) : R.Adr := Classical.choose (hstep q.1 q.2)
  have hstepOf_mem : ∀ q, stepOf q ∈ q.1.2 := fun q => (Classical.choose_spec (hstep q.1 q.2)).1
  have hnext_fst : ∀ q, (next q).1 =
      (R.contract q.1.1 (stepOf q), R.resSet q.1.1 q.1.2 (stepOf q)) := fun _ => rfl
  refine hR.finite_developments t M hM ⟨fun n => stepOf (seq n), ?_⟩
  suffices hgen : ∀ n k, R.IsDevelopment (seq k).1.1 (seq k).1.2
      (List.ofFn fun i : Fin n => stepOf (seq (k + i))) from fun n => by simpa [seq] using hgen n 0
  intro n
  induction n with
  | zero => intro k; simp [IsDevelopment]
  | succ n ih =>
    intro k
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Nat.add_zero, IsDevelopment]
    have ha_mem : stepOf (seq k) ∈ (seq k).1.2 := hstepOf_mem (seq k)
    refine ⟨(seq k).2.1 _ ha_mem, ha_mem, ?_⟩
    have heq : (List.ofFn fun i : Fin n => stepOf (seq (k + i.succ))) =
        (List.ofFn fun i : Fin n => stepOf (seq (k + 1 + i))) := by
      congr 1
      funext i
      exact congrArg (fun m => stepOf (seq m)) (Nat.add_right_comm k i.val 1)
    rw [heq]
    have h1 := ih (k + 1)
    rwa [hseq_succ k, hnext_fst] at h1

noncomputable def minBound {t : R.Obj} {M : Finset R.Adr} (hM : ∀ a ∈ M, R.isStep t a) : ℕ := by
  classical
  exact Nat.find (dev_bounded hR hM)

theorem length_le_minBound {t : R.Obj} {M : Finset R.Adr} (hM : ∀ a ∈ M, R.isStep t a)
    {σ : List R.Adr} (hσ : R.IsDevelopment t M σ) : σ.length ≤ minBound hR hM := by
  classical
  exact Nat.find_spec (dev_bounded hR hM) σ hσ

theorem minBound_step_lt {t : R.Obj} {M : Finset R.Adr} (hM : ∀ a ∈ M, R.isStep t a)
    {a : R.Adr} (ha : a ∈ M) :
    minBound hR (resSet_isStep hR hM (hM a ha)) < minBound hR hM := by
  classical
  have hpos : 1 ≤ minBound hR hM :=
    length_le_minBound hR hM (σ := [a]) ⟨hM a ha, ha, trivial⟩
  have hle : minBound hR (resSet_isStep hR hM (hM a ha)) ≤ minBound hR hM - 1 := by
    refine Nat.find_min' (dev_bounded hR (resSet_isStep hR hM (hM a ha))) ?_
    intro σ' hσ'
    have hcons : (a :: σ').length ≤ minBound hR hM :=
      length_le_minBound hR hM ⟨hM a ha, ha, hσ'⟩
    simp only [List.length_cons] at hcons
    omega
  omega

theorem completeDevelopment_unique {t : R.Obj} {M : Finset R.Adr}
    (hM : ∀ a ∈ M, R.isStep t a) {σ τ : List R.Adr}
    (hσ : R.IsCompleteDevelopment t M σ) (hτ : R.IsCompleteDevelopment t M τ) :
    R.tgt t σ = R.tgt t τ ∧
      ∀ c, R.isStep t c → R.resSetDeriv t {c} σ = R.resSetDeriv t {c} τ := by
  suffices h : ∀ k (t : R.Obj) (M : Finset R.Adr) (hM : ∀ a ∈ M, R.isStep t a),
      minBound hR hM ≤ k → ∀ {σ τ},
      R.IsCompleteDevelopment t M σ → R.IsCompleteDevelopment t M τ →
      R.tgt t σ = R.tgt t τ ∧
        ∀ c, R.isStep t c → R.resSetDeriv t {c} σ = R.resSetDeriv t {c} τ from
    h (minBound hR hM) t M hM le_rfl hσ hτ
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro t M hM hk σ τ hσ hτ
    cases σ with
    | nil =>
      have hMe : M = ∅ := hσ.2
      subst hMe
      have hτe : τ = [] := isDevelopment_empty.1 hτ.1
      subst hτe
      exact ⟨rfl, fun _ _ => rfl⟩
    | cons a σ' =>
      cases τ with
      | nil =>
        have hMe : M = ∅ := hτ.2
        subst hMe
        exact absurd hσ.1.2.1 (by simp)
      | cons b τ' =>
        obtain ⟨⟨ha, haM, hσ'd⟩, hσ'c⟩ := hσ
        obtain ⟨⟨hb, hbM, hτ'd⟩, hτ'c⟩ := hτ
        have hMa := resSet_isStep hR hM ha
        have hMb := resSet_isStep hR hM hb
        have hka : minBound hR hMa < k := lt_of_lt_of_le (minBound_step_lt hR hM haM) hk
        have hkb : minBound hR hMb < k := lt_of_lt_of_le (minBound_step_lt hR hM hbM) hk
        obtain ⟨δa, δb, hδa, hδb, htg, hres⟩ := hR.semantic_orthogonality t a b ha hb
        -- `δb` is a development of `M / a` out of `contract t a`, and `δa` of `M / b` out of `contract t b`.
        have hδb_dev : R.IsDevelopment (R.contract t a) (R.resSet t M a) δb := by
          refine isDevelopment_mono ?_ hδb.1
          rw [← resSet_singleton]
          exact resSet_mono (Finset.singleton_subset_iff.2 hbM)
        have hδa_dev : R.IsDevelopment (R.contract t b) (R.resSet t M b) δa := by
          refine isDevelopment_mono ?_ hδa.1
          rw [← resSet_singleton]
          exact resSet_mono (Finset.singleton_subset_iff.2 haM)
        have hNa_eq_Nb : R.resSetDeriv t M (a :: δb) = R.resSetDeriv t M (b :: δa) := by
          rw [resSetDeriv_eq_biUnion, resSetDeriv_eq_biUnion]
          refine Finset.biUnion_congr rfl fun c hc => hres c (hM c hc)
        let w := R.tgt (R.contract t a) δb
        let N := R.resSetDeriv (R.contract t a) (R.resSet t M a) δb
        have hNw : ∀ c ∈ N, R.isStep w c :=
          resSetDeriv_isStep hR hMa (isDevelopment_valid hδb_dev)
        let π := R.dev w N
        have hπ : R.IsCompleteDevelopment w N π := hR.dev_complete w N hNw
        have hcomp_a : R.IsCompleteDevelopment (R.contract t a) (R.resSet t M a) (δb ++ π) := by
          refine ⟨isDevelopment_append.2 ⟨hδb_dev, hπ.1⟩, ?_⟩
          rw [resSetDeriv_append]
          exact hπ.2
        have hcomp_b : R.IsCompleteDevelopment (R.contract t b) (R.resSet t M b) (δa ++ π) := by
          have hNb : R.resSetDeriv (R.contract t b) (R.resSet t M b) δa = N := hNa_eq_Nb.symm
          refine ⟨isDevelopment_append.2 ⟨hδa_dev, ?_⟩, ?_⟩
          · rw [htg, hNb]; exact hπ.1
          · rw [resSetDeriv_append, htg, hNb]; exact hπ.2
        obtain ⟨htg1, hres1⟩ := ih _ hka (R.contract t a) _ hMa le_rfl ⟨hσ'd, hσ'c⟩ hcomp_a
        obtain ⟨htg2, hres2⟩ := ih _ hkb (R.contract t b) _ hMb le_rfl ⟨hτ'd, hτ'c⟩ hcomp_b
        refine ⟨?_, ?_⟩
        · simp only [tgt_cons, htg1, htg2, tgt_append, htg]
        · intro c hc
          have hca : ∀ d ∈ R.resSet t {c} a, R.isStep (R.contract t a) d :=
            resSet_isStep hR (by simpa) ha
          have hcb : ∀ d ∈ R.resSet t {c} b, R.isStep (R.contract t b) d :=
            resSet_isStep hR (by simpa) hb
          have h1 : R.resSetDeriv (R.contract t a) (R.resSet t {c} a) σ' =
              R.resSetDeriv (R.contract t a) (R.resSet t {c} a) (δb ++ π) := by
            rw [resSetDeriv_eq_biUnion, resSetDeriv_eq_biUnion]
            exact Finset.biUnion_congr rfl fun d hd => hres1 d (hca d hd)
          have h2 : R.resSetDeriv (R.contract t b) (R.resSet t {c} b) τ' =
              R.resSetDeriv (R.contract t b) (R.resSet t {c} b) (δa ++ π) := by
            rw [resSetDeriv_eq_biUnion, resSetDeriv_eq_biUnion]
            exact Finset.biUnion_congr rfl fun d hd => hres2 d (hcb d hd)
          simp only [resSetDeriv_cons, h1, h2, resSetDeriv_append, htg]
          have hmid : R.resSetDeriv (R.contract t a) (R.resSet t {c} a) δb =
              R.resSetDeriv (R.contract t b) (R.resSet t {c} b) δa := hres c hc
          rw [hmid]

theorem completeDevelopment_resSetDeriv_eq {t : R.Obj} {M P : Finset R.Adr}
    (hM : ∀ a ∈ M, R.isStep t a) (hP : ∀ c ∈ P, R.isStep t c) {σ τ : List R.Adr}
    (hσ : R.IsCompleteDevelopment t M σ) (hτ : R.IsCompleteDevelopment t M τ) :
    R.resSetDeriv t P σ = R.resSetDeriv t P τ := by
  rw [resSetDeriv_eq_biUnion, resSetDeriv_eq_biUnion]
  exact Finset.biUnion_congr rfl fun c hc => (completeDevelopment_unique hR hM hσ hτ).2 c (hP c hc)

end OrthogonalHelpers

theorem completeDevelopment_union {t : R.Obj} {M N : Finset R.Adr}
    {δM δN' : List R.Adr}
    (hM : R.IsCompleteDevelopment t M δM)
    (hN' : R.IsCompleteDevelopment (R.tgt t δM) (R.resSetDeriv t N δM) δN') :
    R.IsCompleteDevelopment t (M ∪ N) (δM ++ δN') := by
  have hdM : R.IsDevelopment t (M ∪ N) δM := isDevelopment_mono Finset.subset_union_left hM.1
  have hres : R.resSetDeriv t (M ∪ N) δM = R.resSetDeriv t N δM := by
    rw [resSetDeriv_union, hM.2, Finset.empty_union]
  refine ⟨isDevelopment_append.2 ⟨hdM, hres ▸ hN'.1⟩, ?_⟩
  rw [resSetDeriv_append, hres, hN'.2]

theorem projM_append {t : R.Obj} (τ₁ τ₂ : List R.Adr) (M : Finset R.Adr) :
    R.projM t (τ₁ ++ τ₂) M =
      R.projM t τ₁ M ++ R.projM (R.tgt t τ₁) τ₂ (R.resSetDeriv t M τ₁) := by
  induction τ₁ generalizing t M with
  | nil => simp [projM]
  | cons b τ₁ ih => simp [projM, ih, List.append_assoc]

theorem dev_step_square (hR : R.Orthogonal) {t : R.Obj} {M : Finset R.Adr} {b : R.Adr}
    (hM : ∀ a ∈ M, R.isStep t a) (hb : R.isStep t b) :
    R.tgt (R.tgt t (R.dev t M)) (R.dev (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M))) =
      R.tgt (R.contract t b) (R.dev (R.contract t b) (R.resSet t M b)) ∧
    ∀ P : Finset R.Adr, (∀ c ∈ P, R.isStep t c) →
      R.resSetDeriv t P
          (R.dev t M ++ R.dev (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M))) =
        R.resSetDeriv t P (b :: R.dev (R.contract t b) (R.resSet t M b)) := by
  have hMb := resSet_isStep hR hM hb
  have hB' : ∀ c ∈ R.resSetDeriv t {b} (R.dev t M), R.isStep (R.tgt t (R.dev t M)) c :=
    resSetDeriv_isStep hR (by simpa) (dev_valid hR hM)
  have hc1 : R.IsCompleteDevelopment t (M ∪ {b})
      (R.dev t M ++ R.dev (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M))) :=
    completeDevelopment_union (hR.dev_complete t M hM) (hR.dev_complete _ _ hB')
  have h1 : R.IsCompleteDevelopment t {b} [b] := (isCompleteDevelopment_singleton hR hb).2 rfl
  have hc2 : R.IsCompleteDevelopment t ({b} ∪ M)
      (b :: R.dev (R.contract t b) (R.resSet t M b)) := by
    simpa using completeDevelopment_union h1 (hR.dev_complete _ _ hMb)
  have hc2' : R.IsCompleteDevelopment t (M ∪ {b})
      (b :: R.dev (R.contract t b) (R.resSet t M b)) :=
    (Finset.union_comm M {b}) ▸ hc2
  have hMb_all : ∀ a ∈ M ∪ {b}, R.isStep t a := by
    intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · exact hM a ha
    · exact (Finset.mem_singleton.1 ha) ▸ hb
  refine ⟨?_, fun P hP => completeDevelopment_resSetDeriv_eq hR hMb_all hP hc1 hc2'⟩
  simpa [tgt_append] using (completeDevelopment_unique hR hMb_all hc1 hc2').1

theorem projM_valid_and_tgt_and_res (hR : R.Orthogonal) {t : R.Obj} {τ : List R.Adr}
    {M : Finset R.Adr} (hτ : R.Valid t τ) (hM : ∀ a ∈ M, R.isStep t a) :
    R.Valid (R.tgt t (R.dev t M)) (R.projM t τ M) ∧
      R.tgt (R.tgt t (R.dev t M)) (R.projM t τ M) =
        R.tgt (R.tgt t τ) (R.dev (R.tgt t τ) (R.resSetDeriv t M τ)) ∧
      ∀ P : Finset R.Adr, (∀ c ∈ P, R.isStep t c) →
        R.resSetDeriv t P (R.dev t M ++ R.projM t τ M) =
          R.resSetDeriv t P (τ ++ R.dev (R.tgt t τ) (R.resSetDeriv t M τ)) := by
  induction τ generalizing t M with
  | nil =>
    refine ⟨trivial, rfl, fun P _ => ?_⟩
    simp [projM]
  | cons b τ ih =>
    obtain ⟨hb, hτ'⟩ := hτ
    have hMb := resSet_isStep hR hM hb
    obtain ⟨hv, htg_ih, hres_ih⟩ := ih hτ' hMb
    obtain ⟨htg_sq, hres_sq⟩ := dev_step_square hR hM hb
    have hB' : ∀ c ∈ R.resSetDeriv t {b} (R.dev t M), R.isStep (R.tgt t (R.dev t M)) c :=
      resSetDeriv_isStep hR (by simpa) (dev_valid hR hM)
    refine ⟨?_, ?_, ?_⟩
    · simp only [projM]
      rw [R.valid_append]
      refine ⟨dev_valid hR hB', ?_⟩
      rwa [htg_sq]
    · simp only [projM, tgt_append]
      rw [htg_sq]
      exact htg_ih
    · intro P hP
      simp only [projM, ← List.append_assoc]
      rw [resSetDeriv_append _ _ (R.dev t M ++ _), hres_sq P hP, tgt_append, htg_sq]
      simpa [resSetDeriv_append] using hres_ih (R.resSet t P b) (resSet_isStep hR hP hb)

theorem projM_valid (hR : R.Orthogonal) {t : R.Obj} {τ : List R.Adr} {M : Finset R.Adr}
    (hτ : R.Valid t τ) (hM : ∀ a ∈ M, R.isStep t a) :
    R.Valid (R.tgt t (R.dev t M)) (R.projM t τ M) :=
  (projM_valid_and_tgt_and_res hR hτ hM).1

theorem projM_isCompleteDevelopment (hR : R.Orthogonal) {t : R.Obj} {P M : Finset R.Adr}
    {δ : List R.Adr} (hP : ∀ c ∈ P, R.isStep t c) (hM : ∀ a ∈ M, R.isStep t a)
    (hδ : R.IsCompleteDevelopment t P δ) :
    R.IsCompleteDevelopment (R.tgt t (R.dev t M)) (R.resSetDeriv t P (R.dev t M))
      (R.projM t δ M) := by
  induction δ generalizing t P M with
  | nil =>
    have hPe : P = ∅ := hδ.2
    subst hPe
    simp [projM, IsCompleteDevelopment]
  | cons b δ ih =>
    obtain ⟨⟨hb, hbP, hδd⟩, hδc⟩ := hδ
    have hPb := resSet_isStep hR hP hb
    have hMb := resSet_isStep hR hM hb
    have ih' := ih hPb hMb ⟨hδd, hδc⟩
    obtain ⟨htg_sq, hres_sq⟩ := dev_step_square hR hM hb
    have hB' : ∀ c ∈ R.resSetDeriv t {b} (R.dev t M), R.isStep (R.tgt t (R.dev t M)) c :=
      resSetDeriv_isStep hR (by simpa) (dev_valid hR hM)
    have hc_head := hR.dev_complete (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M)) hB'
    have hres_tail : R.resSetDeriv (R.tgt t (R.dev t M)) (R.resSetDeriv t P (R.dev t M))
        (R.dev (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M))) =
        R.resSetDeriv (R.contract t b) (R.resSet t P b)
          (R.dev (R.contract t b) (R.resSet t M b)) := by
      rw [← resSetDeriv_append, hres_sq P hP, resSetDeriv_cons]
    have hc_tail : R.IsCompleteDevelopment
        (R.tgt (R.tgt t (R.dev t M))
          (R.dev (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M))))
        (R.resSetDeriv (R.tgt t (R.dev t M)) (R.resSetDeriv t P (R.dev t M))
          (R.dev (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M))))
        (R.projM (R.contract t b) δ (R.resSet t M b)) := by
      rwa [htg_sq, hres_tail]
    have hcomb := completeDevelopment_union hc_head hc_tail
    have hunion : R.resSetDeriv t {b} (R.dev t M) ∪ R.resSetDeriv t P (R.dev t M) =
        R.resSetDeriv t P (R.dev t M) := by
      rw [← resSetDeriv_union, Finset.singleton_union, Finset.insert_eq_of_mem hbP]
    simpa [projM, hunion] using hcomb

/-- Permutation equivalence generated inductively by elementary swaps `a (b/a) ~ b (a/b)`,
congruence under concatenation, reflexivity, symmetry, and transitivity. -/
inductive PermGen (R : ResidualSystem) : R.Obj → List R.Adr → List R.Adr → Prop
  | refl {t σ} : R.Valid t σ → PermGen R t σ σ
  | swap {t a b} : R.isStep t a → R.isStep t b →
      PermGen R t (a :: R.dev (R.contract t a) (R.res t a b))
        (b :: R.dev (R.contract t b) (R.res t b a))
  | symm {t σ τ} : PermGen R t σ τ → PermGen R t τ σ
  | trans {t σ τ ρ} : PermGen R t σ τ → PermGen R t τ ρ → PermGen R t σ ρ
  | append {t σ₁ σ₂ τ₁ τ₂} : PermGen R t σ₁ σ₂ →
      PermGen R (R.tgt t σ₁) τ₁ τ₂ → PermGen R t (σ₁ ++ τ₁) (σ₂ ++ τ₂)

theorem swap_isCompleteDevelopment (hR : R.Orthogonal) {t : R.Obj} {a b : R.Adr}
    (ha : R.isStep t a) (hb : R.isStep t b) :
    R.IsCompleteDevelopment t ({a} ∪ {b}) (a :: R.dev (R.contract t a) (R.res t a b)) := by
  have h1 : R.IsCompleteDevelopment t {a} [a] := (isCompleteDevelopment_singleton hR ha).2 rfl
  have hab : ∀ c ∈ R.res t a b, R.isStep (R.contract t a) c := hR.res_isStep t b a hb ha
  have h2 : R.IsCompleteDevelopment (R.tgt t [a]) (R.resSetDeriv t {b} [a])
      (R.dev (R.contract t a) (R.res t a b)) := by
    simpa [resSet_singleton] using hR.dev_complete (R.contract t a) (R.res t a b) hab
  simpa using completeDevelopment_union h1 h2

theorem PermGen.props (hR : R.Orthogonal) {t : R.Obj} {σ τ : List R.Adr}
    (h : PermGen R t σ τ) :
    R.Valid t σ ∧ R.Valid t τ ∧ R.tgt t σ = R.tgt t τ ∧
      ∀ P : Finset R.Adr, (∀ c ∈ P, R.isStep t c) →
        R.resSetDeriv t P σ = R.resSetDeriv t P τ := by
  induction h with
  | refl hσ => exact ⟨hσ, hσ, rfl, fun _ _ => rfl⟩
  | @swap t a b ha hb =>
    have hc1 := swap_isCompleteDevelopment hR ha hb
    have hc2 : R.IsCompleteDevelopment t ({a} ∪ {b})
        (b :: R.dev (R.contract t b) (R.res t b a)) :=
      (Finset.union_comm {b} {a}) ▸ swap_isCompleteDevelopment hR hb ha
    have hab : ∀ c ∈ ({a} ∪ {b} : Finset R.Adr), R.isStep t c := by
      intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · exact (Finset.mem_singleton.1 hc) ▸ ha
      · exact (Finset.mem_singleton.1 hc) ▸ hb
    exact ⟨isDevelopment_valid hc1.1, isDevelopment_valid hc2.1,
      (completeDevelopment_unique hR hab hc1 hc2).1,
      fun P hP => completeDevelopment_resSetDeriv_eq hR hab hP hc1 hc2⟩
  | symm _ ih =>
    exact ⟨ih.2.1, ih.1, ih.2.2.1.symm, fun P hP => (ih.2.2.2 P hP).symm⟩
  | trans _ _ ih₁ ih₂ =>
    exact ⟨ih₁.1, ih₂.2.1, ih₁.2.2.1.trans ih₂.2.2.1,
      fun P hP => (ih₁.2.2.2 P hP).trans (ih₂.2.2.2 P hP)⟩
  | append _ _ ih₁ ih₂ =>
    refine ⟨(R.valid_append _ _ _).2 ⟨ih₁.1, ih₂.1⟩,
      (R.valid_append _ _ _).2 ⟨ih₁.2.1, ih₁.2.2.1 ▸ ih₂.2.1⟩, ?_, ?_⟩
    · rw [tgt_append, tgt_append, ← ih₁.2.2.1, ih₂.2.2.1]
    · intro P hP
      rw [resSetDeriv_append, resSetDeriv_append, ← ih₁.2.2.2 P hP, ← ih₁.2.2.1]
      exact ih₂.2.2.2 _ (resSetDeriv_isStep hR hP ih₁.1)

theorem PermGen.valid_left (hR : R.Orthogonal) {t : R.Obj} {σ τ : List R.Adr}
    (h : PermGen R t σ τ) : R.Valid t σ := (h.props hR).1

theorem PermGen.valid_right (hR : R.Orthogonal) {t : R.Obj} {σ τ : List R.Adr}
    (h : PermGen R t σ τ) : R.Valid t τ := (h.props hR).2.1

theorem PermGen.tgt_eq (hR : R.Orthogonal) {t : R.Obj} {σ τ : List R.Adr}
    (h : PermGen R t σ τ) : R.tgt t σ = R.tgt t τ := (h.props hR).2.2.1

theorem PermGen.resSetDeriv_eq (hR : R.Orthogonal) {t : R.Obj} {σ τ : List R.Adr}
    (h : PermGen R t σ τ) {P : Finset R.Adr} (hP : ∀ c ∈ P, R.isStep t c) :
    R.resSetDeriv t P σ = R.resSetDeriv t P τ := (h.props hR).2.2.2 P hP

theorem permGen_cons {t : R.Obj} {a : R.Adr} {σ τ : List R.Adr}
    (ha : R.isStep t a) (h : PermGen R (R.contract t a) σ τ) :
    PermGen R t (a :: σ) (a :: τ) :=
  PermGen.append (σ₁ := [a]) (σ₂ := [a]) (PermGen.refl (valid_singleton ha)) h

theorem permGen_of_completeDevelopment (hR : R.Orthogonal) {t : R.Obj} {M : Finset R.Adr}
    (hM : ∀ a ∈ M, R.isStep t a) {σ τ : List R.Adr}
    (hσ : R.IsCompleteDevelopment t M σ) (hτ : R.IsCompleteDevelopment t M τ) :
    PermGen R t σ τ := by
  suffices h : ∀ k (t : R.Obj) (M : Finset R.Adr) (hM : ∀ a ∈ M, R.isStep t a),
      minBound hR hM ≤ k → ∀ {σ τ},
      R.IsCompleteDevelopment t M σ → R.IsCompleteDevelopment t M τ → PermGen R t σ τ from
    h (minBound hR hM) t M hM le_rfl hσ hτ
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro t M hM hk σ τ hσ hτ
    cases σ with
    | nil =>
      have hMe : M = ∅ := hσ.2
      subst hMe
      have hτe : τ = [] := isDevelopment_empty.1 hτ.1
      subst hτe
      exact PermGen.refl trivial
    | cons a σ' =>
      cases τ with
      | nil =>
        have hMe : M = ∅ := hτ.2
        subst hMe
        exact absurd hσ.1.2.1 (by simp)
      | cons b τ' =>
        obtain ⟨⟨ha, haM, hσ'd⟩, hσ'c⟩ := hσ
        obtain ⟨⟨hb, hbM, hτ'd⟩, hτ'c⟩ := hτ
        have hMa := resSet_isStep hR hM ha
        have hMb := resSet_isStep hR hM hb
        have hka : minBound hR hMa < k := lt_of_lt_of_le (minBound_step_lt hR hM haM) hk
        have hkb : minBound hR hMb < k := lt_of_lt_of_le (minBound_step_lt hR hM hbM) hk
        let δb := R.dev (R.contract t a) (R.res t a b)
        let δa := R.dev (R.contract t b) (R.res t b a)
        have hsw : PermGen R t (a :: δb) (b :: δa) := PermGen.swap ha hb
        have hδb_dev : R.IsDevelopment (R.contract t a) (R.resSet t M a) δb := by
          refine isDevelopment_mono ?_ (hR.dev_complete _ _ (hR.res_isStep t b a hb ha)).1
          rw [← resSet_singleton]
          exact resSet_mono (Finset.singleton_subset_iff.2 hbM)
        have hδa_dev : R.IsDevelopment (R.contract t b) (R.resSet t M b) δa := by
          refine isDevelopment_mono ?_ (hR.dev_complete _ _ (hR.res_isStep t a b ha hb)).1
          rw [← resSet_singleton]
          exact resSet_mono (Finset.singleton_subset_iff.2 haM)
        let w := R.tgt t (a :: δb)
        let N := R.resSetDeriv t M (a :: δb)
        have hNw : ∀ c ∈ N, R.isStep w c :=
          resSetDeriv_isStep hR hM (hsw.valid_left hR)
        let π := R.dev w N
        have hπ : R.IsCompleteDevelopment w N π := hR.dev_complete w N hNw
        have hcomp_a : R.IsCompleteDevelopment (R.contract t a) (R.resSet t M a) (δb ++ π) :=
          ⟨isDevelopment_append.2 ⟨hδb_dev, hπ.1⟩, by rw [resSetDeriv_append]; exact hπ.2⟩
        have hcomp_b : R.IsCompleteDevelopment (R.contract t b) (R.resSet t M b) (δa ++ π) := by
          have htg : R.tgt (R.contract t b) δa = w := (hsw.tgt_eq hR).symm
          have hNb : R.resSetDeriv (R.contract t b) (R.resSet t M b) δa = N :=
            (hsw.resSetDeriv_eq hR hM).symm
          refine ⟨isDevelopment_append.2 ⟨hδa_dev, ?_⟩, ?_⟩
          · rw [htg, hNb]; exact hπ.1
          · rw [resSetDeriv_append, htg, hNb]; exact hπ.2
        have ih_a := ih _ hka (R.contract t a) _ hMa le_rfl ⟨hσ'd, hσ'c⟩ hcomp_a
        have ih_b := ih _ hkb (R.contract t b) _ hMb le_rfl hcomp_b ⟨hτ'd, hτ'c⟩
        have h1 : PermGen R t (a :: σ') ((a :: δb) ++ π) := permGen_cons ha ih_a
        have h2 : PermGen R t ((a :: δb) ++ π) ((b :: δa) ++ π) :=
          PermGen.append hsw (PermGen.refl (isDevelopment_valid hπ.1))
        have h3 : PermGen R t ((b :: δa) ++ π) (b :: τ') := permGen_cons hb ih_b
        exact (h1.trans h2).trans h3

theorem PermGen.projM (hR : R.Orthogonal) {t : R.Obj} {τ₁ τ₂ : List R.Adr}
    (h : PermGen R t τ₁ τ₂) {M : Finset R.Adr} (hM : ∀ a ∈ M, R.isStep t a) :
    PermGen R (R.tgt t (R.dev t M)) (R.projM t τ₁ M) (R.projM t τ₂ M) := by
  induction h generalizing M with
  | refl hτ => exact PermGen.refl (projM_valid hR hτ hM)
  | @swap t a b ha hb =>
    have hc1 := swap_isCompleteDevelopment hR ha hb
    have hc2 : R.IsCompleteDevelopment t ({a} ∪ {b})
        (b :: R.dev (R.contract t b) (R.res t b a)) :=
      (Finset.union_comm {b} {a}) ▸ swap_isCompleteDevelopment hR hb ha
    have hab : ∀ c ∈ ({a} ∪ {b} : Finset R.Adr), R.isStep t c := by
      intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · exact (Finset.mem_singleton.1 hc) ▸ ha
      · exact (Finset.mem_singleton.1 hc) ▸ hb
    exact permGen_of_completeDevelopment hR
      (resSetDeriv_isStep hR hab (dev_valid hR hM))
      (projM_isCompleteDevelopment hR hab hM hc1)
      (projM_isCompleteDevelopment hR hab hM hc2)
  | symm _ ih => exact (ih hM).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ hM).trans (ih₂ hM)
  | @append t σ₁ σ₂ τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
    rw [projM_append, projM_append]
    have htg₁ := (projM_valid_and_tgt_and_res hR (h₁.valid_left hR) hM).2.1
    have hM₁ := resSetDeriv_isStep hR hM (h₁.valid_left hR)
    have h₂' : PermGen R (R.tgt (R.tgt t (R.dev t M)) (R.projM t σ₁ M))
        (R.projM (R.tgt t σ₁) τ₁ (R.resSetDeriv t M σ₁))
        (R.projM (R.tgt t σ₂) τ₂ (R.resSetDeriv t M σ₂)) := by
      rw [htg₁, ← h₁.tgt_eq hR, ← h₁.resSetDeriv_eq hR hM]
      exact ih₂ hM₁
    exact PermGen.append (ih₁ hM) h₂'

theorem proj_valid_aux (hR : R.Orthogonal) {t : R.Obj} {σ τ : List R.Adr}
    (hσ : R.Valid t σ) (hτ : R.Valid t τ) : R.Valid (R.tgt t τ) (R.proj t σ τ) := by
  induction σ generalizing t τ with
  | nil => trivial
  | cons a σ ih =>
    obtain ⟨ha, hσ'⟩ := hσ
    simp only [proj]
    rw [R.valid_append]
    have haM : ∀ c ∈ ({a} : Finset R.Adr), R.isStep t c := by simpa
    refine ⟨dev_valid hR (resSetDeriv_isStep hR haM hτ), ?_⟩
    have htg := (projM_valid_and_tgt_and_res hR hτ haM).2.1
    have hpm : R.Valid (R.contract t a) (R.projM t τ {a}) := by
      simpa [dev_singleton hR ha] using projM_valid hR hτ haM
    have hv := ih hσ' hpm
    rw [dev_singleton hR ha] at htg
    exact htg ▸ hv

theorem proj_congr_permGen (hR : R.Orthogonal) {t : R.Obj} {ρ σ τ : List R.Adr}
    (hρ : R.Valid t ρ) (h : PermGen R t σ τ) : R.proj t ρ σ = R.proj t ρ τ := by
  induction ρ generalizing t σ τ with
  | nil => rfl
  | cons a ρ ih =>
    obtain ⟨ha, hρ'⟩ := hρ
    have haM : ∀ c ∈ ({a} : Finset R.Adr), R.isStep t c := by simpa
    simp only [proj]
    have hhead : R.dev (R.tgt t σ) (R.resSetDeriv t {a} σ) =
        R.dev (R.tgt t τ) (R.resSetDeriv t {a} τ) := by
      rw [h.tgt_eq hR, h.resSetDeriv_eq hR haM]
    have hpm : PermGen R (R.contract t a) (R.projM t σ {a}) (R.projM t τ {a}) := by
      simpa [dev_singleton hR ha] using h.projM hR haM
    rw [hhead, ih hρ' hpm]

theorem permGen_projM_eq_proj (hR : R.Orthogonal) {t : R.Obj} {ρ : List R.Adr}
    {M : Finset R.Adr} (hρ : R.Valid t ρ) (hM : ∀ a ∈ M, R.isStep t a) :
    PermGen R (R.tgt t (R.dev t M)) (R.projM t ρ M) (R.proj t ρ (R.dev t M)) := by
  induction ρ generalizing t M with
  | nil => exact PermGen.refl trivial
  | cons b ρ ih =>
    obtain ⟨hb, hρ'⟩ := hρ
    have hMb := resSet_isStep hR hM hb
    have hbM : ∀ c ∈ ({b} : Finset R.Adr), R.isStep t c := by simpa
    obtain ⟨htg_sq, _⟩ := dev_step_square hR hM hb
    have hB' : ∀ c ∈ R.resSetDeriv t {b} (R.dev t M), R.isStep (R.tgt t (R.dev t M)) c :=
      resSetDeriv_isStep hR hbM (dev_valid hR hM)
    have hpm_b : PermGen R (R.contract t b)
        (R.dev (R.contract t b) (R.resSet t M b)) (R.projM t (R.dev t M) {b}) := by
      have hc1 := hR.dev_complete (R.contract t b) (R.resSet t M b) hMb
      have hc2 : R.IsCompleteDevelopment (R.contract t b) (R.resSet t M b)
          (R.projM t (R.dev t M) {b}) := by
        simpa [dev_singleton hR hb] using
          projM_isCompleteDevelopment hR hM hbM (hR.dev_complete t M hM)
      exact permGen_of_completeDevelopment hR hMb hc1 hc2
    have htail_eq : R.proj (R.contract t b) ρ (R.dev (R.contract t b) (R.resSet t M b)) =
        R.proj (R.contract t b) ρ (R.projM t (R.dev t M) {b}) :=
      proj_congr_permGen hR hρ' hpm_b
    simp only [projM, proj, ← htail_eq]
    refine PermGen.append (PermGen.refl (dev_valid hR hB')) ?_
    rw [htg_sq]
    exact ih hρ' hMb

theorem proj_cons_left (hR : R.Orthogonal) {t : R.Obj} {a : R.Adr} {σ ρ : List R.Adr}
    (ha : R.isStep t a) (hσ : R.Valid (R.contract t a) σ) (hρ : R.Valid t ρ) :
    R.proj t (a :: σ) ρ = R.proj t [a] ρ ++ R.proj (R.contract t a) σ (R.proj t ρ [a]) := by
  have hpm : PermGen R (R.contract t a) (R.projM t ρ {a}) (R.proj t ρ [a]) := by
    simpa [dev_singleton hR ha] using permGen_projM_eq_proj hR hρ (M := {a}) (by simpa)
  simp [proj, proj_congr_permGen hR hσ hpm]

/-- Iterated single-step projection along the right argument. -/
noncomputable def iterProj (R : ResidualSystem) : R.Obj → List R.Adr → List R.Adr → List R.Adr
  | _, ρ, [] => ρ
  | t, ρ, a :: σ => iterProj R (R.contract t a) (R.proj t ρ [a]) σ

theorem proj_append_left_iterProj (hR : R.Orthogonal) {t : R.Obj} {σ₁ σ₂ ρ : List R.Adr}
    (hσ : R.Valid t (σ₁ ++ σ₂)) (hρ : R.Valid t ρ) :
    R.proj t (σ₁ ++ σ₂) ρ =
      R.proj t σ₁ ρ ++ R.proj (R.tgt t σ₁) σ₂ (iterProj R t ρ σ₁) := by
  induction σ₁ generalizing t ρ with
  | nil => simp [proj, iterProj]
  | cons a σ₁ ih =>
    rw [List.cons_append] at hσ ⊢
    obtain ⟨ha, hσ'⟩ := hσ
    have hσ₁ : R.Valid (R.contract t a) σ₁ := ((R.valid_append _ _ _).1 hσ').1
    have hρ' : R.Valid (R.contract t a) (R.proj t ρ [a]) :=
      proj_valid_aux hR hρ (valid_singleton ha)
    rw [proj_cons_left hR ha hσ' hρ, ih hσ' hρ', ← List.append_assoc,
      ← proj_cons_left hR ha hσ₁ hρ]
    rfl

theorem proj_isCompleteDevelopment (hR : R.Orthogonal) {t : R.Obj} {P : Finset R.Adr}
    {δ ρ : List R.Adr} (hP : ∀ c ∈ P, R.isStep t c)
    (hδ : R.IsCompleteDevelopment t P δ) (hρ : R.Valid t ρ) :
    R.IsCompleteDevelopment (R.tgt t ρ) (R.resSetDeriv t P ρ) (R.proj t δ ρ) := by
  induction δ generalizing t P ρ with
  | nil =>
    have hPe : P = ∅ := hδ.2
    subst hPe
    simp [proj, IsCompleteDevelopment]
  | cons a δ ih =>
    obtain ⟨⟨ha, haP, hδd⟩, hδc⟩ := hδ
    have haM : ∀ c ∈ ({a} : Finset R.Adr), R.isStep t c := by simpa
    have hPa := resSet_isStep hR hP ha
    have hpm_valid := projM_valid hR hρ haM
    rw [dev_singleton hR ha] at hpm_valid
    have ih' := ih hPa ⟨hδd, hδc⟩ hpm_valid
    obtain ⟨_, htg_sq, hres_sq⟩ := projM_valid_and_tgt_and_res hR hρ haM
    rw [dev_singleton hR ha] at htg_sq hres_sq
    have hc_head := hR.dev_complete (R.tgt t ρ) (R.resSetDeriv t {a} ρ)
      (resSetDeriv_isStep hR haM hρ)
    have hres_eq : R.resSetDeriv (R.contract t a) (R.resSet t P a) (R.projM t ρ {a}) =
        R.resSetDeriv (R.tgt t ρ) (R.resSetDeriv t P ρ)
          (R.dev (R.tgt t ρ) (R.resSetDeriv t {a} ρ)) := by
      simpa [resSetDeriv_append] using hres_sq P hP
    have hc_tail : R.IsCompleteDevelopment
        (R.tgt (R.tgt t ρ) (R.dev (R.tgt t ρ) (R.resSetDeriv t {a} ρ)))
        (R.resSetDeriv (R.tgt t ρ) (R.resSetDeriv t P ρ)
          (R.dev (R.tgt t ρ) (R.resSetDeriv t {a} ρ)))
        (R.proj (R.contract t a) δ (R.projM t ρ {a})) := by
      rwa [← htg_sq, ← hres_eq]
    have hcomb := completeDevelopment_union hc_head hc_tail
    have hunion : R.resSetDeriv t {a} ρ ∪ R.resSetDeriv t P ρ = R.resSetDeriv t P ρ := by
      rw [← resSetDeriv_union, Finset.singleton_union, Finset.insert_eq_of_mem haP]
    simpa [proj, hunion] using hcomb

theorem permGen_projM_projM (hR : R.Orthogonal) {t : R.Obj} {M N : Finset R.Adr}
    {ρ : List R.Adr} (hM : ∀ a ∈ M, R.isStep t a) (hN : ∀ a ∈ N, R.isStep t a)
    (hρ : R.Valid t ρ) :
    PermGen R (R.tgt t (R.dev t (M ∪ N)))
      (R.projM (R.tgt t (R.dev t M)) (R.projM t ρ M) (R.resSetDeriv t N (R.dev t M)))
      (R.projM t ρ (M ∪ N)) := by
  induction ρ generalizing t M N with
  | nil => exact PermGen.refl trivial
  | cons b ρ ih =>
    have hMN : ∀ a ∈ M ∪ N, R.isStep t a := by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · exact hM a ha
      · exact hN a ha
    obtain ⟨hb, hρ'⟩ := hρ
    have hbM : ∀ c ∈ ({b} : Finset R.Adr), R.isStep t c := by simpa
    let δM := R.dev t M
    let N' := R.resSetDeriv t N δM
    have hN' : ∀ c ∈ N', R.isStep (R.tgt t δM) c := resSetDeriv_isStep hR hN (dev_valid hR hM)
    have hc_comb : R.IsCompleteDevelopment t (M ∪ N) (δM ++ R.dev (R.tgt t δM) N') :=
      completeDevelopment_union (hR.dev_complete t M hM) (hR.dev_complete _ N' hN')
    have hc_dev := hR.dev_complete t (M ∪ N) hMN
    have htg_MN : R.tgt (R.tgt t δM) (R.dev (R.tgt t δM) N') = R.tgt t (R.dev t (M ∪ N)) := by
      simpa [tgt_append] using (completeDevelopment_unique hR hMN hc_comb hc_dev).1
    have hres_MN_b : R.resSetDeriv (R.tgt t δM) (R.resSetDeriv t {b} δM) (R.dev (R.tgt t δM) N') =
        R.resSetDeriv t {b} (R.dev t (M ∪ N)) := by
      simpa [resSetDeriv_append] using completeDevelopment_resSetDeriv_eq hR hMN hbM hc_comb hc_dev
    simp only [projM]
    rw [projM_append]
    have hB' : ∀ c ∈ R.resSetDeriv t {b} δM, R.isStep (R.tgt t δM) c :=
      resSetDeriv_isStep hR hbM (dev_valid hR hM)
    have hc_head1 := projM_isCompleteDevelopment hR hB' hN'
      (hR.dev_complete (R.tgt t δM) (R.resSetDeriv t {b} δM) hB')
    rw [htg_MN, hres_MN_b] at hc_head1
    have hc_head2 := hR.dev_complete (R.tgt t (R.dev t (M ∪ N)))
      (R.resSetDeriv t {b} (R.dev t (M ∪ N)))
      (resSetDeriv_isStep hR hbM (dev_valid hR hMN))
    have hpm_head := permGen_of_completeDevelopment hR
      (resSetDeriv_isStep hR hbM (dev_valid hR hMN)) hc_head1 hc_head2
    obtain ⟨htg_sq, hres_sq⟩ := dev_step_square hR hM hb
    obtain ⟨htg_sq_MN, _⟩ := dev_step_square hR hMN hb
    have hN'_step : R.resSetDeriv (R.tgt t δM) N'
        (R.dev (R.tgt t δM) (R.resSetDeriv t {b} δM)) =
        R.resSetDeriv (R.contract t b) (R.resSet t N b)
          (R.dev (R.contract t b) (R.resSet t M b)) := by
      rw [← resSetDeriv_append, hres_sq N hN, resSetDeriv_cons]
    have hpm_tail := ih (resSet_isStep hR hM hb) (resSet_isStep hR hN hb) hρ'
    refine PermGen.append hpm_head ?_
    rw [(hpm_head.tgt_eq hR), htg_sq_MN, htg_sq, hN'_step, resSet_union]
    exact hpm_tail

theorem permGen_iterProj_completeDevelopment (hR : R.Orthogonal) {t : R.Obj}
    {M : Finset R.Adr} {δ ρ : List R.Adr}
    (hM : ∀ a ∈ M, R.isStep t a) (hδ : R.IsCompleteDevelopment t M δ) (hρ : R.Valid t ρ) :
    PermGen R (R.tgt t δ) (iterProj R t ρ δ) (R.projM t ρ M) := by
  induction δ generalizing t M ρ with
  | nil =>
    have hMe : M = ∅ := hδ.2
    subst hMe
    simp only [iterProj, tgt_nil, projM_empty hR hρ]
    exact PermGen.refl hρ
  | cons a δ ih =>
    obtain ⟨⟨ha, haM, hδd⟩, hδc⟩ := hδ
    have haSet : ∀ c ∈ ({a} : Finset R.Adr), R.isStep t c := by simpa
    have hMa := resSet_isStep hR hM ha
    have hρ' : R.Valid (R.contract t a) (R.proj t ρ [a]) :=
      proj_valid_aux hR hρ (valid_singleton ha)
    have ih' := ih hMa ⟨hδd, hδc⟩ hρ'
    have htg_δ : R.tgt (R.contract t a) δ = R.tgt t (R.dev t M) := by
      have hc_a : R.IsCompleteDevelopment t M (a :: δ) := ⟨⟨ha, haM, hδd⟩, hδc⟩
      exact (completeDevelopment_unique hR hM hc_a (hR.dev_complete t M hM)).1
    have hpm_a : PermGen R (R.contract t a) (R.proj t ρ [a]) (R.projM t ρ {a}) := by
      simpa [dev_singleton hR ha] using (permGen_projM_eq_proj hR hρ haSet).symm
    have hpm_mid : PermGen R (R.tgt (R.contract t a) δ)
        (R.projM (R.contract t a) (R.proj t ρ [a]) (R.resSet t M a))
        (R.projM (R.contract t a) (R.projM t ρ {a}) (R.resSet t M a)) := by
      have h1 := hpm_a.projM hR hMa
      have htg_a := (completeDevelopment_unique hR hMa ⟨hδd, hδc⟩
        (hR.dev_complete (R.contract t a) (R.resSet t M a) hMa)).1
      rwa [htg_a]
    have hpm_comb : PermGen R (R.tgt (R.contract t a) δ)
        (R.projM (R.contract t a) (R.projM t ρ {a}) (R.resSet t M a))
        (R.projM t ρ M) := by
      have h1 := permGen_projM_projM hR haSet hM hρ
      have hunion : {a} ∪ M = M := by
        rw [Finset.singleton_union, Finset.insert_eq_of_mem haM]
      rw [dev_singleton hR ha] at h1
      simpa [hunion, ← htg_δ] using h1
    exact (ih'.trans hpm_mid).trans hpm_comb

theorem permGen_proj_append_right (hR : R.Orthogonal) {t : R.Obj} {σ τ ρ : List R.Adr}
    (hσ : R.Valid t σ) (hτρ : R.Valid t (τ ++ ρ)) :
    PermGen R (R.tgt t (τ ++ ρ)) (R.proj t σ (τ ++ ρ))
      (R.proj (R.tgt t τ) (R.proj t σ τ) ρ) := by
  induction σ generalizing t τ ρ with
  | nil => exact PermGen.refl trivial
  | cons a σ ih =>
    obtain ⟨ha, hσ'⟩ := hσ
    obtain ⟨hτ, hρ⟩ := (R.valid_append _ _ _).1 hτρ
    have haM : ∀ c ∈ ({a} : Finset R.Adr), R.isStep t c := by simpa
    let M₀ := R.resSetDeriv t {a} τ
    have hM₀ : ∀ c ∈ M₀, R.isStep (R.tgt t τ) c := resSetDeriv_isStep hR haM hτ
    let δ₀ := R.dev (R.tgt t τ) M₀
    have hδ₀ : R.IsCompleteDevelopment (R.tgt t τ) M₀ δ₀ := hR.dev_complete _ M₀ hM₀
    let τ' := R.projM t τ {a}
    let ρ' := R.projM (R.tgt t τ) ρ M₀
    obtain ⟨hτ'_val, htg_τ', _⟩ := projM_valid_and_tgt_and_res hR hτ haM
    rw [dev_singleton hR ha] at hτ'_val htg_τ'
    have hτ'_val' : R.Valid (R.contract t a) τ' := hτ'_val
    have htg_τ'' : R.tgt (R.contract t a) τ' = R.tgt (R.tgt t τ) δ₀ := htg_τ'
    have hρ'_val : R.Valid (R.tgt (R.contract t a) τ') ρ' := by
      rw [htg_τ'']
      exact projM_valid hR hρ hM₀
    have hτ'ρ'_val : R.Valid (R.contract t a) (τ' ++ ρ') :=
      (R.valid_append _ _ _).2 ⟨hτ'_val', hρ'_val⟩
    have ih' := ih hσ' hτ'ρ'_val
    have haσ : R.Valid t (a :: σ) := ⟨ha, hσ'⟩
    have hσ_τ'_val : R.Valid (R.tgt t τ) (δ₀ ++ R.proj (R.contract t a) σ τ') := by
      simpa [proj] using proj_valid_aux hR haσ hτ
    simp only [proj]
    rw [projM_append, proj_append_left_iterProj hR hσ_τ'_val hρ]
    -- Head comparison
    have hM₁ : ∀ c ∈ R.resSetDeriv (R.tgt t τ) M₀ ρ, R.isStep (R.tgt (R.tgt t τ) ρ) c :=
      resSetDeriv_isStep hR hM₀ hρ
    have hc_head1 : R.IsCompleteDevelopment (R.tgt t (τ ++ ρ))
        (R.resSetDeriv t {a} (τ ++ ρ))
        (R.dev (R.tgt t (τ ++ ρ)) (R.resSetDeriv t {a} (τ ++ ρ))) := by
      rw [tgt_append, resSetDeriv_append]
      exact hR.dev_complete _ _ hM₁
    have hc_head2 : R.IsCompleteDevelopment (R.tgt t (τ ++ ρ))
        (R.resSetDeriv t {a} (τ ++ ρ))
        (R.proj (R.tgt t τ) δ₀ ρ) := by
      rw [tgt_append, resSetDeriv_append]
      exact proj_isCompleteDevelopment hR hM₀ hδ₀ hρ
    have hpm_head := permGen_of_completeDevelopment hR
      (by rwa [tgt_append, resSetDeriv_append]) hc_head1 hc_head2
    -- Tail comparison
    have hiter : PermGen R (R.tgt (R.tgt t τ) δ₀)
        (iterProj R (R.tgt t τ) ρ δ₀) ρ' :=
      permGen_iterProj_completeDevelopment hR hM₀ hδ₀ hρ
    have hσ_τ'_sub : R.Valid (R.tgt (R.tgt t τ) δ₀) (R.proj (R.contract t a) σ τ') :=
      ((R.valid_append _ _ _).1 hσ_τ'_val).2
    have htail_congr : R.proj (R.tgt (R.tgt t τ) δ₀) (R.proj (R.contract t a) σ τ')
          (iterProj R (R.tgt t τ) ρ δ₀) =
        R.proj (R.tgt (R.tgt t τ) δ₀) (R.proj (R.contract t a) σ τ') ρ' :=
      proj_congr_permGen hR hσ_τ'_sub hiter
    rw [htail_congr]
    refine PermGen.append hpm_head ?_
    have htg_head : R.tgt (R.tgt t (τ ++ ρ))
        (R.dev (R.tgt t (τ ++ ρ)) (R.resSetDeriv t {a} (τ ++ ρ))) =
        R.tgt (R.contract t a) (τ' ++ ρ') := by
      rw [R.tgt_append (R.contract t a) τ' ρ', htg_τ'', R.tgt_append t τ ρ,
        resSetDeriv_append t {a} τ ρ]
      exact ((projM_valid_and_tgt_and_res hR hρ hM₀).2.1).symm
    rw [htg_head]
    simpa [htg_τ''] using ih'

theorem proj_nil_right_aux (hR : R.Orthogonal) {t : R.Obj} {σ : List R.Adr}
    (hσ : R.Valid t σ) : R.proj t σ [] = σ := by
  induction σ generalizing t with
  | nil => rfl
  | cons a σ ih =>
    obtain ⟨ha, hσ'⟩ := hσ
    simp [proj, projM, dev_singleton hR ha, ih hσ']

theorem permGen_iterProj_eq_proj (hR : R.Orthogonal) {t : R.Obj} {ρ σ : List R.Adr}
    (hρ : R.Valid t ρ) (hσ : R.Valid t σ) :
    PermGen R (R.tgt t σ) (iterProj R t ρ σ) (R.proj t ρ σ) := by
  induction σ generalizing t ρ with
  | nil =>
    simp only [iterProj, tgt_nil, proj_nil_right_aux hR hρ]
    exact PermGen.refl hρ
  | cons a σ ih =>
    obtain ⟨ha, hσ'⟩ := hσ
    have hρ' := proj_valid_aux hR hρ (valid_singleton ha)
    have haσ : R.Valid t ([a] ++ σ) := ⟨ha, hσ'⟩
    have h1 := ih hρ' hσ'
    have h2 := (permGen_proj_append_right hR hρ haσ).symm
    exact h1.trans h2

theorem proj_append_left_aux (hR : R.Orthogonal) {t : R.Obj} {σ τ ρ : List R.Adr}
    (hστ : R.Valid t (σ ++ τ)) (hρ : R.Valid t ρ) :
    R.proj t (σ ++ τ) ρ = R.proj t σ ρ ++ R.proj (R.tgt t σ) τ (R.proj t ρ σ) := by
  obtain ⟨hσ, hτ⟩ := (R.valid_append _ _ _).1 hστ
  rw [proj_append_left_iterProj hR hστ hρ,
    proj_congr_permGen hR hτ (permGen_iterProj_eq_proj hR hρ hσ)]

theorem proj_self_aux (hR : R.Orthogonal) {t : R.Obj} {σ : List R.Adr}
    (hσ : R.Valid t σ) : R.proj t σ σ = [] := by
  induction σ generalizing t with
  | nil => rfl
  | cons a σ ih =>
    obtain ⟨ha, hσ'⟩ := hσ
    have h1 : R.proj t (a :: σ) (a :: σ) =
        R.proj t [a] (a :: σ) ++ R.proj (R.contract t a) σ (R.proj t (a :: σ) [a]) :=
      proj_cons_left hR ha hσ' ⟨ha, hσ'⟩
    have hhead : R.proj t [a] (a :: σ) = [] := by
      simp [proj, resSet_singleton, hR.autoerasure t a ha, dev_empty hR]
    have harg : R.proj t (a :: σ) [a] = σ := by
      rw [proj_cons_left hR ha hσ' (valid_singleton ha)]
      have haa : R.proj t [a] [a] = [] := by
        simp [proj, resSet_singleton, hR.autoerasure t a ha, dev_empty hR]
      rw [haa, List.nil_append]
      exact proj_nil_right_aux hR hσ'
    rw [h1, hhead, harg, List.nil_append, ih hσ']

theorem permGen_dev_projM_comm (hR : R.Orthogonal) {t : R.Obj} {M : Finset R.Adr}
    {τ : List R.Adr} (hM : ∀ a ∈ M, R.isStep t a) (hτ : R.Valid t τ) :
    PermGen R t (R.dev t M ++ R.projM t τ M)
      (τ ++ R.dev (R.tgt t τ) (R.resSetDeriv t M τ)) := by
  induction τ generalizing t M with
  | nil => simp [projM, PermGen.refl (dev_valid hR hM)]
  | cons b τ ih =>
    obtain ⟨hb, hτ'⟩ := hτ
    have hMb := resSet_isStep hR hM hb
    have hbM : ∀ c ∈ ({b} : Finset R.Adr), R.isStep t c := by simpa
    have hMb_all : ∀ a ∈ M ∪ {b}, R.isStep t a := by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · exact hM a ha
      · exact (Finset.mem_singleton.1 ha) ▸ hb
    have hB' : ∀ c ∈ R.resSetDeriv t {b} (R.dev t M), R.isStep (R.tgt t (R.dev t M)) c :=
      resSetDeriv_isStep hR hbM (dev_valid hR hM)
    have hc1 : R.IsCompleteDevelopment t (M ∪ {b})
        (R.dev t M ++ R.dev (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M))) :=
      completeDevelopment_union (hR.dev_complete t M hM) (hR.dev_complete _ _ hB')
    have hc2 : R.IsCompleteDevelopment t (M ∪ {b})
        (b :: R.dev (R.contract t b) (R.resSet t M b)) := by
      have h1 : R.IsCompleteDevelopment t {b} [b] := (isCompleteDevelopment_singleton hR hb).2 rfl
      exact (Finset.union_comm M {b}) ▸
        (by simpa using completeDevelopment_union h1 (hR.dev_complete _ _ hMb))
    have hsq := permGen_of_completeDevelopment hR hMb_all hc1 hc2
    simp only [projM, ← List.append_assoc]
    have hstep1 : PermGen R t
        ((R.dev t M ++ R.dev (R.tgt t (R.dev t M)) (R.resSetDeriv t {b} (R.dev t M))) ++
          R.projM (R.contract t b) τ (R.resSet t M b))
        ((b :: R.dev (R.contract t b) (R.resSet t M b)) ++
          R.projM (R.contract t b) τ (R.resSet t M b)) := by
      refine PermGen.append hsq ?_
      rw [hsq.tgt_eq hR]
      exact PermGen.refl (projM_valid hR hτ' hMb)
    have hstep2 : PermGen R t
        (b :: (R.dev (R.contract t b) (R.resSet t M b) ++
          R.projM (R.contract t b) τ (R.resSet t M b)))
        (b :: (τ ++ R.dev (R.tgt (R.contract t b) τ)
          (R.resSetDeriv (R.contract t b) (R.resSet t M b) τ))) :=
      permGen_cons hb (ih hMb hτ')
    simpa [List.cons_append] using hstep1.trans hstep2

theorem permGen_join_comm (hR : R.Orthogonal) {t : R.Obj} {σ τ : List R.Adr}
    (hσ : R.Valid t σ) (hτ : R.Valid t τ) :
    PermGen R t (R.join t σ τ) (R.join t τ σ) := by
  induction σ generalizing t τ with
  | nil =>
    simp only [join, List.nil_append, proj, List.append_nil, proj_nil_right_aux hR hτ]
    exact PermGen.refl hτ
  | cons a σ ih =>
    obtain ⟨ha, hσ'⟩ := hσ
    have haM : ∀ c ∈ ({a} : Finset R.Adr), R.isStep t c := by simpa
    have hτa_val : R.Valid (R.contract t a) (R.proj t τ [a]) :=
      proj_valid_aux hR hτ (valid_singleton ha)
    -- Step 1: `(a :: σ) ++ (τ / (a :: σ)) ~ a :: (σ ++ ((τ / [a]) / σ))`
    have hp1 : PermGen R t ((a :: σ) ++ R.proj t τ (a :: σ))
        (a :: (σ ++ R.proj (R.contract t a) (R.proj t τ [a]) σ)) := by
      have haσ : R.Valid t ([a] ++ σ) := ⟨ha, hσ'⟩
      have hr := permGen_proj_append_right hR hτ haσ
      simpa [List.cons_append] using
        permGen_cons ha (PermGen.append (PermGen.refl hσ') hr)
    -- Step 2: IH at `contract t a` on `σ` and `τ / [a]`
    have hp2 : PermGen R t (a :: (σ ++ R.proj (R.contract t a) (R.proj t τ [a]) σ))
        (a :: (R.proj t τ [a] ++ R.proj (R.contract t a) σ (R.proj t τ [a]))) :=
      permGen_cons ha (ih hσ' hτa_val)
    -- Step 3: single-step join commutativity `[a] ++ (τ / [a]) ~ τ ++ ([a] / τ)`
    have hp_single : PermGen R t ([a] ++ R.proj t τ [a]) (τ ++ R.proj t [a] τ) := by
      have hpm := permGen_projM_eq_proj hR hτ haM
      rw [dev_singleton hR ha] at hpm
      have hcomm := permGen_dev_projM_comm hR haM hτ
      rw [dev_singleton hR ha] at hcomm
      have h1 : PermGen R t ([a] ++ R.proj t τ [a]) ([a] ++ R.projM t τ {a}) :=
        PermGen.append (PermGen.refl (valid_singleton ha)) hpm.symm
      simpa [proj] using h1.trans hcomm
    have hp3 : PermGen R t
        (([a] ++ R.proj t τ [a]) ++ R.proj (R.contract t a) σ (R.proj t τ [a]))
        ((τ ++ R.proj t [a] τ) ++ R.proj (R.contract t a) σ (R.proj t τ [a])) := by
      refine PermGen.append hp_single ?_
      exact PermGen.refl (proj_valid_aux hR hσ' hτa_val)
    have hfinal := (hp1.trans hp2).trans (by simpa [List.cons_append] using hp3)
    simpa [join, List.append_assoc, ← proj_cons_left hR ha hσ' hτ] using hfinal

theorem permGen_iff_permEq (hR : R.Orthogonal) {t : R.Obj} {σ τ : List R.Adr}
    (hσ : R.Valid t σ) (hτ : R.Valid t τ) :
    PermGen R t σ τ ↔ R.PermEq t σ τ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Prefix, proj_congr_permGen hR hσ h.symm, proj_self_aux hR hσ]
    · rw [Prefix, proj_congr_permGen hR hτ h, proj_self_aux hR hτ]
  · rintro ⟨h1, h2⟩
    unfold Prefix at h1 h2
    have h := permGen_join_comm hR hσ hτ
    simpa [join, h1, h2] using h

theorem PermGen.eq_nil_of_right_nil (hR : R.Orthogonal) {t : R.Obj} {σ : List R.Adr}
    (h : PermGen R t σ []) : σ = [] := by
  have hσ := h.valid_left hR
  rw [← proj_nil_right_aux hR hσ, proj_congr_permGen hR hσ h.symm, proj_self_aux hR hσ]

end ResidualSystem

namespace LTerm

theorem betaStep_iff_beta {t u : LTerm} : BetaStep t u ↔ Beta t u := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    induction p generalizing t with
    | nil =>
      cases t with
      | var => simp [isRedexAt, subAt, isRedex] at hp
      | lam => simp [isRedexAt, subAt, isRedex] at hp
      | app t s =>
        cases t with
        | var => simp [isRedexAt, subAt, isRedex] at hp
        | app => simp [isRedexAt, subAt, isRedex] at hp
        | lam b => exact .beta b s
    | cons i p ih =>
      cases t with
      | var => simp [isRedexAt, subAt] at hp
      | lam t =>
        cases i with
        | zero =>
          have ht : isRedexAt t p = true := by simpa only [Nat.zero_add, isRedexAt, subAt] using hp
          simpa only [Nat.zero_add, contractAt] using Beta.lam (ih ht)
        | succ i => simp [isRedexAt, subAt] at hp
      | app t s =>
        cases i with
        | zero =>
          have ht : isRedexAt t p = true := by simpa only [Nat.zero_add, isRedexAt, subAt] using hp
          simpa only [Nat.zero_add, contractAt] using Beta.appL s (ih ht)
        | succ i =>
          cases i with
          | zero =>
            have hs : isRedexAt s p = true := by simpa only [Nat.zero_add, isRedexAt, subAt] using hp
            simpa only [Nat.zero_add, contractAt] using Beta.appR t (ih hs)
          | succ i => simp [isRedexAt, subAt] at hp
  · intro h
    induction h with
    | beta t s => exact ⟨[], rfl, rfl⟩
    | lam h ih =>
      obtain ⟨p, hp, he⟩ := ih
      exact ⟨0 :: p, by simpa only [Nat.zero_add, isRedexAt, subAt] using hp, by simp [contractAt, he]⟩
    | appL s h ih =>
      obtain ⟨p, hp, he⟩ := ih
      exact ⟨0 :: p, by simpa only [Nat.zero_add, isRedexAt, subAt] using hp, by simp [contractAt, he]⟩
    | appR t h ih =>
      obtain ⟨p, hp, he⟩ := ih
      exact ⟨1 :: p, by simpa only [Nat.zero_add, isRedexAt, subAt] using hp, by simp [contractAt, he]⟩

/-! ### Laneve’s counterexample (`document/01-introduction.tex`)

`S` is the root step, `R` erases its argument from inside the body, and `U`
contracts the self-reproducing Ω. Common lower bounds of `R` and `ST` are
exactly the finite repetitions of `U`.
-/

def laneveOmega : LTerm := app (lam (app (var 0) (var 0))) (lam (app (var 0) (var 0)))
def laneveTerm : LTerm :=
  app (lam (app (lam (var 10)) (app (var 0) laneveOmega))) (lam (var 11))
def laneveU : Pos := [0, 0, 1, 1]
def laneveST : List Pos := [[], [1]]
def laneveR : List Pos := [[0, 0]]

theorem mem_redexes {t : LTerm} {p : Pos} : p ∈ redexes t ↔ isRedexAt t p = true := by
  induction t generalizing p with
  | var n => cases p <;> simp [redexes, isRedexAt, subAt, isRedex]
  | lam t ih =>
    rcases p with _ | ⟨i, p⟩
    · simp [redexes, isRedexAt, subAt, isRedex]
    · cases i <;> simp [redexes, isRedexAt, subAt, ih]
  | app t s iht ihs =>
    rcases p with _ | ⟨i, p⟩
    · simp [redexes, isRedexAt, subAt]
    · rcases i with _ | _ | i <;> simp [redexes, isRedexAt, subAt, iht, ihs]

theorem laneve_steps {p : Pos} (hp : isRedexAt laneveTerm p = true) :
    p = [] ∨ p = [0, 0] ∨ p = laneveU := by
  rw [← mem_redexes] at hp
  have he : redexes laneveTerm = [[], [0, 0], laneveU] := by decide
  simpa [he] using hp

private theorem laneve_contract_U : contractAt laneveTerm laneveU = laneveTerm := by decide

private theorem laneve_lower_cons (p : Pos) (σ : List Pos)
    (hR : lambdaRS.Prefix laneveTerm (p :: σ) laneveR)
    (hST : lambdaRS.Prefix laneveTerm (p :: σ) laneveST)
    (hp : isRedexAt laneveTerm p = true) :
    p = laneveU ∧ lambdaRS.Prefix laneveTerm σ laneveR ∧
      lambdaRS.Prefix laneveTerm σ laneveST := by
  rcases laneve_steps hp with rfl | rfl | rfl
  -- The residual of S after R, or of R after ST, is still a redex.
  · change [] :: _ = [] at hR
    contradiction
  · change [] :: _ = [] at hST
    contradiction
  · exact ⟨rfl, hR, hST⟩

theorem laneve_lower_shape (σ : List Pos) (hv : lambdaRS.Valid laneveTerm σ)
    (hR : lambdaRS.Prefix laneveTerm σ laneveR)
    (hST : lambdaRS.Prefix laneveTerm σ laneveST) :
    ∃ n, σ = List.replicate n laneveU := by
  induction σ with
  | nil => exact ⟨0, rfl⟩
  | cons p σ ih =>
    obtain ⟨rfl, hR, hST⟩ := laneve_lower_cons p σ hR hST hv.1
    have hv' : lambdaRS.Valid laneveTerm σ := by
      simpa only [laneve_contract_U] using hv.2
    obtain ⟨n, rfl⟩ := ih hv' hR hST
    exact ⟨n + 1, rfl⟩

theorem laneve_repeat_valid (n : ℕ) :
    lambdaRS.Valid laneveTerm (List.replicate n laneveU) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    constructor
    · decide
    · simpa only [laneve_contract_U] using ih

theorem laneve_repeat_lower (n : ℕ) :
    lambdaRS.Prefix laneveTerm (List.replicate n laneveU) laneveR ∧
      lambdaRS.Prefix laneveTerm (List.replicate n laneveU) laneveST := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    exact ih

private theorem laneve_repeat_tgt (n : ℕ) :
    lambdaRS.tgt laneveTerm (List.replicate n laneveU) = laneveTerm := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change lambdaRS.tgt (contractAt laneveTerm laneveU) (List.replicate n laneveU) = laneveTerm
    rw [laneve_contract_U]
    exact ih

theorem laneve_repeat_not_le (hOrth : lambdaRS.Orthogonal) (n : ℕ) :
    ¬ lambdaRS.Prefix laneveTerm (List.replicate (n + 1) laneveU)
      (List.replicate n laneveU) := by
  intro h
  have hv := laneve_repeat_valid n
  have he := ResidualSystem.proj_append_left_aux hOrth
    (σ := List.replicate n laneveU) (τ := [laneveU]) (ρ := List.replicate n laneveU)
    (t := laneveTerm) (by simpa only [← List.replicate_succ'] using laneve_repeat_valid (n + 1)) hv
  rw [ResidualSystem.proj_self_aux hOrth hv, laneve_repeat_tgt, List.nil_append] at he
  have hu : lambdaRS.Valid laneveTerm [laneveU] := laneve_repeat_valid 1
  rw [ResidualSystem.proj_nil_right_aux hOrth hu] at he
  change lambdaRS.proj _ _ _ = [] at h
  rw [List.replicate_succ', he] at h
  contradiction

end LTerm

end Thesis
