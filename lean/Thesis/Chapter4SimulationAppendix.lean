/-
# Chapter 4: Simulation of the λ-calculus — Appendix

Controlled subject expansion, free cuts, strong sequentiality, backwards simulation, and strong
head-normal-form refinements (`08-14-hnf-has-refinement.tex` and `08-15-has-hnf-has-refinement.tex`).
-/
import Thesis.Chapter4SimulationDefs
import Thesis.Chapter3ResidualTheoryAppendix

namespace Thesis

open LTerm DTerm

/-! ### Free cuts and strong sequentiality

A free cut chooses an antichain of subterm occurrences. Its entries record the typing
context and type of each chosen occurrence, expressed at the root of the containing term.
Crossing a binder requires the chosen subterm not to use its variable. Using a multiset
retains separate occurrences even when their terms or types are equal.
-/

abbrev CutEntry := Ctx × Ty

namespace CutEntry

def mapCtx (f : Ctx → Ctx) (p : CutEntry) : CutEntry := (f p.1, p.2)

def label (p : CutEntry) : Label := p.2.label

@[simp] theorem label_mapCtx (f : Ctx → Ctx) (p : CutEntry) :
    (mapCtx f p).label = p.label := rfl

@[simp] theorem labels_mapCtx (xs : Multiset CutEntry) (f : Ctx → Ctx) :
    (xs.map (mapCtx f)).map label = xs.map label := by
  rw [Multiset.map_map]
  rfl

end CutEntry

mutual
/-- A selection of pairwise disjoint, free subterm occurrences and their typings. -/
inductive FreeCut : DTerm → Multiset CutEntry → Prop
  | empty (t : DTerm) : FreeCut t 0
  | root {Γ : Ctx} {t : DTerm} {τ : Ty} : HasType Γ t τ → FreeCut t {(Γ, τ)}
  | lam {t : DTerm} {xs : Multiset CutEntry} (ℓ : Label) :
      FreeCut t xs → (∀ p ∈ xs, p.1 0 = 0) →
      FreeCut (.lam ℓ t) (xs.map (CutEntry.mapCtx (Ctx.remove 0)))
  | app {t : DTerm} {ss : List DTerm} {xs ys : Multiset CutEntry} :
      FreeCut t xs → FreeCutMulti ss ys → FreeCut (.app t ss) (xs + ys)
/-- Independent free cuts in a list of sibling terms. -/
inductive FreeCutMulti : List DTerm → Multiset CutEntry → Prop
  | nil : FreeCutMulti [] 0
  | cons {t : DTerm} {ts : List DTerm} {xs ys : Multiset CutEntry} :
      FreeCut t xs → FreeCutMulti ts ys → FreeCutMulti (t :: ts) (xs + ys)
end

/-- The thesis' strong sequentiality condition, expressed by free antichains. Every
pair of disjoint free subterms extends to such a cut (choose those two occurrences).
The condition is required in every subterm, as in the thesis, and includes correctness. -/
structure StronglySequential (t : DTerm) : Prop where
  correct : Correct t
  separate : ∀ s, DTerm.Sub s t → ∀ xs, FreeCut s xs → (xs.map CutEntry.label).Nodup

theorem StronglySequential.sub {s t : DTerm} (ht : StronglySequential t)
    (hs : DTerm.Sub s t) : StronglySequential s where
  correct := ht.correct.sub hs
  separate u hu xs hx := ht.separate u (hu.trans hs) xs hx

theorem FreeCutMulti.empty (ts : List DTerm) : FreeCutMulti ts 0 := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => simpa using FreeCutMulti.cons (.empty t) ih

theorem FreeCutMulti.append {ts ss : List DTerm} {xs ys : Multiset CutEntry}
    (ht : FreeCutMulti ts xs) (hs : FreeCutMulti ss ys) :
    FreeCutMulti (ts ++ ss) (xs + ys) := by
  induction ts generalizing xs with
  | nil => cases ht; simpa using hs
  | cons t ts ih =>
    cases ht with
    | cons ht hts => simpa [add_assoc] using FreeCutMulti.cons ht (ih hts)

theorem FreeCutMulti.perm {ts ss : List DTerm} {xs : Multiset CutEntry}
    (ht : FreeCutMulti ts xs) (hp : ts.Perm ss) : FreeCutMulti ss xs := by
  induction hp generalizing xs with
  | nil => exact ht
  | cons t hp ih => cases ht with | cons ht hts => exact .cons ht (ih hts)
  | swap t s ss =>
    cases ht with
    | cons ht hs =>
      cases hs with
      | cons hs hss => simpa [add_left_comm] using FreeCutMulti.cons hs (.cons ht hss)
  | trans _ _ ih ih' => exact ih' (ih ht)

namespace Ctx

@[simp] theorem remove_zero_apply (Γ : Ctx) (n : ℕ) : Γ.remove 0 n = Γ (n + 1) := by
  simp [remove]

@[simp] theorem remove_zero_cons (M : Multiset Ty) (Γ : Ctx) :
    (cons M Γ).remove 0 = Γ := by funext n; simp [remove, cons]

theorem eta_cons (Γ : Ctx) : cons (Γ 0) (Γ.remove 0) = Γ := by
  rw [← insert_zero, insert_remove]

@[simp] theorem remove_zero_shift_succ (d c : ℕ) (Γ : Ctx) :
    (Γ.shift d (c + 1)).remove 0 = (Γ.remove 0).shift d c := by
  conv_lhs => rw [← eta_cons Γ, shift_cons, remove_zero_cons]

@[simp] theorem remove_zero_remove_succ (k : ℕ) (Γ : Ctx) :
    (Γ.remove (k + 1)).remove 0 = (Γ.remove 0).remove k := by
  conv_lhs => rw [← eta_cons Γ, remove_cons, remove_zero_cons]

@[simp] theorem shift_succ_at_zero (d c : ℕ) (Γ : Ctx) :
    Γ.shift d (c + 1) 0 = Γ 0 := by simp [shift]

@[simp] theorem remove_succ_at_zero (k : ℕ) (Γ : Ctx) :
    Γ.remove (k + 1) 0 = Γ 0 := by simp [remove]

@[simp] theorem shift_inserted_zero (k : ℕ) (Γ : Ctx) (n : ℕ) (hn : n < k) :
    Γ.shift k 0 n = 0 := by simp [shift, hn]

end Ctx

namespace FreeCutMulti

theorem split {ts ss : List DTerm} {xs : Multiset CutEntry}
    (h : FreeCutMulti (ts ++ ss) xs) :
    ∃ ys zs, xs = ys + zs ∧ FreeCutMulti ts ys ∧ FreeCutMulti ss zs := by
  induction ts generalizing xs with
  | nil => exact ⟨0, xs, by simp, .nil, h⟩
  | cons t ts ih =>
    cases h with
    | cons ht hs =>
      obtain ⟨ys, zs, rfl, hys, hzs⟩ := ih hs
      exact ⟨_, zs, by ac_rfl, .cons ht hys, hzs⟩

end FreeCutMulti

theorem FreeCut.shift {t : DTerm} {xs : Multiset CutEntry} (h : FreeCut t xs)
    (d c : ℕ) : FreeCut (t.shift d c) (xs.map (CutEntry.mapCtx (Ctx.shift d c))) := by
  induction h using FreeCut.rec
    (motive_2 := fun ts xs _ => ∀ c,
      FreeCutMulti (ts.map (DTerm.shift d c)) (xs.map (CutEntry.mapCtx (Ctx.shift d c))))
    generalizing c with
  | empty => simpa using FreeCut.empty _
  | root ht => simpa [CutEntry.mapCtx] using FreeCut.root (ht.shift d c)
  | @lam t xs ℓ h hz ih =>
    have hz' : ∀ p ∈ xs.map (CutEntry.mapCtx (Ctx.shift d (c + 1))), p.1 0 = 0 := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
      simpa [CutEntry.mapCtx] using hz q hq
    simpa only [DTerm.shift, Multiset.map_map, Function.comp_def, CutEntry.mapCtx,
      Ctx.remove_zero_shift_succ] using FreeCut.lam ℓ (ih (c + 1)) hz'
  | app h hs ih ihs =>
    simpa only [DTerm.shift, Multiset.map_add] using FreeCut.app (ih c) (ihs c)
  | nil => simpa using FreeCutMulti.nil
  | cons h hs ih ihs =>
    rename_i c
    simpa only [List.map_cons, Multiset.map_add] using FreeCutMulti.cons (ih c) (ihs c)

/-- The context and type information that a cut must preserve when a substitution removes
variable `k`: types agree, as do contexts below `k` (the surrounding bound variables). -/
def CutRelated (k : ℕ) (p q : CutEntry) : Prop :=
  p.2 = q.2 ∧ ∀ n, n < k → p.1 n = q.1 n

theorem CutRelated.labels {k : ℕ} {xs ys : Multiset CutEntry}
    (h : Multiset.Rel (CutRelated k) xs ys) : xs.map CutEntry.label = ys.map CutEntry.label := by
  induction h with
  | zero => rfl
  | cons hp h ih => simp [CutEntry.label, hp.1, ih]

/-- Typing inversion also preserves the surrounding binder contexts. -/
theorem PSubst.typing_prefix {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ Δ : Ctx} {τ ρ : Ty}
    (ht : HasType Γ t τ) (hu : HasType Δ u ρ) :
    τ = ρ ∧ ∀ n, n < k → Γ n = Δ n := by
  obtain ⟨Θ, Ξs, σs, hb, _, _, he⟩ := h.inverse hu
  obtain ⟨rfl, rfl⟩ := hasType_unique ht hb
  refine ⟨rfl, ?_⟩
  intro n hn
  rw [he]
  simp [Ctx.remove, Ctx.shift, hn, -Ctx.shift_sum]

private theorem cut_root_lift {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ Δ : Ctx} {τ ρ : Ty}
    (ht : HasType Γ t τ) (hu : HasType Δ u ρ) :
    ∃ ys, FreeCut u ys ∧ Multiset.Rel (CutRelated k) {(Γ, τ)} ys :=
  ⟨{(Δ, ρ)}, .root hu, .cons (h.typing_prefix ht hu) .zero⟩

/-- Every free antichain of the body survives partition substitution, with the same
selected types and unchanged context below the removed binder. In particular, substitution
cannot hide a collision of external labels in the body. -/
theorem PSubst.lift_cut {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {ρ : Ty} (hu : HasType Γ u ρ)
    {xs : Multiset CutEntry} (hx : FreeCut t xs) :
    ∃ ys, FreeCut u ys ∧ Multiset.Rel (CutRelated k) xs ys := by
  induction h using PSubst.rec
    (motive_2 := fun ts k _ us _ => ∀ {Γs ρs}, HasTypeMulti Γs us ρs →
      ∀ {xs}, FreeCutMulti ts xs →
      ∃ ys, FreeCutMulti us ys ∧ Multiset.Rel (CutRelated k) xs ys)
    generalizing Γ ρ xs with
  | var_eq k hs =>
    cases hx with
    | empty => exact ⟨0, .empty _, .zero⟩
    | root ht => exact cut_root_lift (.var_eq k hs) ht hu
  | var_lt τ hn =>
    cases hx with
    | empty => exact ⟨0, .empty _, .zero⟩
    | root ht => exact cut_root_lift (.var_lt τ hn) ht hu
  | var_gt τ hn =>
    cases hx with
    | empty => exact ⟨0, .empty _, .zero⟩
    | root ht => exact cut_root_lift (.var_gt τ hn) ht hu
  | @lam t u k ss ℓ h ih =>
    cases hx with
    | empty => exact ⟨0, .empty _, .zero⟩
    | root ht => exact cut_root_lift (.lam ℓ h) ht hu
    | lam _ hx hz =>
      cases hu with
      | lam _ hu =>
        obtain ⟨ys, hy, hr⟩ := ih hu hx
        have hz' : ∀ q ∈ ys, q.1 0 = 0 := by
          intro q hq
          obtain ⟨p, hp, hrpq⟩ := Multiset.exists_mem_of_rel_of_mem
            (Multiset.rel_flip.mpr hr) hq
          exact (hrpq.2 0 (by omega)).symm.trans (hz p hp)
        refine ⟨_, .lam ℓ hy hz', Multiset.rel_map.mpr ?_⟩
        apply hr.mono
        intro p hp q hq hrpq
        refine ⟨hrpq.1, ?_⟩
        intro n hn
        simpa [CutEntry.mapCtx] using hrpq.2 (n + 1) (by omega)
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    cases hx with
    | empty => exact ⟨0, .empty _, .zero⟩
    | root ht => exact cut_root_lift (.app h hs hp) ht hu
    | app hx hxs =>
      cases hu with
      | app hu hus _ =>
        obtain ⟨ys, hy, hr⟩ := ih hu hx
        obtain ⟨zs, hz, hr'⟩ := ihs hus hxs
        exact ⟨_, .app hy hz, hr.add hr'⟩
  | nil =>
    rename_i Γs ρs hu xs hx
    cases hx
    exact ⟨0, .nil, .zero⟩
  | cons _ _ ih ihs =>
    rename_i Γs ρs hu xs hx
    cases hu with
    | cons hu hus =>
      cases hx with
      | cons hx hxs =>
        obtain ⟨ys, hy, hr⟩ := ih hu hx
        obtain ⟨zs, hz, hr'⟩ := ihs hus hxs
        exact ⟨_, .cons hy hz, hr.add hr'⟩

/-- The separation part of strong sequentiality, required at all subterms. -/
def Separated (t : DTerm) : Prop :=
  ∀ s, DTerm.Sub s t → ∀ xs, FreeCut s xs → (xs.map CutEntry.label).Nodup

theorem Separated.sub {s t : DTerm} (ht : Separated t) (hs : DTerm.Sub s t) : Separated s :=
  fun u hu xs hx => ht u (hu.trans hs) xs hx

theorem separated_var (n : ℕ) (τ : Ty) : Separated (.var n τ) := by
  intro s hs xs hx
  cases hs
  cases hx <;> simp

theorem DTerm.Sub.shift {s t : DTerm} (hs : Sub s t) (d c : ℕ) :
    ∃ c', Sub (s.shift d c') (t.shift d c) := by
  induction hs generalizing c with
  | refl => exact ⟨c, .refl _⟩
  | lam ℓ h ih =>
    obtain ⟨c', h⟩ := ih (c + 1)
    exact ⟨c', by simpa only [DTerm.shift] using DTerm.Sub.lam ℓ h⟩
  | fn ss h ih =>
    obtain ⟨c', h⟩ := ih c
    exact ⟨c', by simpa only [DTerm.shift] using DTerm.Sub.fn (ss.map (DTerm.shift d c)) h⟩
  | arg t hm h ih =>
    obtain ⟨c', h⟩ := ih c
    exact ⟨c', by simpa only [DTerm.shift] using
      DTerm.Sub.arg (t.shift d c) (List.mem_map.mpr ⟨_, hm, rfl⟩) h⟩

theorem Separated.of_shift {t : DTerm} {d c : ℕ} (h : Separated (t.shift d c)) :
    Separated t := by
  intro s hs xs hx
  obtain ⟨c', hs'⟩ := hs.shift d c
  have hn := h _ hs' _ (hx.shift d c')
  change (xs.map (fun p => p.2.label)).Nodup
  simpa [Multiset.map_map, Function.comp_def, CutEntry.label, CutEntry.mapCtx] using hn

private theorem separate_body_root {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {ρ : Ty} (hu : HasType Γ u ρ)
    (hsep : Separated u) {xs : Multiset CutEntry} (hx : FreeCut t xs) :
    (xs.map CutEntry.label).Nodup := by
  obtain ⟨ys, hy, hr⟩ := h.lift_cut hu hx
  rw [CutRelated.labels hr]
  exact hsep u (.refl u) ys hy

/-- Separation of the contractum implies separation of the raw body and of every consumed
argument. This is the non-circular part of reconstructing correctness. -/
theorem PSubst.separated {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {ρ : Ty} (hu : HasType Γ u ρ)
    (hsep : Separated u) : Separated t ∧ ∀ s ∈ ss, Separated s := by
  induction h using PSubst.rec
    (motive_2 := fun ts _ ss us _ => ∀ {Γs ρs}, HasTypeMulti Γs us ρs →
      (∀ u ∈ us, Separated u) → (∀ t ∈ ts, Separated t) ∧ ∀ s ∈ ss, Separated s)
    generalizing Γ ρ with
  | var_eq k hs =>
    refine ⟨separated_var _ _, ?_⟩
    intro s hm
    have := List.mem_singleton.mp hm
    subst s
    exact hsep.of_shift
  | var_lt τ hn => exact ⟨separated_var _ _, by simp⟩
  | var_gt τ hn => exact ⟨separated_var _ _, by simp⟩
  | @lam t u k ss ℓ h ih =>
    cases hu with
    | lam _ hu =>
      obtain ⟨ht, hs⟩ := ih hu (hsep.sub (.lam ℓ (.refl u)))
      refine ⟨?_, hs⟩
      intro v hv xs hx
      cases hv with
      | refl => exact separate_body_root (.lam ℓ h) (.lam ℓ hu) hsep hx
      | lam _ hv => exact ht v hv xs hx
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    cases hu with
    | app hu hus hperm =>
      obtain ⟨ht, hss₀⟩ := ih hu (hsep.sub (.fn us (.refl u)))
      obtain ⟨hts, hss₁⟩ := ihs hus (fun v hv => hsep.sub (.arg u hv (.refl v)))
      refine ⟨?_, ?_⟩
      · intro v hv xs hx
        cases hv with
        | refl => exact separate_body_root (.app h hs hp) (.app hu hus hperm) hsep hx
        | fn _ hv => exact ht v hv xs hx
        | arg _ hm hv => exact hts _ hm v hv xs hx
      · intro s hm
        rcases List.mem_append.mp (hp.symm.subset hm) with hm | hm
        · exact hss₀ s hm
        · exact hss₁ s hm
  | nil =>
    rename_i Γs ρs hu hsep
    exact ⟨by simp, by simp⟩
  | cons _ _ ih ihs =>
    rename_i Γs ρs hu hsep
    cases hu with
    | cons hu hus =>
      obtain ⟨ht, hss₀⟩ := ih hu (hsep _ (by simp))
      obtain ⟨hts, hss₁⟩ := ihs hus (fun u hu => hsep u (by simp [hu]))
      constructor
      · intro t ht'
        rcases List.mem_cons.mp ht' with rfl | ht'
        · exact ht
        · exact hts t ht'
      · intro s hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hss₀ s hm
        · exact hss₁ s hm

/-- Every variable annotation has sequential arrow domains. This is the part of type
correctness inherited from old syntax; separation supplies the newly formed domains. -/
def AnnotationsSequential (t : DTerm) : Prop :=
  ∀ n τ, DTerm.Sub (.var n τ) t → τ.Sequential

namespace AnnotationsSequential

theorem sub {s t : DTerm} (ht : AnnotationsSequential t) (hs : DTerm.Sub s t) :
    AnnotationsSequential s := fun n τ h => ht n τ (h.trans hs)

theorem var (n : ℕ) {τ : Ty} (hτ : τ.Sequential) : AnnotationsSequential (.var n τ) := by
  intro m σ h
  cases h
  exact hτ

theorem lam {t : DTerm} (ℓ : Label) (ht : AnnotationsSequential t) :
    AnnotationsSequential (.lam ℓ t) := by
  intro n τ h
  cases h with
  | lam _ h => exact ht n τ h

theorem app {t : DTerm} {ss : List DTerm} (ht : AnnotationsSequential t)
    (hs : ∀ s ∈ ss, AnnotationsSequential s) : AnnotationsSequential (.app t ss) := by
  intro n τ h
  cases h with
  | fn _ h => exact ht n τ h
  | arg _ hm h => exact hs _ hm n τ h

theorem of_shift {t : DTerm} {d c : ℕ} (ht : AnnotationsSequential (t.shift d c)) :
    AnnotationsSequential t := by
  intro n τ hs
  obtain ⟨c', hs⟩ := hs.shift d c
  simp only [DTerm.shift] at hs
  split at hs <;> exact ht _ τ hs

end AnnotationsSequential

theorem Correct.annotations {t : DTerm} (ht : Correct t) : AnnotationsSequential t := by
  intro n τ hs
  exact (ht.sub hs).type_sequential (.var n τ)

private def occurrenceEntry (k : ℕ) (τ : Ty) : CutEntry := (Ctx.single k {τ}, τ)

@[simp] theorem Ctx.remove_zero_single_succ (k : ℕ) (M : Multiset Ty) :
    (Ctx.single (k + 1) M).remove 0 = Ctx.single k M := by
  funext n
  simp [Ctx.remove, Ctx.single]

/-- All free occurrences of any one variable form a free cut. Thus separation enforces
sequentiality of contexts, rather than taking that property as an extra assumption. -/
theorem FreeCut.occurrences (t : DTerm) (k : ℕ) :
    FreeCut t ((t.occTypes k : Multiset Ty).map (occurrenceEntry k)) := by
  induction t using DTerm.rec
    (motive_2 := fun ts => ∀ k, FreeCutMulti ts
      ((ts.flatMap (DTerm.occTypes · k) : Multiset Ty).map (occurrenceEntry k)))
    generalizing k with
  | var n τ =>
    by_cases hn : n = k
    · subst n
      simpa [DTerm.occTypes, occurrenceEntry] using FreeCut.root (HasType.var k τ)
    · simpa [DTerm.occTypes, hn] using FreeCut.empty (.var n τ)
  | lam ℓ t ih =>
    have hz : ∀ p ∈ (t.occTypes (k + 1) : Multiset Ty).map (occurrenceEntry (k + 1)),
        p.1 0 = 0 := by
      intro p hp
      obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.mp hp
      simp [occurrenceEntry, Ctx.single]
    simp only [DTerm.occTypes]
    change FreeCut (.lam ℓ t)
      ((t.occTypes (k + 1) : Multiset Ty).map (fun τ => (Ctx.single k {τ}, τ)))
    simpa only [Multiset.map_map, Function.comp_def, CutEntry.mapCtx,
      occurrenceEntry, Ctx.remove_zero_single_succ] using FreeCut.lam ℓ (ih (k + 1)) hz
  | app t ts ih ihs =>
    simpa only [DTerm.occTypes, ← Multiset.coe_add, Multiset.map_add] using
      FreeCut.app (ih k) (ihs k)
  | nil => simpa using FreeCutMulti.nil
  | cons t ts ih ihs =>
    rename_i k
    simpa only [List.flatMap_cons, ← Multiset.coe_add, Multiset.map_add] using
      FreeCutMulti.cons (ih k) (ihs k)

theorem Separated.occTypes {t : DTerm} (ht : Separated t) (k : ℕ) :
    SeqMS (t.occTypes k : Multiset Ty) := by
  have hn := ht t (.refl t) _ (FreeCut.occurrences t k)
  simpa [Multiset.map_map, Function.comp_def, occurrenceEntry, CutEntry.label, SeqMS] using hn

theorem Separated.context_seq {t : DTerm} (ht : Separated t) {Γ : Ctx} {τ : Ty}
    (h : HasType Γ t τ) : Γ.Seq := by
  intro n
  rw [linearity h n]
  exact ht.occTypes n

private theorem occurrence_sub {t : DTerm} {k : ℕ} {τ : Ty}
    (h : τ ∈ t.occTypes k) : ∃ n, DTerm.Sub (.var n τ) t := by
  induction t using DTerm.ind generalizing k with
  | var n σ =>
    simp only [DTerm.occTypes] at h
    split at h
    · have he : τ = σ := List.mem_singleton.mp h
      subst τ
      exact ⟨n, .refl _⟩
    · simp at h
  | lam ℓ t ih =>
    simp only [DTerm.occTypes] at h
    obtain ⟨n, hn⟩ := ih h
    exact ⟨n, .lam ℓ hn⟩
  | app t ss ih ihs =>
    simp only [DTerm.occTypes] at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨n, hn⟩ := ih h
      exact ⟨n, .fn ss hn⟩
    · obtain ⟨s, hs, h⟩ := List.mem_flatMap.mp h
      obtain ⟨n, hn⟩ := ihs s hs h
      exact ⟨n, .arg t hs hn⟩

theorem AnnotationsSequential.context_types {t : DTerm} (ha : AnnotationsSequential t)
    {Γ : Ctx} {τ : Ty} (h : HasType Γ t τ) : Γ.TypesSequential := by
  intro n σ hm
  rw [linearity h n] at hm
  obtain ⟨m, hs⟩ := occurrence_sub hm
  exact ha m σ hs

theorem HasType.type_sequential_of_separated {Γ : Ctx} {t : DTerm} {τ : Ty}
    (h : HasType Γ t τ) (ha : AnnotationsSequential t) (hs : Separated t) : τ.Sequential := by
  revert ha hs
  induction h using HasType.rec (motive_2 := fun _ _ _ _ => True) with
  | var n τ => intro ha _; exact ha n τ (.refl _)
  | @lam Γ M σ t ℓ hb ih =>
    intro ha hs
    have ha' := ha.sub (.lam ℓ (.refl t))
    have hs' := hs.sub (.lam ℓ (.refl t))
    apply Ty.Sequential.arrow
    · have hm := hs'.context_seq hb 0
      simpa [Ctx.cons] using hm
    · intro τ hm
      have hctx := ha'.context_types hb 0 τ
      apply hctx
      simpa [Ctx.cons] using hm
    · exact ih ha' hs'
  | @app Γ t L ℓ τ Δs ss σs ht hss hp ih _ =>
    intro ha hs
    exact (ih (ha.sub (.fn ss (.refl t))) (hs.sub (.fn ss (.refl t)))).cod
  | nil => trivial
  | cons => trivial

/-- Recover the original correctness invariant from separation, inherited annotations,
and unique lambda labels. No condition of correctness has been dropped or weakened. -/
theorem correct_of_separated {t : DTerm} (ht : t.Typable) (ha : AnnotationsSequential t)
    (hs : Separated t) (hl : t.lamLabels.Nodup) : Correct t := by
  refine ⟨ht, hl, ?_, ?_⟩
  · intro s Γ τ hsub h
    exact (hs.sub hsub).context_seq h
  · intro s Γ τ hsub h M ℓ ρ ho
    have ha' := ha.sub hsub
    rcases ho with ⟨n, σ, hm, ho⟩ | ho
    · exact ha'.context_types h n σ hm M ℓ ρ ho
    · exact h.type_sequential_of_separated ha' (hs.sub hsub) M ℓ ρ ho

/-- Sequentiality of variable annotations is inherited by the reconstructed body and
arguments from the correct contractum. Newly computed arrow domains are handled separately. -/
theorem PSubst.annotations {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) (hc : Correct u) :
    AnnotationsSequential t ∧ ∀ s ∈ ss, AnnotationsSequential s := by
  induction h using PSubst.rec
    (motive_2 := fun ts _ ss us _ => (∀ u ∈ us, Correct u) →
      (∀ t ∈ ts, AnnotationsSequential t) ∧ ∀ s ∈ ss, AnnotationsSequential s) with
  | var_eq k hs =>
    refine ⟨.var _ (hc.type_sequential (hs.shift k 0)), ?_⟩
    intro s hm
    have := List.mem_singleton.mp hm
    subst s
    exact hc.annotations.of_shift
  | var_lt τ hn => exact ⟨.var _ (hc.type_sequential (.var _ τ)), by simp⟩
  | var_gt τ hn => exact ⟨.var _ (hc.type_sequential (.var _ τ)), by simp⟩
  | @lam t u k ss ℓ h ih =>
    obtain ⟨ht, hs⟩ := ih (hc.sub (.lam ℓ (.refl u)))
    exact ⟨.lam ℓ ht, hs⟩
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    obtain ⟨ht, hss₀⟩ := ih (hc.sub (.fn us (.refl u)))
    obtain ⟨hts, hss₁⟩ := ihs (fun u' hu => hc.sub (.arg u hu (.refl u')))
    refine ⟨.app ht hts, ?_⟩
    intro s hm
    rcases List.mem_append.mp (hp.symm.subset hm) with hm | hm
    · exact hss₀ s hm
    · exact hss₁ s hm
  | nil => exact ⟨by simp, by simp⟩
  | cons _ _ ih ihs =>
    rename_i hc
    obtain ⟨ht, hs₀⟩ := ih (hc _ (by simp))
    obtain ⟨hts, hs₁⟩ := ihs (fun u hu => hc u (by simp [hu]))
    constructor
    · intro t hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ht
      · exact hts t hm
    · intro s hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hs₀ s hm
      · exact hs₁ s hm

theorem Separated.lam {t : DTerm} (ℓ : Label) (ht : Separated t) : Separated (.lam ℓ t) := by
  intro s hs xs hx
  cases hs with
  | refl =>
    cases hx with
    | empty => simp
    | root => simp
    | lam _ hx hz => simpa only [CutEntry.labels_mapCtx] using ht t (.refl t) _ hx
  | lam _ hs => exact ht s hs xs hx

private theorem partition_labels_nodup {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) (hc : Correct u) :
    (t.lamLabels ++ ss.flatMap DTerm.lamLabels).Nodup := by
  have hp : u.lamLabels.Perm (t.lamLabels ++ ss.flatMap DTerm.lamLabels) :=
    Multiset.coe_eq_coe.mp (by simpa only [← Multiset.coe_add] using h.lamLabels)
  exact hp.nodup_iff.mp hc.uniquely_labeled

/-- Reconstruct correctness of the body and every argument from a strongly sequential
contractum, before introducing the new lambda. -/
theorem PSubst.correct_parts {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) (hc : StronglySequential u) :
    Correct t ∧ ∀ s ∈ ss, Correct s := by
  obtain ⟨Γ, ρ, hu⟩ := hc.correct.typable
  obtain ⟨Θ, Δs, σs, ht, hss, _, _⟩ := h.inverse hu
  obtain ⟨hat, hass⟩ := h.annotations hc.correct
  obtain ⟨hst, hsss⟩ := h.separated hu hc.separate
  have hl := partition_labels_nodup h hc.correct
  refine ⟨correct_of_separated ⟨_, _, ht⟩ hat hst
    ((List.sublist_append_left _ _).nodup hl), ?_⟩
  intro s hs
  apply correct_of_separated (hss.typable_of_mem hs) (hass s hs) (hsss s hs)
  exact (DTerm.Sub.labels_arg hs).nodup ((List.sublist_append_right _ _).nodup hl)

/-- Correctness-preserving beta expansion. The additional separation invariant supplies
sequentiality of the newly gathered binder domain; freshness preserves lambda uniqueness. -/
theorem subject_expansion_correct_beta {t u : DTerm} {ss : List DTerm}
    (ℓ : Label) (h : PSubst t 0 ss u) (hc : StronglySequential u)
    (hfresh : ℓ ∉ u.lamLabels) : Correct (.app (.lam ℓ t) ss) := by
  obtain ⟨Γ, τ, hu⟩ := hc.correct.typable
  obtain ⟨hct, hcss⟩ := h.correct_parts hc
  have ha := h.annotations hc.correct
  have hs := h.separated hu hc.separate
  have hp : u.lamLabels.Perm (t.lamLabels ++ ss.flatMap DTerm.lamLabels) :=
    Multiset.coe_eq_coe.mp (by simpa only [← Multiset.coe_add] using h.lamLabels)
  have hl := partition_labels_nodup h hc.correct
  have hf : ℓ ∉ t.lamLabels ++ ss.flatMap DTerm.lamLabels :=
    fun hm => hfresh (hp.mem_iff.mpr hm)
  have hl' : (DTerm.app (.lam ℓ t) ss).lamLabels.Nodup := by
    simpa only [DTerm.lamLabels, List.cons_append, List.nodup_cons] using And.intro hf hl
  have he := subject_expansion_beta ℓ h hu
  have hctx := hc.correct.seq_ctx u Γ τ (.refl u) hu
  cases he with
  | app ht hss hperm =>
    have hcl : Correct (.lam ℓ t) := correct_of_separated ⟨_, _, ht⟩ (.lam ℓ ha.1)
      (hs.1.lam ℓ) ((DTerm.Sub.fn ss (.refl (.lam ℓ t))).lamLabels_sublist.nodup hl')
    exact Correct.app ht hss hperm hcl hcss hl' hctx

@[simp] theorem Ctx.remove_zero_shift_inserted (k : ℕ) (Γ : Ctx) :
    (Γ.shift (k + 1) 0).remove 0 = Γ.shift k 0 := by
  rw [Ctx.shift_succ_zero, Ctx.remove_zero_cons]

private theorem PSubst.no_resources {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {τ : Ty} (ht : HasType Γ t τ) (hz : Γ k = 0) :
    ss = [] := by
  have he := h.occTypes
  rw [← linearity ht k, hz] at he
  have hn : ss.length = 0 := by simpa using (congrArg Multiset.card he).symm
  exact List.eq_nil_of_length_eq_zero hn

private theorem PSubst.empty_typing {t u : DTerm} {k : ℕ}
    (h : PSubst t k [] u) {Γ Δ : Ctx} {τ ρ : Ty}
    (ht : HasType Γ t τ) (hu : HasType Δ u ρ) : Γ.remove k = Δ ∧ τ = ρ := by
  obtain ⟨Θ, Ξs, σs, hb, hss, _, he⟩ := h.inverse hu
  cases hss
  obtain ⟨rfl, rfl⟩ := hasType_unique ht hb
  exact ⟨by simpa using he.symm, rfl⟩

private theorem cut_compose_root {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ Δ : Ctx} {τ ρ : Ty}
    (ht : HasType Γ t τ) (hu : HasType Δ u ρ)
    (hz : ∀ p ∈ ({(Γ, τ)} : Multiset CutEntry), p.1 k = 0)
    {ys : Multiset CutEntry} (hy : FreeCutMulti ss ys) :
    FreeCut u (({(Γ, τ)} : Multiset CutEntry).map (CutEntry.mapCtx (Ctx.remove k)) +
      ys.map (CutEntry.mapCtx (Ctx.shift k 0))) := by
  have hss := h.no_resources ht (hz (Γ, τ) (by simp))
  subst ss
  cases hy
  obtain ⟨he, hτ⟩ := h.empty_typing ht hu
  simpa [CutEntry.mapCtx, he, hτ] using FreeCut.root hu

/-- Compose a free cut independent of the substituted variable with arbitrary free cuts
of all arguments. The combined selection remains a disjoint free cut of the contractum.
This tracks proper free subterms and their full contexts, not merely their root labels. -/
theorem PSubst.compose_cut {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {ρ : Ty} (hu : HasType Γ u ρ)
    {xs ys : Multiset CutEntry} (hx : FreeCut t xs) (hz : ∀ p ∈ xs, p.1 k = 0)
    (hy : FreeCutMulti ss ys) :
    FreeCut u (xs.map (CutEntry.mapCtx (Ctx.remove k)) +
      ys.map (CutEntry.mapCtx (Ctx.shift k 0))) := by
  induction h using PSubst.rec
    (motive_2 := fun ts k ss us _ => ∀ {Γs ρs}, HasTypeMulti Γs us ρs →
      ∀ {xs ys}, FreeCutMulti ts xs → (∀ p ∈ xs, p.1 k = 0) → FreeCutMulti ss ys →
      FreeCutMulti us (xs.map (CutEntry.mapCtx (Ctx.remove k)) +
        ys.map (CutEntry.mapCtx (Ctx.shift k 0))))
    generalizing Γ ρ xs ys with
  | var_eq k hs =>
    cases hx with
    | empty =>
      cases hy with
      | cons hy hs =>
        cases hs
        simpa using hy.shift k 0
    | root ht => exact cut_compose_root (.var_eq k hs) ht hu hz hy
  | var_lt τ hn =>
    cases hx with
    | empty => cases hy; simpa using FreeCut.empty _
    | root ht => exact cut_compose_root (.var_lt τ hn) ht hu hz hy
  | var_gt τ hn =>
    cases hx with
    | empty => cases hy; simpa using FreeCut.empty _
    | root ht => exact cut_compose_root (.var_gt τ hn) ht hu hz hy
  | @lam t u k ss ℓ h ih =>
    cases hu with
    | lam _ hu =>
      have work {zs : Multiset CutEntry} (hcut : FreeCut t zs)
          (hz₀ : ∀ p ∈ zs, p.1 0 = 0) (hzk : ∀ p ∈ zs, p.1 (k + 1) = 0) :
          FreeCut (.lam ℓ u)
            ((zs.map (CutEntry.mapCtx (Ctx.remove 0))).map (CutEntry.mapCtx (Ctx.remove k)) +
              ys.map (CutEntry.mapCtx (Ctx.shift k 0))) := by
        have hc := ih hu hcut hzk hy
        have hz' : ∀ p ∈ zs.map (CutEntry.mapCtx (Ctx.remove (k + 1))) +
            ys.map (CutEntry.mapCtx (Ctx.shift (k + 1) 0)), p.1 0 = 0 := by
          intro p hp
          rcases Multiset.mem_add.mp hp with hp | hp
          · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
            simpa [CutEntry.mapCtx] using hz₀ q hq
          · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
            simp [CutEntry.mapCtx, Ctx.cons, -Ctx.shift_sum]
        simp only [Multiset.map_map, Function.comp_def]
        change FreeCut (.lam ℓ u)
          (zs.map (fun p => ((p.1.remove 0).remove k, p.2)) +
            ys.map (fun p => (p.1.shift k 0, p.2)))
        simpa only [Multiset.map_add, Multiset.map_map, Function.comp_def, CutEntry.mapCtx,
          Ctx.remove_zero_remove_succ, Ctx.remove_zero_shift_inserted] using FreeCut.lam ℓ hc hz'
      cases hx with
      | empty => simpa using work (.empty t) (by simp) (by simp)
      | root ht => exact cut_compose_root (.lam ℓ h) ht (.lam ℓ hu) hz hy
      | lam _ hx hz₀ =>
        apply work hx hz₀
        intro p hp
        have he := hz (CutEntry.mapCtx (Ctx.remove 0) p) (Multiset.mem_map.mpr ⟨p, hp, rfl⟩)
        simpa [CutEntry.mapCtx] using he
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    cases hu with
    | app hu hus hperm =>
      obtain ⟨ys₀, ys₁, he, hy₀, hy₁⟩ := (hy.perm hp.symm).split
      subst ys
      have work {as bs : Multiset CutEntry} (ha : FreeCut t as) (hb : FreeCutMulti ts bs)
          (hz' : ∀ p ∈ as + bs, p.1 k = 0) :
          FreeCut (.app u us) ((as + bs).map (CutEntry.mapCtx (Ctx.remove k)) +
            (ys₀ + ys₁).map (CutEntry.mapCtx (Ctx.shift k 0))) := by
        have h₀ := ih hu ha (fun p hp => hz' p (Multiset.mem_add.mpr (.inl hp))) hy₀
        have h₁ := ihs hus hb (fun p hp => hz' p (Multiset.mem_add.mpr (.inr hp))) hy₁
        convert FreeCut.app h₀ h₁ using 1
        simp only [Multiset.map_add]
        ac_rfl
      cases hx with
      | empty => simpa using work (.empty t) (FreeCutMulti.empty ts) (by simp)
      | root ht => exact cut_compose_root (.app h hs hp) ht (.app hu hus hperm) hz hy
      | app hx hxs => exact work hx hxs hz
  | nil =>
    rename_i Γs ρs hu xs ys hx hz hy
    cases hx
    cases hy
    simpa using FreeCutMulti.nil
  | cons _ _ ih ihs =>
    rename_i Γs ρs hu xs ys hx hz hy
    cases hu with
    | cons hu hus =>
      cases hx with
      | cons hx hxs =>
        obtain ⟨ys₀, ys₁, rfl, hy₀, hy₁⟩ := hy.split
        have h₀ := ih hu hx (fun p hp => hz p (Multiset.mem_add.mpr (.inl hp))) hy₀
        have h₁ := ihs hus hxs (fun p hp => hz p (Multiset.mem_add.mpr (.inr hp))) hy₁
        convert FreeCutMulti.cons h₀ h₁ using 1
        simp only [Multiset.map_add]
        ac_rfl

namespace Ty

/-- All labels occurring in a type, including labels below its external constructor. -/
def labels : Ty → List Label
  | .base _ ℓ => [ℓ]
  | .arrow M ℓ ρ => ℓ :: (M.flatMap labels ++ labels ρ)

theorem label_mem_labels (τ : Ty) : τ.label ∈ τ.labels := by
  cases τ <;> simp [label, labels]

end Ty

namespace DTerm

/-- Types of all subterm occurrences. This is finite even though typing contexts are functions. -/
def allTypes : DTerm → List Ty
  | .var _ τ => [τ]
  | .lam ℓ t => (DTerm.lam ℓ t).ty :: allTypes t
  | .app t ss => (DTerm.app t ss).ty :: (allTypes t ++ ss.flatMap allTypes)

/-- A finite forbidden-label support that includes lambda labels and every label in every
subterm type, hence in particular every label inside every variable annotation. -/
def labelSupport (t : DTerm) : Finset Label :=
  (t.lamLabels ++ t.allTypes.flatMap Ty.labels).toFinset

theorem ty_mem_allTypes (t : DTerm) : t.ty ∈ t.allTypes := by
  cases t <;> simp [allTypes, DTerm.ty]

private theorem allTypes_arg {s : DTerm} {ss : List DTerm} (hm : s ∈ ss) :
    s.allTypes.Sublist (ss.flatMap allTypes) := by
  induction ss with
  | nil => simp at hm
  | cons a ss ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.sublist_append_left _ _
    · exact (ih hm).trans (List.sublist_append_right _ _)

theorem Sub.allTypes_sublist {s t : DTerm} (hs : Sub s t) : s.allTypes.Sublist t.allTypes := by
  induction hs with
  | refl => exact .refl _
  | lam ℓ _ ih => simp only [allTypes]; exact ih.cons _
  | fn ss _ ih =>
    simp only [allTypes]
    exact (ih.trans (List.sublist_append_left _ _)).cons _
  | arg t hm _ ih =>
    simp only [allTypes]
    exact (ih.trans ((allTypes_arg hm).trans (List.sublist_append_right _ _))).cons _

theorem Sub.labelSupport_subset {s t : DTerm} (hs : Sub s t) :
    s.labelSupport ⊆ t.labelSupport := by
  intro ℓ hm
  simp only [labelSupport, List.mem_toFinset, List.mem_append] at hm ⊢
  rcases hm with hm | hm
  · exact .inl (hs.lamLabels_sublist.subset hm)
  · obtain ⟨τ, hτ, hℓ⟩ := List.mem_flatMap.mp hm
    exact .inr (List.mem_flatMap.mpr ⟨τ, hs.allTypes_sublist.subset hτ, hℓ⟩)

theorem lamLabel_mem_support {t : DTerm} {ℓ : Label} (hm : ℓ ∈ t.lamLabels) :
    ℓ ∈ t.labelSupport := by simp [labelSupport, hm]

theorem typeLabel_mem_support {t : DTerm} {τ : Ty} (hm : τ ∈ t.allTypes) :
    τ.label ∈ t.labelSupport := by
  simp only [labelSupport, List.mem_toFinset, List.mem_append]
  exact .inr (List.mem_flatMap.mpr ⟨τ, hm, τ.label_mem_labels⟩)

end DTerm

/-- Every type selected by a free cut is the type of an actual subterm occurrence. -/
theorem FreeCut.type_mem {t : DTerm} {xs : Multiset CutEntry} (h : FreeCut t xs) :
    ∀ p ∈ xs, p.2 ∈ t.allTypes := by
  induction h using FreeCut.rec
    (motive_2 := fun ts xs _ => ∀ p ∈ xs, p.2 ∈ ts.flatMap DTerm.allTypes) with
  | empty => simp
  | root ht =>
    intro p hp
    have he := Multiset.mem_singleton.mp hp
    subst p
    simpa only [hasType_ty ht] using DTerm.ty_mem_allTypes _
  | lam ℓ h hz ih =>
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    simpa only [DTerm.allTypes, CutEntry.mapCtx] using List.mem_cons_of_mem _ (ih q hq)
  | app h hs ih ihs =>
    intro p hp
    simp only [DTerm.allTypes]
    apply List.mem_cons_of_mem
    rcases Multiset.mem_add.mp hp with hp | hp
    · exact List.mem_append_left _ (ih p hp)
    · exact List.mem_append_right _ (ihs p hp)
  | nil => simp at *
  | cons h hs ih ihs =>
    rename_i p hp
    simp only [List.flatMap_cons]
    rcases Multiset.mem_add.mp hp with hp | hp
    · exact List.mem_append_left _ (ih p hp)
    · exact List.mem_append_right _ (ihs p hp)

theorem FreeCut.label_mem_support {t : DTerm} {xs : Multiset CutEntry} (h : FreeCut t xs)
    {ℓ : Label} (hm : ℓ ∈ xs.map CutEntry.label) : ℓ ∈ t.labelSupport := by
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hm
  exact DTerm.typeLabel_mem_support (h.type_mem p hp)

/-- Freshness can always be satisfied while honoring any externally forbidden finite set. -/
theorem exists_fresh_label (t : DTerm) (avoid : Finset Label) :
    ∃ ℓ, ℓ ∉ avoid ∧ ℓ ∉ t.labelSupport := by
  let ℓ := (avoid ∪ t.labelSupport).sup id + 1
  have hn : ℓ ∉ avoid ∪ t.labelSupport := by
    intro hm
    have hle := Finset.le_sup (f := id) hm
    change ℓ ≤ (avoid ∪ t.labelSupport).sup id at hle
    exact (Nat.not_succ_le_self _) hle
  exact ⟨ℓ, fun h => hn (Finset.mem_union_left _ h), fun h => hn (Finset.mem_union_right _ h)⟩

@[simp] theorem CutEntry.mapCtx_shift_zero : mapCtx (Ctx.shift 0 0) = id := by
  funext p
  rcases p with ⟨Γ, τ⟩
  simp [mapCtx]

/-- A beta expansion preserves every selected old free subterm's full context and type.
The only possible extra cut entry is the new lambda itself. This is stronger than the
pointwise subterm-tracking clause: it also preserves disjointness of the whole selection. -/
theorem PSubst.track_beta_cut {t u : DTerm} {ss : List DTerm}
    (h : PSubst t 0 ss u) (ℓ : Label) {Γ : Ctx} {τ : Ty} (hu : HasType Γ u τ)
    {xs : Multiset CutEntry} (hx : FreeCut (.app (.lam ℓ t) ss) xs) :
    ∃ ys zs, FreeCut u ys ∧ xs = ys + zs ∧
      (zs = 0 ∨ ∃ p, zs = {p} ∧ p.label = ℓ) := by
  cases hx with
  | empty => exact ⟨0, 0, .empty _, by simp, .inl rfl⟩
  | root ht =>
    obtain ⟨rfl, rfl⟩ := hasType_unique ht (subject_expansion_beta ℓ h hu)
    exact ⟨_, 0, .root hu, by simp, .inl rfl⟩
  | app hx hys =>
    have hargs := h.compose_cut hu (.empty t) (by simp) hys
    simp only [Multiset.map_zero, zero_add, CutEntry.mapCtx_shift_zero, Multiset.map_id] at hargs
    cases hx with
    | empty => exact ⟨_, 0, hargs, by simp, .inl rfl⟩
    | root ht =>
      refine ⟨_, _, hargs, by ac_rfl, .inr ⟨_, rfl, ?_⟩⟩
      rw [CutEntry.label, hasType_ty ht]
      simp [DTerm.ty, Ty.label]
    | lam _ hxs hz =>
      have hold := h.compose_cut hu hxs hz hys
      simp only [CutEntry.mapCtx_shift_zero, Multiset.map_id] at hold
      exact ⟨_, 0, hold, by simp, .inl rfl⟩

/-- The strong invariant is preserved by beta expansion when freshness includes type
labels. This proves the original correctness invariant as part of the conclusion. -/
theorem subject_expansion_strong_beta {t u : DTerm} {ss : List DTerm}
    (ℓ : Label) (h : PSubst t 0 ss u) (hc : StronglySequential u)
    (hfresh : ℓ ∉ u.labelSupport) : StronglySequential (.app (.lam ℓ t) ss) := by
  obtain ⟨Γ, τ, hu⟩ := hc.correct.typable
  have hs := h.separated hu hc.separate
  refine ⟨subject_expansion_correct_beta ℓ h hc
    (fun hm => hfresh (DTerm.lamLabel_mem_support hm)), ?_⟩
  intro s hsub xs hx
  cases hsub with
  | refl =>
    obtain ⟨ys, zs, hy, rfl, hz⟩ := h.track_beta_cut ℓ hu hx
    have hn := hc.separate u (.refl u) ys hy
    rcases hz with rfl | ⟨p, rfl, hp⟩
    · simpa using hn
    · have hf : p.label ∉ ys.map CutEntry.label := by
        intro hm
        exact hfresh (hp ▸ hy.label_mem_support hm)
      rw [Multiset.map_add, Multiset.map_singleton, add_comm, Multiset.singleton_add,
        Multiset.nodup_cons]
      exact ⟨hf, hn⟩
  | fn _ hsub => exact (hs.1.lam ℓ) s hsub xs hx
  | arg _ hm hsub => exact hs.2 _ hm s hsub xs hx

namespace DCtx

def comp : DCtx → DCtx → DCtx
  | .hole, D => D
  | .lam ℓ C, D => .lam ℓ (C.comp D)
  | .appL C ss, D => .appL (C.comp D) ss
  | .appR t us C vs, D => .appR t us (C.comp D) vs

@[simp] theorem plug_comp (C D : DCtx) (t : DTerm) :
    (C.comp D).plug t = C.plug (D.plug t) := by
  induction C <;> simp [comp, plug, *]

theorem sub_plug (C : DCtx) (t : DTerm) : DTerm.Sub t (C.plug t) := by
  induction C with
  | hole => exact .refl _
  | lam ℓ C ih => exact .lam ℓ ih
  | appL C ss ih => exact .fn ss ih
  | appR u us C vs ih => exact .arg u (by simp) ih

end DCtx

theorem DStep.plug {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u) (C : DCtx) :
    DStep (C.plug t) ℓ (C.plug u) := by
  induction C with
  | hole => exact h
  | lam m C ih => exact .lam m ih
  | appL C ss ih => exact .appL ss ih
  | appR v us C vs ih => exact .appR v us vs ih

/-- Exact antichain tracking for one fresh-lambda expansion. -/
def CutTracks (v u : DTerm) (ℓ : Label) : Prop :=
  ∀ xs, FreeCut v xs → ∃ ys zs, FreeCut u ys ∧ xs = ys + zs ∧
    (zs = 0 ∨ ∃ p, zs = {p} ∧ p.label = ℓ)

private theorem cut_track_root {v u : DTerm} (ℓ : Label)
    (ht : ∀ {Γ τ}, HasType Γ u τ → HasType Γ v τ) (hu : u.Typable)
    {Γ : Ctx} {τ : Ty} (hv : HasType Γ v τ) :
    ∃ ys zs, FreeCut u ys ∧ ({(Γ, τ)} : Multiset CutEntry) = ys + zs ∧
      (zs = 0 ∨ ∃ p, zs = {p} ∧ p.label = ℓ) := by
  obtain ⟨Δ, ρ, hu⟩ := hu
  obtain ⟨rfl, rfl⟩ := hasType_unique hv (ht hu)
  exact ⟨_, 0, .root hu, by simp, .inl rfl⟩

/-- Tracking is closed under capturing contexts. Full context equality of old cut entries
is what makes the binder case work without an implicit free-variable assumption. -/
theorem DCtx.track_cut (C : DCtx) {v u : DTerm} {ℓ : Label}
    (ht : ∀ {Γ τ}, HasType Γ u τ → HasType Γ v τ) (htrack : CutTracks v u ℓ)
    (hu : (C.plug u).Typable) : CutTracks (C.plug v) (C.plug u) ℓ := by
  induction C with
  | hole => exact htrack
  | lam m C ih =>
    have hu' := (DTerm.Sub.lam m (.refl (C.plug u))).typable hu
    intro xs hx
    cases hx with
    | empty => exact ⟨0, 0, .empty _, by simp, .inl rfl⟩
    | root hv => exact cut_track_root ℓ ((DCtx.lam m C).typing_mono ht) hu hv
    | lam _ hx hz =>
      obtain ⟨ys, zs, hy, he, hnew⟩ := ih hu' _ hx
      have hyz : ∀ p ∈ ys, p.1 0 = 0 := by
        intro p hp
        apply hz p
        rw [he]
        exact Multiset.mem_add.mpr (.inl hp)
      refine ⟨ys.map (CutEntry.mapCtx (Ctx.remove 0)), zs.map (CutEntry.mapCtx (Ctx.remove 0)),
        .lam m hy hyz, by rw [he, Multiset.map_add], ?_⟩
      rcases hnew with rfl | ⟨p, rfl, hp⟩
      · exact .inl (by simp)
      · exact .inr ⟨CutEntry.mapCtx (Ctx.remove 0) p, by simp, hp⟩
  | appL C ss ih =>
    have hu' := (DTerm.Sub.fn ss (.refl (C.plug u))).typable hu
    intro xs hx
    cases hx with
    | empty => exact ⟨0, 0, .empty _, by simp, .inl rfl⟩
    | root hv => exact cut_track_root ℓ ((DCtx.appL C ss).typing_mono ht) hu hv
    | app hx hss =>
      obtain ⟨ys, zs, hy, he, hnew⟩ := ih hu' _ hx
      exact ⟨_, zs, .app hy hss, by rw [he]; ac_rfl, hnew⟩
  | appR t us C vs ih =>
    have hu' := (DTerm.Sub.arg t (by simp : C.plug u ∈ us ++ C.plug u :: vs)
      (.refl (C.plug u))).typable hu
    intro xs hx
    cases hx with
    | empty => exact ⟨0, 0, .empty _, by simp, .inl rfl⟩
    | root hv => exact cut_track_root ℓ ((DCtx.appR t us C vs).typing_mono ht) hu hv
    | app hfn hargs =>
      obtain ⟨as, bs, rfl, ha, hb⟩ := hargs.split
      cases hb with
      | cons hx hvs =>
        obtain ⟨ys, zs, hy, he, hnew⟩ := ih hu' _ hx
        exact ⟨_, zs, .app hfn (ha.append (.cons hy hvs)), by rw [he]; ac_rfl, hnew⟩

theorem CutTracks.root_separate {v u : DTerm} {ℓ : Label} (h : CutTracks v u ℓ)
    (hs : Separated u) (hfresh : ℓ ∉ u.labelSupport) {xs : Multiset CutEntry}
    (hx : FreeCut v xs) : (xs.map CutEntry.label).Nodup := by
  obtain ⟨ys, zs, hy, rfl, hz⟩ := h xs hx
  have hn := hs u (.refl u) ys hy
  rcases hz with rfl | ⟨p, rfl, hp⟩
  · simpa using hn
  · have hf : p.label ∉ ys.map CutEntry.label := by
      intro hm
      exact hfresh (hp ▸ hy.label_mem_support hm)
    rw [Multiset.map_add, Multiset.map_singleton, add_comm, Multiset.singleton_add,
      Multiset.nodup_cons]
    exact ⟨hf, hn⟩

theorem AnnotationsSequential.plug (C : DCtx) {u v : DTerm}
    (ho : AnnotationsSequential (C.plug u)) (hv : AnnotationsSequential v) :
    AnnotationsSequential (C.plug v) := by
  induction C with
  | hole => exact hv
  | lam m C ih => exact .lam m (ih (ho.sub (.lam m (.refl _))))
  | appL C ss ih =>
    exact .app (ih (ho.sub (.fn ss (.refl _)))) (fun s hs => ho.sub (.arg _ hs (.refl s)))
  | appR t us C vs ih =>
    apply AnnotationsSequential.app (ho.sub (.fn _ (.refl t)))
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ho.sub (.arg t (List.mem_append_left _ hs) (.refl s))
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact ih (ho.sub (.arg t (by simp) (.refl _)))
      · exact ho.sub (.arg t (by simp [hs]) (.refl s))

/-- The separation invariant is compositional when old free cuts are tracked exactly and
the new label avoids the entire original context, including sibling type annotations. -/
theorem Separated.plug (C : DCtx) {u v : DTerm} {ℓ : Label}
    (ht : ∀ {Γ τ}, HasType Γ u τ → HasType Γ v τ) (htrack : CutTracks v u ℓ)
    (hv : Separated v) (hu : (C.plug u).Typable) (ho : Separated (C.plug u))
    (hf : ℓ ∉ (C.plug u).labelSupport) : Separated (C.plug v) := by
  induction C with
  | hole => exact hv
  | lam m C ih =>
    have hsub : DTerm.Sub (C.plug u) ((DCtx.lam m C).plug u) := .lam m (.refl _)
    exact (ih (hsub.typable hu) (ho.sub hsub)
      (fun hm => hf (hsub.labelSupport_subset hm))).lam m
  | appL C ss ih =>
    have hsub : DTerm.Sub (C.plug u) ((DCtx.appL C ss).plug u) := .fn ss (.refl _)
    have hc := ih (hsub.typable hu) (ho.sub hsub)
      (fun hm => hf (hsub.labelSupport_subset hm))
    intro s hs xs hx
    cases hs with
    | refl => exact ((DCtx.appL C ss).track_cut ht htrack hu).root_separate ho hf hx
    | fn _ hs => exact hc s hs xs hx
    | arg _ hm hs => exact ho s (.arg (C.plug u) hm hs) xs hx
  | appR t us C vs ih =>
    have hsub : DTerm.Sub (C.plug u) ((DCtx.appR t us C vs).plug u) :=
      .arg t (by simp) (.refl _)
    have hc := ih (hsub.typable hu) (ho.sub hsub)
      (fun hm => hf (hsub.labelSupport_subset hm))
    intro s hs xs hx
    cases hs with
    | refl => exact ((DCtx.appR t us C vs).track_cut ht htrack hu).root_separate ho hf hx
    | fn _ hs => exact ho s (.fn _ hs) xs hx
    | arg _ hm hs =>
      rcases List.mem_append.mp hm with hm | hm
      · exact ho s (.arg t (List.mem_append_left _ hm) hs) xs hx
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact hc s hs xs hx
        · exact ho s (.arg t (by simp [hm]) hs) xs hx

private theorem DCtx.lamLabels_add (C : DCtx) {u v : DTerm} {ℓ : Label}
    (h : (v.lamLabels : Multiset Label) = (u.lamLabels : Multiset Label) + {ℓ}) :
    ((C.plug v).lamLabels : Multiset Label) = ((C.plug u).lamLabels : Multiset Label) + {ℓ} := by
  induction C with
  | hole => exact h
  | lam m C ih =>
    simpa only [DCtx.plug, DTerm.lamLabels, ← Multiset.cons_coe, Multiset.cons_add] using
      congrArg (fun xs : Multiset Label => m ::ₘ xs) ih
  | appL C ss ih =>
    simp only [DCtx.plug, DTerm.lamLabels, ← Multiset.coe_add, ih]
    ac_rfl
  | appR t us C vs ih =>
    simp only [DCtx.plug, DTerm.lamLabels, List.flatMap_append, List.flatMap_cons,
      ← Multiset.coe_add, ih]
    ac_rfl

/-- Strong, correctness-preserving subject expansion in any capturing context. Freshness
is checked against the whole contractum, so it covers the sibling cases of backwards
simulation as well as the newly introduced arrow type. -/
theorem subject_expansion_strong {t u : DTerm} {ss : List DTerm} (C : DCtx) (ℓ : Label)
    (hp : PSubst t 0 ss u) (hc : StronglySequential (C.plug u))
    (hf : ℓ ∉ (C.plug u).labelSupport) :
    StronglySequential (C.plug (.app (.lam ℓ t) ss)) := by
  have hsub := C.sub_plug u
  have hlu : ℓ ∉ u.labelSupport := fun hm => hf (hsub.labelSupport_subset hm)
  have hv := subject_expansion_strong_beta ℓ hp (hc.sub hsub) hlu
  have ht : ∀ {Γ τ}, HasType Γ u τ → HasType Γ (.app (.lam ℓ t) ss) τ :=
    fun h => subject_expansion_beta ℓ hp h
  obtain ⟨Δ, ρ, hluTyped⟩ := (hc.correct.sub hsub).typable
  have htrack : CutTracks (.app (.lam ℓ t) ss) u ℓ :=
    fun _ hx => hp.track_beta_cut ℓ hluTyped hx
  have hsep := Separated.plug C ht htrack hv.separate hc.correct.typable hc.separate hf
  have hann := AnnotationsSequential.plug C hc.correct.annotations hv.correct.annotations
  obtain ⟨Γ, τ, hu⟩ := hc.correct.typable
  have htyped := C.typing_mono ht hu
  have hl : ((DTerm.app (.lam ℓ t) ss).lamLabels : Multiset Label) =
      (u.lamLabels : Multiset Label) + {ℓ} := by
    simp only [DTerm.lamLabels, ← Multiset.cons_coe, ← Multiset.coe_add]
    rw [hp.lamLabels]
    simp [Multiset.singleton_add, add_comm]
  have hlabels : (C.plug (.app (.lam ℓ t) ss)).lamLabels.Nodup := by
    have hn : (((C.plug (.app (.lam ℓ t) ss)).lamLabels : Multiset Label)).Nodup := by
      rw [C.lamLabels_add hl, add_comm, Multiset.singleton_add, Multiset.nodup_cons]
      exact ⟨fun hm => hf (DTerm.lamLabel_mem_support hm), hc.correct.uniquely_labeled⟩
    exact hn
  exact ⟨correct_of_separated ⟨_, _, htyped⟩ hann hsep hlabels, hsep⟩

/-- Reflect typing through a variable shift, without assuming correctness in advance. -/
theorem HasType.of_shift {t : DTerm} {d c : ℕ} {Γ : Ctx} {τ : Ty}
    (h : HasType Γ (t.shift d c) τ) : ∃ Δ, HasType Δ t τ := by
  induction t using DTerm.rec
    (motive_2 := fun ts => ∀ c {Γs σs},
      HasTypeMulti Γs (ts.map (DTerm.shift d c)) σs → ∃ Δs, HasTypeMulti Δs ts σs)
    generalizing c Γ τ with
  | var n σ =>
    simp only [DTerm.shift] at h
    split at h <;> cases h <;> exact ⟨_, .var n σ⟩
  | lam ℓ t ih =>
    simp only [DTerm.shift] at h
    cases h with
    | @lam Γ M σ _ _ hb =>
      obtain ⟨Δ, hΔ⟩ := ih hb
      have he := (hasType_unique (hΔ.shift d (c + 1)) hb).1
      have hz : Δ 0 = M := by simpa [Ctx.cons] using congrFun he 0
      have hctx : Ctx.cons M (Δ.remove 0) = Δ := by rw [← hz, Ctx.eta_cons]
      exact ⟨_, .lam ℓ (by rw [hctx]; exact hΔ)⟩
  | app t ts ih ihs =>
    simp only [DTerm.shift] at h
    cases h with
    | app ht hs hp =>
      obtain ⟨Δ, hΔ⟩ := ih ht
      obtain ⟨Δs, hΔs⟩ := ihs c hs
      exact ⟨_, .app hΔ hΔs hp⟩
  | nil =>
    rename_i c Γs σs h
    cases h
    exact ⟨[], .nil⟩
  | cons t ts ih ihs =>
    rename_i c Γs σs h
    cases h with
    | cons ht hs =>
      obtain ⟨Δ, hΔ⟩ := ih ht
      obtain ⟨Δs, hΔs⟩ := ihs c hs
      exact ⟨_, .cons hΔ hΔs⟩

/-- A refinement of a shifted pure term is itself a shifted refinement. -/
theorem Refines.unshift {t : LTerm} {u : DTerm} {d c : ℕ}
    (h : Refines (t.shift d c) u) : ∃ v, Refines t v ∧ u = v.shift d c := by
  induction t generalizing c u with
  | var n =>
    simp only [LTerm.shift] at h
    split at h <;> cases h <;> rename_i τ <;>
      exact ⟨.var n τ, .var _ _, by simp [DTerm.shift, *]⟩
  | lam t ih =>
    simp only [LTerm.shift] at h
    cases h with
    | lam ℓ h =>
      obtain ⟨v, hv, he⟩ := ih h
      exact ⟨.lam ℓ v, .lam ℓ hv, by simp [DTerm.shift, he]⟩
  | app t s ih ihs =>
    simp only [LTerm.shift] at h
    cases h with
    | @app _ _ u ss hu hs =>
      obtain ⟨v, hv, he⟩ := ih hu
      have work : ∀ us, (∀ a ∈ us, Refines (s.shift d c) a) →
          ∃ (vs : List DTerm), (∀ a ∈ vs, Refines s a) ∧ us = vs.map (DTerm.shift d c) := by
        intro us
        induction us with
        | nil => intro _; exact ⟨[], by simp, rfl⟩
        | cons a us ih' =>
          intro h
          obtain ⟨b, hb, he⟩ := ihs (h a (by simp))
          obtain ⟨bs, hbs, hes⟩ := ih' (fun a ha => h a (by simp [ha]))
          exact ⟨b :: bs, by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hb hbs,
            by simp [he, hes]⟩
      obtain ⟨vs, hvs, hes⟩ := work ss hs
      exact ⟨.app v vs, .app hv hvs, by simp [DTerm.shift, he, hes]⟩

/-- Decompose a typed refinement of a pure substitution. This is stated on raw terms:
correctness of the expansion is a consequence of the strong invariant, not a premise. -/
theorem refinement_substitution_decomposition {t s : LTerm} {u : DTerm} {k : ℕ}
    {Γ : Ctx} {τ : Ty} (hr : Refines (LTerm.substAt k s t) u) (hu : HasType Γ u τ) :
    ∃ b ss, Refines t b ∧ (∀ a ∈ ss, Refines s a) ∧ PSubst b k ss u := by
  induction t generalizing k u Γ τ with
  | var n =>
    by_cases hlt : n < k
    · simp only [LTerm.substAt, hlt] at hr
      cases hr
      exact ⟨_, [], .var _ _, by simp, .var_lt _ hlt⟩
    · by_cases heq : n = k
      · subst n
        simp only [LTerm.substAt, Nat.lt_irrefl, ite_false, ite_true] at hr
        obtain ⟨a, ha, he⟩ := hr.unshift
        subst u
        obtain ⟨Δ, hΔ⟩ := hu.of_shift
        exact ⟨.var k τ, [a], .var _ _, by simpa using ha, .var_eq k hΔ⟩
      · simp only [LTerm.substAt, hlt, heq] at hr
        cases hr
        exact ⟨_, [], .var _ _, by simp, .var_gt _ (by omega)⟩
  | lam t ih =>
    simp only [LTerm.substAt] at hr
    cases hr with
    | lam ℓ hr =>
      cases hu with
      | lam _ hu =>
        obtain ⟨b, ss, hb, hss, hp⟩ := ih hr hu
        exact ⟨.lam ℓ b, ss, .lam ℓ hb, hss, .lam ℓ hp⟩
  | app t r ih ihr =>
    simp only [LTerm.substAt] at hr
    cases hr with
    | @app _ _ u us hru hrus =>
      cases hu with
      | app hu hus hperm =>
        obtain ⟨b, ss₀, hb, hss₀, hp₀⟩ := ih hru hu
        have work : ∀ us {Γs ρs}, HasTypeMulti Γs us ρs →
            (∀ a ∈ us, Refines (LTerm.substAt k s r) a) →
            ∃ bs ss, (∀ a ∈ bs, Refines r a) ∧ (∀ a ∈ ss, Refines s a) ∧
              PSubstMulti bs k ss us := by
          intro us
          induction us with
          | nil => intro _ _ _ _; exact ⟨[], [], by simp, by simp, .nil k⟩
          | cons a us ih' =>
            intro Γs ρs hus hrs
            cases hus with
            | cons ha has =>
              obtain ⟨b, ss₁, hb, hss₁, hp₁⟩ := ihr (hrs a (by simp)) ha
              obtain ⟨bs, ss₂, hbs, hss₂, hp₂⟩ := ih' has (fun a ha => hrs a (by simp [ha]))
              refine ⟨b :: bs, ss₁ ++ ss₂, ?_, ?_, .cons hp₁ hp₂⟩
              · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hb hbs
              · intro a ha
                rcases List.mem_append.mp ha with ha | ha
                · exact hss₁ a ha
                · exact hss₂ a ha
        obtain ⟨bs, ss₁, hbs, hss₁, hp₁⟩ := work us hus hrus
        refine ⟨.app b bs, ss₀ ++ ss₁, .app hb hbs, ?_, .app hp₀ hp₁ (.refl _)⟩
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hss₀ a ha
        · exact hss₁ a ha

/-- Refinement decomposition with the original correctness and strong-sequentiality
conclusions, using a finite forbidden-label set for the newly introduced lambda. -/
theorem refinement_substitution_inverse {t s : LTerm} {u : DTerm}
    (hr : Refines (LTerm.substAt 0 s t) u) (hc : StronglySequential u) (avoid : Finset Label) :
    ∃ b ss ℓ, Refines t b ∧ (∀ a ∈ ss, Refines s a) ∧
      PSubst b 0 ss u ∧ ℓ ∉ avoid ∧ ℓ ∉ u.labelSupport ∧
      StronglySequential (.app (.lam ℓ b) ss) ∧ u = b.subst 0 ss := by
  obtain ⟨Γ, τ, hu⟩ := hc.correct.typable
  obtain ⟨b, ss, hb, hss, hp⟩ := refinement_substitution_decomposition hr hu
  obtain ⟨ℓ, havoid, hfresh⟩ := exists_fresh_label u avoid
  have hseq : SeqMS (ss.map DTerm.ty : Multiset Ty) := by
    rw [← hp.occTypes]
    exact (hp.separated hu hc.separate).1.occTypes 0
  exact ⟨b, ss, ℓ, hb, hss, hp, havoid, hfresh,
    subject_expansion_strong_beta ℓ hp hc hfresh, hp.eq_subst hseq⟩

/-- The separation invariant is strictly stronger than plain correctness. The concrete
counterexample is rejected by the invariant used in backwards reconstruction. -/
theorem correct_not_stronglySequential : ∃ u : DTerm, Correct u ∧ ¬ StronglySequential u := by
  obtain ⟨t, u, ss, Γ, τ, ℓ, hp, _, _, hcu, hfresh, _, hn⟩ :=
    correctness_subject_expansion_counterexample
  exact ⟨u, hcu, fun hs => hn (subject_expansion_correct_beta ℓ hp hs hfresh)⟩

/-- Backwards simulation with a context-parametric induction hypothesis. Freshness is
chosen against the entire current term, so sequential processing of argument siblings
preserves correctness and separation without an implicit label-renaming convention. -/
theorem backwards_simulation_in_context {t s : LTerm} (h : Beta t s)
    {u : DTerm} (hr : Refines s u) (C : DCtx) (hc : StronglySequential (C.plug u))
    (avoid : Finset Label) :
    ∃ (v : DTerm) (hv : StronglySequential (C.plug v)), Refines t v ∧
      Relation.ReflTransGen CRed ⟨C.plug v, hv.correct⟩ ⟨C.plug u, hc.correct⟩ := by
  induction h generalizing u C with
  | beta t s =>
    obtain ⟨Γ, τ, hu⟩ := (hc.correct.sub (C.sub_plug u)).typable
    obtain ⟨b, ss, hb, hss, hp⟩ := refinement_substitution_decomposition hr hu
    obtain ⟨ℓ, havoid, hfresh⟩ := exists_fresh_label (C.plug u) avoid
    have hv := subject_expansion_strong C ℓ hp hc hfresh
    have hseq : SeqMS (ss.map DTerm.ty : Multiset Ty) := by
      rw [← hp.occTypes]
      exact (hp.separated hu (hc.sub (C.sub_plug u)).separate).1.occTypes 0
    have he := hp.eq_subst hseq
    have hd : DStep (C.plug (.app (.lam ℓ b) ss)) ℓ (C.plug u) := by
      simpa only [← he] using (DStep.beta ℓ b ss).plug C
    exact ⟨_, hv, .app (.lam ℓ hb) hss, .single ⟨ℓ, hd⟩⟩
  | lam h ih =>
    cases hr with
    | @lam _ u' m hr =>
      have hc' : StronglySequential ((C.comp (.lam m .hole)).plug u') := by
        simpa only [DCtx.plug_comp, DCtx.plug] using hc
      obtain ⟨v, hv, hr, hp⟩ := ih hr (C.comp (.lam m .hole)) hc'
      refine ⟨.lam m v, ?_, .lam m hr, ?_⟩
      · simpa only [DCtx.plug_comp, DCtx.plug] using hv
      · simpa only [DCtx.plug_comp, DCtx.plug] using hp
  | appL s h ih =>
    cases hr with
    | @app _ _ u' us hr hrs =>
      have hc' : StronglySequential ((C.comp (.appL .hole us)).plug u') := by
        simpa only [DCtx.plug_comp, DCtx.plug] using hc
      obtain ⟨v, hv, hr, hp⟩ := ih hr (C.comp (.appL .hole us)) hc'
      refine ⟨.app v _, ?_, .app hr hrs, ?_⟩
      · simpa only [DCtx.plug_comp, DCtx.plug] using hv
      · simpa only [DCtx.plug_comp, DCtx.plug] using hp
  | @appR f a b h ih =>
    cases hr with
    | @app _ _ u us hfn hrs =>
      have work : ∀ (todo doneArgs : List DTerm), (∀ q ∈ todo, Refines b q) →
          ∀ hc' : StronglySequential (C.plug (.app u (doneArgs ++ todo))),
          ∃ (vs : List DTerm) (hv : StronglySequential (C.plug (.app u (doneArgs ++ vs)))),
            (∀ q ∈ vs, Refines a q) ∧ Relation.ReflTransGen CRed
              ⟨C.plug (.app u (doneArgs ++ vs)), hv.correct⟩
              ⟨C.plug (.app u (doneArgs ++ todo)), hc'.correct⟩ := by
        intro todo
        induction todo with
        | nil => intro doneArgs _ hc'; exact ⟨[], hc', by simp, .refl⟩
        | cons q todo ih' =>
          intro doneArgs hrs hc'
          have hctx : StronglySequential ((C.comp (.appR u doneArgs .hole todo)).plug q) := by
            simpa only [DCtx.plug_comp, DCtx.plug] using hc'
          obtain ⟨q', hq', hrq', hpath⟩ := ih (hrs q (by simp))
            (C.comp (.appR u doneArgs .hole todo)) hctx
          have hnext : StronglySequential (C.plug (.app u ((doneArgs ++ [q']) ++ todo))) := by
            simpa [DCtx.plug, List.append_assoc] using hq'
          obtain ⟨vs, hvs, hrvs, hrest⟩ := ih' (doneArgs ++ [q'])
            (fun v hv => hrs v (by simp [hv])) hnext
          refine ⟨q' :: vs, ?_, ?_, ?_⟩
          · simpa only [List.append_assoc, List.singleton_append] using hvs
          · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hrq' hrvs
          · have hp₁ := hpath
            simp only [DCtx.plug_comp, DCtx.plug] at hp₁
            have hp₂ := hrest
            simp only [List.append_assoc, List.singleton_append] at hp₂
            exact hp₂.trans hp₁
      obtain ⟨vs, hv, hrvs, hpath⟩ := work us [] hrs (by simpa using hc)
      refine ⟨.app u vs, ?_, .app hfn hrvs, ?_⟩
      · simpa using hv
      · simpa using hpath

/-- Backwards simulation for the thesis' position-addressed beta steps, with correctness
and strong sequentiality proved at the reconstructed source. -/
theorem backwards_simulation {t s : LTerm} (h : BetaStep t s) {u : CTerm}
    (hr : Refines s u.1) (hc : StronglySequential u.1) :
    ∃ v : CTerm, StronglySequential v.1 ∧ Refines t v.1 ∧
      Relation.ReflTransGen CRed v u := by
  obtain ⟨v, hv, hrv, hp⟩ := backwards_simulation_in_context
    (betaStep_iff_beta.mp h) hr .hole hc ∅
  exact ⟨⟨v, hv.correct⟩, hv, hrv, hp⟩

/-- Iterate backwards reconstruction along a complete beta derivation. -/
theorem backwards_multisimulation {t s : LTerm} (h : Relation.ReflTransGen BetaStep t s)
    {u : CTerm} (hr : Refines s u.1) (hc : StronglySequential u.1) :
    ∃ v : CTerm, StronglySequential v.1 ∧ Refines t v.1 ∧
      Relation.ReflTransGen CRed v u := by
  induction h generalizing u with
  | refl => exact ⟨u, hc, hr, .refl⟩
  | tail h hstep ih =>
    obtain ⟨w, hw, hrw, hwu⟩ := backwards_simulation hstep hr hc
    obtain ⟨v, hv, hrv, hvw⟩ := ih hrw hw
    exact ⟨v, hv, hrv, hvw.trans hwu⟩

theorem Separated.app_nil {t : DTerm} (hs : Separated t) : Separated (.app t []) := by
  intro s hsub xs hx
  cases hsub with
  | refl =>
    cases hx with
    | empty => simp
    | root => simp
    | app hx hxs => cases hxs; simpa using hs t (.refl t) _ hx
  | fn _ hsub => exact hs s hsub xs hx
  | arg _ hm _ => simp at hm

theorem StronglySequential.var (n : ℕ) {τ : Ty} (hτ : τ.Sequential) :
    StronglySequential (.var n τ) := ⟨Correct.var n hτ, separated_var n τ⟩

theorem StronglySequential.app_nil {Γ : Ctx} {t : DTerm} {ℓ : Label} {τ : Ty}
    (h : HasType Γ t (.arrow [] ℓ τ)) (hc : StronglySequential t) :
    StronglySequential (.app t []) := by
  have ht : HasType Γ (.app t []) τ := by simpa using HasType.app h .nil (List.Perm.refl [])
  have hs := Separated.app_nil hc.separate
  exact ⟨correct_of_separated ⟨_, _, ht⟩ (.app hc.correct.annotations (by simp)) hs
    (by simpa [DTerm.lamLabels] using hc.correct.uniquely_labeled), hs⟩

theorem StronglySequential.lam {t : DTerm} (ℓ : Label) (hc : StronglySequential t)
    (hfresh : ℓ ∉ t.lamLabels) : StronglySequential (.lam ℓ t) := by
  obtain ⟨Γ, τ, ht⟩ := hc.correct.typable
  have hb : HasType (Ctx.cons (Γ 0) (Γ.remove 0)) t τ := by rw [Ctx.eta_cons]; exact ht
  have htyped := HasType.lam ℓ hb
  have hs := Separated.lam ℓ hc.separate
  exact ⟨correct_of_separated ⟨_, _, htyped⟩ (.lam ℓ hc.correct.annotations) hs
    (by simpa [DTerm.lamLabels] using And.intro hfresh hc.correct.uniquely_labeled), hs⟩

private theorem head_has_strong_refinement {t : LTerm} (h : IsHeadApp t)
    (τ : Ty) (hτ : τ.Sequential) :
    ∃ u Γ, Refines t u ∧ HasType Γ u τ ∧ StronglySequential u ∧ IsEmptyHeadApp u := by
  induction h generalizing τ with
  | var n => exact ⟨_, _, .var n τ, .var n τ, .var n hτ, .var n τ⟩
  | app s h ih =>
    have hA : (Ty.arrow [] 0 τ).Sequential :=
      Ty.Sequential.arrow (by simp [SeqMS]) (by simp) hτ
    obtain ⟨u, Γ, hr, ht, hc, hshape⟩ := ih (.arrow [] 0 τ) hA
    refine ⟨.app u [], Γ, .app hr (by simp), ?_, hc.app_nil ht, .app hshape⟩
    simpa using HasType.app ht .nil (List.Perm.refl [])

/-- Canonical head-normal-form refinements satisfy the stronger invariant and use empty
argument lists. This provides the invariant's base case for backwards reconstruction. -/
theorem hnf_has_strong_refinement {t : LTerm} (h : IsHNF t) :
    ∃ u : DTerm, Refines t u ∧ StronglySequential u ∧ IsEmptyHNF u := by
  induction h with
  | head h =>
    obtain ⟨u, Γ, hr, ht, hc, hshape⟩ := head_has_strong_refinement h (.base 0 0)
      (Ty.sequential_base 0 0)
    exact ⟨u, hr, hc, .head hshape⟩
  | lam h ih =>
    obtain ⟨u, hr, hc, hshape⟩ := ih
    obtain ⟨ℓ, _, hfresh⟩ := exists_fresh_label u ∅
    exact ⟨.lam ℓ u, .lam ℓ hr,
      hc.lam ℓ (fun hm => hfresh (DTerm.lamLabel_mem_support hm)), .lam ℓ hshape⟩

/-- The formerly delicate `(3 → 2)` implication, proved independently of the unfinished
forward simulation and residual-theory proofs. -/
theorem head_normalizing_has_strong_refinement {t : LTerm} (h : t.HasHNF) :
    ∃ v : CTerm, StronglySequential v.1 ∧ Refines t v.1 ∧
      ∃ n : CTerm, IsEmptyHNF n.1 ∧ Relation.ReflTransGen CRed v n := by
  obtain ⟨s, hpath, hnf⟩ := h
  obtain ⟨u, hr, hc, hshape⟩ := hnf_has_strong_refinement hnf
  let n : CTerm := ⟨u, hc.correct⟩
  obtain ⟨v, hv, hrv, hp⟩ := backwards_multisimulation hpath (u := n) hr hc
  exact ⟨v, hv, hrv, n, hshape, hp⟩

/-! ### Forward refinement and head normalization (`08-11`, `08-12`, `08-15`) -/

theorem Refines.shift {t : LTerm} {u : DTerm} (h : Refines t u) (d c : ℕ) :
    Refines (t.shift d c) (u.shift d c) := by
  induction h generalizing c with
  | var n τ => simp only [LTerm.shift, DTerm.shift]; split <;> exact .var _ _
  | lam ℓ h ih => simpa only [LTerm.shift, DTerm.shift] using Refines.lam ℓ (ih (c + 1))
  | app h hs ih ihs =>
    simp only [LTerm.shift, DTerm.shift]
    apply Refines.app (ih c)
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ihs b hb c

/-- The substitution-refinement lemma is proved for resource partitions first; this
avoids assuming that raw type-directed lookup succeeds without typing premises. -/
theorem PSubst.refines {b u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst b k ss u) {t s : LTerm} (hr : Refines t b)
    (hs : ∀ a ∈ ss, Refines s a) : Refines (LTerm.substAt k s t) u := by
  induction h using PSubst.rec
    (motive_2 := fun bs k ss us _ => ∀ t s : LTerm,
      (∀ b ∈ bs, Refines t b) → (∀ a ∈ ss, Refines s a) →
      ∀ a ∈ us, Refines (LTerm.substAt k s t) a) generalizing t s with
  | @var_eq a Γ τ k ht =>
    cases hr
    simpa only [LTerm.substAt, lt_self_iff_false, ↓reduceIte] using
      (hs a (by simp)).shift k 0
  | @var_lt n k τ hn => cases hr; simpa [LTerm.substAt, hn] using Refines.var n τ
  | @var_gt n k τ hn =>
    cases hr
    simpa [LTerm.substAt, show ¬ n < k by omega, show ¬ n = k by omega]
      using Refines.var (n - 1) τ
  | lam ℓ h ih =>
    cases hr with
    | lam _ hr => simpa only [LTerm.substAt] using Refines.lam ℓ (ih hr hs)
  | app h hm hp ih ihm =>
    cases hr with
    | app hr hrs =>
      simp only [LTerm.substAt]
      apply Refines.app (ih hr (fun a ha => hs a (hp.subset (List.mem_append_left _ ha))))
      exact ihm _ _ hrs (fun a ha => hs a (hp.subset (List.mem_append_right _ ha)))
  | nil => rename_i t s ht hs a ha; simp at ha
  | cons h hm ih ihm =>
    rename_i t s ht hs a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ih (ht _ (by simp)) (fun a ha => hs a (List.mem_append_left _ ha))
    · exact ihm t s (fun b hb => ht b (by simp [hb]))
        (fun a ha => hs a (List.mem_append_right _ ha)) a ha

theorem refinement_substitution {t s : LTerm} {b : DTerm} {ss : List DTerm}
    {ℓ : Label} (hr : Refines t b) (hs : ∀ a ∈ ss, Refines s a)
    (hc : Correct (.app (.lam ℓ b) ss)) : Refines (LTerm.substAt 0 s t) (b.subst 0 ss) := by
  obtain ⟨Γ, τ, ht⟩ := hc.typable
  cases ht with
  | app hf hm hp =>
    cases hf with
    | @lam Γ M τ b ℓ hb =>
      have hmatch : (_ : Multiset Ty) = (b.occTypes 0 : Multiset Ty) :=
        (Multiset.coe_eq_coe.mpr hp).trans (by simpa [Ctx.cons] using hasType_occTypes hb 0)
      obtain ⟨u, hu⟩ := PSubst.exists hm hmatch
      have hseq : SeqMS (ss.map DTerm.ty : Multiset Ty) := by
        rw [← hm.types_eq, hmatch]
        have he := hasType_occTypes hb 0
        change M = _ at he
        rw [← he]
        simpa [Ctx.cons] using
          hc.seq_ctx b _ _ (.fn ss (.lam ℓ (.refl b))) hb 0
      rw [← hu.eq_subst hseq]
      exact hu.refines hr hs

theorem DRed.reduces_plug {t u : DTerm} (h : Relation.ReflTransGen DRed t u) (C : DCtx) :
    Relation.ReflTransGen DRed (C.plug t) (C.plug u) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => obtain ⟨ℓ, hs⟩ := hs; exact ih.tail ⟨ℓ, hs.plug C⟩

theorem DRed.reduces_app_args {ss us : List DTerm}
    (h : List.Forall₂ (Relation.ReflTransGen DRed) ss us) (f : DTerm) (pre : List DTerm) :
    Relation.ReflTransGen DRed (.app f (pre ++ ss)) (.app f (pre ++ us)) := by
  induction h generalizing pre with
  | nil => exact .refl
  | @cons a b ss us hab h ih =>
    have h₁ := DRed.reduces_plug hab (.appR f pre .hole ss)
    have h₂ := ih (pre ++ [b])
    simp only [List.append_assoc, List.singleton_append] at h₂
    exact h₁.trans h₂

/-- Forward simulation, by the four context cases of `08-12-simulation.tex`.
Argument copies are reduced one at a time; empty argument lists require no steps. -/
theorem simulation_raw {t s : LTerm} (h : Beta t s) {u : DTerm}
    (hr : Refines t u) (hc : Correct u) :
    ∃ v, Relation.ReflTransGen DRed u v ∧ Refines s v := by
  induction h generalizing u with
  | beta t s =>
    cases hr with
    | app hf hs =>
      cases hf with
      | lam ℓ hf => exact ⟨_, .single ⟨ℓ, .beta ℓ _ _⟩, refinement_substitution hf hs hc⟩
  | lam h ih =>
    cases hr with
    | lam ℓ hr =>
      obtain ⟨v, hp, hv⟩ := ih hr (hc.sub (.lam ℓ (.refl _)))
      exact ⟨_, DRed.reduces_plug hp (.lam ℓ .hole), .lam ℓ hv⟩
  | appL s h ih =>
    cases hr with
    | @app _ _ f ss hf hs =>
      obtain ⟨v, hp, hv⟩ := ih hf (hc.sub (.fn ss (.refl _)))
      exact ⟨_, DRed.reduces_plug hp (.appL .hole ss), .app hv hs⟩
  | @appR t s s' h ih =>
    cases hr with
    | @app _ _ f ss hf hs =>
      have work : ∀ ts : List DTerm, (∀ a ∈ ts, Refines s a) →
          (∀ a ∈ ts, Correct a) → ∃ us, List.Forall₂
            (fun a b => Relation.ReflTransGen DRed a b ∧ Refines s' b) ts us := by
        intro ts
        induction ts with
        | nil => intro _ _; exact ⟨[], .nil⟩
        | cons a ts iht =>
          intro hr hc
          obtain ⟨b, hp, hb⟩ := ih (hr a (by simp)) (hc a (by simp))
          obtain ⟨bs, hbs⟩ := iht (fun a ha => hr a (by simp [ha]))
            (fun a ha => hc a (by simp [ha]))
          exact ⟨b :: bs, .cons ⟨hp, hb⟩ hbs⟩
      obtain ⟨us, hu⟩ := work ss hs (fun a ha => hc.sub (.arg f ha (.refl a)))
      have hp := hu.imp (fun _ _ h => h.1)
      refine ⟨.app f us, ?_, .app hf ?_⟩
      · simpa using DRed.reduces_app_args hp f []
      · clear hp hs hc
        induction hu with
        | nil => simp
        | cons h hu ih => simpa only [List.mem_cons, forall_eq_or_imp] using And.intro h.2 ih

theorem DRed.correct_reduces {t u : DTerm} (hc : Correct t)
    (h : Relation.ReflTransGen DRed t u) : Correct u := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => obtain ⟨ℓ, hs⟩ := hs; exact correct_of_dStep ih hs

theorem DRed.reduces_correct_terms {t u : DTerm} (h : Relation.ReflTransGen DRed t u)
    (ht : Correct t) (hu : Correct u) :
    Relation.ReflTransGen CRed (⟨t, ht⟩ : CTerm) (⟨u, hu⟩ : CTerm) := by
  induction h with
  | refl => exact .refl
  | @tail b c hp hs ih =>
    have hb := DRed.correct_reduces ht hp
    exact (ih hb).tail hs

/-- A head reduction always has a represented copy in a refinement: unlike a step
inside an erased argument, it consumes a lambda of the correct refining term. -/
theorem Refines.head_progress {t : LTerm} {u : DTerm} (hr : Refines t u)
    (hc : Correct u) : IsHNF t ∨
      ∃ s v ℓ, Beta t s ∧ DStep u ℓ v ∧ Refines s v := by
  induction t generalizing u with
  | var n => exact .inl (.head (.var n))
  | lam t ih =>
    cases hr with
    | lam ℓ hr =>
      rcases ih hr (hc.sub (.lam ℓ (.refl _))) with hn | ⟨s, v, m, hb, hd, hv⟩
      · exact .inl (.lam hn)
      · exact .inr ⟨.lam s, .lam ℓ v, m, .lam hb, .lam ℓ hd, .lam ℓ hv⟩
  | app t s ih _ =>
    cases hr with
    | @app _ _ f ss hf hs =>
      cases t with
      | lam b =>
        cases hf with
        | lam ℓ hf => exact .inr ⟨_, _, ℓ, .beta b s, .beta ℓ _ _,
            refinement_substitution hf hs hc⟩
      | var n => exact .inl (.head (.app s (.var n)))
      | app a b =>
        rcases ih hf (hc.sub (.fn ss (.refl f))) with hn | ⟨r, v, ℓ, hb, hd, hv⟩
        · cases hn with
          | head hh => exact .inl (.head (.app s hh))
        · exact .inr ⟨.app r s, .app v ss, ℓ, .appL s hb, .appL ss hd, .app hv hs⟩

/-- The forward implication uses induction on the number of lambdas in the refinement,
as in the head-reduction argument of `08-15-has-hnf-has-refinement.tex`. -/
theorem Refines.hasHNF {t : LTerm} {u : DTerm} (hr : Refines t u)
    (hc : Correct u) : t.HasHNF := by
  generalize he : u.size = n
  induction n using Nat.strong_induction_on generalizing t u with
  | h n ih =>
    rcases hr.head_progress hc with hn | ⟨s, v, ℓ, hb, hd, hv⟩
    · exact ⟨t, .refl, hn⟩
    · have hsize := size_dStep hc hd
      obtain ⟨r, hp, hn⟩ := ih v.size (by omega) hv (correct_of_dStep hc hd) rfl
      exact ⟨r, (Relation.ReflTransGen.single (betaStep_iff_beta.mpr hb)).trans hp, hn⟩

/-! ### Named simulation traces

Keeping the contracted labels makes it possible to compare the constructive context
proof with the sorted canonical development used by `simTgt`.
-/

inductive DTrace : DTerm → List Label → DTerm → Prop
  | nil (t : DTerm) : DTrace t [] t
  | cons {t u v : DTerm} {ℓ : Label} {σ : List Label} :
      DStep t ℓ u → DTrace u σ v → DTrace t (ℓ :: σ) v

namespace DTrace

theorem append {t u v : DTerm} {σ τ : List Label} (h : DTrace t σ u)
    (k : DTrace u τ v) : DTrace t (σ ++ τ) v := by
  induction h with
  | nil => exact k
  | cons hs h ih => exact .cons hs (ih k)

theorem plug {t u : DTerm} {σ : List Label} (h : DTrace t σ u) (C : DCtx) :
    DTrace (C.plug t) σ (C.plug u) := by
  induction h with
  | nil => exact .nil _
  | cons hs h ih => exact .cons (hs.plug C) ih

theorem specification {t u : DTerm} {σ : List Label} (h : DTrace t σ u)
    (ht : Correct t) :
    distRS.Valid (⟨t, ht⟩ : CTerm) σ ∧
    (distRS.tgt (⟨t, ht⟩ : CTerm) σ).1 = u := by
  induction h with
  | nil => exact ⟨trivial, rfl⟩
  | @cons t v u ℓ σ hs h ih =>
    obtain ⟨hm, he⟩ := (dStep_iff_hasRedex ht).1 hs
    have hv := correct_of_dStep ht hs
    obtain ⟨hp, hu⟩ := ih hv
    have eq : distRS.contract (⟨t, ht⟩ : CTerm) ℓ = (⟨v, hv⟩ : CTerm) :=
      Subtype.ext he.symm
    refine ⟨⟨hm, eq.symm ▸ hp⟩, ?_⟩
    change (distRS.tgt (distRS.contract (⟨t, ht⟩ : CTerm) ℓ) σ).1 = u
    rw [eq]
    exact hu

end DTrace

@[simp] theorem simRes_app_zero (f : DTerm) (ss : List DTerm) (p : Pos) :
    simRes (.app f ss) (0 :: p) = simRes f p := by cases f <;> rfl

@[simp] theorem simRes_app_one (f : DTerm) (ss : List DTerm) (p : Pos) :
    simRes (.app f ss) (1 :: p) = (ss.map (simRes · p)).foldr (· ∪ ·) ∅ := by
  cases f <;> rfl

@[simp] theorem LTerm.contractAt_app_zero (f s : LTerm) (p : Pos) :
    contractAt (.app f s) (0 :: p) = .app (contractAt f p) s := by cases f <;> rfl

@[simp] theorem LTerm.contractAt_app_one (f s : LTerm) (p : Pos) :
    contractAt (.app f s) (1 :: p) = .app f (contractAt s p) := by cases f <;> rfl

theorem mem_fold_simRes {ss : List DTerm} {p : Pos} {ℓ : Label} :
    ℓ ∈ (ss.map (simRes · p)).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ ss, ℓ ∈ simRes a p := by
  induction ss with
  | nil => simp
  | cons a ss ih => simp [ih, or_and_right, exists_or]

/-- Every represented distributive redex comes from a beta-redex position in the
underlying pure term (`08-13-reverse-simulation.tex`). -/
theorem DStep.simulation_position {u v : DTerm} {ℓ : Label} (h : DStep u ℓ v)
    {t : LTerm} (hr : Refines t u) :
    ∃ p, isRedexAt t p = true ∧ ℓ ∈ simRes u p := by
  induction h generalizing t with
  | beta ℓ b ss =>
    cases hr with
    | app hf hs => cases hf with | lam _ hf => exact ⟨[], rfl, by simp [simRes]⟩
  | lam m h ih =>
    cases hr with
    | lam _ hr =>
      obtain ⟨p, hp, hm⟩ := ih hr
      exact ⟨0 :: p, by simpa only [isRedexAt, subAt] using hp, hm⟩
  | appL ss h ih =>
    cases hr with
    | app hf hs =>
      obtain ⟨p, hp, hm⟩ := ih hf
      exact ⟨0 :: p, by simpa only [isRedexAt, subAt] using hp, by simpa using hm⟩
  | appR f us vs h ih =>
    cases hr with
    | app hf hs =>
      obtain ⟨p, hp, hm⟩ := ih (hs _ (by simp))
      exact ⟨1 :: p, by simpa only [isRedexAt, subAt] using hp,
        by rw [simRes_app_one]; exact mem_fold_simRes.mpr ⟨_, by simp, hm⟩⟩

theorem simRes_isStep {u : DTerm} {p : Pos} {ℓ : Label} (h : ℓ ∈ simRes u p) :
    u.hasRedex ℓ = true := by
  induction p generalizing u with
  | nil =>
    cases u with
    | var => simp [simRes] at h
    | lam => simp [simRes] at h
    | app f ss => cases f <;> simp_all [simRes, DTerm.hasRedex, DTerm.isLamWith]
  | cons i p ih =>
    cases u with
    | var => simp [simRes] at h
    | lam m u =>
      cases i with
      | zero => simpa only [DTerm.hasRedex] using (ih (u := u) (by simpa only [simRes] using h))
      | succ i => simp [simRes] at h
    | app f ss =>
      cases i with
      | zero =>
        have hf := ih (u := f) (by simpa only [simRes_app_zero] using h)
        simp [DTerm.hasRedex, hf]
      | succ i =>
        cases i with
        | succ i => simp [simRes] at h
        | zero =>
          obtain ⟨a, ha, hm⟩ := mem_fold_simRes.mp (simRes_app_one f ss p ▸ h)
          have hm' := ih hm
          have hx : ss.any (DTerm.hasRedex · ℓ) = true := List.any_eq_true.mpr ⟨a, ha, hm'⟩
          simp [DTerm.hasRedex, hx]

/-- Every simulation image is the label of a lambda of its source. -/
theorem simRes_label_mem {u : DTerm} {p : Pos} {ℓ : Label} (h : ℓ ∈ simRes u p) :
    ℓ ∈ u.lamLabels := by
  obtain ⟨v, hv⟩ := DTerm.hasRedex_iff_step.mp (simRes_isStep h)
  exact hv.label_mem

private theorem simRes_root_unique {u : DTerm} {q : Pos} {ℓ : Label} (hc : Correct u)
    (hroot : ℓ ∈ simRes u []) (hq : ℓ ∈ simRes u q) : q = [] := by
  cases u with
  | var => simp [simRes] at hroot
  | lam => simp [simRes] at hroot
  | app f ss =>
    cases f with
    | var => simp [simRes] at hroot
    | app => simp [simRes] at hroot
    | lam m b =>
      have he : ℓ = m := by simpa only [simRes, Finset.mem_singleton] using hroot
      subst ℓ
      cases q with
      | nil => rfl
      | cons i q =>
        cases i with
        | zero =>
          have hh : m ∈ simRes (.lam m b) q := by simpa only [simRes_app_zero] using hq
          obtain ⟨v, hv⟩ := DTerm.hasRedex_iff_step.mp (simRes_isStep hh)
          exact False.elim (hv.label_ne_outer (hc.sub (.fn ss (.refl _))) rfl)
        | succ i =>
          cases i with
          | zero =>
            obtain ⟨s, hs, hm⟩ := mem_fold_simRes.mp (simRes_app_one _ _ _ ▸ hq)
            exact False.elim (hc.fn_arg_labels (by simp [DTerm.lamLabels]) hs (simRes_label_mem hm))
          | succ i => simp [simRes] at hq

/-- Different pure redex positions have disjoint simulation images (`08-19`). -/
theorem simRes_position_unique {u : DTerm} {p q : Pos} {ℓ : Label} (hc : Correct u)
    (hp : ℓ ∈ simRes u p) (hq : ℓ ∈ simRes u q) : p = q := by
  induction u using DTerm.ind generalizing p q with
  | var n τ => cases p <;> simp [simRes] at hp
  | lam m u ih =>
    cases p with
    | nil => simp [simRes] at hp
    | cons i p =>
      cases i with
      | succ i => simp [simRes] at hp
      | zero =>
        cases q with
        | nil => simp [simRes] at hq
        | cons j q =>
          cases j with
          | succ j => simp [simRes] at hq
          | zero =>
            exact congrArg (List.cons 0) (ih (hc.sub (.lam m (.refl u))) hp hq)
  | app f ss ih ihs =>
    cases p with
    | nil => exact (simRes_root_unique hc hp hq).symm
    | cons i p =>
      cases q with
      | nil => exact simRes_root_unique hc hq hp
      | cons j q =>
        cases i with
        | zero =>
          have hp' : ℓ ∈ simRes f p := by simpa only [simRes_app_zero] using hp
          cases j with
          | zero =>
            have hq' : ℓ ∈ simRes f q := by simpa only [simRes_app_zero] using hq
            exact congrArg (List.cons 0) (ih (hc.sub (.fn ss (.refl f))) hp' hq')
          | succ j =>
            cases j with
            | zero =>
              obtain ⟨s, hs, hq'⟩ := mem_fold_simRes.mp (simRes_app_one _ _ _ ▸ hq)
              exact False.elim (hc.fn_arg_labels (simRes_label_mem hp') hs (simRes_label_mem hq'))
            | succ j => simp [simRes] at hq
        | succ i =>
          cases i with
          | succ i => simp [simRes] at hp
          | zero =>
            obtain ⟨s, hs, hp'⟩ := mem_fold_simRes.mp (simRes_app_one _ _ _ ▸ hp)
            cases j with
            | zero =>
              have hq' : ℓ ∈ simRes f q := by simpa only [simRes_app_zero] using hq
              exact False.elim (hc.fn_arg_labels (simRes_label_mem hq') hs (simRes_label_mem hp'))
            | succ j =>
              cases j with
              | succ j => simp [simRes] at hq
              | zero =>
                obtain ⟨r, hr, hq'⟩ := mem_fold_simRes.mp (simRes_app_one _ _ _ ▸ hq)
                have hn := hc.uniquely_labeled
                rw [DTerm.lamLabels] at hn
                have he := unique_label_child (List.nodup_append.mp hn).2.1 hs hr
                  (simRes_label_mem hp') (simRes_label_mem hq')
                subst r
                exact congrArg (List.cons 1) (ihs s hs (hc.sub (.arg f hs (.refl s))) hp' hq')

theorem simulation_at_trace {p : Pos} {t : LTerm} {u : DTerm}
    (hr : Refines t u) (hc : Correct u) (hp : isRedexAt t p = true) :
    ∃ v σ, DTrace u σ v ∧ σ.toFinset = simRes u p ∧ Refines (contractAt t p) v := by
  induction p generalizing t u with
  | nil =>
    cases t with
    | var => simp [isRedexAt, subAt, isRedex] at hp
    | lam => simp [isRedexAt, subAt, isRedex] at hp
    | app t s =>
      cases t with
      | var => simp [isRedexAt, subAt, isRedex] at hp
      | app => simp [isRedexAt, subAt, isRedex] at hp
      | lam b =>
        cases hr with
        | app hf hs =>
          cases hf with
          | lam ℓ hf => exact ⟨_, [ℓ], .cons (.beta ℓ _ _) (.nil _), by simp [simRes],
              refinement_substitution hf hs hc⟩
  | cons i p ih =>
    cases t with
    | var => simp [isRedexAt, subAt] at hp
    | lam t =>
      cases i with
      | succ i => simp [isRedexAt, subAt] at hp
      | zero =>
        cases hr with
        | lam ℓ hr =>
          obtain ⟨v, σ, ht, he, hv⟩ := ih hr (hc.sub (.lam ℓ (.refl _)))
            (by simpa [isRedexAt, subAt] using hp)
          exact ⟨.lam ℓ v, σ, ht.plug (.lam ℓ .hole), he, .lam ℓ hv⟩
    | app t s =>
      cases hr with
      | @app _ _ f ss hf hs =>
        cases i with
        | zero =>
          obtain ⟨v, σ, ht, he, hv⟩ := ih hf (hc.sub (.fn ss (.refl _)))
            (by simpa [isRedexAt, subAt] using hp)
          exact ⟨.app v ss, σ, ht.plug (.appL .hole ss), by simpa using he,
            by simpa only [LTerm.contractAt_app_zero] using Refines.app hv hs⟩
        | succ i =>
          cases i with
          | succ i => simp [isRedexAt, subAt] at hp
          | zero =>
            have hp' : isRedexAt s p = true := by simpa [isRedexAt, subAt] using hp
            have work : ∀ ts pre : List DTerm, (∀ a ∈ ts, Refines s a) →
                (∀ a ∈ ts, Correct a) → ∃ us σ,
                DTrace (.app f (pre ++ ts)) σ (.app f (pre ++ us)) ∧
                σ.toFinset = (ts.map (simRes · p)).foldr (· ∪ ·) ∅ ∧
                ∀ a ∈ us, Refines (contractAt s p) a := by
              intro ts
              induction ts with
              | nil => intro pre _ _; exact ⟨[], [], .nil _, rfl, by simp⟩
              | cons a ts iht =>
                intro pre hr hc
                obtain ⟨b, σ, ht, he, hb⟩ := ih (hr a (by simp)) (hc a (by simp)) hp'
                obtain ⟨bs, τ, htt, het, hbs⟩ := iht (pre ++ [b])
                  (fun a ha => hr a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
                simp only [List.append_assoc, List.singleton_append] at htt
                exact ⟨b :: bs, σ ++ τ, (ht.plug (.appR f pre .hole ts)).append htt,
                  by simp [he, het], by simpa only [List.mem_cons, forall_eq_or_imp] using (And.intro hb hbs)⟩
            obtain ⟨us, σ, ht, he, hv⟩ := work ss [] hs
              (fun a ha => hc.sub (.arg f ha (.refl a)))
            exact ⟨.app f us, σ, ht, by simpa using he,
              by simpa only [Nat.zero_add, LTerm.contractAt_app_one] using Refines.app hf hv⟩

theorem ResidualSystem.IsDevelopment.valid {R : ResidualSystem} {t : R.Obj}
    {M : Finset R.Adr} {σ : List R.Adr} (h : R.IsDevelopment t M σ) : R.Valid t σ := by
  induction σ generalizing t M with
  | nil => trivial
  | cons a σ ih => exact ⟨h.1, ih h.2.2⟩

/-- The constructive simulation trace and the canonical sorted development have the
same names and therefore the same target. -/
theorem simulation_canonical {t : LTerm} {u : CTerm} {p : Pos}
    (hr : Refines t u.1) (hp : lambdaRS.isStep t p) :
    Refines (contractAt t p) (simTgt u p).1 := by
  obtain ⟨v, σ, ht, he, hv⟩ := simulation_at_trace hr u.2 hp
  obtain ⟨hσ, htarget⟩ := ht.specification u.2
  have hm : ∀ m ∈ simRes u.1 p, distRS.isStep u m := fun m hm => simRes_isStep hm
  have hd := (distRS.orthogonal.dev_complete u _ hm).1.valid
  have hn : distRS.names (distRS.dev u (simRes u.1 p)) = distRS.names σ := by
    simpa only [distRS, distRS.names, Finset.sort_toFinset] using he.symm
  have eq := ResidualSystem.tgt_eq_of_permEq distRS.orthogonal hd hσ
    ((distRS.permEq_iff_names hd hσ).2 hn)
  change Refines (contractAt t p) (distRS.tgt u (distRS.dev u (simRes u.1 p))).1
  rw [eq]
  exact htarget.symm ▸ hv

theorem tgt_simDeriv (t' : CTerm) (σ : List Pos) :
    distRS.tgt t' (simDeriv t' σ) = simTgtDeriv t' σ := by
  induction σ generalizing t' with
  | nil => rfl
  | cons p σ ih => rw [simDeriv, ResidualSystem.tgt_append, simTgtDeriv, ← ih]; rfl

theorem distRS_completeDevelopment_names {t : CTerm} {M : Finset Label} {σ : List Label}
    (hM : ∀ a ∈ M, distRS.isStep t a) (h : distRS.IsCompleteDevelopment t M σ) :
    distRS.names σ = M := by
  have hv := ResidualSystem.isDevelopment_valid h.1
  have h1 := (distRS.residual_names hM hv).1
  rw [h.2] at h1
  exact Finset.Subset.antisymm (distRS.development_subset hM h.1) (Finset.sdiff_eq_empty_iff_subset.mp h1.symm)

theorem distRS_completeDevelopment_permEq {t : CTerm} {M : Finset Label} {σ τ : List Label}
    (hM : ∀ a ∈ M, distRS.isStep t a)
    (hσ : distRS.IsCompleteDevelopment t M σ) (hτ : distRS.IsCompleteDevelopment t M τ) :
    distRS.PermEq t σ τ := by
  have hvσ := ResidualSystem.isDevelopment_valid hσ.1
  have hvτ := ResidualSystem.isDevelopment_valid hτ.1
  rw [distRS.permEq_iff_names hvσ hvτ]
  rw [distRS_completeDevelopment_names hM hσ, distRS_completeDevelopment_names hM hτ]

/-! ### Simulation residuals and substitution (for the cube lemma) -/

theorem simRes_var (n : ℕ) (τ : Ty) (p : Pos) : simRes (.var n τ) p = ∅ := by
  cases p <;> simp [simRes]

theorem simRes_lam_zero (ℓ : Label) (u : DTerm) (p : Pos) :
    simRes (.lam ℓ u) (0 :: p) = simRes u p := by simp [simRes]

theorem simRes_shift (d : ℕ) (t : DTerm) : ∀ (c : ℕ) (p : Pos),
    simRes (t.shift d c) p = simRes t p := by
  induction t using DTerm.ind with
  | var n τ =>
    intro c p
    by_cases h : n < c <;> simp [DTerm.shift, h, simRes_var]
  | lam m t ih =>
    intro c p
    cases p with
    | nil => simp [simRes, DTerm.shift]
    | cons i p =>
      cases i with
      | zero => simp [DTerm.shift, simRes_lam_zero, ih]
      | succ i => simp [simRes, DTerm.shift]
  | app t ss ih ihs =>
    intro c p
    cases p with
    | nil =>
      cases t with
      | var n τ => by_cases h : n < c <;> simp [DTerm.shift, h, simRes]
      | lam m t => simp [simRes, DTerm.shift]
      | app t ss' => simp [simRes, DTerm.shift]
    | cons i p =>
      cases i with
      | zero => simp only [DTerm.shift, simRes_app_zero]; exact ih c p
      | succ i =>
        cases i with
        | zero =>
          simp only [DTerm.shift]
          rw [show (((0 : ℕ) + 1) :: p) = (1 :: p) from rfl, simRes_app_one, simRes_app_one]
          ext ℓ
          rw [mem_fold_simRes, mem_fold_simRes]
          constructor
          · rintro ⟨a, ha, hℓ⟩
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
            exact ⟨b, hb, by rwa [ihs b hb c p] at hℓ⟩
          · rintro ⟨b, hb, hℓ⟩
            exact ⟨b.shift d c, List.mem_map_of_mem hb, by rwa [ihs b hb c p]⟩
        | succ i => simp [DTerm.shift, simRes]

/-- Substitution does not move redexes of the body. -/
theorem simRes_subst_redex {b : LTerm} {b' : DTerm} (hr : Refines b b') :
    ∀ (r : Pos) (k : ℕ) (ss : List DTerm), isRedexAt b r = true →
      simRes (b'.subst k ss) r = simRes b' r := by
  induction hr with
  | var n τ => intro r k ss h; simp [isRedexAt, subAt] at h; cases r <;> simp [subAt, isRedex] at h
  | lam ℓ h ih =>
    intro r k ss hp
    rcases r with _ | ⟨i, r⟩
    · simp [isRedexAt, subAt, isRedex] at hp
    · rcases i with _ | i
      · simp only [isRedexAt_lam_zero] at hp
        simp only [DTerm.subst, simRes_lam_zero]
        exact ih r (k + 1) ss hp
      · simp at hp
  | @app t s t' ss' ht hs iht ihs =>
    intro r k ss hp
    rcases r with _ | ⟨i, r⟩
    · cases ht with
      | lam ℓ _ => simp [DTerm.subst, simRes]
      | _ => simp [isRedexAt, subAt, isRedex] at hp
    · rcases i with _ | _ | i
      · simp only [isRedexAt_app_zero] at hp
        simp only [DTerm.subst, simRes_app_zero]
        exact iht r k ss hp
      · replace hp : isRedexAt s r = true := by simpa using hp
        simp only [DTerm.subst]
        rw [show (((0 : ℕ) + 1) :: r) = (1 :: r) from rfl, simRes_app_one, simRes_app_one]
        ext ℓ
        rw [mem_fold_simRes, mem_fold_simRes]
        constructor
        · rintro ⟨a, ha, hℓ⟩
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
          exact ⟨c, hc, by rwa [ihs c hc r k ss hp] at hℓ⟩
        · rintro ⟨c, hc, hℓ⟩
          exact ⟨c.subst k ss, List.mem_map_of_mem hc, by rwa [ihs c hc r k ss hp]⟩
      · simp at hp

/-- The bag of a correct redex has exactly the types of the occurrences of the bound variable,
and these types are pairwise distinct. -/
theorem bag_types {ℓ : Label} {b' : DTerm} {ss : List DTerm}
    (hc : Correct (.app (.lam ℓ b') ss)) :
    (ss.map DTerm.ty : Multiset Ty) = (b'.occTypes 0 : Multiset Ty) ∧
      SeqMS (ss.map DTerm.ty : Multiset Ty) := by
  obtain ⟨Γ, τ, ht⟩ := hc.typable
  cases ht with
  | app hf hm hp =>
    cases hf with
    | @lam Γ M τ b ℓ hb =>
      have hmatch : (_ : Multiset Ty) = (b'.occTypes 0 : Multiset Ty) :=
        (Multiset.coe_eq_coe.mpr hp).trans (by simpa [Ctx.cons] using hasType_occTypes hb 0)
      refine ⟨by rw [← hm.types_eq]; exact hmatch, ?_⟩
      rw [← hm.types_eq, hmatch]
      have he := hasType_occTypes hb 0
      change M = _ at he
      rw [← he]
      simpa [Ctx.cons] using
        hc.seq_ctx b' _ _ (.fn ss (.lam ℓ (.refl b'))) hb 0

/-- In a bag with pairwise distinct types, lookup by type finds the element itself. -/
theorem find_ty_eq {ss : List DTerm} (hseq : SeqMS (ss.map DTerm.ty : Multiset Ty))
    {a : DTerm} (ha : a ∈ ss) : ss.find? (fun s => decide (s.ty = a.ty)) = some a := by
  have hnd : (ss.map (fun s => (s.ty).label)).Nodup := by
    simpa [SeqMS, List.map_map, Function.comp_def] using hseq
  cases hf : ss.find? (fun s => decide (s.ty = a.ty)) with
  | none =>
    have := List.find?_eq_none.mp hf a ha
    simp at this
  | some a' =>
    have ha' := List.mem_of_find?_eq_some hf
    have hty : a'.ty = a.ty := by simpa using List.find?_some hf
    have := List.inj_on_of_nodup_map hnd ha' ha (by rw [hty])
    rw [this]

/-- Every bag element chosen by the type of an occurrence ends up below that occurrence. -/
theorem subst_usage {b : LTerm} {b' : DTerm} (hr : Refines b b') :
    ∀ (k : ℕ) (ss : List DTerm) (τ : Ty) (a : DTerm) (r : Pos), τ ∈ b'.occTypes k →
      ss.find? (fun s => decide (s.ty = τ)) = some a →
      ∃ o ∈ occs b k, simRes a r ⊆ simRes (b'.subst k ss) (o ++ r) := by
  induction hr with
  | var n τ0 =>
    intro k ss τ a r hτ hf
    simp only [DTerm.occTypes] at hτ
    split_ifs at hτ with hn
    · have hτ' : τ = τ0 := by simpa using hτ
      subst hτ'; subst hn
      refine ⟨[], by simp [occs], ?_⟩
      simp [DTerm.subst, hf, simRes_shift]
    · simp at hτ
  | lam ℓ h ih =>
    intro k ss τ a r hτ hf
    simp only [DTerm.occTypes] at hτ
    obtain ⟨o, ho, hsub⟩ := ih (k + 1) ss τ a r hτ hf
    refine ⟨0 :: o, ?_, ?_⟩
    · simp only [occs, List.mem_map]; exact ⟨o, ho, rfl⟩
    · simp only [DTerm.subst, List.cons_append]
      rw [simRes_lam_zero]; exact hsub
  | @app t s f us ht hs iht ihs =>
    intro k ss τ a r hτ hf
    simp only [DTerm.occTypes, List.mem_append, List.mem_flatMap] at hτ
    rcases hτ with hτ | ⟨u, hu, hτ⟩
    · obtain ⟨o, ho, hsub⟩ := iht k ss τ a r hτ hf
      refine ⟨0 :: o, ?_, ?_⟩
      · simp only [occs, List.mem_append, List.mem_map]; exact Or.inl ⟨o, ho, rfl⟩
      · simp only [DTerm.subst, List.cons_append, simRes_app_zero]; exact hsub
    · obtain ⟨o, ho, hsub⟩ := ihs u hu k ss τ a r hτ hf
      refine ⟨1 :: o, ?_, ?_⟩
      · simp only [occs, List.mem_append, List.mem_map]; exact Or.inr ⟨o, ho, rfl⟩
      · intro ℓ hℓ
        simp only [DTerm.subst, List.cons_append]
        rw [show (1 : ℕ) = 0 + 1 from rfl, simRes_app_one]
        exact mem_fold_simRes.mpr ⟨u.subst k ss, List.mem_map_of_mem hu, hsub hℓ⟩

/-- Everything simulated below an occurrence comes from some bag element. -/
theorem subst_usage_sub {b : LTerm} {b' : DTerm} (hr : Refines b b') :
    ∀ (k : ℕ) (ss : List DTerm) (r : Pos), ∀ o ∈ occs b k, ∀ ℓ ∈ simRes (b'.subst k ss) (o ++ r),
      ∃ a ∈ ss, ℓ ∈ simRes a r := by
  induction hr with
  | var n τ0 =>
    intro k ss r o ho ℓ hℓ
    simp only [occs] at ho
    split_ifs at ho with hn
    · have : o = [] := by simpa using ho
      subst this; subst hn
      simp only [DTerm.subst, List.nil_append] at hℓ
      simp only [lt_self_iff_false, ↓reduceIte] at hℓ
      cases hf : ss.find? (fun s => decide (s.ty = τ0)) with
      | none => rw [hf] at hℓ; simp [simRes_var] at hℓ
      | some a =>
        rw [hf] at hℓ
        simp only [Option.map_some, Option.getD_some, simRes_shift] at hℓ
        exact ⟨a, List.mem_of_find?_eq_some hf, hℓ⟩
    · simp at ho
  | lam ℓ' h ih =>
    intro k ss r o ho ℓ hℓ
    simp only [occs, List.mem_map] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    simp only [DTerm.subst, List.cons_append] at hℓ
    rw [simRes_lam_zero] at hℓ
    exact ih (k + 1) ss r o' ho' ℓ hℓ
  | @app t s f us ht hs iht ihs =>
    intro k ss r o ho ℓ hℓ
    simp only [occs, List.mem_append, List.mem_map] at ho
    rcases ho with ⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩
    · simp only [DTerm.subst, List.cons_append, simRes_app_zero] at hℓ
      exact iht k ss r o' ho' ℓ hℓ
    · simp only [DTerm.subst, List.cons_append] at hℓ
      rw [show (1 : ℕ) = 0 + 1 from rfl, simRes_app_one] at hℓ
      obtain ⟨x, hx, hℓx⟩ := mem_fold_simRes.mp hℓ
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      exact ihs u hu k ss r o' ho' ℓ hℓx

/-- Root case of the cube lemma, redex inside the argument. -/
theorem cube_root_arg {b : LTerm} {b' : DTerm} {s : LTerm} {ss : List DTerm} {ℓ : Label}
    (hr : Refines b b') (hs : ∀ a ∈ ss, Refines s a)
    (hc : Correct (.app (.lam ℓ b') ss)) (r : Pos) :
    (ss.map (simRes · r)).foldr (· ∪ ·) ∅ =
      ((occs b 0).map (fun o => [] ++ o ++ r)).toFinset.biUnion (simRes (b'.subst 0 ss)) := by
  obtain ⟨hA, hseq⟩ := bag_types hc
  ext ℓ'
  rw [mem_fold_simRes, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hℓ⟩
    have hty : a.ty ∈ (b'.occTypes 0 : Multiset Ty) := by
      rw [← hA]; exact Multiset.mem_coe.mpr (List.mem_map_of_mem ha)
    obtain ⟨o, ho, hsub⟩ := subst_usage hr 0 ss a.ty a r (Multiset.mem_coe.mp hty)
      (find_ty_eq hseq ha)
    exact ⟨o ++ r, List.mem_toFinset.mpr (List.mem_map.mpr ⟨o, ho, by simp⟩), hsub hℓ⟩
  · rintro ⟨x, hx, hℓ⟩
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    simp only [List.nil_append] at hℓ
    exact subst_usage_sub hr 0 ss r o ho ℓ' hℓ

theorem fold_cube {p' : Pos} {X : Finset Pos} {ts us : List DTerm}
    (h : List.Forall₂ (fun a b => simRes a p' = X.biUnion (simRes b)) ts us) :
    (ts.map (simRes · p')).foldr (· ∪ ·) ∅ =
      X.biUnion (fun z => (us.map (simRes · z)).foldr (· ∪ ·) ∅) := by
  induction h with
  | nil => ext ℓ; simp
  | cons hab _ ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [hab, ih, ← Finset.biUnion_union]

/-- The cube property between a term, its refinement, the contracted position and the result. -/
def CubeProp (t : LTerm) (u : DTerm) (q : Pos) (v : DTerm) : Prop :=
  ∀ p, isRedexAt t p = true → p ≠ q → simRes u p = (residuals t q p).biUnion (simRes v)

theorem simRes_app_root (f : DTerm) (xs ys : List DTerm) :
    simRes (.app f xs) [] = simRes (.app f ys) [] := by
  cases f <;> simp [simRes]

theorem cube_root {b : LTerm} {s : LTerm} {b' : DTerm} {ss : List DTerm} {ℓ : Label}
    (hf : Refines b b') (hs : ∀ a ∈ ss, Refines s a)
    (hc : Correct (.app (.lam ℓ b') ss)) :
    CubeProp (.app (.lam b) s) (.app (.lam ℓ b') ss) [] (b'.subst 0 ss) := by
  intro p hp hne
  rcases p with _ | ⟨i, p⟩
  · exact absurd rfl hne
  rcases i with _ | _ | i
  · rcases p with _ | ⟨j, r⟩
    · simp [isRedexAt, subAt, isRedex] at hp
    rcases j with _ | j
    · simp only [isRedexAt_app_zero, isRedexAt_lam_zero] at hp
      have hres : residuals (.app (.lam b) s) [] (0 :: 0 :: r) = {r} := by
        simp [residuals, subAt]
      rw [hres, Finset.singleton_biUnion]
      rw [show (0 :: 0 :: r) = (0 :: (0 :: r)) from rfl, simRes_app_zero, simRes_lam_zero]
      exact (simRes_subst_redex hf r 0 ss hp).symm
    · simp at hp
  · replace hp : isRedexAt s p = true := by simpa using hp
    have hres : residuals (.app (.lam b) s) [] (1 :: p) =
        ((occs b 0).map (fun o => [] ++ o ++ p)).toFinset := by
      simp [residuals, subAt]
    rw [hres, show ((1 : ℕ) :: p) = (((0 : ℕ) + 1) :: p) from rfl, simRes_app_one]
    exact cube_root_arg hf hs hc p
  · simp at hp

theorem refines_lam_head {b : LTerm} {f : DTerm} (hf : Refines (.lam b) f) :
    ∃ ℓ f0, f = .lam ℓ f0 := by
  cases hf with
  | lam ℓ h => exact ⟨ℓ, _, rfl⟩

theorem isRedexAt_app_nil_lam {t1 s : LTerm} (h : isRedexAt (.app t1 s) [] = true) :
    ∃ b, t1 = .lam b := by
  cases t1 <;> simp_all [isRedexAt, subAt, isRedex]

theorem forall₂_right_mem {P : DTerm → Prop} {l : List DTerm} {l' : List DTerm}
    (h : List.Forall₂ (fun (_ : DTerm) b => P b) l l') : ∀ b ∈ l', P b := by
  induction h with
  | nil => simp
  | cons hab _ ih => intro b hb; rcases List.mem_cons.mp hb with rfl | hb; exact hab; exact ih b hb

/-- The constructive simulation trace also satisfies the cube equation (`08-16`). -/
theorem cube_trace {q : Pos} {t : LTerm} {u : DTerm}
    (hr : Refines t u) (hc : Correct u) (hq : isRedexAt t q = true) :
    ∃ v σ, DTrace u σ v ∧ σ.toFinset = simRes u q ∧ Refines (contractAt t q) v ∧
      (∀ ℓ u0, u = .lam ℓ u0 → ∃ v0, v = .lam ℓ v0) ∧ CubeProp t u q v := by
  induction q generalizing t u with
  | nil =>
    cases t with
    | var => simp [isRedexAt, subAt, isRedex] at hq
    | lam => simp [isRedexAt, subAt, isRedex] at hq
    | app t s =>
      cases t with
      | var => simp [isRedexAt, subAt, isRedex] at hq
      | app => simp [isRedexAt, subAt, isRedex] at hq
      | lam b =>
        cases hr with
        | app hf hs =>
          cases hf with
          | lam ℓ hf =>
            exact ⟨_, [ℓ], .cons (.beta ℓ _ _) (.nil _), by simp [simRes],
              refinement_substitution hf hs hc, (by intro ℓ' u0 h; cases h),
              cube_root hf hs hc⟩
  | cons i q ih =>
    cases t with
    | var => simp [isRedexAt, subAt] at hq
    | lam t0 =>
      cases i with
      | succ i => simp [isRedexAt, subAt] at hq
      | zero =>
        cases hr with
        | lam ℓ hr0 =>
          obtain ⟨v, σ, ht, he, hv, hlam, hcube⟩ := ih hr0 (hc.sub (.lam ℓ (.refl _)))
            (by simpa [isRedexAt, subAt] using hq)
          refine ⟨.lam ℓ v, σ, ht.plug (.lam ℓ .hole), he, .lam ℓ hv, ?_, ?_⟩
          · intro ℓ' u0' h; cases h; exact ⟨v, rfl⟩
          · intro p hp hne
            rcases p with _ | ⟨j, p⟩
            · simp [isRedexAt, subAt, isRedex] at hp
            rcases j with _ | j
            · replace hp : isRedexAt t0 p = true := by simpa using hp
              have hne' : p ≠ q := fun h => hne (by rw [h])
              rw [simRes_lam_zero, ctx_lam.residuals_in t0 q p, Finset.image_biUnion]
              simp only [simRes_lam_zero]
              exact hcube p hp hne'
            · simp at hp
    | app t1 s =>
      cases hr with
      | @app _ _ f ss hf hs =>
        cases i with
        | zero =>
          obtain ⟨v, σ, ht, he, hv, hlam, hcube⟩ := ih hf (hc.sub (.fn ss (.refl _)))
            (by simpa [isRedexAt, subAt] using hq)
          refine ⟨.app v ss, σ, ht.plug (.appL .hole ss), by simpa using he,
            by simpa only [LTerm.contractAt_app_zero] using Refines.app hv hs, ?_, ?_⟩
          · intro ℓ' u0 h; cases h
          · intro p hp hne
            rcases p with _ | ⟨j, p⟩
            · have hres : residuals (.app t1 s) (0 :: q) [] = {[]} :=
                LTerm.Ctx.residuals_out (C := fun t => LTerm.app t s) (i := 0) _ _ _ (by intro p'; simp)
              rw [hres, Finset.singleton_biUnion]
              obtain ⟨b, rfl⟩ := isRedexAt_app_nil_lam hp
              obtain ⟨ℓ', f0, rfl⟩ := refines_lam_head hf
              obtain ⟨v0, rfl⟩ := hlam ℓ' f0 rfl
              simp [simRes]
            rcases j with _ | _ | j
            · replace hp : isRedexAt t1 p = true := by simpa using hp
              have hne' : p ≠ q := fun h => hne (by rw [h])
              rw [simRes_app_zero, (ctx_appL s).residuals_in t1 q p, Finset.image_biUnion]
              simp only [simRes_app_zero]
              exact hcube p hp hne'
            · have hres : residuals (.app t1 s) (0 :: q) (1 :: p) = {1 :: p} :=
                LTerm.Ctx.residuals_out (C := fun t => LTerm.app t s) (i := 0) _ _ _ (by intro p'; simp)
              rw [hres, Finset.singleton_biUnion]
              rw [show ((1 : ℕ) :: p) = (((0 : ℕ) + 1) :: p) from rfl, simRes_app_one, simRes_app_one]
            · simp at hp
        | succ i =>
          cases i with
          | succ i => simp [isRedexAt, subAt] at hq
          | zero =>
            have hp' : isRedexAt s q = true := by simpa [isRedexAt, subAt] using hq
            have work : ∀ ts pre : List DTerm, (∀ a ∈ ts, Refines s a) →
                (∀ a ∈ ts, Correct a) → ∃ us σ,
                DTrace (.app f (pre ++ ts)) σ (.app f (pre ++ us)) ∧
                σ.toFinset = (ts.map (simRes · q)).foldr (· ∪ ·) ∅ ∧
                List.Forall₂ (fun a b => Refines (contractAt s q) b ∧ CubeProp s a q b) ts us := by
              intro ts
              induction ts with
              | nil => intro pre _ _; exact ⟨[], [], .nil _, rfl, .nil⟩
              | cons a ts iht =>
                intro pre hr hc
                obtain ⟨b, σ, ht, he, hb, _, hcb⟩ := ih (hr a (by simp)) (hc a (by simp)) hp'
                obtain ⟨bs, τ, htt, het, hbs⟩ := iht (pre ++ [b])
                  (fun a ha => hr a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
                simp only [List.append_assoc, List.singleton_append] at htt
                exact ⟨b :: bs, σ ++ τ, (ht.plug (.appR f pre .hole ts)).append htt,
                  by simp [he, het], .cons ⟨hb, hcb⟩ hbs⟩
            obtain ⟨us, σ, ht, he, hF⟩ := work ss [] hs
              (fun a ha => hc.sub (.arg f ha (.refl a)))
            have hus : ∀ a ∈ us, Refines (contractAt s q) a :=
              forall₂_right_mem (hF.imp (fun a b h => h.1))
            refine ⟨.app f us, σ, ht, by simpa using he,
              by simpa only [Nat.zero_add, LTerm.contractAt_app_one] using Refines.app hf hus,
              ?_, ?_⟩
            · intro ℓ' u0 h; cases h
            · intro p hp hne
              rcases p with _ | ⟨j, p⟩
              · have hres : residuals (.app t1 s) (1 :: q) [] = {[]} :=
                  LTerm.Ctx.residuals_out (C := fun x => LTerm.app t1 x) (i := 1) _ _ _ (by intro p'; simp)
                rw [hres, Finset.singleton_biUnion]
                exact simRes_app_root f ss us
              rcases j with _ | _ | j
              · have hres : residuals (.app t1 s) (1 :: q) (0 :: p) = {0 :: p} :=
                  LTerm.Ctx.residuals_out (C := fun x => LTerm.app t1 x) (i := 1) _ _ _ (by intro p'; simp)
                rw [hres, Finset.singleton_biUnion]
                simp only [simRes_app_zero]
              · replace hp : isRedexAt s p = true := by simpa using hp
                have hne' : p ≠ q := fun h => hne (by rw [h])
                rw [(ctx_appR t1).residuals_in s q p, Finset.image_biUnion]
                rw [show ((1 : ℕ) :: p) = (((0 : ℕ) + 1) :: p) from rfl, simRes_app_one]
                have hF' := hF.imp (fun a b hab => hab.2 p hp hne')
                rw [fold_cube hF']
                apply Finset.biUnion_congr rfl
                intro z _
                rw [show (((0 : ℕ) + 1) :: z) = ((1 : ℕ) :: z) from rfl, simRes_app_one]
              · simp at hp

/-- The constructive trace reaches the canonical simulation residual. -/
theorem simTgt_eq_trace {u : CTerm} {q : Pos} {v : DTerm} {σ : List Label}
    (ht : DTrace u.1 σ v) (he : σ.toFinset = simRes u.1 q) : (simTgt u q).1 = v := by
  obtain ⟨hσ, htarget⟩ := ht.specification u.2
  have hm : ∀ m ∈ simRes u.1 q, distRS.isStep u m := fun m hm => simRes_isStep hm
  have hd := (distRS.orthogonal.dev_complete u _ hm).1.valid
  have hn : distRS.names (distRS.dev u (simRes u.1 q)) = distRS.names σ := by
    simpa only [distRS, distRS.names, Finset.sort_toFinset] using he.symm
  have eq := ResidualSystem.tgt_eq_of_permEq distRS.orthogonal hd hσ
    ((distRS.permEq_iff_names hd hσ).2 hn)
  change (distRS.tgt u (distRS.dev u (simRes u.1 q))).1 = v
  rw [eq]
  exact htarget

end Thesis
