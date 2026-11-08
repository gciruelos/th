/-
# Chapter 2: A distributive λ-calculus (λ^dist) — Appendix

Auxiliary definitions and lemmas for Chapter 2:
* Structural induction `DTerm.ind`, type sequentiality `Ty.Sequential`, context operations
  (`Ctx.shift`, `Ctx.remove`, `Ctx.insert`).
* Unconditional syntactic typing determination (`hasType_ty`, `hasType_ctx`, `hasType_unique`).
* Partition-based substitution properties (`PSubst.exists`, `PSubst.occTypes`, `PSubst.inverse`),
  typing subject expansion (`subject_expansion`, `subject_expansion_subst`,
  `subject_expansion_typeDirected`), and counterexamples.
* Forward substitution typing and correctness, lambda conservation and size bounds.
* Substitution commutation and strong permutation, following the Chapter 2 appendices.
* Reduction/context correspondence and determinism by label.
-/
import Thesis.Chapter2DistLambdaCalcDefs

namespace Thesis

namespace Ty

/-- Every arrow domain occurring anywhere in this type is sequential. This does not
require all arrow labels in the type to be globally distinct. -/
def Sequential (τ : Ty) : Prop :=
  ∀ M ℓ ρ, Occurs (.arrow M ℓ ρ) τ → SeqMS (M : Multiset Ty)

theorem sequential_base (α : ℕ) (ℓ : Label) : Sequential (.base α ℓ) := by
  intro M m ρ h
  cases h

theorem Sequential.arrow {M : List Ty} {ℓ : Label} {ρ : Ty}
    (hM : SeqMS (M : Multiset Ty)) (hdom : ∀ τ ∈ M, Sequential τ)
    (hcod : Sequential ρ) : Sequential (.arrow M ℓ ρ) := by
  intro N m σ h
  cases h with
  | refl => exact hM
  | dom hm h => exact hdom _ hm _ _ _ h
  | cod h => exact hcod _ _ _ h

theorem Sequential.cod {M : List Ty} {ℓ : Label} {ρ : Ty}
    (h : Sequential (.arrow M ℓ ρ)) : Sequential ρ := by
  intro N m σ ho
  exact h _ _ _ (.cod ho)

end Ty

namespace Ctx

/-- Shift a context along the same insertion of indices as `DTerm.shift`. -/
def shift (d c : ℕ) (Γ : Ctx) : Ctx := fun n =>
  if n < c then Γ n else if n < c + d then 0 else Γ (n - d)

/-- Delete the variable at index `k`. -/
def remove (k : ℕ) (Γ : Ctx) : Ctx := fun n =>
  if n < k then Γ n else Γ (n + 1)

/-- Insert a variable with multiset `M` at index `k`. -/
def insert (k : ℕ) (M : Multiset Ty) (Γ : Ctx) : Ctx := fun n =>
  if n < k then Γ n else if n = k then M else Γ (n - 1)

@[simp] theorem shift_zero (d c : ℕ) : shift d c 0 = 0 := by
  funext n; simp [shift]

@[simp] theorem shift_add (d c : ℕ) (Γ Δ : Ctx) :
    shift d c (Γ + Δ) = shift d c Γ + shift d c Δ := by
  funext n; simp only [shift, Pi.add_apply]; split <;> simp_all
  split <;> simp_all

@[simp] theorem shift_sum (d c : ℕ) (Γs : List Ctx) :
    shift d c Γs.sum = (Γs.map (shift d c)).sum := by
  induction Γs with
  | nil => simp
  | cons Γ Γs ih => simp [ih]

@[simp] theorem shift_cons (d c : ℕ) (M : Multiset Ty) (Γ : Ctx) :
    shift d (c + 1) (cons M Γ) = cons M (shift d c Γ) := by
  funext n
  cases n with
  | zero => simp [shift, cons]
  | succ n =>
    simp only [shift, cons, Nat.add_lt_add_iff_right]
    split <;> rename_i h
    · simp
    · split <;> rename_i h'
      · simp [show n < c + d by omega]
      · have he : n + 1 - d = (n - d) + 1 := by omega
        simp [show ¬ n < c + d by omega, he]

@[simp] theorem shift_single (d c n : ℕ) (M : Multiset Ty) :
    shift d c (single n M) = single (if n < c then n else n + d) M := by
  funext m
  simp only [shift, single]
  split_ifs <;> first | rfl | omega

@[simp] theorem shift_succ_zero (k : ℕ) (Γ : Ctx) :
    shift (k + 1) 0 Γ = cons 0 (shift k 0 Γ) := by
  funext n
  cases n with
  | zero => simp [shift, cons]
  | succ n => simp [shift, cons, Nat.succ_sub_succ_eq_sub]

@[simp] theorem remove_zero (k : ℕ) : remove k 0 = 0 := by
  funext n; simp [remove]

@[simp] theorem remove_add (k : ℕ) (Γ Δ : Ctx) :
    remove k (Γ + Δ) = remove k Γ + remove k Δ := by
  funext n; simp [remove]; split <;> rfl

@[simp] theorem insert_remove (k : ℕ) (Γ : Ctx) : insert k (Γ k) (remove k Γ) = Γ := by
  funext n
  simp only [insert, remove]
  split <;> rename_i h
  · rfl
  · split <;> rename_i h'
    · subst n; rfl
    · have : n - 1 + 1 = n := by omega
      simp [show ¬ n - 1 < k by omega, this]

@[simp] theorem insert_zero (M : Multiset Ty) (Γ : Ctx) : insert 0 M Γ = cons M Γ := by
  funext n; cases n <;> simp [insert, cons]

@[simp] theorem shift_zero_cutoff (Γ : Ctx) : shift 0 0 Γ = Γ := by
  funext n; simp [shift]

@[simp] theorem remove_cons (k : ℕ) (M : Multiset Ty) (Γ : Ctx) :
    remove (k + 1) (cons M Γ) = cons M (remove k Γ) := by
  funext n; cases n <;> simp [remove, cons]

@[simp] theorem cons_add (M N : Multiset Ty) (Γ Δ : Ctx) :
    cons M Γ + cons N Δ = cons (M + N) (Γ + Δ) := by
  funext n; cases n <;> rfl

@[simp] theorem cons_zero : cons 0 0 = 0 := by
  funext n; cases n <;> rfl

@[simp] theorem remove_single (k n : ℕ) (M : Multiset Ty) (h : n ≠ k) :
    remove k (single n M) = single (if n < k then n else n - 1) M := by
  funext m
  simp only [remove, single]
  split <;> split <;> split <;> simp_all <;> omega

end Ctx

namespace DTerm

/-- Induction principle for `DTerm` (which is nested through `List`). -/
@[elab_as_elim]
theorem ind {P : DTerm → Prop}
    (var : ∀ n τ, P (.var n τ)) (lam : ∀ ℓ t, P t → P (.lam ℓ t))
    (app : ∀ t ss, P t → (∀ s ∈ ss, P s) → P (.app t ss)) : ∀ t, P t := by
  intro t
  induction t using DTerm.rec (motive_2 := fun ss => ∀ s ∈ ss, P s) with
  | var n τ => exact var n τ
  | lam ℓ t ih => exact lam ℓ t ih
  | app t ss ih ihs => exact app t ss ih ihs
  | nil => simp_all
  | cons s ss ih ihs =>
    rename_i x hx
    rcases List.mem_cons.1 hx with rfl | hx
    exacts [ih, ihs x hx]

end DTerm

/-! ### Unconditional typing determination -/

/-- For any typable term (without correctness assumptions), the context records the free
occurrence types of each variable. -/
theorem hasType_occTypes {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ) (n : ℕ) :
    Γ n = (t.occTypes n : Multiset Ty) := by
  induction h using HasType.rec
    (motive_2 := fun Δs ts _ _ => ∀ n, Δs.sum n = ((ts.flatMap (DTerm.occTypes · n) : List Ty) : Multiset Ty))
    generalizing n with
  | var m σ =>
    simp only [Ctx.single, DTerm.occTypes]
    by_cases h : n = m
    · subst h; simp
    · simp [h, Ne.symm h]
  | lam ℓ _ ih => simpa [Ctx.cons, DTerm.occTypes] using ih (n + 1)
  | app _ _ _ ih ihs =>
    simp only [Pi.add_apply, DTerm.occTypes, ← Multiset.coe_add, ih n, ihs n]
  | nil => simp
  | cons _ _ ih ihs =>
    rename_i m
    simp [List.sum_cons, Pi.add_apply, ih m, ihs m]

/-- Every typing derivation gives the syntactically determined type. -/
theorem hasType_ty {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ) :
    τ = t.ty := by
  induction h using HasType.rec (motive_2 := fun _ _ _ _ => True) with
  | var => rfl
  | @lam Γ M σ t ℓ h ih =>
    have hm := hasType_occTypes h 0
    change M = _ at hm
    simp only [DTerm.ty, ← ih, ← hm]
  | app _ _ _ ih _ => simp [DTerm.ty, ← ih]
  | nil => trivial
  | cons => trivial

/-- Every typing derivation gives the syntactically determined context. -/
theorem hasType_ctx {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ) :
    Γ = t.ctx := funext (hasType_occTypes h)

/-- Typing is unique even without correctness. -/
theorem hasType_unique {Γ Γ' : Ctx} {t : DTerm} {τ τ' : Ty}
    (h : HasType Γ t τ) (h' : HasType Γ' t τ') : Γ = Γ' ∧ τ = τ' :=
  ⟨(hasType_ctx h).trans (hasType_ctx h').symm,
   (hasType_ty h).trans (hasType_ty h').symm⟩

/-- The computed type and context are those of the (unique) typing derivation. -/
theorem hasType_iff {Γ : Ctx} {t : DTerm} {τ : Ty} (ht : Correct t) :
    HasType Γ t τ ↔ Γ = t.ctx ∧ τ = t.ty := by
  constructor
  · intro h
    exact ⟨hasType_ctx h, hasType_ty h⟩
  · rintro ⟨rfl, rfl⟩
    obtain ⟨Δ, σ, h⟩ := ht.typable
    simpa only [hasType_ctx h, hasType_ty h] using h

namespace Ctx

/-- All types in a context have sequential arrow domains. -/
def TypesSequential (Γ : Ctx) : Prop := ∀ n τ, τ ∈ Γ n → τ.Sequential

theorem TypesSequential.add {Γ Δ : Ctx} (hΓ : Γ.TypesSequential)
    (hΔ : Δ.TypesSequential) : (Γ + Δ).TypesSequential := by
  intro n τ hm
  rcases Multiset.mem_add.mp hm with hm | hm
  · exact hΓ n τ hm
  · exact hΔ n τ hm

theorem typesSequential_zero : TypesSequential 0 := by simp [TypesSequential]

end Ctx

namespace Correct

theorem type_sequential {t : DTerm} (h : Correct t) {Γ : Ctx} {τ : Ty}
    (ht : HasType Γ t τ) : τ.Sequential := by
  intro M ℓ ρ ho
  exact h.seq_ty t Γ τ (.refl t) ht M ℓ ρ (.inr ho)

theorem context_typesSequential {t : DTerm} (h : Correct t) {Γ : Ctx} {τ : Ty}
    (ht : HasType Γ t τ) : Γ.TypesSequential := by
  intro n σ hm M ℓ ρ ho
  exact h.seq_ty t Γ τ (.refl t) ht M ℓ ρ (.inl ⟨n, σ, hm, ho⟩)

/-- A variable is correct exactly as far as the sequentiality of its annotated type allows. -/
theorem var (n : ℕ) {τ : Ty} (hτ : τ.Sequential) : Correct (.var n τ) := by
  refine ⟨⟨_, _, .var n τ⟩, by simp [DTerm.lamLabels], ?_, ?_⟩
  · intro s Γ σ hsub ht k
    cases hsub
    cases ht
    simp only [Ctx.single]
    split <;> simp [SeqMS]
  · intro s Γ σ hsub ht M ℓ ρ ho
    cases hsub
    cases ht
    rcases ho with ⟨k, υ, hm, ho⟩ | ho
    · by_cases hk : k = n
      · simp [Ctx.single, hk] at hm
        subst υ
        exact hτ M ℓ ρ ho
      · simp [Ctx.single, hk] at hm
    · exact hτ M ℓ ρ ho

end Correct

theorem HasTypeMulti.context_typesSequential {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) (hc : ∀ s ∈ ss, Correct s) : Γs.sum.TypesSequential := by
  induction ss generalizing Γs σs with
  | nil => cases hs; exact Ctx.typesSequential_zero
  | cons s ss ih =>
    cases hs with
    | cons h hs =>
      exact (hc s (by simp)).context_typesSequential h |>.add
        (ih hs (fun t ht => hc t (by simp [ht])))

/-- Correctness of an application follows from correct children, distinct lambda labels,
and sequentiality of the combined context. -/
theorem Correct.app {t : DTerm} {ss : List DTerm} {Γ : Ctx} {Δs : List Ctx}
    {L σs : List Ty} {ℓ : Label} {τ : Ty}
    (ht : HasType Γ t (.arrow L ℓ τ)) (hs : HasTypeMulti Δs ss σs) (hp : σs.Perm L)
    (hc : Correct t) (hcs : ∀ s ∈ ss, Correct s)
    (hlabels : (DTerm.app t ss).lamLabels.Nodup) (hctx : (Γ + Δs.sum).Seq) :
    Correct (.app t ss) := by
  have ha := HasType.app ht hs hp
  have hty := (hc.type_sequential ht).cod
  have hcts := (hc.context_typesSequential ht).add (hs.context_typesSequential hcs)
  refine ⟨⟨_, _, ha⟩, hlabels, ?_, ?_⟩
  · intro s Δ σ hsub h
    cases hsub with
    | refl => exact (hasType_unique h ha).1 ▸ hctx
    | fn _ hsub => exact hc.seq_ctx s Δ σ hsub h
    | arg _ hm hsub => exact (hcs _ hm).seq_ctx s Δ σ hsub h
  · intro s Δ σ hsub h M m ρ ho
    cases hsub with
    | refl =>
      obtain ⟨rfl, rfl⟩ := hasType_unique h ha
      rcases ho with ⟨n, υ, hm, ho⟩ | ho
      · exact hcts n υ hm M m ρ ho
      · exact hty M m ρ ho
    | fn _ hsub => exact hc.seq_ty s Δ σ hsub h M m ρ ho
    | arg _ hm hsub => exact (hcs _ hm).seq_ty s Δ σ hsub h M m ρ ho

namespace DTerm.Sub

theorem trans {s t u : DTerm} (hs : Sub s t) (ht : Sub t u) : Sub s u := by
  induction ht with
  | refl => exact hs
  | lam ℓ _ ih => exact .lam ℓ ih
  | fn ss _ ih => exact .fn ss ih
  | arg t hm _ ih => exact .arg t hm ih

theorem labels_arg {s : DTerm} {ss : List DTerm} (hm : s ∈ ss) :
    s.lamLabels.Sublist (ss.flatMap DTerm.lamLabels) := by
  induction ss with
  | nil => simp at hm
  | cons a ss ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.sublist_append_left _ _
    · exact (ih hm).trans (List.sublist_append_right _ _)

theorem lamLabels_sublist {s t : DTerm} (hs : Sub s t) :
    s.lamLabels.Sublist t.lamLabels := by
  induction hs with
  | refl => exact .refl _
  | lam ℓ _ ih => simpa only [DTerm.lamLabels] using ih.cons ℓ
  | fn ss _ ih => simpa only [DTerm.lamLabels] using ih.trans (List.sublist_append_left _ _)
  | arg t hm _ ih =>
    simpa only [DTerm.lamLabels] using
      ih.trans ((labels_arg hm).trans (List.sublist_append_right _ _))

end DTerm.Sub

theorem HasTypeMulti.typable_of_mem {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) {s : DTerm} (hm : s ∈ ss) : s.Typable := by
  induction ss generalizing Γs σs with
  | nil => simp at hm
  | cons t ss ih =>
    cases hs with
    | cons ht hs =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, _, ht⟩
      · exact ih hs hm

theorem DTerm.Sub.typable {s t : DTerm} (hs : Sub s t) (ht : t.Typable) : s.Typable := by
  induction hs with
  | refl => exact ht
  | lam ℓ _ ih =>
    obtain ⟨Γ, τ, h⟩ := ht
    cases h with
    | lam _ h => exact ih ⟨_, _, h⟩
  | fn ss _ ih =>
    obtain ⟨Γ, τ, h⟩ := ht
    cases h with
    | app h _ _ => exact ih ⟨_, _, h⟩
  | arg t hm _ ih =>
    obtain ⟨Γ, τ, h⟩ := ht
    cases h with
    | app _ hs _ => exact ih (hs.typable_of_mem hm)

theorem Correct.sub {s t : DTerm} (ht : Correct t) (hs : DTerm.Sub s t) : Correct s where
  typable := hs.typable ht.typable
  uniquely_labeled := hs.lamLabels_sublist.nodup ht.uniquely_labeled
  seq_ctx u Γ τ hu h := ht.seq_ctx u Γ τ (hu.trans hs) h
  seq_ty u Γ τ hu h M ℓ ρ ho := ht.seq_ty u Γ τ (hu.trans hs) h M ℓ ρ ho

/-! ### Shifting, partitioning, and typing subject expansion -/

/-- Typing is preserved by shifting free variables. -/
theorem HasType.shift {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ)
    (d c : ℕ) : HasType (Γ.shift d c) (t.shift d c) τ := by
  induction h using HasType.rec
    (motive_2 := fun Δs ts σs _ => ∀ c,
      HasTypeMulti (Δs.map (Ctx.shift d c)) (ts.map (DTerm.shift d c)) σs)
    generalizing c with
  | var n τ =>
    simp only [DTerm.shift, Ctx.shift_single]
    split <;> exact HasType.var _ _
  | lam ℓ _ ih =>
    simpa only [DTerm.shift] using
      HasType.lam ℓ (by simpa only [Ctx.shift_cons] using ih (c + 1))
  | app _ _ hp ih ihs =>
    simpa only [DTerm.shift, Ctx.shift_add, Ctx.shift_sum] using
      HasType.app (ih c) (ihs c) hp
  | nil => exact HasTypeMulti.nil
  | cons _ _ ih ihs =>
    rename_i c
    exact HasTypeMulti.cons (ih c) (ihs c)

namespace HasTypeMulti

theorem append {Γs Δs : List Ctx} {ts ss : List DTerm} {τs σs : List Ty}
    (ht : HasTypeMulti Γs ts τs) (hs : HasTypeMulti Δs ss σs) :
    HasTypeMulti (Γs ++ Δs) (ts ++ ss) (τs ++ σs) := by
  induction ts generalizing Γs τs with
  | nil => cases ht; exact hs
  | cons t ts ih =>
    cases ht with
    | cons h ht => exact .cons h (ih ht)

/-- Reordering arguments also reorders their contexts and types. -/
theorem perm {Γs : List Ctx} {ts ss : List DTerm} {τs : List Ty}
    (ht : HasTypeMulti Γs ts τs) (hp : ts.Perm ss) :
    ∃ Δs σs, HasTypeMulti Δs ss σs ∧ Δs.Perm Γs ∧ σs.Perm τs := by
  induction hp generalizing Γs τs with
  | nil =>
    cases ht
    exact ⟨[], [], .nil, .nil, .nil⟩
  | cons t hp ih =>
    cases ht with
    | cons h hs =>
      obtain ⟨Δs, σs, h', hΔ, hσ⟩ := ih hs
      exact ⟨_ :: Δs, _ :: σs, .cons h h', hΔ.cons _, hσ.cons _⟩
  | swap t s ts =>
    cases ht with
    | cons h hs =>
      cases hs with
      | cons h' hs => exact ⟨_, _, .cons h' (.cons h hs), .swap .., .swap ..⟩
  | trans hp hp' ih ih' =>
    obtain ⟨Δs, σs, h, hΔ, hσ⟩ := ih ht
    obtain ⟨Ξs, ρs, h', hΞ, hρ⟩ := ih' h
    exact ⟨Ξs, ρs, h', hΞ.trans hΔ, hρ.trans hσ⟩

/-- The type list of a typed list is determined by its terms. -/
theorem types_eq {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) : σs = ss.map DTerm.ty := by
  induction ss generalizing Γs σs with
  | nil => cases hs; rfl
  | cons s ss ih =>
    cases hs with
    | cons h hs => simp only [List.map_cons, ← hasType_ty h, ← ih hs]

theorem perm_types {Γs : List Ctx} {ss : List DTerm} {σs τs : List Ty}
    (hs : HasTypeMulti Γs ss σs) (hp : σs.Perm τs) :
    ∃ Δs ts, HasTypeMulti Δs ts τs ∧ Δs.Perm Γs ∧ ts.Perm ss := by
  induction hp generalizing Γs ss with
  | nil => cases hs; exact ⟨[], [], .nil, .nil, .nil⟩
  | cons τ hp ih =>
    cases hs with
    | cons h hs =>
      obtain ⟨Δs, ts, h', hΔ, hts⟩ := ih hs
      exact ⟨_ :: Δs, _ :: ts, .cons h h', hΔ.cons _, hts.cons _⟩
  | swap σ τ τs =>
    cases hs with
    | cons h hs =>
      cases hs with
      | cons h' hs => exact ⟨_, _, .cons h' (.cons h hs), .swap .., .swap ..⟩
  | trans hp hp' ih ih' =>
    obtain ⟨Δs, ts, h, hΔ, hts⟩ := ih hs
    obtain ⟨Ξs, us, h', hΞ, hus⟩ := ih' h
    exact ⟨Ξs, us, h', hΞ.trans hΔ, hus.trans hts⟩

theorem split_types {Γs : List Ctx} {ss : List DTerm} (σs τs : List Ty)
    (hs : HasTypeMulti Γs ss (σs ++ τs)) :
    ∃ Γs₀ Γs₁ ss₀ ss₁, Γs = Γs₀ ++ Γs₁ ∧ ss = ss₀ ++ ss₁ ∧
      HasTypeMulti Γs₀ ss₀ σs ∧ HasTypeMulti Γs₁ ss₁ τs := by
  induction σs generalizing Γs ss with
  | nil => exact ⟨[], Γs, [], ss, rfl, rfl, .nil, hs⟩
  | cons σ σs ih =>
    cases hs with
    | cons h hs =>
      obtain ⟨Γs₀, Γs₁, ss₀, ss₁, rfl, rfl, h₀, h₁⟩ := ih hs
      exact ⟨_ :: Γs₀, Γs₁, _ :: ss₀, ss₁, rfl, rfl, .cons h h₀, h₁⟩

/-- Split resources by a multiset equation, without assuming distinct argument types. -/
theorem partition {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) (M N : Multiset Ty) (hm : (σs : Multiset Ty) = M + N) :
    ∃ Γs₀ Γs₁ ss₀ ss₁, HasTypeMulti Γs₀ ss₀ (Ty.canon M) ∧
      HasTypeMulti Γs₁ ss₁ (Ty.canon N) ∧ (Γs₀ ++ Γs₁).Perm Γs ∧ (ss₀ ++ ss₁).Perm ss := by
  have hp : σs.Perm ((Ty.canon M) ++ (Ty.canon N)) :=
    Multiset.coe_eq_coe.mp (by simpa only [← Multiset.coe_add, Ty.coe_canon] using hm)
  obtain ⟨Δs, ts, h, hΔ, hts⟩ := hs.perm_types hp
  obtain ⟨Γs₀, Γs₁, ss₀, ss₁, rfl, rfl, h₀, h₁⟩ := h.split_types (Ty.canon M) (Ty.canon N)
  exact ⟨Γs₀, Γs₁, ss₀, ss₁, h₀, h₁, hΔ, hts⟩

/-- A replacement preserving every typing can be made at any position of a typed list. -/
theorem replace {u v : DTerm}
    (h : ∀ {Γ τ}, HasType Γ u τ → HasType Γ v τ)
    {Γs : List Ctx} {τs : List Ty} (us vs : List DTerm)
    (ht : HasTypeMulti Γs (us ++ u :: vs) τs) :
    HasTypeMulti Γs (us ++ v :: vs) τs := by
  induction us generalizing Γs τs with
  | nil =>
    cases ht with
    | cons hu hs => exact .cons (h hu) hs
  | cons t ts ih =>
    cases ht with
    | cons ht hs => exact .cons ht (ih hs)

end HasTypeMulti

/-- Exact occurrence matching and typable arguments suffice to construct a partition
substitution on raw terms. Correctness of the body is not assumed or smuggled into this
construction: it must be established separately when needed. -/
theorem PSubst.exists {t : DTerm} {k : ℕ} {Δs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Δs ss σs)
    (hm : (σs : Multiset Ty) = (t.occTypes k : Multiset Ty)) :
    ∃ u, PSubst t k ss u := by
  induction t using DTerm.rec
    (motive_2 := fun ts => ∀ k {Δs ss σs}, HasTypeMulti Δs ss σs →
      (σs : Multiset Ty) = (ts.flatMap (DTerm.occTypes · k) : Multiset Ty) →
      ∃ us ss', PSubstMulti ts k ss' us ∧ ss'.Perm ss)
    generalizing k Δs ss σs with
  | var n τ =>
    by_cases hn : n = k
    · subst n
      have hσ : σs = [τ] := List.perm_singleton.mp
        (Multiset.coe_eq_coe.mp (by simpa [DTerm.occTypes] using hm))
      subst σs
      cases hs with
      | cons h hs =>
        cases hs
        exact ⟨_, .var_eq k h⟩
    · have hσ : σs = [] := by simpa [DTerm.occTypes, hn] using hm
      subst σs
      cases hs
      by_cases hlt : n < k
      · exact ⟨_, .var_lt τ hlt⟩
      · exact ⟨_, .var_gt τ (by omega)⟩
  | lam ℓ t ih =>
    obtain ⟨u, h⟩ := ih hs (by simpa only [DTerm.occTypes] using hm)
    exact ⟨_, .lam ℓ h⟩
  | app t ts ih ihs =>
    obtain ⟨Δs₀, Δs₁, ss₀, ss₁, h₀, h₁, _, hp⟩ := hs.partition
      (t.occTypes k : Multiset Ty) (ts.flatMap (DTerm.occTypes · k) : Multiset Ty)
      (by simpa only [DTerm.occTypes, ← Multiset.coe_add] using hm)
    obtain ⟨u, hu⟩ := ih h₀ (Ty.coe_canon _)
    obtain ⟨us, ss₁', hus, hperm⟩ := ihs k h₁ (Ty.coe_canon _)
    exact ⟨_, .app hu hus (((List.Perm.refl ss₀).append hperm).trans hp)⟩
  | nil =>
    rename_i k Δs ss σs hs hm
    have hσ : σs = [] := by simpa using hm
    subst σs
    cases hs
    exact ⟨[], [], .nil k, .nil⟩
  | cons t ts ih ihs =>
    rename_i k Δs ss σs hs hm
    obtain ⟨Δs₀, Δs₁, ss₀, ss₁, h₀, h₁, _, hp⟩ := hs.partition
      (t.occTypes k : Multiset Ty) (ts.flatMap (DTerm.occTypes · k) : Multiset Ty)
      (by simpa only [List.flatMap_cons, ← Multiset.coe_add] using hm)
    obtain ⟨u, hu⟩ := ih h₀ (Ty.coe_canon _)
    obtain ⟨us, ss₁', hus, hperm⟩ := ihs k h₁ (Ty.coe_canon _)
    exact ⟨_, _, .cons hu hus, ((List.Perm.refl ss₀).append hperm).trans hp⟩

/-- The substitution relation enforces the thesis' implicit resource-matching condition. -/
theorem PSubst.occTypes {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) :
    (t.occTypes k : Multiset Ty) = (ss.map DTerm.ty : Multiset Ty) := by
  induction h using PSubst.rec
    (motive_2 := fun ts k ss _ _ =>
      (ts.flatMap (DTerm.occTypes · k) : Multiset Ty) = (ss.map DTerm.ty : Multiset Ty)) with
  | var_eq k hs => simp [DTerm.occTypes, ← hasType_ty hs]
  | var_lt τ h => simp [DTerm.occTypes, Nat.ne_of_lt h]
  | var_gt τ h => simp [DTerm.occTypes, Ne.symm (Nat.ne_of_lt h)]
  | lam _ _ ih => simpa only [DTerm.occTypes] using ih
  | app _ _ hp ih ihs =>
    simp only [DTerm.occTypes, ← Multiset.coe_add, ih, ihs]
    exact Multiset.coe_eq_coe.mpr (by simpa using hp.map DTerm.ty)
  | nil => rfl
  | cons _ _ ih ihs => simp [← Multiset.coe_add, ih, ihs]

/-- Inverting a partition substitution reconstructs the body's typing and all consumed
arguments, with an exact decomposition of the resulting context. -/
theorem PSubst.inverse {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {ρ : Ty} (hu : HasType Γ u ρ) :
    ∃ Θ Δs σs, HasType Θ t ρ ∧ HasTypeMulti Δs ss σs ∧
      Θ k = (σs : Multiset Ty) ∧ Γ = Θ.remove k + Δs.sum.shift k 0 := by
  induction h using PSubst.rec
    (motive_2 := fun ts k ss us _ => ∀ {Γs ρs}, HasTypeMulti Γs us ρs →
      ∃ Θs Δs σs, HasTypeMulti Θs ts ρs ∧ HasTypeMulti Δs ss σs ∧
        Θs.sum k = (σs : Multiset Ty) ∧ Γs.sum = Θs.sum.remove k + Δs.sum.shift k 0)
    generalizing Γ ρ with
  | @var_eq s Δ τ k hs =>
    obtain ⟨hΓ, hρ⟩ := hasType_unique hu (hs.shift k 0)
    subst Γ
    subst ρ
    refine ⟨Ctx.single k {τ}, [Δ], [τ], .var k τ, .cons hs .nil, ?_, ?_⟩
    · simp [Ctx.single]
    · have hz : (Ctx.single k {τ}).remove k = 0 := by
        funext n
        simp only [Ctx.remove, Ctx.single, Pi.zero_apply]
        split_ifs <;> first | rfl | omega
      simp [hz]
  | @var_lt n k τ hlt =>
    cases hu
    refine ⟨Ctx.single n {τ}, [], [], .var n τ, .nil, ?_, ?_⟩
    · simp [Ctx.single, show k ≠ n by omega]
    · simp [Ctx.remove_single k n {τ} (by omega), hlt]
  | @var_gt n k τ hgt =>
    cases hu
    refine ⟨Ctx.single n {τ}, [], [], .var n τ, .nil, ?_, ?_⟩
    · simp [Ctx.single, show k ≠ n by omega]
    · simp [Ctx.remove_single k n {τ} (by omega), show ¬ n < k by omega]
  | @lam t u k ss ℓ h ih =>
    cases hu with
    | @lam Γ M ρ _ _ hu =>
      obtain ⟨Θ, Δs, σs, ht, hs, hm, he⟩ := ih hu
      let Θ' : Ctx := fun n => Θ (n + 1)
      have hzero : M = Θ 0 := by
        have := congrFun he 0
        simpa [Ctx.cons, Ctx.remove, Ctx.shift, -Ctx.shift_sum] using this
      have hcons : Θ = Ctx.cons M Θ' := by
        funext n
        cases n with
        | zero => exact hzero.symm
        | succ n => rfl
      refine ⟨Θ', Δs, σs, .lam ℓ (hcons ▸ ht), hs, hm, ?_⟩
      rw [hcons, Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add] at he
      exact funext fun n => congrFun he (n + 1)
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    cases hu with
    | app hu hus hperm =>
      obtain ⟨Θ, Δs, σs, ht, hss, hm, he⟩ := ih hu
      obtain ⟨Θs, Ξs, τs, hts, hss', hm', he'⟩ := ihs hus
      obtain ⟨Ωs, υs, hss'', hΩ, hυ⟩ := (hss.append hss').perm hp
      refine ⟨Θ + Θs.sum, Ωs, υs, .app ht hts hperm, hss'', ?_, ?_⟩
      · simpa only [Pi.add_apply, hm, hm', Multiset.coe_add] using
          (Multiset.coe_eq_coe.mpr hυ).symm
      · rw [hΩ.sum_eq, List.sum_append, Ctx.shift_add, he, he', Ctx.remove_add]
        ac_rfl
  | nil k =>
    rename_i Γs ρs hu
    cases hu
    exact ⟨[], [], [], .nil, .nil, rfl, by simp⟩
  | @cons t u ts us ss₀ ss₁ k h hs ih ihs =>
    rename_i Γs ρs hu
    cases hu with
    | cons hu hus =>
      obtain ⟨Θ, Δs, σs, ht, hss, hm, he⟩ := ih hu
      obtain ⟨Θs, Ξs, τs, hts, hss', hm', he'⟩ := ihs hus
      refine ⟨Θ :: Θs, Δs ++ Ξs, σs ++ τs, .cons ht hts, hss.append hss', ?_, ?_⟩
      · simp only [List.sum_cons, Pi.add_apply, hm, hm', Multiset.coe_add]
      · simp only [List.sum_cons, List.sum_append, Ctx.remove_add, Ctx.shift_add]
        rw [he, he']
        ac_rfl

/-- Subject expansion at the contracted redex, without a correctness assumption. -/
theorem subject_expansion_beta {t u : DTerm} {ss : List DTerm} {Γ : Ctx} {τ : Ty}
    (ℓ : Label) (hs : PSubst t 0 ss u) (hu : HasType Γ u τ) :
    HasType Γ (.app (.lam ℓ t) ss) τ := by
  obtain ⟨Θ, Δs, σs, ht, hss, hm, he⟩ := hs.inverse hu
  have hbody : HasType (Ctx.cons (σs : Multiset Ty) (Θ.remove 0)) t τ := by
    rw [← Ctx.insert_zero, ← hm, Ctx.insert_remove]
    exact ht
  rw [he, Ctx.shift_zero_cutoff]
  exact .app (.lam ℓ hbody) hss (Multiset.coe_eq_coe.mp (Ty.coe_canon _).symm)

/-- Typing-preserving replacements remain so in any capturing one-hole context. -/
theorem DCtx.typing_mono (C : DCtx) {u v : DTerm}
    (h : ∀ {Γ τ}, HasType Γ u τ → HasType Γ v τ)
    {Γ : Ctx} {τ : Ty} (ht : HasType Γ (C.plug u) τ) :
    HasType Γ (C.plug v) τ := by
  induction C generalizing Γ τ with
  | hole => exact h ht
  | lam ℓ C ih =>
    cases ht with
    | lam _ ht => exact .lam ℓ (ih ht)
  | appL C ss ih =>
    cases ht with
    | app ht hs hp => exact .app (ih ht) hs hp
  | appR t us C vs ih =>
    cases ht with
    | app ht hs hp => exact .app ht (hs.replace (fun h => ih h) us vs) hp

/-- **Subject expansion** for partition-based substitution, including under binders and
in argument positions. This is a typing theorem on raw terms; it asserts no preservation
of correctness. -/
theorem subject_expansion {t u : DTerm} {ss : List DTerm} {Γ : Ctx} {τ : Ty}
    (C : DCtx) (ℓ : Label) (hs : PSubst t 0 ss u) (hu : HasType Γ (C.plug u) τ) :
    HasType Γ (C.plug (.app (.lam ℓ t) ss)) τ :=
  C.typing_mono (fun h => subject_expansion_beta ℓ hs h) hu

private theorem find_type {ss : List DTerm} {s : DTerm}
    (hnd : (ss.map DTerm.ty).Nodup) (hs : s ∈ ss) :
    ss.find? (fun t => decide (t.ty = s.ty)) = some s := by
  classical
  induction ss with
  | nil => simp at hs
  | cons t ts ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hs with rfl | hs
    · simp
    · have hne : t.ty ≠ s.ty := by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨s, hs, he.symm⟩)
      simp [hne, ih hnd.2 hs]

/-- Partition substitution agrees with type-directed lookup in any environment containing
its resources, provided the environment has distinct argument types. -/
theorem PSubst.eq_subst_of_subset {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) (env : List DTerm) (hsub : ss ⊆ env)
    (hnd : (env.map DTerm.ty).Nodup) : u = t.subst k env := by
  classical
  induction h using PSubst.rec
    (motive_2 := fun ts k ss us _ => ss ⊆ env →
      us = ts.map (fun t => t.subst k env)) with
  | @var_eq s Γ τ k hs =>
    have hm : s ∈ env := hsub (by simp)
    simp [DTerm.subst, hasType_ty hs, find_type hnd hm]
  | var_lt τ h => simp [DTerm.subst, h]
  | @var_gt n k τ h => simp [DTerm.subst, show ¬ n < k by omega,
      show ¬ n = k by omega]
  | lam ℓ h ih => simpa only [DTerm.subst] using congrArg (DTerm.lam ℓ) (ih hsub)
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    have h₀ : ss₀ ⊆ env := fun _ hm => hsub (hp.subset (List.mem_append_left _ hm))
    have h₁ : ss₁ ⊆ env := fun _ hm => hsub (hp.subset (List.mem_append_right _ hm))
    simp only [DTerm.subst, ih h₀, ihs h₁]
  | nil => rfl
  | @cons t u ts us ss₀ ss₁ k h hs ih ihs =>
    rename_i hsub
    have h₀ : ss₀ ⊆ env := fun _ hm => hsub (List.mem_append_left _ hm)
    have h₁ : ss₁ ⊆ env := fun _ hm => hsub (List.mem_append_right _ hm)
    simp only [List.map_cons, ih h₀, ihs h₁]

/-- Subject expansion for type-directed substitution with a sequential partition witness. -/
theorem subject_expansion_subst {t u : DTerm} {ss : List DTerm} {Γ : Ctx} {τ : Ty}
    (C : DCtx) (ℓ : Label) (hp : PSubst t 0 ss u)
    (hseq : SeqMS (ss.map DTerm.ty : Multiset Ty))
    (hu : HasType Γ (C.plug (t.subst 0 ss)) τ) :
    HasType Γ (C.plug (.app (.lam ℓ t) ss)) τ := by
  have he : u = t.subst 0 ss :=
    hp.eq_subst_of_subset ss (fun _ h => h)
      (List.Nodup.of_map (f := Ty.label) (by simpa [SeqMS] using hseq))
  exact subject_expansion C ℓ hp (he.symm ▸ hu)

/-- The type-directed typing expansion theorem with explicit, checkable resource
conditions. No partition witness or correctness assumption on the redex is needed. -/
theorem subject_expansion_typeDirected {t : DTerm} {ss : List DTerm} {Δs : List Ctx}
    {σs : List Ty} {Γ : Ctx} {τ : Ty} (C : DCtx) (ℓ : Label)
    (hs : HasTypeMulti Δs ss σs)
    (hm : (σs : Multiset Ty) = (t.occTypes 0 : Multiset Ty))
    (hseq : SeqMS (σs : Multiset Ty))
    (hu : HasType Γ (C.plug (t.subst 0 ss)) τ) :
    HasType Γ (C.plug (.app (.lam ℓ t) ss)) τ := by
  obtain ⟨u, hp⟩ := PSubst.exists hs hm
  apply subject_expansion_subst C ℓ hp _ hu
  simpa only [← hs.types_eq] using hseq

/-! ### Counterexamples -/

/-- The unrestricted type-directed analogue of subject expansion is false, even when the
body and arguments are typable and the argument types match all variable occurrences.
For `z[x][x]` and arguments `[a,b]` of the same type, lookup produces `z[a][a]`, whose
context cannot type the redex (it omits `b`). -/
theorem typeDirected_subject_expansion_counterexample :
    ∃ (t : DTerm) (ss : List DTerm) (Γ : Ctx) (τ : Ty),
      t.Typable ∧ (∀ s ∈ ss, s.Typable) ∧
      (t.occTypes 0 : Multiset Ty) = (ss.map DTerm.ty : Multiset Ty) ∧
      HasType Γ (t.subst 0 ss) τ ∧ ¬ HasType Γ (.app (.lam 4 t) ss) τ := by
  classical
  let τ := Ty.base 0 0
  let σ := Ty.base 1 1
  let ζ := Ty.arrow [τ] 2 (.arrow [τ] 3 σ)
  let t := DTerm.app (.app (.var 1 ζ) [.var 0 τ]) [.var 0 τ]
  let a := DTerm.var 1 τ
  let b := DTerm.var 2 τ
  let u := DTerm.app (.app (.var 0 ζ) [a]) [a]
  have ht : t.Typable := ⟨_, _,
    HasType.app (.app (.var 1 ζ) (.cons (.var 0 τ) .nil) (.refl _))
      (.cons (.var 0 τ) .nil) (.refl _)⟩
  have hu : HasType u.ctx u σ := by
    have h := HasType.app
      (HasType.app (.var 0 ζ) (.cons (.var 1 τ) .nil) (List.Perm.refl _))
      (.cons (.var 1 τ) .nil) (List.Perm.refl _)
    exact hasType_ctx h ▸ h
  have hsubst : t.subst 0 [a, b] = u := by
    simp [t, a, b, u, DTerm.subst, DTerm.ty, DTerm.shift]
  refine ⟨t, [a, b], u.ctx, σ, ht, ?_, ?_, hsubst ▸ hu, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨_, _, .var 1 τ⟩
    · exact ⟨_, _, .var 2 τ⟩
  · simp [t, a, b, DTerm.occTypes, DTerm.ty]
  · intro h
    have he := hasType_occTypes h 2
    simp [u, t, a, b, DTerm.ctx, DTerm.occTypes] at he

/-- Correctness permits repeated arrow labels: it controls domains, not global uniqueness
of type labels. Both arrows here have label `7`, but their domains are empty. -/
theorem correct_repeated_arrow_labels :
    Correct (.var 0 (.arrow [] 7 (.arrow [] 7 (.base 0 8)))) := by
  apply Correct.var
  apply Ty.Sequential.arrow (by simp [SeqMS]) (by simp)
  exact Ty.Sequential.arrow (by simp [SeqMS]) (by simp) (Ty.sequential_base 0 8)

/-- Typing subject expansion does not preserve correctness, even for exact resource
partitioning and a fresh lambda label. All old arrows in `ζ` have distinct labels (2 and 3),
but abstracting the two equal-labeled argument types introduces a nonsequential binder domain. -/
theorem correctness_subject_expansion_counterexample :
    ∃ (t u : DTerm) (ss : List DTerm) (Γ : Ctx) (τ : Ty) (ℓ : Label),
      PSubst t 0 ss u ∧ u = t.subst 0 ss ∧ HasType Γ u τ ∧ Correct u ∧ ℓ ∉ u.lamLabels ∧
      HasType Γ (.app (.lam ℓ t) ss) τ ∧ ¬ Correct (.app (.lam ℓ t) ss) := by
  let τ := Ty.base 0 0
  let υ := Ty.base 1 0
  let σ := Ty.base 2 1
  let ζ := Ty.arrow [τ] 2 (.arrow [υ] 3 σ)
  let t := DTerm.app (.app (.var 1 ζ) [.var 0 τ]) [.var 0 υ]
  let a := DTerm.app (.var 1 (.arrow [] 5 τ)) []
  let b := DTerm.app (.var 1 (.arrow [] 6 υ)) []
  let u := DTerm.app (.app (.var 0 ζ) [a]) [b]
  have hτ : τ.Sequential := Ty.sequential_base 0 0
  have hυ : υ.Sequential := Ty.sequential_base 1 0
  have hσ : σ.Sequential := Ty.sequential_base 2 1
  have hζ : ζ.Sequential := Ty.Sequential.arrow (by simp [SeqMS])
    (by simpa using hτ) (Ty.Sequential.arrow (by simp [SeqMS]) (by simpa using hυ) hσ)
  have ha : HasType (Ctx.single 1 {.arrow [] 5 τ}) a τ := by
    simpa using HasType.app (.var 1 (.arrow [] 5 τ)) .nil (List.Perm.refl [])
  have hb : HasType (Ctx.single 1 {.arrow [] 6 υ}) b υ := by
    simpa using HasType.app (.var 1 (.arrow [] 6 υ)) .nil (List.Perm.refl [])
  have ca : Correct a := by
    apply Correct.app (.var 1 (.arrow [] 5 τ)) .nil (.refl _)
      (Correct.var 1 (Ty.Sequential.arrow (by simp [SeqMS]) (by simp) hτ))
    · simp
    · simp [DTerm.lamLabels]
    · intro n
      simp only [List.sum_nil, add_zero, Ctx.single]
      split <;> simp [SeqMS]
  have cb : Correct b := by
    apply Correct.app (.var 1 (.arrow [] 6 υ)) .nil (.refl _)
      (Correct.var 1 (Ty.Sequential.arrow (by simp [SeqMS]) (by simp) hυ))
    · simp
    · simp [DTerm.lamLabels]
    · intro n
      simp only [List.sum_nil, add_zero, Ctx.single]
      split <;> simp [SeqMS]
  have hf := HasType.app (.var 0 ζ) (.cons ha .nil) (List.Perm.refl _)
  have hu := HasType.app hf (.cons hb .nil) (List.Perm.refl _)
  have cf : Correct (.app (.var 0 ζ) [a]) := by
    apply Correct.app (.var 0 ζ) (.cons ha .nil) (.refl _) (Correct.var 0 hζ)
    · intro s hs
      have : s = a := List.mem_singleton.mp hs
      subst s
      exact ca
    · simp [DTerm.lamLabels, a]
    · intro n
      rcases n with _ | _ | n <;> simp [Ctx.single, SeqMS, Ty.label]
  have cu : Correct u := by
    apply Correct.app hf (.cons hb .nil) (.refl _) cf
    · intro s hs
      have : s = b := List.mem_singleton.mp hs
      subst s
      exact cb
    · simp [DTerm.lamLabels, a, b]
    · intro n
      rcases n with _ | _ | _ | n <;> simp [Ctx.single, SeqMS, Ty.label]
  have hp : PSubst t 0 [a, b] u := by
    have hz : PSubst (.var 1 ζ) 0 [] (.var 0 ζ) := .var_gt ζ (by omega)
    have hsa : PSubst (.var 0 τ) 0 [a] a := by
      simpa [a, DTerm.shift] using PSubst.var_eq 0 ha
    have hsb : PSubst (.var 0 υ) 0 [b] b := by
      simpa [b, DTerm.shift] using PSubst.var_eq 0 hb
    exact .app (.app hz (.cons hsa (.nil 0)) (.refl _))
      (.cons hsb (.nil 0)) (.refl _)
  have he : u = t.subst 0 [a, b] :=
    hp.eq_subst_of_subset [a, b] (fun _ h => h) (by simp [a, b, DTerm.ty, τ, υ])
  refine ⟨t, u, [a, b], _, σ, 4, hp, he, hu, cu, ?_, subject_expansion_beta 4 hp hu, ?_⟩
  · simp [u, a, b, DTerm.lamLabels]
  · intro hc
    have ht := HasType.app
      (HasType.app (.var 1 ζ) (.cons (.var 0 τ) .nil) (List.Perm.refl _))
        (.cons (.var 0 υ) .nil) (List.Perm.refl _)
    have hseq := hc.seq_ctx t _ σ (.fn _ (.lam 4 (.refl t))) ht 0
    simp [Ctx.single, SeqMS, Ty.label, τ, υ] at hseq

/-- The correctness failure also occurs for the existing type-directed reduction itself;
it is not an artifact of extending substitution to a partition relation. -/
theorem correctness_dStep_expansion_counterexample :
    ∃ (t u : DTerm) (ℓ : Label) (Γ : Ctx) (τ : Ty),
      DStep t ℓ u ∧ HasType Γ u τ ∧ Correct u ∧ HasType Γ t τ ∧ ¬ Correct t := by
  obtain ⟨t, u, ss, Γ, τ, ℓ, _, he, hu, hc, _, ht, hn⟩ :=
    correctness_subject_expansion_counterexample
  refine ⟨_, u, ℓ, Γ, τ, ?_, hu, hc, ht, hn⟩
  simpa only [← he] using DStep.beta ℓ t ss

theorem DTerm.lamLabels_shift (t : DTerm) (d c : ℕ) :
    (t.shift d c).lamLabels = t.lamLabels := by
  induction t using DTerm.rec
    (motive_2 := fun ts => ∀ c,
      (ts.map (DTerm.shift d c)).flatMap DTerm.lamLabels = ts.flatMap DTerm.lamLabels)
    generalizing c with
  | var => simp only [DTerm.shift]; split <;> simp [DTerm.lamLabels]
  | lam ℓ t ih => simp [DTerm.shift, DTerm.lamLabels, ih]
  | app t ss ih ihs => simp [DTerm.shift, DTerm.lamLabels, ih, ihs]
  | nil => simp
  | cons t ts ih ihs =>
    rename_i c
    simp [ih c, ihs c]

/-- Partition substitution preserves every old lambda occurrence, without copying any. -/
theorem PSubst.lamLabels {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) :
    (u.lamLabels : Multiset Label) = (t.lamLabels : Multiset Label) +
      (ss.flatMap DTerm.lamLabels : Multiset Label) := by
  induction h using PSubst.rec
    (motive_2 := fun ts _ ss us _ =>
      (us.flatMap DTerm.lamLabels : Multiset Label) =
        (ts.flatMap DTerm.lamLabels : Multiset Label) +
        (ss.flatMap DTerm.lamLabels : Multiset Label)) with
  | var_eq k hs => simp [DTerm.lamLabels_shift, DTerm.lamLabels]
  | var_lt => simp [DTerm.lamLabels]
  | var_gt => simp [DTerm.lamLabels]
  | lam ℓ h ih =>
    simpa only [DTerm.lamLabels, ← Multiset.cons_coe, Multiset.cons_add] using
      congrArg (fun xs : Multiset Label => ℓ ::ₘ xs) ih
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    have hperm := Multiset.coe_eq_coe.mpr (hp.flatMap_right DTerm.lamLabels)
    simp only [List.flatMap_append, ← Multiset.coe_add] at hperm
    simp only [DTerm.lamLabels, ← Multiset.coe_add, ih, ihs]
    rw [← hperm]
    ac_rfl
  | nil => simp
  | cons h hs ih ihs =>
    simp only [List.flatMap_cons, List.flatMap_append, ← Multiset.coe_add, ih, ihs]
    ac_rfl

/-- Correctness of an abstraction follows from its correct body and fresh lambda label. -/
theorem Correct.lam {t : DTerm} {Γ : Ctx} {M : Multiset Ty} {τ : Ty} (ℓ : Label)
    (ht : HasType (Ctx.cons M Γ) t τ) (hc : Correct t)
    (hl : (ℓ :: t.lamLabels).Nodup) : Correct (.lam ℓ t) := by
  have ha := HasType.lam ℓ ht
  have hctx := hc.seq_ctx t _ τ (.refl t) ht
  have hct := hc.context_typesSequential ht
  have hty := Ty.Sequential.arrow (ℓ := ℓ) (M := Ty.canon M) (by simpa only [Ty.coe_canon, Ctx.cons] using hctx 0)
    (fun σ hm => hct 0 σ (by simpa only [Ty.mem_canon, Ctx.cons] using hm)) (hc.type_sequential ht)
  refine ⟨⟨_, _, ha⟩, by simpa only [DTerm.lamLabels] using hl, ?_, ?_⟩
  · intro s Δ σ hsub h n
    cases hsub with
    | refl => obtain ⟨rfl, rfl⟩ := hasType_unique h ha; exact hctx (n + 1)
    | lam _ hsub => exact hc.seq_ctx s Δ σ hsub h n
  · intro s Δ σ hsub h N m ρ ho
    cases hsub with
    | refl =>
      obtain ⟨rfl, rfl⟩ := hasType_unique h ha
      rcases ho with ⟨n, υ, hm, ho⟩ | ho
      · exact hct (n + 1) υ hm N m ρ ho
      · exact hty N m ρ ho
    | lam _ hsub => exact hc.seq_ty s Δ σ hsub h N m ρ ho

/-- Syntactically computed contexts coincide with the contexts of a multi-typing. -/
theorem HasTypeMulti.contexts_eq {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) : ss.map DTerm.ctx = Γs := by
  induction ss generalizing Γs σs with
  | nil => cases hs; rfl
  | cons s ss ih =>
    cases hs with
    | cons h hs => simp only [List.map_cons, ← hasType_ctx h, ih hs]

/-- Shifting preserves multi-typing. -/
theorem HasTypeMulti.shift {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) (d c : ℕ) :
    HasTypeMulti (Γs.map (Ctx.shift d c)) (ss.map (DTerm.shift d c)) σs := by
  induction ss generalizing Γs σs with
  | nil => cases hs; exact .nil
  | cons s ss ih => cases hs with | cons h hs => exact .cons (h.shift d c) (ih hs)

/-- Shifting introduces only empty context entries. -/
theorem Ctx.Seq.shift {Γ : Ctx} (h : Γ.Seq) (d c : ℕ) : (Γ.shift d c).Seq := by
  intro n
  simp only [Ctx.shift]
  split
  · exact h n
  · split
    · simp [SeqMS]
    · exact h _

/-- Index shifting preserves all three correctness conditions. -/
theorem Correct.shift {t : DTerm} (hc : Correct t) (d c : ℕ) : Correct (t.shift d c) := by
  induction t using DTerm.ind generalizing c with
  | var n τ =>
    have hτ := hc.type_sequential (.var n τ)
    simp only [DTerm.shift]
    split <;> exact Correct.var _ hτ
  | lam ℓ t ih =>
    obtain ⟨Γ, τ, ht⟩ := hc.typable
    cases ht with
    | lam _ ht =>
      have hu := ht.shift d (c + 1)
      rw [Ctx.shift_cons] at hu
      simp only [DTerm.shift]

      exact Correct.lam ℓ hu (ih (hc.sub (.lam ℓ (.refl t))) (c + 1))
        (by simpa only [DTerm.lamLabels, DTerm.lamLabels_shift] using hc.uniquely_labeled)
  | app t ss ih ihs =>
    obtain ⟨Γ, τ, ht⟩ := hc.typable
    cases ht with
    | app ht hs hp =>
      simp only [DTerm.shift]

      apply Correct.app (ht.shift d c) (hs.shift d c) hp
        (ih (hc.sub (.fn ss (.refl t))) c)
      · intro s hm
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
        exact ihs s hs (hc.sub (.arg t hs (.refl s))) c
      · have hh := hc.uniquely_labeled
        rw [← DTerm.lamLabels_shift (.app t ss) d c] at hh
        simpa only [DTerm.shift] using hh
      · rw [← Ctx.shift_sum, ← Ctx.shift_add]
        exact (hc.seq_ctx _ _ _ (.refl _) (.app ht hs hp)).shift d c

/-- Forward typing for the resource partition substitution of `03-03-the-calculus.tex`. -/
theorem PSubst.typing {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {τ : Ty} (ht : HasType Γ t τ) :
    HasType (Γ.remove k + (ss.map DTerm.ctx).sum.shift k 0) u τ := by
  induction h using PSubst.rec
    (motive_2 := fun ts k ss us _ => ∀ {Γs τs}, HasTypeMulti Γs ts τs →
      ∃ Δs, HasTypeMulti Δs us τs ∧
        Δs.sum = Γs.sum.remove k + (ss.map DTerm.ctx).sum.shift k 0)
    generalizing Γ τ with
  | @var_eq s Δ τ k hs =>
    cases ht
    have hz : (Ctx.single k {τ}).remove k = 0 := by
      funext n; simp only [Ctx.remove, Ctx.single, Pi.zero_apply]
      split_ifs <;> first | rfl | omega
    simpa [hz, ← hasType_ctx hs] using hs.shift k 0
  | @var_lt n k τ hlt =>
    cases ht
    simpa [Ctx.remove_single k n {τ} (by omega), hlt] using HasType.var n τ
  | @var_gt n k τ hgt =>
    cases ht
    simpa [Ctx.remove_single k n {τ} (by omega), show ¬ n < k by omega] using HasType.var (n - 1) τ
  | lam ℓ _ ih =>
    cases ht with
    | lam _ ht =>
      have hu := ih ht
      rw [Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add, add_zero] at hu
      exact HasType.lam ℓ hu
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    cases ht with
    | app ht hts hperm =>
      obtain ⟨Δs, hus, he⟩ := ihs hts
      have ha := HasType.app (ih ht) hus hperm
      have hp' := (hp.map DTerm.ctx).sum_eq
      simp only [List.map_append, List.sum_append] at hp'
      rw [he] at ha
      convert ha using 1
      rw [Ctx.remove_add, ← hp', Ctx.shift_add]
      ac_rfl
  | nil k =>
    rename_i Γs τs ht
    cases ht
    exact ⟨[], .nil, by simp⟩
  | cons _ _ ih ihs =>
    rename_i Γs τs ht
    cases ht with
    | cons ht hts =>
      obtain ⟨Δs, hus, he⟩ := ihs hts
      refine ⟨_ :: Δs, .cons (ih ht) hus, ?_⟩
      simp only [List.sum_cons, List.map_append, List.sum_append, Ctx.remove_add,
        Ctx.shift_add, he]
      ac_rfl

theorem PSubstMulti.typing {ts us : List DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubstMulti ts k ss us) {Γs : List Ctx} {τs : List Ty}
    (ht : HasTypeMulti Γs ts τs) :
    ∃ Δs, HasTypeMulti Δs us τs ∧
      Δs.sum = Γs.sum.remove k + (ss.map DTerm.ctx).sum.shift k 0 := by
  induction ts generalizing ss us Γs τs with
  | nil => cases h; cases ht; exact ⟨[], .nil, by simp⟩
  | cons t ts ih =>
    cases h with
    | cons h hs =>
      cases ht with
      | cons ht hts =>
        obtain ⟨Δs, hus, he⟩ := ih hs hts
        refine ⟨_ :: Δs, .cons (h.typing ht) hus, ?_⟩
        simp only [List.sum_cons, List.map_append, List.sum_append, Ctx.remove_add,
          Ctx.shift_add, he]
        ac_rfl

theorem SeqMS.of_le {M N : Multiset Ty} (h : M ≤ N) (hs : SeqMS N) : SeqMS M :=
  Multiset.nodup_of_le (Multiset.map_le_map h) hs

theorem Ctx.Seq.left {Γ Δ : Ctx} (h : (Γ + Δ).Seq) : Γ.Seq :=
  fun n => SeqMS.of_le (le_add_right le_rfl) (h n)

theorem Ctx.Seq.right {Γ Δ : Ctx} (h : (Γ + Δ).Seq) : Δ.Seq :=
  fun n => SeqMS.of_le (le_add_left le_rfl) (h n)

/-- Correctness of substitution: the resulting contexts are sequential and lambda
occurrences are distinct. These are the three checks in `08-03-subject-reduction.tex`. -/
theorem PSubst.correct {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {τ : Ty} (ht : HasType Γ t τ)
    (hc : Correct t) (hcs : ∀ s ∈ ss, Correct s) (hl : u.lamLabels.Nodup)
    (hctx : (Γ.remove k + (ss.map DTerm.ctx).sum.shift k 0).Seq) : Correct u := by
  induction h using PSubst.rec
    (motive_2 := fun ts k ss us _ => ∀ {Γs τs}, HasTypeMulti Γs ts τs →
      (∀ t ∈ ts, Correct t) → (∀ s ∈ ss, Correct s) →
      (us.flatMap DTerm.lamLabels).Nodup →
      (Γs.sum.remove k + (ss.map DTerm.ctx).sum.shift k 0).Seq →
      ∀ u ∈ us, Correct u)
    generalizing Γ τ with
  | var_eq k hs => exact (hcs _ (by simp)).shift k 0
  | var_lt τ hlt => cases ht; exact Correct.var _ (hc.type_sequential (.var _ _))
  | var_gt τ hgt => cases ht; exact Correct.var _ (hc.type_sequential (.var _ _))
  | @lam t u k ss ℓ h ih =>
    cases ht with
    | lam _ ht =>
      have hu := h.typing ht
      rw [Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add, add_zero] at hu
      simp only [DTerm.lamLabels] at hl
      apply Correct.lam ℓ hu _ hl
      apply ih ht (hc.sub (.lam ℓ (.refl t))) hcs (List.nodup_cons.mp hl).2
      intro n
      cases n with
      | zero =>
        simpa only [Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add, add_zero, Ctx.cons] using
          hc.seq_ctx t _ _ (.lam ℓ (.refl t)) ht 0
      | succ n =>
        simpa only [Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add, add_zero,
          Ctx.cons] using hctx n
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    cases ht with
    | @app Γ _ L m τ Γs _ σs ht hts hperm =>
      obtain ⟨Δs, hus, he⟩ := hs.typing hts
      have hu := h.typing ht
      have hsum : (Γ.remove k + (ss₀.map DTerm.ctx).sum.shift k 0) + Δs.sum =
          (Γ + Γs.sum).remove k + (ss.map DTerm.ctx).sum.shift k 0 := by
        rw [he, Ctx.remove_add, ← (hp.map DTerm.ctx).sum_eq,
          List.map_append, List.sum_append, Ctx.shift_add]
        ac_rfl
      have hctx' := hsum.symm ▸ hctx
      simp only [DTerm.lamLabels] at hl
      apply Correct.app hu hus hperm
      · exact ih ht (hc.sub (.fn ts (.refl t)))
          (fun s hm => hcs s (hp.subset (List.mem_append_left _ hm)))
          ((List.nodup_append.mp hl).1) hctx'.left
      · apply ihs hts (fun s hm => hc.sub (.arg t hm (.refl s)))
          (fun s hm => hcs s (hp.subset (List.mem_append_right _ hm)))
          ((List.nodup_append.mp hl).2.1)
        exact he ▸ hctx'.right
      · simpa only [DTerm.lamLabels] using hl
      · exact hctx'
  | nil => rename_i Γs τs ht hc hcs hl hctx u hu; cases ht; simp at hu
  | @cons t u ts us ss₀ ss₁ k h hs ih ihs =>
    rename_i Γs τs ht hc hcs hl hctx v hv
    cases ht with
    | @cons Γ _ σ Γs _ σs ht hts =>
      have he : (Γ.remove k + (ss₀.map DTerm.ctx).sum.shift k 0) +
          (Γs.sum.remove k + (ss₁.map DTerm.ctx).sum.shift k 0) =
          (Γ :: Γs).sum.remove k + ((ss₀ ++ ss₁).map DTerm.ctx).sum.shift k 0 := by
        simp only [List.sum_cons, Ctx.remove_add, List.map_append, List.sum_append,
          Ctx.shift_add]
        ac_rfl
      have hctx' := he.symm ▸ hctx
      simp only [List.flatMap_cons] at hl
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ih ht (hc _ (by simp)) (fun s hm => hcs s (by simp [hm]))
          (List.nodup_append.mp hl).1 hctx'.left
      · exact ihs hts (fun s hm => hc s (by simp [hm]))
          (fun s hm => hcs s (by simp [hm])) (List.nodup_append.mp hl).2.1 hctx'.right v hv

/-- Lambda counting is unchanged by index shifting. -/
theorem DTerm.size_shift (t : DTerm) (d c : ℕ) : (t.shift d c).size = t.size := by
  induction t using DTerm.rec
    (motive_2 := fun ts => ∀ c,
      ((ts.map (DTerm.shift d c)).map DTerm.size).sum = (ts.map DTerm.size).sum)
    generalizing c with
  | var => simp only [DTerm.shift]; split <;> simp [DTerm.size]
  | lam ℓ t ih => simp [DTerm.shift, DTerm.size, ih]
  | app t ts ih ihs => simp only [DTerm.shift, DTerm.size, ih, ihs]
  | nil => simp
  | cons t ts ih ihs => rename_i c; simpa only [List.map_cons, List.sum_cons, ih c] using congrArg (t.size + ·) (ihs c)

/-- The alternative substitution at a correct beta redex is an exact resource partition. -/
theorem Correct.beta_partition {ℓ : Label} {b : DTerm} {ss : List DTerm}
    (hc : Correct (.app (.lam ℓ b) ss)) : PSubst b 0 ss (b.subst 0 ss) := by
  obtain ⟨Γ, τ, ht⟩ := hc.typable
  cases ht with
  | @app Γ _ L m τ Δs _ σs hf hs hp =>
    cases hf with
    | @lam Γ M _ _ _ hb =>
      have hm := (Multiset.coe_eq_coe.mpr hp).trans (Ty.coe_canon M)
      have hocc := hasType_occTypes hb 0
      obtain ⟨u, hu⟩ := PSubst.exists (t := b) (k := 0) hs (hm.trans hocc)
      have hseq := hc.seq_ctx b _ _ (.fn ss (.lam ℓ (.refl b))) hb 0
      have hseq' : SeqMS (σs : Multiset Ty) := hm.symm ▸ hseq
      have hn : (ss.map DTerm.ty).Nodup := List.Nodup.of_map (f := Ty.label) (by
        simpa only [← hs.types_eq, SeqMS, Multiset.map_coe, Multiset.coe_nodup] using
          hseq')
      exact hu.eq_subst_of_subset ss (fun _ h => h) hn ▸ hu

/-- A step removes its lambda label and preserves every other lambda occurrence. -/
theorem DStep.lamLabels {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u) (hc : Correct t) :
    ℓ ::ₘ (u.lamLabels : Multiset Label) = (t.lamLabels : Multiset Label) := by
  induction h with
  | beta ℓ b ss =>
    have hh := hc.beta_partition.lamLabels
    simpa only [DTerm.lamLabels, ← Multiset.coe_add, ← Multiset.cons_coe,
      Multiset.cons_add] using congrArg (fun xs : Multiset Label => ℓ ::ₘ xs) hh
  | lam m h ih =>
    have hh := ih (hc.sub (.lam m (.refl _)))
    simp only [DTerm.lamLabels, ← Multiset.cons_coe]
    rw [Multiset.cons_swap, hh]
  | appL ss h ih =>
    have hh := ih (hc.sub (.fn ss (.refl _)))
    simp only [DTerm.lamLabels, ← Multiset.coe_add, ← Multiset.cons_add, hh]
  | @appR s s' ℓ t us vs h ih =>
    have hh := ih (hc.sub (.arg t (by simp) (.refl _)))
    simp only [DTerm.lamLabels, List.flatMap_append, List.flatMap_cons, ← Multiset.coe_add]
    calc
      _ = (t.lamLabels : Multiset Label) +
          ((us.flatMap DTerm.lamLabels : Multiset Label) +
            ((ℓ ::ₘ (s'.lamLabels : Multiset Label)) + (vs.flatMap DTerm.lamLabels : Multiset Label))) := by
              simp only [Multiset.cons_add, Multiset.add_cons]
      _ = _ := by rw [hh]

/-- Preservation of typing and correctness (`08-03-subject-reduction.tex`). -/
theorem DStep.subject_reduction {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u)
    (hc : Correct t) {Γ : Ctx} {τ : Ty} (ht : HasType Γ t τ) : HasType Γ u τ ∧ Correct u := by
  have hlabels : u.lamLabels.Nodup := by
    have hh := h.lamLabels hc
    have hn : (ℓ ::ₘ (u.lamLabels : Multiset Label)).Nodup := hh.symm ▸ hc.uniquely_labeled
    exact (Multiset.nodup_cons.mp hn).2
  induction h generalizing Γ τ with
  | beta ℓ b ss =>
    have hp := hc.beta_partition
    cases ht with
    | @app Γ _ L m τ Δs _ σs hf hs hperm =>
      cases hf with
      | @lam Γ M _ _ _ hb =>
        have he : (ss.map DTerm.ctx).sum = Δs.sum := congrArg List.sum hs.contexts_eq
        have hu := hp.typing hb
        simp only [he, Ctx.shift_zero_cutoff] at hu
        have hcctx := hc.seq_ctx _ _ _ (.refl _) (.app (.lam ℓ hb) hs hperm)
        refine ⟨hu, hp.correct hb (hc.sub (.fn ss (.lam ℓ (.refl b))))
          (fun s hm => hc.sub (.arg _ hm (.refl s))) hlabels ?_⟩
        simpa only [he, Ctx.shift_zero_cutoff, show (Ctx.cons M Γ).remove 0 = Γ from rfl] using hcctx
  | lam m h ih =>
    cases ht with
    | lam _ ht =>
      obtain ⟨hu, hcu⟩ := ih (hc.sub (.lam m (.refl _))) ht
        ((List.nodup_cons.mp (by simpa only [DTerm.lamLabels] using hlabels)).2)
      exact ⟨.lam m hu, Correct.lam m hu hcu (by simpa only [DTerm.lamLabels] using hlabels)⟩
  | appL ss h ih =>
    cases ht with
    | app ht hs hp =>
      obtain ⟨hu, hcu⟩ := ih (hc.sub (.fn ss (.refl _))) ht
        ((List.nodup_append.mp (by simpa only [DTerm.lamLabels] using hlabels)).1)
      exact ⟨.app hu hs hp, Correct.app hu hs hp hcu
        (fun s hm => hc.sub (.arg _ hm (.refl s))) hlabels
        (hc.seq_ctx _ _ _ (.refl _) (.app ht hs hp))⟩
  | @appR s s' ℓ t us vs h ih =>
    cases ht with
    | app ht hs hp =>
      have hcs := hc.sub (.arg t (by simp) (.refl s))
      obtain ⟨Ξ, σ, hv⟩ := hcs.typable
      have hlv := (DTerm.Sub.arg t (ss := us ++ s' :: vs) (by simp) (.refl s')).lamLabels_sublist.nodup hlabels
      obtain ⟨hu, hcu⟩ := ih hcs hv hlv
      have hus := HasTypeMulti.replace (fun hh => by
        obtain ⟨rfl, rfl⟩ := hasType_unique hh hv
        exact hu) us vs hs
      have ha := HasType.app ht hus hp
      refine ⟨ha, Correct.app ht hus hp (hc.sub (.fn _ (.refl t))) ?_ hlabels ?_⟩
      · intro s hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hc.sub (.arg t (by simp [hm]) (.refl s))
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact hcu
          · exact hc.sub (.arg t (by simp [hm]) (.refl s))
      · exact hc.seq_ctx _ _ _ (.refl _) (.app ht hs hp)

/-- The resource partition uses each argument exactly once (`08-05-termination.tex`). -/
theorem PSubst.size {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) : u.size = t.size + (ss.map DTerm.size).sum := by
  induction h using PSubst.rec
    (motive_2 := fun ts _ ss us _ => (us.map DTerm.size).sum =
      (ts.map DTerm.size).sum + (ss.map DTerm.size).sum) with
  | var_eq => simp [DTerm.size_shift, DTerm.size]
  | var_lt => simp [DTerm.size]
  | var_gt => simp [DTerm.size]
  | lam ℓ h ih => simp [DTerm.size, ih]; omega
  | app _ _ hp ih ihs =>
    have := (hp.map DTerm.size).sum_eq
    simp only [List.map_append, List.sum_append] at this
    simp only [DTerm.size, ih, ihs]
    omega
  | nil => simp
  | cons _ _ ih ihs => simp only [List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, ih, ihs]; omega

/-! ### Reduction and size helpers -/

namespace DTerm

/-- Inserting indices inside an already inserted gap just enlarges that gap. -/
theorem shift_gap (t : DTerm) (a b c d : ℕ) (hbc : b ≤ c) (hca : c ≤ b + a) :
    (t.shift a b).shift d c = t.shift (a + d) b := by
  induction t using DTerm.ind generalizing b c with
  | var n τ =>
    by_cases hn : n < b
    · simp [shift, hn, show n < c by omega]
    · simp only [shift, ite_eq_right hn, ite_eq_right (show ¬ n + a < c by omega)]
      congr 1; omega
  | lam ℓ t ih =>
    simp only [shift]
    rw [ih (b + 1) (c + 1) (by omega) (by omega)]
  | app t ts ih ihs =>
    simp only [shift, List.map_map]
    rw [ih b c hbc hca]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs b c hbc hca)

/-- Removing an index inside an inserted gap leaves a smaller gap. -/
theorem subst_shift_gap (t : DTerm) (d c i : ℕ) (ss : List DTerm)
    (hci : c ≤ i) (hid : i ≤ c + d) :
    (t.shift (d + 1) c).subst i ss = t.shift d c := by
  induction t using DTerm.ind generalizing c i with
  | var n τ =>
    by_cases hn : n < c
    · simp [shift, subst, hn, show n < i by omega]
    · simp only [shift, ite_eq_right hn, subst,
        ite_eq_right (show ¬ n + (d + 1) < i by omega),
        ite_eq_right (show ¬ n + (d + 1) = i by omega)]
      congr 1
  | lam ℓ t ih =>
    simp only [shift, subst]
    rw [ih (c + 1) (i + 1) (by omega) (by omega)]
  | app t ts ih ihs =>
    simp only [shift, subst, List.map_map]
    rw [ih c i hci hid]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs c i hci hid)

/-- Shifting below a substituted variable commutes with substitution. Arguments
are stored outside all crossed binders, as in the definition of `subst`. -/
theorem shift_subst (t : DTerm) (d c k : ℕ) (ss : List DTerm) (hck : c ≤ k) :
    (t.shift d c).subst (k + d) ss = (t.subst k ss).shift d c := by
  induction t using DTerm.ind generalizing c k with
  | var n τ =>
    by_cases hn : n < c
    · simp only [shift, ite_eq_left hn, subst, ite_eq_left (show n < k + d by omega),
        ite_eq_left (show n < k by omega)]
    · by_cases hnk : n < k
      · simp [shift, subst, hn, hnk, show n + d < k + d by omega]
      · by_cases he : n = k
        · subst n
          simp only [shift, ite_eq_right hn, subst, Nat.lt_irrefl, ↓reduceIte]
          cases hf : ss.find? (fun s => decide (s.ty = τ)) with
          | none => simp [shift, hn]
          | some s =>
            simp only [Option.map_some, Option.getD_some]
            exact (shift_gap s k 0 c d (by omega) (by omega)).symm
        · have hgt : k < n := by omega
          simp only [shift, ite_eq_right hn, subst,
            ite_eq_right (show ¬ n + d < k + d by omega),
            ite_eq_right (show ¬ n + d = k + d by omega), ite_eq_right (show ¬ n < k by omega),
            ite_eq_right he, ite_eq_right (show ¬ n - 1 < c by omega)]
          congr 1; omega
  | lam ℓ t ih =>
    simp only [shift, subst]
    rw [show k + d + 1 = (k + 1) + d by omega, ih (c + 1) (k + 1) (by omega)]
  | app t ts ih ihs =>
    simp only [shift, subst, List.map_map]
    rw [ih c k hck]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs c k hck)

/-- Every occurrence selected by the alternative substitution has a matching argument.
Unlike partition substitution, unused extra arguments are allowed. -/
def SubstDefined (t : DTerm) (k : ℕ) (ss : List DTerm) : Prop :=
  ∀ τ ∈ t.occTypes k, ∃ s ∈ ss, s.ty = τ

/-- With a type-preserving argument transformation, lookup commutes with `map`. -/
theorem find_type_map {ss : List DTerm} (f : DTerm → DTerm)
    (hf : ∀ s ∈ ss, (f s).ty = s.ty) (τ : Ty) :
    (ss.map f).find? (fun s => decide (s.ty = τ)) =
      (ss.find? (fun s => decide (s.ty = τ))).map f := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.find?_cons, hf s (by simp)]
    split
    · rfl
    · exact ih (fun u hu => hf u (by simp [hu]))

/-- Substitution commutation (`03-03-the-calculus.tex`, alternative substitution).
The first lookup must be defined, and substitution in the arguments must preserve
their types. There is no additional shift of `us`: arguments already live outside
all binders crossed by `subst`. -/
theorem subst_commute (t : DTerm) (i k : ℕ) (ss us : List DTerm)
    (hd : t.SubstDefined i ss)
    (ht : ∀ s ∈ ss, (s.subst k us).ty = s.ty) :
    (t.subst i ss).subst (i + k) us =
      (t.subst (i + k + 1) us).subst i (ss.map (·.subst k us)) := by
  induction t using DTerm.ind generalizing i with
  | var n τ =>
    by_cases hni : n < i
    · simp only [subst, ite_eq_left hni, ite_eq_left (show n < i + k by omega),
        ite_eq_left (show n < i + k + 1 by omega)]
    · by_cases he : n = i
      · subst n
        obtain ⟨s, hs, hty⟩ := hd τ (by simp [occTypes])
        have hf : (ss.find? (fun s => decide (s.ty = τ))).isSome :=
          by rw [List.isSome_find?]; exact List.any_eq_true.mpr ⟨s, hs, by simpa using hty⟩
        cases hfind : ss.find? (fun s => decide (s.ty = τ)) with
        | none => simp [hfind] at hf
        | some s =>
          simp only [subst, Nat.lt_irrefl, ↓reduceIte,
            ite_eq_left (show i < i + k + 1 by omega), find_type_map _ ht, hfind,
            Option.map_some, Option.getD_some]
          simpa only [Nat.zero_add, Nat.add_comm] using shift_subst s i 0 k us (Nat.zero_le k)
      · have hgt : i < n := by omega
        by_cases hnk : n = i + k + 1
        · subst n
          simp only [subst, ite_eq_right (show ¬ i + k + 1 < i by omega), ite_eq_right (by omega : ¬ i + k + 1 = i),
            show i + k + 1 - 1 = i + k by omega, Nat.lt_irrefl, ↓reduceIte]
          cases hfind : us.find? (fun s => decide (s.ty = τ)) with
          | none => simp [subst, show ¬ i + k + 1 < i by omega,
              show ¬ i + k + 1 = i by omega]
          | some s =>
            simp only [Option.map_some, Option.getD_some]
            exact (subst_shift_gap s (i + k) 0 i _ (Nat.zero_le i) (by omega)).symm
        · by_cases hlt : n < i + k + 1
          · simp only [subst, ite_eq_right hni, ite_eq_right he,
              ite_eq_left (show n - 1 < i + k by omega), ite_eq_left hlt]
          · simp only [subst, ite_eq_right hni, ite_eq_right he,
              ite_eq_right (show ¬ n - 1 < i + k by omega), ite_eq_right (show ¬ n - 1 = i + k by omega),
              ite_eq_right hlt, ite_eq_right hnk,
              ite_eq_right (show ¬ n - 1 < i by omega), ite_eq_right (show ¬ n - 1 = i by omega)]
  | lam ℓ t ih =>
    simpa only [subst, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (lam ℓ) (ih (i + 1) (by simpa only [SubstDefined, occTypes] using hd))
  | app t ts ih ihs =>
    simp only [SubstDefined, occTypes] at hd
    have hdt : t.SubstDefined i ss := fun τ hm => hd τ (List.mem_append_left _ hm)
    have hdts : ∀ s ∈ ts, s.SubstDefined i ss := fun s hs τ hm =>
      hd τ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, hm⟩))
    simp only [subst, List.map_map]
    rw [ih i hdt]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs i (hdts s hs))

end DTerm

/-- Regression witnesses for the former commutation statement. The first conjunct
shows why missing lookups must be excluded; the second refutes the extra shift even
when both original substitutions consume exactly their matching resources. -/
theorem DTerm.subst_commute_counterexamples :
    let x := DTerm.var 0 (.base 0 0)
    let y := DTerm.var 1 (.base 0 0)
    ((x.subst 0 []).subst 0 [y] ≠
      (x.subst 1 [y]).subst 0 []) ∧
    ((y.subst 0 []).subst 0 [x] ≠
      (y.subst 1 [x.shift 1 0]).subst 0 []) := by
  simp [DTerm.subst, DTerm.shift, DTerm.ty]

/-- Choose typed matching arguments for a list of occurrence types. -/
theorem HasTypeMulti.choose {σs : List Ty} {ss : List DTerm}
    (h : ∀ τ ∈ σs, ∃ s ∈ ss, ∃ Γ, HasType Γ s τ) :
    ∃ Γs ss', HasTypeMulti Γs ss' σs ∧ ∀ s ∈ ss', s ∈ ss := by
  induction σs with
  | nil => exact ⟨[], [], .nil, by simp⟩
  | cons τ σs ih =>
    obtain ⟨s, hs, Γ, ht⟩ := h τ (by simp)
    obtain ⟨Γs, ts, hts, hmem⟩ := ih (fun τ hm => h τ (by simp [hm]))
    refine ⟨Γ :: Γs, s :: ts, .cons ht hts, ?_⟩
    intro t hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hs
    · exact hmem t hm

theorem PSubst.defined {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) : t.SubstDefined k ss := by
  intro τ hm
  have hm' : τ ∈ (ss.map DTerm.ty : Multiset Ty) := h.occTypes ▸ hm
  obtain ⟨s, hs, he⟩ := List.mem_map.mp hm'
  exact ⟨s, hs, he⟩

/-- The alternative substitution can use a larger sequential list than the exact
partition. Only arguments matching actual occurrences are consumed. -/
theorem DTerm.partition_of_defined {t : DTerm} {k : ℕ} {ss : List DTerm}
    (hd : t.SubstDefined k ss) (hs : ∀ s ∈ ss, s.Typable)
    (hn : (ss.map DTerm.ty).Nodup) :
    ∃ ts, (∀ s ∈ ts, s ∈ ss) ∧ PSubst t k ts (t.subst k ss) := by
  obtain ⟨Γs, ts, hts, hmem⟩ := HasTypeMulti.choose (σs := t.occTypes k) (ss := ss) (by
    intro τ hm
    obtain ⟨s, hs', he⟩ := hd τ hm
    obtain ⟨Γ, σ, ht⟩ := hs s hs'
    exact ⟨s, hs', Γ, (he ▸ hasType_ty ht) ▸ ht⟩)
  obtain ⟨u, hp⟩ := PSubst.exists hts rfl
  exact ⟨ts, hmem, hp.eq_subst_of_subset ss hmem hn ▸ hp⟩

/-- Defined alternative substitution preserves the type even with unused extra arguments. -/
theorem HasType.subst_ty {t : DTerm} {Γ : Ctx} {τ : Ty} (ht : HasType Γ t τ)
    {k : ℕ} {ss : List DTerm} (hd : t.SubstDefined k ss)
    (hs : ∀ s ∈ ss, s.Typable) (hn : (ss.map DTerm.ty).Nodup) :
    (t.subst k ss).ty = t.ty := by
  obtain ⟨ts, _, hp⟩ := DTerm.partition_of_defined hd hs hn
  exact (hasType_ty (hp.typing ht)).symm.trans (hasType_ty ht)

/-- Reduction in the body survives substitution (`08-07-strong-permutation.tex`). -/
theorem DStep.subst {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u) (hc : Correct t)
    (k : ℕ) (ss : List DTerm) (hd : t.SubstDefined k ss)
    (hs : ∀ s ∈ ss, s.Typable) (hn : (ss.map DTerm.ty).Nodup) :
    DStep (t.subst k ss) ℓ (u.subst k ss) := by
  induction h generalizing k with
  | beta ℓ b ts =>
    have hp := hc.beta_partition
    have htype : ∀ s ∈ ts, (s.subst k ss).ty = s.ty := by
      intro s hm
      obtain ⟨Γ, τ, ht⟩ := (hc.sub (.arg _ hm (.refl s))).typable
      apply ht.subst_ty _ hs hn
      intro τ hτ
      apply hd τ
      simp only [DTerm.occTypes]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hm, hτ⟩)
    have he := b.subst_commute 0 k ts ss hp.defined htype
    simp only [Nat.zero_add] at he
    simp only [DTerm.subst]
    rw [he]
    exact DStep.beta ℓ (b.subst (k + 1) ss) (ts.map (·.subst k ss))
  | lam m h ih =>
    simp only [DTerm.subst]
    apply DStep.lam m (ih (hc.sub (.lam m (.refl _))) (k + 1) _)
    simpa only [DTerm.SubstDefined, DTerm.occTypes] using hd
  | appL ts h ih =>
    simp only [DTerm.subst]
    apply DStep.appL _ (ih (hc.sub (.fn ts (.refl _))) k _)
    intro τ hm
    exact hd τ (by simpa only [DTerm.occTypes] using List.mem_append_left _ hm)
  | @appR s s' ℓ t us vs h ih =>
    simp only [DTerm.subst, List.map_append, List.map_cons]
    apply DStep.appR _ _ _ (ih (hc.sub (.arg t (by simp) (.refl s))) k _)
    intro τ hm
    apply hd τ
    simp only [DTerm.occTypes]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, by simp, hm⟩)

namespace DTerm

/-- Commutation of two ordered index insertions. -/
theorem shift_shift (t : DTerm) (a b c d : ℕ) (hbc : b ≤ c) :
    (t.shift a b).shift d (c + a) = (t.shift d c).shift a b := by
  induction t using DTerm.ind generalizing b c with
  | var n τ =>
    by_cases hnb : n < b
    · simp [shift, hnb, show n < c by omega, show n < c + a by omega]
    · by_cases hnc : n < c
      · simp [shift, hnb, hnc, show n + a < c + a by omega]
      · simp only [shift, ite_eq_right hnb, ite_eq_right hnc,
          ite_eq_right (show ¬ n + a < c + a by omega),
          ite_eq_right (show ¬ n + d < b by omega)]
        congr 1; omega
  | lam ℓ t ih =>
    simp only [shift]
    rw [show c + a + 1 = (c + 1) + a by omega, ih (b + 1) (c + 1) (by omega)]
  | app t ts ih ihs =>
    simp only [shift, List.map_map]
    rw [ih b c hbc]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs b c hbc)

/-- Shifting above a substituted variable shifts its arguments too. -/
theorem subst_shift (t : DTerm) (k d c : ℕ) (ss : List DTerm)
    (hd : t.SubstDefined k ss) (ht : ∀ s ∈ ss, (s.shift d c).ty = s.ty) :
    (t.subst k ss).shift d (c + k) =
      (t.shift d (c + k + 1)).subst k (ss.map (DTerm.shift d c)) := by
  induction t using DTerm.ind generalizing k with
  | var n τ =>
    by_cases hnk : n < k
    · simp [subst, shift, hnk, show n < c + k by omega, show n < c + k + 1 by omega]
    · by_cases he : n = k
      · subst n
        simp only [subst, Nat.lt_irrefl, ↓reduceIte, shift,
          ite_eq_left (show k < c + k + 1 by omega), find_type_map _ ht]
        cases hf : ss.find? (fun s => decide (s.ty = τ)) with
        | none =>
          obtain ⟨s, hs, he⟩ := hd τ (by simp [occTypes])
          have hf' : (ss.find? (fun s => decide (s.ty = τ))).isSome := by
            rw [List.isSome_find?]
            exact List.any_eq_true.mpr ⟨s, hs, by simpa using he⟩
          simp [hf] at hf'
        | some s =>
          simp only [Option.map_some, Option.getD_some]
          exact shift_shift s k 0 c d (Nat.zero_le c)
      · by_cases hnc : n < c + k + 1
        · simp [subst, shift, hnk, he, hnc, show n - 1 < c + k by omega]
        · simp only [subst, ite_eq_right hnk, ite_eq_right he, shift,
            ite_eq_right (show ¬ n - 1 < c + k by omega), ite_eq_right hnc, subst,
            ite_eq_right (show ¬ n + d < k by omega),
            ite_eq_right (show ¬ n + d = k by omega)]
          congr 1; omega
  | lam ℓ t ih =>
    simpa only [subst, shift, Nat.add_assoc] using congrArg (lam ℓ) (ih (k + 1) (by simpa only [SubstDefined, occTypes] using hd))
  | app t ts ih ihs =>
    simp only [SubstDefined, occTypes] at hd
    have hdt : t.SubstDefined k ss := fun τ hm => hd τ (List.mem_append_left _ hm)
    have hdts : ∀ s ∈ ts, s.SubstDefined k ss := fun s hs τ hm =>
      hd τ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, hm⟩))
    simp only [subst, shift, List.map_map]
    rw [ih k hdt]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs k (hdts s hs))

end DTerm

/-- Shifting a typed term leaves its type unchanged. -/
theorem HasType.shift_ty {Γ : Ctx} {t : DTerm} {τ : Ty} (ht : HasType Γ t τ)
    (d c : ℕ) : (t.shift d c).ty = t.ty :=
  (hasType_ty (ht.shift d c)).symm.trans (hasType_ty ht)

/-- Steps are stable under insertion of free-variable indices. -/
theorem DStep.shift {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u) (hc : Correct t)
    (d c : ℕ) : DStep (t.shift d c) ℓ (u.shift d c) := by
  induction h generalizing c with
  | beta ℓ b ss =>
    have ht : ∀ s ∈ ss, (s.shift d c).ty = s.ty := by
      intro s hm
      obtain ⟨Γ, τ, ht⟩ := (hc.sub (.arg _ hm (.refl s))).typable
      exact ht.shift_ty d c
    have he := b.subst_shift 0 d c ss hc.beta_partition.defined ht
    simp only [Nat.add_zero] at he
    simp only [DTerm.shift]
    rw [he]
    exact .beta ℓ _ _
  | lam m h ih => simpa only [DTerm.shift] using .lam m (ih (hc.sub (.lam m (.refl _))) (c + 1))
  | appL ss h ih => simpa only [DTerm.shift] using .appL _ (ih (hc.sub (.fn ss (.refl _))) c)
  | appR t us vs h ih =>
    simpa only [DTerm.shift, List.map_append, List.map_cons] using
      .appR _ _ _ (ih (hc.sub (.arg t (by simp) (.refl _))) c)

/-- A single labelled reduction in a list, retaining its occurrence. -/
inductive DListStep : List DTerm → Label → List DTerm → Prop
  | head {s s' : DTerm} {ss : List DTerm} {ℓ : Label} :
      DStep s ℓ s' → DListStep (s :: ss) ℓ (s' :: ss)
  | tail {s : DTerm} {ss ss' : List DTerm} {ℓ : Label} :
      DListStep ss ℓ ss' → DListStep (s :: ss) ℓ (s :: ss')

theorem DListStep.spec {ss ss' : List DTerm} {ℓ : Label} (h : DListStep ss ℓ ss') :
    ∃ us s s' vs, ss = us ++ s :: vs ∧ ss' = us ++ s' :: vs ∧ DStep s ℓ s' := by
  induction h with
  | head h => exact ⟨[], _, _, _, rfl, rfl, h⟩
  | tail h ih =>
    obtain ⟨us, s, s', vs, rfl, rfl, hs⟩ := ih
    exact ⟨_ :: us, s, s', vs, rfl, rfl, hs⟩

theorem DListStep.app {ss ss' : List DTerm} {ℓ : Label} (h : DListStep ss ℓ ss')
    (t : DTerm) : DStep (.app t ss) ℓ (.app t ss') := by
  obtain ⟨us, s, s', vs, rfl, rfl, hs⟩ := h.spec
  exact .appR t us vs hs

theorem DListStep.of_append {s s' : DTerm} {ℓ : Label} (h : DStep s ℓ s')
    (us vs : List DTerm) : DListStep (us ++ s :: vs) ℓ (us ++ s' :: vs) := by
  induction us with
  | nil => exact .head h
  | cons u us ih => exact .tail ih

/-- An application step contracts its root, its function, or one argument. -/
theorem DStep.app_cases {t u : DTerm} {ss : List DTerm} {ℓ : Label}
    (h : DStep (.app t ss) ℓ u) :
    (∃ b, t = .lam ℓ b ∧ u = b.subst 0 ss) ∨
      (∃ t', DStep t ℓ t' ∧ u = .app t' ss) ∨
      ∃ ss', DListStep ss ℓ ss' ∧ u = .app t ss' := by
  cases h with
  | beta ℓ b ss => exact .inl ⟨b, rfl, rfl⟩
  | appL _ h => exact .inr (.inl ⟨_, h, rfl⟩)
  | appR t us vs h => exact .inr (.inr ⟨_, DListStep.of_append h us vs, rfl⟩)

/-- A resource occurrence can be reduced once in the result of partition substitution. -/
theorem PSubst.step_resource [DecidableEq DTerm] {s s' : DTerm} {ℓ : Label} (hstep : DStep s ℓ s')
    (hc : Correct s) {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (hp : PSubst t k ss u) (hm : s ∈ ss) :
    ∃ v, DStep u ℓ v ∧ PSubst t k (s' :: ss.erase s) v := by
  classical
  induction hp using PSubst.rec
    (motive_2 := fun ts k ss us _ => s ∈ ss →
      ∃ rs vs, rs.Perm (s' :: ss.erase s) ∧ DListStep us ℓ vs ∧ PSubstMulti ts k rs vs) with
  | var_eq k ht =>
    have he := List.mem_singleton.mp hm
    subst he
    obtain ⟨ht', _⟩ := hstep.subject_reduction hc ht
    exact ⟨_, hstep.shift hc k 0, by simpa using PSubst.var_eq k ht'⟩
  | var_lt => simp at hm
  | var_gt => simp at hm
  | lam m hp ih =>
    obtain ⟨v, hv, hp'⟩ := ih hm
    exact ⟨_, .lam m hv, .lam m hp'⟩
  | @app t u ts us ss ss₀ ss₁ k hp hps hperm ih ihs =>
    have hm' := hperm.symm.subset hm
    by_cases hm₀ : s ∈ ss₀
    · obtain ⟨v, hv, hp'⟩ := ih hm₀
      refine ⟨_, .appL us hv, .app hp' hps ?_⟩
      simpa only [List.cons_append, List.erase_append_left ss₁ hm₀] using
        (hperm.erase s).cons s'
    · have hm₁ : s ∈ ss₁ := (List.mem_append.mp hm').resolve_left hm₀
      obtain ⟨rs, vs, hr, hv, hp'⟩ := ihs hm₁
      refine ⟨_, hv.app u, .app hp hp' ?_⟩
      exact ((List.Perm.refl ss₀).append hr).trans (List.perm_middle.trans (by
        simpa only [List.erase_append_right ss₁ hm₀] using (hperm.erase s).cons s'))
  | nil => rename_i hm; simp at hm
  | @cons t u ts us ss₀ ss₁ k hp hps ih ihs =>
    rename_i hm
    by_cases hm₀ : s ∈ ss₀
    · obtain ⟨v, hv, hp'⟩ := ih hm₀
      refine ⟨(s' :: ss₀.erase s) ++ ss₁, v :: us, ?_, .head hv, .cons hp' hps⟩
      simp only [List.erase_append_left ss₁ hm₀, List.cons_append]
      exact .refl _
    · have hm₁ : s ∈ ss₁ := (List.mem_append.mp hm).resolve_left hm₀
      obtain ⟨rs, vs, hr, hv, hp'⟩ := ihs hm₁
      refine ⟨ss₀ ++ rs, u :: vs, ?_, .tail hv, .cons hp hp'⟩
      exact ((List.Perm.refl ss₀).append hr).trans (by
        simpa only [List.erase_append_right ss₁ hm₀] using List.perm_middle)

theorem DListStep.types {ss ss' : List DTerm} {ℓ : Label} (h : DListStep ss ℓ ss')
    (hc : ∀ s ∈ ss, Correct s) : ss'.map DTerm.ty = ss.map DTerm.ty := by
  induction h with
  | @head s s' ss ℓ h =>
    obtain ⟨Γ, τ, ht⟩ := (hc s (by simp)).typable
    obtain ⟨hu, _⟩ := h.subject_reduction (hc s (by simp)) ht
    simp only [List.map_cons, (hasType_ty hu).symm.trans (hasType_ty ht)]
  | tail h ih =>
    simp only [List.map_cons, ih (fun s hs => hc s (by simp [hs]))]

/-- A step in one resource survives substitution exactly once
(`08-07-strong-permutation.tex`, reduction inside a substitution). -/
theorem DListStep.substitute {ss ss' : List DTerm} {ℓ : Label} (h : DListStep ss ℓ ss')
    (hc : ∀ s ∈ ss, Correct s) (hn : (ss.map DTerm.ty).Nodup)
    {t u : DTerm} {k : ℕ} (hp : PSubst t k ss u) :
    DStep u ℓ (t.subst k ss') := by
  classical
  have hn' : (ss'.map DTerm.ty).Nodup := h.types hc ▸ hn
  obtain ⟨us, s, s', vs, rfl, rfl, hs⟩ := h.spec
  obtain ⟨v, hv, hp'⟩ := hp.step_resource hs (hc s (by simp)) (by simp)
  have he : ((us ++ s :: vs).erase s).Perm (us ++ vs) := by
    simpa using (List.perm_middle (a := s) (l₁ := us) (l₂ := vs)).erase s
  have hperm : (s' :: (us ++ s :: vs).erase s).Perm (us ++ s' :: vs) :=
    (he.cons s').trans List.perm_middle.symm
  exact hp'.eq_subst_of_subset _ (fun _ hm => hperm.subset hm) hn' ▸ hv

/-- Lift a diamond argument on individual terms to one-step list reductions. -/
theorem DListStep.permutation {ss ss₁ ss₂ : List DTerm} {ℓ m : Label}
    (ih : ∀ s ∈ ss, ∀ {u v a b}, DStep s a u → DStep s b v →
      (a = b ∧ u = v) ∨ ∃ w, DStep u b w ∧ DStep v a w)
    (h₁ : DListStep ss ℓ ss₁) (h₂ : DListStep ss m ss₂) :
    (ℓ = m ∧ ss₁ = ss₂) ∨ ∃ ss₃, DListStep ss₁ m ss₃ ∧ DListStep ss₂ ℓ ss₃ := by
  induction h₁ generalizing ss₂ with
  | @head s u ts a h =>
    cases h₂ with
    | head h' =>
      rcases ih s (by simp) h h' with ⟨rfl, rfl⟩ | ⟨w, hu, hv⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨w :: ts, .head hu, .head hv⟩
    | tail h' => exact .inr ⟨_, .tail h', .head h⟩
  | @tail s ts us a h iht =>
    cases h₂ with
    | head h' => exact .inr ⟨_, .head h', .tail h⟩
    | tail h' =>
      rcases iht (fun t ht => ih t (by simp [ht])) h' with ⟨rfl, rfl⟩ | ⟨vs, hu, hv⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨s :: vs, .tail hu, .tail hv⟩

/-- The two nested-redex cases of strong permutation: a step inside the beta body,
or inside one of its resources (`08-07-strong-permutation.tex`). -/
theorem DStep.beta_permutation {b v : DTerm} {ss : List DTerm} {ℓ m : Label}
    (hc : Correct (.app (.lam ℓ b) ss)) (h : DStep (.app (.lam ℓ b) ss) m v) :
    (ℓ = m ∧ b.subst 0 ss = v) ∨
      ∃ w, DStep (b.subst 0 ss) m w ∧ DStep v ℓ w := by
  have hp := hc.beta_partition
  have hb := hc.sub (.fn ss (.lam ℓ (.refl b)))
  have hs : ∀ s ∈ ss, Correct s := fun s hm => hc.sub (.arg _ hm (.refl s))
  obtain ⟨Γ, τ, ht⟩ := hb.typable
  have hseq : SeqMS (b.occTypes 0 : Multiset Ty) := by
    rw [← hasType_occTypes ht 0]
    exact hb.seq_ctx b Γ τ (.refl b) ht 0
  have hseq' : SeqMS (ss.map DTerm.ty : Multiset Ty) := hp.occTypes ▸ hseq
  have hn : (ss.map DTerm.ty).Nodup := List.Nodup.of_map (f := Ty.label)
    (by simpa only [SeqMS, Multiset.map_coe, Multiset.coe_nodup] using hseq')
  rcases h.app_cases with ⟨b', he, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨ss', hss, rfl⟩
  · cases he
    exact .inl ⟨rfl, rfl⟩
  · cases hf with
    | lam _ hf =>
      exact .inr ⟨_, hf.subst hb 0 ss hp.defined
        (fun s hm => (hs s hm).typable) hn, .beta ℓ _ ss⟩
  · exact .inr ⟨_, hss.substitute hs hn hp, .beta ℓ b ss'⟩

/-- Strong permutation, with equality of the original steps allowed as a separate case.
The structural cases are exactly the context cases in `08-07-strong-permutation.tex`. -/
theorem DStep.permutation {t u v : DTerm} {ℓ m : Label} (hc : Correct t)
    (h₁ : DStep t ℓ u) (h₂ : DStep t m v) :
    (ℓ = m ∧ u = v) ∨ ∃ w, DStep u m w ∧ DStep v ℓ w := by
  induction t using DTerm.ind generalizing u v ℓ m with
  | var => cases h₁
  | lam a t ih =>
    cases h₁ with
    | lam _ h₁ =>
      cases h₂ with
      | lam _ h₂ =>
        rcases ih (hc.sub (.lam a (.refl t))) h₁ h₂ with ⟨rfl, rfl⟩ | ⟨w, hu, hv⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨.lam a w, .lam a hu, .lam a hv⟩
  | app t ss ih ihs =>
    rcases h₁.app_cases with ⟨b, rfl, rfl⟩ | ⟨t₁, ht₁, rfl⟩ | ⟨ss₁, hs₁, rfl⟩
    · exact DStep.beta_permutation hc h₂
    · rcases h₂.app_cases with ⟨b, rfl, rfl⟩ | ⟨t₂, ht₂, rfl⟩ | ⟨ss₂, hs₂, rfl⟩
      · rcases DStep.beta_permutation hc h₁ with ⟨he, hu⟩ | ⟨w, hu, hv⟩
        · exact .inl ⟨he.symm, hu.symm⟩
        · exact .inr ⟨w, hv, hu⟩
      · rcases ih (hc.sub (.fn ss (.refl t))) ht₁ ht₂ with ⟨rfl, rfl⟩ | ⟨w, hu, hv⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨.app w ss, .appL ss hu, .appL ss hv⟩
      · exact .inr ⟨.app t₁ ss₂, hs₂.app t₁, .appL ss₂ ht₁⟩
    · rcases h₂.app_cases with ⟨b, rfl, rfl⟩ | ⟨t₂, ht₂, rfl⟩ | ⟨ss₂, hs₂, rfl⟩
      · rcases DStep.beta_permutation hc h₁ with ⟨he, hu⟩ | ⟨w, hu, hv⟩
        · exact .inl ⟨he.symm, hu.symm⟩
        · exact .inr ⟨w, hv, hu⟩
      · exact .inr ⟨.app t₂ ss₁, .appL ss₁ ht₂, hs₁.app t₂⟩
      · rcases DListStep.permutation
          (fun s hm => ihs s hm (hc.sub (.arg t hm (.refl s)))) hs₁ hs₂ with
          ⟨rfl, rfl⟩ | ⟨ss₃, hu, hv⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨.app t ss₃, hu.app t, hv.app t⟩

/-- Every step contracts a lambda present in its source, independently of typing. -/
theorem DStep.label_mem {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u) : ℓ ∈ t.lamLabels := by
  induction h with
  | beta => simp [DTerm.lamLabels]
  | lam _ _ ih => simp [DTerm.lamLabels, ih]
  | appL _ _ ih => simp [DTerm.lamLabels, ih]
  | @appR s s' ℓ t us vs h ih =>
    simp only [DTerm.lamLabels, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨s, by simp, ih⟩

/-- In a correct term, the target of a step is determined by its label. -/
theorem dStep_deterministic {t u u' : DTerm} {ℓ : Label} (ht : Correct t)
    (h : DStep t ℓ u) (h' : DStep t ℓ u') : u = u' := by
  rcases DStep.permutation ht h h' with ⟨_, he⟩ | ⟨v, hu, _⟩
  · exact he
  · have hn : (ℓ ::ₘ (u.lamLabels : Multiset Label)).Nodup :=
      (h.lamLabels ht).symm ▸ ht.uniquely_labeled
    exact False.elim ((Multiset.nodup_cons.mp hn).1 hu.label_mem)

/-- Substitution is linear: it neither erases nor duplicates λs (`08-05-termination.tex`). -/
theorem size_subst {Γ : Ctx} {t : DTerm} {τ : Ty} {Δs : List Ctx} {ss : List DTerm}
    {σs : List Ty} (ht : HasType (Ctx.cons (σs : Multiset Ty) Γ) t τ)
    (hs : HasTypeMulti Δs ss σs) (hseq : SeqMS (σs : Multiset Ty)) :
    (t.subst 0 ss).size = t.size + (ss.map DTerm.size).sum := by
  obtain ⟨u, hp⟩ := PSubst.exists (t := t) (k := 0) hs (by
    exact hasType_occTypes ht 0)
  have hn : (ss.map DTerm.ty).Nodup := List.Nodup.of_map (f := Ty.label)
    (by simpa only [← hs.types_eq, SeqMS, Multiset.map_coe, Multiset.coe_nodup] using hseq)
  rw [← hp.eq_subst_of_subset ss (fun _ h => h) hn]
  exact hp.size

/-- Each step consumes exactly one λ. -/
theorem size_dStep {t u : DTerm} {ℓ : Label} (ht : Correct t) (h : DStep t ℓ u) :
    u.size + 1 = t.size := by
  induction h with
  | beta ℓ t ss =>
    obtain ⟨Γ, τ, hh⟩ := ht.typable
    cases hh with
    | app hf hs hp =>
      cases hf with
      | @lam Γ M σ _ _ hb =>
        rename_i Δs σs
        have he : (σs : Multiset Ty) = M := by
          exact (Multiset.coe_eq_coe.mpr hp).trans (Ty.coe_canon M)
        have hb' := he.symm ▸ hb
        have hseq := ht.seq_ctx t _ _ (.fn ss (.lam ℓ (.refl t))) hb 0
        have hh := size_subst hb' hs (he.symm ▸ hseq)
        simp only [DTerm.size] at *
        omega
  | lam m h ih =>
    have hh := ih (ht.sub (.lam m (.refl _)))
    simp only [DTerm.size] at *; omega
  | appL ss h ih =>
    have hh := ih (ht.sub (.fn ss (.refl _)))
    simp only [DTerm.size] at *; omega
  | appR t us vs h ih =>
    have hh := ih (ht.sub (.arg t (by simp) (.refl _)))
    simp only [DTerm.size, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons] at *
    omega

end Thesis
