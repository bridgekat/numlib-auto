/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: core's `Init.Data.List.Lemmas` / `Init.Data.List.Monadic` and
`Mathlib.Data.List.Basic`, `Mathlib.Algebra.BigOperators.Group.List.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Forall2

/-!
# Loops as folds

An algorithm written as a program is a loop `l.foldlM step s₀` over an index list, and in exact
arithmetic (the monad `Id`) a `List.foldl` (core's `List.idRun_foldlM`). This file collects the
general facts about such folds that the proofs about algorithms keep needing.

* **Invariants.** `List.foldl_prefix_induction` (an invariant indexed by the processed prefix),
  `List.foldl_induction` (indexed by the step count, the `List` twin of core's
  `Array.foldl_induction`), `List.foldl_finRange_induction`, and their `Id` forms
  `List.idRun_foldlM_induction`, `List.idRun_foldlM_finRange_induction`. An invariant independent
  of the step is core's `List.foldlRecOn`.
* **Restructuring a loop.** `List.foldlM_hom` (a loop commutes with a map of states that
  intertwines its steps), `List.foldlM_flatMap` (a loop over a `flatMap` is a loop of loops),
  `List.foldlM_lens` and its pure form `List.foldl_lens` (a loop acting on one component of its
  state is one update of that component) and `List.foldlM_range_succ` (the last pass of a loop
  over `List.range`).
* **Loops writing one entry per step**, over a state `κ → β` updated by `Function.update`:
  `List.foldl_update_apply_of_forall_ne` (an entry no step writes keeps its value),
  `List.foldl_update_apply_of_pairwise` (when no step reads an entry written by an earlier step,
  each written entry holds its step's value on the initial state), its two common special cases
  `List.foldl_update_of_nodup` and `List.foldl_update_eq_ite`, and the in-place (Gauss–Seidel)
  form `List.exists_foldl_update_apply_of_pairwise_rel` / `List.foldl_update_apply_of_pairwise_rel`,
  where a step may read the entries written before it.
* **Exact arithmetic.** Running sums and differences (`List.foldl_add_eq_add_sum_map`,
  `List.foldl_sub_eq_sub_sum_map`), loop interchange (`List.foldl_apply_of_pi`) and a loop
  accumulating into one entry (`List.foldl_update_self`, `List.foldlM_update_self`).
-/

universe u v

namespace List

variable {α β γ κ : Type*}

/-! ### Small list facts -/

/-- A list of length at least two has two heads. -/
theorem exists_cons_cons_of_two_le_length :
    ∀ {l : List α}, 2 ≤ l.length → ∃ a b t, l = a :: b :: t
  | a :: b :: t, _ => ⟨a, b, t, rfl⟩
  | [], h => absurd h (by simp)
  | [_], h => absurd h (by simp)

/-- In a list that is pairwise related by `r`, split as `p ++ i :: q`, an element `j ≠ i` with
`¬ r i j` lies before `i`. -/
theorem mem_prefix_of_pairwise {r : α → α → Prop} {l p q : List α} {i j : α}
    (hs : l.Pairwise r) (h : l = p ++ i :: q) (hj : j ∈ l) (hji : j ≠ i) (hr : ¬ r i j) :
    j ∈ p := by
  rw [h] at hs hj
  rcases mem_append.1 hj with hj | hj
  · exact hj
  · rcases mem_cons.1 hj with rfl | hj
    · exact absurd rfl hji
    · exact absurd ((pairwise_cons.1 (pairwise_append.1 hs).2.1).1 j hj) hr

/-- Values related one by one to a duplicate-free list of indices are the values of a function on
the indices (defined as `d` off the list). -/
theorem Forall₂.exists_map_eq_of_nodup {R : α → β → Prop} {o : List α} {ps : List β}
    (h : Forall₂ R o ps) (ho : o.Nodup) (d : α → β) :
    ∃ p : α → β, (∀ i ∈ o, R i (p i)) ∧ o.map p = ps := by
  classical
  induction h with
  | nil => exact ⟨d, by simp, rfl⟩
  | @cons a b o ps hab _ ih =>
    rcases nodup_cons.1 ho with ⟨ha, ho'⟩
    obtain ⟨p, hp, hmap⟩ := ih ho'
    refine ⟨Function.update p a b, fun i hi => ?_, ?_⟩
    · rcases mem_cons.1 hi with rfl | hi
      · rwa [Function.update_self]
      · rw [Function.update_of_ne fun (e : i = a) => ha (e ▸ hi)]
        exact hp i hi
    · rw [map_cons, Function.update_self, ← hmap]
      congr 1
      exact map_congr_left fun i hi => Function.update_of_ne (fun (e : i = a) => ha (e ▸ hi)) _ _

/-- A product over a filtered list is the product of the mapped list with the factors outside the
filter replaced by `1`. -/
@[to_additive /-- A sum over a filtered list is the sum of the mapped list with the terms outside
the filter replaced by `0`. -/]
theorem prod_map_filter {M : Type*} [Monoid M] (p : α → Prop) [DecidablePred p] (f : α → M)
    (l : List α) : ((l.filter p).map f).prod = (l.map fun a => if p a then f a else 1).prod := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- A product over a filtered `List.finRange n` is the `Finset` product over the filter. -/
@[to_additive /-- A sum over a filtered `List.finRange n` is the `Finset` sum over the filter. -/]
theorem prod_map_filter_finRange {M : Type*} [CommMonoid M] {n : ℕ} (p : Fin n → Prop)
    [DecidablePred p] (f : Fin n → M) :
    (((finRange n).filter p).map f).prod = ∏ i ∈ Finset.univ.filter p, f i := by
  rw [prod_map_filter, Finset.prod_filter, Fin.prod_univ_def]

/-! ### Invariants -/

/-- **A loop invariant for `List.foldl`, indexed by the processed prefix**: if `I [] b`, and the
step on the element `x` that follows a prefix `p` maps states satisfying `I p` to states satisfying
`I (p ++ [x])`, then the fold satisfies `I l`. -/
theorem foldl_prefix_induction {l : List α} (f : β → α → β) (I : List α → β → Prop) {b : β}
    (h0 : I [] b) (hstep : ∀ p x q, l = p ++ x :: q → ∀ s, I p s → I (p ++ [x]) (f s x)) :
    I l (l.foldl f b) := by
  suffices H : ∀ (r p : List α) (s : β), p ++ r = l → I p s → I l (r.foldl f s) from
    H l [] b rfl h0
  intro r
  induction r with
  | nil => rintro p s rfl hs; simpa using hs
  | cons x r ih =>
    rintro p s rfl hs
    exact ih (p ++ [x]) (f s x) (by simp) (hstep p x r rfl s hs)

/-- **A loop invariant for `List.foldl`, indexed by the step count**: if `motive 0 init` and step
`i` maps states satisfying `motive i` to states satisfying `motive (i + 1)`, the fold satisfies
`motive l.length`. The `List` twin of core's `Array.foldl_induction`. -/
theorem foldl_induction {l : List α} (motive : ℕ → β → Prop) {init : β} (h0 : motive 0 init)
    {f : β → α → β} (hf : ∀ i : Fin l.length, ∀ b, motive i b → motive (i + 1) (f b l[i])) :
    motive l.length (l.foldl f init) := by
  induction l generalizing motive init with
  | nil => exact h0
  | cons a l ih =>
    exact ih (fun k b => motive (k + 1) b) (hf ⟨0, by simp⟩ init h0)
      fun i b hb => hf ⟨i + 1, by simp⟩ b hb

/-- **A loop invariant for a fold over `List.finRange n`**, indexed by the step count. -/
theorem foldl_finRange_induction {n : ℕ} (motive : ℕ → β → Prop) {init : β} (h0 : motive 0 init)
    {f : β → Fin n → β} (hf : ∀ (k : Fin n) (b : β), motive k b → motive (k + 1) (f b k)) :
    motive n ((finRange n).foldl f init) := by
  have h := foldl_induction (l := finRange n) motive h0 fun i b hb => by
    have e : (finRange n)[i] = ⟨i, by simpa using i.2⟩ := Fin.ext (by simp)
    rw [e]
    exact hf ⟨i, by simpa using i.2⟩ b hb
  rwa [length_finRange] at h

/-- **A loop invariant in exact arithmetic, indexed by the step count**: the `Id` form of
`List.foldl_induction`. -/
theorem idRun_foldlM_induction {α β : Type u} {l : List α} (motive : ℕ → β → Prop) {init : β}
    (h0 : motive 0 init) {f : β → α → Id β}
    (hf : ∀ i : Fin l.length, ∀ b, motive i b → motive (i + 1) (f b l[i]).run) :
    motive l.length (l.foldlM f init).run := by
  rw [idRun_foldlM]
  exact foldl_induction motive h0 hf

/-- **A loop invariant for a loop over `List.finRange n` in exact arithmetic**: the `Id` form of
`List.foldl_finRange_induction`. -/
theorem idRun_foldlM_finRange_induction {β : Type u} {n : ℕ} (motive : ℕ → β → Prop) {init : β}
    (h0 : motive 0 init) {f : β → Fin n → Id β}
    (hf : ∀ (k : Fin n) (b : β), motive k b → motive (k + 1) (f b k).run) :
    motive n ((finRange n).foldlM f init).run := by
  rw [idRun_foldlM]
  exact foldl_finRange_induction motive h0 hf

/-! ### Restructuring a loop -/

/-- **A loop acting on one component of its state**, the pure form of `List.foldlM_lens`: if every
step reads the component `get s` of its state and writes it back by `set`, the loop is one `set` of
the loop run on that component alone. The three hypotheses say that `get`/`set` is a lens. -/
theorem foldl_lens {σ : Type*} (get : σ → β) (set : σ → β → σ)
    (hgs : ∀ s b, get (set s b) = b) (hss : ∀ s b b', set (set s b) b' = set s b')
    (hsg : ∀ s, set s (get s) = s) (f : β → α → β) (l : List α) (s₀ : σ) :
    l.foldl (fun s a => set s (f (get s) a)) s₀ = set s₀ (l.foldl f (get s₀)) := by
  induction l generalizing s₀ with
  | nil => exact (hsg s₀).symm
  | cons a l ih => simp only [foldl_cons, ih, hgs, hss]

section Monadic

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- **A loop commutes with a map of states that intertwines its steps**: the monadic form of core's
`List.foldl_hom`. -/
theorem foldlM_hom {β₁ β₂ : Type u} (f : β₁ → β₂) {g₁ : β₁ → α → m β₁} {g₂ : β₂ → α → m β₂}
    {l : List α} {init : β₁} (H : ∀ x y, g₂ (f x) y = f <$> g₁ x y) :
    l.foldlM g₂ (f init) = f <$> l.foldlM g₁ init := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp only [foldlM_cons, map_bind, ← ih, H, bind_map_left]

/-- A loop over a `flatMap` is a loop of loops: the monadic form of core's `List.foldl_flatMap`. -/
theorem foldlM_flatMap {β : Type u} {f : α → List γ} {g : β → γ → m β} {l : List α} {init : β} :
    (l.flatMap f).foldlM g init = l.foldlM (fun acc x => (f x).foldlM g acc) init := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih]

/-- A loop of loops is one loop over the pairs, the outer index first. -/
theorem foldlM_foldlM_eq_foldlM_flatMap {σ : Type u} (l₁ : List α) (l₂ : α → List β)
    (f : σ → α → β → m σ) (s : σ) :
    l₁.foldlM (fun s a => (l₂ a).foldlM (fun s b => f s a b) s) s =
      (l₁.flatMap fun a => (l₂ a).map (a, ·)).foldlM (fun s p => f s p.1 p.2) s := by
  simp only [foldlM_flatMap, foldlM_map]

/-- **A loop acting on one component of its state.** If every step of a loop reads the component
`get s` of its state and writes it back by `set`, the loop is one `set` of the loop run on that
component alone. The three hypotheses say that `get`/`set` is a lens. -/
theorem foldlM_lens {σ β : Type u} (get : σ → β) (set : σ → β → σ)
    (hgs : ∀ s b, get (set s b) = b) (hss : ∀ s b b', set (set s b) b' = set s b')
    (hsg : ∀ s, set s (get s) = s) (f : β → α → m β) (l : List α) (s₀ : σ) :
    l.foldlM (fun s a => do let b ← f (get s) a; pure (set s b)) s₀
      = (do let b ← l.foldlM f (get s₀); pure (set s₀ b)) := by
  induction l generalizing s₀ with
  | nil => simp only [foldlM_nil, pure_bind, hsg]
  | cons a l ih => simp only [foldlM_cons, bind_assoc, pure_bind, ih, hgs, hss]

/-- A loop that only rewrites index `i`, each time from its current value, is one update of `i`:
the monadic form of `List.foldl_update_self`. -/
theorem foldlM_update_self {ι β : Type u} [DecidableEq ι] (i : ι) (h : α → β → m β) (l : List α)
    (y : ι → β) :
    l.foldlM (fun (y : ι → β) a => do let b ← h a (y i); pure (Function.update y i b)) y
      = (do let b ← l.foldlM (fun b a => h a b) (y i); pure (Function.update y i b)) :=
  foldlM_lens (fun y => y i) (fun y b => Function.update y i b) (by simp) (by simp) (by simp)
    (fun b a => h a b) l y

/-- The last pass of a loop over `List.range (n + 1)`. -/
theorem foldlM_range_succ {β : Type u} (f : β → ℕ → m β) (b : β) (n : ℕ) :
    (range (n + 1)).foldlM f b = (range n).foldlM f b >>= fun c => f c n := by
  rw [range_succ, foldlM_append]
  simp

end Monadic

/-- The last pass of a loop over `List.range (n + 1)`, in exact arithmetic. -/
theorem idRun_foldlM_range_succ {β : Type u} (f : β → ℕ → Id β) (b : β) (n : ℕ) :
    ((range (n + 1)).foldlM f b).run = (f ((range n).foldlM f b).run n).run := by
  rw [foldlM_range_succ]
  rfl

/-! ### Folds in exact arithmetic -/

/-- A running sum `c + f k₁ + f k₂ + …` is `c` plus the sum of the mapped list. -/
theorem foldl_add_eq_add_sum_map {M : Type*} [AddMonoid M] (f : α → M) (l : List α) (c : M) :
    l.foldl (fun c k => c + f k) c = c + (l.map f).sum := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp [ih, add_assoc]

/-- A running difference `c - f k₁ - f k₂ - …` is `c` minus the sum of the mapped list. -/
theorem foldl_sub_eq_sub_sum_map {M : Type*} [SubtractionCommMonoid M] (f : α → M) (l : List α)
    (c : M) : l.foldl (fun c k => c - f k) c = c - (l.map f).sum := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp [ih, sub_sub]

/-- **Loop interchange in exact arithmetic**: if every step of a loop over a state `ι → β` acts
entrywise, each entry of the result is the loop run on that entry alone. -/
theorem foldl_apply_of_pi {ι : Type*} (f : (ι → β) → α → ι → β) (g : α → ι → β → β)
    (hf : ∀ y a i, f y a i = g a i (y i)) (l : List α) (y₀ : ι → β) (i : ι) :
    l.foldl f y₀ i = l.foldl (fun b a => g a i b) (y₀ i) := by
  induction l generalizing y₀ with
  | nil => rfl
  | cons a l ih => simp [ih, hf]

/-- A loop that only rewrites index `i`, each time from its current value, is one update of `i`.
-/
theorem foldl_update_self {ι : Type*} [DecidableEq ι] (h : α → β → β) (i : ι) (l : List α)
    (y : ι → β) :
    l.foldl (fun y k => Function.update y i (h k (y i))) y
      = Function.update y i (l.foldl (fun b k => h k b) (y i)) := by
  induction l generalizing y with
  | nil => simp
  | cons a l ih => simp [ih]

/-! ### Loops writing one entry per step -/

section Update

variable [DecidableEq κ]

/-- **An entry no step writes keeps its value.** In a loop whose step `a` writes the entry `w a`
of a state `κ → β` (with any value `h a y` computed from the current state), an entry `k` that is
`w a` for no `a ∈ l` is never touched. -/
theorem foldl_update_apply_of_forall_ne (w : α → κ) (h : α → (κ → β) → β) {l : List α} {k : κ}
    (hk : ∀ a ∈ l, w a ≠ k) (y : κ → β) :
    l.foldl (fun y a => Function.update y (w a) (h a y)) y k = y k := by
  induction l generalizing y with
  | nil => rfl
  | cons a l ih =>
    rw [foldl_cons, ih (fun b hb => hk b (mem_cons_of_mem a hb)),
      Function.update_of_ne (hk a mem_cons_self).symm]

/-- **A loop in which no step reads an earlier step's output.** In a loop whose step `a` writes
the entry `w a` of a state `κ → β` with the value `h a y`, if the written entries are distinct and
no step reads (`h b` does not depend on) an entry written by an earlier step, then each written
entry holds its step's value on the initial state. Together with
`List.foldl_update_apply_of_forall_ne`, the loop is a simultaneous update. -/
theorem foldl_update_apply_of_pairwise (w : α → κ) (h : α → (κ → β) → β) {l : List α}
    (hl : l.Pairwise fun a b => w a ≠ w b ∧
      ∀ y y' : κ → β, (∀ k, k ≠ w a → y k = y' k) → h b y = h b y')
    (y : κ → β) {a : α} (ha : a ∈ l) :
    l.foldl (fun y a => Function.update y (w a) (h a y)) y (w a) = h a y := by
  induction l generalizing y with
  | nil => exact absurd ha not_mem_nil
  | cons b l ih =>
    obtain ⟨hbl, hl'⟩ := pairwise_cons.1 hl
    rw [foldl_cons]
    rcases mem_cons.1 ha with rfl | ha
    · rw [foldl_update_apply_of_forall_ne w h (fun c hc => (hbl c hc).1.symm),
        Function.update_self]
    · rw [ih hl' _ ha]
      exact (hbl a ha).2 _ _ fun k hk => Function.update_of_ne hk _ _

/-- **One entry per step, over a duplicate-free list.** A loop whose step `i` replaces entry `i`
by `g i y`, a value that reads only entry `i` and the entries outside `l`, replaces every entry
`i ∈ l` by `g i` of the initial state. -/
theorem foldl_update_of_nodup {l : List κ} (hl : l.Nodup) (g : κ → (κ → β) → β)
    (hg : ∀ i ∈ l, ∀ y y' : κ → β, (∀ r, r ∉ l → y r = y' r) → y i = y' i → g i y = g i y')
    (y : κ → β) :
    l.foldl (fun y i => Function.update y i (g i y)) y = fun r => if r ∈ l then g r y else y r := by
  have hpw : l.Pairwise fun a b => id a ≠ id b ∧
      ∀ y y' : κ → β, (∀ k, k ≠ id a → y k = y' k) → g b y = g b y' :=
    hl.pairwise_of_forall_ne fun a ha b hb hab => ⟨hab, fun z z' hz =>
      hg b hb z z' (fun r hr => hz r fun e => hr (e ▸ ha)) (hz b (Ne.symm hab))⟩
  funext r
  split_ifs with hr
  · exact foldl_update_apply_of_pairwise id g hpw y hr
  · exact foldl_update_apply_of_forall_ne id g (fun a ha (e : a = r) => hr (e ▸ ha)) y

/-- **A loop writing values fixed in advance** sets the listed entries and keeps the others. -/
theorem foldl_update_eq_ite (g : κ → β) (l : List κ) (y : κ → β) :
    l.foldl (fun y i => Function.update y i (g i)) y = fun i => if i ∈ l then g i else y i := by
  induction l generalizing y with
  | nil => simp
  | cons a l ih =>
    rw [foldl_cons, ih]
    funext i
    by_cases hi : i ∈ l
    · simp [hi]
    · by_cases hia : i = a
      · subst hia; simp [hi]
      · simp [hi, hia]

/-- **An in-place loop along an ordered list** (the Gauss–Seidel form). In a loop whose step `i`
writes the entry `w i` of a state `κ → β` with the value `f i y` read from the current state, along
a list ordered by an asymmetric relation `r`, with `w` injective on the list, the value written at
`w i` is `f i v` for a state `v` that agrees with the final state at the entries written before `i`
and with the initial state at every entry not written before `i`. -/
theorem exists_foldl_update_apply_of_pairwise_rel (w : α → κ) (r : α → α → Prop)
    (hr : ∀ i j, r i j → ¬ r j i) (f : α → (κ → β) → β) {l : List α}
    (hw : Set.InjOn w {a | a ∈ l}) (hl : l.Pairwise r) (x : κ → β) {i : α} (hi : i ∈ l) :
    ∃ v : κ → β,
      (∀ j ∈ l, r j i → v (w j) = l.foldl (fun y j => Function.update y (w j) (f j y)) x (w j)) ∧
      (∀ k, (∀ j ∈ l, r j i → w j ≠ k) → v k = x k) ∧
      l.foldl (fun y j => Function.update y (w j) (f j y)) x (w i) = f i v := by
  induction l generalizing x with
  | nil => exact absurd hi not_mem_nil
  | cons a l ih =>
    rw [pairwise_cons] at hl
    have ha : a ∉ l := fun h => hr a a (hl.1 a h) (hl.1 a h)
    have hne : ∀ j ∈ l, w j ≠ w a := fun j hj h =>
      ha (hw (mem_cons_of_mem a hj) mem_cons_self h ▸ hj)
    simp only [foldl_cons]
    rcases mem_cons.1 hi with rfl | hil
    · refine ⟨x, fun j hj hji => ?_, fun _ _ => rfl, ?_⟩
      · rcases mem_cons.1 hj with rfl | hjl
        · exact absurd hji (fun h => hr _ _ h h)
        · exact absurd (hl.1 j hjl) (hr _ _ hji)
      · rw [foldl_update_apply_of_forall_ne w f hne, Function.update_self]
    · obtain ⟨v, hv₁, hv₂, hv₃⟩ := ih (hw.mono fun j hj => mem_cons_of_mem a hj) hl.2
        (Function.update x (w a) (f a x)) hil
      have hva : v (w a) = f a x := by
        rw [hv₂ (w a) fun j hj _ => hne j hj, Function.update_self]
      refine ⟨v, fun j hj hji => ?_, fun k hk => ?_, hv₃⟩
      · rcases mem_cons.1 hj with rfl | hjl
        · rw [hva, foldl_update_apply_of_forall_ne w f hne, Function.update_self]
        · exact hv₁ j hjl hji
      · rw [hv₂ k fun j hj hji => hk j (mem_cons_of_mem a hj) hji]
        exact Function.update_of_ne (hk a mem_cons_self (hl.1 i hil)).symm _ _

/-- **An in-place loop along an ordered list**, entry by entry: if the step at `i` rewrites entry
`i` by `f i y` from the current state `y`, along a list ordered by an asymmetric relation `r`, the
final state `z` satisfies `z i = f i v` where `v` agrees with `z` at the entries processed before
`i` and with the initial state elsewhere. -/
theorem foldl_update_apply_of_pairwise_rel (r : κ → κ → Prop) [DecidableRel r]
    (hr : ∀ i j, r i j → ¬ r j i) (f : κ → (κ → β) → β) {l : List κ} (hl : l.Pairwise r)
    (x : κ → β) {i : κ} (hi : i ∈ l) :
    l.foldl (fun y i => Function.update y i (f i y)) x i =
      f i (fun j => if j ∈ l ∧ r j i then
        l.foldl (fun y i => Function.update y i (f i y)) x j else x j) := by
  obtain ⟨v, hv₁, hv₂, hv₃⟩ :=
    exists_foldl_update_apply_of_pairwise_rel id r hr f (Set.injOn_id _) hl x hi
  have hv₃' : l.foldl (fun y i => Function.update y i (f i y)) x i = f i v := hv₃
  rw [hv₃']
  congr 1
  funext j
  split_ifs with hj
  · exact hv₁ j hj.1 hj.2
  · exact hv₂ j fun j' hj' hj'i e => hj (e ▸ ⟨hj', hj'i⟩)

end Update

/-- **One entry per step, in exact arithmetic.** A loop over a duplicate-free index list whose step
`a` rewrites entry `a` from its current value leaves the entries off the list alone and writes each
entry of the list once, from its initial value. -/
theorem idRun_foldlM_update_apply {ι β : Type u} [DecidableEq ι] (g : ι → β → Id β)
    (l : List ι) (hl : l.Nodup) (y₀ : ι → β) (i : ι) :
    (l.foldlM (fun (y : ι → β) a => do
      let b ← g a (y a); pure (Function.update y a b)) y₀).run i =
      if i ∈ l then (g i (y₀ i)).run else y₀ i := by
  rw [idRun_foldlM]
  exact congrFun (foldl_update_of_nodup hl (fun a y => (g a (y a)).run)
    (fun a _ y y' _ h => by rw [h]) y₀) i

end List
