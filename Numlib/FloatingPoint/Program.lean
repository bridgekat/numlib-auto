import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Forall2
import Mathlib.Data.Set.Functor
import Numlib.FloatingPoint.InnerProduct

/-!
# Algorithms as programs with a rounding hook

The semantics that lets one definition of a numerical algorithm carry both its exact and its
floating-point meaning. An algorithm is written once, in its textbook's operation order, generic in
a monad `M` and a hook `rnd : K → M K` through which every arithmetic result passes.

* **Exact semantics**: `M := Id`, `rnd := pure`. Core's `List.idRun_foldlM` turns the program into
  a `List.foldl`, and the lemmas here turn folds into sums (`List.foldl_add_eq_add_sum_map`) and
  entrywise loops into per-entry folds (`List.foldl_apply_of_pi`, `List.foldl_update_self`).
* **Floating-point semantics**: `M := SetM`, `rnd := fp.round` for a rounding model
  `fp : RoundingModel K`, where `fp.round x = {y | fp.Rounds x y}`
  (`FloatingPoint.RoundingModel.round`). The run set of the program is the set of all results of
  all admissible rounding choices, and a rounding theorem quantifies over it:
  `∀ out ∈ (alg fp.round …).run, …`. `SetM.mem_run_bind` is "some admissible choice at each step";
  `SetM.mem_run_foldlM_iff_foldlRel` turns the run set of a loop into a relational fold
  (`List.FoldlRel`), the shape of the relational predicates of `Numlib/FloatingPoint`
  (`RoundsSumFrom` is such a fold); `SetM.forall_mem_run_foldlM` and
  `SetM.forall_mem_run_foldlM_finRange` are the Hoare rules of a loop;
  `SetM.mem_run_foldlM_update_of_nodup` is the workhorse of every loop that writes one entry per
  step (a saxpy, the inner loop of column-oriented substitution, a column of a rank-one update):
  over a duplicate-free index list whose step `a` rewrites only entry `a`, from `y a` and entries
  outside the list, the run set is the product of the per-entry run sets.
  `SetM.mem_run_foldlM_of_pi` is loop interchange for the rarer loops whose every step acts on every
  entry independently, and `SetM.mem_run_foldlM_update_self_iff` handles a loop accumulating into
  one entry. The preferred route from an algorithm to an error bound is a *bridge* "every run
  satisfies the backbone relation" (`RoundsDot`, `RoundsForwardSubst`, `RoundsLU`, …) followed by
  the backbone theorem about the relation.
* **The exact model** `RoundingModel.exact K` has hook `pure` (`RoundingModel.round_exact`), so an
  exact specification is read off a bridge proved for every model.

## Conventions

The conventions below are final (Golub–Van Loan round, consolidated and revised by review). Every
surface algorithm follows them; the same list, with the same numbers, heads the description of
`NumlibSurface/GolubVanLoan`.

1. **What is rounded.** *Exact* (not passed through `rnd`): unary negation, `|·|`, `sign` and
   copysign, copying, comparisons (a comparison stores nothing and acts on the values the program
   holds). *Rounded* (exactly one `rnd` after each): the result of every `+`, `−`, `×`, `/` and
   `√` (`√` is `Real.sqrt` followed by one `rnd`), **including arithmetic whose only use is a
   test** — `fl(tol · fl(|h_ii| + |h_{i-1,i-1}|))`, `δ ← fl(tol · ‖A‖_F)`, the `fl(1 − fl(α²))` of
   a positivity check. IEEE negation, `abs` and copysign are exact, and the relational model does
   not know `Rounds x x`, so rounding them would only add spurious error.
2. A division by a unit diagonal inside a factorization is not performed.
3. Loops are `List.foldlM` over `List.finRange n` or an explicit index list, never `for … in
   [a:b]`. A `while` loop is `List.foldlM` over `List.range fuel` with a `done : Bool` field in the
   state: once `done`, a step is the identity; the spec theorem states what holds after
   `min fuel stop` passes (`stop` the book's exit index). The fuel parameter is named `fuel : ℕ`
   and is the **last** explicit argument. Structural or well-founded recursion is reserved for
   genuinely recursive algorithms (Strassen, the FFT, recursive block LU/Cholesky/QR, `LUdisp`).
4. A program that branches on a real test is a `noncomputable def` (through `Real.decidableEq`,
   `Real.decidableLT`).
5. A step the book delegates to an algorithm of a *later* chapter ("compute the SVD", "find
   `λ₊`") is a monadic function parameter, and the spec theorem assumes its specification; a step
   delegated to an *earlier* chapter calls that chapter's program.
6. `fp.IsIdempotent` is assumed **only when the stated constant needs it**: a program whose
   accumulation starts from `0` and whose bound is the book's `γ_n` through a relation that starts
   from the unrounded first term (`RoundsDot`, `RoundsSum`) needs it (the `0 + p` paragraph
   below); a relation that itself absorbs the `0 + p` rounding (`RoundsForwardSubstDot`) needs
   nothing.
7. The monad variable is `M` (`{M : Type → Type} [Monad M]`), never `m`, which is the book's row
   count.
8. Breakdown is not checked in the program (`x / 0 = 0`); the spec theorem carries the hypotheses
   (nonzero pivots, nonsingular leading submatrices, …). Overwrites are state updates
   (`Function.update`, `Matrix.updateRow`); a multi-output state is a structure or a tuple.
9. **Hypotheses of a rounding theorem are about the inputs and the values the program returns**,
   never about intermediate values a run overwrites (a computed pivot `t_j` that is then replaced
   by `√t_j`, a packed factor the program does not return). A composite (factor, then solve) is
   stated nested, one program per quantifier:
   `∀ F ∈ (alg₁ fp.round A).run, hyp F → ∀ x ∈ (alg₂ fp.round F b).run, concl` (the shape of
   `GolubVanLoan.Chapter03.theorem_3_3_2`).
10. **Submatrices are index lists.** A block `A(j:m, k:n)` of the book is the full matrix together
    with the filtered index lists of its rows and columns (`rows : List (Fin m)`,
    `cols : List (Fin n)`), never a copy typed by a loop-dependent `Fin (m - j)`; a subvector
    `x(j:m)` is the full vector with its list of active indices. Helpers operate in place on the
    full matrix over such lists (`GolubVanLoan.Chapter05.houseOn rnd o x`,
    `householderApplyLeft/Right`, `givensApplyLeft/Right`), and a vector-level book algorithm is
    its helper at the full list (`algorithm_5_1_1 rnd x = houseOn rnd (List.finRange (k+1)) x` by
    `rfl`). The backbone relations read such a block through the subtype `{i // i ∈ rows}` or a
    pivot `i : ι` of the full index type.
11. **Exact specs are read off bridges.** When a bridge "every run satisfies the backbone relation
    `R`" exists, the exact spec `_spec` is its instance at `RoundingModel.exact` (`round_exact`
    and `R`'s exact characterization, e.g. `roundsLU_exact_iff`, `mem_run_dotAccum_exact_iff`),
    not a second proof at `Id`.
12. **Node suffixes.** `algorithm_N_M_K` is the program; `_spec` its exact semantics; `_rounds`
    says every run satisfies a backbone relation (`∀ out ∈ run, FloatingPoint.RoundsX …`, the
    bridge); `_mem_run` characterizes the run set (an `↔`) when no backbone relation exists;
    `_rounding` is the book's error bound for every run. A node proving the bound through a
    bridge depends on the `_rounds` node.
13. **One helper family, one reflector-data type.** Updates shared by several algorithms are
    defined once (for Golub–Van Loan: chapter 5), in symmetric pairs `…Left`/`…Right` on index
    lists; Householder data are `List ((Fin m → ℝ) × ℝ)` — pairs `(v, β)` in order of
    application, `v` full length and zero off its active rows — carrying the `β` the program
    returned. A reflector is **never** rebuilt as `β = 2/(vᵀv)` from a stored `v` (when `house`
    returns `β = 0`, the rebuilt `I − 2e₁e₁ᵀ` is not the identity it applied).
14. **Symmetric pairs are separate nodes** (`…Left` and `…Right`, `…_col` and `…_row`, forward and
    backward accumulation), each with its own `_spec`; consumers depend on the half they use.

## The inner-product accumulation

The one accumulation every algorithm uses is here: `dotAccum rnd o x y c` computes
`c + ∑_{k ∈ o} x k * y k` as `c ← fl(c + fl(x k * y k))` ([golub2013matrix] Algorithm 1.1.1 with
`c = 0`, and the inner loops of the row gaxpy and of the `ijk` matrix product).

**The `0 + p` mismatch.** A loop `c = 0; c = c + x₁y₁; …` rounds `0 + fl(x₁y₁)`, while
`RoundsSum` starts from the unrounded first term, and the relational model cannot know that
`0 + p` rounds to `p`. Both readings are provided: unconditionally, a run of `dotAccum` from any
start `c` is within `γ_{n+1} (|c| + ∑|x_k||y_k|)` of `c + ∑ x_k y_k`
(`abs_sub_le_of_mem_run_dotAccum`, paying one extra rounding); under `fp.IsIdempotent` (true of
every concrete format) a run from `c = 0` over any duplicate-free order covering the indices is a
`RoundsDot` (`roundsDot_of_mem_run_dotAccum`), so the bound is Higham's `γ_n`. This is the rigorous
reading of [golub2013matrix] (2.7.9), where `s₁ = x₁y₁(1 + δ₁)` silently assumes the first addition
exact.

**Nonempty run sets.** A theorem about every run is vacuous if the run set is empty, which happens
exactly when some rounding has no admissible value. Over a total model
(`RoundingModel.IsTotal`) `SetM.run_bind_nonempty` and `SetM.run_foldlM_nonempty` give nonempty
run sets, as `dotAccum_run_nonempty` shows.

Complex algorithms (the FFT) take `rnd : ℂ → M ℂ` with the same exact semantics; there is no
complex rounding model.

The `SetM` and `List` lemmas are upstreaming candidates (natural homes `Mathlib.Data.Set.Functor`
and `Mathlib.Data.List.*`); they live here until a second module needs them.
-/

universe u v

/-! ### The run calculus of `SetM` -/

namespace SetM

section Run

variable {α β : Type u}

/-- The run set of `pure a` is `{a}`. -/
@[simp]
theorem mem_run_pure {a b : α} : b ∈ (pure a : SetM α).run ↔ b = a := Iff.rfl

/-- **The run set of a bind**: `b` is a result of `s >>= f` iff it is a result of `f a` for some
result `a` of `s`. In the floating-point reading, "some admissible choice at each step". -/
@[simp]
theorem mem_run_bind {s : SetM α} {f : α → SetM β} {b : β} :
    b ∈ (s >>= f).run ↔ ∃ a ∈ s.run, b ∈ (f a).run := by
  change b ∈ ⋃ i ∈ SetM.run s, SetM.run (f i) ↔ _
  simp

/-- The run set of a map is the image of the run set. -/
@[simp]
theorem mem_run_map {s : SetM α} {f : α → β} {b : β} :
    b ∈ (f <$> s).run ↔ ∃ a ∈ s.run, f a = b := by
  rw [← bind_pure_comp, mem_run_bind]
  simp [eq_comm]

/-- A bind has a result when its first step has one and every result of the first step leads to
a result of the second. -/
theorem run_bind_nonempty {s : SetM α} {f : α → SetM β} (hs : s.run.Nonempty)
    (hf : ∀ a ∈ s.run, (f a).run.Nonempty) : (s >>= f).run.Nonempty := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hf a ha
  exact ⟨b, mem_run_bind.2 ⟨a, ha, hb⟩⟩

/-- A loop whose every step has a result, from every state, has a result. -/
theorem run_foldlM_nonempty {γ : Type*} {f : β → γ → SetM β} {l : List γ}
    (hf : ∀ b a, a ∈ l → (f b a).run.Nonempty) (b₀ : β) : (l.foldlM f b₀).run.Nonempty := by
  induction l generalizing b₀ with
  | nil => exact ⟨b₀, mem_run_pure.2 rfl⟩
  | cons a l ih =>
    rw [List.foldlM_cons]
    exact run_bind_nonempty (hf b₀ a List.mem_cons_self) fun b _ =>
      ih (fun b a' ha' => hf b a' (List.mem_cons_of_mem _ ha')) b

end Run

end SetM

/-- An `if` between two `pure`s is a `pure` of an `if`: the exact-semantics collapse of a program
that branches on a computed value. -/
theorem ite_pure {f : Type u → Type v} [Pure f] {α : Type u} (c : Prop) [Decidable c] (a b : α) :
    (if c then pure a else pure b : f α) = pure (if c then a else b) :=
  (apply_ite pure c a b).symm

/-! ### The relational fold -/

namespace List

/-- **The relational left fold**: `FoldlRel R a l b` says that `b` is reachable from `a` by
stepping through the list `l` with the relation `R`, one element at a time from the left. It is
to a relation what `List.foldl` is to a function. -/
inductive FoldlRel {α β : Type*} (R : β → α → β → Prop) : β → List α → β → Prop
  /-- Stepping through the empty list stays put. -/
  | nil (b : β) : FoldlRel R b [] b
  /-- One step with `R`, followed by the rest of the list. -/
  | cons {b c d : β} {a : α} {l : List α} (h : R b a c) (t : FoldlRel R c l d) :
      FoldlRel R b (a :: l) d

variable {α β : Type*} {R : β → α → β → Prop}

/-- A relational fold over the empty list stays put. -/
@[simp]
theorem foldlRel_nil_iff {a b : β} : FoldlRel R a [] b ↔ b = a :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; exact .nil b⟩

/-- A relational fold over `x :: l` is one step followed by a fold over `l`. -/
@[simp]
theorem foldlRel_cons_iff {a b : β} {x : α} {l : List α} :
    FoldlRel R a (x :: l) b ↔ ∃ c, R a x c ∧ FoldlRel R c l b :=
  ⟨fun h => by cases h with | cons h t => exact ⟨_, h, t⟩, fun ⟨_, h, t⟩ => .cons h t⟩

/-- A relational fold over a concatenation passes through an intermediate state. -/
theorem FoldlRel.append {a b : β} {l₁ l₂ : List α} :
    FoldlRel R a (l₁ ++ l₂) b ↔ ∃ c, FoldlRel R a l₁ c ∧ FoldlRel R c l₂ b := by
  induction l₁ generalizing a with
  | nil => simp
  | cons x l₁ ih =>
    simp only [cons_append, foldlRel_cons_iff, ih]
    exact ⟨fun ⟨c, h, d, h₁, h₂⟩ => ⟨d, ⟨c, h, h₁⟩, h₂⟩,
      fun ⟨d, ⟨c, h, h₁⟩, h₂⟩ => ⟨c, h, d, h₁, h₂⟩⟩

/-! ### Folds in exact arithmetic -/

/-- A running sum `c + f k₁ + f k₂ + …` is `c` plus the sum of the mapped list. -/
theorem foldl_add_eq_add_sum_map {M : Type*} [AddMonoid M] (f : α → M) (l : List α) (c : M) :
    l.foldl (fun c k => c + f k) c = c + (l.map f).sum := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp [ih, add_assoc]

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

end List

/-! ### Loops in the relational semantics -/

namespace SetM

section Loops

variable {α : Type*} {β : Type u}

/-- **The run set of a loop is the relational fold of its body.** -/
theorem mem_run_foldlM_iff_foldlRel {f : β → α → SetM β} {l : List α} {a b : β} :
    b ∈ (l.foldlM f a).run ↔ List.FoldlRel (fun c x c' => c' ∈ (f c x).run) a l b := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih]

/-- **The Hoare rule of a loop**, with the invariant indexed by the processed prefix: if `I [] a`,
and a step on the element `x` that follows a prefix `p` maps states satisfying `I p` to states
satisfying `I (p ++ [x])`, then every result of the loop satisfies `I l`. -/
theorem forall_mem_run_foldlM {f : β → α → SetM β} {l : List α} {a : β} (I : List α → β → Prop)
    (h0 : I [] a)
    (hstep : ∀ p x q, l = p ++ x :: q → ∀ c, I p c → ∀ c' ∈ (f c x).run, I (p ++ [x]) c') :
    ∀ b ∈ (l.foldlM f a).run, I l b := by
  suffices H : ∀ (r p : List α) (c : β), p ++ r = l → I p c → ∀ b ∈ (r.foldlM f c).run, I l b
    from H l [] a rfl h0
  intro r
  induction r with
  | nil =>
    rintro p c rfl hc b hb
    rw [List.foldlM_nil, mem_run_pure] at hb
    subst hb
    simpa using hc
  | cons x r ih =>
    rintro p c rfl hc b hb
    rw [List.foldlM_cons, mem_run_bind] at hb
    obtain ⟨c', hc', hb⟩ := hb
    exact ih (p ++ [x]) c' (by simp) (hstep p x r rfl c hc c' hc') b hb

/-- **The Hoare rule of a `finRange` loop**, with the invariant indexed by the step count: if
`I 0 a` and step `k` maps states satisfying `I k` to states satisfying `I (k + 1)`, every result
of the loop satisfies `I n`. -/
theorem forall_mem_run_foldlM_finRange {n : ℕ} {f : β → Fin n → SetM β} {a : β}
    (I : ℕ → β → Prop) (h0 : I 0 a)
    (hstep : ∀ (k : Fin n) (c : β), I k c → ∀ c' ∈ (f c k).run, I (k + 1) c') :
    ∀ b ∈ ((List.finRange n).foldlM f a).run, I n b := by
  have H := forall_mem_run_foldlM (l := List.finRange n) (f := f) (a := a)
    (fun p c => I p.length c) h0 fun p x q hl c hc c' hc' => by
      have hlt : p.length < (List.finRange n).length := by rw [hl]; simp
      have hx : ((List.finRange n)[p.length]'hlt : ℕ) = p.length := by simp
      have hx' : (List.finRange n)[p.length]'hlt = x := by
        simp only [hl, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
      rw [hx'] at hx
      simpa [hx] using hstep x c (hx ▸ hc) c' hc'
  simpa using H

/-- **Loop interchange in the relational model.** If every step of a loop over a state `ι → β` acts
entrywise with independent roundings — the results of step `a` from `y` are exactly the states
whose entry `i` is a result of `g a i (y i)`, for every `i` — then the run set of the loop is the
product of the run sets of the per-entry loops. -/
theorem mem_run_foldlM_of_pi {ι : Type u} (f : (ι → β) → α → SetM (ι → β))
    (g : α → ι → β → SetM β) (hf : ∀ y a y', y' ∈ (f y a).run ↔ ∀ i, y' i ∈ (g a i (y i)).run)
    (l : List α) (y₀ y : ι → β) :
    y ∈ (l.foldlM f y₀).run ↔ ∀ i, y i ∈ (l.foldlM (fun b a => g a i b) (y₀ i)).run := by
  induction l generalizing y₀ with
  | nil => simp only [List.foldlM_nil, mem_run_pure]; exact funext_iff
  | cons a l ih =>
    simp only [List.foldlM_cons, mem_run_bind, ih, hf]
    constructor
    · rintro ⟨z, hz, hy⟩ i; exact ⟨z i, hz i, hy i⟩
    · intro h
      choose z hz hy using h
      exact ⟨z, hz, hy⟩

/-- **A loop that accumulates into one entry.** A loop that rewrites the single index `i` of a
state `ι → β`, each time from its current value, has as results the updates of the initial state
at `i` by the results of the loop run on entry `i` alone. The relational twin of
`List.foldl_update_self`. -/
theorem mem_run_foldlM_update_self_iff {ι : Type u} [DecidableEq ι] (g : α → β → SetM β) (i : ι)
    (l : List α) (y₀ y : ι → β) :
    y ∈ (l.foldlM (fun (y : ι → β) a => do
        let b ← g a (y i); pure (Function.update y i b)) y₀).run ↔
      y = Function.update y₀ i (y i) ∧ y i ∈ (l.foldlM (fun b a => g a b) (y₀ i)).run := by
  induction l generalizing y₀ with
  | nil =>
    simp only [List.foldlM_nil, mem_run_pure]
    constructor
    · rintro rfl; simp
    · rintro ⟨h1, h2⟩; rw [h1, h2]; simp
  | cons a l ih =>
    simp only [List.foldlM_cons, mem_run_bind, mem_run_pure, ih]
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, h1, h2⟩
      rw [Function.update_idem] at h1
      rw [Function.update_self] at h2
      exact ⟨h1, b, hb, h2⟩
    · rintro ⟨h1, b, hb, h2⟩
      exact ⟨_, ⟨b, hb, rfl⟩, by rwa [Function.update_idem], by rwa [Function.update_self]⟩

/-- The auxiliary form of `mem_run_foldlM_update_of_nodup`, with a frozen set `S ⊇ l` so that the
induction hypothesis applies to the tail. -/
private theorem mem_run_foldlM_update_aux {ι : Type u} [DecidableEq ι]
    (g : ι → β → (ι → β) → SetM β) (S : Set ι) (l : List ι) (hl : l.Nodup)
    (hlS : ∀ a ∈ l, a ∈ S)
    (hg : ∀ a ∈ l, ∀ b (y y' : ι → β), (∀ i, i ∉ S → y i = y' i) → g a b y = g a b y')
    (y₀ y : ι → β) :
    y ∈ (l.foldlM (fun (y : ι → β) a => do
        let b ← g a (y a) y; pure (Function.update y a b)) y₀).run ↔
      (∀ i, i ∉ l → y i = y₀ i) ∧ ∀ i ∈ l, y i ∈ (g i (y₀ i) y₀).run := by
  induction l generalizing y₀ with
  | nil =>
    simp only [List.foldlM_nil, mem_run_pure, List.not_mem_nil, not_false_eq_true,
      forall_const, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨fun h _ => by rw [h], fun h => funext h⟩
  | cons a l ih =>
    rcases List.nodup_cons.1 hl with ⟨ha, hl'⟩
    have ih' := fun y₀ => ih hl' (fun c hc => hlS c (List.mem_cons_of_mem _ hc))
      (fun c hc => hg c (List.mem_cons_of_mem _ hc)) y₀
    simp only [List.foldlM_cons, mem_run_bind, mem_run_pure]
    -- the steps after the first read the updated state as they would read the initial one
    have key : ∀ b, ∀ c ∈ l, g c ((Function.update y₀ a b) c) (Function.update y₀ a b) =
        g c (y₀ c) y₀ := by
      intro b c hc
      have hca : c ≠ a := fun e => ha (e ▸ hc)
      rw [Function.update_of_ne hca]
      exact hg c (List.mem_cons_of_mem _ hc) _ _ _ fun i hi => by
        have : i ≠ a := fun e => hi (e ▸ hlS a List.mem_cons_self)
        rw [Function.update_of_ne this]
    constructor
    · rintro ⟨z, ⟨b, hb, rfl⟩, hy⟩
      rw [ih'] at hy
      obtain ⟨hout, hin⟩ := hy
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have hia : i ≠ a := fun e => hi (e ▸ List.mem_cons_self)
        rw [hout i fun h => hi (List.mem_cons_of_mem _ h), Function.update_of_ne hia]
      · rcases List.mem_cons.1 hi with rfl | hi
        · rw [hout i ha, Function.update_self]; exact hb
        · have := hin i hi; rwa [key b i hi] at this
    · rintro ⟨hout, hin⟩
      refine ⟨Function.update y₀ a (y a), ⟨y a, hin a List.mem_cons_self, rfl⟩, ?_⟩
      rw [ih']
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · by_cases hia : i = a
        · subst hia; rw [Function.update_self]
        · rw [Function.update_of_ne hia]
          exact hout i fun h => (List.mem_cons.1 h).elim hia hi
      · rw [key (y a) i hi]; exact hin i (List.mem_cons_of_mem _ hi)

/-- **One entry per step.** Over a duplicate-free index list `l`, a loop whose step `a` rewrites
only entry `a` — from its current value `y a` and from entries outside `l` — writes each entry of
`l` once, from its initial value and the frozen entries, so its run set is the product of the
per-entry run sets: `y` is a result iff it agrees with `y₀` off `l` and each `y i`, `i ∈ l`, is a
result of the step `g i (y₀ i) y₀`. The loops of a saxpy, of a column gaxpy, of column-oriented
substitution and of the rank-one updates of LU and Cholesky have this shape. -/
theorem mem_run_foldlM_update_of_nodup {ι : Type u} [DecidableEq ι]
    (g : ι → β → (ι → β) → SetM β) (l : List ι) (hl : l.Nodup)
    (hg : ∀ a ∈ l, ∀ b (y y' : ι → β), (∀ i, i ∉ l → y i = y' i) → g a b y = g a b y')
    (y₀ y : ι → β) :
    y ∈ (l.foldlM (fun (y : ι → β) a => do
        let b ← g a (y a) y; pure (Function.update y a b)) y₀).run ↔
      (∀ i, i ∉ l → y i = y₀ i) ∧ ∀ i ∈ l, y i ∈ (g i (y₀ i) y₀).run :=
  mem_run_foldlM_update_aux g {i | i ∈ l} l hl (fun _ h => h) hg y₀ y

end Loops

end SetM

/-! ### The rounding hook -/

namespace FloatingPoint

section Hook

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The rounding hook of the relational model**: the set of admissible roundings of `x`, in
Mathlib's `SetM` monad. An algorithm written with a hook `rnd : K → M K` has its floating-point
semantics at `M := SetM`, `rnd := fp.round`. -/
def RoundingModel.round (fp : RoundingModel K) (x : K) : SetM K := {y | fp.Rounds x y}

/-- The results of the hook are the admissible roundings. -/
@[simp]
theorem RoundingModel.mem_run_round {fp : RoundingModel K} {x y : K} :
    y ∈ (fp.round x).run ↔ fp.Rounds x y := Iff.rfl

/-- In the exact model the hook is `pure`, so a program run in the exact model has the single
result of its exact semantics. -/
theorem RoundingModel.round_exact : (RoundingModel.exact K).round = pure := rfl

/-- Over a total model the hook always has a result. -/
theorem RoundingModel.run_round_nonempty {fp : RoundingModel K} (hfp : fp.IsTotal) (x : K) :
    (fp.round x).run.Nonempty :=
  hfp x

/-- A running sum is the relational fold of the rounded addition. -/
theorem roundsSumFrom_iff_foldlRel {fp : RoundingModel K} {s t : K} {l : List K} :
    RoundsSumFrom fp s l t ↔ List.FoldlRel (fun s x t => fp.Rounds (s + x) t) s l t := by
  induction l generalizing s with
  | nil => exact ⟨fun h => by cases h; exact .nil _, fun h => by cases h; exact .nil _⟩
  | cons x l ih =>
    rw [List.foldlRel_cons_iff]
    exact ⟨fun h => by cases h with | cons ht hr => exact ⟨_, ht, ih.1 hr⟩,
      fun ⟨_, ht, hr⟩ => .cons ht (ih.2 hr)⟩

end Hook

/-! ### The inner-product accumulation -/

section DotAccum

variable {K : Type u}

/-- **The inner-product accumulation**, generic in the monad: `dotAccum rnd o x y c` computes
`c + ∑_{k ∈ o} x k * y k` as `c ← rnd (c + rnd (x k * y k))` for `k` in the order of the list
`o` ([golub2013matrix] Algorithm 1.1.1 with `c = 0`; the inner loops of the row gaxpy and of the
`ijk` matrix product start from `c = y i`, resp. `c = C i j`). -/
def dotAccum [Add K] [Mul K] {M : Type u → Type v} [Monad M] (rnd : K → M K) {ι : Type*}
    (o : List ι) (x y : ι → K) (c : K) : M K :=
  o.foldlM (fun c k => do rnd (c + (← rnd (x k * y k)))) c

/-- With the hook `pure`, in any lawful monad, the accumulation is the exact running sum. -/
theorem dotAccum_pure [AddMonoid K] [Mul K] {M : Type u → Type v} [Monad M] [LawfulMonad M]
    {ι : Type*} (o : List ι) (x y : ι → K) (c : K) :
    dotAccum (M := M) pure o x y c = pure (c + (o.map fun k => x k * y k).sum) := by
  unfold dotAccum
  simp only [pure_bind, List.foldlM_pure]
  rw [List.foldl_add_eq_add_sum_map]

/-- **The exact semantics of the accumulation**: `c + ∑_{k ∈ o} x k * y k`. -/
theorem dotAccum_id [AddMonoid K] [Mul K] {ι : Type*} (o : List ι) (x y : ι → K) (c : K) :
    Id.run (dotAccum (M := Id) pure o x y c) = c + (o.map fun k => x k * y k).sum := by
  rw [dotAccum_pure]
  rfl

/-- The exact accumulation over `List.finRange n` is `c + x ⬝ᵥ y`. -/
theorem dotAccum_id_finRange [AddCommMonoid K] [Mul K] {n : ℕ} (x y : Fin n → K) (c : K) :
    Id.run (dotAccum (M := Id) pure (List.finRange n) x y c) = c + x ⬝ᵥ y := by
  rw [dotAccum_id, dotProduct, Fin.sum_univ_def]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {ι : Type*}

/-- Over a total model the accumulation has a result, so theorems about its every run are not
vacuous. -/
theorem dotAccum_run_nonempty {fp : RoundingModel K} (hfp : fp.IsTotal) (o : List ι)
    (x y : ι → K) (c : K) : (dotAccum fp.round o x y c).run.Nonempty :=
  SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
    (RoundingModel.run_round_nonempty hfp _) fun _ _ => RoundingModel.run_round_nonempty hfp _) c

/-- **The bridge from the accumulation to the relational sum**: a result of `dotAccum` in a model
is a running sum from the unrounded start `c` of admissible roundings of the products, one per
entry of `o` (so `o` may repeat indices). -/
theorem mem_run_dotAccum_iff {fp : RoundingModel K} {o : List ι} {x y : ι → K} {c s : K} :
    s ∈ (dotAccum fp.round o x y c).run ↔
      ∃ ps : List K, List.Forall₂ (fun k p => fp.Rounds (x k * y k) p) o ps ∧
        RoundsSumFrom fp c ps s := by
  unfold dotAccum
  induction o generalizing c with
  | nil =>
    simp only [List.foldlM_nil, SetM.mem_run_pure, List.forall₂_nil_left_iff, exists_eq_left]
    exact ⟨fun h => h ▸ .nil _, fun h => by cases h; rfl⟩
  | cons k o ih =>
    simp only [List.foldlM_cons, SetM.mem_run_bind, RoundingModel.mem_run_round, ih,
      List.forall₂_cons_left_iff]
    constructor
    · rintro ⟨t, ⟨p, hp, ht⟩, ps, hps, hsum⟩
      exact ⟨p :: ps, ⟨p, ps, hp, hps, rfl⟩, .cons ht hsum⟩
    · rintro ⟨_, ⟨p, ps, hp, hps, rfl⟩, (_ | ⟨ht, hsum⟩)⟩
      exact ⟨_, ⟨p, hp, ht⟩, ps, hps, hsum⟩

/-- **The accumulation in the exact model** is the exact running sum: the lemma from which the
exact specification of every program built on `dotAccum` is read off its bridge. -/
theorem mem_run_dotAccum_exact_iff {o : List ι} {x y : ι → K} {c s : K} :
    s ∈ (dotAccum (RoundingModel.exact K).round o x y c).run ↔
      s = c + (o.map fun k => x k * y k).sum := by
  rw [RoundingModel.round_exact, dotAccum_pure, SetM.mem_run_pure]

/-- Values related one by one to a duplicate-free list of indices are the values of a function on
the indices. -/
private theorem exists_forall_map_eq_of_forall₂ {β : Type*} {R : ι → β → Prop} {o : List ι}
    (ho : o.Nodup) {ps : List β} (h : List.Forall₂ R o ps) (d : ι → β) :
    ∃ p : ι → β, (∀ i ∈ o, R i (p i)) ∧ o.map p = ps := by
  classical
  induction h with
  | nil => exact ⟨d, by simp, rfl⟩
  | @cons a b o ps hab _ ih =>
    rcases List.nodup_cons.1 ho with ⟨ha, ho'⟩
    obtain ⟨p, hp, hmap⟩ := ih ho'
    refine ⟨Function.update p a b, fun i hi => ?_, ?_⟩
    · rcases List.mem_cons.1 hi with rfl | hi
      · rwa [Function.update_self]
      · rw [Function.update_of_ne fun (e : i = a) => ha (e ▸ hi)]
        exact hp i hi
    · rw [List.map_cons, Function.update_self, ← hmap]
      congr 1
      exact List.map_congr_left fun i hi =>
        Function.update_of_ne (fun (e : i = a) => ha (e ▸ hi)) _ _

/-- **The accumulation from `0` is Higham's inner product when rounding fixes its outputs**: over
an idempotent model, a result of `dotAccum` from `c = 0` along a duplicate-free order covering the
indices is a `RoundsDot`, since the first addition `0 + fl(x₁ y₁)` is then exact. Consequently
`|s - x ⬝ᵥ y| ≤ γ_n |x| ⬝ᵥ |y|` (`abs_sub_le_of_roundsDot`), the rigorous form of
[golub2013matrix] (2.7.11)–(2.7.12). -/
theorem roundsDot_of_mem_run_dotAccum {fp : RoundingModel K} (hfp : fp.IsIdempotent)
    {o : List ι} (ho : o.Nodup) (hmem : ∀ i, i ∈ o) {x y : ι → K} {s : K}
    (h : s ∈ (dotAccum fp.round o x y 0).run) : RoundsDot fp x y s := by
  obtain ⟨ps, hps, hsum⟩ := mem_run_dotAccum_iff.1 h
  obtain ⟨p, hp, rfl⟩ := exists_forall_map_eq_of_forall₂ ho hps 0
  refine ⟨o, p, ho, hmem, fun i => hp i (hmem i), ?_⟩
  cases o with
  | nil =>
    cases hsum
    exact roundsSum_nil.2 rfl
  | cons k o =>
    rcases hsum with _ | ⟨ht, hr⟩
    rw [zero_add] at ht
    obtain rfl := hfp (hp k List.mem_cons_self) ht
    exact hr

/-- The two list-level facts behind `abs_sub_le_of_mem_run_dotAccum`: the rounded products differ
from the exact ones by at most `u ∑ |x_k| |y_k|` in sum, and are at most `(1 + u) ∑ |x_k| |y_k|`
in absolute value. -/
private theorem forall₂_rounds_mul_bounds {fp : RoundingModel K} {x y : ι → K} {o : List ι}
    {ps : List K} (h : List.Forall₂ (fun k p => fp.Rounds (x k * y k) p) o ps) :
    |ps.sum - (o.map fun k => x k * y k).sum| ≤ fp.u * (o.map fun k => |x k| * |y k|).sum ∧
      (ps.map (|·|)).sum ≤ (1 + fp.u) * (o.map fun k => |x k| * |y k|).sum := by
  induction h with
  | nil => simp
  | @cons k p o ps hkp _ ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hk : |p - x k * y k| ≤ fp.u * (|x k| * |y k|) := by
      rw [← abs_mul]; exact fp.abs_sub_le hkp
    have hp : |p| ≤ (1 + fp.u) * (|x k| * |y k|) := by
      have h1 : |p| ≤ |p - x k * y k| + |x k * y k| := by
        simpa using abs_add_le (p - x k * y k) (x k * y k)
      rw [abs_mul] at h1
      linarith
    simp only [List.sum_cons, List.map_cons]
    refine ⟨?_, by linarith⟩
    calc |p + ps.sum - (x k * y k + (o.map fun k => x k * y k).sum)|
        = |(p - x k * y k) + (ps.sum - (o.map fun k => x k * y k).sum)| := by ring_nf
      _ ≤ |p - x k * y k| + |ps.sum - (o.map fun k => x k * y k).sum| := abs_add_le _ _
      _ ≤ fp.u * (|x k| * |y k|) + fp.u * (o.map fun k => |x k| * |y k|).sum :=
          add_le_add hk ih₁
      _ = fp.u * (|x k| * |y k| + (o.map fun k => |x k| * |y k|).sum) := by ring

/-- **Unconditional bound for an accumulation onto any start** ([higham2002accuracy] for
`fl(c + xᵀy)`): a result of `dotAccum` over `n` terms from the start `c` is within
`γ_{n+1} (|c| + ∑ |x_k| |y_k|)` of `c + ∑ x_k y_k`. With `c = 0` this is the `γ_{n+1}` price of
not knowing that `0 + p` is exact; over an idempotent model `roundsDot_of_mem_run_dotAccum`
recovers `γ_n`. -/
theorem abs_sub_le_of_mem_run_dotAccum {fp : RoundingModel K} {o : List ι} {x y : ι → K}
    {c s : K} (hlu : ((o.length + 1 : ℕ) : K) * fp.u < 1)
    (h : s ∈ (dotAccum fp.round o x y c).run) :
    |s - (c + (o.map fun k => x k * y k).sum)|
      ≤ gamma fp.u (o.length + 1) * (|c| + (o.map fun k => |x k| * |y k|).sum) := by
  obtain ⟨ps, hps, hsum⟩ := mem_run_dotAccum_iff.1 h
  have hlen : ps.length = o.length := hps.length_eq.symm
  have hu0 := fp.u_nonneg
  have hcast : ((o.length + 1 : ℕ) : K) * fp.u = (o.length : K) * fp.u + fp.u := by
    push_cast; ring
  have hn0 : (0 : K) ≤ (o.length : K) * fp.u := by positivity
  have hn : (o.length : K) * fp.u < 1 := by linarith
  have hu1 : fp.u < 1 := by linarith
  have hsf := abs_sub_le_of_roundsSumFrom hu1 hsum (by rw [hlen]; exact hn)
  rw [hlen] at hsf
  obtain ⟨hdiff, habs⟩ := forall₂_rounds_mul_bounds hps
  set A := (o.map fun k => |x k| * |y k|).sum
  set P := (o.map fun k => x k * y k).sum
  have hA : 0 ≤ A := List.sum_nonneg fun a ha => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 ha
    positivity
  have hg : 0 ≤ gamma fp.u o.length := gamma_nonneg hu0 hn
  have hstep := gamma_mul_one_add_add_le hu0 hu1 hlu
  have hmono := gamma_mono hu0 (Nat.le_succ o.length) hlu
  calc |s - (c + P)| ≤ |s - (c + ps.sum)| + |ps.sum - P| := by
        have : s - (c + P) = (s - (c + ps.sum)) + (ps.sum - P) := by ring
        rw [this]; exact abs_add_le _ _
    _ ≤ gamma fp.u o.length * (|c| + (ps.map (|·|)).sum) + fp.u * A := add_le_add hsf hdiff
    _ ≤ gamma fp.u o.length * (|c| + (1 + fp.u) * A) + fp.u * A := by gcongr
    _ = gamma fp.u o.length * |c| + (gamma fp.u o.length * (1 + fp.u) + fp.u) * A := by ring
    _ ≤ gamma fp.u (o.length + 1) * |c| + gamma fp.u (o.length + 1) * A := by
        gcongr
    _ = gamma fp.u (o.length + 1) * (|c| + A) := by ring

end DotAccum

end FloatingPoint
