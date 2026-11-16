/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Set.Functor
import Mathlib.LinearAlgebra.Matrix.RowCol
import Numlib.Data.List.Fold
import Numlib.FloatingPoint.InnerProduct

/-!
# Algorithms as programs with a rounding hook

This module gives one definition of a numerical algorithm both its exact meaning and its
floating-point meaning. An algorithm is written once, in the operation order of its textbook,
generic in a monad `M` and a hook `rnd : K → M K` through which every arithmetic result passes. The
exact semantics takes `M := Id` and `rnd := pure`. The floating-point semantics takes `M := SetM`
and `rnd := fp.round` for a rounding model `fp`, where `fp.round x` is the set of admissible
roundings of $x$. The set of runs of a program is then the set of all results of all admissible
rounding choices, and a rounding theorem is a statement about every element of it:
`∀ out ∈ (alg fp.round …).run, …`. In the exact model `FloatingPoint.RoundingModel.exact` the hook
is `pure`, so an exact specification follows from a theorem proved for every model.

The module proves the rules for reasoning about sets of runs: the run set of a bind, the Hoare rules
of a loop, and product formulas for the run set of a loop that writes one entry of a vector or
matrix per step. It defines the two accumulations that the algorithms of the library use: the
inner-product accumulation $c \leftarrow fl(c + fl(x_k y_k))$, which follows Algorithm 1.1.1 of
[golub2013matrix], and the running difference $t \leftarrow fl(t - fl(a_k b_k))$, which is the loop
of Lemma 8.4 of [higham2002accuracy]. Over a duplicate-free order, a run of either accumulation
satisfies the corresponding relation of `Numlib.FloatingPoint.InnerProduct`, and the error bounds
follow from that relation. Over a total model every run set is nonempty, so a theorem about every
run is not vacuous.

## Main definitions

* `FloatingPoint.RoundingModel.round`: the rounding hook of a rounding model, the set of admissible
  roundings of $x$.
* `FloatingPoint.dotAccum`: the inner-product accumulation $c + \sum_{k \in o} x_k y_k$, one
  rounding per product and per addition.
* `FloatingPoint.runningDiff`: the running difference $c - \sum_{k \in o} a_k b_k$, one rounding per
  product and per subtraction.

## Main results

* `SetM.mem_run_bind`: a result of `s >>= f` is a result of `f a` for some result `a` of `s`.
* `SetM.forall_mem_run_foldlM`: the Hoare rule of a loop, with an invariant indexed by the processed
  prefix.
* `SetM.mem_run_foldlM_update_of_nodup`: over a duplicate-free index list, the run set of a loop
  that writes one entry per step is the product of the per-entry run sets.
* `FloatingPoint.RoundingModel.round_exact`: the hook of the exact model is `pure`.
* `FloatingPoint.mem_run_dotAccum_iff`: a result of the inner-product accumulation is an admissible
  running sum of admissible roundings of the products.
* `FloatingPoint.roundsDot_of_mem_run_dotAccum`: over an idempotent model, a run of the accumulation
  from $0$ over a duplicate-free order of all indices is an admissible inner product.
* `FloatingPoint.abs_sub_le_of_mem_run_dotAccum`: a run of the accumulation over $n$ terms from the
  start $c$ is within $\gamma_{n+1} (|c| + \sum_k |x_k| |y_k|)$ of $c + \sum_k x_k y_k$.
* `FloatingPoint.mem_run_runningDiff_iff`: over a duplicate-free order, the results of the running
  difference are exactly the admissible running differences.

## Conventions

Every surface algorithm follows the conventions below. The same list, with the same numbers, is in
the module doc comment of `NumlibSurface.GolubVanLoan`.

1. **What is rounded.** The following are exact, and do not pass through `rnd`: unary negation, the
   absolute value, `sign` and copysign, copying, and comparisons (a comparison stores nothing and
   acts on the values that the program holds). The result of every $+$, $-$, $\times$, $/$ and
   $\sqrt{\cdot}$ is rounded, with exactly one `rnd` after each operation ($\sqrt{\cdot}$ is
   `Real.sqrt` followed by one `rnd`). This includes arithmetic whose only use is a test, such as
   $fl(\mathrm{tol} \cdot fl(|h_{ii}| + |h_{i-1,i-1}|))$, $\delta \leftarrow fl(\mathrm{tol} \cdot
   \|A\|_F)$, or the $fl(1 - fl(\alpha^2))$ of a positivity check. IEEE negation, absolute value and
   copysign are exact, and the relational model does not know that $x$ rounds to $x$, so rounding
   them would only add spurious error.
2. A division by a unit diagonal inside a factorization is not performed.
3. Loops are `List.foldlM` over `List.finRange n` or an explicit index list, never `for … in [a:b]`.
   A `while` loop is `List.foldlM` over `List.range fuel` with a field `done : Bool` in the state:
   once `done` holds, a step is the identity, and the specification theorem states what holds after
   `min fuel stop` passes, where `stop` is the exit index of the book. The fuel parameter is named
   `fuel : ℕ` and is the last explicit argument. Structural or well-founded recursion is reserved
   for genuinely recursive algorithms (Strassen, the FFT, recursive block LU, Cholesky and QR,
   `LUdisp`).
4. A program that branches on a real test is a `noncomputable def` (through `Real.decidableEq` and
   `Real.decidableLT`).
5. A step that the book delegates to an algorithm of a later chapter ("compute the SVD", "find
   $\lambda_+$") is a monadic function parameter, and the specification theorem assumes its
   specification. A step delegated to an earlier chapter calls the program of that chapter.
6. `fp.IsIdempotent` is assumed only when the stated constant needs it. A program whose accumulation
   starts from $0$, and whose bound is the constant $\gamma_n$ of the book through a relation that
   starts from the unrounded first term (`FloatingPoint.RoundsDot`, `FloatingPoint.RoundsSum`),
   needs it; see the section on the inner-product accumulation below. A relation that itself absorbs
   the rounding of $0 + p$ (`FloatingPoint.RoundsForwardSubstDot`) needs nothing.
7. The monad variable is `M` (`{M : Type → Type} [Monad M]`), never `m`, which is the row count of
   the book.
8. Breakdown is not checked in the program (`x / 0 = 0`). The specification theorem carries the
   hypotheses (nonzero pivots, nonsingular leading submatrices, …). Overwrites are state updates
   (`Function.update`, `Matrix.updateRow`), and a state with several outputs is a structure or a
   tuple.
9. **The hypotheses of a rounding theorem are about the inputs and the values that the program
   returns**, never about intermediate values that a run overwrites (such as a computed pivot $t_j$
   that is then replaced by $\sqrt{t_j}$, or a packed factor that the program does not return). A
   composite algorithm (factor, then solve) is stated nested, with one program per quantifier: `∀ F
   ∈ (alg₁ fp.round A).run, hyp F → ∀ x ∈ (alg₂ fp.round F b).run, concl`, as in
   `GolubVanLoan.Chapter03.theorem_3_3_2`.
10. **Submatrices are index lists.** A block $A(j{:}m, k{:}n)$ of the book is the full matrix
    together with the filtered index lists of its rows and columns (`rows : List (Fin m)`,
    `cols : List (Fin n)`), never a copy typed by a loop-dependent `Fin (m - j)`. A subvector
    $x(j{:}m)$ is the full vector with its list of active indices. Helpers operate in place on the
    full matrix over such lists (`GolubVanLoan.Chapter05.houseOn`,
    `GolubVanLoan.Chapter05.householderApplyLeft`, `GolubVanLoan.Chapter05.householderApplyRight`,
    `GolubVanLoan.Chapter05.givensApplyLeft`, `GolubVanLoan.Chapter05.givensApplyRight`), and a
    vector-level algorithm of the book is its helper at the full list (`algorithm_5_1_1 rnd x =
    houseOn rnd (List.finRange (k+1)) x` holds by `rfl`). The backbone relations read such a block
    through the subtype `{i // i ∈ rows}` or through a pivot `i : ι` of the full index type.
11. **Exact specifications are read off bridges.** When a bridge "every run satisfies the backbone
    relation `R`" exists, the exact specification `_spec` is its instance at
    `FloatingPoint.RoundingModel.exact`, through `FloatingPoint.RoundingModel.round_exact` and the
    exact characterization of `R` (for example `FloatingPoint.roundsLU_exact_iff` or
    `FloatingPoint.mem_run_dotAccum_exact_iff`), and not a second proof at `Id`.
12. **Suffixes of declaration names.** `algorithm_N_M_K` is the program; `_spec` is its exact
    semantics; `_rounds` says that every run satisfies a backbone relation
    (`∀ out ∈ run, FloatingPoint.RoundsX …`, the bridge); `_mem_run` characterizes the run set (an
    `↔`) when no backbone relation exists; `_rounding` is the error bound of the book for every run.
    A declaration that proves the bound through a bridge depends on the `_rounds` declaration.
13. **One helper family, one type of reflector data.** Updates shared by several algorithms are
    defined once (for Golub and Van Loan: in chapter 5), in symmetric pairs `…Left` and `…Right` on
    index lists. Householder data are `List ((Fin m → ℝ) × ℝ)`: pairs $(v, \beta)$ in order of
    application, with $v$ of full length and zero off its active rows, carrying the $\beta$ that the
    program returned. A reflector is never rebuilt as $\beta = 2/(v^T v)$ from a stored $v$: when
    `house` returns $\beta = 0$, the rebuilt $I - 2 e_1 e_1^T$ is not the identity that it applied.
14. **Symmetric pairs are separate declarations** (`…Left` and `…Right`, `…_col` and `…_row`,
    forward and backward accumulation), each with its own `_spec`. A user depends on the half that
    it uses.

## Implementation notes

* In the exact semantics, `List.idRun_foldlM` of Lean core turns a program into a `List.foldl`. The
  lemmas of `Numlib.Data.List.Fold` turn folds into sums (`List.foldl_add_eq_add_sum_map`),
  entrywise loops into per-entry folds (`List.foldl_apply_of_pi`, `List.foldl_update_self`), and
  loops that write one entry per step into simultaneous updates (`List.foldl_update_of_nodup`,
  `List.foldl_update_apply_of_pairwise`), and they give the invariants of loops
  (`List.foldl_prefix_induction`, `List.idRun_foldlM_induction`).
* In the floating-point semantics, `SetM.mem_run_bind` reads as "some admissible choice at each
  step". `SetM.forall_mem_run_foldlM` and `SetM.forall_mem_run_foldlM_finRange` are the Hoare rules
  of a loop. `SetM.mem_run_foldlM_update_of_nodup` covers every loop that writes one entry per step
  (a saxpy, the inner loop of column-oriented substitution, a column of a rank-one update).
  `SetM.mem_run_foldlM_of_pi` is loop interchange for the rarer loops whose every step acts on every
  entry independently, and `SetM.mem_run_foldlM_update_self_iff` covers a loop that accumulates into
  one entry.
* The preferred route from an algorithm to an error bound is a bridge "every run satisfies the
  backbone relation" (`FloatingPoint.RoundsDot`, `FloatingPoint.RoundsForwardSubst`,
  `FloatingPoint.RoundsLU`, …), followed by the backbone theorem about the relation.
* Complex algorithms (the FFT) take a hook `rnd : ℂ → M ℂ` with the same exact semantics. There is
  no complex rounding model.
* The `SetM` and `List` lemmas are candidates for Mathlib, with natural homes
  `Mathlib.Data.Set.Functor` and `Mathlib.Data.List`. The pure `List` lemmas are in
  `Numlib.Data.List.Fold`. The `SetM` lemmas are in this module until a second module needs them.
-/

universe u v

/-! ### The run calculus of `SetM` -/

namespace SetM

section Run

variable {α β : Type u}

/-- The run set of `pure a` is $\{a\}$: $b$ is a result of `pure a` if and only if $b = a$. -/
@[simp]
theorem mem_run_pure {a b : α} : b ∈ (pure a : SetM α).run ↔ b = a := Iff.rfl

/-- **The run set of a bind**: $b$ is a result of `s >>= f` if and only if $b$ is a result of `f a`
for some result $a$ of `s`. In the floating-point reading, this is "some admissible choice at
each step". -/
@[simp]
theorem mem_run_bind {s : SetM α} {f : α → SetM β} {b : β} :
    b ∈ (s >>= f).run ↔ ∃ a ∈ s.run, b ∈ (f a).run := by
  change b ∈ ⋃ i ∈ SetM.run s, SetM.run (f i) ↔ _
  simp

/-- The run set of a map is the image of the run set: $b$ is a result of `Functor.map f s` if and
only if $b = f(a)$ for some result $a$ of `s`. -/
@[simp]
theorem mem_run_map {s : SetM α} {f : α → β} {b : β} :
    b ∈ (f <$> s).run ↔ ∃ a ∈ s.run, f a = b := by
  rw [← bind_pure_comp, mem_run_bind]
  simp [eq_comm]

/-- A bind has a result if its first step `s` has a result and every result $a$ of `s` gives a step
`f a` that has a result. -/
theorem run_bind_nonempty {s : SetM α} {f : α → SetM β} (hs : s.run.Nonempty)
    (hf : ∀ a ∈ s.run, (f a).run.Nonempty) : (s >>= f).run.Nonempty := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hf a ha
  exact ⟨b, mem_run_bind.2 ⟨a, ha, hb⟩⟩

/-- A loop has a result if every step has a result: if `f b a` has a result for every state $b$ and
every element $a$ of the list $l$, then the loop `l.foldlM f b₀` has a result for every initial
state $b_0$. -/
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

/-- An `if` between two `pure` values is `pure` of an `if`: `(if c then pure a else pure b) = pure
(if c then a else b)`, for any type constructor with `Pure`. This collapses, in the exact
semantics, a program that branches on a computed value. -/
theorem ite_pure {f : Type u → Type v} [Pure f] {α : Type u} (c : Prop) [Decidable c] (a b : α) :
    (if c then pure a else pure b : f α) = pure (if c then a else b) :=
  (apply_ite pure c a b).symm

/-! ### Loops in the relational semantics -/

namespace SetM

section Loops

variable {α : Type*} {β : Type u}

/-- **The Hoare rule of a loop**, with the invariant indexed by the processed prefix. Let $I$ be a
predicate on pairs of a prefix of the list $l$ and a state. Suppose that $I([\,], a)$ holds, and
that for every decomposition $l = p \mathbin{+\!\!+} [x] \mathbin{+\!\!+} q$, every state $c$
with $I(p, c)$ and every result $c'$ of the step on $x$ from $c$, the invariant
$I(p \mathbin{+\!\!+} [x], c')$ holds. Then every result $b$ of the loop over $l$ from $a$
satisfies $I(l, b)$. -/
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

/-- **The Hoare rule of a loop over `List.finRange n`**, with the invariant indexed by the step
count. Let $I$ be a predicate on pairs of a natural number and a state. Suppose that $I(0, a)$
holds, and that for every $k < n$, every state $c$ with $I(k, c)$ and every result $c'$ of step
$k$ from $c$, the invariant $I(k + 1, c')$ holds. Then every result $b$ of the loop from $a$
satisfies $I(n, b)$. -/
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

/-- **Loop interchange in the relational model.** Consider a loop over a list $l$ with a state
$y : \iota \to \beta$. Suppose that every step acts entrywise with independent roundings: for
every state $y$ and element $a$, the results of step $a$ from $y$ are exactly the states $y'$
such that $y'(i)$ is a result of $g(a, i, y(i))$ for every $i$. Then $y$ is a result of the loop
from $y_0$ if and only if, for every $i$, $y(i)$ is a result of the loop on entry $i$ alone,
with steps $g(\cdot, i, \cdot)$, from $y_0(i)$. -/
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

/-- **A loop that accumulates into one entry.** Consider a loop over a list $l$ with a state
$y : \iota \to \beta$, whose step $a$ replaces entry $i$ by a result of $g(a, y(i))$ and leaves
the other entries unchanged. Then $y$ is a result of the loop from $y_0$ if and only if $y$
agrees with $y_0$ except at $i$, and $y(i)$ is a result of the loop with steps $g$ run on entry
$i$ alone from $y_0(i)$. This is the relational form of `List.foldl_update_self`. -/
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

/-- The auxiliary form of `SetM.mem_run_foldlM_update_of_nodup`, with a fixed set $S \supseteq l$ of
indices, so that the induction hypothesis applies to the tail of the list. -/
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

/-- **One entry per step.** Let $l$ be a list of indices without duplicates, and consider a loop
over $l$ with a state $y : \iota \to \beta$ whose step $a$ replaces entry $a$ by a result of
$g(a, y(a), y)$. Suppose that, for $a \in l$, the step $g(a, b, y)$ depends on $y$ only through
the entries outside $l$. Then $y$ is a result of the loop from $y_0$ if and only if
$y(i) = y_0(i)$ for every $i \notin l$, and $y(i)$ is a result of $g(i, y_0(i), y_0)$ for every
$i \in l$.

So the loop writes each entry of $l$ once, from its initial value and the entries that the loop
does not write, and its run set is the product of the per-entry run sets. The loops of a saxpy,
of a column gaxpy, of column-oriented substitution and of the rank-one updates of LU and
Cholesky have this form. -/
theorem mem_run_foldlM_update_of_nodup {ι : Type u} [DecidableEq ι]
    (g : ι → β → (ι → β) → SetM β) (l : List ι) (hl : l.Nodup)
    (hg : ∀ a ∈ l, ∀ b (y y' : ι → β), (∀ i, i ∉ l → y i = y' i) → g a b y = g a b y')
    (y₀ y : ι → β) :
    y ∈ (l.foldlM (fun (y : ι → β) a => do
        let b ← g a (y a) y; pure (Function.update y a b)) y₀).run ↔
      (∀ i, i ∉ l → y i = y₀ i) ∧ ∀ i ∈ l, y i ∈ (g i (y₀ i) y₀).run :=
  mem_run_foldlM_update_aux g {i | i ∈ l} l hl (fun _ h => h) hg y₀ y

/-- **The Hoare rule of a loop that writes one entry per step, in dependence order.** Let $l$ be a
list of indices without duplicates, and consider the loop over $l$ from the state $b$ whose step
$i$ replaces entry $i$ of the state $s$ by a result $x$ of $g(i, s)$. Let $R(i, s, x)$ be a
property of an index, a state and a value. Suppose that, for every decomposition
$l = p \mathbin{+\!\!+} [i] \mathbin{+\!\!+} q$:

* every state $s$ that agrees with $b$ outside $p$, and every result $x$ of $g(i, s)$, satisfy
  $R(i, s, x)$;
* $R(i, s, x)$ depends on $s$ only through the entries in $p$.

Then every result $y$ of the loop satisfies $R(i, y, y(i))$ for every $i \in l$. The
row-oriented triangular substitutions have this form. -/
theorem forall_mem_run_foldlM_update_of_nodup {ι : Type u} [DecidableEq ι] {l : List ι}
    (hl : l.Nodup) (g : ι → (ι → β) → SetM β) (R : ι → (ι → β) → β → Prop) (b : ι → β)
    (hg : ∀ p i q, l = p ++ i :: q → ∀ s : ι → β, (∀ j, j ∉ p → s j = b j) →
      ∀ x ∈ (g i s).run, R i s x)
    (hR : ∀ p i q, l = p ++ i :: q → ∀ (s s' : ι → β) x, (∀ j ∈ p, s j = s' j) →
      R i s x → R i s' x) :
    ∀ y ∈ (l.foldlM (fun s i => do let x ← g i s; pure (Function.update s i x)) b).run,
      ∀ i ∈ l, R i y (y i) := by
  intro y hy
  refine (forall_mem_run_foldlM (l := l) (a := b)
    (fun p s => (∀ j, j ∉ p → s j = b j) ∧ ∀ i ∈ p, R i s (s i))
    ⟨fun _ _ => rfl, by simp⟩ ?_ y hy).2
  rintro p x q hl' c ⟨hc₁, hc₂⟩ c' hc'
  rw [mem_run_bind] at hc'
  obtain ⟨v, hv, hc'⟩ := hc'
  rw [mem_run_pure] at hc'
  subst hc'
  have hxp : x ∉ p := fun h =>
    List.disjoint_of_nodup_append (hl' ▸ hl) h List.mem_cons_self
  have hagree : ∀ j ∈ p, c j = Function.update c x v j := fun j hj =>
    (Function.update_of_ne (fun (e : j = x) => hxp (e ▸ hj)) _ _).symm
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have hjx : j ≠ x := fun e => hj (List.mem_append.2 (Or.inr (e ▸ List.mem_singleton_self x)))
    rw [Function.update_of_ne hjx]
    exact hc₁ j fun h => hj (List.mem_append.2 (Or.inl h))
  · rcases List.mem_append.1 hi with hi | hi
    · have hix : i ≠ x := fun e => hxp (e ▸ hi)
      rw [Function.update_of_ne hix]
      obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hi
      refine hR p₁ i (p₂ ++ x :: q) (by rw [hl']; simp) c _ (c i) (fun j hj => ?_) (hc₂ i hi)
      exact hagree j (List.mem_append.2 (Or.inl hj))
    · rw [List.mem_singleton.1 hi, Function.update_self]
      exact hR p x q hl' c _ v hagree (hg p x q hl' c hc₁ v hv)

end Loops

end SetM

/-!
### Loops over matrices

A matrix state is overwritten by `Matrix.updateRow` or `Matrix.updateCol`. A loop that acts on one
row, one column or one entry is one update of that row, column or entry. A loop that writes one
entry per step over a duplicate-free list of positions has the product run set, through the entry
view `Matrix.uncurry_updateRow_update`. In exact arithmetic, a loop that writes one row or one
column per step writes each listed row or column once.
-/

namespace Matrix

section Loops

variable {M : Type u → Type v} [Monad M] [LawfulMonad M] {m n R : Type u} {α : Type*}

/-- **A loop that acts on row $i$ of a matrix.** In a lawful monad, a loop over a list $l$ whose
step $a$ replaces row $i$ of the matrix $A$ by a result of $h(a, A_{i,:})$ equals the following
program: run the loop with steps $h$ on the row vector $(A_0)_{i,:}$, and replace row $i$ of
$A_0$ by its result. -/
theorem foldlM_updateRow [DecidableEq m] (i : m) (h : α → (n → R) → M (n → R)) (l : List α)
    (A₀ : Matrix m n R) :
    l.foldlM (fun (A : Matrix m n R) a => do let r ← h a (A i); pure (A.updateRow i r)) A₀
      = (do let r ← l.foldlM (fun r a => h a r) (A₀ i); pure (A₀.updateRow i r)) :=
  List.foldlM_lens (fun A : Matrix m n R => A i) (fun A r => A.updateRow i r) (by simp)
    (by simp [updateRow_idem]) (by simp [updateRow_eq_self]) (fun r a => h a r) l A₀

/-- **A loop that acts on column $j$ of a matrix.** In a lawful monad, a loop over a list $l$ whose
step $a$ replaces column $j$ of the matrix $A$ by a result of $h(a, A_{:,j})$ equals the
following program: run the loop with steps $h$ on the column vector $(A_0)_{:,j}$, and replace
column $j$ of $A_0$ by its result. -/
theorem foldlM_updateCol [DecidableEq n] (j : n) (h : α → (m → R) → M (m → R)) (l : List α)
    (A₀ : Matrix m n R) :
    l.foldlM (fun (A : Matrix m n R) a => do
        let c ← h a (fun i => A i j); pure (A.updateCol j c)) A₀
      = (do let c ← l.foldlM (fun c a => h a c) (fun i => A₀ i j); pure (A₀.updateCol j c)) :=
  List.foldlM_lens (fun A : Matrix m n R => fun i => A i j) (fun A c => A.updateCol j c)
    (fun _ _ => by ext; simp) (by simp [updateCol_idem]) (fun A => by simp) (fun c a => h a c) l A₀

/-- **A loop that accumulates into entry $(i, j)$ of a matrix.** In a lawful monad, a loop over a
list $l$ whose step $a$ replaces the entry $A_{ij}$ by a result of $h(a, A_{ij})$ equals the
following program: run the loop with steps $h$ on the scalar $(A_0)_{ij}$, and replace entry
$(i, j)$ of $A_0$ by its result. -/
theorem foldlM_updateRow_update [DecidableEq m] [DecidableEq n] (i : m) (j : n)
    (h : α → R → M R) (l : List α) (A₀ : Matrix m n R) :
    l.foldlM (fun (A : Matrix m n R) a => do
        let c ← h a (A i j); pure (A.updateRow i (Function.update (A i) j c))) A₀
      = (do
        let c ← l.foldlM (fun c a => h a c) (A₀ i j)
        pure (A₀.updateRow i (Function.update (A₀ i) j c))) :=
  List.foldlM_lens (fun A : Matrix m n R => A i j)
    (fun A c => A.updateRow i (Function.update (A i) j c)) (by simp)
    (fun A b b' => by simp [updateRow_idem]) (by simp [updateRow_eq_self]) (fun c a => h a c) l A₀

/-- **A loop that writes the entries of row $i$ of a matrix.** In a lawful monad, a loop over a list
$l$ of column indices whose step $j$ replaces $A_{ij}$ by a result of $h(j, A_{ij})$ equals the
following program: run the entrywise loop on the row vector $(A_0)_{i,:}$, and replace row $i$
of $A_0$ by its result. This is `Matrix.foldlM_updateRow` with a step that writes one entry. -/
theorem foldlM_updateRow_entrywise [DecidableEq m] [DecidableEq n] (i : m) (h : n → R → M R)
    (l : List n) (A₀ : Matrix m n R) :
    l.foldlM (fun (A : Matrix m n R) j => do
        let c ← h j (A i j); pure (A.updateRow i (Function.update (A i) j c))) A₀
      = (do
        let r ← l.foldlM (fun (r : n → R) j => do
          let c ← h j (r j); pure (Function.update r j c)) (A₀ i)
        pure (A₀.updateRow i r)) := by
  have := foldlM_updateRow i
    (fun j (r : n → R) => do let c ← h j (r j); pure (Function.update r j c)) l A₀
  simpa only [bind_assoc, pure_bind] using this

end Loops

/-- **One row per step, in exact arithmetic.** Let $l$ be a list of row indices without duplicates.
A loop over $l$ whose step $a$ replaces row $a$ by $g(a, A_{a,:})$ replaces every listed row
once, from its initial value: row $i$ of the result is $g(i, (A_0)_{i,:})$ if $i \in l$, and
$(A_0)_{i,:}$ otherwise. This is the row form of `List.idRun_foldlM_update_apply`. -/
theorem idRun_foldlM_updateRow_apply {m n R : Type u} [DecidableEq m]
    (g : m → (n → R) → Id (n → R)) (l : List m) (hl : l.Nodup) (A₀ : Matrix m n R) (i : m) :
    (l.foldlM (fun (A : Matrix m n R) a => do
      let r ← g a (A a); pure (A.updateRow a r)) A₀).run i =
      if i ∈ l then (g i (A₀ i)).run else A₀ i :=
  List.idRun_foldlM_update_apply (β := n → R) g l hl A₀ i

/-- **One column per step, in exact arithmetic.** Let $l$ be a list of column indices without
duplicates. A loop over $l$ whose step $c$ replaces column $c$ by $f(c, A_{:,c})$ replaces every
listed column once, from its initial value: entry $(i, j)$ of the result is $f(j, A_{:,j})_i$ if
$j \in l$, and $A_{ij}$ otherwise.

The proof is `List.foldl_update_of_nodup` on the transposed state. If $f(c, \cdot)$ is constant,
the loop writes columns that are fixed in advance. -/
theorem foldl_updateCol_apply {m n R : Type*} [DecidableEq n] (f : n → (m → R) → m → R)
    {l : List n} (hl : l.Nodup) (A : Matrix m n R) (i : m) (j : n) :
    l.foldl (fun (A : Matrix m n R) c => A.updateCol c (f c fun i => A i c)) A i j =
      if j ∈ l then f j (fun i => A i j) i else A i j := by
  have hhom := List.foldl_hom (transpose : Matrix m n R → Matrix n m R)
    (g₁ := fun (A : Matrix m n R) c => A.updateCol c (f c fun i => A i c))
    (g₂ := fun (y : Matrix n m R) c => Function.update y c (f c (y c))) (l := l)
    (init := A) fun A c => updateRow_transpose
  refine (congrFun (congrFun hhom j) i).symm.trans ((congrFun (congrFun
    (List.foldl_update_of_nodup hl (fun c y => f c (y c)) (fun _ _ _ _ _ e => by rw [e]) Aᵀ) j)
    i).trans ?_)
  split_ifs <;> rfl

/-- **The entry view of a one-entry update**: replacing entry $(i, j)$ of a matrix $A$ by $x$ is the
same as updating $A$, read as a function on positions, at $(i, j)$ with $x$.

Through this identity and `List.foldl_hom` or `List.foldlM_hom`, the loop lemmas about
`Function.update` (`List.foldl_update_of_nodup`, …) apply to loops over the entries of a matrix. -/
theorem uncurry_updateRow_update {m n R : Type*} [DecidableEq m] [DecidableEq n]
    (A : Matrix m n R) (i : m) (j : n) (x : R) :
    Function.uncurry (A.updateRow i (Function.update (A i) j x)) =
      Function.update (Function.uncurry A) (i, j) x :=
  Function.uncurry_update_update A i j x

end Matrix

namespace SetM

/-- **One matrix entry per step.** Let $l$ be a list of positions without duplicates, and consider a
loop over $l$ whose step at $(i, j)$ replaces the entry $A_{ij}$ by a result of
$g((i, j), A_{ij}, A)$. Suppose that, for every position in $l$, the step depends on $A$ only
through the entries at positions outside $l$. Then $A$ is a result of the loop from $A_0$ if and
only if $A_{ij} = (A_0)_{ij}$ for every $(i, j) \notin l$, and $A_{ij}$ is a result of
$g((i, j), (A_0)_{ij}, A_0)$ for every $(i, j) \in l$. This is the matrix form of
`SetM.mem_run_foldlM_update_of_nodup`. -/
theorem mem_run_foldlM_updateRow_update_of_nodup {m n β : Type u} [DecidableEq m] [DecidableEq n]
    (l : List (m × n)) (hl : l.Nodup) (g : m × n → β → Matrix m n β → SetM β)
    (hg : ∀ a ∈ l, ∀ x (A A' : Matrix m n β),
      (∀ i j, (i, j) ∉ l → A i j = A' i j) → g a x A = g a x A')
    (A₀ A : Matrix m n β) :
    A ∈ (l.foldlM (fun (A : Matrix m n β) a => do
        let x ← g a (A a.1 a.2) A
        pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) A₀).run ↔
      (∀ i j, (i, j) ∉ l → A i j = A₀ i j) ∧ ∀ a ∈ l, A a.1 a.2 ∈ (g a (A₀ a.1 a.2) A₀).run := by
  have hmap := List.foldlM_hom (m := SetM) (Function.uncurry : Matrix m n β → m × n → β)
    (g₁ := fun (A : Matrix m n β) a => do
      let x ← g a (A a.1 a.2) A
      pure (A.updateRow a.1 (Function.update (A a.1) a.2 x)))
    (g₂ := fun y a => do
      let x ← g a (y a) (Matrix.of (Function.curry y))
      pure (Function.update y a x)) (l := l) (init := A₀) fun B a => by
      rw [map_bind]
      refine congrArg (g a (B a.1 a.2) B >>= ·) (funext fun x => ?_)
      exact ((map_pure (f := SetM) (Function.uncurry : Matrix m n β → m × n → β) _).trans
        (congrArg pure (Matrix.uncurry_updateRow_update B a.1 a.2 x))).symm
  have key := mem_run_foldlM_update_of_nodup (fun a x y => g a x (Matrix.of (Function.curry y)))
    l hl (fun a ha x y y' hy => hg a ha x _ _ fun i j hij => hy (i, j) hij)
    (Function.uncurry A₀) (Function.uncurry A)
  have hA : A ∈ (l.foldlM (fun (A : Matrix m n β) a => do
        let x ← g a (A a.1 a.2) A
        pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) A₀).run ↔
      Function.uncurry A ∈ (Function.uncurry <$> l.foldlM (fun (A : Matrix m n β) a => do
        let x ← g a (A a.1 a.2) A
        pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) A₀).run := by
    rw [mem_run_map]
    exact ⟨fun h => ⟨A, h, rfl⟩, fun ⟨B, hB, hBA⟩ => Function.uncurry_injective hBA ▸ hB⟩
  rw [hA, ← hmap, key]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨fun i j hij => h₁ (i, j) hij, h₂⟩,
    fun ⟨h₁, h₂⟩ => ⟨fun p hp => h₁ p.1 p.2 hp, h₂⟩⟩

end SetM

/-! ### The rounding hook -/

namespace FloatingPoint

section Hook

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The rounding hook of a rounding model**: the set of admissible roundings of $x$, as an element
of the monad `SetM` of Mathlib. An algorithm written with a hook `rnd : K → M K` has its
floating-point semantics at `M := SetM` and `rnd := fp.round`. -/
def RoundingModel.round (fp : RoundingModel K) (x : K) : SetM K := {y | fp.Rounds x y}

/-- The results of the hook at $x$ are the admissible roundings of $x$. -/
@[simp]
theorem RoundingModel.mem_run_round {fp : RoundingModel K} {x y : K} :
    y ∈ (fp.round x).run ↔ fp.Rounds x y := Iff.rfl

/-- In the exact model the hook is `pure`. So a program run in the exact model has the single result
of its exact semantics. -/
theorem RoundingModel.round_exact : (RoundingModel.exact K).round = pure := rfl

/-- Over a total model, the hook at every $x$ has a result. -/
theorem RoundingModel.run_round_nonempty {fp : RoundingModel K} (hfp : fp.IsTotal) (x : K) :
    (fp.round x).run.Nonempty :=
  hfp x

end Hook

/-!
### The inner-product accumulation

The inner-product accumulation computes $c + \sum_{k \in o} x_k y_k$ as
$c \leftarrow fl(c + fl(x_k y_k))$. A loop $c = 0$; $c = c + x_1 y_1$; … rounds $0 + fl(x_1 y_1)$,
while `FloatingPoint.RoundsSum` starts from the unrounded first term, and the relational model
cannot know that $0 + p$ rounds to $p$. Both readings are given. Without further hypotheses, a run
from any start $c$ is within $\gamma_{n+1} (|c| + \sum_k |x_k| |y_k|)$ of $c + \sum_k x_k y_k$, at
the price of one extra rounding. Over an idempotent model (every concrete format is one), a run from
$c = 0$ over a duplicate-free order of all indices satisfies `FloatingPoint.RoundsDot`, so the bound
is the constant $\gamma_n$ of [higham2002accuracy]. This is the rigorous reading of (2.7.9) of
[golub2013matrix], where $s_1 = x_1 y_1 (1 + \delta_1)$ assumes without saying so that the first
addition is exact.
-/

section DotAccum

variable {K : Type u}

/-- **The inner-product accumulation**, generic in the monad. For a list $o$ of indices, vectors
$x, y$ and a start $c$, `FloatingPoint.dotAccum rnd o x y c` computes
$c + \sum_{k \in o} x_k y_k$ by the loop $$c \leftarrow \mathrm{rnd}(c + \mathrm{rnd}(x_k
y_k))$$ for $k$ in the order of $o$.

With $c = 0$ this is Algorithm 1.1.1 of [golub2013matrix]. The inner loops of the row gaxpy and
of the $ijk$ matrix product start from $c = y_i$ and $c = C_{ij}$. -/
def dotAccum [Add K] [Mul K] {M : Type u → Type v} [Monad M] (rnd : K → M K) {ι : Type*}
    (o : List ι) (x y : ι → K) (c : K) : M K :=
  o.foldlM (fun c k => do rnd (c + (← rnd (x k * y k)))) c

/-- With the hook `pure`, in any lawful monad, the accumulation is `pure` of the exact sum
$c + \sum_{k \in o} x_k y_k$. -/
theorem dotAccum_pure [AddMonoid K] [Mul K] {M : Type u → Type v} [Monad M] [LawfulMonad M]
    {ι : Type*} (o : List ι) (x y : ι → K) (c : K) :
    dotAccum (M := M) pure o x y c = pure (c + (o.map fun k => x k * y k).sum) := by
  unfold dotAccum
  simp only [pure_bind, List.foldlM_pure]
  rw [List.foldl_add_eq_add_sum_map]

/-- **The exact semantics of the accumulation**: with the hook `pure` in the monad `Id`, the result
is $c + \sum_{k \in o} x_k y_k$, where the sum runs over the list $o$, with repetitions. -/
theorem dotAccum_id [AddMonoid K] [Mul K] {ι : Type*} (o : List ι) (x y : ι → K) (c : K) :
    Id.run (dotAccum (M := Id) pure o x y c) = c + (o.map fun k => x k * y k).sum := by
  rw [dotAccum_pure]
  rfl

/-- The exact accumulation over `List.finRange n` is $c + x^T y$. -/
theorem dotAccum_id_finRange [AddCommMonoid K] [Mul K] {n : ℕ} (x y : Fin n → K) (c : K) :
    Id.run (dotAccum (M := Id) pure (List.finRange n) x y c) = c + x ⬝ᵥ y := by
  rw [dotAccum_id, dotProduct, Fin.sum_univ_def]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {ι : Type*}

/-- Over a total model the accumulation has a result, so theorems about all its runs are not
vacuous. -/
theorem dotAccum_run_nonempty {fp : RoundingModel K} (hfp : fp.IsTotal) (o : List ι)
    (x y : ι → K) (c : K) : (dotAccum fp.round o x y c).run.Nonempty :=
  SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
    (RoundingModel.run_round_nonempty hfp _) fun _ _ => RoundingModel.run_round_nonempty hfp _) c

/-- **The bridge from the accumulation to the relational sum.** In a rounding model, $s$ is a result
of `FloatingPoint.dotAccum fp.round o x y c` if and only if there are values $p_k$, one for each
entry $k$ of the list $o$, such that $p_k$ is an admissible rounding of $x_k y_k$ and $s$ is an
admissible running sum (`FloatingPoint.RoundsSumFrom`) of the list $(p_k)_{k \in o}$ from the
unrounded start $c$.

The list $o$ may repeat indices; the values $p_k$ are then a list, not a function of $k$. -/
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

/-- **The accumulation in the exact model** is the exact running sum: $s$ is a result if and only if
$s = c + \sum_{k \in o} x_k y_k$. The exact specification of every program built on
`FloatingPoint.dotAccum` follows from its bridge and this lemma. -/
theorem mem_run_dotAccum_exact_iff {o : List ι} {x y : ι → K} {c s : K} :
    s ∈ (dotAccum (RoundingModel.exact K).round o x y c).run ↔
      s = c + (o.map fun k => x k * y k).sum := by
  rw [RoundingModel.round_exact, dotAccum_pure, SetM.mem_run_pure]

/-- **A run of the accumulation over a duplicate-free order.** If $o$ has no duplicates and $s$ is a
result of the accumulation in a rounding model, then there is a function $p$ on the indices such
that $p_j$ is an admissible rounding of $x_j y_j$ for every $j \in o$, and $s$ is an admissible
running sum of $(p_j)_{j \in o}$ from the start $c$. -/
theorem exists_of_mem_run_dotAccum {fp : RoundingModel K} {o : List ι} (ho : o.Nodup)
    {x y : ι → K} {c s : K} (h : s ∈ (dotAccum fp.round o x y c).run) :
    ∃ p : ι → K, (∀ j ∈ o, fp.Rounds (x j * y j) (p j)) ∧ RoundsSumFrom fp c (o.map p) s := by
  obtain ⟨ps, hps, hsum⟩ := mem_run_dotAccum_iff.1 h
  obtain ⟨p, hp, rfl⟩ := hps.exists_map_eq_of_nodup ho 0
  exact ⟨p, hp, hsum⟩

/-- A result $s$ of the accumulation is either the start $c$ (this happens when $o$ is empty) or an
admissible rounding of some value. -/
theorem eq_or_rounds_of_mem_run_dotAccum {fp : RoundingModel K} {o : List ι} {x y : ι → K}
    {c s : K} (h : s ∈ (dotAccum fp.round o x y c).run) : s = c ∨ ∃ z, fp.Rounds z s := by
  induction o generalizing c with
  | nil => exact Or.inl h
  | cons k o ih =>
    simp only [dotAccum, List.foldlM_cons, SetM.mem_run_bind, RoundingModel.mem_run_round] at h
    obtain ⟨c', ⟨p, -, hc'⟩, h⟩ := h
    rcases ih h with rfl | h
    · exact Or.inr ⟨_, hc'⟩
    · exact Or.inr h

/-- **A run of a loop of rounded subtractions of rounded values.** Let $o$ be a list of indices
without duplicates, and let $x$ be a result of the loop $c \leftarrow fl(c - fl(f_r))$ over $o$
from $c$. Then there is a function $p$ such that $p_r$ is an admissible rounding of $f_r$ for
every $r \in o$, and $x$ is an admissible running sum of $(-p_r)_{r \in o}$ from the start $c$. -/
theorem exists_of_mem_run_foldlM_sub {fp : RoundingModel K} {o : List ι} (ho : o.Nodup)
    {f : ι → K} {c x : K}
    (h : x ∈ (o.foldlM (fun (c : K) r => do let p ← fp.round (f r); fp.round (c - p)) c).run) :
    ∃ p : ι → K, (∀ r ∈ o, fp.Rounds (f r) (p r)) ∧ RoundsSumFrom fp c (o.map fun r => -p r) x := by
  classical
  induction o generalizing c with
  | nil =>
    rw [List.foldlM_nil, SetM.mem_run_pure] at h
    exact ⟨fun _ => 0, by simp, h ▸ .nil _⟩
  | cons a o ih =>
    simp only [List.foldlM_cons, bind_assoc, SetM.mem_run_bind, RoundingModel.mem_run_round] at h
    obtain ⟨pa, hpa, c', hc', h⟩ := h
    obtain ⟨p, hp, hsum⟩ := ih (List.nodup_cons.1 ho).2 h
    have ha : a ∉ o := (List.nodup_cons.1 ho).1
    refine ⟨Function.update p a pa, fun r hr => ?_, ?_⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · rwa [Function.update_self]
      · rw [Function.update_of_ne fun (e : r = a) => ha (e ▸ hr)]
        exact hp r hr
    · rw [List.map_cons, Function.update_self]
      have hmap : (o.map fun r => -Function.update p a pa r) = o.map fun r => -p r :=
        List.map_congr_left fun r hr => by
          rw [Function.update_of_ne fun (e : r = a) => ha (e ▸ hr)]
      rw [hmap]
      exact .cons (by rw [← sub_eq_add_neg]; exact hc') hsum

/-- **The accumulation from $0$ is the inner product of [higham2002accuracy] when rounding fixes its
outputs.** Let the rounding model be idempotent, and let $o$ be a list of indices without
duplicates that contains every index. Then every result $s$ of the accumulation from $c = 0$
along $o$ is an admissible inner product of $x$ and $y$ (`FloatingPoint.RoundsDot`).

The first addition $0 + fl(x_1 y_1)$ is exact in an idempotent model. By
`FloatingPoint.abs_sub_le_of_roundsDot`, the result satisfies
$|s - x^T y| \le \gamma_n |x|^T |y|$, the rigorous form of (2.7.11)–(2.7.12) of
[golub2013matrix]. -/
theorem roundsDot_of_mem_run_dotAccum {fp : RoundingModel K} (hfp : fp.IsIdempotent)
    {o : List ι} (ho : o.Nodup) (hmem : ∀ i, i ∈ o) {x y : ι → K} {s : K}
    (h : s ∈ (dotAccum fp.round o x y 0).run) : RoundsDot fp x y s := by
  obtain ⟨p, hp, hsum⟩ := exists_of_mem_run_dotAccum ho h
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

/-- The two facts about lists behind `FloatingPoint.abs_sub_le_of_mem_run_dotAccum`: the sum of the
rounded products differs from the exact sum by at most $u \sum_k |x_k| |y_k|$, and the sum of
their absolute values is at most $(1 + u) \sum_k |x_k| |y_k|$. -/
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

/-- **A bound for an accumulation onto any start**, with no hypothesis on the model (the bound of
[higham2002accuracy] for $fl(c + x^T y)$). Let $o$ be a list of $n$ indices, possibly with
repetitions, and let $(n + 1)u < 1$. Every result $s$ of the accumulation from the start $c$
satisfies $$\Bigl|s - \Bigl(c + \sum_{k \in o} x_k y_k\Bigr)\Bigr| \le \gamma_{n+1} \Bigl(|c| +
\sum_{k \in o} |x_k| |y_k|\Bigr).$$

With $c = 0$, the constant $\gamma_{n+1}$ is the price of not knowing that $0 + p$ is exact.
Over an idempotent model, `FloatingPoint.roundsDot_of_mem_run_dotAccum` gives the constant
$\gamma_n$. -/
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

/-!
### The running difference

The running difference computes $c - \sum_{k \in o} a_k b_k$ as $t \leftarrow fl(t - fl(a_k b_k))$.
It is the loop of Lemma 8.4 of [higham2002accuracy], used in the gaxpy forms of LU, $LDL^T$ and
Cholesky factorization and in column-oriented substitution. Over a duplicate-free order, its run set
is the relation `FloatingPoint.RoundsRunningDiff` that the backbone substitutions and factorizations
use.
-/

section RunningDiff

variable {K : Type u}

/-- **The running difference**, generic in the monad. For a list $o$ of indices, vectors $a, b$ and
a start $c$, `FloatingPoint.runningDiff rnd o a b c` computes $c - \sum_{k \in o} a_k b_k$ by
the loop $$t \leftarrow \mathrm{rnd}(t - \mathrm{rnd}(a_k b_k))$$ for $k$ in the order of $o$,
starting from $t = c$.

It is the subtractive twin of `FloatingPoint.dotAccum` and the loop of Lemma 8.4 of
[higham2002accuracy]. It is the inner loop of the gaxpy forms of LU, $LDL^T$ and Cholesky
factorization and of column-oriented substitution, which accumulate onto an entry of the matrix.
Its relation is `FloatingPoint.RoundsRunningDiff` (see `FloatingPoint.mem_run_runningDiff_iff`). -/
def runningDiff [Sub K] [Mul K] {M : Type u → Type v} [Monad M] (rnd : K → M K) {ι : Type*}
    (o : List ι) (a b : ι → K) (c : K) : M K :=
  o.foldlM (fun t k => do let p ← rnd (a k * b k); rnd (t - p)) c

/-- With the hook `pure`, in any lawful monad, the running difference is `pure` of the exact
difference $c - \sum_{k \in o} a_k b_k$. -/
theorem runningDiff_pure [SubtractionCommMonoid K] [Mul K] {M : Type u → Type v} [Monad M]
    [LawfulMonad M] {ι : Type*} (o : List ι) (a b : ι → K) (c : K) :
    runningDiff (M := M) pure o a b c = pure (c - (o.map fun k => a k * b k).sum) := by
  unfold runningDiff
  simp only [pure_bind, List.foldlM_pure]
  rw [List.foldl_sub_eq_sub_sum_map]

/-- **The exact semantics of the running difference**: with the hook `pure` in the monad `Id`, the
result is $c - \sum_{k \in o} a_k b_k$, where the sum runs over the list $o$, with repetitions. -/
theorem runningDiff_id [SubtractionCommMonoid K] [Mul K] {ι : Type*} (o : List ι) (a b : ι → K)
    (c : K) : Id.run (runningDiff (M := Id) pure o a b c) = c - (o.map fun k => a k * b k).sum := by
  rw [runningDiff_pure]
  rfl

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {ι : Type*}

/-- Over a total model the running difference has a result. -/
theorem runningDiff_run_nonempty {fp : RoundingModel K} (hfp : fp.IsTotal) (o : List ι)
    (a b : ι → K) (c : K) : (runningDiff fp.round o a b c).run.Nonempty :=
  SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
    (RoundingModel.run_round_nonempty hfp _) fun _ _ => RoundingModel.run_round_nonempty hfp _) c

/-- **The bridge from the running difference to its relation.** Let $o$ be a list of indices without
duplicates. In a rounding model, $t$ is a result of `FloatingPoint.runningDiff fp.round o a b c`
if and only if $t$ is an admissible running difference
`FloatingPoint.RoundsRunningDiff fp o a b c t`: there are admissible roundings $p_r$ of
$a_r b_r$, $r \in o$, such that $t$ is an admissible running sum of $(-p_r)_{r \in o}$ from $c$. -/
theorem mem_run_runningDiff_iff {fp : RoundingModel K} {o : List ι} (ho : o.Nodup)
    {a b : ι → K} {c t : K} :
    t ∈ (runningDiff fp.round o a b c).run ↔ RoundsRunningDiff fp o a b c t := by
  constructor
  · exact fun h => exists_of_mem_run_foldlM_sub ho h
  rintro ⟨p, hp, hs⟩
  clear ho
  unfold runningDiff
  induction o generalizing c with
  | nil =>
    cases hs
    exact SetM.mem_run_pure.2 rfl
  | cons k o ih =>
    rw [List.map_cons] at hs
    rcases hs with _ | ⟨hc, hs⟩
    simp only [List.foldlM_cons, bind_assoc, SetM.mem_run_bind, RoundingModel.mem_run_round]
    exact ⟨p k, hp k List.mem_cons_self, _, by rwa [sub_eq_add_neg],
      ih (fun r hr => hp r (List.mem_cons_of_mem _ hr)) hs⟩

/-- **The running difference in the exact model** is the exact difference: $t$ is a result if and
only if $t = c - \sum_{k \in o} a_k b_k$. The exact specification of a program built on
`FloatingPoint.runningDiff` follows from its bridge and this lemma. -/
theorem mem_run_runningDiff_exact_iff {o : List ι} {a b : ι → K} {c t : K} :
    t ∈ (runningDiff (RoundingModel.exact K).round o a b c).run ↔
      t = c - (o.map fun k => a k * b k).sum := by
  rw [RoundingModel.round_exact, runningDiff_pure, SetM.mem_run_pure]

end RunningDiff

end FloatingPoint
