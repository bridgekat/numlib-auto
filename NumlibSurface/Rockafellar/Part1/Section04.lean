import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Deriv
import Numlib.Analysis.Convex.Gateaux
import Numlib.Analysis.Convex.Homogeneous
import Numlib.Analysis.Convex.Line
import Numlib.Analysis.Convex.Saddle.Differential
import Numlib.Analysis.Convex.Subdifferential.Gradient
import NumlibSurface.Common.Euclidean

/-!
# Rockafellar, §4: Convex Functions

Convex functions on `ℝⁿ` with values in `[-∞, +∞]`: the secant and Jensen inequalities, the
second-derivative tests, convexity of level sets, and positively homogeneous convex functions.
All 11 numbered results of §4 are formalized.

Rockafellar's convex function is defined on **all** of `ℝⁿ` and is convex when its epigraph is,
which is the backbone's `ConvexFn` exactly. Only Theorems 4.4 and 4.5 take a finite `f`, being
about `C²` functions; anywhere else `f : Rn n → ℝ` would be a mistranslation. Properness is
imposed only where the book imposes it: Corollaries 4.7.1 and 4.7.2 and Theorem 4.8.

## The extended arithmetic

The conventions §4 lays down are content, not boilerplate.

* **`0 · ∞ = 0`** holds on the nose for Mathlib's `EReal`, and `theorem_4_3` depends on it: the
  book's `λ₁ f x₁ + ⋯ + λₘ f xₘ` is well defined at an index with `λᵢ = 0` and `f xᵢ = +∞` only
  because that term is `0`.
* **`inf ∅ = +∞`** is what the backbone's `restrictFn`, `⨅ _ : x ∈ s, f x`, computes off `s` — the
  book's own device for extending a function given on a convex set by `+∞`. `theorem_4_1` is
  stated through it.
* **`∞ − ∞` is undefined** in the book, whereas Mathlib's `EReal` totalises it as `⊥`. Nothing
  here relies on that totalisation: every statement whose right-hand side could produce the
  combination carries the book's own hypothesis `∀ x, f x ≠ ⊥`, so the value is never consulted.
  `theorem_4_2` is the one characterisation stated for the full range `[-∞, +∞]`, and it uses
  strict inequalities between *reals* precisely so that no infinite sum appears; `theorem_4_6` and
  `corollary_4_6_1` are about level sets, where no sum occurs.

`theorem_4_5` states positive semi-definiteness of the Hessian in the coordinate-free form
`0 ≤ fderiv ℝ (fderiv ℝ f) x z z` rather than through the matrix of second partial derivatives.

## References

* [rockafellar1970convex] §4.
-/

namespace Rockafellar

open ConvexAnalysis NumlibSurface

/-! ### Theorem 4.1 -/

/-- **Theorem 4.1.** For `f : C → (-∞, +∞]` with `C` convex, `f` is convex on `C` iff
`f ((1 − λ) x + λ y) ≤ (1 − λ) f x + λ f y` for all `x, y ∈ C` and `0 < λ < 1`.

"Convex on `C`" is `ConvexFn (restrictFn C f)`, the book's own convention that a function given on
`C` is extended to `ℝⁿ` by `+∞`. The hypothesis `∀ x, f x ≠ ⊥` is "values in `(-∞, +∞]`", which
keeps the right-hand side from being the forbidden `∞ − ∞`. -/
theorem theorem_4_1 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) {f : Rn n → EReal}
    (hbot : ∀ x, f x ≠ ⊥) :
    ConvexFn (restrictFn C f) ↔ ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y := by
  have hrb : ∀ x, restrictFn C f x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ C <;> simp [hx, hbot x]
  rw [convexFn_iff_le hrb]
  constructor
  · intro h x hx y hy a b ha hb hab
    have hmem : a • x + b • y ∈ C := hC hx hy ha.le hb.le hab
    have hkey := h x y a b ha hb hab
    rwa [restrictFn_of_mem hx, restrictFn_of_mem hy, restrictFn_of_mem hmem] at hkey
  · intro h x y a b ha hb hab
    by_cases hx : x ∈ C
    · by_cases hy : y ∈ C
      · have hmem : a • x + b • y ∈ C := hC hx hy ha.le hb.le hab
        rw [restrictFn_of_mem hx, restrictFn_of_mem hy, restrictFn_of_mem hmem]
        exact h x hx y hy a b ha hb hab
      · rw [restrictFn_of_notMem hy, EReal.coe_mul_top_of_pos hb,
          EReal.add_top_of_ne_bot (EReal.coe_mul_ne_bot ha.le (hrb x))]
        exact le_top
    · rw [restrictFn_of_notMem hx, EReal.coe_mul_top_of_pos ha,
        EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot hb.le (hrb y))]
      exact le_top

/-! ### Theorem 4.2 -/

/-- **Theorem 4.2.** `f : ℝⁿ → [-∞, +∞]` is convex iff `f ((1 − λ) x + λ y) < (1 − λ) α + λ β`
for `0 < λ < 1` whenever `f x < α` and `f y < β`. This is the characterisation that survives for
functions taking **both** infinite values, and Rockafellar remarks that it could serve as the
definition in general; `α` and `β` are reals, so no infinite sum is formed. -/
theorem theorem_4_2 {n : ℕ} (f : Rn n → EReal) :
    ConvexFn f ↔ ∀ (x y : Rn n) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, f x < (α : EReal) → f y < (β : EReal) →
        f (a • x + b • y) < ((a * α + b * β : ℝ) : EReal) :=
  convexFn_iff_forall_lt f

/-! ### Theorem 4.3 -/

/-- **Theorem 4.3 (Jensen's inequality).** `f : ℝⁿ → (-∞, +∞]` is convex iff
`f (λ₁x₁ + ⋯ + λₘxₘ) ≤ λ₁ f x₁ + ⋯ + λₘ f xₘ` whenever `λᵢ ≥ 0` and `∑ λᵢ = 1`.

The right-hand side is an `EReal` sum, well formed only under the convention `0 · ∞ = 0`: an
index with `λᵢ = 0` and `f xᵢ = +∞` must contribute `0`, not `∞`. -/
theorem theorem_4_3 {n : ℕ} {f : Rn n → EReal} (hbot : ∀ x, f x ≠ ⊥) :
    ConvexFn f ↔ ∀ (m : ℕ) (l : Fin m → ℝ) (x : Fin m → Rn n), (∀ i, 0 ≤ l i) →
      ∑ i, l i = 1 → f (∑ i, l i • x i) ≤ ∑ i, (l i : EReal) * f (x i) := by
  classical
  constructor
  · intro hconv m l x hl hl1
    set t : Finset (Fin m) := Finset.univ.filter fun i => l i ≠ 0 with ht
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin m)), i ∉ t → l i = 0 := by
      intro i _ hi
      simpa [ht] using hi
    have hsub : t ⊆ (Finset.univ : Finset (Fin m)) := Finset.filter_subset _ _
    have hsx : ∑ i ∈ t, l i • x i = ∑ i, l i • x i :=
      Finset.sum_subset hsub fun i hi hi' => by rw [hzero i hi hi', zero_smul]
    have hsf : ∑ i ∈ t, (l i : EReal) * f (x i) = ∑ i, (l i : EReal) * f (x i) :=
      Finset.sum_subset hsub fun i hi hi' => by
        rw [hzero i hi hi', EReal.coe_zero, zero_mul]
    have hs1 : ∑ i ∈ t, l i = 1 :=
      (Finset.sum_subset hsub fun i hi hi' => hzero i hi hi').trans hl1
    rw [← hsx, ← hsf]
    by_cases htop : ∑ i ∈ t, (l i : EReal) * f (x i) = ⊤
    · rw [htop]; exact le_top
    have hnb : ∀ i ∈ t, (l i : EReal) * f (x i) ≠ ⊥ :=
      fun i _ => EReal.coe_mul_ne_bot (hl i) (hbot (x i))
    have hnt := EReal.forall_ne_top_of_sum_ne_top t _ hnb htop
    have hfin : ∀ i ∈ t, f (x i) = ((f (x i)).toReal : EReal) := by
      intro i hi
      have hli : 0 < l i := lt_of_le_of_ne (hl i) (Ne.symm (by simpa [ht] using hi))
      refine (EReal.coe_toReal ?_ (hbot (x i))).symm
      intro hc
      exact hnt i hi (by rw [hc, EReal.coe_mul_top_of_pos hli])
    have key := hconv.sum_le t x (fun i => (f (x i)).toReal) l
      (fun i hi => le_of_eq (hfin i hi)) (fun i _ => hl i) hs1
    refine key.trans (le_of_eq ?_)
    rw [EReal.coe_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [EReal.coe_mul, ← hfin i hi]
  · intro h
    rw [convexFn_iff_le hbot]
    intro x y a b ha hb hab
    have key := h 2 ![a, b] ![x, y] (fun i => by fin_cases i <;> simp [ha.le, hb.le])
      (by simpa [Fin.sum_univ_two] using hab)
    simpa [Fin.sum_univ_two] using key

/-! ### Theorem 4.4 -/

/-- **Theorem 4.4.** A `C²` real function on an open interval `(α, β)` is convex iff `f'' ≥ 0`
throughout. One of the two results of §4 genuinely about a *finite* function, so `f : ℝ → ℝ` is
correct here; `Ioo α β` is open, so the book's `f''` is `deriv (deriv f)`. -/
theorem theorem_4_4 {α β : ℝ} {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo α β)) :
    ConvexOn ℝ (Set.Ioo α β) f ↔ ∀ x ∈ Set.Ioo α β, 0 ≤ deriv (deriv f) x := by
  have hd1 : DifferentiableOn ℝ f (Set.Ioo α β) := hf.differentiableOn (by norm_num)
  have hd2 : DifferentiableOn ℝ (deriv f) (Set.Ioo α β) :=
    (hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).differentiableOn (by norm_num)
  constructor
  · intro hconv x hx
    have hmono : MonotoneOn (deriv f) (Set.Ioo α β) :=
      hconv.monotoneOn_deriv fun y hy => (hd1 y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
    have h := hmono.derivWithin_nonneg (x := x)
    rwa [derivWithin_of_isOpen isOpen_Ioo hx] at h
  · intro h
    exact convexOn_of_deriv2_nonneg' (convex_Ioo α β) hd1 hd2 h

/-! ### Theorem 4.5

The reduction to lines is the backbone's `convexOn_iff_lines` and `isOpen_line_steps`
(`Numlib/Analysis/Convex/Line.lean`), and the derivative of a restriction to a line is
`HasLineDerivAt.hasDerivAt_line` (`Numlib/Analysis/Convex/Gateaux.lean`); what remains local is
the `C²` bookkeeping of Rockafellar's "straightforward calculation" of `g''`. -/

section Lines

variable {n : ℕ} {C : Set (Rn n)} {f : Rn n → ℝ} {y z : Rn n}

/-- A `C²` function on an open set has an honest Fréchet derivative there. -/
private theorem hasFDerivAt_of_contDiffOn (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {u : Rn n}
    (hu : u ∈ C) : HasFDerivAt f (fderiv ℝ f u) u :=
  (((hf.differentiableOn (by norm_num)) u hu).differentiableAt
    (hCopen.mem_nhds hu)).hasFDerivAt

/-- The derivative of a `C²` function is itself differentiable on the open set. -/
private theorem hasFDerivAt_fderiv_of_contDiffOn (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C)
    {u : Rn n} (hu : u ∈ C) : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) u) u :=
  ((((hf.fderiv_of_isOpen (m := 1) hCopen (by norm_num)).differentiableOn
    (by norm_num)) u hu).differentiableAt (hCopen.mem_nhds hu)).hasFDerivAt

/-- Near a step that stays in `C`, `deriv g` for `g t = f (y + t • z)` is
`s ↦ ⟨∇f (y + s • z), z⟩`. -/
private theorem deriv_comp_line_eventuallyEq (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {t : ℝ}
    (ht : y + t • z ∈ C) :
    (deriv fun s : ℝ => f (y + s • z)) =ᶠ[nhds t] fun s : ℝ => fderiv ℝ f (y + s • z) z := by
  filter_upwards [(isOpen_line_steps hCopen y z).mem_nhds
    (show t ∈ {t : ℝ | y + t • z ∈ C} from ht)] with s hs
  exact ((hasFDerivAt_of_contDiffOn hCopen hf hs).hasLineDerivAt z).hasDerivAt_line.deriv

/-- Rockafellar's "straightforward calculation": for `g t = f (y + t • z)`, `g'' t = ⟨z, Q_x z⟩`
with `x = y + t • z`, where `Q_x` is the second Fréchet derivative. -/
private theorem hasDerivAt_deriv_comp_line (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {t : ℝ}
    (ht : y + t • z ∈ C) :
    HasDerivAt (deriv fun s : ℝ => f (y + s • z))
      (fderiv ℝ (fderiv ℝ f) (y + t • z) z z) t := by
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (y + s • z))
      (fderiv ℝ (fderiv ℝ f) (y + t • z) z) t :=
    ((hasFDerivAt_fderiv_of_contDiffOn hCopen hf ht).hasLineDerivAt z).hasDerivAt_line
  have h2 : HasDerivAt (fun s : ℝ => (fderiv ℝ f (y + s • z)) z)
      (fderiv ℝ (fderiv ℝ f) (y + t • z) z z) t :=
    (ContinuousLinearMap.apply ℝ ℝ z).hasFDerivAt.comp_hasDerivAt t h1
  exact h2.congr_of_eventuallyEq (deriv_comp_line_eventuallyEq hCopen hf ht)

end Lines

/-- **Theorem 4.5.** A `C²` real function on an open convex `C ⊆ ℝⁿ` is convex on `C` iff its
Hessian is positive semi-definite at every `x ∈ C`. Positive semi-definiteness is the book's own
`⟨z, Q_x z⟩ ≥ 0` for every `z`, and that quadratic form is the second Fréchet derivative
`fderiv ℝ (fderiv ℝ f) x z z`, which is how the condition is stated here. -/
theorem theorem_4_5 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) (hCopen : IsOpen C)
    {f : Rn n → ℝ} (hf : ContDiffOn ℝ 2 f C) :
    ConvexOn ℝ C f ↔ ∀ x ∈ C, ∀ z : Rn n, 0 ≤ fderiv ℝ (fderiv ℝ f) x z z := by
  have hderiv : ∀ {y z : Rn n} {s : ℝ}, y + s • z ∈ C →
      HasDerivAt (fun s : ℝ => f (y + s • z)) (fderiv ℝ f (y + s • z) z) s := fun hs =>
    ((hasFDerivAt_of_contDiffOn hCopen hf hs).hasLineDerivAt _).hasDerivAt_line
  rw [convexOn_iff_lines hC]
  constructor
  · intro h x hx z
    have h0 : x + (0 : ℝ) • z ∈ C := by simpa using hx
    have hmono : MonotoneOn (deriv fun s : ℝ => f (x + s • z)) {t : ℝ | x + t • z ∈ C} :=
      (h x z).monotoneOn_deriv fun s hs => (hderiv hs).differentiableAt
    have hnn := hmono.derivWithin_nonneg (x := (0 : ℝ))
    rw [derivWithin_of_isOpen (isOpen_line_steps hCopen x z) h0,
      (hasDerivAt_deriv_comp_line hCopen hf h0).deriv] at hnn
    simpa using hnn
  · intro h y z
    refine convexOn_of_deriv2_nonneg' (hC.line_steps y z)
      (fun s hs => (hderiv hs).differentiableAt.differentiableWithinAt)
      (fun s hs =>
        (hasDerivAt_deriv_comp_line hCopen hf hs).differentiableAt.differentiableWithinAt)
      fun s hs => ?_
    change (0 : ℝ) ≤ deriv (deriv fun s : ℝ => f (y + s • z)) s
    rw [(hasDerivAt_deriv_comp_line hCopen hf hs).deriv]
    exact h _ hs z

/-! ### Theorem 4.6 and Corollary 4.6.1 -/

/-- **Theorem 4.6.** For convex `f` and any `α ∈ [-∞, +∞]`, the level sets `{x | f x < α}` and
`{x | f x ≤ α}` are convex. `α` genuinely ranges over `EReal`, including `±∞`, and no properness
or finiteness hypothesis is needed. -/
theorem theorem_4_6 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (α : EReal) :
    Convex ℝ {x | f x < α} ∧ Convex ℝ {x | f x ≤ α} :=
  ⟨hf.convex_lt α, hf.convex_le α⟩

/-- **Corollary 4.6.1.** The solution set `{x | fᵢ x ≤ αᵢ for all i}` of an arbitrary system of
convex inequalities is convex. -/
theorem corollary_4_6_1 {n : ℕ} {I : Type*} {f : I → Rn n → EReal} (hf : ∀ i, ConvexFn (f i))
    (α : I → ℝ) : Convex ℝ {x : Rn n | ∀ i, f i x ≤ ((α i : ℝ) : EReal)} := by
  have hEq : {x : Rn n | ∀ i, f i x ≤ ((α i : ℝ) : EReal)}
      = ⋂ i, {x : Rn n | f i x ≤ ((α i : ℝ) : EReal)} := by
    ext x; simp
  rw [hEq]
  exact convex_iInter fun i => (hf i).convex_le _

/-! ### Theorem 4.7 and its corollaries -/

/-- **Theorem 4.7.** A positively homogeneous `f : ℝⁿ → (-∞, +∞]` is convex iff it is
subadditive, `f (x + y) ≤ f x + f y`. -/
theorem theorem_4_7 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hbot : ∀ x, f x ≠ ⊥) :
    ConvexFn f ↔ ∀ x y : Rn n, f (x + y) ≤ f x + f y :=
  hf.convexFn_iff_subadditive hbot

/-- **Corollary 4.7.1.** For positively homogeneous proper convex `f`,
`f (λ₁x₁ + ⋯ + λₘxₘ) ≤ λ₁ f x₁ + ⋯ + λₘ f xₘ` whenever every `λᵢ > 0`.

The index range must be non-empty, which the book's `λ₁, …, λₘ` implies: the empty sum would
assert `f 0 ≤ 0`, and such an `f` may have `f 0 = +∞` — take `δ(·|C)` for a convex cone `C`
missing the origin. -/
theorem corollary_4_7_1 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : Proper f) {m : ℕ} (hm : 0 < m) {l : Fin m → ℝ} (hl : ∀ i, 0 < l i)
    (x : Fin m → Rn n) : f (∑ i, l i • x i) ≤ ∑ i, (l i : EReal) * f (x i) :=
  hf.sum_le hconv hproper.ne_bot ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i _ => hl i) x

/-- **Corollary 4.7.2.** For positively homogeneous proper convex `f`, `f (-x) ≥ -f x`. -/
theorem corollary_4_7_2 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : Proper f) (x : Rn n) : -(f x) ≤ f (-x) :=
  hf.neg_le hconv hproper.ne_bot x

/-! ### Theorem 4.8 -/

/-- **Theorem 4.8.** A positively homogeneous proper convex `f` is linear on a subspace `L` iff
`f (-x) = -f x` for every `x ∈ L`. "Linear on `L`" is the existence of a genuine linear functional
`L →ₗ[ℝ] ℝ` agreeing with `f` there; extracting one is part of the content, since a function odd
at `x` is automatically finite there. -/
theorem theorem_4_8 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : Proper f) (L : Submodule ℝ (Rn n)) :
    (∃ g : L →ₗ[ℝ] ℝ, ∀ x : L, f x = ((g x : ℝ) : EReal)) ↔ ∀ x ∈ L, f (-x) = -(f x) :=
  hf.exists_linearMap_iff hconv hproper.ne_bot L

/-- **Theorem 4.8**, final sentence: it suffices that `f (-bᵢ) = -f bᵢ` on a spanning set of `L`.
Stated for an arbitrary *non-empty* spanning set rather than a basis. Non-emptiness is not
decoration: the book's argument uses `f 0 = 0`, which is available only once some vector is known
to be odd, so for `L = {0}` with an empty basis the statement fails as printed — a positively
homogeneous proper convex `f` may have `f 0 = +∞`. -/
theorem theorem_4_8_basis {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : Proper f) {L : Submodule ℝ (Rn n)} {b : Set (Rn n)} (hb : b.Nonempty)
    (hspan : Submodule.span ℝ b = L) (hodd : ∀ v ∈ b, f (-v) = -(f v)) :
    ∀ x ∈ L, f (-x) = -(f x) := by
  subst hspan
  exact fun x hx => hf.neg_eq_of_mem_span hconv hproper.ne_bot hb hodd hx

end Rockafellar
