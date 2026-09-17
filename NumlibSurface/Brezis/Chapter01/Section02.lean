import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Normed.Module.Annihilator
import NumlibSurface.Brezis.Chapter01.Section01

/-!
# Brezis §1.2: the geometric forms of the Hahn–Banach theorem

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §1.2: separation of convex sets in a real normed space
`E`. The book's vocabulary is defined in its own generality — an affine hyperplane `[f = α]` is
the level set of a nonzero linear functional that is *not* assumed continuous (footnote 3), and
a hyperplane separates or strictly separates two sets — and bridged, for continuous `f`, to the
backbone's `ConvexAnalysis.Separates` / `SeparatesStrongly` (`Numlib/Analysis/Convex/Separation`).
The theorems are Mathlib's: Proposition 1.5 is `LinearMap.continuous_iff_isClosed_ker`, Theorem
1.6 is `geometric_hahn_banach_open`, Lemma 1.2 is the API of `gauge`, Lemma 1.3 is
`geometric_hahn_banach_open_point`, Theorem 1.7 is `geometric_hahn_banach_closed_compact`,
Corollary 1.8 is the backbone's `Submodule.exists_dual_eq_zero_of_notMem`, Remark 4's
finite-dimensional clause is the backbone's proper-separation theorem
`ConvexAnalysis.exists_separatesProperly_iff_disjoint_relint`, and the Comments' Theorem 1.13
(Krein–Milman) is `closure_convexHull_extremePoints`.

## Main results

* `IsHyperplane`, `proposition_1_5` — affine hyperplanes; `[f = α]` is closed iff `f` is
  continuous.
* `Separates`, `StrictlySeparates` with `separates_iff`, `strictlySeparates_iff` — the book's
  two notions of separation and their identification with the backbone's.
* `theorem_1_6`, `lemma_1_2`, `lemma_1_3`, `theorem_1_7` — the first geometric form, the gauge,
  the separation of a point from an open convex set, the second geometric form. "A closed
  hyperplane separates `A` and `B`" is stated literally: some linear `f ≠ 0` and `α` with
  `[f = α]` closed and separating.
* `remark_1_4` — in finite dimension any two disjoint nonempty convex sets are separated.
* `corollary_1_8`, `remark_1_5` — a non-dense subspace is annihilated by a nonzero functional;
  the density criterion.
* `theorem_1_13` — Krein–Milman.

Remark 4's first clause (two disjoint closed convex subsets of `ℓ¹` that no closed hyperplane
separates, Exercise 1.14) is not formalized.
-/

open Metric Set

namespace Brezis.Chapter01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Hyperplanes and separation -/

/-- **The Definition of an affine hyperplane**: a subset `H = [f = α] = {x | f x = α}` of `E`
with `f` a linear functional that does not vanish identically — `f` is *not* assumed continuous
(footnote 3) — and `α ∈ ℝ`. -/
def IsHyperplane (H : Set E) : Prop :=
  ∃ (f : E →ₗ[ℝ] ℝ) (α : ℝ), f ≠ 0 ∧ H = {x | f x = α}

/-- **Proposition 1.5.** The hyperplane `H = [f = α]` is closed if and only if `f` is
continuous. -/
theorem proposition_1_5 (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0) (α : ℝ) :
    IsClosed {x | f x = α} ↔ Continuous f := by
  refine ⟨fun h => ?_, fun h => isClosed_singleton.preimage h⟩
  -- `[f = α]` is a translate of `ker f`
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (LinearMap.ext hcon)
  set x₁ : E := (α / f x) • x with hx₁
  have hfx₁ : f x₁ = α := by rw [hx₁, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
  have hker : (LinearMap.ker f : Set E) = (fun y => y + x₁) ⁻¹' {x | f x = α} := by
    ext y
    simp [hfx₁]
  rw [LinearMap.continuous_iff_isClosed_ker, hker]
  exact h.preimage (continuous_id.add continuous_const)

/-- **The Definition of separation**: the hyperplane `[f = α]` separates `A` and `B` when
`f x ≤ α` on `A` and `f x ≥ α` on `B`, for a linear `f` as in `IsHyperplane`. -/
def Separates (f : E →ₗ[ℝ] ℝ) (α : ℝ) (A B : Set E) : Prop :=
  (∀ x ∈ A, f x ≤ α) ∧ ∀ x ∈ B, α ≤ f x

/-- For a continuous `f`, the book's separation is the backbone's `ConvexAnalysis.Separates`. -/
theorem separates_iff (f : StrongDual ℝ E) (α : ℝ) (A B : Set E) :
    Separates (f : E →ₗ[ℝ] ℝ) α A B ↔ ConvexAnalysis.Separates f α A B :=
  ⟨fun h => ⟨fun x hx => h.1 x hx, fun x hx => h.2 x hx⟩,
    fun h => ⟨fun _ hx => h.le_of_mem_left hx, fun _ hx => h.le_of_mem_right hx⟩⟩

/-- **The Definition of strict separation**: `[f = α]` strictly separates `A` and `B` when for
some `ε > 0`, `f x ≤ α - ε` on `A` and `f x ≥ α + ε` on `B`. -/
def StrictlySeparates (f : E →ₗ[ℝ] ℝ) (α : ℝ) (A B : Set E) : Prop :=
  ∃ ε > 0, (∀ x ∈ A, f x ≤ α - ε) ∧ ∀ x ∈ B, α + ε ≤ f x

/-- For a continuous `f`, the book's strict separation is the backbone's
`ConvexAnalysis.SeparatesStrongly` (whose gap form is this definition word for word). -/
theorem strictlySeparates_iff (f : StrongDual ℝ E) (α : ℝ) (A B : Set E) :
    StrictlySeparates (f : E →ₗ[ℝ] ℝ) α A B ↔ ConvexAnalysis.SeparatesStrongly f α A B :=
  ConvexAnalysis.separatesStrongly_iff_exists_gap.symm

/-- A nonzero continuous functional is nonzero as a linear map. -/
private theorem coe_ne_zero {f : StrongDual ℝ E} (hf : f ≠ 0) : (f : E →ₗ[ℝ] ℝ) ≠ 0 :=
  fun h =>
    hf (ContinuousLinearMap.coe_injective (h.trans ContinuousLinearMap.toLinearMap_zero.symm))

/-! ### The two geometric forms -/

/-- **Theorem 1.6 (Hahn–Banach, first geometric form).** Let `A, B ⊆ E` be two nonempty convex
subsets with `A ∩ B = ∅`, one of which is open. Then there is a closed hyperplane `[f = α]`
separating `A` and `B`. -/
theorem theorem_1_6 {A B : Set E} (hA : Convex ℝ A) (hAne : A.Nonempty) (hB : Convex ℝ B)
    (hBne : B.Nonempty) (hAB : Disjoint A B) (hopen : IsOpen A ∨ IsOpen B) :
    ∃ (f : E →ₗ[ℝ] ℝ) (α : ℝ), f ≠ 0 ∧ IsClosed {x | f x = α} ∧ Separates f α A B := by
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  rcases hopen with hAo | hBo
  · obtain ⟨f, u, hfA, hfB⟩ := geometric_hahn_banach_open hA hAo hB hAB
    have hne : f ≠ 0 := by
      rintro rfl
      have := (hfA a ha).trans_le (hfB b hb)
      simp at this
    exact ⟨f, u, coe_ne_zero hne, isClosed_eq f.continuous continuous_const,
      fun x hx => (hfA x hx).le, fun x hx => hfB x hx⟩
  · obtain ⟨f, u, hfB, hfA⟩ := geometric_hahn_banach_open hB hBo hA hAB.symm
    have hne : f ≠ 0 := by
      rintro rfl
      have := (hfB b hb).trans_le (hfA a ha)
      simp at this
    refine ⟨-f, -u, coe_ne_zero (neg_ne_zero.2 hne), isClosed_eq (-f).continuous continuous_const,
      fun x hx => ?_, fun x hx => ?_⟩
    · have := hfA x hx
      simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
      linarith
    · have := hfB x hx
      simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
      linarith

/-- **Lemma 1.2 (the gauge).** Let `C ⊆ E` be an open convex set with `0 ∈ C` and
`p x = inf {α > 0 | α⁻¹ x ∈ C}` its gauge (Minkowski functional), Mathlib's `gauge C`. Then `p`
satisfies (1) `p (λ x) = λ p x` for `λ > 0`, (2) `p (x + y) ≤ p x + p y`, (9) `0 ≤ p x ≤ M ‖x‖`
for some constant `M`, and (10) `C = {x | p x < 1}`. -/
theorem lemma_1_2 {C : Set E} (hC : Convex ℝ C) (hCo : IsOpen C) (h0 : (0 : E) ∈ C) :
    (∀ l : ℝ, 0 < l → ∀ x, gauge C (l • x) = l * gauge C x) ∧
      (∀ x y, gauge C (x + y) ≤ gauge C x + gauge C y) ∧
      (∃ M : ℝ, ∀ x, 0 ≤ gauge C x ∧ gauge C x ≤ M * ‖x‖) ∧
      C = {x | gauge C x < 1} := by
  obtain ⟨r, hr, hrC⟩ := Metric.isOpen_iff.1 hCo 0 h0
  refine ⟨fun l hl x => gauge_smul_of_nonneg hl.le x,
    gauge_add_le hC (absorbent_nhds_zero (hCo.mem_nhds h0)), ⟨r⁻¹, fun x => ⟨gauge_nonneg x, ?_⟩⟩,
    (setOfPred_gauge_lt_one_eq_self_of_isOpen hC h0 hCo).symm⟩
  rw [← div_eq_inv_mul, le_div_iff₀' hr]
  exact mul_gauge_le_norm hrC

/-- **Lemma 1.3.** Let `C ⊆ E` be a nonempty open convex set and `x₀ ∉ C`. Then there is
`f ∈ E*` with `f x < f x₀` for all `x ∈ C`; in particular the hyperplane `[f = f x₀]` separates
`{x₀}` and `C`. -/
theorem lemma_1_3 {C : Set E} (hC : Convex ℝ C) (hCne : C.Nonempty) (hCo : IsOpen C) {x₀ : E}
    (hx₀ : x₀ ∉ C) :
    ∃ f : StrongDual ℝ E, (∀ x ∈ C, f x < f x₀) ∧ f ≠ 0 ∧ Separates f (f x₀) C {x₀} := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hC hCo hx₀
  obtain ⟨c, hc⟩ := hCne
  have hne : f ≠ 0 := by
    rintro rfl
    exact lt_irrefl _ (hf c hc)
  exact ⟨f, hf, hne, fun x hx => (hf x hx).le,
    fun x hx => by rw [mem_singleton_iff.1 hx]; exact le_rfl⟩

/-- **Theorem 1.7 (Hahn–Banach, second geometric form).** Let `A, B ⊆ E` be two nonempty convex
subsets with `A ∩ B = ∅`, `A` closed and `B` compact. Then there is a closed hyperplane
`[f = α]` strictly separating `A` and `B`. -/
theorem theorem_1_7 {A B : Set E} (hA : Convex ℝ A) (hAne : A.Nonempty) (hAc : IsClosed A)
    (hB : Convex ℝ B) (hBne : B.Nonempty) (hBc : IsCompact B) (hAB : Disjoint A B) :
    ∃ (f : E →ₗ[ℝ] ℝ) (α : ℝ), f ≠ 0 ∧ IsClosed {x | f x = α} ∧ StrictlySeparates f α A B := by
  obtain ⟨f, u, v, hfA, huv, hfB⟩ := geometric_hahn_banach_closed_compact hA hAc hB hBc hAB
  have hsep := ConvexAnalysis.separatesStrongly_of_forall_lt hfA huv hfB
  exact ⟨f, (u + v) / 2, coe_ne_zero (hsep.ne_zero hAne hBne),
    isClosed_eq f.continuous continuous_const, (strictlySeparates_iff f _ A B).2 hsep⟩

/-- **Remark 4, the finite-dimensional clause.** If `E` is finite-dimensional, any two nonempty
disjoint convex sets `A`, `B` are separated by a closed hyperplane, with no further assumption
(Exercise 1.9). -/
theorem remark_1_4 [FiniteDimensional ℝ E] {A B : Set E} (hA : Convex ℝ A) (hAne : A.Nonempty)
    (hB : Convex ℝ B) (hBne : B.Nonempty) (hAB : Disjoint A B) :
    ∃ (f : E →ₗ[ℝ] ℝ) (α : ℝ), f ≠ 0 ∧ IsClosed {x | f x = α} ∧ Separates f α A B := by
  obtain ⟨f, α, hsep⟩ :=
    (ConvexAnalysis.exists_separatesProperly_iff_disjoint_relint hA hB hAne hBne).2
      (hAB.mono intrinsicInterior_subset intrinsicInterior_subset)
  exact ⟨f, α, coe_ne_zero (hsep.ne_zero hAne hBne), isClosed_eq f.continuous continuous_const,
    (separates_iff f α A B).2 hsep.toSeparates⟩

/-! ### Corollary 1.8 and the density criterion -/

/-- **Corollary 1.8.** Let `F ⊆ E` be a linear subspace with `closure F ≠ E`. Then there is
`f ∈ E*`, `f ≢ 0`, with `⟨f, x⟩ = 0` for all `x ∈ F`. -/
theorem corollary_1_8 {F : Submodule ℝ E} (hF : F.topologicalClosure ≠ ⊤) :
    ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ x ∈ F, f x = 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ F.topologicalClosure := by
    by_contra hcon
    push Not at hcon
    exact hF (Submodule.eq_top_iff'.2 hcon)
  obtain ⟨f, hf1, hf0, hfx⟩ :=
    F.topologicalClosure.exists_dual_eq_zero_of_notMem F.isClosed_topologicalClosure hx₀
  exact ⟨f, fun h => hfx (by simp [h]), fun x hx => hf0 x (F.le_topologicalClosure hx)⟩

/-- **Remark 5.** A linear subspace `F ⊆ E` is dense iff every continuous linear functional on
`E` that vanishes on `F` vanishes everywhere on `E`. -/
theorem remark_1_5 (F : Submodule ℝ E) :
    Dense (F : Set E) ↔ ∀ f : StrongDual ℝ E, (∀ x ∈ F, f x = 0) → f = 0 := by
  rw [← Submodule.strongDualAnnihilator_eq_bot_iff, Submodule.eq_bot_iff]
  simp only [Submodule.mem_strongDualAnnihilator]

/-! ### Krein–Milman -/

/-- **Theorem 1.13 (Krein–Milman; Comments on Chapter 1).** A compact convex subset `K` of `E`
coincides with the closed convex hull of its extremal points,
`K = closure (conv (extremal points of K))`; the book's extremal points are Mathlib's
`K.extremePoints ℝ` and its `conv` is `convexHull ℝ`. -/
theorem theorem_1_13 {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) :
    closure (convexHull ℝ (K.extremePoints ℝ)) = K :=
  closure_convexHull_extremePoints hK hKc

end Brezis.Chapter01
