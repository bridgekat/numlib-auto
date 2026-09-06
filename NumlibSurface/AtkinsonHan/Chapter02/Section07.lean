import Mathlib.Analysis.InnerProductSpace.Dual
import Numlib.Analysis.Convex.Uniform
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Normed.Module.WeakDual
import NumlibSurface.AtkinsonHan.Chapter03.Section03

/-!
# Atkinson–Han §2.7: weak convergence

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.7.

Definition 2.7.1, weak convergence of a sequence, is already in this surface as
`AtkinsonHan.Chapter03.WeakSeqTendsto`, introduced in §3.3 for Example 3.3.5 before this section was
planned; it is reused here rather than defined a second time.

## Main results

* `proposition_2_7_2` — a weakly convergent sequence is bounded.
* `exercise_2_7_2` — the norm is weakly sequentially lower semicontinuous, `‖u‖ ≤ liminf ‖uₙ‖`.
* `example_2_7_3` — `sin (n x) ⇀ 0` in `L²(0, 2π)` but not in norm; this is also the example that
  makes the inequality of `exercise_2_7_2` strict.
* `exercise_2_7_3`, `exercise_2_7_4` — the Radon–Riesz property, in an inner product space and in
  a uniformly convex Banach space.

The two general facts are the backbone's: `exists_norm_le_of_tendsto_toWeakSpace` and
`norm_le_liminf_norm_of_weak_tendsto` (`Numlib/Analysis/Normed/Module/WeakDual`), stated there for
Mathlib's `WeakSpace` topology and carried across by `tendsto_toWeakSpace_iff`; and
`tendsto_of_forall_inner_tendsto_of_tendsto_norm`, `tendsto_of_forall_dual_tendsto_of_tendsto_norm`
(`Numlib/Analysis/Convex/Uniform`).

Example 2.7.3 is read on the circle: `L²(0, 2π)` is `L²(AddCircle (2π))`, and the book's `sin (n x)`
is `trigFun (2π) (-n)` up to the normalisation of Theorem 1.3.13 — an orthonormal sequence, which
is what makes it weakly null and of constant norm.

## Not formalized here

Theorem 2.7.5 — a Banach space is reflexive if and only if every bounded sequence has a weakly
convergent subsequence — is not planned, and neither is **Definition 2.7.4**, reflexivity itself:
`exercise_2_7_4` below is Exercise 2.7.4, the Radon–Riesz property in a uniformly convex space, and
is a different result from the Definition that precedes Theorem 2.7.5. The obstruction to the
Theorem is that it is the Eberlein–Šmulian theorem together with
Kakutani's characterisation of reflexivity, and Mathlib has neither reflexivity as a class nor
Banach–Alaoglu in a form that would give it. Everything in the book that consumes it (Theorems
3.3.8, 3.3.10–3.3.12, 3.3.14 and Mazur's lemma) is already recorded as unplanned in
`Numlib/Variational/Minimization`. Example 2.7.3's uniform-integrability criterion
(Dunford–Pettis) is not planned for the same reason, and neither is part (b) of Exercise 2.7.4,
the uniform convexity of `Lᵖ` by the Clarkson inequalities.
-/

open Filter MeasureTheory Topology

open scoped Real

namespace AtkinsonHan.Chapter02

section General

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Proposition 2.7.2.** A weakly convergent sequence in a normed space is bounded. This is the
principle of uniform boundedness applied to the images of the `uₙ` in the double dual. -/
theorem proposition_2_7_2 {v : ℕ → V} {u : V} (h : Chapter03.WeakSeqTendsto 𝕜 v u) :
    ∃ C : ℝ, ∀ n, ‖v n‖ ≤ C :=
  exists_norm_le_of_tendsto_toWeakSpace (tendsto_toWeakSpace_iff.2 h)

/-- **Exercise 2.7.2.** `uₙ ⇀ u` implies `‖u‖ ≤ liminf ‖uₙ‖`: the norm is weakly sequentially
lower semicontinuous. The book proves the same statement twice; it is `Chapter03.example_3_3_5`.
`example_2_7_3` is an instance in which the inequality is strict. -/
theorem exercise_2_7_2 {v : ℕ → V} {u : V} (h : Chapter03.WeakSeqTendsto 𝕜 v u) :
    ‖u‖ ≤ liminf (fun n => ‖v n‖) atTop :=
  norm_le_liminf_norm_of_weak_tendsto (tendsto_toWeakSpace_iff.2 h)

end General

/-! ### Example 2.7.3 -/

section Example

/-- In a Hilbert space, weak convergence of a sequence is convergence of every inner product,
by the Riesz representation of the dual. -/
theorem weakSeqTendsto_iff_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {v : ℕ → H} {u : H} :
    Chapter03.WeakSeqTendsto ℝ v u ↔
      ∀ w : H, Tendsto (fun n => inner ℝ (v n) w) atTop (𝓝 (inner ℝ u w)) := by
  constructor
  · intro h w
    have h' := h (InnerProductSpace.toDual ℝ H w)
    simp only [InnerProductSpace.toDual_apply_apply] at h'
    simpa only [real_inner_comm] using h'
  · intro h ℓ
    obtain ⟨w, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective ℓ
    simp only [InnerProductSpace.toDual_apply_apply]
    simpa only [real_inner_comm] using h w

/-- An orthonormal sequence in a Hilbert space converges weakly to `0`: its inner products against
a fixed vector are square-summable by Bessel's inequality, hence tend to zero. -/
theorem weakSeqTendsto_zero_of_orthonormal {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {φ : ι → H} (hφ : Orthonormal ℝ φ) {g : ℕ → ι}
    (hg : Function.Injective g) : Chapter03.WeakSeqTendsto ℝ (fun n => φ (g n)) 0 := by
  refine weakSeqTendsto_iff_inner.2 fun w => ?_
  have hgt : Tendsto g atTop cofinite := Nat.cofinite_eq_atTop ▸ hg.tendsto_cofinite
  have h1 : Tendsto (fun n => ‖inner ℝ (φ (g n)) w‖ ^ 2) atTop (𝓝 0) :=
    (hφ.inner_products_summable w).tendsto_cofinite_zero.comp hgt
  have h2 : Tendsto (fun n => ‖inner ℝ (φ (g n)) w‖) atTop (𝓝 0) := by
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h3
  simpa using tendsto_zero_iff_norm_tendsto_zero.2 h2

local instance instTwoPiPos : Fact (0 < 2 * π) := Fact.mk Real.two_pi_pos

/-- **Example 2.7.3.** The sequence `sin (n x)` converges weakly to `0` in `L²(0, 2π)` but not in
norm: it is orthonormal, so every inner product against it tends to zero by Bessel's inequality,
while its terms all have norm `1`. Read on the circle, the book's `sin (n x)` normalised for the
probability Haar measure is `trigFun (2π) (-n)` of Theorem 1.3.13.

Since the weak limit is `0` and every term has norm `1`, this is also an example in which the
inequality of `exercise_2_7_2` is strict. -/
theorem example_2_7_3 :
    Chapter03.WeakSeqTendsto ℝ (fun n : ℕ => trigLp (2 * π) (-(n + 1) : ℤ)) 0 ∧
      (∀ n : ℕ, ‖trigLp (2 * π) (-(n + 1) : ℤ)‖ = 1) ∧
      ¬ Tendsto (fun n : ℕ => trigLp (2 * π) (-(n + 1) : ℤ)) atTop (𝓝 0) := by
  have hinj : Function.Injective fun n : ℕ => (-(n + 1) : ℤ) := by
    intro a b hab
    simpa using hab
  have hnorm : ∀ n : ℕ, ‖trigLp (2 * π) (-(n + 1) : ℤ)‖ = 1 := fun n =>
    orthonormal_trigFun.1 (-(n + 1) : ℤ)
  refine ⟨weakSeqTendsto_zero_of_orthonormal orthonormal_trigFun hinj, hnorm, fun h => ?_⟩
  have h1 : Tendsto (fun n : ℕ => ‖trigLp (2 * π) (-(n + 1) : ℤ)‖) atTop (𝓝 0) := by
    simpa using h.norm
  rw [tendsto_congr hnorm] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

end Example

/-! ### The Radon–Riesz property -/

/-- **Exercise 2.7.3.** In a Hilbert space, `uₙ → u` if and only if `uₙ ⇀ u` and `‖uₙ‖ → ‖u‖`:
weak convergence together with convergence of the norms is convergence. -/
theorem exercise_2_7_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {v : ℕ → H} {u : H} :
    Tendsto v atTop (𝓝 u) ↔
      Chapter03.WeakSeqTendsto ℝ v u ∧ Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖u‖) := by
  rw [tendsto_of_forall_inner_tendsto_of_tendsto_norm (𝕜 := ℝ), weakSeqTendsto_iff_inner]

/-- **Exercise 2.7.4 (a), (c)**, the Radon–Riesz property. In a uniformly convex Banach space —
a Hilbert space in particular, by Mathlib's `InnerProductSpace.toUniformConvexSpace` — weak
convergence together with convergence of the norms implies convergence in norm. -/
theorem exercise_2_7_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]
    {v : ℕ → E} {u : E} (hweak : Chapter03.WeakSeqTendsto ℝ v u)
    (hnorm : Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖u‖)) : Tendsto v atTop (𝓝 u) :=
  tendsto_of_forall_dual_tendsto_of_tendsto_norm hweak hnorm

end AtkinsonHan.Chapter02
