import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.SpecialFunctions.FlatFunctions
import Numlib.Analysis.Calculus.Gradient
import Numlib.Analysis.InnerProductSpace.NormPow
import Numlib.Optimization.Complexity.SlowExampleHighOrder
import Numlib.Optimization.Optimality.CurveConditions
import Numlib.Optimization.Optimality.HighOrder
import Numlib.Optimization.Optimality.TaylorStability
import NumlibSurface.CartisGouldToint.Chapter01.Section01

/-!
# Cartis–Gould–Toint §12.1: Optimality conditions revisited

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §12.1: curve-based necessary
conditions of arbitrary order, the Taylor-decrement measure `φ^δ_{f,j}`, `(ε, δ)`-approximate
minimizers and their stability. Points live in `ℝⁿ = EuclideanSpace ℝ (Fin n)`; the univariate
examples are stated on `ℝ`. Tensor norms are Mathlib operator norms; `∇^j f(x)[s]^j` is
`iteratedFDeriv ℝ j f x (fun _ => s)`; `f ∈ C^∞` is `ContDiff ℝ ∞ f`.

## Main definitions

* `phiMeasure f j δ x = φ^δ_{f,j}(x)` (12.1.10), an abbreviation of `Optimization.taylorMeasure`;
* `IsQthOrderMinimizer f x q`: the conclusions of Theorem 12.1.1 hold for `j ∈ [1, q]`;
* `peanoQuartic κ₁ κ₂` (12.1.8), `hancock`, `lewis` ((12.1.2), (12.1.3));
* `IsEpsDeltaApproxMinimizer f q ε δ x`: Key Definition (12.1.25).

## Main results

* `example_12_1_1`, `example_12_1_1_variant`, `example_12_1_2`, `example_12_1_3`,
  `example_12_1_4`: the examples of §12.1;
* `theorem_12_1_1` – `theorem_12_1_8`.

## Deviations from the book

* **Theorem 12.1.5 is false as printed** (`theorem_12_1_5_counterexample`): an isolated minimizer
  `s = 0` of `T_{f,j}(x, ·)` need not be uniformly isolated. `theorem_12_1_5` assumes growth of
  order `j`, `c ‖s‖^j ≤ T_{f,j}(x, s) - f(x)` near `0`.
* **Example 12.1.2.** The printed choice "`κ₁ = 1`, `κ₂ = 2`" does not give a saddle
  (`f = (x₂ - x₁²/2)² + 7x₁⁴/4 ≥ 0`); the saddle needs `κ₁² > 4κ₂ ≥ 0`, e.g. `κ₁ = 3`, `κ₂ = 2`
  (the curve `x₂ = 3x₁²/2` and Figure 12.1.2 use `κ₁ = 3`). Theorem 12.1.2 is stated for
  `peanoQuartic 3 2`. The tensor entries of the example are stated through the diagonal values
  `∇^k f(0)[d]^k`, which determine symmetric tensors.
* **Example 12.1.1.** The printed descent curve `αe₂ + ½exp(-1/2α²)e₁` is garbled; the curve
  `(t, ½exp(-1/t²))` is used.
* **Theorem 12.1.1.** The restriction to tuples of nonzero `s_i` is dropped (stronger statement).
* **Theorems 12.1.3 and 12.1.6.** The identities hold for every `f` (Lean's derivatives are total
  functions); in (ii) of Theorem 12.1.6 the book's "continuously differentiable" does not even
  make `∇²f(x)` meaningful. The constant `κ(x)` of Theorem 12.1.6 (ii) is made explicit:
  `‖∇f(x)‖² ≤ δ² ε₂ max(‖∇²f(x)‖, ε₂)`. The projected norm of Theorem 12.1.3 (iii) is
  `‖P_M[T]‖ = sup_{d ∈ M, ‖d‖ ≤ 1} |T[d]³|` with `M = ker¹[∇f(x)] ∩ ker²[∇²f(x)]`, for which the
  first- and second-order hypotheses are not needed.
* **Theorem 12.1.7.** The condition `δ_j ≤ jε_j/(2‖∇^j f(x)‖)` is written multiplicatively (so
  that `∇^j f(x) = 0` is allowed). The recursive use after the theorem needs `ε_q ≤ ⋯ ≤ ε_1`
  (the printed chain is reversed).
* **Theorem 12.1.8.** The printed `δ^j` in (12.1.35) is `δ_j^j`.
* **Example 12.1.3.** Part (iv) (vanishing measures for radii `δ ≤ 3‖x*‖/(p-1)`) is stated in one
  variable. The book's appeal to Lemma B.4.1 for the directions orthogonal to `x*` does not cover
  mixed directions, and the `n`-dimensional claim fails: for `p = 3`, `σ = p!`, `‖x*‖ = 1` and
  `δ = 3/2 = 3‖x*‖/(p-1)`, the decrement `ΔT_{m,3}(x*, d)` is about `+0.14` at
  `d ≈ (-1.12, 0.28, 0.96)`, where (12.1.16) predicts `φ^δ_{m,3}(x*) = 0`
  (`example1213_taylorDecrement_unit` gives the decrement in every direction).
  Part (iii) is stated as the book's equality `φ^1_{m,3}(x*) = (p-4)σ/(6(p-1)!)`, proved for
  all directions.

## Not formalized

The weak approximate minimizers (12.1.40) of the notes, the projected-norm relaxation (12.1.24),
the asymptotic `O(ε₂)` remark after Theorem 12.1.6 and the discussion of §12.1.6 (approximate
displacements are in `Optimization.IsApproxMeasureStep`).
-/

open Set Filter Topology Metric
open scoped Nat ContDiff RealInnerProductSpace

namespace CartisGouldToint.Chapter12

/-! ### The measure `φ^δ_{f,j}` -/

section Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The measure `φ^δ_{f,j}(x) = f(x) - min_{‖d‖ ≤ δ} T_{f,j}(x, d) = max_{‖d‖ ≤ δ} ΔT_{f,j}(x, d)`
of [cartis2022evaluation], (12.1.10)–(12.1.11): the largest decrease of the `j`-th order Taylor
model within distance `δ`. -/
noncomputable abbrev phiMeasure (f : E → ℝ) (j : ℕ) (δ : ℝ) (x : E) : ℝ :=
  Optimization.taylorMeasure (ftaylorSeries ℝ f x) j δ univ

/-- (12.1.10): `φ^δ_{f,j}(x) = sup_{‖d‖ ≤ δ} (f(x) - T_{f,j}(x, d))`. -/
theorem phiMeasure_eq_sSup (f : E → ℝ) (j : ℕ) (δ : ℝ) (x : E) :
    phiMeasure f j δ x = sSup ((fun d => f x - taylorPolynomial f j x d) '' closedBall 0 δ) := by
  rw [phiMeasure, Optimization.taylorMeasure_eq_sSup, inter_univ]
  congr 1
  refine image_congr fun d _ => ?_
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right]

/-- The measure is nonnegative for `δ ≥ 0`. -/
theorem phiMeasure_nonneg (f : E → ℝ) (j : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    0 ≤ phiMeasure f j δ x :=
  Optimization.taylorMeasure_nonneg _ j (mem_univ 0) hδ

/-- Every model decrease within distance `δ` is at most the measure. -/
theorem sub_taylorPolynomial_le_phiMeasure (f : E → ℝ) (j : ℕ) {δ : ℝ} (x : E) {d : E}
    (hd : ‖d‖ ≤ δ) : f x - taylorPolynomial f j x d ≤ phiMeasure f j δ x := by
  have := Optimization.taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ f x) j (S := univ)
    (d := d) (δ := δ) ⟨mem_closedBall_zero_iff.2 hd, mem_univ d⟩
  rwa [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right] at this

end Measure



/-! ### Curve-based conditions (§12.1.2) -/

section Curve

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- `x` is a *`q`-th order minimizer* of `f` ([cartis2022evaluation], §12.1.2, after
Theorem 12.1.1): the conclusions (12.1.6)–(12.1.7) of Theorem 12.1.1 hold for all `j ∈ [1, q]`,
with the coefficients `Optimization.curveCoeff` built on the index sets `P(j,k)` of (12.1.5). -/
def IsQthOrderMinimizer (f : 𝔼 → ℝ) (x : 𝔼) (q : ℕ) : Prop :=
  Optimization.IsCurveCritical (ftaylorSeries ℝ f x) q

theorem isQthOrderMinimizer_iff {f : 𝔼 → ℝ} {x : 𝔼} {q : ℕ} :
    IsQthOrderMinimizer f x q ↔ ∀ j ∈ Finset.Icc 1 q, ∀ s : ℕ → 𝔼,
      (∀ i ∈ Finset.Ico 1 j, Optimization.curveCoeff (ftaylorSeries ℝ f x) s i = 0) →
        0 ≤ Optimization.curveCoeff (ftaylorSeries ℝ f x) s j :=
  Iff.rfl

/-- **Theorem 12.1.1** ([cartis2022evaluation]): if `f` is `C^q` near a local minimizer `x`, then
for every `j ∈ [1, q]` and every `s_1, s_2, …` such that the coefficients (12.1.7) of orders
`1, …, j-1` vanish, the coefficient (12.1.6) of order `j`,
`∑_{k=1}^j (1/k!) ∑_{(ℓ_1,…,ℓ_k) ∈ P(j,k)} ∇^k f(x)[s_{ℓ_1}, …, s_{ℓ_k}]`, is nonnegative: `x` is
a `q`-th order minimizer. (The book's restriction to nonzero `s_i` is unnecessary.) -/
theorem theorem_12_1_1 {f : 𝔼 → ℝ} {x : 𝔼} {q : ℕ} (hf : ContDiffAt ℝ q f x)
    (hmin : IsLocalMin f x) : IsQthOrderMinimizer f x q :=
  hmin.isCurveCritical hf

end Curve

/-! ### Examples in the plane (§12.1.1, §12.1.2, §12.1.4) -/

section Plane

/-- Coordinates of `ℝᵐ` are smooth. -/
theorem contDiff_coord {m : ℕ} {k : WithTop ℕ∞} (i : Fin m) :
    ContDiff ℝ k fun x : EuclideanSpace ℝ (Fin m) => x i :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).contDiff

/-! #### Hancock's example -/

/-- Hancock's example ([cartis2022evaluation], (12.1.2)): `f(x) = x₂ (x₂ - exp(-1/x₁²))` for
`x₁ ≠ 0` and `f(x) = x₂²` for `x₁ = 0`, on `ℝ²` (the book's `x₁, x₂` are `x 0, x 1`). -/
noncomputable def hancock (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if x 0 ≠ 0 then x 1 * (x 1 - Real.exp (-1 / x 0 ^ 2)) else x 1 ^ 2

theorem hancock_eq (x : EuclideanSpace ℝ (Fin 2)) :
    hancock x = x 1 * (x 1 - expNegInvGlue (x 0 ^ 2)) := by
  unfold hancock
  split_ifs with h
  · have hpos : 0 < x 0 ^ 2 := by positivity
    rw [expNegInvGlue, ite_eq_right_iff.2 fun h => absurd h (not_le.2 hpos), neg_div, one_div]
  · push Not at h
    simp [h, sq]

/-- **Example 12.1.1** ([cartis2022evaluation], (12.1.2), Hancock). For `f = hancock`:
(a) `f` is `C^∞`; (b) the origin is a local minimizer of `f` along every line (no line is a
descent line); (c) along the curve `(t, ½ exp(-1/t²))`,
`f = -¼ exp(-1/t²)² = -¼ exp(-2/t²) < 0`, so the origin is not a local minimizer; (d) `f` and
`g(x) = x₂²` have the same derivatives of every order at the origin, while the origin is a global
minimizer of `g`: no condition on the Taylor coefficients at `0` decides local minimality. -/
theorem example_12_1_1 :
    ContDiff ℝ ∞ hancock ∧
    (∀ d : EuclideanSpace ℝ (Fin 2), IsLocalMin (fun t : ℝ => hancock (t • d)) 0) ∧
    (∀ t : ℝ, t ≠ 0 →
      hancock (!₂[t, Real.exp (-1 / t ^ 2) / 2]) = -Real.exp (-1 / t ^ 2) ^ 2 / 4) ∧
    ¬ IsLocalMin hancock 0 ∧
    (∀ k : ℕ, iteratedFDeriv ℝ k hancock 0 =
      iteratedFDeriv ℝ k (fun x : EuclideanSpace ℝ (Fin 2) => x 1 ^ 2) 0) ∧
    IsMinOn (fun x : EuclideanSpace ℝ (Fin 2) => x 1 ^ 2) univ 0 := by
  have hfun : hancock = fun x => x 1 * (x 1 - expNegInvGlue (x 0 ^ 2)) := funext hancock_eq
  have hw : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin 2) => expNegInvGlue (x 0 ^ 2) :=
    (expNegInvGlue.contDiff (n := ⊤)).comp ((contDiff_coord 0).pow 2)
  refine ⟨?_, fun d => ?_, fun t ht => by simp [hancock, ht]; ring, ?_, fun k => ?_,
    fun x _ => by simpa using sq_nonneg (x 1)⟩
  · rw [hfun]
    exact (contDiff_coord 1).mul ((contDiff_coord 1).sub hw)
  · -- along the line `t ↦ t d`: `f(t d) ≥ t² d₂² - |t| |d₂| t² d₁² ≥ 0` for small `t`
    unfold IsLocalMin IsMinFilter
    simp only [zero_smul, hancock_eq]
    simp only [PiLp.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      expNegInvGlue.zero, sub_zero, mul_zero, PiLp.smul_apply, smul_eq_mul]
    rcases eq_or_ne (d 1) 0 with hd | hd
    · exact Eventually.of_forall fun t => by simp [hd]
    · have hr : 0 < |d 1| / (d 0 ^ 2 + 1) := by positivity
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, lt_div_iff₀ (by positivity)] at ht
      have hg0 := expNegInvGlue.nonneg ((t * d 0) ^ 2)
      have hg := expNegInvGlue_le_self (sq_nonneg (t * d 0))
      set g := expNegInvGlue ((t * d 0) ^ 2)
      have h1 : t * d 1 * g ≤ |t * d 1| * g := mul_le_mul_of_nonneg_right (le_abs_self _) hg0
      have h2 : |t * d 1| * g ≤ |t * d 1| * (t * d 0) ^ 2 :=
        mul_le_mul_of_nonneg_left hg (abs_nonneg _)
      have h3 : |t * d 1| * (t * d 0) ^ 2 = t ^ 2 * |d 1| * (|t| * d 0 ^ 2) := by
        rw [abs_mul, mul_pow]; ring
      have h4 : |t| * d 0 ^ 2 ≤ |d 1| := by nlinarith [abs_nonneg t]
      have h5 : t ^ 2 * |d 1| * (|t| * d 0 ^ 2) ≤ t ^ 2 * |d 1| * |d 1| :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have h6 : t ^ 2 * |d 1| * |d 1| = (t * d 1) ^ 2 := by
        rw [mul_assoc, ← sq, sq_abs]; ring
      nlinarith
  · refine Optimization.not_isLocalMin_of_curve (l := 𝓝[>] (0 : ℝ))
      (γ := fun t : ℝ => !₂[t, expNegInvGlue (t ^ 2) / 2]) ?_
      (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
    · have hc : Continuous fun t : ℝ =>
          (!₂[t, expNegInvGlue (t ^ 2) / 2] : EuclideanSpace ℝ (Fin 2)) :=
        (PiLp.continuous_toLp 2 _).comp (by
          refine continuous_pi fun i => ?_
          fin_cases i
          · exact continuous_id
          · exact ((expNegInvGlue.contDiff (n := 0)).continuous.comp
              (continuous_pow 2)).div_const 2)
      have h0 : (!₂[(0 : ℝ), expNegInvGlue ((0 : ℝ) ^ 2) / 2] : EuclideanSpace ℝ (Fin 2)) = 0 := by
        ext i; fin_cases i <;> simp
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simp only [h0] at this
      exact this
    · have hg := expNegInvGlue.pos_of_pos (pow_pos ht 2)
      rw [hancock_eq, hancock_eq]
      simp
      nlinarith
  · -- `f = g - x₂ · expNegInvGlue(x₁²)` and the second term is flat at `0`
    have hsplit : hancock = (fun x : EuclideanSpace ℝ (Fin 2) => x 1 ^ 2) -
        fun x => x 1 * expNegInvGlue (x 0 ^ 2) := by
      rw [hfun]; funext x; simp only [Pi.sub_apply]; ring
    have hflat : ‖iteratedFDeriv ℝ k
        (fun x : EuclideanSpace ℝ (Fin 2) => x 1 * expNegInvGlue (x 0 ^ 2)) 0‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      refine (norm_iteratedFDeriv_mul_le (N := ∞) (contDiff_coord 1) hw 0
        (by exact_mod_cast le_top)).trans (le_of_eq ?_)
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [iteratedFDeriv_expNegInvGlue_comp_eq_zero ((contDiff_coord 0).pow 2) (by simp),
        norm_zero, mul_zero]
    rw [hsplit, iteratedFDeriv_sub_apply ((contDiff_coord 1).pow 2).contDiffAt
      (((contDiff_coord 1).mul hw).contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_eq_zero.1 hflat, sub_zero]

/-! #### Lewis' example -/


/-- Lewis' variant of Hancock's example ([cartis2022evaluation], (12.1.3)):
`f(x) = x₂ (x₂ - sin(1/x₁) exp(-1/x₁²))` for `x₁ ≠ 0` and `f(x) = x₂²` for `x₁ = 0`. -/
noncomputable def lewis (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if x 0 ≠ 0 then x 1 * (x 1 - Real.sin (1 / x 0) * Real.exp (-1 / x 0 ^ 2)) else x 1 ^ 2

theorem lewis_eq (x : EuclideanSpace ℝ (Fin 2)) :
    lewis x = x 1 * (x 1 - oscFlat 1 0 (x 0)) := by
  unfold lewis
  split_ifs with h
  · have hpos : 0 < x 0 ^ 2 := by positivity
    simp [oscFlat, expNegInvGlue, not_le.2 hpos, one_div, neg_div]
  · push Not at h
    simp [oscFlat, h, sq]

/-- **Example 12.1.1, variant (12.1.3)** ([cartis2022evaluation], due to A. Lewis). For
`f = lewis`: `f` is `C^∞`, the origin is not a local minimizer of `f`, and yet there is no
continuous descent curve from the origin: no `γ` continuous on `[0, 1]` with `γ(0) = 0` and
`f(γ(α)) < f(0)` for all `α ∈ (0, 1]`. -/
theorem example_12_1_1_variant :
    ContDiff ℝ ∞ lewis ∧ ¬ IsLocalMin lewis 0 ∧
      ¬ ∃ γ : ℝ → EuclideanSpace ℝ (Fin 2), ContinuousOn γ (Icc 0 1) ∧ γ 0 = 0 ∧
        ∀ α ∈ Ioc (0 : ℝ) 1, lewis (γ α) < lewis 0 := by
  have hh : ContDiff ℝ ∞ (oscFlat 1 0) := contDiff_oscFlat 1 0 (n := ⊤)
  have hfun : lewis = fun x => x 1 * (x 1 - oscFlat 1 0 (x 0)) := funext lewis_eq
  have hl0 : lewis 0 = 0 := by simp [lewis_eq, oscFlat]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact (contDiff_coord 1).mul ((contDiff_coord 1).sub (hh.comp (contDiff_coord 0)))
  · -- along `t_k = 1/(π/2 + 2kπ)`, `x = (t_k, h(t_k)/2)` gives `f = -h(t_k)²/4 < 0`
    set t : ℕ → ℝ := fun k => (Real.pi / 2 + k * (2 * Real.pi))⁻¹
    have ht0 : ∀ k, 0 < t k := fun k => by have := Real.pi_pos; positivity
    have htlim : Tendsto t atTop (𝓝 0) := by
      refine tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ ?_)
      exact tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    have hval : ∀ k, oscFlat 1 0 (t k) = expNegInvGlue (t k ^ 2) := fun k => by
      simp [oscFlat, t, Real.sin_add_nat_mul_two_pi]
    refine Optimization.not_isLocalMin_of_curve (l := atTop)
      (γ := fun k => !₂[t k, oscFlat 1 0 (t k) / 2]) ?_ (Eventually.of_forall fun k => ?_)
    · have hc : Continuous fun s : ℝ =>
          (!₂[s, oscFlat 1 0 s / 2] : EuclideanSpace ℝ (Fin 2)) :=
        (PiLp.continuous_toLp 2 _).comp (by
          refine continuous_pi fun i => ?_
          fin_cases i
          · exact continuous_id
          · exact (hh.continuous).div_const 2)
      have h0 : (!₂[(0 : ℝ), oscFlat 1 0 0 / 2] : EuclideanSpace ℝ (Fin 2)) = 0 := by
        ext i; fin_cases i <;> simp [oscFlat]
      have := (hc.tendsto 0).comp htlim
      simp only [h0] at this
      exact this
    · have hg := expNegInvGlue.pos_of_pos (pow_pos (ht0 k) 2)
      rw [lewis_eq, hl0]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hval]
      nlinarith
  · -- no continuous descent curve
    rintro ⟨γ, hγc, hγ0, hneg⟩
    set u : ℝ → ℝ := fun α => γ α 0
    have hu : ContinuousOn u (Icc 0 1) :=
      (contDiff_coord (k := 0) (0 : Fin 2)).continuous.comp_continuousOn hγc
    -- descent forces `u α ≠ 0` and `sin(1/u α) ≠ 0`
    have hsin : ∀ α ∈ Ioc (0 : ℝ) 1, Real.sin (u α)⁻¹ ≠ 0 := fun α hα hs => by
      have := hneg α hα
      rw [lewis_eq, hl0] at this
      simp only [oscFlat, hs, u, Polynomial.eval_one, Polynomial.eval_zero, mul_zero, zero_mul,
        add_zero, sub_zero] at this
      nlinarith [sq_nonneg (γ α 1)]
    have hu1 : u 1 ≠ 0 := fun h => hsin 1 ⟨one_pos, le_rfl⟩ (by rw [h]; simp)
    -- a zero `z = 1/(kπ)` of `sin(1/·)` with `0 < z < |u 1|`
    obtain ⟨k, hk⟩ := exists_nat_gt (|u 1| * Real.pi)⁻¹
    have hupos : 0 < |u 1| := abs_pos.2 hu1
    have hkpos : (0 : ℝ) < k := lt_trans (by positivity) hk
    set z : ℝ := (k * Real.pi)⁻¹
    have hz0 : 0 < z := by have := Real.pi_pos; positivity
    have hzu : z < |u 1| := by
      rw [inv_lt_comm₀ (by have := Real.pi_pos; positivity) hupos]
      rw [inv_lt_iff_one_lt_mul₀ (by positivity)] at hk
      rw [inv_lt_iff_one_lt_mul₀ hupos]
      nlinarith [Real.pi_pos]
    -- near `0`, `|u| < z`
    obtain ⟨ε, hε, hball⟩ := Metric.continuousWithinAt_iff.1 (hγc 0 ⟨le_rfl, zero_le_one⟩)
      z hz0
    set α₀ : ℝ := min (ε / 2) 1
    have hα₀ : α₀ ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, min_le_right _ _⟩
    have hsmall : |u α₀| < z := by
      have := hball ⟨hα₀.1.le, hα₀.2⟩ (by
        rw [Real.dist_eq, sub_zero, abs_of_pos hα₀.1]
        exact (min_le_left _ _).trans_lt (by linarith))
      rw [hγ0, dist_zero_right] at this
      have hle : |u α₀| ≤ ‖γ α₀‖ := by
        simpa [u, Real.norm_eq_abs] using PiLp.norm_apply_le (γ α₀) 0
      exact hle.trans_lt this
    -- the intermediate value theorem for `|u|` on `[α₀, 1]`
    have hsub : Icc α₀ 1 ⊆ Icc 0 1 := Icc_subset_Icc_left hα₀.1.le
    obtain ⟨α, hα, hαz⟩ := intermediate_value_Icc hα₀.2 (hu.mono hsub).abs
      ⟨hsmall.le, hzu.le⟩
    have hαI : α ∈ Ioc (0 : ℝ) 1 := ⟨hα₀.1.trans_le hα.1, hα.2⟩
    refine hsin α hαI ?_
    rcases abs_eq hz0.le |>.1 hαz with h | h
    · rw [h, inv_inv]
      exact Real.sin_nat_mul_pi k
    · rw [h, inv_neg, inv_inv, Real.sin_neg, Real.sin_nat_mul_pi k, neg_zero]


/-! #### Peano's quartic -/

/-- Peano's quartic ([cartis2022evaluation], (12.1.8)):
`f(x) = x₂² - κ₁ x₁² x₂ + κ₂ x₁⁴` on `ℝ²` (the book's `x₁, x₂` are `x 0, x 1`). -/
def peanoQuartic (κ₁ κ₂ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 1 ^ 2 - κ₁ * x 0 ^ 2 * x 1 + κ₂ * x 0 ^ 4

theorem contDiff_peanoQuartic (κ₁ κ₂ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (peanoQuartic κ₁ κ₂) :=
  (((contDiff_coord 1).pow 2).sub ((contDiff_const.mul ((contDiff_coord 0).pow 2)).mul
    (contDiff_coord 1))).add (contDiff_const.mul ((contDiff_coord 0).pow 4))

@[simp]
theorem peanoQuartic_zero (κ₁ κ₂ : ℝ) : peanoQuartic κ₁ κ₂ 0 = 0 := by
  simp [peanoQuartic]

/-- The curve directions `s₁ = e₁`, `s₂ = (κ₁/2) e₂` (and `s_ℓ = 0` for `ℓ ≥ 3`) of
Example 12.1.2. -/
noncomputable def peanoDirections (κ₁ : ℝ) (ℓ : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  if ℓ = 1 then !₂[1, 0] else if ℓ = 2 then !₂[0, κ₁ / 2] else 0

/-- Coordinates of a polynomial curve. -/
theorem polyCurve_apply {m q : ℕ} (s : ℕ → EuclideanSpace ℝ (Fin m)) (α : ℝ) (i : Fin m) :
    (∑ ℓ ∈ Finset.Icc 1 q, α ^ ℓ • s ℓ) i = ∑ ℓ ∈ Finset.Icc 1 q, α ^ ℓ * s ℓ i := by
  simp [WithLp.ofLp_sum]

/-- The coefficients of Peano's quartic along a polynomial curve of order `2`:
`c₁ = 0`, `c₂ = (s₁)₂²`. -/
theorem curveCoeff_peanoQuartic_two (κ₁ κ₂ : ℝ) (s : ℕ → EuclideanSpace ℝ (Fin 2)) :
    Optimization.curveCoeff (ftaylorSeries ℝ (peanoQuartic κ₁ κ₂) 0) s 1 = 0 ∧
      Optimization.curveCoeff (ftaylorSeries ℝ (peanoQuartic κ₁ κ₂) 0) s 2 = s 1 1 ^ 2 := by
  have h := Optimization.curveCoeff_eq_of_isLittleO (x := 0) (q := 2) (s := s)
    (a := fun i => if i = 2 then s 1 1 ^ 2 else 0) (contDiff_peanoQuartic κ₁ κ₂).contDiffAt
    (Optimization.isLittleO_of_eq_pow_succ_mul (P := fun α => 2 * s 1 1 * s 2 1 + α * s 2 1 ^ 2 -
      κ₁ * (s 1 0 + α * s 2 0) ^ 2 * (s 1 1 + α * s 2 1) + κ₂ * α * (s 1 0 + α * s 2 0) ^ 4)
      (by fun_prop) fun α => by
        rw [show Finset.Icc 1 2 = {1, 2} by decide]
        simp [peanoQuartic]
        ring)
  exact ⟨by simpa using h 1 (by simp), by simpa using h 2 (by simp)⟩

/-- Along a polynomial curve of order `3` with `(s₁)₂ = 0`, the coefficients `c₁, c₂, c₃` of
Peano's quartic vanish. -/
theorem curveCoeff_peanoQuartic_three (κ₁ κ₂ : ℝ) (s : ℕ → EuclideanSpace ℝ (Fin 2))
    (hs : s 1 1 = 0) :
    ∀ i ∈ Finset.Icc 1 3,
      Optimization.curveCoeff (ftaylorSeries ℝ (peanoQuartic κ₁ κ₂) 0) s i = 0 := by
  have h := Optimization.curveCoeff_eq_of_isLittleO (x := 0) (q := 3) (s := s) (a := fun _ => 0)
    (contDiff_peanoQuartic κ₁ κ₂).contDiffAt
    (Optimization.isLittleO_of_eq_pow_succ_mul (P := fun α =>
      (s 2 1 + α * s 3 1) ^ 2 - κ₁ * (s 1 0 + α * s 2 0 + α ^ 2 * s 3 0) ^ 2 * (s 2 1 + α * s 3 1) +
        κ₂ * (s 1 0 + α * s 2 0 + α ^ 2 * s 3 0) ^ 4)
      (by fun_prop) fun α => by
        rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]
        simp [peanoQuartic, hs]
        ring)
  exact h

/-- The coefficients of Peano's quartic along the curve of `peanoDirections`:
`(c₁, c₂, c₃, c₄) = (0, 0, 0, κ₂ - κ₁²/4)`. -/
theorem curveCoeff_peanoDirections (κ₁ κ₂ : ℝ) :
    ∀ i ∈ Finset.Icc 1 4, Optimization.curveCoeff (ftaylorSeries ℝ (peanoQuartic κ₁ κ₂) 0)
      (peanoDirections κ₁) i = [0, 0, 0, 0, κ₂ - κ₁ ^ 2 / 4].getD i 0 :=
  Optimization.curveCoeff_eq_of_isLittleO (contDiff_peanoQuartic κ₁ κ₂).contDiffAt
    ((Asymptotics.isLittleO_zero (fun α : ℝ => α ^ 4) (𝓝[>] 0)).congr_left fun α => by
      rw [show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]
      simp [peanoQuartic, peanoDirections]
      ring)

/-- **Example 12.1.2** ([cartis2022evaluation], (12.1.8)–(12.1.9)). For Peano's quartic
`f = peanoQuartic κ₁ κ₂`:
* its derivatives at `0` are `∇f(0) = 0`, `∇²f(0)[d]² = 2 d₂²`, `∇³f(0)[d]³ = -6κ₁ d₁² d₂` and
  `∇⁴f(0)[d]⁴ = 24 κ₂ d₁⁴` (i.e. `∇²f(0) = diag(0, 2)`, the only nonzero third and fourth
  derivative entries are `-2κ₁` at the permutations of `(1, 1, 2)` and `24κ₂` at `(1, 1, 1, 1)`);
* along the curve `s₁ = e₁`, `s₂ = (κ₁/2) e₂`, the coefficients (12.1.6) are
  `c₁ = c₂ = c₃ = 0` and `c₄ = κ₂ - κ₁²/4` ((12.1.9)), and indeed
  `f(t e₁ + (κ₁/2) t² e₂) = (κ₂ - κ₁²/4) t⁴`;
* if `κ₂ ≥ 0`, the origin is a local minimizer of `f` along every line;
* if `κ₁² > 4κ₂`, the origin is not a local minimizer of `f`.
Hence for `κ₁² > 4κ₂ ≥ 0` (e.g. `κ₁ = 3`, `κ₂ = 2`; the printed `κ₁ = 1`, `κ₂ = 2` does not give
a saddle) the origin is minimal along every line but is a saddle point. -/
theorem example_12_1_2 (κ₁ κ₂ : ℝ) :
    (∀ d : EuclideanSpace ℝ (Fin 2),
      iteratedFDeriv ℝ 1 (peanoQuartic κ₁ κ₂) 0 (fun _ => d) = 0 ∧
      iteratedFDeriv ℝ 2 (peanoQuartic κ₁ κ₂) 0 (fun _ => d) = 2 * d 1 ^ 2 ∧
      iteratedFDeriv ℝ 3 (peanoQuartic κ₁ κ₂) 0 (fun _ => d) = -6 * κ₁ * d 0 ^ 2 * d 1 ∧
      iteratedFDeriv ℝ 4 (peanoQuartic κ₁ κ₂) 0 (fun _ => d) = 24 * κ₂ * d 0 ^ 4) ∧
    (∀ i ∈ Finset.Icc 1 3,
      Optimization.curveCoeff (ftaylorSeries ℝ (peanoQuartic κ₁ κ₂) 0) (peanoDirections κ₁) i = 0) ∧
    Optimization.curveCoeff (ftaylorSeries ℝ (peanoQuartic κ₁ κ₂) 0) (peanoDirections κ₁) 4 =
      κ₂ - κ₁ ^ 2 / 4 ∧
    (∀ t : ℝ, peanoQuartic κ₁ κ₂ (!₂[t, κ₁ / 2 * t ^ 2]) = (κ₂ - κ₁ ^ 2 / 4) * t ^ 4) ∧
    (0 ≤ κ₂ → ∀ d : EuclideanSpace ℝ (Fin 2),
      IsLocalMin (fun t : ℝ => peanoQuartic κ₁ κ₂ (t • d)) 0) ∧
    (4 * κ₂ < κ₁ ^ 2 → ¬ IsLocalMin (peanoQuartic κ₁ κ₂) 0) := by
  have hcurve : ∀ t : ℝ, peanoQuartic κ₁ κ₂ (!₂[t, κ₁ / 2 * t ^ 2]) = (κ₂ - κ₁ ^ 2 / 4) * t ^ 4 :=
    fun t => by simp [peanoQuartic]; ring
  refine ⟨fun d => ?_, ?_, ?_, hcurve, fun hκ d => ?_, fun hκ => ?_⟩
  · have h := Optimization.iteratedFDeriv_apply_diag_eq_of_poly (x := 0) (d := d) (N := 4)
      (a := fun i => [0, 0, d 1 ^ 2, -κ₁ * d 0 ^ 2 * d 1, κ₂ * d 0 ^ 4].getD i 0)
      (contDiff_peanoQuartic κ₁ κ₂).contDiffAt (Eventually.of_forall fun t => by
        simp [peanoQuartic, Finset.sum_Icc_succ_top]
        ring)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h 1 (by simp)
    · rw [h 2 (by simp)]; simp [Nat.factorial]
    · rw [h 3 (by simp)]; simp [Nat.factorial]; ring
    · rw [h 4 (by simp)]; simp [Nat.factorial]; ring
  · intro i hi
    have := curveCoeff_peanoDirections κ₁ κ₂ i (Finset.Icc_subset_Icc_right (by norm_num) hi)
    rw [this]
    obtain ⟨h1, h3⟩ := Finset.mem_Icc.1 hi
    interval_cases i <;> rfl
  · simpa using curveCoeff_peanoDirections κ₁ κ₂ 4 (by simp)
  · unfold IsLocalMin IsMinFilter
    have hf : ∀ t : ℝ, peanoQuartic κ₁ κ₂ (t • d) =
        t ^ 2 * (d 1 ^ 2 - κ₁ * t * d 0 ^ 2 * d 1 + κ₂ * t ^ 2 * d 0 ^ 4) := fun t => by
      simp [peanoQuartic]; ring
    simp only [zero_smul, peanoQuartic_zero, hf]
    rcases eq_or_ne (d 1) 0 with hd | hd
    · exact Eventually.of_forall fun t => by rw [hd]; ring_nf; positivity
    · have hc : ContinuousAt
          (fun t : ℝ => d 1 ^ 2 - κ₁ * t * d 0 ^ 2 * d 1 + κ₂ * t ^ 2 * d 0 ^ 4) 0 := by fun_prop
      have hpos : 0 < d 1 ^ 2 - κ₁ * 0 * d 0 ^ 2 * d 1 + κ₂ * 0 ^ 2 * d 0 ^ 4 := by
        norm_num; positivity
      filter_upwards [hc.eventually (lt_mem_nhds hpos)] with t ht
      exact mul_nonneg (sq_nonneg t) ht.le
  · refine Optimization.not_isLocalMin_of_curve (l := 𝓝[>] (0 : ℝ))
      (γ := fun t : ℝ => !₂[t, κ₁ / 2 * t ^ 2]) ?_
      (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
    · have hc : Continuous fun t : ℝ => (!₂[t, κ₁ / 2 * t ^ 2] : EuclideanSpace ℝ (Fin 2)) :=
        (PiLp.continuous_toLp 2 _).comp (by fun_prop)
      have h0 : (!₂[(0 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) = 0 := by
        ext i; fin_cases i <;> simp
      simpa [h0] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    · rw [hcurve, peanoQuartic_zero]
      have : 0 < t ^ 4 := by positivity
      nlinarith

/-- **Theorem 12.1.2** ([cartis2022evaluation]): linesearch methods are unsuitable for finding
high-order minimizers. Its formal content, for Peano's quartic `f = peanoQuartic 3 2`: (i) no
straight line through the origin is a descent line (a linesearch started at `0` finds no
decrease along any direction and stops there); (ii) the origin is a third-order minimizer;
(iii) it is not a fourth-order minimizer; (iv) it is not a local minimizer. -/
theorem theorem_12_1_2 :
    (∀ d : EuclideanSpace ℝ (Fin 2), ∃ τ : ℝ, 0 < τ ∧ ∀ t ∈ Icc (0 : ℝ) τ,
      peanoQuartic 3 2 0 ≤ peanoQuartic 3 2 (t • d)) ∧
    IsQthOrderMinimizer (peanoQuartic 3 2) 0 3 ∧
    ¬ IsQthOrderMinimizer (peanoQuartic 3 2) 0 4 ∧ ¬ IsLocalMin (peanoQuartic 3 2) 0 := by
  obtain ⟨-, hc13, hc4, -, hline, hsaddle⟩ := example_12_1_2 3 2
  refine ⟨fun d => ?_, ?_, fun h => ?_, hsaddle (by norm_num)⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hline (by norm_num) d)
    refine ⟨ε / 2, by positivity, fun t ht => ?_⟩
    have := hball (show dist t 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; linarith [ht.2])
    simpa using this
  · intro j hj s hzero
    obtain ⟨h1, h2⟩ := curveCoeff_peanoQuartic_two 3 2 s
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 by simp at hj; omega) with rfl | rfl | rfl
    · rw [h1]
    · rw [h2]; positivity
    · have hs : s 1 1 = 0 := by
        have := hzero 2 (by simp)
        rw [h2] at this
        exact pow_eq_zero_iff two_ne_zero |>.1 this
      rw [curveCoeff_peanoQuartic_three 3 2 s hs 3 (by simp)]
  · have := h 4 (by simp) (peanoDirections 3) fun i hi =>
      hc13 i (by simp at hi ⊢; omega)
    rw [hc4] at this
    norm_num at this

end Plane

/-! ### Relations with the classical measures (§12.1.3) -/

section Classical

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

private theorem norm_ftaylorSeries_one (f : 𝔼 → ℝ) (x : 𝔼) :
    ‖ftaylorSeries ℝ f x 1‖ = ‖gradient f x‖ := by
  rw [EuclideanSpace.norm_gradient_eq]
  exact norm_iteratedFDeriv_one f

private theorem ftaylorSeries_one_eq_zero_iff (f : 𝔼 → ℝ) (x : 𝔼) :
    ftaylorSeries ℝ f x 1 = 0 ↔ gradient f x = 0 := by
  rw [← norm_eq_zero, norm_ftaylorSeries_one, norm_eq_zero]

/-- **Theorem 12.1.3 (i)** ([cartis2022evaluation], (12.1.12)): for `δ > 0`,
`‖∇f(x)‖ = φ^δ_{f,1}(x) / δ`; hence `φ^δ_{f,1}(x) = 0` iff `∇f(x) = 0`. -/
theorem theorem_12_1_3_i {δ : ℝ} (hδ : 0 < δ) :
    ‖gradient f x‖ = phiMeasure f 1 δ x / δ ∧ (phiMeasure f 1 δ x = 0 ↔ gradient f x = 0) := by
  refine ⟨?_, ?_⟩
  · rw [phiMeasure, Optimization.taylorMeasure_one_eq _ hδ.le, norm_ftaylorSeries_one,
      mul_div_cancel_left₀ _ hδ.ne']
  · rw [phiMeasure, Optimization.taylorMeasure_one_eq_zero_iff _ hδ, ftaylorSeries_one_eq_zero_iff]

/-- **Theorem 12.1.3 (ii)** ([cartis2022evaluation], (12.1.14)): if `φ^δ_{f,2}(x) = 0` for some
`δ > 0`, then `∇f(x) = 0` and `λ_min[∇²f(x)] ≥ 0`: `x` is a first- and second-order minimizer.
(The converse also holds.) -/
theorem theorem_12_1_3_ii {δ : ℝ} (hδ : 0 < δ) :
    phiMeasure f 2 δ x = 0 ↔ gradient f x = 0 ∧ 0 ≤ Chapter01.hessianMinEig f x := by
  rw [phiMeasure, Optimization.taylorMeasure_two_eq_zero_iff _ hδ, ftaylorSeries_one_eq_zero_iff]
  rfl

/-- The subspace `M(x) = ker¹[∇f(x)] ∩ ker²[∇²f(x)]` of Theorem 12.1.3 (iii): the directions `d`
with `∇f(x)[d] = 0` and `∇²f(x)[d]² = 0`. -/
def nullDirections (f : 𝔼 → ℝ) (x : 𝔼) : Set 𝔼 :=
  {d | iteratedFDeriv ℝ 1 f x (fun _ => d) = 0 ∧ iteratedFDeriv ℝ 2 f x (fun _ => d) = 0}

/-- The projected norm `‖P_{M(x)}[∇³f(x)]‖ = sup_{d ∈ M(x), ‖d‖ ≤ 1} |∇³f(x)[d]³|` of
Theorem 12.1.3 (iii) (the tensor norm (A.7) of the restriction to `M(x)`). -/
noncomputable def projectedThirdNorm (f : 𝔼 → ℝ) (x : 𝔼) : ℝ :=
  sSup ((fun d => |iteratedFDeriv ℝ 3 f x (fun _ => d)|) '' {d | d ∈ nullDirections f x ∧ ‖d‖ ≤ 1})

/-- **Theorem 12.1.3 (iii)** ([cartis2022evaluation], (12.1.13), (12.1.15)): for every `δ > 0`,
`(δ³/3!) ‖P_{M(x)}[∇³f(x)]‖ ≤ φ^δ_{f,3}(x)`; consequently, if `φ^δ_{f,3}(x)/δ³ → 0` as `δ → 0⁺`,
then `∇³f(x)[d]³ = 0` for all `d ∈ M(x)` (the third-order condition of Theorem 1.1.1). -/
theorem theorem_12_1_3_iii :
    (∀ δ, 0 < δ → δ ^ 3 / 3! * projectedThirdNorm f x ≤ phiMeasure f 3 δ x) ∧
      (Tendsto (fun δ => phiMeasure f 3 δ x / δ ^ 3) (𝓝[>] 0) (𝓝 0) →
        ∀ d ∈ nullDirections f x, iteratedFDeriv ℝ 3 f x (fun _ => d) = 0) := by
  have hbound : ∀ δ, 0 ≤ δ → ∀ d ∈ nullDirections f x, ‖d‖ ≤ 1 →
      δ ^ 3 / 6 * |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ phiMeasure f 3 δ x :=
    fun δ hδ d hd hd1 =>
      Optimization.abs_apply_three_le_taylorMeasure (ftaylorSeries ℝ f x) hδ hd1 hd.1 hd.2
  refine ⟨fun δ hδ => ?_, fun hlim d hd => ?_⟩
  · have hδ3 : 0 < δ ^ 3 / 3! := by positivity
    rw [← le_div_iff₀' hδ3]
    refine csSup_le ⟨_, ⟨0, ⟨⟨(iteratedFDeriv ℝ 1 f x).map_zero, (iteratedFDeriv ℝ 2 f x).map_zero⟩,
      by simp⟩, rfl⟩⟩ ?_
    rintro _ ⟨d, ⟨hd, hd1⟩, rfl⟩
    rw [le_div_iff₀' hδ3]
    simpa [Nat.factorial] using hbound δ hδ.le d hd hd1
  · -- reduce to a direction of norm at most one
    set c : ℝ := (‖d‖ + 1)⁻¹
    have hc : 0 < c := by positivity
    have hcd : ‖c • d‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg hc.le, inv_mul_le_iff₀ (by positivity)]
      linarith
    have hscale : ∀ k (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔼) ℝ),
        (T fun _ => c • d) = c ^ k * T fun _ => d := fun k T => by
      have := T.map_smul_univ (fun _ => c) (fun _ => d)
      simpa [Finset.prod_const] using this
    have hcM : c • d ∈ nullDirections f x := by
      refine ⟨?_, ?_⟩
      · rw [hscale, hd.1, mul_zero]
      · rw [hscale, hd.2, mul_zero]
    -- `|∇³f(x)[c d]³| ≤ 6 φ(δ)/δ³ → 0`
    have hle : ∀ δ ∈ Ioi (0 : ℝ), |iteratedFDeriv ℝ 3 f x (fun _ => c • d)| ≤
        6 * (phiMeasure f 3 δ x / δ ^ 3) := fun δ hδ => by
      have := hbound δ (le_of_lt hδ) _ hcM hcd
      have hδ3 : 0 < δ ^ 3 := pow_pos hδ 3
      rw [mul_div_assoc', le_div_iff₀ hδ3]
      linarith
    have hlim6 := hlim.const_mul 6
    rw [mul_zero] at hlim6
    have h0 : |iteratedFDeriv ℝ 3 f x (fun _ => c • d)| ≤ 0 :=
      ge_of_tendsto hlim6 (eventually_nhdsWithin_of_forall hle)
    have h0' : iteratedFDeriv ℝ 3 f x (fun _ => c • d) = 0 := abs_nonpos_iff.1 h0
    rw [hscale] at h0'
    exact (mul_eq_zero.1 h0').resolve_left (pow_ne_zero _ hc.ne')

/-- **Theorem 12.1.4** ([cartis2022evaluation]): if `f` is `C^j` near a local minimizer `x`, then
`φ^δ_{f,j}(x) = 0` for every `δ > 0` when `j ∈ {1, 2}` (12.1.16), and
`φ^δ_{f,j}(x) / δ^j → 0` as `δ → 0⁺` for every `j` (12.1.17). -/
theorem theorem_12_1_4 {j : ℕ} (hf : ContDiffAt ℝ j f x) (hmin : IsLocalMin f x) :
    (j ∈ Finset.Icc 1 2 → ∀ δ, 0 < δ → phiMeasure f j δ x = 0) ∧
      Tendsto (fun δ => phiMeasure f j δ x / δ ^ j) (𝓝[>] 0) (𝓝 0) :=
  ⟨fun hj _ hδ => Optimization.taylorMeasure_eq_zero_of_isLocalMin hf hmin hj hδ.le,
    Optimization.tendsto_taylorMeasure_div_pow_of_isLocalMin hf hmin⟩

end Classical

/-! ### Example 12.1.3 -/

section Example3

variable {n : ℕ}

/-- The model `m(x) = -β ⟪e, x⟫ + σ ‖x‖^{p+1}/(p+1)!` of Example 12.1.3 ([cartis2022evaluation],
(12.1.18)). -/
noncomputable def example1213Model (β σ : ℝ) (p : ℕ) (e : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -β * ⟪e, x⟫ + σ * ‖x‖ ^ (p + 1) / (p + 1)!

/-- The radial profile `g(r) = -β r + σ r^{p+1}/(p+1)!` of the model is strictly convex on
`[0, ∞)` and minimized at `r* = (β p!/σ)^{1/p}`. -/
theorem example1213_radial {p : ℕ} (hp : 1 ≤ p) {β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) :
    StrictConvexOn ℝ (Ici 0) (fun r : ℝ => -β * r + σ * r ^ (p + 1) / (p + 1)!) ∧
      IsMinOn (fun r : ℝ => -β * r + σ * r ^ (p + 1) / (p + 1)!) (Ici 0)
        ((β * p ! / σ) ^ (1 / (p : ℝ))) := by
  refine ⟨⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩, ?_⟩
  · have key := (strictConvexOn_pow (n := p + 1) (by omega)).2 hx hy hxy ha hb hab
    have hc : 0 < σ / (p + 1)! := by positivity
    have := mul_lt_mul_of_pos_left key hc
    simp only [smul_eq_mul] at this ⊢
    have hb' : b = 1 - a := by linarith
    subst hb'
    have e1 : a * (-β * x + σ * x ^ (p + 1) / (p + 1)!) + (1 - a) * (-β * y +
        σ * y ^ (p + 1) / (p + 1)!) = -β * (a * x + (1 - a) * y) +
          σ / (p + 1)! * (a * x ^ (p + 1) + (1 - a) * y ^ (p + 1)) := by ring
    have e2 : -β * (a * x + (1 - a) * y) + σ * (a * x + (1 - a) * y) ^ (p + 1) / (p + 1)! =
        -β * (a * x + (1 - a) * y) + σ / (p + 1)! * (a * x + (1 - a) * y) ^ (p + 1) := by ring
    rw [e1, e2]
    linarith
  · obtain ⟨hmin, -, -⟩ := Optimization.isMinOn_neg_monomial_add_regularization le_rfl hp hσ hβ
    have hts : (β / (σ * (1 - 1).factorial / p.factorial)) ^ (1 / ((p - 1 + 1 : ℕ) : ℝ)) =
        (β * p ! / σ) ^ (1 / (p : ℝ)) := by
      rw [Nat.sub_add_cancel hp]
      congr 1
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      field_simp
    rw [hts] at hmin
    intro r hr
    have hr' : 0 ≤ r := hr
    have := hmin (mem_univ r)
    have ht : 0 ≤ (β * p ! / σ) ^ (1 / (p : ℝ)) := by positivity
    simp only [Set.mem_ofPred_eq, Optimization.negMonomialRegModel, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one, abs_of_nonneg hr', abs_of_nonneg ht] at this
    exact this

/-- The third-order Taylor decrement of the model of Example 12.1.3 along its minimizer
((12.1.21)): with `t* = (β p!/σ)^{1/p}` and `p ≥ 2`,
`ΔT_{m,3}(x*, α x*) = -σα² t*^{p+1}/(2!(p-1)!) - σα³ t*^{p+1}/(3!(p-2)!)`. Along the ray,
`m((1 + u) x*) = m(x*) + ∑_{i ≥ 2} σ t*^{p+1} u^i/(i!(p+1-i)!)`. -/
theorem example1213_taylorDecrement {p : ℕ} (hp : 2 ≤ p) {β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (α : ℝ) :
    (ftaylorSeries ℝ (example1213Model β σ p e)
        ((β * p ! / σ) ^ (1 / (p : ℝ)) • e)).taylorDecrement 3
        (α • (β * p ! / σ) ^ (1 / (p : ℝ)) • e) =
      -σ * α ^ 2 * ((β * p ! / σ) ^ (1 / (p : ℝ))) ^ (p + 1) / (2 ! * (p + 1 - 2)!) -
        σ * α ^ 3 * ((β * p ! / σ) ^ (1 / (p : ℝ))) ^ (p + 1) / (3 ! * (p + 1 - 3)!) := by
  set ts := (β * p ! / σ) ^ (1 / (p : ℝ)) with hts
  set m := example1213Model β σ p e
  set K := σ * ts ^ (p + 1) / (p + 1)!
  have ht0 : 0 < ts := by positivity
  have htp : ts ^ p = β * p ! / σ := by
    rw [hts, one_div, Real.rpow_inv_natCast_pow (by positivity) (by omega)]
  have hK : K * (p + 1) = β * ts := by
    simp only [K]
    rw [pow_succ, htp, Nat.factorial_succ]
    push_cast
    field_simp
  have hxs : ts • e ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_smul, he, Real.norm_of_nonneg ht0.le, mul_one]
    exact ht0.ne'
  have hm : ContDiffAt ℝ (p + 1 : ℕ) m (ts • e) :=
    ((contDiff_const.mul ((contDiff_const (c := e)).inner ℝ contDiff_id)).contDiffAt).add
      ((((contDiffAt_norm ℝ hxs).pow (p + 1)).const_smul σ).div_const _)
  set c : ℕ → ℝ := fun i => K * (p + 1).choose i - if i = 1 then β * ts else 0
  -- the expansion along the ray `t ↦ x* + t α x*`
  have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), m (ts • e + t • α • ts • e) =
      m (ts • e) + ∑ i ∈ Finset.Icc 1 (p + 1), t ^ i * (α ^ i * c i) := by
    have hr : 0 < 1 / (|α| + 1) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hr] with t ht
    have hu : 0 ≤ 1 + t * α := by
      have h1 : t * |α| ≤ 1 := by
        have h2 := ht.2
        rw [lt_div_iff₀ (by positivity)] at h2
        nlinarith [ht.1, abs_nonneg α]
      have := neg_abs_le α
      nlinarith [ht.1]
    have hpt : ts • e + t • α • ts • e = (1 + t * α) • ts • e := by
      rw [smul_smul, add_smul, one_smul]
    have hval : ∀ v : ℝ, 0 ≤ v → m (v • ts • e) = -β * v * ts + K * v ^ (p + 1) := fun v hv => by
      simp only [m, K, example1213Model, inner_smul_right, real_inner_self_eq_norm_sq, he,
        norm_smul, Real.norm_of_nonneg hv, Real.norm_of_nonneg ht0.le, mul_pow]
      ring
    have h1 : m (ts • e) = -β * ts + K := by simpa using hval 1 zero_le_one
    rw [hpt, hval _ hu, h1, add_comm (1 : ℝ), add_pow, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), zero_add, Nat.succ_eq_add_one,
      Finset.Ico_add_one_right_eq_Icc]
    simp only [c, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_Icc, le_refl, true_and]
    have : ∀ i ∈ Finset.Icc 1 (p + 1), K * ((t * α) ^ i * 1 ^ (p + 1 - i) * ((p + 1).choose i)) =
        t ^ i * (α ^ i * (K * ((p + 1).choose i))) := fun i _ => by ring
    rw [mul_add K, Finset.mul_sum, Finset.sum_congr rfl this]
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, pow_one,
      show (1 ≤ p + 1) = True from eq_true (by omega), ite_true]
    ring
  have hT := Optimization.taylorPolynomial_eq_of_poly hm hray (p := 3) (by omega)
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right, hT, show Finset.Icc 1 3 = {1, 2, 3} by decide]
  have hc1 : c 1 = 0 := by simp [c, ← hK]
  have hc2 : c 2 = σ * ts ^ (p + 1) / (2 ! * (p + 1 - 2)!) := by
    simp only [c, K, show ((2 : ℕ) = 1) = False from eq_false (by norm_num), ite_false, sub_zero]
    rw [Nat.cast_choose ℝ (by omega)]
    field_simp
  have hc3 : c 3 = σ * ts ^ (p + 1) / (3 ! * (p + 1 - 3)!) := by
    simp only [c, K, show ((3 : ℕ) = 1) = False from eq_false (by norm_num), ite_false, sub_zero]
    rw [Nat.cast_choose ℝ (by omega)]
    field_simp
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, hc1,
    hc2, hc3]
  ring

/-- The third-order Taylor decrement of the model of Example 12.1.3 at its minimizer `x* = e`
(the case `‖x*‖ = 1`, i.e. `β = σ/p!`) in an arbitrary direction `d`: with `a = ⟪e, d⟫`,
`ΔT_{m,3}(e, d) = -σ/(2 p!) (p a² + p(p-1)/3 a³ + (1 + (p-1) a)(‖d‖² - a²))`. Along the ray
`‖e + t d‖^{p+1} = (1 + 2ta + t²‖d‖²)^{(p+1)/2}`, expanded to third order. -/
theorem example1213_taylorDecrement_unit {p : ℕ} {σ : ℝ}
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (d : EuclideanSpace ℝ (Fin n)) :
    (ftaylorSeries ℝ (example1213Model (σ / p !) σ p e) e).taylorDecrement 3 d =
      -(σ / (2 * p !)) * (p * ⟪e, d⟫ ^ 2 + p * (p - 1) / 3 * ⟪e, d⟫ ^ 3 +
        (1 + (p - 1) * ⟪e, d⟫) * (‖d‖ ^ 2 - ⟪e, d⟫ ^ 2)) := by
  set a := ⟪e, d⟫
  set ν := ‖d‖ ^ 2
  set r : ℝ := ((p : ℝ) + 1) / 2
  set σ' : ℝ := σ / (p + 1)!
  set m := example1213Model (σ / p !) σ p e
  have hβ : σ / p ! = σ' * (p + 1) := by
    simp only [σ', Nat.factorial_succ]; push_cast; field_simp
  have he0 : e ≠ 0 := by rw [← norm_ne_zero_iff, he]; norm_num
  have hm : ContDiffAt ℝ 3 m e :=
    ((contDiff_const.mul ((contDiff_const (c := e)).inner ℝ contDiff_id)).contDiffAt).add
      ((((contDiffAt_norm ℝ he0).pow (p + 1)).const_smul σ).div_const _)
  set g : ℝ → ℝ := fun u => (1 + u) ^ r
  have hg : ContDiffAt ℝ 3 g 0 :=
    (contDiffAt_const.add contDiffAt_id).rpow_const_of_ne (by norm_num)
  have hgd : ∀ i, iteratedDeriv i g 0 = ∏ j : Fin i, (r - j) := fun i => by
    have := iteratedDeriv_const_add_rpow r 1 i 0 (by norm_num)
    simpa using this
  set T : ℝ → ℝ := fun h => 1 + r * h + r * (r - 1) / 2 * h ^ 2 + r * (r - 1) * (r - 2) / 6 * h ^ 3
  have hgT : ∀ h, taylorPolynomial g 3 0 h = T h := fun h => by
    simp only [taylorPolynomial_apply, Finset.sum_range_succ, Finset.sum_range_zero,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hgd, smul_eq_mul, T]
    simp [Fin.prod_univ_succ, Nat.factorial]
    ring
  have hP := sub_taylorPolynomial_isLittleO hg
  set u : ℝ → ℝ := fun t => 2 * a * t + ν * t ^ 2
  have hu : Tendsto u (𝓝[>] 0) (𝓝 0) := by
    have : Continuous u := by fun_prop
    simpa [u] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hP' : (fun t => g (u t) - T (u t)) =o[𝓝[>] 0] fun t => t ^ 3 := by
    have h1 := (hP.comp_tendsto hu)
    refine (h1.congr_left fun t => by simp [hgT]).trans_isBigO ?_
    have hb : ∀ t : ℝ, |t| ≤ 1 → ‖u t‖ ^ 3 ≤ (2 * |a| + |ν|) ^ 3 * |t| ^ 3 := fun t ht => by
      have : |u t| ≤ (2 * |a| + |ν|) * |t| := by
        simp only [u]
        calc |2 * a * t + ν * t ^ 2| ≤ |2 * a * t| + |ν * t ^ 2| := abs_add_le _ _
          _ = 2 * |a| * |t| + |ν| * (|t| * |t|) := by
              rw [abs_mul, abs_mul, abs_mul, abs_two, pow_two, abs_mul]
          _ ≤ 2 * |a| * |t| + |ν| * (1 * |t|) := by gcongr
          _ = (2 * |a| + |ν|) * |t| := by ring
      rw [Real.norm_eq_abs]
      calc |u t| ^ 3 ≤ ((2 * |a| + |ν|) * |t|) ^ 3 := by gcongr
        _ = _ := mul_pow _ _ _
    refine Asymptotics.IsBigO.of_bound ((2 * |a| + |ν|) ^ 3) ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)]
      with t ht
    have ht' : |t| ≤ 1 := by simpa [Real.dist_eq] using ht
    simpa [Function.comp_def, abs_pow] using hb t ht'
  have hr2 : (p : ℝ) + 1 = 2 * r := by simp only [r]; ring
  have hβ' : σ / p ! = σ' * (2 * r) := by rw [hβ, hr2]
  -- the model along the ray `t ↦ e + t d`
  have hnorm : ∀ t : ℝ, ‖e + t • d‖ ^ (p + 1) = g (u t) := fun t => by
    have hsq : ‖e + t • d‖ ^ 2 = 1 + u t := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        he]
      simp only [u, a, ν]
      ring
    simp only [g]
    rw [← hsq, ← Real.rpow_natCast (‖e + t • d‖) 2, ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_natCast]
    congr 1
    push_cast
    rw [hr2]
  have hmval : ∀ t : ℝ, m (e + t • d) = -(σ / p !) * (1 + t * a) + σ' * g (u t) := fun t => by
    simp only [m, example1213Model, hnorm, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, he]
    simp only [σ', a]
    ring
  have hme : m e = -(σ / p !) + σ' := by
    have := hmval 0
    simp only [zero_smul, add_zero, zero_mul, u, g] at this
    simpa using this
  set c₂ : ℝ := σ' * (r * ν + 2 * r * (r - 1) * a ^ 2)
  set c₃ : ℝ := σ' * (2 * r * (r - 1) * a * ν + 4 / 3 * r * (r - 1) * (r - 2) * a ^ 3)
  have hres : (fun t => m (e + t • d) - m e -
      ∑ i ∈ Finset.Icc 1 3, t ^ i * [0, 0, c₂, c₃].getD i 0) =o[𝓝[>] 0] fun t => t ^ 3 := by
    have h2 := Optimization.isLittleO_of_eq_pow_succ_mul (q := 3)
      (r := fun t => σ' * (T (u t) - 1) - σ / p ! * t * a - t ^ 2 * c₂ - t ^ 3 * c₃)
      (P := fun t => σ' * (r * (r - 1) / 2 * ν ^ 2 +
        r * (r - 1) * (r - 2) * (2 * a ^ 2 * ν + a * ν ^ 2 * t + ν ^ 3 * t ^ 2 / 6)))
      (by fun_prop) fun t => by
        simp only [T, u, c₂, c₃]
        rw [hβ']
        ring
    refine ((hP'.const_mul_left σ').add h2).congr_left fun t => ?_
    rw [hmval, hme, show Finset.Icc 1 3 = {1, 2, 3} by decide]
    simp
    ring
  have hT := Optimization.taylorPolynomial_eq_of_isLittleO hm hres (p := 3) le_rfl
  rw [ftaylorSeries_taylorDecrement_eq, hT, show Finset.Icc 1 3 = {1, 2, 3} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [List.getD_cons_succ, List.getD_cons_zero, c₂, c₃, σ']
  rw [Nat.factorial_succ]
  push_cast
  simp only [r]
  field_simp
  ring

/-- The elementary inequality behind the value of `φ^1_{m,3}(x*)` in Example 12.1.3: for `P > 4`,
`a² + t ≤ 1` and `t ≥ 0`, `P a² + P(P-1)/3 a³ + (1 + (P-1)a) t ≥ -P(P-4)/3`. -/
theorem example1213_bound {P a t : ℝ} (hP : 4 < P) (ha : a ^ 2 + t ≤ 1) (ht : 0 ≤ t) :
    -(P * (P - 4) / 3) ≤ P * a ^ 2 + P * (P - 1) / 3 * a ^ 3 + (1 + (P - 1) * a) * t := by
  have ha1 : 0 ≤ a + 1 := by nlinarith [sq_nonneg (a + 1)]
  rcases le_or_gt 0 (1 + (P - 1) * a) with hc | hc
  · have hQ : 0 ≤ (P - 1) * a ^ 2 - (P - 4) * a + (P - 4) := by
      nlinarith [sq_nonneg (2 * (P - 1) * a - (P - 4))]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ P) ha1) hQ, mul_nonneg hc ht]
  · have hR : 0 ≤ (P - 3) * a ^ 2 - (P - 6) * a + (P - 3) := by
      nlinarith [sq_nonneg (2 * (P - 3) * a - (P - 6))]
    have h1 : (1 + (P - 1) * a) * (1 - a ^ 2) ≤ (1 + (P - 1) * a) * t := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ P - 1) ha1) hR]

/-- **Example 12.1.3** ([cartis2022evaluation], (12.1.18)–(12.1.21)). Let `p ≥ 1`, `β, σ > 0`,
`‖e‖ = 1` and `m(x) = -β ⟪e, x⟫ + σ ‖x‖^{p+1}/(p+1)!` on `ℝⁿ`. Then:
(i) `m` has the unique global minimizer `x* = (β p!/σ)^{1/p} e`, with
`m(x*) = -p (p!/σ)^{1/p} β^{(p+1)/p}/(p+1)` ((12.1.19)–(12.1.20));
(ii) for `p ≥ 2`, along `x*`,
`ΔT_{m,3}(x*, α x*) = -σα²‖x*‖^{p+1}/(2(p-1)!) - σα³‖x*‖^{p+1}/(6(p-2)!)`
((12.1.21));
(iii) if `p > 4` and `‖x*‖ = 1`, then `φ^1_{m,3}(x*) = (p-4)σ/(6(p-1)!) > 0` (attained at
`d = -x*`): (12.1.16) fails for `j = 3` with `δ = 1` although `x*` is the global minimizer;
(iv) in one variable, `φ^δ_{m,j}(x*) = 0` for all `j ∈ [1, p]` and all radii with
`(p - 1) δ ≤ 3 |x*|` (no restriction when `j ≤ 2`). -/
theorem example_12_1_3 {p : ℕ} (hp : 1 ≤ p) {β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) :
    (IsMinOn (example1213Model β σ p e) univ ((β * p ! / σ) ^ (1 / (p : ℝ)) • e) ∧
      (∀ x, example1213Model β σ p e x =
        example1213Model β σ p e ((β * p ! / σ) ^ (1 / (p : ℝ)) • e) →
          x = (β * p ! / σ) ^ (1 / (p : ℝ)) • e) ∧
      example1213Model β σ p e ((β * p ! / σ) ^ (1 / (p : ℝ)) • e) =
        -p * (p ! / σ) ^ (1 / (p : ℝ)) * β ^ (((p : ℝ) + 1) / p) / (p + 1)) ∧
    (2 ≤ p → ∀ α : ℝ,
      (ftaylorSeries ℝ (example1213Model β σ p e)
          ((β * p ! / σ) ^ (1 / (p : ℝ)) • e)).taylorDecrement 3
          (α • (β * p ! / σ) ^ (1 / (p : ℝ)) • e) =
        -σ * α ^ 2 * ‖(β * p ! / σ) ^ (1 / (p : ℝ)) • e‖ ^ (p + 1) / (2 * (p - 1)!) -
          σ * α ^ 3 * ‖(β * p ! / σ) ^ (1 / (p : ℝ)) • e‖ ^ (p + 1) / (6 * (p - 2)!)) ∧
    (4 < p → ‖(β * p ! / σ) ^ (1 / (p : ℝ)) • e‖ = 1 →
      0 < ((p : ℝ) - 4) * σ / (6 * (p - 1)!) ∧
      phiMeasure (example1213Model β σ p e) 3 1 ((β * p ! / σ) ^ (1 / (p : ℝ)) • e) =
        ((p : ℝ) - 4) * σ / (6 * (p - 1)!)) ∧
    (∀ j ∈ Finset.Icc 1 p, ∀ δ : ℝ,
      (j ≤ 2 ∨ ((p : ℝ) - 1) * δ ≤ 3 * (β * p ! / σ) ^ (1 / (p : ℝ))) →
      phiMeasure (fun t : ℝ => -β * t + σ * |t| ^ (p + 1) / (p + 1)!) j δ
        ((β * p ! / σ) ^ (1 / (p : ℝ))) = 0) := by
  set ts := (β * p ! / σ) ^ (1 / (p : ℝ)) with hts
  set m := example1213Model β σ p e
  set g : ℝ → ℝ := fun r => -β * r + σ * r ^ (p + 1) / (p + 1)!
  have ht0 : 0 < ts := by positivity
  have htp : ts ^ p = β * p ! / σ := by
    rw [hts, one_div, Real.rpow_inv_natCast_pow (by positivity) (by omega)]
  have hK : σ * ts ^ (p + 1) / (p + 1)! * (p + 1) = β * ts := by
    rw [pow_succ, htp, Nat.factorial_succ]
    push_cast
    field_simp
  obtain ⟨hconv, hgmin⟩ := example1213_radial hp hβ hσ
  have hnorm : ‖ts • e‖ = ts := by rw [norm_smul, he, Real.norm_of_nonneg ht0.le, mul_one]
  have hmts : m (ts • e) = g ts := by
    simp only [m, g, example1213Model, hnorm, inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring
  have hmge : ∀ x, g ‖x‖ ≤ m x := fun x => by
    have := real_inner_le_norm e x
    rw [he, one_mul] at this
    simp only [m, g, example1213Model]
    nlinarith
  refine ⟨⟨fun x _ => ?_, fun x hx => ?_, ?_⟩, fun hp2 α => ?_, fun hp4 hn1 => ?_,
    fun j hj δ hδ => ?_⟩
  · -- (i) global minimality
    change m (ts • e) ≤ m x
    rw [hmts]
    exact (hgmin (norm_nonneg x)).trans (hmge x)
  · -- (i) uniqueness
    have h1 := hmge x
    have h2 : g ts ≤ g ‖x‖ := hgmin (norm_nonneg x)
    rw [hmts] at hx
    have hgx : g ‖x‖ = g ts := le_antisymm (h1.trans hx.le) h2
    have hnx : ‖x‖ = ts := hconv.eq_of_isMinOn (fun r hr => by
        change g ‖x‖ ≤ g r
        rw [hgx]
        exact hgmin hr) hgmin (norm_nonneg x) ht0.le
    have hin : ⟪e, x⟫ = ‖e‖ * ‖x‖ := by
      have : m x = g ‖x‖ := by rw [hx, hgx]
      simp only [m, g, example1213Model] at this
      rw [he, one_mul]
      nlinarith
    have := inner_eq_norm_mul_iff_real.1 hin
    rw [he, one_smul, hnx] at this
    exact this.symm
  · -- (i) the minimal value
    rw [hmts]
    simp only [g]
    have hpow : β ^ (((p : ℝ) + 1) / p) = β * β ^ (1 / (p : ℝ)) := by
      rw [show ((p : ℝ) + 1) / p = 1 + 1 / p by field_simp, Real.rpow_add hβ, Real.rpow_one]
    rw [hpow, show σ * ts ^ (p + 1) / (p + 1)! = β * ts / (p + 1) from
      eq_div_of_mul_eq (by positivity) hK]
    have hts' : ts = (p ! / σ) ^ (1 / (p : ℝ)) * β ^ (1 / (p : ℝ)) := by
      rw [hts, ← Real.mul_rpow (by positivity) hβ.le]
      ring_nf
    rw [hts']
    field_simp
    ring
  · -- (ii) the third-order Taylor decrement along `x*`
    rw [example1213_taylorDecrement hp2 hβ hσ he α, hnorm,
      show p + 1 - 2 = p - 1 by omega, show p + 1 - 3 = p - 2 by omega]
    simp only [Nat.factorial]
    push_cast
    ring
  · -- (iii) the measure of order `3` with radius `1` for `p > 4`, `‖x*‖ = 1`
    have hts1 : ts = 1 := by rw [← hnorm]; exact hn1
    have hβeq : β = σ / p ! := by
      have h1 := htp
      rw [hts1, one_pow] at h1
      have : (0 : ℝ) < p ! := by positivity
      field_simp at h1 ⊢
      linarith
    have hxs : ts • e = e := by rw [hts1, one_smul]
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
    have hk : (2 : ℝ) < k := by exact_mod_cast (show 2 < k by omega)
    refine ⟨by
      rw [show ((k + 2 : ℕ) : ℝ) - 4 = k - 2 by push_cast; ring]
      have : (0 : ℝ) < (k + 2 - 1)! := by positivity
      apply div_pos (mul_pos (by linarith) hσ) (by positivity), le_antisymm ?_ ?_⟩
    · -- upper bound: maximize the decrement over the unit ball
      change Optimization.taylorMeasure _ 3 1 univ ≤ _
      refine Optimization.decrementMeasure_le ⟨0, by simp, mem_univ _⟩ fun d hd => ?_
      have hd1 : ‖d‖ ≤ 1 := by simpa using hd.1
      have key := example1213_taylorDecrement_unit (p := k + 2) (σ := σ) he d
      rw [← hβeq] at key
      rw [show m = example1213Model β σ (k + 2) e from rfl, hxs, key]
      have ha : |⟪e, d⟫| ≤ ‖d‖ := by
        simpa [he] using abs_real_inner_le_norm e d
      have ha2 : ⟪e, d⟫ ^ 2 ≤ ‖d‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
      have hb := example1213_bound (P := ((k + 2 : ℕ) : ℝ)) (a := ⟪e, d⟫)
        (t := ‖d‖ ^ 2 - ⟪e, d⟫ ^ 2) (by push_cast; linarith)
        (by nlinarith [norm_nonneg d]) (by linarith)
      have hK : 0 < σ / (2 * ((k + 2 : ℕ) ! : ℝ)) := by positivity
      calc _ ≤ σ / (2 * ((k + 2 : ℕ) ! : ℝ)) *
            (((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 4) / 3) := by nlinarith
        _ = _ := by
          rw [show k + 2 - 1 = k + 1 by omega, Nat.factorial_succ (k + 1)]
          push_cast
          field_simp
          ring
    · -- lower bound: the displacement `-x*`
      have hle := sub_taylorPolynomial_le_phiMeasure m 3 (ts • e) (d := (-1 : ℝ) • ts • e)
        (δ := 1) (by rw [norm_smul, hnorm, hts1]; simp)
      have hΔ := example1213_taylorDecrement (by omega : 2 ≤ k + 2) hβ hσ he (-1)
      rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
        taylorPolynomial_zero_right] at hΔ
      refine le_trans (le_of_eq ?_) (hΔ ▸ hle)
      rw [← hts, hts1, show k + 2 + 1 - 2 = k + 1 by omega, show k + 2 + 1 - 3 = k by omega,
        show k + 2 - 1 = k + 1 by omega, Nat.factorial_succ k]
      simp only [Nat.factorial]
      push_cast
      field_simp
      ring
  · -- (iv) one variable: the backbone computation
    exact Optimization.taylorMeasure_linearRegModel_eq_zero
      (Set.mem_Icc.2 (Finset.mem_Icc.1 hj)) hβ hσ hδ

end Example3

/-! ### Sufficient conditions (§12.1.4) -/

section Sufficient

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- **Theorem 12.1.5 is false as printed** ([cartis2022evaluation]). Let
`f(x) = (x₂ - x₁²)² + x₂⁶ - x₁⁷` on `ℝ²` and `j = 6`, `x = 0`. Then `f` is a polynomial (hence
`C^∞`, with `‖∇⁷f(0)‖` bounded), `T_{f,6}(0, s) = (s₂ - s₁²)² + s₂⁶` has the isolated (strict,
even global) minimizer `s = 0`, but `T_{f,7}(0, ·) = f` and `f(t, t²) = t¹² - t⁷ < 0` for
`t ∈ (0, 1)`: the origin is neither an isolated minimizer of `T_{f,7}(0, ·)` nor a local
minimizer of `f`. In particular the printed statement fails. (The printed proof chooses `|α|`
small for each direction separately; the radius is not uniform. `theorem_12_1_5` is the
corrected statement.) -/
theorem theorem_12_1_5_counterexample :
    let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => (x 1 - x 0 ^ 2) ^ 2 + x 1 ^ 6 - x 0 ^ 7
    ContDiff ℝ ∞ f ∧
      (∀ s, taylorPolynomial f 6 0 s = (s 1 - s 0 ^ 2) ^ 2 + s 1 ^ 6) ∧
      Optimization.IsStrictLocalMinOn (taylorPolynomial f 6 0) univ 0 ∧
      taylorPolynomial f 7 0 = f ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, f (!₂[t, t ^ 2]) < 0) ∧
      ¬ IsLocalMin f 0 ∧
      ¬ (∀ (g : EuclideanSpace ℝ (Fin 2) → ℝ) (L : ℝ), ContDiff ℝ 7 g →
        Optimization.IsStrictLocalMinOn (taylorPolynomial g 6 0) univ 0 →
        ‖iteratedFDeriv ℝ 7 g 0‖ ≤ L → IsLocalMin g 0) := by
  intro f
  have hf : ContDiff ℝ ∞ f :=
    ((((contDiff_coord 1).sub ((contDiff_coord 0).pow 2)).pow 2).add
      ((contDiff_coord 1).pow 6)).sub ((contDiff_coord 0).pow 7)
  have hf0 : f 0 = 0 := by simp [f]
  -- the expansion of `f` along a ray
  have hray : ∀ s : EuclideanSpace ℝ (Fin 2), ∀ t : ℝ, f (0 + t • s) = f 0 +
      ∑ i ∈ Finset.Icc 1 7, t ^ i * [0, 0, s 1 ^ 2, -2 * s 1 * s 0 ^ 2, s 0 ^ 4, 0, s 1 ^ 6,
        -s 0 ^ 7].getD i 0 := fun s t => by
    rw [show Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} by decide]
    simp [f]
    ring
  have hT6 : ∀ s, taylorPolynomial f 6 0 s = (s 1 - s 0 ^ 2) ^ 2 + s 1 ^ 6 := fun s => by
    rw [Optimization.taylorPolynomial_eq_of_poly (hf.contDiffAt.of_le (by simp))
      (Eventually.of_forall (hray s)) (by norm_num), hf0]
    rw [show Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} by decide]
    simp
    ring
  have hT7 : taylorPolynomial f 7 0 = f := funext fun s => by
    rw [Optimization.taylorPolynomial_eq_self_of_poly (hf.contDiffAt.of_le (by simp))
      (hray s), zero_add]
  have hneg : ∀ t ∈ Ioo (0 : ℝ) 1, f (!₂[t, t ^ 2]) < 0 := fun t ht => by
    have h5 : t ^ 5 < 1 := pow_lt_one₀ ht.1.le ht.2 (by norm_num)
    have h7 : 0 < t ^ 7 := pow_pos ht.1 7
    have : f (!₂[t, t ^ 2]) = t ^ 7 * (t ^ 5 - 1) := by simp [f]; ring
    rw [this]
    exact mul_neg_of_pos_of_neg h7 (by linarith)
  have hnotmin : ¬ IsLocalMin f 0 := by
    refine Optimization.not_isLocalMin_of_curve (l := 𝓝[>] (0 : ℝ))
      (γ := fun t : ℝ => !₂[t, t ^ 2]) ?_ ?_
    · have hc : Continuous fun t : ℝ => (!₂[t, t ^ 2] : EuclideanSpace ℝ (Fin 2)) :=
        (PiLp.continuous_toLp 2 _).comp (by fun_prop)
      have h0 : (!₂[(0 : ℝ), (0 : ℝ) ^ 2] : EuclideanSpace ℝ (Fin 2)) = 0 := by
        ext i; fin_cases i <;> simp
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simp only [h0] at this
      exact this
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      rw [hf0]
      exact hneg t ht
  have hstrict : Optimization.IsStrictLocalMinOn (taylorPolynomial f 6 0) univ 0 := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have hy0 : y ≠ 0 := hy.2
    rw [hT6, hT6]
    simp only [PiLp.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero, add_zero]
    rcases eq_or_ne (y 1) 0 with h1 | h1
    · have h0 : y 0 ≠ 0 := fun h0 => hy0 (by ext i; fin_cases i <;> simp [h0, h1])
      rw [h1]
      have : 0 < y 0 ^ 4 := by positivity
      nlinarith
    · have : 0 < y 1 ^ 6 := by positivity
      nlinarith [sq_nonneg (y 1 - y 0 ^ 2)]
  refine ⟨hf, hT6, hstrict, hT7, hneg, hnotmin, fun h => hnotmin ?_⟩
  exact h f _ (hf.of_le (by simp)) hstrict le_rfl

/-- **Theorem 12.1.5** ([cartis2022evaluation]), corrected. Let `f` be `C^{j+1}` near `x` with
`‖∇^{j+1} f(x)‖ ≤ L`, and suppose that `s = 0` is a *uniformly* isolated minimizer of
`T_{f,j}(x, ·)`: `c ‖s‖^j ≤ T_{f,j}(x, s) - f(x)` for `‖s‖ ≤ r`, with `c, r > 0`. Then `s = 0` is
an isolated (strict) local minimizer of `T_{f,j+1}(x, ·)` and `x` is an isolated local minimizer
of `f`. (As printed, with "isolated minimizer of `T_{f,j}(x, ·)`" only, the theorem is false:
`theorem_12_1_5_counterexample`.) -/
theorem theorem_12_1_5 {f : 𝔼 → ℝ} {x : 𝔼} {j : ℕ} {L c r : ℝ}
    (hf : ContDiffAt ℝ (j + 1) f x) (hL : ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L) (hc : 0 < c)
    (hr : 0 < r) (hgrowth : ∀ s : 𝔼, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ taylorPolynomial f j x s - f x) :
    Optimization.IsStrictLocalMinOn (taylorPolynomial f (j + 1) x) univ 0 ∧
      Optimization.IsStrictLocalMinOn f univ x := by
  refine ⟨?_, Optimization.isStrictLocalMin_of_taylorPolynomial_growth
    (hf.of_le (by exact_mod_cast Nat.le_succ j)) hc hr hgrowth⟩
  rw [taylorPolynomial_eq_taylorSum]
  refine Optimization.isStrictLocalMin_taylorPolynomial_succ_of_growth _ hc hr hL fun s hs => ?_
  have h0 : (ftaylorSeries ℝ f x).taylorSum j 0 = f x := taylorPolynomial_zero_right f j x
  rw [h0]
  exact hgrowth s hs

end Sufficient

/-! ### Approximate minimizers (§12.1.5) -/

section Approx

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- **Key Definition (12.1.25)** ([cartis2022evaluation]): given tolerances
`ε = (ε_1, …, ε_q) ∈ (0, 1]^q` and optimality radii `δ = (δ_1, …, δ_q) ∈ (0, 1]^q`, `x` is an
*`(ε, δ)`-approximate `q`-th order minimizer* of `f` when `φ^{δ_j}_{f,j}(x) ≤ ε_j δ_j^j / j!` for
all `j ∈ [1, q]`. -/
def IsEpsDeltaApproxMinimizer (f : 𝔼 → ℝ) (q : ℕ) (ε δ : ℕ → ℝ) (x : 𝔼) : Prop :=
  (∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1 ∧ δ j ∈ Ioc 0 1) ∧
    Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f x) univ q ε δ

theorem isEpsDeltaApproxMinimizer_iff {q : ℕ} {ε δ : ℕ → ℝ} :
    IsEpsDeltaApproxMinimizer f q ε δ x ↔
      (∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1 ∧ δ j ∈ Ioc 0 1) ∧
        ∀ j ∈ Finset.Icc 1 q, phiMeasure f j (δ j) x ≤ ε j * δ j ^ j / j ! := by
  rw [IsEpsDeltaApproxMinimizer, Optimization.isEpsDeltaApprox_iff]

/-- **Nested optimality** ([cartis2022evaluation], after Theorem 12.1.7): an `(ε, δ)`-approximate
`q`-th order minimizer is an `(ε, δ)`-approximate `q'`-th order minimizer for every `q' ≤ q`. -/
theorem IsEpsDeltaApproxMinimizer.mono {q q' : ℕ} {ε δ : ℕ → ℝ}
    (h : IsEpsDeltaApproxMinimizer f q ε δ x) (hq : q' ≤ q) :
    IsEpsDeltaApproxMinimizer f q' ε δ x := by
  rw [isEpsDeltaApproxMinimizer_iff] at h ⊢
  exact ⟨fun j hj => h.1 j (Finset.Icc_subset_Icc_right hq hj),
    fun j hj => h.2 j (Finset.Icc_subset_Icc_right hq hj)⟩

/-- **Theorem 12.1.6 (i)** ([cartis2022evaluation], (12.1.22)): if `δ₁ > 0` and
`φ^{δ₁}_{f,1}(x) ≤ ε₁ δ₁`, then `‖∇f(x)‖ ≤ ε₁`. -/
theorem theorem_12_1_6_i {ε₁ δ₁ : ℝ} (hδ : 0 < δ₁) (h : phiMeasure f 1 δ₁ x ≤ ε₁ * δ₁) :
    ‖gradient f x‖ ≤ ε₁ := by
  rw [(theorem_12_1_3_i hδ).1, div_le_iff₀ hδ]
  exact h

/-- **Theorem 12.1.6 (ii)** ([cartis2022evaluation], (12.1.23), (12.1.28)), with an explicit
constant: if `δ > 0`, `ε₂ ≥ 0` and `φ^δ_{f,2}(x) ≤ ε₂ δ²/2`, then `λ_min[∇²f(x)] ≥ -ε₂` and
`‖∇f(x)‖² ≤ δ² ε₂ max(‖∇²f(x)‖, ε₂)`; hence, for `ε₂ ≤ 1`, `‖∇f(x)‖ ≤ δ κ(x) √ε₂` with
`κ(x) = √(max(‖∇²f(x)‖, 1))`. -/
theorem theorem_12_1_6_ii {ε₂ δ : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε₂)
    (h : phiMeasure f 2 δ x ≤ ε₂ * δ ^ 2 / 2) :
    -ε₂ ≤ Chapter01.hessianMinEig f x ∧
      ‖gradient f x‖ ^ 2 ≤ δ ^ 2 * ε₂ * max ‖iteratedFDeriv ℝ 2 f x‖ ε₂ ∧
      (ε₂ ≤ 1 → ‖gradient f x‖ ≤ δ * √(max ‖iteratedFDeriv ℝ 2 f x‖ 1) * √ε₂) := by
  have h2 := Optimization.norm_sq_le_of_taylorMeasure_two_le _ hδ hε h
  rw [norm_ftaylorSeries_one] at h2
  refine ⟨Optimization.neg_le_minCurvature_of_taylorMeasure_two_le _ hδ hε h, h2, fun hε1 => ?_⟩
  have h3 : ‖gradient f x‖ ^ 2 ≤ (δ * √(max ‖iteratedFDeriv ℝ 2 f x‖ 1) * √ε₂) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (le_max_of_le_right zero_le_one), Real.sq_sqrt hε]
    refine h2.trans ?_
    have : max ‖iteratedFDeriv ℝ 2 f x‖ ε₂ ≤ max ‖iteratedFDeriv ℝ 2 f x‖ 1 :=
      max_le_max le_rfl hε1
    calc δ ^ 2 * ε₂ * max ‖iteratedFDeriv ℝ 2 f x‖ ε₂
        ≤ δ ^ 2 * ε₂ * max ‖iteratedFDeriv ℝ 2 f x‖ 1 := by gcongr
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

/-- **Theorem 12.1.7** ([cartis2022evaluation], proof in Appendix B): cascading approximate
optimality. Let `j ≥ 2`, `ε_j, δ_j ∈ (0, 1]`, `ε_j ≤ ε_{j-1}`, `φ^{δ_j}_{f,j}(x) ≤ ε_j δ_j^j/j!`
(12.1.30) and `2 δ_j ‖∇^j f(x)‖ ≤ j ε_j` (the book's `δ_j ≤ jε_j/(2‖∇^j f(x)‖)`). Then
`φ^{δ_j}_{f,j-1}(x) ≤ ε_{j-1} δ_j^{j-1}/(j-1)!` (12.1.31). -/
theorem theorem_12_1_7 {j : ℕ} {ε : ℕ → ℝ} {δ : ℝ} (hj : 2 ≤ j) (hε : ε j ∈ Ioc 0 1)
    (hδ : δ ∈ Ioc 0 1) (hεε : ε j ≤ ε (j - 1)) (h : phiMeasure f j δ x ≤ ε j * δ ^ j / j !)
    (hδε : 2 * δ * ‖iteratedFDeriv ℝ j f x‖ ≤ j * ε j) :
    phiMeasure f (j - 1) δ x ≤ ε (j - 1) * δ ^ (j - 1) / (j - 1)! := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hεε ⊢
  refine Optimization.taylorMeasure_le_of_taylorMeasure_succ_le _ (by omega) (mem_univ 0)
    hδ.1.le hδ.2 hε.1.le hεε h ?_
  have : ‖ftaylorSeries ℝ f x (k + 1)‖ = ‖iteratedFDeriv ℝ (k + 1) f x‖ := rfl
  rw [this]
  push_cast at hδε
  linarith

/-- **Example 12.1.4** ([cartis2022evaluation]): for `f(t) = t⁴/24` and `x ≠ 0`,
`φ^{|x|}_{f,4}(x) = x⁴/24` (the optimality displacement is `d = -x`). Hence (12.1.25) at order `4`
with radius `δ₄ = |x|` holds iff `ε₄ ≥ 1`: with radii shrinking like `|x_k|`, no iterate
`x_k ≠ 0` is detected as approximately optimal for `ε₄ < 1`. -/
theorem example_12_1_4 {x : ℝ} (hx : x ≠ 0) :
    phiMeasure (fun t : ℝ => t ^ 4 / 24) 4 |x| x = x ^ 4 / 24 ∧
      ∀ ε₄ : ℝ, (phiMeasure (fun t : ℝ => t ^ 4 / 24) 4 |x| x ≤ ε₄ * |x| ^ 4 / 4! ↔ 1 ≤ ε₄) := by
  set f : ℝ → ℝ := fun t => t ^ 4 / 24
  have hf : ContDiffAt ℝ 4 f x := ((contDiff_id.pow 4).div_const 24).contDiffAt
  -- the Taylor polynomial of degree 4 of a quartic is the quartic itself
  have hT : ∀ d : ℝ, taylorPolynomial f 4 x d = f (x + d) := fun d =>
    Optimization.taylorPolynomial_eq_self_of_poly hf (a := fun i => [0, 4 * x ^ 3 * d / 24,
      6 * x ^ 2 * d ^ 2 / 24, 4 * x * d ^ 3 / 24, d ^ 4 / 24].getD i 0) fun t => by
        simp [f, Finset.sum_Icc_succ_top, smul_eq_mul]
        ring
  have hφ : phiMeasure f 4 |x| x = x ^ 4 / 24 := by
    rw [phiMeasure_eq_sSup]
    refine IsGreatest.csSup_eq ⟨⟨-x, by simp, by simp [hT, f]⟩, ?_⟩
    rintro _ ⟨d, -, rfl⟩
    simp only [hT, f]
    have : 0 ≤ (x + d) ^ 4 := by positivity
    linarith
  refine ⟨hφ, fun ε₄ => ?_⟩
  have hx4 : 0 < x ^ 4 := by positivity
  rw [hφ, show |x| ^ 4 = x ^ 4 by rw [pow_abs, abs_of_nonneg hx4.le]]
  norm_num [Nat.factorial]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end Approx

/-! ### Stability (§12.1.7) -/

section Stability

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- **Theorem 12.1.8** ([cartis2022evaluation]): stability of approximate minimizers. Let `f` be
`C^j` on an open ball `B(x, r)` with `r > δ_j`, `∇^j f` Lipschitz with constant `L ≥ 0` on it,
and `φ^{δ_j}_{f,j}(x) ≤ ε_j δ_j^j / j!` (12.1.34) (the book's `δ_j, ε_j ∈ (0, 1]` are not
needed). If `L > 0`, then `f(x + d) ≥ f(x) - 2 ε_j δ_j^j / j!` whenever
`‖d‖ ≤ min(δ_j, (j+1) ε_j / L)` (12.1.35); if
`L = 0`, `f(x + d) ≥ f(x) - ε_j δ_j^j / j!` whenever `‖d‖ ≤ δ_j` (12.1.36). -/
theorem theorem_12_1_8 {f : 𝔼 → ℝ} {x : 𝔼} {j : ℕ} {r L ε δ : ℝ}
    (hf : ContDiffOn ℝ j f (ball x r)) (hr : δ < r) (hL0 : 0 ≤ L)
    (hL : IteratedFDerivLipschitzOn f j L (ball x r)) (h : phiMeasure f j δ x ≤ ε * δ ^ j / j !) :
    (0 < L → ∀ d : 𝔼, ‖d‖ ≤ min δ ((j + 1) * ε / L) → f x - 2 * ε * δ ^ j / j ! ≤ f (x + d)) ∧
      (L = 0 → ∀ d : 𝔼, ‖d‖ ≤ δ → f x - ε * δ ^ j / j ! ≤ f (x + d)) := by
  have hsub : closedBall x δ ⊆ ball x r := closedBall_subset_ball hr
  have hf' : ∀ y ∈ closedBall x δ, ContDiffAt ℝ j f y := fun y hy =>
    hf.contDiffAt (isOpen_ball.mem_nhds (hsub hy))
  have hL' := hL.mono hsub
  have h' : Optimization.taylorMeasure (ftaylorSeries ℝ f x) j δ univ ≤ ε * δ ^ j / j ! + 0 := by
    rw [add_zero]; exact h
  refine ⟨fun hLpos d hd => ?_, fun hL0' d hd => ?_⟩
  · have hLd : L * ‖d‖ ≤ (j + 1) * ε := by
      have := (le_div_iff₀' hLpos).1 (hd.trans (min_le_right _ _))
      linarith
    have := Optimization.le_of_taylorMeasure_le_of_mul_le hf' hL' hL0 h' (mem_univ d)
      (hd.trans (min_le_left _ _)) hLd
    linarith
  · subst hL0'
    have := Optimization.le_of_taylorMeasure_le_of_lipschitz_zero hf' hL' h' (mem_univ d) hd
    linarith

end Stability

end CartisGouldToint.Chapter12
