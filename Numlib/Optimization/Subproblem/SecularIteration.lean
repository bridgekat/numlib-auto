import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Numlib.Nonlinear.MonotoneNewton
import Numlib.Optimization.Subproblem.Secular

/-!
# Iterations for the secular equation

Let `H` be symmetric with leftmost eigenvalue `λ₁`, `g ≠ 0`, `s(λ) = -(H + λ)⁻¹ g` and
`π(λ) = ‖s(λ)‖²` (`Numlib.Optimization.Subproblem.Secular`). The multiplier `λ*` of the
trust-region and regularization subproblems is, in the easy case, the root in `(λₛ, ∞)` of a
secular equation `π(λ) = τ(λ)`, with `τ = Δ²` (trust region) or `τ(λ) = (λ/σ)^{2/(r-2)}`
(regularization). This file proves that the corrections of Cartis–Gould–Toint, *Evaluation
complexity of algorithms for nonconvex optimization*, §8.2–§8.3, computed from a current
`λc ∈ 𝓛 = (λₛ, λ*]`, never pass `λ*`, and that the resulting monotone iterations converge.

## Main definitions

* `secularTaylor g H k λc δ`: the Taylor polynomial `tₖ(δ)` of `π` at `λc` (8.2.12), and
  `taylorCorrection g H τ k λc`: the rightmost root of `tₖ(δ) = τ(λc + δ)` (8.2.15).
* `trSecular g H Δ β` and `regSecular g H σ r β`: the transformed secular functions
  `θ_β = π ^ β - τ ^ β` of the two subproblems.
* `trNewtonCorrection g H Δ λc` (8.2.24) and `regNewtonCorrection g H σ r β λc` (8.2.25): the
  Newton corrections on `θ_β`.
* `IsSecularTarget hH g τ a λ*`: the standing hypotheses of the Taylor iterations.

## Main results

* `newtonCorrection_eq`, `trNewtonCorrection_eq`, `regNewtonCorrection_eq`: closed forms
  ((B.8.7), (8.2.24), (8.2.25)).
* `trSecular_shape`, `regSecular_shape`: convexity, monotonicity and derivative signs of `θ_β`.
* `trNewtonCorrection_mem`, `regNewtonCorrection_mem`: from `λc ≤ λ*` the Newton corrections
  land in `[λc, λ*]`; from `λc > λ*` (in `𝓖`) they overshoot to `≤ λ*`.
* `IsSecularTarget.taylorCorrection_mem`, `IsSecularTarget.isGreatest_taylorCorrection`: odd-order
  Taylor corrections are attained roots of (8.2.15) and land in `[λc, λ*]`.
* `tendsto_of_trNewtonCorrection_le`, `tendsto_of_regNewtonCorrection_le`: iterations taking
  steps at least as long as a Newton correction without passing `λ*` (plain Newton, the
  `β`-maximizing iteration (8.2.26), Algorithms 8.3.1/8.3.2) increase to `λ*`, globally
  `Q`-linearly and ultimately `Q`-superlinearly (Lemma B.8.1).
* `IsSecularTarget.tendsto_of_taylorCorrection_le`: the same iterations with odd-order Taylor
  corrections increase to `λ*`.

## Implementation notes

The root `λ*` is a hypothesis (`π(λ*) = τ(λ*)` with `λ* > λₛ`, the easy case) rather than the
multiplier of a global minimizer; the two agree by the optimality conditions of §8.3. Domains are
`λ > -λ₁` for the trust region and the Taylor corrections and `λ > λₛ = max 0 (-λ₁)` for
regularization, where `λ ↦ (λ/σ) ^ γ` needs `λ > 0`.

## Hypotheses

* In (8.2.25) `βⱼ ∈ [-1/2, (r-2)/2]` must be nonzero, since `θ₀ ≡ 0`. The `β → 0` limit of the
  trust-region factor is `newtonFactor μ 0 = -log μ`, the Newton step for `log π - log τ`, which is
  not treated here.
* Convexity of `-λ^γ` for `γ ∈ (0, 1]` and concavity for `γ < 0` hold on `λ > 0`; the interval
  `λ ≥ λₛ` may contain `0` when `λ₁ ≥ 0`.

## Not formalized

* The ultimate `Q`-order `k` of the odd-order Taylor iterations stated in §8.3: only their
  convergence is proved.
* The overshoot from `𝓖` in the hard case (when `λ* = λₛ` is not a root in the open domain), and
  the "least-negative root" remark of §8.2.1.
-/

open Set Filter Topology
open Finset (range)
open scoped Nat RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E}

/-! ### Definitions -/

/-- The `k`-th order Taylor polynomial `tₖ(δ) = ∑_{j ≤ k} π⁽ʲ⁾(λc) / j! δʲ` of the secular
function at `λc` (book (8.2.12)). -/
noncomputable def secularTaylor (g : E) (H : E →L[ℝ] E) (k : ℕ) (lamc δ : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j

/-- The Taylor correction `δₖᵀ(λc)` (book §8.2.1 and Algorithm 8.3.1): the rightmost real root of
`tₖ(δ) = τ(λc + δ)` (8.2.15), defined as the supremum of the root set (which is nonempty and
bounded above for odd `k` and `λc ∈ 𝓛`, `taylorCorrection_mem`). -/
noncomputable def taylorCorrection (g : E) (H : E →L[ℝ] E) (τ : ℝ → ℝ) (k : ℕ) (lamc : ℝ) : ℝ :=
  sSup {δ | secularTaylor g H k lamc δ = τ (lamc + δ)}

/-- The transformed trust-region secular function `θ_β(λ) = π(λ) ^ β - Δ ^ (2 β)` (book (8.2.16)
with `τ = Δ²`). -/
noncomputable def trSecular (g : E) (H : E →L[ℝ] E) (Δ β lam : ℝ) : ℝ :=
  secular g H lam ^ β - Δ ^ (2 * β)

/-- The trust-region Newton correction (book (8.2.24)):
`δᴺ = 2 π(λc) / π'(λc) (1 - ‖s(λc)‖ / Δ)`, the Newton step for `π(λ) ^ (-1/2) = Δ⁻¹`
(`trNewtonCorrection_eq`). -/
noncomputable def trNewtonCorrection (g : E) (H : E →L[ℝ] E) (Δ lamc : ℝ) : ℝ :=
  2 * secular g H lamc / deriv (secular g H) lamc * (1 - ‖step g H lamc‖ / Δ)

/-- The transformed regularization secular function
`θ_β(λ) = π(λ) ^ β - (λ / σ) ^ (2 β / (r - 2))` (book §8.2.2). -/
noncomputable def regSecular (g : E) (H : E →L[ℝ] E) (σ r β lam : ℝ) : ℝ :=
  secular g H lam ^ β - (lam / σ) ^ (2 * β / (r - 2))

/-- The regularization Newton correction `δᴺ(λc, β) = -θ_β(λc) / θ_β'(λc)` (book (8.2.25), first
line). -/
noncomputable def regNewtonCorrection (g : E) (H : E →L[ℝ] E) (σ r β lamc : ℝ) : ℝ :=
  -regSecular g H σ r β lamc / deriv (regSecular g H σ r β) lamc

variable {g : E} {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-! ### Derivatives -/

theorem hasDerivAt_trSecular (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) (Δ β : ℝ) :
    HasDerivAt (trSecular g H Δ β)
      (β * secular g H lam ^ (β - 1) * deriv (secular g H) lam) lam :=
  (hasDerivAt_secular_rpow hg hlam β).sub_const _

theorem hasDerivAt_regSecular (hg : g ≠ 0) {σ r β lam : ℝ} (hσ : 0 < σ)
    (hlam : -leftmost hH < lam) (hpos : 0 < lam) :
    HasDerivAt (regSecular g H σ r β)
      (β * secular g H lam ^ (β - 1) * deriv (secular g H) lam -
        2 * β / (r - 2) * (lam / σ) ^ (2 * β / (r - 2) - 1) / σ) lam := by
  have h2 := ((hasDerivAt_id' lam).div_const σ).rpow_const (p := 2 * β / (r - 2))
    (Or.inl (div_pos hpos hσ).ne')
  exact ((hasDerivAt_secular_rpow hg hlam β).sub h2).congr_deriv (by ring)

/-! ### Closed forms of the Newton corrections -/

/-- **The Newton step on the transformed trust-region secular equation** (book (B.8.7)). For
`g ≠ 0`, `λc > -λ₁`, `Δ > 0` and `β ≠ 0`, the Newton correction for
`θ_β(λ) = π(λ) ^ β - Δ ^ (2 β) = 0` from `λc` is `(-π/π') · newtonFactor (Δ²/π) β`, with
`π = π(λc)`, `π' = π'(λc)`. By `antitone_newtonFactor` (Lemma B.8.2) it decreases as `β`
increases, so `β = -1/2` (`trNewtonCorrection_eq`) gives the longest step among `β ≥ -1/2`. -/
theorem newtonCorrection_eq (hg : g ≠ 0) {lamc Δ β : ℝ} (hlam : -leftmost hH < lamc)
    (hΔ : 0 < Δ) (hβ : β ≠ 0) :
    -trSecular g H Δ β lamc / deriv (trSecular g H Δ β) lamc =
      -secular g H lamc / deriv (secular g H) lamc *
        newtonFactor (Δ ^ 2 / secular g H lamc) β := by
  rw [(hasDerivAt_trSecular hg hlam Δ β).deriv, newtonFactor_of_ne_zero _ hβ, trSecular,
    Real.div_rpow (sq_nonneg _) (secular_pos hg hlam).le, Real.rpow_mul hΔ.le, Real.rpow_two,
    Real.rpow_sub_one (secular_pos hg hlam).ne']
  have hp := (secular_pos (hH := hH) hg hlam).ne'
  have hp' := (deriv_secular_neg (hH := hH) hg hlam).ne
  have hA : secular g H lamc ^ β ≠ 0 := (Real.rpow_pos_of_pos (secular_pos hg hlam) _).ne'
  field_simp

/-- The trust-region correction (8.2.24) is the `β = -1/2` case of `newtonCorrection_eq`, i.e.
the Newton step for `π(λ) ^ (-1/2) = Δ⁻¹`. -/
theorem trNewtonCorrection_eq (hg : g ≠ 0) {lamc Δ : ℝ} (hlam : -leftmost hH < lamc)
    (hΔ : 0 < Δ) :
    trNewtonCorrection g H Δ lamc = -trSecular g H Δ (-1 / 2) lamc /
      deriv (trSecular g H Δ (-1 / 2)) lamc := by
  rw [newtonCorrection_eq hg hlam hΔ (by norm_num), newtonFactor_of_ne_zero _ (by norm_num),
    trNewtonCorrection]
  have hs : 0 < ‖step g H lamc‖ := by
    have := secular_pos (hH := hH) hg hlam
    rw [secular] at this
    exact norm_pos_iff.2 fun h => by simp [h] at this
  have hpow : (Δ ^ 2 / secular g H lamc) ^ (-1 / 2 : ℝ) = ‖step g H lamc‖ / Δ := by
    rw [secular, ← div_pow, ← Real.rpow_two, ← Real.rpow_mul (div_pos hΔ hs).le]
    norm_num [Real.rpow_neg_one, inv_div]
  rw [hpow]
  ring

/-- **The regularization Newton correction in closed form** (book (8.2.25), last line). For
`g ≠ 0`, `σ > 0`, `r > 2`, `β ≠ 0` and `λc > max 0 (-λ₁)`, with `π = π(λc)`, `π' = π'(λc)`,
`μ = (λc/σ) ^ (2/(r-2)) / π` and `ω = 2π / ((r - 2) λc π')`:
`δᴺ(λc, β) = (-π/π') (1 - μ^β) / (β (1 - ω μ^β))`, and `1 - ω μ^β > 0` (as `ω < 0`). -/
theorem regNewtonCorrection_eq (hg : g ≠ 0) {σ r β lamc : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hβ : β ≠ 0) (hlam : -leftmost hH < lamc) (hpos : 0 < lamc) :
    0 < 1 - 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) *
        ((lamc / σ) ^ (2 / (r - 2)) / secular g H lamc) ^ β ∧
    regNewtonCorrection g H σ r β lamc =
      -secular g H lamc / deriv (secular g H) lamc *
        ((1 - ((lamc / σ) ^ (2 / (r - 2)) / secular g H lamc) ^ β) /
          (β * (1 - 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) *
            ((lamc / σ) ^ (2 / (r - 2)) / secular g H lamc) ^ β))) := by
  have hp := secular_pos (hH := hH) hg hlam
  have hp' := deriv_secular_neg (hH := hH) hg hlam
  have hr2 : 0 < r - 2 := by linarith
  have hx : 0 < lamc / σ := div_pos hpos hσ
  have hμ : ((lamc / σ) ^ (2 / (r - 2)) / secular g H lamc) ^ β =
      (lamc / σ) ^ (2 * β / (r - 2)) / secular g H lamc ^ β := by
    rw [Real.div_rpow (Real.rpow_nonneg hx.le _) hp.le, ← Real.rpow_mul hx.le]
    congr 2
    ring
  rw [hμ]
  set A := secular g H lamc ^ β with hA_def
  set B := (lamc / σ) ^ (2 * β / (r - 2)) with hB_def
  have hA : 0 < A := Real.rpow_pos_of_pos hp _
  have hB : 0 < B := Real.rpow_pos_of_pos hx _
  have hω : 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) < 0 :=
    div_neg_of_pos_of_neg (by positivity) (mul_neg_of_pos_of_neg (by positivity) hp')
  have hpos' : 0 < 1 - 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) *
      (B / A) := by
    have : 0 < B / A := div_pos hB hA
    nlinarith
  refine ⟨hpos', ?_⟩
  rw [regNewtonCorrection, (hasDerivAt_regSecular hg hσ hlam hpos).deriv, regSecular,
    Real.rpow_sub_one hp.ne', Real.rpow_sub_one hx.ne', ← hA_def, ← hB_def]
  have hpne := hp.ne'
  have hp'ne := hp'.ne
  have hAne := hA.ne'
  have hσne := hσ.ne'
  have hlne := hpos.ne'
  have hr2ne := hr2.ne'
  have hD : β * (A / secular g H lamc) * deriv (secular g H) lamc -
      2 * β / (r - 2) * (B / (lamc / σ)) / σ =
      β * deriv (secular g H) lamc / secular g H lamc * A *
        (1 - 2 * secular g H lamc / ((r - 2) * lamc * deriv (secular g H) lamc) * (B / A)) := by
    field_simp
  rw [hD]
  have := hpos'.ne'
  field_simp

/-! ### Shape of the transformed secular functions -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `x ↦ x ^ p` is convex on `(0, ∞)` for `p ≤ 0`. -/
theorem convexOn_rpow_Ioi_of_nonpos {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Ioi 0) fun x : ℝ => x ^ p := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
    (fun x hx => (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx))).continuousWithinAt)
    ?_ ?_
  · rw [interior_Ioi]
    exact fun x hx =>
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi, Real.deriv_rpow_const']
    intro x hx y _ hxy
    exact mul_le_mul_of_nonpos_left (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)) hp

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The regularization target `t ↦ (t / σ) ^ γ` on `(0, ∞)`: concave and monotone for
`γ ∈ [0, 1]`, convex and antitone for `γ ≤ 0`. -/
theorem regTarget_shape {σ γ : ℝ} (hσ : 0 < σ) :
    (0 ≤ γ → γ ≤ 1 → ConcaveOn ℝ (Ioi 0) (fun t : ℝ => (t / σ) ^ γ) ∧
      MonotoneOn (fun t : ℝ => (t / σ) ^ γ) (Ioi 0)) ∧
    (γ ≤ 0 → ConvexOn ℝ (Ioi 0) (fun t : ℝ => (t / σ) ^ γ) ∧
      AntitoneOn (fun t : ℝ => (t / σ) ^ γ) (Ioi 0)) := by
  have heq : EqOn (fun t : ℝ => (σ ^ γ)⁻¹ • t ^ γ) (fun t : ℝ => (t / σ) ^ γ) (Ioi 0) :=
    fun t ht => by
      simp only [smul_eq_mul]
      rw [Real.div_rpow (le_of_lt ht) hσ.le, div_eq_inv_mul]
  have hc : 0 ≤ (σ ^ γ)⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hσ.le _)
  refine ⟨fun h0 h1 => ⟨(((Real.concaveOn_rpow h0 h1).subset Ioi_subset_Ici_self
      (convex_Ioi 0)).smul hc).congr heq, fun x hx y _ hxy => ?_⟩, fun h0 =>
    ⟨((convexOn_rpow_Ioi_of_nonpos h0).smul hc).congr heq, fun x hx y _ hxy => ?_⟩⟩
  · exact Real.rpow_le_rpow (div_pos hx hσ).le (div_le_div_of_nonneg_right hxy hσ.le) h0
  · exact Real.rpow_le_rpow_of_nonpos (div_pos hx hσ) (div_le_div_of_nonneg_right hxy hσ.le) h0

/-- **Shape of the transformed trust-region secular function** for `β ∈ [-1/2, 0)`, on `λ > -λ₁`:
`θ_β = π ^ β - Δ ^ (2 β)` is concave and strictly increasing with positive derivative. -/
theorem trSecular_shape (hg : g ≠ 0) (Δ : ℝ) {β : ℝ} (hβ : β ∈ Ico (-1 / 2) 0) :
    ConcaveOn ℝ (Ioi (-leftmost hH)) (trSecular g H Δ β) ∧
      StrictMonoOn (trSecular g H Δ β) (Ioi (-leftmost hH)) ∧
      ∀ x ∈ Ioi (-leftmost hH), 0 < deriv (trSecular g H Δ β) x := by
  obtain ⟨hm, hc, -⟩ := (secular_shape (hH := hH) hg β).2.2.2.2.2.2 hβ
  refine ⟨hc.sub (convexOn_const _ (convex_Ioi _)), fun x hx y hy hxy => ?_, fun x hx => ?_⟩
  · simp only [trSecular]
    linarith [hm hx hy hxy]
  · rw [(hasDerivAt_trSecular hg hx Δ β).deriv]
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos hβ.2 (Real.rpow_pos_of_pos (secular_pos hg hx) _))
      (deriv_secular_neg hg hx)

/-- **Shape of the transformed regularization secular function** (book §8.2.2), on
`λ > λₛ = max 0 (-λ₁)`, for `σ > 0`, `r > 2`: `θ_β = π ^ β - (λ/σ) ^ (2β/(r-2))` is convex and
strictly decreasing with negative derivative for `β ∈ (0, (r-2)/2]`, and concave and strictly
increasing with positive derivative for `β ∈ [-1/2, 0)`. -/
theorem regSecular_shape (hg : g ≠ 0) {σ r β : ℝ} (hσ : 0 < σ) (hr : 2 < r) :
    (β ∈ Ioc 0 ((r - 2) / 2) →
      ConvexOn ℝ (Ioi (shiftThreshold hH)) (regSecular g H σ r β) ∧
      StrictAntiOn (regSecular g H σ r β) (Ioi (shiftThreshold hH)) ∧
      ∀ x ∈ Ioi (shiftThreshold hH), deriv (regSecular g H σ r β) x < 0) ∧
    (β ∈ Ico (-1 / 2) 0 →
      ConcaveOn ℝ (Ioi (shiftThreshold hH)) (regSecular g H σ r β) ∧
      StrictMonoOn (regSecular g H σ r β) (Ioi (shiftThreshold hH)) ∧
      ∀ x ∈ Ioi (shiftThreshold hH), 0 < deriv (regSecular g H σ r β) x) := by
  have hr2 : 0 < r - 2 := by linarith
  have hS1 : Ioi (shiftThreshold hH) ⊆ Ioi (-leftmost hH) := Ioi_shiftThreshold_subset
  have hS0 : Ioi (shiftThreshold hH) ⊆ Ioi 0 := Ioi_subset_Ioi shiftThreshold_nonneg
  have hconv : Convex ℝ (Ioi (shiftThreshold hH)) := convex_Ioi _
  have hderiv : ∀ x ∈ Ioi (shiftThreshold hH), deriv (regSecular g H σ r β) x =
      β * secular g H x ^ (β - 1) * deriv (secular g H) x -
        2 * β / (r - 2) * (x / σ) ^ (2 * β / (r - 2) - 1) / σ := fun x hx =>
    (hasDerivAt_regSecular hg hσ (hS1 hx) (hS0 hx)).deriv
  have hφ : ∀ x ∈ Ioi (shiftThreshold hH), 0 < (x / σ) ^ (2 * β / (r - 2) - 1) / σ :=
    fun x hx => div_pos (Real.rpow_pos_of_pos (div_pos (hS0 hx) hσ) _) hσ
  have hψ : ∀ x ∈ Ioi (shiftThreshold hH), 0 < secular g H x ^ (β - 1) :=
    fun x hx => Real.rpow_pos_of_pos (secular_pos hg (hS1 hx)) _
  constructor
  · intro hβ
    have hγ0 : 0 ≤ 2 * β / (r - 2) := div_nonneg (by linarith [hβ.1]) hr2.le
    have hγ1 : 2 * β / (r - 2) ≤ 1 := (div_le_one hr2).2 (by linarith [hβ.2])
    obtain ⟨hφc, hφm⟩ := (regTarget_shape (γ := 2 * β / (r - 2)) hσ).1 hγ0 hγ1
    obtain ⟨hm, hc, -⟩ := (secular_shape (hH := hH) hg β).2.2.2.2.2.1 hβ.1
    refine ⟨(hc.convexOn.subset hS1 hconv).sub (hφc.subset hS0 hconv),
      fun x hx y hy hxy => ?_, fun x hx => ?_⟩
    · simp only [regSecular]
      linarith [hm (hS1 hx) (hS1 hy) hxy, hφm (hS0 hx) (hS0 hy) hxy.le]
    · rw [hderiv x hx]
      have h1 : β * secular g H x ^ (β - 1) * deriv (secular g H) x < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hβ.1 (hψ x hx)) (deriv_secular_neg hg (hS1 hx))
      have h2 : 0 < 2 * β / (r - 2) * ((x / σ) ^ (2 * β / (r - 2) - 1) / σ) :=
        mul_pos (div_pos (by linarith [hβ.1]) hr2) (hφ x hx)
      rw [mul_div_assoc]
      linarith
  · intro hβ
    have hγ0 : 2 * β / (r - 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hβ.2]) hr2.le
    obtain ⟨hφc, hφm⟩ := (regTarget_shape (γ := 2 * β / (r - 2)) hσ).2 hγ0
    obtain ⟨hm, hc, -⟩ := (secular_shape (hH := hH) hg β).2.2.2.2.2.2 hβ
    refine ⟨(hc.subset hS1 hconv).sub (hφc.subset hS0 hconv),
      fun x hx y hy hxy => ?_, fun x hx => ?_⟩
    · simp only [regSecular]
      linarith [hm (hS1 hx) (hS1 hy) hxy, hφm (hS0 hx) (hS0 hy) hxy.le]
    · rw [hderiv x hx]
      have h1 : 0 < β * secular g H x ^ (β - 1) * deriv (secular g H) x :=
        mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hβ.2 (hψ x hx))
          (deriv_secular_neg hg (hS1 hx))
      have h2 : 2 * β / (r - 2) * ((x / σ) ^ (2 * β / (r - 2) - 1) / σ) < 0 :=
        mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith [hβ.2]) hr2) (hφ x hx)
      rw [mul_div_assoc]
      linarith

/-! ### Newton corrections stay on the correct side -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A Newton correction `-θ x / θ' x` on a convex nonincreasing function with `θ' x < 0` does not
pass a root `r`, and it is nonnegative from `x ≤ r`. -/
theorem newtonCorrection_mem_of_convexOn {θ : ℝ → ℝ} {S : Set ℝ} {r x : ℝ}
    (hc : ConvexOn ℝ S θ) (hm : AntitoneOn θ S) (hr : r ∈ S) (hθr : θ r = 0) (hx : x ∈ S)
    (hd : HasDerivAt θ (deriv θ x) x) (hneg : deriv θ x < 0) :
    x + -θ x / deriv θ x ≤ r ∧ (x ≤ r → 0 ≤ -θ x / deriv θ x) := by
  refine ⟨?_, fun hxr => ?_⟩
  · have := Newton.scalarStep_le_of_convexOn hc hr hθr hx hd.hasDerivWithinAt hneg
    rwa [Newton.scalarStep, sub_eq_add_neg, ← neg_div] at this
  · have : 0 ≤ θ x := hθr ▸ hm hx hr hxr
    exact div_nonneg_of_nonpos (neg_nonpos.2 this) hneg.le

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The concave mirror of `newtonCorrection_mem_of_convexOn`. -/
theorem newtonCorrection_mem_of_concaveOn {θ : ℝ → ℝ} {S : Set ℝ} {r x : ℝ}
    (hc : ConcaveOn ℝ S θ) (hm : MonotoneOn θ S) (hr : r ∈ S) (hθr : θ r = 0) (hx : x ∈ S)
    (hd : HasDerivAt θ (deriv θ x) x) (hpos : 0 < deriv θ x) :
    x + -θ x / deriv θ x ≤ r ∧ (x ≤ r → 0 ≤ -θ x / deriv θ x) := by
  refine ⟨?_, fun hxr => ?_⟩
  · have := Newton.scalarStep_le_of_concaveOn hc hr hθr hx hd.hasDerivWithinAt hpos
    rwa [Newton.scalarStep, sub_eq_add_neg, ← neg_div] at this
  · have : θ x ≤ 0 := hθr ▸ hm hx hr hxr
    exact div_nonneg (neg_nonneg.2 this) hpos.le

/-- **Trust-region Newton corrections** (book §8.2.2 and §8.3.2, easy case). Let `Δ > 0` and let
`λ* > -λ₁` solve `π(λ*) = Δ²`. From every `λc > -λ₁`, `λc + δᴺ(λc) ≤ λ*` (from `𝓖 = (λ*, ∞)`
the correction overshoots to `≤ λ*`), and from `λc ≤ λ*` (in `𝓛`) the correction is
nonnegative, so `λc + δᴺ(λc) ∈ [λc, λ*]`. -/
theorem trNewtonCorrection_mem {Δ lamStar lamc : ℝ} (hΔ : 0 < Δ)
    (hstar : -leftmost hH < lamStar) (hroot : secular g H lamStar = Δ ^ 2)
    (hc : -leftmost hH < lamc) :
    lamc + trNewtonCorrection g H Δ lamc ≤ lamStar ∧
      (lamc ≤ lamStar → lamc ≤ lamc + trNewtonCorrection g H Δ lamc) := by
  have hg : g ≠ 0 := ne_zero_of_secular_pos (lam := lamStar) (by rw [hroot]; positivity)
  obtain ⟨hcv, hm, hd⟩ := trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)
  have hθr : trSecular g H Δ (-1 / 2) lamStar = 0 := by
    rw [trSecular, hroot, ← Real.rpow_two, ← Real.rpow_mul hΔ.le, sub_self]
  have h := newtonCorrection_mem_of_concaveOn hcv hm.monotoneOn hstar hθr hc
    ((hasDerivAt_trSecular hg hc Δ _).differentiableAt.hasDerivAt) (hd lamc hc)
  rw [← trNewtonCorrection_eq hg hc hΔ] at h
  exact ⟨h.1, fun hle => le_add_of_nonneg_right (h.2 hle)⟩

omit [FiniteDimensional ℝ E] in
/-- The root of the regularization secular equation is a root of every `θ_β`. -/
theorem regSecular_root {σ r β lamStar : ℝ} (hσ : 0 < σ) (hpos : 0 < lamStar)
    (hroot : secular g H lamStar = (lamStar / σ) ^ (2 / (r - 2))) :
    regSecular g H σ r β lamStar = 0 := by
  rw [regSecular, hroot, ← Real.rpow_mul (div_pos hpos hσ).le, sub_eq_zero]
  congr 1
  ring

/-- **Regularization Newton corrections** (book §8.2.2 and §8.3.1, easy case). Let `σ > 0`,
`r > 2`, `β ∈ [-1/2, 0) ∪ (0, (r-2)/2]` and let `λ* > λₛ` solve the secular equation
`π(λ*) = (λ*/σ) ^ (2/(r-2))` (8.2.42). From every `λc > λₛ`, `λc + δᴺ(λc, β) ≤ λ*`, and from
`λc ≤ λ*` the correction is nonnegative. (`β = 0` is excluded since `θ₀ ≡ 0`.) -/
theorem regNewtonCorrection_mem {σ r β lamStar lamc : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hβ : β ∈ Ico (-1 / 2) 0 ∪ Ioc 0 ((r - 2) / 2)) (hstar : shiftThreshold hH < lamStar)
    (hroot : secular g H lamStar = (lamStar / σ) ^ (2 / (r - 2)))
    (hc : shiftThreshold hH < lamc) :
    lamc + regNewtonCorrection g H σ r β lamc ≤ lamStar ∧
      (lamc ≤ lamStar → lamc ≤ lamc + regNewtonCorrection g H σ r β lamc) := by
  have h0 : ∀ {x}, shiftThreshold hH < x → 0 < x := fun h =>
    lt_of_le_of_lt shiftThreshold_nonneg h
  have h1 : ∀ {x}, shiftThreshold hH < x → -leftmost hH < x := fun h =>
    lt_of_le_of_lt neg_leftmost_le_shiftThreshold h
  have hg : g ≠ 0 := ne_zero_of_secular_pos
    (hroot ▸ Real.rpow_pos_of_pos (div_pos (h0 hstar) hσ) _)
  have hθr := regSecular_root (β := β) (g := g) (H := H) hσ (h0 hstar) hroot
  have hd := (hasDerivAt_regSecular (β := β) (r := r) hg hσ (h1 hc) (h0 hc)).differentiableAt
    |>.hasDerivAt
  have h : lamc + regNewtonCorrection g H σ r β lamc ≤ lamStar ∧
      (lamc ≤ lamStar → 0 ≤ regNewtonCorrection g H σ r β lamc) := by
    rcases hβ with hβ | hβ
    · obtain ⟨hcv, hm, hd'⟩ := (regSecular_shape (hH := hH) hg hσ hr).2 hβ
      exact newtonCorrection_mem_of_concaveOn hcv hm.monotoneOn hstar hθr hc hd (hd' lamc hc)
    · obtain ⟨hcv, hm, hd'⟩ := (regSecular_shape (hH := hH) hg hσ hr).1 hβ
      exact newtonCorrection_mem_of_convexOn hcv hm.antitoneOn hstar hθr hc hd (hd' lamc hc)
  exact ⟨h.1, fun hle => le_add_of_nonneg_right (h.2 hle)⟩

/-! ### Convergence of Newton-type iterations -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Iterations at least as long as Newton's** on a convex decreasing function (the convergence
argument behind Algorithms 8.3.1/8.3.2). Let `θ` satisfy the hypotheses of Lemma B.8.1 on
`(a, ∞)` with root `r` (`Newton.IsConvexAntiRoot`) and `θ'` continuous at `r`. If
`x 0 ∈ (a, r]` and `N(x j) ≤ x (j+1) ≤ r` for the Newton step `N`, then `x` increases to `r`,
`r - x (j+1) ≤ γ (r - x j)` with `γ = 1 - θ'(r)/θ'(x 0) ∈ [0, 1)`, and the convergence is
`Q`-superlinear. -/
theorem tendsto_of_scalarStep_le {θ θ' : ℝ → ℝ} {a r : ℝ}
    (h : Newton.IsConvexAntiRoot θ θ' (Ioi a) r) (hcont : ContinuousWithinAt θ' (Ioi a) r)
    {x : ℕ → ℝ} (hx0 : x 0 ∈ Ioc a r)
    (hstep : ∀ j, x j ∈ Ioi a → Newton.scalarStep θ θ' (x j) ≤ x (j + 1))
    (hle : ∀ j, x (j + 1) ≤ r) :
    Monotone x ∧ Tendsto x atTop (𝓝 r) ∧ 1 - θ' r / θ' (x 0) ∈ Ico 0 1 ∧
      (∀ j, r - x (j + 1) ≤ (1 - θ' r / θ' (x 0)) * (r - x j)) ∧
      ConvergesSuperlinearly x r := by
  have hmem : ∀ j, x j ∈ Icc (x 0) r := by
    intro j
    induction j with
    | zero => exact ⟨le_rfl, hx0.2⟩
    | succ j ih =>
      have hS : x j ∈ Ioi a := lt_of_lt_of_le hx0.1 ih.1
      exact ⟨ih.1.trans (((h.scalarStep_mem_Icc_and_sub_le hS ih.2).1.1).trans (hstep j hS)),
        hle j⟩
  have hS : ∀ j, x j ∈ Ioi a := fun j => lt_of_lt_of_le hx0.1 (hmem j).1
  have har : a < r := hx0.1.trans_le hx0.2
  have hneg : θ' r < 0 :=
    h.deriv_root_neg (x := (a + r) / 2) (show a < (a + r) / 2 by linarith) (by linarith)
  have hbound : ∀ j, r - x (j + 1) ≤ (1 - θ' r / θ' (x j)) * (r - x j) := fun j =>
    (sub_le_sub_left (hstep j (hS j)) r).trans
      (h.scalarStep_mem_Icc_and_sub_le (hS j) (hmem j).2).2
  have hd0 : ∀ j, θ' (x 0) ≤ θ' (x j) := fun j => h.monotoneOn_deriv (hS 0) (hS j) (hmem j).1
  have hdr : ∀ j, θ' (x j) ≤ θ' r := fun j => h.monotoneOn_deriv (hS j) h.mem (hmem j).2
  have hlin : ∀ j, r - x (j + 1) ≤ (1 - θ' r / θ' (x 0)) * (r - x j) := fun j =>
    (hbound j).trans (mul_le_mul_of_nonneg_right
      (Newton.one_sub_div_le_one_sub_div (hd0 j) (hdr j) hneg) (sub_nonneg.2 (hmem j).2))
  have hγ' : 1 - θ' r / θ' (x 0) ∈ Ico 0 1 :=
    Newton.one_sub_div_mem_Ico (hdr 0) hneg
  have hpow : ∀ j, r - x j ≤ (1 - θ' r / θ' (x 0)) ^ j * (r - x 0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, mul_comm _ (1 - θ' r / θ' (x 0)), mul_assoc]
      exact (hlin j).trans (mul_le_mul_of_nonneg_left ih hγ'.1)
  have h0 : Tendsto (fun j => r - x j) atTop (𝓝 0) :=
    squeeze_zero (fun j => sub_nonneg.2 (hmem j).2) hpow (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ'.1 hγ'.2).mul_const (r - x 0))
  have hlim : Tendsto x atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).sub h0
  refine ⟨monotone_nat_of_le_succ fun j =>
      ((h.scalarStep_mem_Icc_and_sub_le (hS j) (hmem j).2).1.1).trans (hstep j (hS j)),
    hlim, hγ', hlin, ?_⟩
  refine Newton.convergesSuperlinearly_of_le_one_sub_div (d := fun k => θ' (x k)) hneg.ne
    (hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hS⟩))
    (fun _ => le_rfl) hdr fun k => ?_
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hle k)), abs_sub_comm,
    abs_of_nonneg (sub_nonneg.2 (hmem k).2)]
  exact hbound k

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The concave increasing mirror of `tendsto_of_scalarStep_le`. -/
theorem tendsto_of_scalarStep_le_of_concaveOn {θ θ' : ℝ → ℝ} {a r : ℝ}
    (hc : ConcaveOn ℝ (Ioi a) θ) (hm : StrictMonoOn θ (Ioi a))
    (hd : ∀ x ∈ Ioi a, HasDerivWithinAt θ (θ' x) (Ioi a) x) (hθr : θ r = 0) (hθ'r : θ' r ≠ 0)
    (hcont : ContinuousWithinAt θ' (Ioi a) r) {x : ℕ → ℝ} (hx0 : x 0 ∈ Ioc a r)
    (hstep : ∀ j, x j ∈ Ioi a → Newton.scalarStep θ θ' (x j) ≤ x (j + 1))
    (hle : ∀ j, x (j + 1) ≤ r) :
    Monotone x ∧ Tendsto x atTop (𝓝 r) ∧ 1 - θ' r / θ' (x 0) ∈ Ico 0 1 ∧
      (∀ j, r - x (j + 1) ≤ (1 - θ' r / θ' (x 0)) * (r - x j)) ∧
      ConvergesSuperlinearly x r := by
  have h := Newton.isConvexAntiRoot_neg hc hm hd (hx0.1.trans_le hx0.2) hθr hθ'r
  have := tendsto_of_scalarStep_le h hcont.neg hx0
    (fun j hj => by rw [Newton.scalarStep_neg]; exact hstep j hj) hle
  simpa only [neg_div_neg_eq] using this

/-- **Convergence of trust-region Newton-type iterations** (book §8.3.2, Algorithm 8.3.2, easy
case). Let `Δ > 0`, `λ* > -λ₁` with `π(λ*) = Δ²`, and let `λ : ℕ → ℝ` take steps at least as long
as the Newton correction (8.2.24) without passing `λ*`: `λ 0 ∈ (-λ₁, λ*]` and
`λ j + δᴺ(λ j) ≤ λ (j + 1) ≤ λ*`. Then `λ` increases to `λ*`, globally `Q`-linearly with factor
`γ = 1 - θ'(λ*)/θ'(λ 0) ∈ [0, 1)` for `θ = trSecular g H Δ (-1/2)`, and `Q`-superlinearly. -/
theorem tendsto_of_trNewtonCorrection_le {Δ lamStar : ℝ} (hΔ : 0 < Δ)
    (hstar : -leftmost hH < lamStar) (hroot : secular g H lamStar = Δ ^ 2) {x : ℕ → ℝ}
    (hx0 : x 0 ∈ Ioc (-leftmost hH) lamStar)
    (hstep : ∀ j, x j + trNewtonCorrection g H Δ (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar) :
    Monotone x ∧ Tendsto x atTop (𝓝 lamStar) ∧
      1 - deriv (trSecular g H Δ (-1 / 2)) lamStar / deriv (trSecular g H Δ (-1 / 2)) (x 0) ∈
        Ico 0 1 ∧
      (∀ j, lamStar - x (j + 1) ≤ (1 - deriv (trSecular g H Δ (-1 / 2)) lamStar /
        deriv (trSecular g H Δ (-1 / 2)) (x 0)) * (lamStar - x j)) ∧
      ConvergesSuperlinearly x lamStar := by
  have hg : g ≠ 0 := ne_zero_of_secular_pos (lam := lamStar) (by rw [hroot]; positivity)
  obtain ⟨hcv, hm, hd⟩ := trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)
  have hθr : trSecular g H Δ (-1 / 2) lamStar = 0 := by
    rw [trSecular, hroot, ← Real.rpow_two, ← Real.rpow_mul hΔ.le, sub_self]
  have hsmooth : ContDiffOn ℝ 2 (trSecular g H Δ (-1 / 2)) (Ioi (-leftmost hH)) :=
    (contDiffOn_secular_rpow hg _).sub contDiffOn_const
  refine tendsto_of_scalarStep_le_of_concaveOn hcv hm
    (fun y hy => (hasDerivAt_trSecular hg hy Δ _).differentiableAt.hasDerivAt.hasDerivWithinAt)
    hθr (hd lamStar hstar).ne'
    ((hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).continuousWithinAt hstar)
    hx0 (fun j hj => ?_) fun j => (hstep j).2
  rw [Newton.scalarStep, sub_eq_add_neg, ← neg_div, ← trNewtonCorrection_eq hg hj hΔ]
  exact (hstep j).1

/-- **Convergence of regularization Newton-type iterations** (book §8.2.2 and §8.3.1,
Algorithm 8.3.1, easy case; Lemma B.8.1). Let `σ > 0`, `r > 2`,
`β ∈ [-1/2, 0) ∪ (0, (r-2)/2]`, `λ* > λₛ` with `π(λ*) = (λ*/σ) ^ (2/(r-2))`, and let
`λ 0 ∈ (λₛ, λ*]`, `λ j + δᴺ(λ j, β) ≤ λ (j + 1) ≤ λ*` (e.g. the plain Newton iteration, the
`β`-maximizing iteration (8.2.26), or Algorithm 8.3.1, which takes the largest of several
corrections). Then `λ` increases to `λ*`, globally `Q`-linearly with factor
`γ = 1 - θ_β'(λ*)/θ_β'(λ 0) ∈ [0, 1)`, and `Q`-superlinearly. -/
theorem tendsto_of_regNewtonCorrection_le {σ r β lamStar : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hβ : β ∈ Ico (-1 / 2) 0 ∪ Ioc 0 ((r - 2) / 2)) (hstar : shiftThreshold hH < lamStar)
    (hroot : secular g H lamStar = (lamStar / σ) ^ (2 / (r - 2))) {x : ℕ → ℝ}
    (hx0 : x 0 ∈ Ioc (shiftThreshold hH) lamStar)
    (hstep : ∀ j, x j + regNewtonCorrection g H σ r β (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar) :
    Monotone x ∧ Tendsto x atTop (𝓝 lamStar) ∧
      1 - deriv (regSecular g H σ r β) lamStar / deriv (regSecular g H σ r β) (x 0) ∈ Ico 0 1 ∧
      (∀ j, lamStar - x (j + 1) ≤ (1 - deriv (regSecular g H σ r β) lamStar /
        deriv (regSecular g H σ r β) (x 0)) * (lamStar - x j)) ∧
      ConvergesSuperlinearly x lamStar := by
  have h0 : ∀ {x}, shiftThreshold hH < x → 0 < x := fun h =>
    lt_of_le_of_lt shiftThreshold_nonneg h
  have h1 : ∀ {x}, shiftThreshold hH < x → -leftmost hH < x := fun h =>
    lt_of_le_of_lt neg_leftmost_le_shiftThreshold h
  have hg : g ≠ 0 := ne_zero_of_secular_pos
    (hroot ▸ Real.rpow_pos_of_pos (div_pos (h0 hstar) hσ) _)
  have hθr := regSecular_root (β := β) (g := g) (H := H) hσ (h0 hstar) hroot
  have hderiv : ∀ y ∈ Ioi (shiftThreshold hH),
      HasDerivWithinAt (regSecular g H σ r β) (deriv (regSecular g H σ r β) y)
        (Ioi (shiftThreshold hH)) y := fun y hy =>
    (hasDerivAt_regSecular hg hσ (h1 hy) (h0 hy)).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hsmooth : ContDiffOn ℝ 2 (regSecular g H σ r β) (Ioi (shiftThreshold hH)) := by
    refine ((contDiffOn_secular_rpow hg β).mono Ioi_shiftThreshold_subset).sub fun y hy => ?_
    exact ((contDiffAt_id.div_const σ).rpow_const_of_ne
      (div_pos (h0 hy) hσ).ne').contDiffWithinAt
  have hcont : ContinuousWithinAt (deriv (regSecular g H σ r β)) (Ioi (shiftThreshold hH))
      lamStar :=
    (hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).continuousWithinAt hstar
  have hstep' : ∀ j, x j ∈ Ioi (shiftThreshold hH) →
      Newton.scalarStep (regSecular g H σ r β) (deriv (regSecular g H σ r β)) (x j) ≤
        x (j + 1) := fun j _ => by
    rw [Newton.scalarStep, sub_eq_add_neg, ← neg_div]
    exact (hstep j).1
  rcases hβ with hβ | hβ
  · obtain ⟨hcv, hm, hd⟩ := (regSecular_shape (hH := hH) hg hσ hr).2 hβ
    exact tendsto_of_scalarStep_le_of_concaveOn hcv hm hderiv hθr (hd lamStar hstar).ne' hcont
      hx0 hstep' fun j => (hstep j).2
  · obtain ⟨hcv, hm, hd⟩ := (regSecular_shape (hH := hH) hg hσ hr).1 hβ
    exact tendsto_of_scalarStep_le ⟨hcv, hm, hderiv, hstar, hθr, (hd lamStar hstar).ne⟩ hcont
      hx0 hstep' fun j => (hstep j).2

/-! ### Taylor corrections -/

omit [FiniteDimensional ℝ E] in
theorem secularTaylor_zero (g : E) (H : E →L[ℝ] E) (k : ℕ) (lamc : ℝ) :
    secularTaylor g H k lamc 0 = secular g H lamc := by
  simp [secularTaylor, Finset.sum_range_succ']

omit [FiniteDimensional ℝ E] in
theorem continuous_secularTaylor (g : E) (H : E →L[ℝ] E) (k : ℕ) (lamc : ℝ) :
    Continuous (secularTaylor g H k lamc) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow j)

/-- **Odd-order Taylor polynomials underestimate `π` to the right** (Theorem 8.2.2): for
`λc > -λ₁`, odd `k` and `δ > 0`, `tₖ(δ) ≤ π(λc + δ)`. -/
theorem secularTaylor_le_secular {lamc δ : ℝ} {k : ℕ} (hlam : -leftmost hH < lamc) (hk : Odd k)
    (hδ : 0 < δ) : secularTaylor g H k lamc δ ≤ secular g H (lamc + δ) :=
  ((secular_taylor_bounds hlam k).1 δ hδ).2 hk

/-- **Even-order Taylor polynomials overestimate `π` to the right** (Theorem 8.2.2): for
`λc > -λ₁`, even `k` and `δ > 0`, `π(λc + δ) ≤ tₖ(δ)`. -/
theorem secular_le_secularTaylor {lamc δ : ℝ} {k : ℕ} (hlam : -leftmost hH < lamc) (hk : Even k)
    (hδ : 0 < δ) : secular g H (lamc + δ) ≤ secularTaylor g H k lamc δ :=
  ((secular_taylor_bounds hlam k).1 δ hδ).1 hk

/-- Standing hypotheses for the Taylor iterations: `g ≠ 0`, a target `τ` continuous and
monotone on `(a, ∞) ⊆ (-λ₁, ∞)`, and a root `λ* > a` of `π = τ` (Lemma 8.2.1 gives one when
`π > τ` near `a`). -/
structure IsSecularTarget (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (g : E) (τ : ℝ → ℝ)
    (a lamStar : ℝ) : Prop where
  ne_zero : g ≠ 0
  le_left : -leftmost hH ≤ a
  continuousOn : ContinuousOn τ (Ioi a)
  monotoneOn : MonotoneOn τ (Ioi a)
  lt_root : a < lamStar
  root : secular g H lamStar = τ lamStar

namespace IsSecularTarget

variable {τ : ℝ → ℝ} {a lamStar : ℝ} (h : IsSecularTarget hH g τ a lamStar)
include h

theorem neg_leftmost_lt {x : ℝ} (hx : a < x) : -leftmost hH < x := h.le_left.trans_lt hx

/-- `π ≥ τ` on `(a, λ*]` (the set `𝓛`). -/
theorem tau_le_secular {x : ℝ} (hx : x ∈ Ioc a lamStar) : τ x ≤ secular g H x := by
  have hm := (secular_shape (hH := hH) h.ne_zero 0).2.2.1
  calc τ x ≤ τ lamStar := h.monotoneOn hx.1 h.lt_root hx.2
    _ = secular g H lamStar := h.root.symm
    _ ≤ secular g H x := hm.antitoneOn (h.neg_leftmost_lt hx.1) (h.neg_leftmost_lt h.lt_root) hx.2

/-- Every root of `tₖ(δ) = τ(λc + δ)` for odd `k` and `λc ∈ (a, λ*]` satisfies `λc + δ ≤ λ*`:
for `λc + δ > λ*`, `tₖ(δ) ≤ π(λc + δ) < π(λ*) = τ(λ*) ≤ τ(λc + δ)`. -/
theorem taylor_root_le {k : ℕ} (hk : Odd k) {lamc δ : ℝ} (hc : lamc ∈ Ioc a lamStar)
    (hδ : secularTaylor g H k lamc δ = τ (lamc + δ)) : δ ≤ lamStar - lamc := by
  by_contra hlt
  push Not at hlt
  have hδ0 : 0 < δ := by linarith [hc.2]
  have hlam := h.neg_leftmost_lt hc.1
  have h1 := secularTaylor_le_secular (g := g) hlam hk hδ0
  have h2 := (secular_shape (hH := hH) h.ne_zero 0).2.2.1 (h.neg_leftmost_lt h.lt_root)
    (show -leftmost hH < lamc + δ by linarith) (show lamStar < lamc + δ by linarith)
  have h3 := h.monotoneOn h.lt_root (show a < lamc + δ by linarith [hc.1])
    (show lamStar ≤ lamc + δ by linarith)
  linarith [h.root]

/-- Odd-order Taylor equations have a root in `[η, λ* - λc]` as soon as `tₖ(η) ≥ τ(λc + η)` for
some `0 ≤ η ≤ λ* - λc` (intermediate value theorem; at `η = 0` this holds on `𝓛`). -/
theorem exists_taylor_root {k : ℕ} (hk : Odd k) {lamc η : ℝ} (hc : lamc ∈ Ioc a lamStar)
    (hη0 : 0 ≤ η) (hη : η ≤ lamStar - lamc)
    (hfη : τ (lamc + η) ≤ secularTaylor g H k lamc η) :
    ∃ δ ∈ Icc η (lamStar - lamc), secularTaylor g H k lamc δ = τ (lamc + δ) := by
  have hlam := h.neg_leftmost_lt hc.1
  -- the value at the right end is `≤ 0`
  have hend : secularTaylor g H k lamc (lamStar - lamc) ≤ τ (lamc + (lamStar - lamc)) := by
    have e : lamc + (lamStar - lamc) = lamStar := by ring
    rw [e, ← h.root]
    rcases (sub_nonneg.2 hc.2).lt_or_eq with hpos | hzero
    · have := secularTaylor_le_secular (g := g) hlam hk hpos
      rw [e] at this
      exact this
    · rw [← hzero, secularTaylor_zero, show lamc = lamStar by linarith [hzero]]
  have hcont : ContinuousOn (fun δ => secularTaylor g H k lamc δ - τ (lamc + δ))
      (Icc η (lamStar - lamc)) := by
    refine (continuous_secularTaylor g H k lamc).continuousOn.sub ?_
    refine h.continuousOn.comp (continuous_const.add continuous_id).continuousOn fun δ hδ => ?_
    change a < lamc + δ
    linarith [hc.1, hδ.1]
  obtain ⟨δ, hδ, hfδ⟩ := intermediate_value_Icc' hη hcont
    (show (0 : ℝ) ∈ Icc _ _ from ⟨sub_nonpos.2 hend, sub_nonneg.2 hfη⟩)
  exact ⟨δ, hδ, sub_eq_zero.1 hfδ⟩

/-- **Odd-order Taylor corrections underestimate `λ*`** (book §8.2.1, Theorem 8.2.2). For odd `k`
and `λc ∈ (a, λ*]`, the roots of (8.2.15) form a nonempty set bounded above, and its rightmost
point `δₖᵀ(λc)` satisfies `λc ≤ λc + δₖᵀ(λc) ≤ λ*`. -/
theorem taylorCorrection_mem {k : ℕ} (hk : Odd k) {lamc : ℝ} (hc : lamc ∈ Ioc a lamStar) :
    {δ | secularTaylor g H k lamc δ = τ (lamc + δ)}.Nonempty ∧
      BddAbove {δ | secularTaylor g H k lamc δ = τ (lamc + δ)} ∧
      lamc ≤ lamc + taylorCorrection g H τ k lamc ∧
      lamc + taylorCorrection g H τ k lamc ≤ lamStar := by
  obtain ⟨δ, hδ, hroot⟩ := h.exists_taylor_root hk hc le_rfl (sub_nonneg.2 hc.2)
    (by rw [add_zero, secularTaylor_zero]; exact h.tau_le_secular hc)
  have hbdd : BddAbove {δ | secularTaylor g H k lamc δ = τ (lamc + δ)} :=
    ⟨lamStar - lamc, fun δ hδ => h.taylor_root_le hk hc hδ⟩
  refine ⟨⟨δ, hroot⟩, hbdd, ?_, ?_⟩
  · have : δ ≤ taylorCorrection g H τ k lamc := le_csSup hbdd hroot
    linarith [hδ.1]
  · have : taylorCorrection g H τ k lamc ≤ lamStar - lamc :=
      csSup_le ⟨δ, hroot⟩ fun δ hδ => h.taylor_root_le hk hc hδ
    linarith

/-- The rightmost root is attained: `δₖᵀ(λc)` is the greatest root of (8.2.15) for odd `k` and
`λc ∈ (a, λ*]` (the root set is closed near its supremum, where `τ` is continuous). -/
theorem isGreatest_taylorCorrection {k : ℕ} (hk : Odd k) {lamc : ℝ}
    (hc : lamc ∈ Ioc a lamStar) :
    IsGreatest {δ | secularTaylor g H k lamc δ = τ (lamc + δ)} (taylorCorrection g H τ k lamc) := by
  obtain ⟨hne, hbdd, hlo, -⟩ := h.taylorCorrection_mem hk hc
  refine ⟨?_, fun δ hδ => le_csSup hbdd hδ⟩
  set T := taylorCorrection g H τ k lamc with hT
  have haT : a < lamc + T := by linarith [hc.1]
  -- `f = tₖ - τ(λc + ·)` is continuous at `T`
  have hf : ContinuousAt (fun δ => secularTaylor g H k lamc δ - τ (lamc + δ)) T :=
    (continuous_secularTaylor g H k lamc).continuousAt.sub
      ((h.continuousOn.continuousAt (Ioi_mem_nhds haT)).comp
        (continuous_const.add continuous_id).continuousAt)
  by_contra hT0
  have hev := hf.eventually_ne (sub_ne_zero.2 hT0)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨δ, hδ, hlt⟩ := exists_lt_of_lt_csSup hne (show T - η < T by linarith)
  have hδT : δ ≤ T := le_csSup hbdd hδ
  exact hball (show dist δ T < η by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    (sub_eq_zero.2 hδ)

/-- The Taylor correction solves (8.2.15): `tₖ(δₖᵀ(λc)) = τ(λc + δₖᵀ(λc))`. -/
theorem secularTaylor_taylorCorrection {k : ℕ} (hk : Odd k) {lamc : ℝ}
    (hc : lamc ∈ Ioc a lamStar) :
    secularTaylor g H k lamc (taylorCorrection g H τ k lamc) =
      τ (lamc + taylorCorrection g H τ k lamc) :=
  (h.isGreatest_taylorCorrection hk hc).1

end IsSecularTarget

/-- A uniform first-order bound on the Taylor polynomials: for `x₀ ≤ x` with `x₀ > -λ₁` and
`δ ∈ [0, 1]`, `|tₖ(δ) - π(x)| ≤ B δ`, where `B` depends only on `x₀` and `k`. -/
theorem abs_secularTaylor_sub_le {x₀ x δ : ℝ} (hx₀ : -leftmost hH < x₀) (hx : x₀ ≤ x)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    |secularTaylor g H k x δ - secular g H x| ≤
      (∑ j ∈ range (k + 1), ((j + 1)! : ℝ) *
        secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) x₀ / j !) * δ := by
  have hxl : -leftmost hH < x := hx₀.trans_le hx
  rw [← secularTaylor_zero g H k x, secularTaylor, secularTaylor, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul, abs_div, iteratedDeriv_secular_eq hxl, abs_mul, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
    abs_of_nonneg (secularMoment_nonneg secularWeight_nonneg (mem_secularDomain_of_lt hxl) _),
    Nat.abs_cast]
  have hmom := secularMoment_le_of_le (g := g) hx₀ hx (j + 2)
  have hpow : |δ ^ j - 0 ^ j| ≤ δ := by
    rcases j with _ | j
    · simpa using hδ0
    · rw [zero_pow (Nat.succ_ne_zero j), sub_zero, abs_of_nonneg (pow_nonneg hδ0 _)]
      exact pow_le_of_le_one hδ0 hδ1 (Nat.succ_ne_zero j)
  have hfac : (0 : ℝ) < j ! := by positivity
  calc ((j + 1)! : ℝ) * secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) x /
        j ! * |δ ^ j - 0 ^ j|
      ≤ ((j + 1)! : ℝ) * secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) x₀ /
        j ! * δ :=
        mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmom (by positivity))
          hfac.le) hpow (abs_nonneg _) (div_nonneg (mul_nonneg (by positivity)
            (secularMoment_nonneg secularWeight_nonneg (mem_secularDomain_of_lt hx₀) _))
            hfac.le)

namespace IsSecularTarget

variable {τ : ℝ → ℝ} {a lamStar : ℝ} (h : IsSecularTarget hH g τ a lamStar)
include h

/-- **Convergence of odd-order Taylor iterations** (book §8.2.1 and Algorithm 8.3.1 without
Newton candidates). For odd `k`, if `λ 0 ∈ (a, λ*]` and
`λ j + δₖᵀ(λ j) ≤ λ (j + 1) ≤ λ*` for all `j`, then `λ` increases to `λ*`. (At a limit
`λ̄ < λ*`, `π - τ` is bounded below near `λ̄` by a positive constant and the Taylor coefficients are
bounded, so the corrections stay bounded below, which contradicts convergence.) -/
theorem tendsto_of_taylorCorrection_le {k : ℕ} (hk : Odd k) {x : ℕ → ℝ}
    (hx0 : x 0 ∈ Ioc a lamStar)
    (hstep : ∀ j, x j + taylorCorrection g H τ k (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar) :
    Monotone x ∧ Tendsto x atTop (𝓝 lamStar) := by
  have hmem : ∀ j, x j ∈ Ioc a lamStar ∧ x j ≤ x (j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨hx0, (h.taylorCorrection_mem hk hx0).2.2.1.trans (hstep 0).1⟩
    | succ j ih =>
      have h1 : x (j + 1) ∈ Ioc a lamStar := ⟨ih.1.1.trans_le ih.2, (hstep j).2⟩
      exact ⟨h1, (h.taylorCorrection_mem hk h1).2.2.1.trans (hstep (j + 1)).1⟩
  have hmono : Monotone x := monotone_nat_of_le_succ fun j => (hmem j).2
  have hbdd : BddAbove (range x) := ⟨lamStar, by rintro _ ⟨j, rfl⟩; exact (hmem j).1.2⟩
  set L := ⨆ j, x j with hL_def
  have hlim : Tendsto x atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  have hxL : ∀ j, x j ≤ L := fun j => le_ciSup hbdd j
  have hLs : L ≤ lamStar := ciSup_le fun j => (hmem j).1.2
  have haL : a < L := hx0.1.trans_le (hxL 0)
  refine ⟨hmono, ?_⟩
  suffices hLeq : L = lamStar by rwa [← hLeq]
  by_contra hne
  have hLlt : L < lamStar := lt_of_le_of_ne hLs hne
  have hLl := h.neg_leftmost_lt haL
  have hanti := (secular_shape (hH := hH) h.ne_zero 0).2.2.1
  -- the gap `m = π(L) - τ(L) > 0`
  set m := secular g H L - τ L with hm_def
  have hm : 0 < m := by
    have h1 := hanti hLl (h.neg_leftmost_lt h.lt_root) hLlt
    have h2 := h.monotoneOn haL h.lt_root hLlt.le
    rw [hm_def]
    linarith [h.root]
  set B := ∑ j ∈ range (k + 1), ((j + 1)! : ℝ) *
    secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) (x 0) / j ! with hB_def
  -- a uniform lower bound `η` on the corrections
  have hτL : Tendsto (fun η => τ (L + η)) (𝓝 0) (𝓝 (τ L)) := by
    have := (h.continuousOn.continuousAt (Ioi_mem_nhds haL)).tendsto
    have hadd : Tendsto (fun η : ℝ => L + η) (𝓝 0) (𝓝 L) := by
      simpa using (tendsto_const_nhds (x := L)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact this.comp hadd
  have hBη : Tendsto (fun η => B * η) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const_mul B).tendsto 0
  obtain ⟨η, hη0, ⟨hη1, hη2⟩, hη3, hη4⟩ :=
    ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)).and (nhdsWithin_le_nhds
      (((eventually_lt_nhds one_pos).and (eventually_lt_nhds (sub_pos.2 hLlt))).and
        (((tendsto_order.1 hBη).2 _ (by positivity : 0 < m / 4)).and
          ((tendsto_order.1 hτL).2 _ (by linarith : τ L < τ L + m / 4)))))).exists
  have hη0' : (0 : ℝ) < η := hη0
  have hcorr : ∀ j, η ≤ taylorCorrection g H τ k (x j) := by
    intro j
    have hxj := (hmem j).1
    have hxjl := h.neg_leftmost_lt hxj.1
    have ht : |secularTaylor g H k (x j) η - secular g H (x j)| ≤ B * η :=
      abs_secularTaylor_sub_le (h.neg_leftmost_lt hx0.1) (hmono (Nat.zero_le j)) hη0'.le hη1.le k
    have hπ : secular g H L ≤ secular g H (x j) := hanti.antitoneOn hxjl hLl (hxL j)
    have hτ : τ (x j + η) ≤ τ (L + η) :=
      h.monotoneOn (show a < x j + η by linarith [hxj.1]) (show a < L + η by linarith)
        (by linarith [hxL j])
    have hfη : τ (x j + η) ≤ secularTaylor g H k (x j) η := by
      have := (abs_le.1 ht).1
      linarith
    obtain ⟨δ, hδ, hroot⟩ := h.exists_taylor_root hk hxj hη0'.le
      (by linarith [hxL j]) hfη
    exact hδ.1.trans (le_csSup ⟨lamStar - x j, fun δ hδ => h.taylor_root_le hk hxj hδ⟩ hroot)
  have hgrow : ∀ j, x 0 + j * η ≤ x j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      push_cast
      linarith [(hstep j).1, hcorr j]
  obtain ⟨j, hj⟩ := exists_nat_gt ((lamStar - x 0) / η)
  have := hgrow j
  rw [div_lt_iff₀ hη0'] at hj
  linarith [(hmem j).1.2]

end IsSecularTarget

end Subproblem
