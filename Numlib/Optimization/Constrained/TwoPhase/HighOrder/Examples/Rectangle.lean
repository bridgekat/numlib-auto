import Numlib.Optimization.Constrained.TwoPhase.HighOrder.TRqCalls
import Numlib.Optimization.Complexity.SlowExample.TRqSaddle
import Numlib.Optimization.ModelBased.HighOrder.TRqCall

/-!
# Trust-region inner calls on a rectangle

On `ℝ²`, the problem with objective `f(x) = x₁`, constraint `c(x) = x₂ ∈ ℝ¹` and feasible set
`X = [0, 2] × [-1, 1]`, started at `x₀ = (2, 0)`. The merit function
`μ(·, t) = ½ ‖r(·, t)‖² = ½ (x₂² + (x₁ - t)²)` is quadratic with unit Hessian, and its first-order
measure at `v ∈ X` with `t ≤ v₁` is at least `max(v₁ - t, |v₂|) δ ≥ ‖r(v, t)‖ δ/√2` for radii
`δ ≤ min(v₁, 1)`. Hence, for the dual tolerance `ε₁ = 1/2`:

* the criticality test (14.3.34) of [cartis2022evaluation] fails at every such point
  (`Constrained.TwoPhaseExample.Rectangle.not_targetCrit`);
* a call of the trust-region method TRq (`Optimization.IsTRqCallOut`) on `μ(·, t)` with tolerance
  `β ‖r(x_{k,0}, t)‖/2` makes only unsuccessful first-order iterations as long as its radius is
  large, so it stays at its start for `L` iterations when `4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`
  (`Constrained.TwoPhaseExample.Rectangle.trqCall_eq_start`).

Along every run of Phase 2 of a high-order target-following method
(`Constrained.IsHighOrderTargetRun`) from `x₀` the targets drop by at most `2 ε₀` per outer
iteration, so the first `⌊1/(4 ε₀)⌋` outer iterations do not stop, and when every inner call is a
TRq call each of their calls is longer than `L`: the run uses at least `⌊1/(4ε₀)⌋ (L + 1)`
evaluations (`Constrained.TwoPhaseExample.Rectangle.funEvals_ge`), of order
`ε₀^{-1} log(1/ε₀)`.

## Main definitions

* `Constrained.TwoPhaseExample.Rectangle.obj`, `con`, `rect`, `start`: the data;
* `Constrained.TwoPhaseExample.Rectangle.tol ε₀`: the tolerances `(ε₀, 1/2, 1/2, …)`.

## Main results

* `Constrained.TwoPhaseExample.Rectangle.trqCall_eq_start`: short TRq calls do not move;
* `Constrained.TwoPhaseExample.Rectangle.not_stop`, `lt_e_of_trqCalls`: early outer iterations do
  not stop and their TRq calls are long;
* `Constrained.TwoPhaseExample.Rectangle.funEvals_ge`: the evaluation count of every such run.
-/

open Set Metric
open scoped Nat ContDiff

namespace Constrained.TwoPhaseExample.Rectangle

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The coordinates are continuous. -/
theorem continuous_coord (i : Fin 2) : Continuous (fun v : ℝ² => v i) :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).continuous

/-- The objective `f(x) = x₁` (`x₁ = v 0`). -/
noncomputable def obj : ℝ² → ℝ := fun v => v 0

/-- The constraint `c(x) = x₂`, as a map into `ℝ¹` (`x₂ = v 1`). -/
noncomputable def con : ℝ² → EuclideanSpace ℝ (Fin 1) := fun v => EuclideanSpace.single 0 (v 1)

/-- The feasible set `X = [0, 2] × [-1, 1]`. -/
def rect : Set ℝ² := {v | 0 ≤ v 0 ∧ v 0 ≤ 2 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1}

/-- The starting point `x₀ = (2, 0)`. -/
noncomputable def start : ℝ² := EuclideanSpace.single 0 2

/-- `‖c(v)‖ = |v₂|`. -/
theorem norm_con (v : ℝ²) : ‖con v‖ = |v 1| := by
  simp [con]

/-- `μ(v, t) = (v₂² + (v₁ - t)²)/2`. -/
theorem targetMerit_eq (t : ℝ) : targetMerit obj con t =
    fun v => ((v 1) ^ 2 + (v 0 - t) ^ 2) / 2 := by
  funext v
  simp [targetMerit_def, norm_con, obj, sq_abs]

/-- `‖r(v, t)‖ = √(v₂² + (v₁ - t)²)`. -/
theorem targetResidual_eq (t : ℝ) (v : ℝ²) : targetResidual obj con t v =
    √((v 1) ^ 2 + (v 0 - t) ^ 2) := by
  simp [targetResidual_def, norm_con, obj, sq_abs]

/-- The derivative of `μ(·, t)`: `s ↦ v₂ s₂ + (v₁ - t) s₁`. -/
theorem hasFDerivAt_targetMerit (t : ℝ) (v : ℝ²) :
    HasFDerivAt (fun w : ℝ² => ((w 1) ^ 2 + (w 0 - t) ^ 2) / 2)
      ((v 1) • (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ) + (v 0 - t) • EuclideanSpace.proj 0) v := by
  have h1 : HasFDerivAt (fun w : ℝ² => w 1) (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have h0 : HasFDerivAt (fun w : ℝ² => w 0) (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have := ((h1.pow 2).add ((h0.sub_const t).pow 2)).mul_const (1 / 2 : ℝ)
  convert this using 1
  · funext w; simp only [Pi.add_apply]; ring
  · ext s; simp; ring

/-- The first-order Taylor decrement of `μ(·, t)` at `v`:
`ΔT₁(s) = -(v₂ s₂ + (v₁ - t) s₁)`. -/
theorem taylorDecrement_one (t : ℝ) (v s : ℝ²) :
    (ftaylorSeries ℝ (targetMerit obj con t) v).taylorDecrement 1 s =
      -(v 1 * s 1 + (v 0 - t) * s 0) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply, targetMerit_eq]
  change -(iteratedFDeriv ℝ 1 _ v (fun _ => s)) = _
  rw [iteratedFDeriv_one_apply, (hasFDerivAt_targetMerit t v).fderiv]
  simp


/-- `μ(·, t)` is quadratic with unit Hessian:
`μ(v + s) = μ(v) + ∇μ(v)·s + ‖s‖²/2`. -/
theorem targetMerit_add (t : ℝ) (v s : ℝ²) :
    targetMerit obj con t (v + s) =
      targetMerit obj con t v +
      (v 1 * s 1 + (v 0 - t) * s 0) + ‖s‖ ^ 2 / 2 := by
  rw [targetMerit_eq, EuclideanSpace.norm_sq_eq_fin_two]
  simp only [PiLp.add_apply]
  ring

/-- `|∇μ(v)·s| ≤ ‖r(v, t)‖ ‖s‖` (Cauchy–Schwarz). -/
theorem abs_lin_le (t : ℝ) (v s : ℝ²) :
    |v 1 * s 1 + (v 0 - t) * s 0| ≤ targetResidual obj con t v * ‖s‖ := by
  rw [targetResidual_eq, ← Real.sqrt_sq (norm_nonneg s), EuclideanSpace.norm_sq_eq_fin_two,
    ← Real.sqrt_mul (by positivity)]
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (v 1 * s 0 - (v 0 - t) * s 1)]

/-- Membership in `X`. -/
theorem mem_rect {v : ℝ²} : v ∈ rect ↔ 0 ≤ v 0 ∧ v 0 ≤ 2 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1 := Iff.rfl

/-- The two coordinate directions give the lower bounds `(v₀ - t) δ` and `|v₁| δ` for the
first-order measure of `μ(·, t)` at `v ∈ X` with `t ≤ v₀` and `δ ≤ min(v₀, 1)`. -/
theorem taylorMeasure_ge {t δ : ℝ} {v : ℝ²} (hv : v ∈ rect) (hδ0 : 0 ≤ δ) (hδv : δ ≤ v 0)
    (hδ1 : δ ≤ 1) :
    (v 0 - t) * δ ≤ Optimization.taylorMeasure
        (ftaylorSeries ℝ (targetMerit obj con t) v) 1 δ {d | v + d ∈ rect} ∧
      |v 1| * δ ≤ Optimization.taylorMeasure
        (ftaylorSeries ℝ (targetMerit obj con t) v) 1 δ
          {d | v + d ∈ rect} := by
  obtain ⟨h0, h2, h3, h4⟩ := hv
  constructor
  · have hd : ((-δ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ²) ∈
        closedBall (0 : ℝ²) δ ∩ {d | v + d ∈ rect} := by
      refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
      · rw [norm_smul]; simp [abs_of_nonneg hδ0]
      · simp only [Set.mem_ofPred_eq, mem_rect, PiLp.add_apply, PiLp.smul_apply,
          PiLp.single_apply]
        norm_num
        refine ⟨by linarith, by linarith, h3, h4⟩
    have := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit obj con t) v) 1 hd
    rw [taylorDecrement_one] at this
    simp only [PiLp.smul_apply, PiLp.single_apply] at this
    norm_num at this
    linarith
  · rcases le_total 0 (v 1) with hs | hs
    · have hd : ((-δ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ²) ∈
          closedBall (0 : ℝ²) δ ∩ {d | v + d ∈ rect} := by
        refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
        · rw [norm_smul]; simp [abs_of_nonneg hδ0]
        · simp only [Set.mem_ofPred_eq, mem_rect, PiLp.add_apply, PiLp.smul_apply,
            PiLp.single_apply]
          norm_num
          refine ⟨h0, h2, by linarith, by linarith⟩
      have := Optimization.taylorDecrement_le_taylorMeasure
        (ftaylorSeries ℝ (targetMerit obj con t) v) 1 hd
      rw [taylorDecrement_one] at this
      simp only [PiLp.smul_apply, PiLp.single_apply] at this
      norm_num at this
      rw [abs_of_nonneg hs]
      linarith
    · have hd : (δ • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ²) ∈
          closedBall (0 : ℝ²) δ ∩ {d | v + d ∈ rect} := by
        refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
        · rw [norm_smul]; simp [abs_of_nonneg hδ0]
        · simp only [Set.mem_ofPred_eq, mem_rect, PiLp.add_apply, PiLp.smul_apply,
            PiLp.single_apply]
          norm_num
          refine ⟨h0, h2, by linarith, by linarith⟩
      have := Optimization.taylorDecrement_le_taylorMeasure
        (ftaylorSeries ℝ (targetMerit obj con t) v) 1 hd
      rw [taylorDecrement_one] at this
      simp only [PiLp.smul_apply, PiLp.single_apply] at this
      norm_num at this
      rw [abs_of_nonpos hs]
      linarith

/-- The criticality test (14.3.34) fails at every `v ∈ X` with `t ≤ v₀`, positive residual and
radius `δ ≤ min(v₀, 1)`, for `ε₁ = 1/2` and every `q ≥ 1` (its first-order part fails). -/
theorem not_targetCrit {q : ℕ} (hq : 1 ≤ q) {t : ℝ} {v : ℝ²} {ε δo : ℕ → ℝ}
    (hε1 : ε 1 = 1 / 2) (hv : v ∈ rect)
    (ht : t ≤ v 0) (hρ : 0 < targetResidual obj con t v) (hδ0 : 0 < δo 1)
    (hδv : δo 1 ≤ v 0) (hδ1 : δo 1 ≤ 1) : ¬ targetCrit obj con rect q ε t v δo := by
  intro hm
  have h := hm 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
  obtain ⟨ha, hb⟩ := taylorMeasure_ge (t := t) hv hδ0.le hδv hδ1
  rw [hε1] at h
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  set ρ := targetResidual obj con t v with hρdef
  have hsq : ρ ^ 2 = (v 1) ^ 2 + (v 0 - t) ^ 2 := by
    rw [hρdef, targetResidual_eq, Real.sq_sqrt (by positivity)]
  have h1 : v 0 - t ≤ ρ / 2 := by nlinarith
  have h2 : |v 1| ≤ ρ / 2 := by nlinarith
  have h3 : (v 1) ^ 2 ≤ (ρ / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : (v 0 - t) ^ 2 ≤ (ρ / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  nlinarith


/-- At `v ∈ X` with `t ≤ v₁` and `v₁ ≥ 1`, positive residual `ρ`, radius `δ ∈ (0, 1]` and
`β ≤ 1`, the first-order measure of `μ(·, t)` exceeds `β ρ δ/2`: it is at least
`max(v₁ - t, |v₂|) δ ≥ ρ δ/√2` (`taylorMeasure_ge`). -/
theorem taylorMeasure_gt {t δ β : ℝ} {v : ℝ²} (hv : v ∈ rect) (ht : t ≤ v 0) (hx1 : 1 ≤ v 0)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hβ1 : β ≤ 1)
    (hρ : 0 < targetResidual obj con t v) :
    β * targetResidual obj con t v * (1 / 2) * δ <
      Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit obj con t) v) 1
        δ {d | v + d ∈ rect} := by
  obtain ⟨ha, hb⟩ := taylorMeasure_ge (t := t) hv hδ0.le (hδ1.trans hx1) hδ1
  set M := Optimization.taylorMeasure
    (ftaylorSeries ℝ (targetMerit obj con t) v) 1 δ {d | v + d ∈ rect}
  set ρ := targetResidual obj con t v with hρdef
  have hsq : ρ ^ 2 = (v 1) ^ 2 + (v 0 - t) ^ 2 := by
    rw [hρdef, targetResidual_eq, Real.sq_sqrt (by positivity)]
  by_contra hc
  push Not at hc
  have hρδ : 0 < ρ * δ := mul_pos hρ hδ0
  have hM : M ≤ ρ * δ / 2 := by nlinarith
  have h1 : (v 0 - t) * δ ≤ ρ * δ / 2 := ha.trans hM
  have h2 : |v 1| * δ ≤ ρ * δ / 2 := hb.trans hM
  have h3 : ((v 0 - t) * δ) ^ 2 ≤ (ρ * δ / 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) hδ0.le) h1 2
  have h4 : (|v 1| * δ) ^ 2 ≤ (ρ * δ / 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hδ0.le) h2 2
  have h5 : (|v 1| * δ) ^ 2 = (v 1) ^ 2 * δ ^ 2 := by rw [mul_pow, sq_abs]
  have h6 : ((v 0 - t) * δ) ^ 2 = (v 0 - t) ^ 2 * δ ^ 2 := by rw [mul_pow]
  have h7 : (ρ * δ) ^ 2 = ((v 1) ^ 2 + (v 0 - t) ^ 2) * δ ^ 2 := by rw [mul_pow, hsq]
  nlinarith

/-- **A TRq call on `μ(·, t)` stays at its start for `L` iterations** (any `q ≥ 1`): if the
call starts at `x_{k,0} ∈ X` with `t ≤ (x_{k,0})_1` and `(x_{k,0})_1 ≥ 1`, the residual
`ρ₀ = ‖r(x_{k,0}, t)‖ ∈ (0, ε₀]`, the tolerance is `ε'_1 = β ρ₀/2` with `β ≤ 1`, `ϑ ≤ 1` and
`4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`, then every iteration `i < min(e, L)` is unsuccessful: the
first-order test fails at `x_{k,0}` (its measure is at least `ρ₀ δ/√2 > ε'_1 δ`), so the step has
order `1`; the radius is at least `4 ρ₀/(ς β)`, so the step has length `> 2 ρ₀` and increases
`μ(·, t)` (`μ` is quadratic with unit Hessian). Hence a call of length `e ≤ L` ends where it
started. -/
theorem trqCall_eq_start {q : ℕ} (hq : 1 ≤ q) {P : Optimization.TRqParams} {ϑ β ε₀ t : ℝ}
    {xi : ℕ → ℝ²} {e : ℕ} {succ : ℕ → Prop} {δo ε' : ℕ → ℝ}
    (h : Optimization.IsTRqCallOut (targetMerit obj con t) rect P q ε' ϑ
      xi e succ δo)
    (hε' : ε' 1 = β * targetResidual obj con t (xi 0) * (1 / 2))
    (hρ : 0 < targetResidual obj con t (xi 0))
    (hρε : targetResidual obj con t (xi 0) ≤ ε₀) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hϑ : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) (hX : xi 0 ∈ rect) (ht : t ≤ (xi 0) 0) (hx1 : 1 ≤ (xi 0) 0)
    {L : ℕ} (hL : 4 * ε₀ / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ) (he : e ≤ L) : xi e = xi 0 := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, hek, hxi, -, -⟩ := h
  set F := targetMerit obj con t with hF
  set ρ₀ := targetResidual obj con t (xi 0) with hρ₀
  have hγ0 := P.γ₁_pos
  have hγ1 := P.γ₁_le_one
  have hς := P.ς_pos
  have hx0 : x 0 = xi 0 := (hxi 0 (Nat.zero_le _)).symm
  have hϑ0 : 0 < ϑ := by
    rcases hϑ.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have : min P.Δ₀ ϑ = 0 := by rw [← h']; exact min_eq_right P.Δ₀_pos.le
      rw [this, mul_zero] at hL
      have : 0 < 4 * ε₀ / (P.ς * β) := by
        have : 0 < ε₀ := hρ.trans_le hρε
        positivity
      linarith
  -- an iteration at `x₀` with radius `Δ_i ≥ γ₁^i Δ₀` is unsuccessful
  have key := hr.toIsTRRun.eq_zero_of_unsucc (L := L) fun i hiL hk hxi0 hΔi => by
    have hst := Optimization.IsTRqRun.isTRqStep hr hk
    have hΔpos : 0 < Δ i := lt_of_lt_of_le (mul_pos (pow_pos P.γ₁_pos i) P.Δ₀_pos) hΔi
    have hj : jk i = 1 := by
      have hmem := Finset.mem_Icc.1 hst.order_mem
      by_contra hne
      have h1q : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
      have hle1 := hst.taylorDecrement_le_of_lt 1 h1q (by omega)
      have hw := (hr.witness i (fun l hl => hk l hl.le) 1 h1q).2
      rw [hxi0, hx0] at hle1 hw
      rw [hε'] at hle1
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hle1
      set δ := min (Δ i) ϑ with hδ
      have hgt := taylorMeasure_gt hX ht hx1 (lt_min hΔpos hϑ0)
        ((min_le_right _ _).trans hϑ1) hβ1 hρ
      have hw' : P.ς * Optimization.taylorMeasure (ftaylorSeries ℝ F (xi 0)) 1 δ
          {d | xi 0 + d ∈ rect} ≤ P.ς * (β * ρ₀ * (1 / 2) * δ) :=
        (hw.trans hle1).trans_eq (by ring)
      exact absurd (le_of_mul_le_mul_left hw' P.ς_pos) (not_le.2 hgt)
    have hlt := hst.lt_taylorDecrement
    have hle := hst.taylorDecrement_le
    rw [hj] at hlt hle
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hlt
    -- the radius
    have hpow : P.γ₁ ^ L ≤ P.γ₁ ^ i := pow_le_pow_of_le_one hγ0.le hγ1 (by omega)
    have hδ : 4 * ε₀ / (P.ς * β) ≤ min (Δ i) ϑ := by
      refine hL.trans ?_
      rw [mul_min_of_nonneg _ _ (pow_nonneg hγ0.le _)]
      refine min_le_min ((mul_le_mul_of_nonneg_right hpow P.Δ₀_pos.le).trans hΔi) ?_
      exact mul_le_of_le_one_left hϑ (pow_le_one₀ hγ0.le hγ1)
    set Pd := (ftaylorSeries ℝ F (x i)).taylorDecrement 1 (s i) with hPd
    have hρ₀' : targetResidual obj con t (x i) = ρ₀ := by
      rw [hxi0, hx0]
    have hPd_big : 2 * ρ₀ ^ 2 < Pd := by
      have h1 : P.ς * ε' 1 * min (Δ i) ϑ < Pd := hlt.trans_le hle
      rw [hε'] at h1
      have h2 : P.ς * (β * ρ₀ * (1 / 2)) * (4 * ε₀ / (P.ς * β)) = 2 * ρ₀ * ε₀ := by
        field_simp; ring
      have h3 : P.ς * (β * ρ₀ * (1 / 2)) * (4 * ε₀ / (P.ς * β)) ≤
          P.ς * (β * ρ₀ * (1 / 2)) * min (Δ i) ϑ :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      nlinarith
    have hPd_le : Pd ≤ ρ₀ * ‖s i‖ := by
      have := abs_lin_le t (x i) (s i)
      rw [hρ₀'] at this
      rw [hPd, hF, taylorDecrement_one]
      exact (neg_le_abs _).trans this
    have hPd0 : 0 < Pd := lt_of_le_of_lt (by positivity) hPd_big
    have hs : 2 * ρ₀ < ‖s i‖ := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_left hc hρ.le]
    change Optimization.trqRatio F (fun k => ftaylorSeries ℝ F (x k)) x s jk i < P.η₁
    rw [Optimization.trqRatio_eq, hj, Optimization.reductionRatio_def, ← hPd]
    have hadd := targetMerit_add t (x i) (s i)
    rw [← hF] at hadd
    have hlin : (x i) 1 * (s i) 1 + ((x i) 0 - t) * (s i) 0 = -Pd := by
      rw [hPd, hF, taylorDecrement_one]; ring
    rw [hadd, hlin]
    have hnum : F (x i) - (F (x i) + -Pd + ‖s i‖ ^ 2 / 2) < 0 := by
      have : 2 * Pd < ‖s i‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hPd_le (le_of_lt (by positivity : (0:ℝ) < 2))
        nlinarith
      linarith
    exact (div_neg_of_neg_of_pos hnum hPd0).trans P.η₁_pos
  rw [hxi e le_rfl, hxi 0 (Nat.zero_le _),
    (key e he fun l hl => hhit.2 l (lt_of_lt_of_le hl hek)).1]


section Run

variable {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝ²} {D : HighOrderTargetSeq ℝ²} {q : ℕ}

/-- `f(x_{k+1}) ≥ t_k - ε₀` along Phase 2. -/
theorem obj_succ_ge (h2 : IsHighOrderTargetRun obj con rect q θ β ε x₁ D) {k : ℕ}
    (hk1 : 1 ≤ k)
    (hk : D.Before obj con rect q θ ε k) : D.t k - ε 0 ≤ obj (D.x (k + 1)) := by
  have h1 := (abs_sub_le_targetResidual (f := obj) (c := con) (t := D.t k)
    (x := D.x (k + 1)))
  have h2' := h2.residual_succ_le hk1 hk
  have h3 := (h2.isTargetSequence hk).residual_le h2.θ_lt_one.le h2.ε₀_pos.le hk1 le_rfl
  have := neg_abs_le (obj (D.x (k + 1)) - D.t k)
  linarith

/-- **The targets decrease by at most `2 ε₀` per outer iteration**: starting from
`x₁ = (2, 0)`, `t_k ≥ 2 - (2k - 1) ε₀` for every outer iteration `k ≥ 1` reached. -/
theorem target_ge (h2 : IsHighOrderTargetRun obj con rect q θ β ε start D) :
    ∀ k, 1 ≤ k → D.Before obj con rect q θ ε k → 2 - (2 * k - 1) * ε 0 ≤ D.t k := by
  have hε₀ := h2.ε₀_pos
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    rw [h2.t_one]
    have hc : ‖con start‖ = 0 := by simp [norm_con, start]
    have hf : obj start = 2 := by simp [obj, start]
    rw [hc, hf, show ε 0 ^ 2 - (0 : ℝ) ^ 2 = ε 0 ^ 2 by ring, Real.sqrt_sq hε₀.le]
    push_cast; linarith
  | succ k hk1 ih =>
    intro hK
    have hk := hK.mono k.le_succ
    have ihk := ih hk
    have hs : ¬ D.Stop obj con rect q θ ε k := hK k hk1 (Nat.lt_succ_self k)
    have hf := obj_succ_ge h2 hk1 hk
    push_cast
    rcases TargetFollowingSeq.ka_or_kb_of_not_stop hs with ha | hb
    · rw [h2.t_succ_a k hk1 hk ha]
      have : √(ε 0 ^ 2 - ‖con (D.x (k + 1))‖ ^ 2) ≤ ε 0 := by
        calc √(ε 0 ^ 2 - ‖con (D.x (k + 1))‖ ^ 2) ≤ √(ε 0 ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (con (D.x (k + 1)))])
          _ = ε 0 := Real.sqrt_sq hε₀.le
      linarith
    · rw [h2.t_succ_b k hk1 hk hb]
      linarith

/-- **Phase 2 cannot stop early**: at an outer iteration `k ≥ 1` reached with
`(2k + 1) ε₀ ≤ 1`, the iterate `x_{k+1}` has `f ≥ 1`, so (14.3.34) fails there for every
target that Step 2 can produce, and the Step-1 output condition (14.3.32) excludes case (c). -/
theorem not_stop (hq : 1 ≤ q)
    (h2 : IsHighOrderTargetRun obj con rect q θ β ε start D) (hε1 : ε 1 = 1 / 2)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before obj con rect q θ ε k)
    (hkε : (2 * k + 1) * ε 0 ≤ 1) : ¬ D.Stop obj con rect q θ ε k := by
  have hε₀ := h2.ε₀_pos
  have hθ := h2.θ_pos
  have ht := target_ge h2 k hk1 hk
  have hf := obj_succ_ge h2 hk1 hk
  have hy1 : 1 ≤ (D.x (k + 1)) 0 := by
    change 1 ≤ obj (D.x (k + 1)); nlinarith
  have hyX := h2.mem_succ k hk1 hk
  obtain ⟨hδ0, hδ1⟩ := h2.radius_mem k hk1 hk 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
  have hδy : D.δ (k + 1) 1 ≤ (D.x (k + 1)) 0 := hδ1.trans hy1
  have hθε : 0 < θ * ε 0 := mul_pos hθ hε₀
  rintro (⟨hna, hnb⟩ | ⟨hab, hm⟩)
  · -- case (c)
    have hge : θ * ε 0 ≤ targetResidual obj con (D.t k) (D.x (k + 1)) :=
      not_lt.1 hna
    have hft : D.t k ≤ obj (D.x (k + 1)) := not_lt.1 fun hlt => hnb ⟨hge, hlt⟩
    rcases h2.output k hk1 hk with h | h | h
    · exact hna h
    · exact hnb ⟨hge, h⟩
    · exact not_targetCrit hq hε1 hyX hft (hθε.trans_le hge) hδ0 hδy hδ1 h
  · change targetCrit obj con rect q ε (D.t (k + 1)) (D.x (k + 1)) (D.δ (k + 1)) at hm
    rcases hab with ha | hb
    · rw [h2.t_succ_a k hk1 hk ha] at hm
      have hc : ‖con (D.x (k + 1))‖ ≤ ε 0 :=
        norm_le_targetResidual.trans (ha.le.trans
          (mul_le_of_le_one_left hε₀.le h2.θ_lt_one.le))
      refine not_targetCrit hq hε1 hyX ?_ ?_ hδ0 hδy hδ1 hm
      · change _ ≤ obj (D.x (k + 1)); linarith [Real.sqrt_nonneg
          (ε 0 ^ 2 - ‖con (D.x (k + 1))‖ ^ 2)]
      · rw [targetResidual_sub_sqrt hε₀.le hc]; exact hε₀
    · rw [h2.t_succ_b k hk1 hk hb] at hm
      refine not_targetCrit hq hε1 hyX ?_ ?_ hδ0 hδy hδ1 hm
      · change _ ≤ obj (D.x (k + 1)); linarith [hb.2]
      · rw [targetResidual_two_mul_sub]; exact hθε.trans_le hb.1

end Run


section Count

variable {P : Optimization.TRqParams} {ϑ θ β : ℝ} {ε : ℕ → ℝ} {D : HighOrderTargetSeq ℝ²} {q : ℕ}

/-- **Every call of an early outer iteration is long**: at an outer iteration `k ≥ 1` reached
with `(2k - 1) ε₀ ≤ 1`, a TRq call has more than `L` iterations when
`4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`: otherwise it returns `x_{k+1} = x_k`, where no test of
(14.3.32) holds. -/
theorem lt_e_of_trqCalls (hq : 1 ≤ q)
    (h2 : IsHighOrderTargetRun obj con rect q θ β ε start D)
    (hcalls : ∀ k, 1 ≤ k → D.Before obj con rect q θ ε k →
      Optimization.IsTRqCallOut (targetMerit obj con (D.t k)) rect P q
        (fun j => β * targetResidual obj con (D.t k) (D.x k) * ε j) ϑ (D.xi k) (D.e k)
        (D.succ k) (D.δ (k + 1))) (hε1 : ε 1 = 1 / 2)
    (hϑ : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) {L : ℕ} (hL : 4 * ε 0 / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before obj con rect q θ ε k) (hkε : (2 * k - 1) * ε 0 ≤ 1) :
    L < D.e k := by
  by_contra hle
  push Not at hle
  have hε₀ := h2.ε₀_pos
  have hθε : 0 < θ * ε 0 := mul_pos h2.θ_pos hε₀
  have hlo := h2.le_targetResidual k hk1 hk
  have hhi := (h2.isTargetSequence hk).residual_le h2.θ_lt_one.le hε₀.le hk1 le_rfl
  have h0 := h2.inner_zero k hk1 hk
  have ht := target_ge h2 k hk1 hk
  have hft : D.t k ≤ obj (D.x k) := by
    have := (h2.isTargetSequence hk).sub_target_nonneg hk1 le_rfl; linarith
  have hx1 : 1 ≤ (D.x k) 0 := by change 1 ≤ obj (D.x k); linarith
  have hβ1 : β ≤ 1 := h2.β_le_θ.trans h2.θ_lt_one.le
  have hstuck := trqCall_eq_start hq (hcalls k hk1 hk) (by rw [h0, hε1])
    (by rw [h0]; linarith) (by rw [h0]; exact hhi) h2.β_pos hβ1 hϑ hϑ1
    (by rw [h0]; exact h2.x_mem k hk1 hk) (by rw [h0]; exact hft) (by rw [h0]; exact hx1) hL hle
  have hx : D.x (k + 1) = D.x k := by rw [← h2.inner_end k hk1 hk, hstuck, h0]
  obtain ⟨hδ0, hδ1⟩ := h2.radius_mem k hk1 hk 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
  rcases h2.output k hk1 hk with h | h | h
  · rw [hx] at h; linarith
  · rw [hx] at h; linarith
  · rw [hx] at h
    exact not_targetCrit hq hε1 (h2.x_mem k hk1 hk) hft (hθε.trans_le hlo) hδ0
      (hδ1.trans hx1) hδ1 h

/-- **The evaluation count of Phase 2 is at least `⌊1/(4ε₀)⌋ (L + 1)`** for every run from `x₀`
whose inner calls are TRq calls, when `ε₀ ≤ 1/2` and `4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`. -/
theorem funEvals_ge (hq : 1 ≤ q)
    (h2 : IsHighOrderTargetRun obj con rect q θ β ε start D)
    (hcalls : ∀ k, 1 ≤ k → D.Before obj con rect q θ ε k →
      Optimization.IsTRqCallOut (targetMerit obj con (D.t k)) rect P q
        (fun j => β * targetResidual obj con (D.t k) (D.x k) * ε j) ϑ (D.xi k) (D.e k)
        (D.succ k) (D.δ (k + 1))) (hε1 : ε 1 = 1 / 2)
    (hε₀2 : ε 0 ≤ 1 / 2) (hϑ : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) {L : ℕ}
    (hL : 4 * ε 0 / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ) {kε : ℕ}
    (hend : D.IsEnd obj con rect q θ ε kε) :
    (⌊1 / (4 * ε 0)⌋₊ : ℝ) * (L + 1) ≤ D.funEvals kε := by
  have hε₀ := h2.ε₀_pos
  obtain ⟨hkε1, hstop, hbef⟩ := hend
  set N := ⌊1 / (4 * ε 0)⌋₊ with hN
  have hNle : (N : ℝ) ≤ 1 / (4 * ε 0) := Nat.floor_le (by positivity)
  -- `kε` is large
  have hbig : 1 < (2 * kε + 1) * ε 0 := by
    by_contra hc
    push Not at hc
    exact not_stop hq h2 hε1 hkε1 hbef hc hstop
  have hNk : N ≤ kε := by
    have : (N : ℝ) ≤ kε := by
      have h1 : 1 / (4 * ε 0) ≤ (kε : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    exact_mod_cast this
  have hcount : ∀ k ∈ Finset.Icc 1 N, L + 1 ≤ D.e k := fun k hk => by
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    have hkb : D.Before obj con rect q θ ε k :=
      hbef.mono (hkN.trans hNk)
    have hkε : (2 * k - 1) * ε 0 ≤ 1 := by
      have : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have : (k : ℝ) * ε 0 ≤ 1 / 4 := by
        calc (k : ℝ) * ε 0 ≤ (1 / (4 * ε 0)) * ε 0 := by gcongr; linarith
          _ = 1 / 4 := by field_simp
      nlinarith
    exact lt_e_of_trqCalls hq h2 hcalls hε1 hϑ hϑ1 hL hk1 hkb hkε
  have hsum : N * (L + 1) ≤ ∑ j ∈ Finset.Icc 1 kε, D.e j := by
    calc N * (L + 1) = ∑ _j ∈ Finset.Icc 1 N, (L + 1) := by simp
      _ ≤ ∑ j ∈ Finset.Icc 1 N, D.e j := Finset.sum_le_sum hcount
      _ ≤ ∑ j ∈ Finset.Icc 1 kε, D.e j :=
          Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right hNk)
  rw [HighOrderTargetSeq.funEvals_eq_sum]
  have : ((N * (L + 1) : ℕ) : ℝ) ≤ ((1 + ∑ j ∈ Finset.Icc 1 kε, D.e j : ℕ) : ℝ) := by
    exact_mod_cast hsum.trans (Nat.le_add_left _ _)
  push_cast at this ⊢
  exact this

end Count

/-- The coordinates are smooth. -/
theorem contDiff_coord (i : Fin 2) : ContDiff ℝ ∞ (fun v : ℝ² => v i) :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).contDiff

/-- `X` is closed. -/
theorem isClosed_rect : IsClosed rect := by
  have hc : ∀ a : ℝ, Continuous fun _ : ℝ² => a := fun a => continuous_const
  have h := ((isClosed_le (hc 0) (continuous_coord 0)).inter
    (isClosed_le (continuous_coord 0) (hc 2))).inter
    ((isClosed_le (hc (-1)) (continuous_coord 1)).inter
    (isClosed_le (continuous_coord 1) (hc 1)))
  convert h using 1
  ext v
  simp only [rect, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- `x₀ ∈ X`. -/
theorem start_mem : start ∈ rect := by
  simp only [mem_rect, start, PiLp.single_apply]
  norm_num

/-- `X` lies in the ball of radius `3`. -/
theorem rect_subset_ball : rect ⊆ ball (0 : ℝ²) 3 := by
  intro v hv
  obtain ⟨h0, h2, h3, h4⟩ := hv
  rw [mem_ball_zero_iff]
  have hs := EuclideanSpace.norm_sq_eq_fin_two v
  have : ‖v‖ ^ 2 < 3 ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this

/-- The tolerances `ε₀` and `ε_j = 1/2` (`j ≥ 1`). -/
noncomputable def tol (ε₀ : ℝ) : ℕ → ℝ := fun j => if j = 0 then ε₀ else 1 / 2

end Constrained.TwoPhaseExample.Rectangle
