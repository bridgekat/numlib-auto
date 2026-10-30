import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Basic
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity
import Numlib.Optimization.Constrained.TargetMeritTaylor
import Numlib.Analysis.Calculus.MultivariateTaylor.Coord
import Numlib.Optimization.Optimality.CurveConditions
import Numlib.Analysis.InnerProductSpace.EuclideanProd

/-!
# A Phase-2 run that stops at once on an interval

On `ℝ¹` with `X = [-1, 1]` and `c ≡ 0` (so the Lagrangian is the objective and the multiplier
estimate vanishes), Phase-2 data of a high-order target-following method that never move
(`Constrained.TwoPhaseExample.Interval.seq ε₀`: iterate `0`, target `-ε₀`, radii `1`) form a run
from `x₁ = 0` as soon as `g(0) = 0` and the criticality test (14.3.34) holds at `0` for the target
`-ε₀`; the run terminates at the first outer iteration, in case (c), with output target `-ε₀`.

For `ε₀ = 1/100`, `ε_j = 1` (`j ≥ 1`), the quadratic objective `f(x) = x/4 - (25/8) x²` and the
cubic objective `f(x) = x/12 - (25/72) x² + (625/216) x³` pass the criticality test of order
`q = 2`, resp. `q = 3` (`∇²μ(0) = ∇f(0)² + ε₀ ∇²f(0) = 0`, and `∇³μ(0) = 0` for the cubic one),
while their measures of order `q` on `X ∩ ker ∇c` are large compared with
`ε_q δ^q + φ_1 (‖∇f‖ δ + … + ‖∇^{q-1} f‖ δ^{q-1})` (`quad_lt_taylorMeasure_two`,
`cubic_lt_taylorMeasure_three`).

## Main definitions

* `Constrained.TwoPhaseExample.Interval.interval`, `con`: the problem data;
* `Constrained.TwoPhaseExample.Interval.seq ε₀`: the stationary Phase-2 data;
* `Constrained.TwoPhaseExample.Interval.quad`, `cubic`, `tol`: the objectives and tolerances.

## Main results

* `Constrained.TwoPhaseExample.Interval.isHighOrderTargetRun`, `isEnd_one`, `targetOut_one`,
  `isEndCritContract`: the stationary run;
* `Constrained.TwoPhaseExample.Interval.targetCrit_quad`, `targetCrit_cubic`: the criticality tests;
* `Constrained.TwoPhaseExample.Interval.quad_lt_taylorMeasure_two`,
  `Constrained.TwoPhaseExample.Interval.cubic_lt_taylorMeasure_three`: the measure inequalities.
-/

open Set Metric
open scoped Nat RealInnerProductSpace
open Constrained (innerLagrangian)

namespace Constrained.TwoPhaseExample.Interval

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)


/-- The simple constraint set `X = [-1, 1]`. -/
def interval : Set ℝ¹ := {x | |x 0| ≤ 1}

/-- The zero equality constraint `c ≡ 0`. -/
def con : ℝ¹ → ℝ¹ := fun _ => 0

/-- The Phase-2 data in which every iterate is `0`, every target `-ε₀`, every radius `1`, and the
inner method returns its starting point without iterating. -/
noncomputable def seq (ε₀ : ℝ) : HighOrderTargetSeq ℝ¹ :=
  ⟨fun _ => 0, fun _ => -ε₀, fun _ _ => 1, fun _ _ => 0, fun _ => 0, fun _ _ => False⟩

/-- `‖r(0, -ε₀)‖ = ε₀` when `g(0) = 0`. -/
theorem targetResidual_zero {g : ℝ¹ → ℝ} (hg0 : g 0 = 0) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) :
    Constrained.targetResidual g con (-ε₀) 0 = ε₀ := by
  simp [Constrained.targetResidual_def, con, hg0, Real.sqrt_sq hε₀]

/-! ### The stationary run -/

section Run

variable {g : ℝ¹ → ℝ} {q : ℕ} {ε : ℕ → ℝ}

theorem not_isKa (hg0 : g 0 = 0) (hε0 : 0 < ε 0) (k : ℕ) :
    ¬ (seq (ε 0)).IsKa g con (1 / 2) ε k := fun h => by
  simp only [HighOrderTargetSeq.isKa_iff, seq] at h
  rw [targetResidual_zero hg0 hε0.le] at h
  linarith

theorem not_isKb (hg0 : g 0 = 0) (hε0 : 0 < ε 0) (k : ℕ) :
    ¬ (seq (ε 0)).IsKb g con (1 / 2) ε k := fun h => by
  simp only [HighOrderTargetSeq.isKb_iff, seq, hg0] at h
  linarith [h.2]

/-- **The stationary run**: for `g(0) = 0`, admissible tolerances and `θ = β = 1/2`, the data
`seq ε₀` form a run of Phase 2 from `x₁ = 0` (with `t₁ = -ε₀`) as soon as the criticality test
(14.3.34) holds at `0` for the target `-ε₀` with radii `1`. -/
theorem isHighOrderTargetRun (hg0 : g 0 = 0) (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j)
    (hε1 : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1)
    (hcrit : targetCrit g con interval q ε (-ε 0) 0 (fun _ => 1)) :
    IsHighOrderTargetRun g con interval q (1 / 2) (1 / 2) ε 0 (seq (ε 0)) := by
  have hε0 : 0 < ε 0 := hε 0 (by simp)
  have hmem0 : (0 : ℝ¹) ∈ interval := by simp [interval]
  refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, hε, hε1, hmem0,
    by simp only [con, norm_zero]; positivity, rfl, ?_, fun _ _ _ => hmem0,
    fun _ _ _ _ _ => ⟨one_pos, le_rfl⟩, fun _ _ _ => Or.inr (Or.inr hcrit),
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ i hi => absurd hi (Nat.not_lt_zero _),
    fun _ _ _ i hi => absurd hi (Nat.not_lt_zero _),
    fun k _ _ h => absurd h (not_isKa hg0 hε0 k), fun k _ _ h => absurd h (not_isKb hg0 hε0 k)⟩
  simp [seq, con, hg0, Real.sqrt_sq hε0.le]

/-- The stationary run terminates at the first outer iteration, in case (c). -/
theorem isEnd_one (hg0 : g 0 = 0) (hε0 : 0 < ε 0) :
    (seq (ε 0)).IsEnd g con interval q (1 / 2) ε 1 :=
  ⟨le_rfl, Or.inl ⟨not_isKa hg0 hε0 1, not_isKb hg0 hε0 1⟩, fun j h1 hj => absurd hj (by omega)⟩

/-- The output target of the stationary run is `-ε₀`. -/
theorem targetOut_one (hg0 : g 0 = 0) (hε0 : 0 < ε 0) :
    (seq (ε 0)).targetOut g con (1 / 2) ε 1 = -ε 0 := by
  classical
  simp only [HighOrderTargetSeq.targetOut, not_isKa hg0 hε0 1, not_isKb hg0 hε0 1, or_self,
    ite_false]
  rfl

/-- The calls of the stationary run make no iteration, so the end-criticality contract holds with
`κ_uns = κ_unc = 1` and every `κ_decr`, `π`. -/
theorem isEndCritContract (κdecr : ℝ) (π : ℕ → ℝ) :
    (seq (ε 0)).IsEndCritContract g con interval q (1 / 2) (1 / 2) ε κdecr 1 1 π :=
  ⟨fun k _ _ => by simp only [seq, Nat.cast_zero, one_mul]; positivity,
    fun k _ _ i hi => absurd hi (Nat.not_lt_zero _),
    fun k _ _ i hi => absurd hi (Nat.not_lt_zero _)⟩

end Run

/-- With `c ≡ 0` the Lagrangian is the objective. -/
theorem innerLagrangian_con (g : ℝ¹ → ℝ) (y : ℝ¹) : innerLagrangian g con y = g := by
  funext x; simp [con]

/-- With `c ≡ 0` the multiplier estimate vanishes. -/
theorem targetMultiplier_con (g : ℝ¹ → ℝ) (t : ℝ) :
    Constrained.targetMultiplier g con t 0 = 0 := by
  simp [Constrained.targetMultiplier_def, con]

/-- `∇c(0) = 0`. -/
theorem fderiv_con : fderiv ℝ con 0 = 0 := by
  unfold con; simp

private theorem contDiff_coord : ContDiff ℝ ⊤ (fun x : ℝ¹ => x 0) := contDiff_piLp_apply (p := 2)

private theorem abs_le_one_of_mem_closedBall {d : ℝ¹} (hd : d ∈ closedBall (0 : ℝ¹) 1) :
    |d 0| ≤ 1 := by
  rw [← EuclideanSpace.norm_eq_abs_fin_one]; exact mem_closedBall_zero_iff.1 hd

/-- The first-order measure at `0` on `X = [-1, 1]` with radius `1` is at most `|A|` when
`∇g(0)[d] = A d₀`. -/
theorem taylorMeasure_one_le {g : ℝ¹ → ℝ} {A : ℝ} (hA : ∀ d, fderiv ℝ g 0 d = A * d 0) :
    Optimization.taylorMeasure (ftaylorSeries ℝ g 0) 1 1 {d | 0 + d ∈ interval} ≤ |A| := by
  rw [Optimization.taylorMeasure]
  refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, by simp [interval]⟩
    fun d hd => ?_
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply, hA]
  have := abs_le_one_of_mem_closedBall hd.1
  calc -(A * d 0) ≤ |A * d 0| := neg_le_abs _
    _ = |A| * |d 0| := abs_mul _ _
    _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |A| := mul_one _

/-- `‖∇g(0)‖ ≤ |A|` when `∇g(0)[d] = A d₀`. -/
theorem norm_fderiv_le {g : ℝ¹ → ℝ} {A : ℝ} (hA : ∀ d, fderiv ℝ g 0 d = A * d 0) :
    ‖fderiv ℝ g 0‖ ≤ |A| := by
  refine (EuclideanSpace.norm_clm_fin_one_le _).trans ?_
  simp [hA]

/-! #### The `q = 2` instance -/

/-- The quadratic objective `f(x) = x/4 - (25/8) x²`. -/
noncomputable def quad : ℝ¹ → ℝ := fun x => x 0 / 4 - 25 / 8 * x 0 ^ 2

/-- The tolerances `ε₀ = 1/100`, `ε_j = 1` (`j ≥ 1`). -/
noncomputable def tol : ℕ → ℝ := fun j => if j = 0 then 1 / 100 else 1

/-- `ε₀ = 1/100`. -/
theorem tol_zero : tol 0 = 1 / 100 := rfl

/-- `ε_j = 1` for `j ≠ 0`. -/
theorem tol_of_ne {j : ℕ} (hj : j ≠ 0) : tol j = 1 := by simp [tol, hj]

/-- The tolerances are positive. -/
theorem tol_pos (j : ℕ) : 0 < tol j := by unfold tol; split_ifs <;> norm_num

/-- The tolerances are at most `1`. -/
theorem tol_le_one (j : ℕ) : tol j ≤ 1 := by unfold tol; split_ifs <;> norm_num

/-- The quadratic objective is smooth. -/
theorem contDiff_quad : ContDiff ℝ ⊤ quad :=
  (contDiff_coord.div_const 4).sub (contDiff_const.mul (contDiff_coord.pow 2))

private theorem quad_ray (d : ℝ¹) (s : ℝ) :
    quad (0 + s • d) = quad 0 + ∑ i ∈ Finset.Icc 1 2,
      s ^ i * (if i = 1 then d 0 / 4 else -(25 / 8) * d 0 ^ 2) := by
  simp [quad, Finset.sum_Icc_succ_top]
  ring

/-- `∇f(0)[d] = d₀/4` for the quadratic objective. -/
theorem fderiv_quad (d : ℝ¹) : fderiv ℝ quad 0 d = 1 / 4 * d 0 := by
  have := Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 2)
    (contDiff_quad.contDiffAt.of_le le_top) (Filter.Eventually.of_forall (quad_ray d)) 1
    (by simp)
  rw [iteratedFDeriv_one_apply] at this
  rw [this]; simp; ring

/-- The test (14.3.34) at `x = 0` for the target `-ε₀` (`ε₀ = 1/100`, radii `1`, tolerances
`ε_j/2`), when `μ(·, -ε₀) = (g + 1/100)²/2` is a polynomial of degree `N` along every ray, with
coefficients `a_d(i)`, whose partial Taylor decrements are within the tolerances on `[-1, 1]`. -/
private theorem targetCrit_of_poly {g : ℝ¹ → ℝ} (hg0 : g 0 = 0) (hg : ContDiff ℝ ⊤ g)
    {q N : ℕ} (hqN : q ≤ N) (a : ℝ¹ → ℕ → ℝ)
    (hpoly : ∀ (d : ℝ¹) (s : ℝ), (g (0 + s • d) + 1 / 100) ^ 2 / 2 =
      (g 0 + 1 / 100) ^ 2 / 2 + ∑ i ∈ Finset.Icc 1 N, s ^ i * a d i)
    (hle : ∀ d : ℝ¹, |d 0| ≤ 1 → ∀ j ∈ Finset.Icc 1 q,
      -∑ i ∈ Finset.Icc 1 j, a d i ≤ tol j * (1 / 2) * tol 0 * 1 ^ j / j !) :
    targetCrit g con interval q (fun j => tol j * (1 / 2)) (-tol 0) 0 (fun _ => 1) := by
  intro j hj
  have he : Constrained.targetMerit g con (-tol 0) = fun x => (g x + 1 / 100) ^ 2 / 2 := by
    funext x; simp [Constrained.targetMerit_def, con, tol_zero]
  have hsm : ContDiffAt ℝ N (Constrained.targetMerit g con (-tol 0)) 0 := by
    rw [he]
    exact (((hg.add contDiff_const).pow 2).div_const 2).contDiffAt.of_le le_top
  rw [Optimization.taylorMeasure]
  refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, by simp [interval]⟩
    fun d hd => ?_
  rw [Optimization.taylorDecrement_eq_of_poly (a := a d) hsm (fun s => by rw [he]; exact hpoly d s)
      ((Finset.mem_Icc.1 hj).2.trans hqN), targetResidual_zero hg0 (tol_pos 0).le]
  exact hle d (abs_le_one_of_mem_closedBall hd.1) j hj

/-- **The criticality test (14.3.34) holds at `0`** for the quadratic objective, `q = 2`, the
target `-ε₀` and the tolerances `ε_j/2`: `∇μ(0) = 1/400`, `∇²μ(0) = ∇f(0)² + ε₀ ∇²f(0) = 0`. -/
theorem targetCrit_quad :
    targetCrit quad con interval 2 (fun j => tol j * (1 / 2)) (-tol 0) 0 (fun _ => 1) :=
  targetCrit_of_poly (by simp [quad]) contDiff_quad (N := 4) (by norm_num)
    (fun d i => if i = 1 then d 0 / 400 else if i = 2 then 0 else
      if i = 3 then -(25 / 32) * d 0 ^ 3 else 625 / 128 * d 0 ^ 4)
    (fun d s => by simp [quad, Finset.sum_Icc_succ_top]; ring) fun d hd j hj => by
      rw [abs_le] at hd
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
      interval_cases j <;> simp [Finset.sum_Icc_succ_top, tol] <;> linarith

private theorem neg_single_mem :
    -EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈
      closedBall (0 : ℝ¹) 1 ∩ ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  refine ⟨mem_closedBall_zero_iff.2 (by simp), by simp [interval],
    by simp [fderiv_con]⟩

/-- The first-order measure at `0` is nonnegative. -/
theorem taylorMeasure_one_nonneg (g : ℝ¹ → ℝ) :
    0 ≤ Optimization.taylorMeasure (ftaylorSeries ℝ g 0) 1 1 {d | 0 + d ∈ interval} :=
  Optimization.taylorMeasure_nonneg _ 1 (by simp [interval]) zero_le_one

/-- **The second-order measure of the quadratic objective** on `X ∩ ker ∇c` at `0` with radius `1`
is at least `27/8` (along `-e₁`). -/
theorem le_taylorMeasure_two_quad :
    27 / 8 ≤ Optimization.taylorMeasure (ftaylorSeries ℝ quad 0) 2 1
    ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  refine le_trans ?_ (Optimization.taylorDecrement_le_taylorMeasure _ 2 neg_single_mem)
  rw [Optimization.taylorDecrement_eq_of_poly (N := 2) (contDiff_quad.contDiffAt.of_le le_top)
    (quad_ray _) le_rfl]
  simp [Finset.sum_Icc_succ_top]
  norm_num

/-! ### A cubic objective -/

/-- The cubic objective `f(x) = x/12 - (25/72) x² + (625/216) x³` (`∇f(0) = 1/12`,
`∇²f(0) = -25/36`, `∇³f(0) = 625/36`). -/
noncomputable def cubic : ℝ¹ → ℝ := fun x => x 0 / 12 - 25 / 72 * x 0 ^ 2 + 625 / 216 * x 0 ^ 3

/-- The cubic objective is smooth. -/
theorem contDiff_cubic : ContDiff ℝ ⊤ cubic :=
  ((contDiff_coord.div_const 12).sub (contDiff_const.mul (contDiff_coord.pow 2))).add
    (contDiff_const.mul (contDiff_coord.pow 3))

private theorem cubic_ray (d : ℝ¹) (s : ℝ) :
    cubic (0 + s • d) = cubic 0 + ∑ i ∈ Finset.Icc 1 3,
      s ^ i * (if i = 1 then d 0 / 12 else if i = 2 then -(25 / 72) * d 0 ^ 2
        else 625 / 216 * d 0 ^ 3) := by
  simp [cubic, Finset.sum_Icc_succ_top]
  ring

/-- `∇f(0)[d] = d₀/12` for the cubic objective. -/
theorem fderiv_cubic (d : ℝ¹) : fderiv ℝ cubic 0 d = 1 / 12 * d 0 := by
  have := Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 3)
    (contDiff_cubic.contDiffAt.of_le le_top) (Filter.Eventually.of_forall (cubic_ray d)) 1
    (by simp)
  rw [iteratedFDeriv_one_apply] at this
  rw [this]; simp; ring

/-- `‖∇²f(0)‖ ≤ 25/36` for the cubic objective. -/
theorem norm_iteratedFDeriv_two_cubic_le : ‖iteratedFDeriv ℝ 2 cubic 0‖ ≤ 25 / 36 := by
  refine (EuclideanSpace.norm_multilinear_fin_one_le _).trans ?_
  rw [Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 3)
    (contDiff_cubic.contDiffAt.of_le le_top) (Filter.Eventually.of_forall (cubic_ray _)) 2
    (by simp)]
  simp [Nat.factorial]
  norm_num

/-- **The criticality test (14.3.34) holds at `0`** for the cubic objective, `q = 3`, the target
`-ε₀` and the tolerances `ε_j/2`: `∇²μ(0) = ∇³μ(0) = 0`. -/
theorem targetCrit_cubic :
    targetCrit cubic con interval 3 (fun j => tol j * (1 / 2)) (-tol 0) 0 (fun _ => 1) :=
  targetCrit_of_poly (by simp [cubic]) contDiff_cubic (N := 6) (by norm_num)
    (fun d i => if i = 1 then d 0 / 1200 else if i = 2 then 0 else if i = 3 then 0 else
      if i = 4 then 3125 / 10368 * d 0 ^ 4 else if i = 5 then -(15625 / 15552) * d 0 ^ 5 else
      390625 / 93312 * d 0 ^ 6)
    (fun d s => by simp [cubic, Finset.sum_Icc_succ_top]; ring) fun d hd j hj => by
      rw [abs_le] at hd
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
      interval_cases j <;> simp [Finset.sum_Icc_succ_top, tol, Nat.factorial] <;> linarith

/-- **The third-order measure of the cubic objective** on `X ∩ ker ∇c` at `0` with radius `1` is at
least `718/216` (along `-e₁`). -/
theorem le_taylorMeasure_three_cubic :
    718 / 216 ≤ Optimization.taylorMeasure (ftaylorSeries ℝ cubic 0) 3 1
    ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  refine le_trans ?_ (Optimization.taylorDecrement_le_taylorMeasure _ 3 neg_single_mem)
  rw [Optimization.taylorDecrement_eq_of_poly (N := 3) (contDiff_cubic.contDiffAt.of_le le_top)
    (cubic_ray _) le_rfl]
  simp [Finset.sum_Icc_succ_top]
  norm_num

/-- `X ⊆ B(0, 2)`. -/
theorem interval_subset_ball : interval ⊆ ball (0 : ℝ¹) 2 := fun x hx => by
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq_abs_fin_one]
  exact lt_of_le_of_lt hx (by norm_num)

/-! ### The measure inequalities -/

/-- For the quadratic objective, `½ (1 + φ¹_1 ‖∇f(0)‖) < φ¹_2` at `0`, where `φ¹_j` is the
`j`-th order measure with radius `1` (on `X` for `j = 1`, on `X ∩ ker ∇c` for `j = 2`):
`½ (1 + 1/16) = 17/32 < 27/8`. -/
theorem quad_lt_taylorMeasure_two :
    (1 + Optimization.taylorMeasure (ftaylorSeries ℝ quad 0) 1 1 {d | 0 + d ∈ interval} *
        ‖fderiv ℝ quad 0‖) / 2 <
      Optimization.taylorMeasure (ftaylorSeries ℝ quad 0) 2 1
        ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  have h1 := taylorMeasure_one_le fderiv_quad
  have h2 := norm_fderiv_le fderiv_quad
  have h0 := taylorMeasure_one_nonneg quad
  have hl := le_taylorMeasure_two_quad
  rw [abs_of_pos (by norm_num)] at h1 h2
  have : Optimization.taylorMeasure (ftaylorSeries ℝ quad 0) 1 1 {d | 0 + d ∈ interval} *
      ‖fderiv ℝ quad 0‖ ≤ 1 / 4 * (1 / 4) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
  linarith

/-- For the cubic objective, `⅙ (1 + 3 φ¹_1 (‖∇f(0)‖ + ‖∇²f(0)‖)) < φ¹_3` at `0`:
`⅙ (1 + 3 · (1/12)(1/12 + 25/36)) = 43/216 < 718/216`. -/
theorem cubic_lt_taylorMeasure_three :
    (1 + 3 * Optimization.taylorMeasure (ftaylorSeries ℝ cubic 0) 1 1 {d | 0 + d ∈ interval} *
        (‖fderiv ℝ cubic 0‖ + ‖iteratedFDeriv ℝ 2 cubic 0‖)) / 6 <
      Optimization.taylorMeasure (ftaylorSeries ℝ cubic 0) 3 1
        ({d | 0 + d ∈ interval} ∩ {d | fderiv ℝ con 0 d = 0}) := by
  have h1 := taylorMeasure_one_le fderiv_cubic
  have h2 := norm_fderiv_le fderiv_cubic
  have h3 := norm_iteratedFDeriv_two_cubic_le
  have h0 := taylorMeasure_one_nonneg cubic
  have hl := le_taylorMeasure_three_cubic
  rw [abs_of_pos (by norm_num)] at h1 h2
  have : Optimization.taylorMeasure (ftaylorSeries ℝ cubic 0) 1 1 {d | 0 + d ∈ interval} *
      (‖fderiv ℝ cubic 0‖ + ‖iteratedFDeriv ℝ 2 cubic 0‖) ≤ 1 / 12 * (1 / 12 + 25 / 36) :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  nlinarith

end Constrained.TwoPhaseExample.Interval
