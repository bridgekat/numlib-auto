import NumlibSurface.CartisGouldToint.Chapter14.Section03TrustRegionSharp

/-!
# Cartis–Gould–Toint §14.3: Theorem 14.3.9 with a trust-region INNER fails in the printed order

Counterexample for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Theorem 14.3.9 (OCR l. 17583) when
INNER is of trust-region type (TRq-SC) and the exponents are the printed `π_j = j + 1` of (14.2.12):
for every `q ≥ 2`, whole runs of TPqp-GC with TRq-SC calls (`IsTPqpGCTRqSCRun`) are **not** within
`O((1 + |log(ε₀ ε_min)|) max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}])` derivative evaluations, on
a fixed problem satisfying all the hypotheses of the theorem, with fixed algorithm parameters, both
for runs ending in Phase 1 and for runs ending in Phase 2. (For `q = 1` the printed order holds up
to the logarithmic factor, `theorem_14_3_9_trq_one`; for every `q` the theorem holds with the
exponents `q + 1`, `theorem_14_3_9_trq`.)

**The problem.** `n = 2`, `X = {v | v_1 ≥ 1}` (closed, convex, unbounded), `f = 0`, and
* Phase-1 version: `c(v) = (1, v_1^{-1/8}, v_2) ∈ ℝ³` (`trqSlowC`), `x₀ = (2, 0)`;
* Phase-2 version: `c₂(v) = (v_1^{-1/8}, v_2) ∈ ℝ²` (`trqSlowC2`), `x₀ = (256, 0)`.

c.D1qLB.X holds for every `q` on `X₀ = {v_1 > 1/2}` (`trqSlowC_assumption`,
`trqSlowC2_assumption`); f.D1qLB.X and f.B.Fb are trivial. In both versions INNER minimizes, up to
a constant, `ν(v) = ½‖c(v)‖² = ½ + v_1^{-1/4}/2 + v_2²/2`, whose slope along the first axis is
`A(v_1) = v_1^{-5/4}/8` (`trqSlowA`), with curvature `B(v_1) = 5 v_1^{-9/4}/32` (`trqSlowB`,
`B(v_1) δ ≤ A(v_1)` for `v_1 ≥ 2`, `δ ≤ 1`) and unit curvature along the second axis. The TRq
parameters are fixed (`trqSlowParams`: `Δ₀ = Δ_max = 1`, `η = (1/4, 3/4)`, `γ = (1/4, 1/2, 2)`,
`ς = 1/4`), `ϑ = 1`.

**The tolerances.** `ε₀ = 1`, `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`, `ε_j = 1` for `j ≥ 3`
(`trqSlowTol`): the printed order is `2^{20M}` and `|log(ε₀ ε_min)| = 10 M log 2`.

**The INNER run** (TRq-SC on `ν` with tolerances `ε_j/2`, `trqSlow_exists_long_run`), with
`y = 2^{-10M}`:
* travel (`trqSlow_travel_phase`): first-order steps `(1/2, 0)` at radius `1` along the first axis
  while `A > ε_1/2`, the last one `(1/2, y)`; all are successful;
* shrinking (`trqSlow_shrink_phase`): at `(a, y)`, `10M` unsuccessful first-order steps `(0, -Δ)`
  (ratio `1 - Δ/(2y)`) halve the radius from `1` to `y`, and a successful one reaches `(a, 0)`;
* slow phase (`trqSlow_slow_phase`): steps `(y, 0)` at radius `y`; the first-order test passes
  (`A ≤ ε_1/2`) and the second-order test fails as long as `A > ε_2 y/8`, i.e. while
  `v_1 < 2^{12M}`; every step is successful and decreases `ν` by about `A y`, as little as
  `≈ ε_2 ε_1²`; there are `2^{22M} - 2^{18M} - 2^{10M}` of them;
* any TRq-SC run continues; it terminates (`Chapter12.theorem_12_2_5_anchored`).

In the Phase-1 version this is the only INNER call of LENq-SC, and Phase 1 exits with `‖c‖ ≥ 1`
(`trqSlow_exists_tpqp_run`). In the Phase-2 version `‖c₂(x₀)‖ = 1/2 = θ ε₀` (`θ = β = 1/2`), Phase 1
ends at once, `t_1 = -√3/2`, `μ(·, t_1)` differs from `½‖c‖²` by a constant (`trq_run_congr`),
`‖r(·, t_1)‖ ≥ √3/2 ≥ θ ε₀` throughout, the run is the single INNER call of Phase 2, and Phase 2
ends in case (c) (`trqSlow_exists_tpqp_run_phase2`). Either way the derivative evaluations are
at least `2^{22M}/2`, against `(1 + 10 M log 2) 2^{20M}` (`trqSlow_not_le_printed`).

The mechanism: the trust-region radius is shared by all orders. First-order failures across a
direction of unit curvature drive it down to the scale of `ε_1`; then second-order steps along a
direction of slope between `ε_2 ε_1` and `ε_1` and negligible curvature decrease the model by
only `≈ ε_2 ε_1²` each, and a fixed function with slope `≈ v_1^{-5/4}` has such slopes along a
path of length `≈ (ε_2 ε_1)^{-4/5}`. With `ε₀ = 1` the INNER run alone (TRq-SC,
`trqSlow_exists_long_run`) exceeds `max_j ε_j^{-(j+1)}`, so the error is already in the TRq-SC
row `j + 1` of (14.2.12), not in the counting of Theorem 14.3.9.

## Main definitions

* `trqSlowC`, `trqSlowC2`, `trqSlowX`, `trqSlowX₀`, `trqSlowParams`, `trqSlowβ₁`, `trqSlowTol`:
  the data of the counterexamples;
* `trqSlowA`, `trqSlowB`, `trqSlowNu`: the slope, curvature and closed form of `½‖c‖²`.

## Main results

* `trq_splice`: an explicit prefix of TRq-SC iterations followed by any TRq-SC run is a TRq-SC run;
* `trq_run_congr`: a TRq-SC run transfers to a function with the same Taylor decrements and
  differences on `X`;
* `trqSlow_exists_long_run`: the long TRq-SC run;
* `trqSlow_exists_tpqp_run`, `trqSlow_exists_tpqp_run_phase2`: the long TPqp-GC runs;
* `theorem_14_3_9_trq_printed_false` (Phase 1) and `theorem_14_3_9_trq_printed_false_phase2`
  (Phase 2): no `κ` bounds the derivative evaluations by
  `κ (1 + |log(ε₀ ε_min)|) max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}]`, `q ≥ 2`;
* `theorem_14_3_9_trq_printed_false_conclusion`,
  `theorem_14_3_9_trq_printed_false_conclusion_phase2`: all hypotheses of `theorem_14_3_9_trq`
  hold, and its conclusion with `π_j = j + 1` in place of `q + 1` fails.

## Not formalized

Variants of the counterexample for other TRq parameters and thresholds `ϑ`. Corrected orders
for TRq-SC INNER runs other than `theorem_14_3_9_trq` and `theorem_14_3_9_trq_one` (archived at
commit 8c2b1518 on branch `claude/cartis-gould-toint-formalization`).
-/

open Set Metric
open scoped Nat ContDiff Topology

namespace CartisGouldToint.Chapter14

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

set_option hygiene false in
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

section OneDim

/-- `p(t) = t^{-1/4}`. -/
noncomputable def trqSlowP : ℝ → ℝ := fun t => t ^ (-(1 / 4 : ℝ))

/-- `p^{(k)}(t) = (-1/4)(-1/4 - 1)⋯(-1/4 - k + 1) t^{-1/4 - k}`. -/
theorem iteratedDeriv_trqSlowP (k : ℕ) (t : ℝ) :
    iteratedDeriv k trqSlowP t =
      (descPochhammer ℝ k).eval (-(1 / 4 : ℝ)) * t ^ (-(1 / 4 : ℝ) - k) := by
  rw [iteratedDeriv_eq_iterate]; exact Real.iter_deriv_rpow_const _ _ _

/-- `p'(t) = -t^{-5/4}/4`. -/
theorem iteratedDeriv_trqSlowP_one (t : ℝ) :
    iteratedDeriv 1 trqSlowP t = -(t ^ (-(5 / 4 : ℝ)) / 4) := by
  rw [iteratedDeriv_trqSlowP]
  norm_num
  ring

/-- `p''(t) = 5 t^{-9/4}/16`. -/
theorem iteratedDeriv_trqSlowP_two (t : ℝ) :
    iteratedDeriv 2 trqSlowP t = 5 * t ^ (-(9 / 4 : ℝ)) / 16 := by
  rw [iteratedDeriv_trqSlowP]
  norm_num [descPochhammer_succ_right]
  ring

/-- `p` is smooth on `(0, ∞)`. -/
theorem contDiffOn_trqSlowP : ContDiffOn ℝ ∞ trqSlowP (Ioi 0) := fun _ hx =>
  (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt

end OneDim

section Problem

/-- The point `(a, b)` of `ℝ²`. -/
noncomputable def slowPt (a b : ℝ) : ℝ² := WithLp.toLp 2 ![a, b]

@[simp] theorem slowPt_apply_zero (a b : ℝ) : slowPt a b 0 = a := rfl

@[simp] theorem slowPt_apply_one (a b : ℝ) : slowPt a b 1 = b := rfl

/-- `(a, b) + (c, d) = (a + c, b + d)`. -/
theorem slowPt_add (a b c d : ℝ) : slowPt a b + slowPt c d = slowPt (a + c) (b + d) := by
  ext i; fin_cases i <;> simp [slowPt]

/-- `‖(a, b)‖² = a² + b²`. -/
theorem norm_slowPt_sq (a b : ℝ) : ‖slowPt a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [trqLog_norm_sq]; rfl

/-- `‖(a, b)‖ ≤ |a| + |b|`. -/
theorem norm_slowPt_le (a b : ℝ) : ‖slowPt a b‖ ≤ |a| + |b| := by
  have h := norm_slowPt_sq a b
  have h0 : 0 ≤ |a| + |b| := by positivity
  have h1 : ‖slowPt a b‖ ^ 2 ≤ (|a| + |b|) ^ 2 := by
    rw [h]; nlinarith [sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]
  nlinarith [norm_nonneg (slowPt a b)]

/-- `g(t) = t^{-1/8}`, the second component of the constraint. -/
noncomputable def trqSlowG : ℝ → ℝ := fun t => t ^ (-(1 / 8 : ℝ))

/-- `g(t)² = p(t)` for `t ≥ 0`. -/
theorem trqSlowG_sq {t : ℝ} (ht : 0 ≤ t) : trqSlowG t ^ 2 = trqSlowP t := by
  rw [trqSlowG, trqSlowP, ← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

/-- The constraint `c(v) = (1, v_1^{-1/8}, v_2)` of the example (`v_1 = v 0`, `v_2 = v 1`). -/
noncomputable def trqSlowC : ℝ² → ℝ³ := fun v => WithLp.toLp 2 ![1, trqSlowG (v 0), v 1]

/-- `‖c(v)‖² = 1 + g(v_1)² + v_2²`. -/
theorem norm_trqSlowC_sq (v : ℝ²) : ‖trqSlowC v‖ ^ 2 = 1 + trqSlowG (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [trqSlowC, sq_abs]

/-- `‖c(v)‖ ≥ 1`. -/
theorem one_le_norm_trqSlowC (v : ℝ²) : 1 ≤ ‖trqSlowC v‖ := by
  have h := norm_trqSlowC_sq v
  have : 1 ≤ ‖trqSlowC v‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg (trqSlowG (v 0)), sq_nonneg (v 1)]
  nlinarith [norm_nonneg (trqSlowC v)]

/-- The infeasibility measure `ν = ½ ‖c‖²` near the half-plane `v_1 > 0`:
`ν(w) = ½ + p(w_1)/2 + w_2²/2`. -/
noncomputable def trqSlowNu : ℝ² → ℝ := fun w => 1 / 2 + trqSlowP (w 0) / 2 + trqSadSq (w 1)

/-- `ν = ½ ‖c‖²` on `v_1 ≥ 0`. -/
theorem phi2_trqSlowC_eq {v : ℝ²} (hv : 0 ≤ v 0) : phi2 trqSlowC v = trqSlowNu v := by
  rw [phi2_apply, norm_trqSlowC_sq, trqSlowG_sq hv, trqSlowNu, trqSadSq]
  ring

/-- `ν(a, b) = ½ + a^{-1/4}/2 + b²/2` for `a ≥ 0`. -/
theorem phi2_trqSlowC_slowPt {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    phi2 trqSlowC (slowPt a b) = 1 / 2 + a ^ (-(1 / 4 : ℝ)) / 2 + b ^ 2 / 2 := by
  rw [phi2_trqSlowC_eq (by simpa using ha)]
  simp [trqSlowNu, trqSlowP, trqSadSq]

/-- `ν` and `½ ‖c‖²` agree near every point of the open half-plane `v_1 > 0`. -/
theorem phi2_trqSlowC_eventuallyEq {v : ℝ²} (hv : 0 < v 0) : phi2 trqSlowC =ᶠ[𝓝 v] trqSlowNu := by
  have hU : IsOpen {w : ℝ² | 0 < w 0} :=
    isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)
  filter_upwards [hU.mem_nhds hv] with w hw
  exact phi2_trqSlowC_eq (le_of_lt hw)

/-- The Taylor series of `½ ‖c‖²` at a point of the open half-plane `v_1 > 0` is that of `ν`. -/
theorem ftaylorSeries_phi2_trqSlowC {v : ℝ²} (hv : 0 < v 0) :
    ftaylorSeries ℝ (phi2 trqSlowC) v = ftaylorSeries ℝ trqSlowNu v :=
  ((phi2_trqSlowC_eventuallyEq hv).ftaylorSeries ℝ).eq_of_nhds

/-- `ν` is smooth near every point of the open half-plane `v_1 > 0`. -/
theorem contDiffAt_trqSlowNu {v : ℝ²} (hv : 0 < v 0) (n : ℕ) : ContDiffAt ℝ n trqSlowNu v := by
  have h2 : ContDiffAt ℝ n (fun w : ℝ² => trqSlowP (w 0) / 2) v :=
    ((Real.contDiffAt_rpow_const_of_ne hv.ne').comp v
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).contDiff.contDiffAt).div_const 2
  have h3 : ContDiffAt ℝ n (fun w : ℝ² => trqSadSq (w 1)) v :=
    (trqSad_contDiff_coordSq 1).contDiffAt.of_le (by exact_mod_cast le_top)
  exact (contDiffAt_const.add h2).add h3

/-- `∇^k ν(v)[s]^k = p^{(k)}(v_1)/2 · s_1^k + (t²/2)^{(k)}(v_2) s_2^k` for `k ≥ 1`, `v_1 > 0`. -/
theorem iteratedFDeriv_trqSlowNu_apply {v : ℝ²} (hv : 0 < v 0) {k : ℕ} (hk : k ≠ 0) (s : ℝ²) :
    iteratedFDeriv ℝ k trqSlowNu v (fun _ => s) =
      iteratedDeriv k trqSlowP (v 0) / 2 * (s 0) ^ k + iteratedDeriv k trqSadSq (v 1) * (s 1) ^ k
        := by
  have e : trqSlowNu =
      ((fun _ => (1 / 2 : ℝ)) + fun w : ℝ² => trqSlowP (w 0) / 2) + fun w => trqSadSq (w 1) := by
    funext w; rfl
  have h1 : ContDiffAt ℝ k (fun _ : ℝ² => (1 / 2 : ℝ)) v := contDiffAt_const
  have h2 : ContDiffAt ℝ k (fun w : ℝ² => trqSlowP (w 0) / 2) v :=
    ((Real.contDiffAt_rpow_const_of_ne hv.ne').comp v
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).contDiff.contDiffAt).div_const 2
  have h3 : ContDiffAt ℝ k (fun w : ℝ² => trqSadSq (w 1)) v :=
    (trqSad_contDiff_coordSq 1).contDiffAt.of_le (by exact_mod_cast le_top)
  have h12 : ContDiffAt ℝ k ((fun _ : ℝ² => (1 / 2 : ℝ)) + fun w : ℝ² => trqSlowP (w 0) / 2) v :=
    h1.add h2
  rw [e, iteratedFDeriv_add_apply h12 h3, iteratedFDeriv_add_apply h1 h2,
    iteratedFDeriv_const_of_ne hk]
  simp only [Pi.zero_apply, add_apply, zero_add]
  have hP : ContDiffAt ℝ k (fun t => trqSlowP t / 2) (v 0) :=
    ((contDiffOn_trqSlowP.div_const 2).contDiffAt (isOpen_Ioi.mem_nhds hv)).of_le
      (by exact_mod_cast le_top)
  rw [ContDiffAt.iteratedFDeriv_comp_coord_apply_const 0 hP s,
    iteratedDeriv_div_const, ContDiffAt.iteratedFDeriv_comp_coord_apply_const 1
      (contDiff_trqSadSq.contDiffAt.of_le (by exact_mod_cast le_top)) s]

/-- `|ν'| = t^{-5/4}/8` (the slope along the first axis). -/
noncomputable def trqSlowA (t : ℝ) : ℝ := t ^ (-(5 / 4 : ℝ)) / 8

/-- `ν'' = 5 t^{-9/4}/32` (the curvature along the first axis). -/
noncomputable def trqSlowB (t : ℝ) : ℝ := 5 * t ^ (-(9 / 4 : ℝ)) / 32

/-- `ΔT_1(v, s) = A(v_1) s_1 - v_2 s_2` for `v_1 > 0`. -/
theorem trqSlow_ΔT1 {v : ℝ²} (hv : 0 < v 0) (s : ℝ²) :
    (ftaylorSeries ℝ (phi2 trqSlowC) v).taylorDecrement 1 s = trqSlowA (v 0) * s 0 - v 1 * s 1 := by
  rw [ftaylorSeries_phi2_trqSlowC hv, FormalMultilinearSeries.taylorDecrement_one_apply]
  change -(iteratedFDeriv ℝ 1 trqSlowNu v (fun _ => s)) = _
  rw [iteratedFDeriv_trqSlowNu_apply hv one_ne_zero, iteratedDeriv_trqSlowP_one,
    iteratedDeriv_trqSadSq_one, trqSlowA]
  ring

/-- `ΔT_2(v, s) = A(v_1) s_1 - v_2 s_2 - (B(v_1) s_1² + s_2²)/2` for `v_1 > 0`. -/
theorem trqSlow_ΔT2 {v : ℝ²} (hv : 0 < v 0) (s : ℝ²) :
    (ftaylorSeries ℝ (phi2 trqSlowC) v).taylorDecrement 2 s =
      trqSlowA (v 0) * s 0 - v 1 * s 1 - (trqSlowB (v 0) * (s 0) ^ 2 + (s 1) ^ 2) / 2 := by
  rw [ftaylorSeries_phi2_trqSlowC hv, FormalMultilinearSeries.taylorDecrement_two]
  change -(iteratedFDeriv ℝ 1 trqSlowNu v (fun _ => s)) -
    2⁻¹ * iteratedFDeriv ℝ 2 trqSlowNu v (fun _ => s) = _
  rw [iteratedFDeriv_trqSlowNu_apply hv one_ne_zero, iteratedFDeriv_trqSlowNu_apply hv two_ne_zero,
    iteratedDeriv_trqSlowP_one, iteratedDeriv_trqSlowP_two, iteratedDeriv_trqSadSq_one,
    iteratedDeriv_trqSadSq_two, trqSlowA, trqSlowB]
  ring

end Problem

section Scalar

/-- `A(t) > 0` for `t > 0`. -/
theorem trqSlowA_pos {t : ℝ} (ht : 0 < t) : 0 < trqSlowA t := by
  unfold trqSlowA; positivity

/-- `B(t) ≥ 0` for `t > 0`. -/
theorem trqSlowB_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ trqSlowB t := by
  unfold trqSlowB; positivity

/-- `A` is nonincreasing on `(0, ∞)`. -/
theorem trqSlowA_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : trqSlowA t ≤ trqSlowA s := by
  unfold trqSlowA
  have := Real.rpow_le_rpow_of_nonpos hs hst (by norm_num : (-(5 / 4 : ℝ)) ≤ 0)
  linarith

/-- `B(t) = (5/4) A(t)/t`. -/
theorem trqSlowB_eq {t : ℝ} (ht : 0 < t) : trqSlowB t = 5 / 4 * trqSlowA t / t := by
  unfold trqSlowB trqSlowA
  have : t ^ (-(9 / 4 : ℝ)) = t ^ (-(5 / 4 : ℝ)) * t ^ (-1 : ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  rw [this, Real.rpow_neg_one]
  field_simp
  ring

/-- `B(t) δ ≤ A(t)` for `t ≥ 2` and `0 ≤ δ ≤ 1`. -/
theorem trqSlowB_mul_le {t δ : ℝ} (ht : 2 ≤ t) (hδ1 : δ ≤ 1) :
    trqSlowB t * δ ≤ trqSlowA t := by
  have ht0 : 0 < t := by linarith
  rw [trqSlowB_eq ht0, div_mul_eq_mul_div, div_le_iff₀ ht0]
  have := trqSlowA_pos ht0
  nlinarith

/-- `A(t) ≤ 2 A(t + h)` for `t ≥ 2` and `0 ≤ h ≤ 1/2`. -/
theorem trqSlowA_le_two_mul {t h : ℝ} (ht : 2 ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2) :
    trqSlowA t ≤ 2 * trqSlowA (t + h) := by
  have ht0 : 0 < t := by linarith
  have h1 : trqSlowA (5 / 4 * t) ≤ trqSlowA (t + h) := trqSlowA_anti (by linarith) (by linarith)
  have h2 : trqSlowA (5 / 4 * t) = (5 / 4 : ℝ) ^ (-(5 / 4 : ℝ)) * trqSlowA t := by
    unfold trqSlowA
    rw [Real.mul_rpow (by norm_num) ht0.le]
    ring
  have h3 : (16 / 25 : ℝ) ≤ (5 / 4 : ℝ) ^ (-(5 / 4 : ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5 / 4)
      (by norm_num : (-2 : ℝ) ≤ -(5 / 4 : ℝ))
    have e : (5 / 4 : ℝ) ^ (-2 : ℝ) = 16 / 25 := by
      rw [Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    linarith
  have := trqSlowA_pos ht0
  nlinarith

/-- `(t^{-1/4})' = -2 A(t)`. -/
theorem hasDerivAt_rpow_quarter {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) (-(2 * trqSlowA t)) t := by
  have := Real.hasDerivAt_rpow_const (p := -(1 / 4 : ℝ)) (Or.inl ht.ne')
  convert this using 1
  unfold trqSlowA
  norm_num
  ring

/-- **The decrease along the first axis**: for `t ≥ 2` and `0 ≤ h ≤ 1/2`,
`t^{-1/4}/2 - (t + h)^{-1/4}/2 ≥ A(t) h / 2`. -/
theorem trqSlow_decrease_ge {t h : ℝ} (ht : 2 ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2) :
    trqSlowA t * h / 2 ≤ t ^ (-(1 / 4 : ℝ)) / 2 - (t + h) ^ (-(1 / 4 : ℝ)) / 2 := by
  have ht0 : 0 < t := by linarith
  rcases hh0.eq_or_lt with rfl | hpos
  · simp
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (-(1 / 4 : ℝ)))
    (fun x => -(2 * trqSlowA x)) (by linarith : t < t + h)
    (fun x hx =>
      (Real.continuousAt_rpow_const x _ (Or.inl (by linarith [hx.1]))).continuousWithinAt)
    (fun x hx => hasDerivAt_rpow_quarter (by linarith [hx.1]))
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  have hA : trqSlowA (t + h) ≤ trqSlowA ξ := trqSlowA_anti hξ0 hξ.2.le
  have hA2 := trqSlowA_le_two_mul ht hh0 hh
  simp only [add_sub_cancel_left] at hξd
  rw [eq_div_iff hpos.ne'] at hξd
  nlinarith

end Scalar

section Splice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The TRq parameters `P` with the initial radius replaced by `r ∈ (0, Δ_max]`. -/
def trqWithΔ₀ (P : Optimization.TRqParams) (r : ℝ) (h0 : 0 < r) (h1 : r ≤ P.Δmax) :
    Optimization.TRqParams :=
  { P with Δ₀ := r, Δ₀_pos := h0, Δ₀_le_Δmax := h1 }

omit [NormedSpace ℝ E] in
/-- The number of indices `k < T + T'` satisfying `p` is the number below `T` plus the number of
`m < T'` with `p (T + m)`. -/
theorem card_filter_range_add (p : ℕ → Prop) [DecidablePred p] (T T' : ℕ) :
    ((Finset.range (T + T')).filter p).card =
      ((Finset.range T).filter p).card + ((Finset.range T').filter fun m => p (T + m)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_range_add _ _ _

/-- A Step-2 iteration fails the termination test of TRq. -/
theorem not_measureTestPasses_of_isTRqStep {D : FormalMultilinearSeries ℝ E ℝ} {S : Set E}
    {ς : ℝ} {q : ℕ} {ε : ℕ → ℝ} {δ Δ : ℝ} {d : ℕ → E} {j : ℕ} {s : E}
    (h : Optimization.IsTRqStep D S ς q ε δ Δ d j s) :
    ¬ Optimization.MeasureTestPasses (fun j => D.taylorDecrement j) q ς ε (fun _ => δ) d :=
  fun ht => absurd (ht j h.order_mem) (not_le.2 h.lt_taylorDecrement)

open Classical in
/-- **Splicing an explicit prefix with a TRq-SC run.** If `T` explicit iterations
`(x_k, s_k, Δ_k, j_k, d_k)`, `k < T`, starting from `Δ_0 = Δ₀`, satisfy Steps 1–4 of
Algorithm 12.2.1 (with feasible steps), and a TRq-SC run starts at `x_T` with initial radius
`r = Δ_T`, the concatenation is a TRq-SC run. It does not terminate before `T + T'` if the tail does
not terminate before `T'`, its successful iterations below `T + T'` are those of the prefix
and of the tail below `T'`, and it agrees with the prefix up to `T`, radius included. -/
theorem trq_splice {F : E → ℝ} {X : Set E} {P : Optimization.TRqParams} {q : ℕ} {ε : ℕ → ℝ}
    {ϑ : ℝ} {T : ℕ} {xp sp : ℕ → E} {Δp : ℕ → ℝ} {jp : ℕ → ℕ} {dp : ℕ → ℕ → E}
    (h0 : Δp 0 = P.Δ₀) {r : ℝ} (hr : Δp T = r) (hpos : 0 < r) (hmax : r ≤ P.Δmax)
    (hstep : ∀ k < T, Optimization.IsTRqStep (ftaylorSeries ℝ F (xp k)) {e | xp k + e ∈ X} P.ς q
      ε (min (Δp k) ϑ) (Δp k) (dp k) (jp k) (sp k))
    (hacc : ∀ k < T, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio F (xp k) (sp k)
        ((ftaylorSeries ℝ F (xp k)).taylorDecrement (jp k) (sp k)))
      (xp k) (sp k) (xp (k + 1)) (Δp k) (Δp (k + 1)))
    (hwit : ∀ k < T, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ F (xp k)).taylorDecrement j) (min (Δp k) ϑ) {e | xp k + e ∈ X} P.ς
        (dp k j))
    (hcap : ∀ k < T, Δp (k + 1) ≤ P.Δmax)
    {y sy : ℕ → E} {Δy : ℕ → ℝ} {jy : ℕ → ℕ} {dy : ℕ → ℕ → E} (hy0 : y 0 = xp T)
    (hy : Chapter12.algorithm_12_2_1_feasible F X (trqWithΔ₀ P r hpos hmax) q ε ϑ y sy Δy jy dy)
    {T' c : ℕ} (hyns : ∀ k < T', ¬ Chapter12.trqStop F P q ε ϑ y Δy dy k)
    (hyc : c ≤ ((Finset.range T').filter fun k => P.η₁ ≤ Chapter12.trqRho F y sy jy k).card) :
    ∃ (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E), x 0 = xp 0 ∧
      Chapter12.algorithm_12_2_1_feasible F X P q ε ϑ x s Δ jk d ∧
      (∀ k < T + T', ¬ Chapter12.trqStop F P q ε ϑ x Δ d k) ∧
      ((Finset.range T).filter fun k => P.η₁ ≤ Optimization.reductionRatio F (xp k) (sp k)
          ((ftaylorSeries ℝ F (xp k)).taylorDecrement (jp k) (sp k))).card + c ≤
        ((Finset.range (T + T')).filter fun k => P.η₁ ≤ Chapter12.trqRho F x s jk k).card ∧
      (∀ k ≤ T, x k = xp k) ∧ Δ T = Δp T := by
  obtain ⟨x, hx⟩ : ∃ x : ℕ → E, ∀ k, x k = if k < T then xp k else y (k - T) := ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → E, ∀ k, s k = if k < T then sp k else sy (k - T) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → ℝ, ∀ k, Δ k = if k < T then Δp k else Δy (k - T) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨jk, hjk⟩ : ∃ jk : ℕ → ℕ, ∀ k, jk k = if k < T then jp k else jy (k - T) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℕ → E, ∀ k, d k = if k < T then dp k else dy (k - T) :=
    ⟨_, fun _ => rfl⟩
  have hΔy0 : Δy 0 = Δp T := hy.toIsTRRun.delta_zero.trans hr.symm
  -- the prefix and the tail
  have hxl : ∀ k, k ≤ T → x k = xp k := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hx, ite_eq_left hk]
    · rw [hx, ite_eq_right (lt_irrefl _), Nat.sub_self, hy0]
  have hΔl : ∀ k, k ≤ T → Δ k = Δp k := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hΔ, ite_eq_left hk]
    · rw [hΔ, ite_eq_right (lt_irrefl _), Nat.sub_self, hΔy0]
  have hsl : ∀ k < T, s k = sp k := fun k hk => by rw [hs, ite_eq_left hk]
  have hjl : ∀ k < T, jk k = jp k := fun k hk => by rw [hjk, ite_eq_left hk]
  have hdl : ∀ k < T, d k = dp k := fun k hk => by rw [hd, ite_eq_left hk]
  have hxr : ∀ m, x (T + m) = y m := fun m => by
    rw [hx, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hΔr : ∀ m, Δ (T + m) = Δy m := fun m => by
    rw [hΔ, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hsr : ∀ m, s (T + m) = sy m := fun m => by
    rw [hs, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hjr : ∀ m, jk (T + m) = jy m := fun m => by
    rw [hjk, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hdr : ∀ m, d (T + m) = dy m := fun m => by
    rw [hd, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hcases : ∀ k, k < T ∨ ∃ m, k = T + m := fun k => by
    rcases lt_or_ge k T with h | h
    · exact Or.inl h
    · exact Or.inr ⟨k - T, by omega⟩
  -- the tests
  have hstopl : ∀ k < T, ¬ Chapter12.trqStop F P q ε ϑ x Δ d k := fun k hk h => by
    have hst := hstep k hk
    change Optimization.MeasureTestPasses
      (fun j => (ftaylorSeries ℝ F (x k)).taylorDecrement j) q P.ς ε
      (fun _ => min (Δ k) ϑ) (d k) at h
    rw [hxl k hk.le, hΔl k hk.le, hdl k hk] at h
    exact not_measureTestPasses_of_isTRqStep hst h
  have hstopr : ∀ m, Chapter12.trqStop F P q ε ϑ x Δ d (T + m) ↔
      Chapter12.trqStop F (trqWithΔ₀ P r hpos hmax) q ε ϑ y Δy dy m := fun m => by
    change Optimization.MeasureTestPasses
      (fun j => (ftaylorSeries ℝ F (x (T + m))).taylorDecrement j) q P.ς ε
      (fun _ => min (Δ (T + m)) ϑ) (d (T + m)) ↔ _
    rw [hxr, hΔr, hdr]
    rfl
  have htail : ∀ m, (∀ i ≤ T + m, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i) →
      ∀ i ≤ m, ¬ Chapter12.trqStop F (trqWithΔ₀ P r hpos hmax) q ε ϑ y Δy dy i :=
    fun m hk i hi => (hstopr i).not.1 (hk (T + i) (by omega))
  have htail' : ∀ m, (∀ i < T + m, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i) →
      ∀ i < m, ¬ Chapter12.trqStop F (trqWithΔ₀ P r hpos hmax) q ε ϑ y Δy dy i :=
    fun m hk i hi => (hstopr i).not.1 (hk (T + i) (by omega))
  have hrun : Chapter12.algorithm_12_2_1_feasible F X P q ε ϑ x s Δ jk d := by
    refine ⟨⟨?_, fun k hk => ?_, fun k hk => ?_⟩, fun k hk j hj => ?_, fun k hk => ?_⟩
    · -- the initial radius
      rw [hΔl 0 (Nat.zero_le _), h0]
    · -- Step 2
      rcases hcases k with hkT | ⟨m, rfl⟩
      · rw [hxl k hkT.le, hΔl k hkT.le, hdl k hkT, hjl k hkT, hsl k hkT]
        exact hstep k hkT
      · rw [hxr, hΔr, hdr, hjr, hsr]
        exact hy.step m (htail m hk)
    · -- Steps 3–4
      change Optimization.TRAcceptance P.toTRParams
        (Optimization.trqRatio F (fun k => ftaylorSeries ℝ F (x k)) x s jk k)
        (x k) (s k) (x (k + 1)) (Δ k) (Δ (k + 1))
      rw [Optimization.trqRatio_eq]
      rcases hcases k with hkT | ⟨m, rfl⟩
      · rw [hxl k hkT.le, hΔl k hkT.le, hjl k hkT, hsl k hkT, hxl (k + 1) hkT,
          hΔl (k + 1) hkT]
        exact hacc k hkT
      · have := hy.accept m (htail m hk)
        rw [show T + m + 1 = T + (m + 1) by omega, hxr, hxr, hΔr, hΔr, hsr, hjr]
        exact this
    · -- Step 1
      rcases hcases k with hkT | ⟨m, rfl⟩
      · rw [hxl k hkT.le, hΔl k hkT.le, hdl k hkT]
        exact hwit k hkT j hj
      · have := hy.witness m (htail' m hk) j hj
        rw [hxr, hΔr, hdr]
        exact this
    · -- the cap
      change Δ (k + 1) ≤ P.Δmax
      rcases hcases k with hkT | ⟨m, rfl⟩
      · rw [hΔl (k + 1) hkT]; exact hcap k hkT
      · have := hy.cap m (htail m hk)
        rw [show T + m + 1 = T + (m + 1) by omega, hΔr]
        exact this
  refine ⟨x, s, Δ, jk, d, hxl 0 (Nat.zero_le _), hrun, fun k hk => ?_, ?_, hxl, hΔl T le_rfl⟩
  · rcases hcases k with hkT | ⟨m, rfl⟩
    · exact hstopl k hkT
    · exact (hstopr m).not.2 (hyns m (by omega))
  · rw [card_filter_range_add]
    gcongr ?_ + ?_
    · refine le_of_eq (congrArg Finset.card (Finset.filter_congr fun k hk => ?_))
      have hkT := Finset.mem_range.1 hk
      change P.η₁ ≤ Optimization.reductionRatio F (xp k) (sp k)
          ((ftaylorSeries ℝ F (xp k)).taylorDecrement (jp k) (sp k)) ↔
        P.η₁ ≤ Optimization.trqRatio F (fun k => ftaylorSeries ℝ F (x k)) x s jk k
      rw [Optimization.trqRatio_eq, hxl k hkT.le, hsl k hkT, hjl k hkT]
    · refine hyc.trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun m _ => ?_)))
      change P.η₁ ≤ Optimization.trqRatio F (fun k => ftaylorSeries ℝ F (y k)) y sy jy m ↔
        P.η₁ ≤ Optimization.trqRatio F (fun k => ftaylorSeries ℝ F (x k)) x s jk (T + m)
      rw [Optimization.trqRatio_eq, Optimization.trqRatio_eq, hxr, hsr, hjr]

end Splice

section Iterations

/-- The trust-region parameters of the example: `Δ₀ = Δ_max = 1`, `η₁ = 1/4`, `η₂ = 3/4`,
`γ₁ = 1/4`, `γ₂ = 1/2`, `γ₃ = 2`, `ς = 1/4`. -/
noncomputable def trqSlowParams : Optimization.TRqParams where
  Δ₀ := 1
  η₁ := 1 / 4
  η₂ := 3 / 4
  γ₁ := 1 / 4
  γ₂ := 1 / 2
  γ₃ := 2
  Δ₀_pos := one_pos
  η₁_pos := by norm_num
  η₁_le_η₂ := by norm_num
  η₂_lt_one := by norm_num
  γ₁_pos := by norm_num
  γ₁_le_γ₂ := by norm_num
  γ₂_lt_one := by norm_num
  one_le_γ₃ := by norm_num
  Δmax := 1
  ς := 1 / 4
  Δ₀_le_Δmax := le_rfl
  ς_pos := by norm_num
  ς_le_one := by norm_num

/-- The feasible set of the example: the closed half-plane `X = {v | v_1 ≥ 1}`. -/
def trqSlowX : Set ℝ² := {v | 1 ≤ v 0}

/-- The open half-plane `X₀ = {v | v_1 > 1/2} ⊇ X` of the assumptions. -/
def trqSlowX₀ : Set ℝ² := {v | 1 / 2 < v 0}

/-- `(a, b) + (c, d) ∈ X` when `a + c ≥ 1`. -/
theorem slowPt_add_mem {a b c d : ℝ} (h : 1 ≤ a + c) : slowPt a b + slowPt c d ∈ trqSlowX := by
  rw [slowPt_add]; exact h

/-- The successful iterations keep the radius. -/
theorem trqSlow_accept_succ {E : Type*} [NormedAddCommGroup E] {ρ Δ : ℝ} {x s x' : E}
    (hΔ : 0 ≤ Δ) (hρ : trqSlowParams.η₁ ≤ ρ) (hx : x' = x + s) :
    Optimization.TRAcceptance trqSlowParams.toTRParams ρ x s x' Δ Δ := by
  refine ⟨by rw [ite_eq_left hρ]; exact hx, ⟨fun _ => ⟨le_rfl, ?_⟩, fun _ _ => ⟨?_, le_rfl⟩,
    fun h => absurd h (not_lt.2 hρ)⟩⟩
  · change Δ ≤ 2 * Δ; linarith
  · change 1 / 2 * Δ ≤ Δ; linarith

/-- The unsuccessful iterations halve the radius. -/
theorem trqSlow_accept_unsucc {E : Type*} [NormedAddCommGroup E] {ρ Δ : ℝ} {x s : E}
    (hΔ : 0 ≤ Δ) (hρ : ρ < trqSlowParams.η₁) :
    Optimization.TRAcceptance trqSlowParams.toTRParams ρ x s x Δ (Δ / 2) := by
  have hρ' : ρ < 1 / 4 := hρ
  refine ⟨(ite_eq_right (not_le.2 hρ)).symm, ⟨fun h => absurd h (not_le.2 (hρ'.trans (by
    norm_num : (1 : ℝ) / 4 < 3 / 4))), fun h => absurd h (not_le.2 hρ), fun _ => ⟨?_, ?_⟩⟩⟩
  · change 1 / 4 * Δ ≤ Δ / 2; linarith
  · change Δ / 2 ≤ 1 / 2 * Δ; linarith

/-- A ratio is at least `η₁ = 1/4` when the actual decrease is at least a quarter of the
predicted one. -/
theorem trqSlow_ratio_ge_quarter {E : Type*} [NormedAddCommGroup E] {F : E → ℝ} {x s : E}
    {pred : ℝ} (hp : 0 < pred)
    (h : pred / 4 ≤ F x - F (x + s)) :
    trqSlowParams.η₁ ≤ Optimization.reductionRatio F x s pred := by
  change (1 / 4 : ℝ) ≤ _
  rw [Optimization.reductionRatio_def, le_div_iff₀ hp]; linarith

/-- A ratio is below `η₁ = 1/4` when the actual decrease is below a quarter of the predicted
one. -/
theorem trqSlow_ratio_lt_quarter {E : Type*} [NormedAddCommGroup E] {F : E → ℝ} {x s : E}
    {pred : ℝ} (hp : 0 < pred)
    (h : F x - F (x + s) < pred / 4) :
    Optimization.reductionRatio F x s pred < trqSlowParams.η₁ := by
  change _ < (1 / 4 : ℝ)
  rw [Optimization.reductionRatio_def, div_lt_iff₀ hp]; linarith

/-- `ΔT_1(v, d) ≤ (A(a) + |b|) δ` at `v = (a, b)`, `a > 0`, for `‖d‖ ≤ δ`. -/
theorem trqSlow_ΔT1_le {a b δ : ℝ} (ha : 0 < a) {d : ℝ²} (hd : ‖d‖ ≤ δ) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 1 d ≤
      (trqSlowA a + |b|) * δ := by
  rw [trqSlow_ΔT1 (by simpa using ha)]
  simp only [slowPt_apply_zero, slowPt_apply_one]
  have h0 := (EuclideanSpace.abs_apply_le_norm d 0).trans hd
  have h1 := (EuclideanSpace.abs_apply_le_norm d 1).trans hd
  have hA := (trqSlowA_pos ha).le
  have e0 : trqSlowA a * d 0 ≤ trqSlowA a * δ :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hA).trans (mul_le_mul_of_nonneg_left h0 hA)
  have e1 : -(b * d 1) ≤ |b| * δ := by
    have := neg_abs_le (b * d 1)
    rw [abs_mul] at this
    nlinarith [abs_nonneg b]
  nlinarith

/-- `ΔT_2(v, d) ≤ ΔT_1(v, d)` at `v = (a, b)`, `a > 0` (the Hessian is positive semidefinite). -/
theorem trqSlow_ΔT2_le_ΔT1 {a b : ℝ} (ha : 0 < a) (d : ℝ²) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 2 d ≤
      (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 1 d := by
  rw [trqSlow_ΔT1 (by simpa using ha), trqSlow_ΔT2 (by simpa using ha)]
  have := trqSlowB_nonneg (t := (slowPt a b) 0) (by simpa using ha)
  nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]

/-- `ΔT_2(v, d) ≤ A(a) δ + b²/2` at `v = (a, b)`, `a > 0`, for `‖d‖ ≤ δ`. -/
theorem trqSlow_ΔT2_le {a b δ : ℝ} (ha : 0 < a) {d : ℝ²} (hd : ‖d‖ ≤ δ) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 2 d ≤
      trqSlowA a * δ + b ^ 2 / 2 := by
  rw [trqSlow_ΔT2 (by simpa using ha)]
  simp only [slowPt_apply_zero, slowPt_apply_one]
  have h0 := (EuclideanSpace.abs_apply_le_norm d 0).trans hd
  have hA := (trqSlowA_pos ha).le
  have hB := trqSlowB_nonneg ha
  have e0 : trqSlowA a * d 0 ≤ trqSlowA a * δ :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hA).trans (mul_le_mul_of_nonneg_left h0 hA)
  nlinarith [sq_nonneg (d 1 + b), mul_nonneg hB (sq_nonneg (d 0))]

/-- The measure bound behind the Step-1 displacements. -/
theorem trqSlow_isApproxMeasureStep {a b δ B : ℝ} (ha : 1 ≤ a) (hδ : 0 ≤ δ) {j : ℕ} {d : ℝ²}
    (hdδ : ‖d‖ ≤ δ) (hdX : 1 ≤ a + d 0)
    (hB : ∀ e : ℝ², ‖e‖ ≤ δ →
      (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement j e ≤ B)
    (hd : B / 4 ≤ (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement j d) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement j) δ
      {e | slowPt a b + e ∈ trqSlowX} trqSlowParams.ς d := by
  have hd' : d = slowPt (d 0) (d 1) := by ext i; fin_cases i <;> rfl
  refine ⟨⟨mem_closedBall_zero_iff.2 hdδ, ?_⟩, ?_⟩
  · change slowPt a b + d ∈ trqSlowX
    rw [hd']; exact slowPt_add_mem hdX
  · have hm : Optimization.decrementMeasure
        ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement j) δ
        {e | slowPt a b + e ∈ trqSlowX} ≤ B :=
      Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, by
        change slowPt a b + 0 ∈ trqSlowX
        rw [add_zero]; exact ha⟩ fun e he => hB e (mem_closedBall_zero_iff.1 he.1)
    change 1 / 4 * _ ≤ _
    linarith

end Iterations

section Steps

/-- `ΔT_1((a, b), (σ, τ)) = A(a) σ - b τ` for `a > 0`. -/
theorem trqSlow_ΔT1_pt {a : ℝ} (ha : 0 < a) (b σ τ : ℝ) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 1 (slowPt σ τ) =
      trqSlowA a * σ - b * τ := by
  rw [trqSlow_ΔT1 (by simpa using ha)]; simp

/-- `ΔT_2((a, b), (σ, τ)) = A(a) σ - b τ - (B(a) σ² + τ²)/2` for `a > 0`. -/
theorem trqSlow_ΔT2_pt {a : ℝ} (ha : 0 < a) (b σ τ : ℝ) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 2 (slowPt σ τ) =
      trqSlowA a * σ - b * τ - (trqSlowB a * σ ^ 2 + τ ^ 2) / 2 := by
  rw [trqSlow_ΔT2 (by simpa using ha)]; simp

/-- Unused orders: some approximate optimality displacement exists at every point of `X`. -/
theorem trqSlow_exists_witness : ∃ W : ℝ² → ℝ → ℕ → ℝ², ∀ (y : ℝ²) (δ : ℝ) (j : ℕ),
    y ∈ trqSlowX → 0 ≤ δ → Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) y).taylorDecrement j) δ {e | y + e ∈ trqSlowX}
        trqSlowParams.ς (W y δ j) := by
  have hX : IsClosed trqSlowX :=
    isClosed_le continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)
  have hW : ∀ (y : ℝ²) (δ : ℝ) (j : ℕ), ∃ w : ℝ², y ∈ trqSlowX → 0 ≤ δ →
      Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ (phi2 trqSlowC) y).taylorDecrement j) δ
        {e | y + e ∈ trqSlowX} trqSlowParams.ς w := by
    intro y δ j
    by_cases h : y ∈ trqSlowX ∧ 0 ≤ δ
    · obtain ⟨w, hw⟩ := Optimization.exists_isApproxMeasureStep_taylorDecrement
        (ftaylorSeries ℝ (phi2 trqSlowC) y) j (hX.preimage (continuous_const.add continuous_id))
        (by change y + 0 ∈ trqSlowX; rw [add_zero]; exact h.1) h.2 trqSlowParams.ς_le_one
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose W hW using hW
  exact ⟨W, hW⟩

/-- On the axis, `(δ/4, 0)` is an approximate first-order displacement. -/
theorem trqSlow_wit_axis_one {a δ : ℝ} (ha : 2 ≤ a) (hδ : 0 ≤ δ) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a 0)).taylorDecrement 1) δ
      {e | slowPt a 0 + e ∈ trqSlowX} trqSlowParams.ς (slowPt (δ / 4) 0) := by
  have ha0 : 0 < a := by linarith
  refine trqSlow_isApproxMeasureStep (B := trqSlowA a * δ) (by linarith) hδ
    ((norm_slowPt_le _ _).trans (by rw [abs_of_nonneg (by linarith), abs_zero]; linarith))
    (by simp; linarith) (fun e he => (trqSlow_ΔT1_le ha0 he).trans_eq (by simp)) ?_
  rw [trqSlow_ΔT1_pt ha0]; ring_nf; rfl

/-- On the axis, `(δ, 0)` is an approximate second-order displacement for `δ ≤ 1`. -/
theorem trqSlow_wit_axis_two {a δ : ℝ} (ha : 2 ≤ a) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a 0)).taylorDecrement 2) δ
      {e | slowPt a 0 + e ∈ trqSlowX} trqSlowParams.ς (slowPt δ 0) := by
  have ha0 : 0 < a := by linarith
  refine trqSlow_isApproxMeasureStep (B := trqSlowA a * δ) (by linarith) hδ
    ((norm_slowPt_le _ _).trans (by rw [abs_of_nonneg hδ, abs_zero, add_zero]))
    (by simp; linarith) (fun e he => ((trqSlow_ΔT2_le_ΔT1 ha0 e).trans
      (trqSlow_ΔT1_le ha0 he)).trans_eq (by simp)) ?_
  rw [trqSlow_ΔT2_pt ha0]
  have := trqSlowB_mul_le ha hδ1
  have := (trqSlowA_pos ha0).le
  nlinarith

/-- At `(a, y)` with `A(a) ≤ y`, `(0, -δ)` is an approximate first-order displacement. -/
theorem trqSlow_wit_shrink_one {a y δ : ℝ} (ha : 2 ≤ a) (hy : 0 ≤ y) (hAy : trqSlowA a ≤ y)
    (hδ : 0 ≤ δ) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a y)).taylorDecrement 1) δ
      {e | slowPt a y + e ∈ trqSlowX} trqSlowParams.ς (slowPt 0 (-δ)) := by
  have ha0 : 0 < a := by linarith
  refine trqSlow_isApproxMeasureStep (B := (trqSlowA a + |y|) * δ) (by linarith) hδ
    ((norm_slowPt_le _ _).trans (by rw [abs_zero, abs_neg, abs_of_nonneg hδ, zero_add]))
    (by simp; linarith) (fun e he => trqSlow_ΔT1_le ha0 he) ?_
  rw [trqSlow_ΔT1_pt ha0, abs_of_nonneg hy]
  nlinarith

/-- At `(a, y)` with `0 ≤ y ≤ δ ≤ 1`, `(δ/2, -min(y, δ/2))` is an approximate second-order
displacement. -/
theorem trqSlow_wit_shrink_two {a y δ : ℝ} (ha : 2 ≤ a) (hy : 0 ≤ y) (hyδ : y ≤ δ) (hδ1 : δ ≤ 1) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a y)).taylorDecrement 2) δ
      {e | slowPt a y + e ∈ trqSlowX} trqSlowParams.ς (slowPt (δ / 2) (-min y (δ / 2))) := by
  have ha0 : 0 < a := by linarith
  have hδ : 0 ≤ δ := hy.trans hyδ
  have hb0 : 0 ≤ min y (δ / 2) := le_min hy (by linarith)
  have hb1 : min y (δ / 2) ≤ y := min_le_left _ _
  have hb2 : min y (δ / 2) ≤ δ / 2 := min_le_right _ _
  have hb3 : y / 2 ≤ min y (δ / 2) := le_min (by linarith) (by linarith)
  have hn : ‖slowPt (δ / 2) (-min y (δ / 2))‖ ≤ δ := by
    refine (norm_slowPt_le _ _).trans ?_
    rw [abs_neg, abs_of_nonneg hb0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ δ / 2)]
    linarith
  refine trqSlow_isApproxMeasureStep (B := trqSlowA a * δ + y ^ 2 / 2) (by linarith) hδ hn
    (by simp; linarith) (fun e he => trqSlow_ΔT2_le ha0 he) ?_
  rw [trqSlow_ΔT2_pt ha0]
  have hB := trqSlowB_mul_le ha hδ1
  have hA := (trqSlowA_pos ha0).le
  have hB0 := trqSlowB_nonneg ha0
  set b := min y (δ / 2)
  have h1 : trqSlowB a * (δ / 2) ^ 2 ≤ trqSlowA a * δ / 4 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hb1) (sub_nonneg.2 hb3)]

/-- **A first-order step on the axis**: at `(a, 0)` with `ε_1 < A(a)` the first order fails
(Step-1 displacement `(δ/4, 0)`), and every feasible `(h, τ)` in the trust region with
`h ≥ δ/4` is a valid step. -/
theorem trqSlow_step_axis_one {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ} {a δ Δ h τ : ℝ} (ha : 2 ≤ a)
    (hδ : 0 < δ) (hε : ε 1 < trqSlowA a) (hh : δ / 4 ≤ h) (hs : ‖slowPt h τ‖ ≤ Δ)
    {d : ℕ → ℝ²} (hd1 : d 1 = slowPt (δ / 4) 0) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a 0))
      {e | slowPt a 0 + e ∈ trqSlowX} trqSlowParams.ς q ε δ Δ d 1 (slowPt h τ) := by
  have ha0 : 0 < a := by linarith
  have hA := trqSlowA_pos ha0
  refine ⟨Finset.mem_Icc.2 ⟨le_rfl, hq⟩, ?_, fun i hi hi1 => absurd hi1
    (by have := (Finset.mem_Icc.1 hi).1; omega), ⟨mem_closedBall_zero_iff.2 hs,
      slowPt_add_mem (by linarith)⟩, ?_⟩
  · rw [hd1, trqSlow_ΔT1_pt ha0]
    change (1 / 4 : ℝ) * ε 1 * δ ^ 1 / ((1 : ℕ)! : ℝ) < _
    norm_num
    nlinarith
  · rw [hd1, trqSlow_ΔT1_pt ha0, trqSlow_ΔT1_pt ha0]
    nlinarith

/-- **A second-order step on the axis**: at `(a, 0)` with `A(a) ≤ ε_1` and `ε_2 δ < 4 A(a)` the
first order passes, the second order fails, and the step is `(δ, 0)`. -/
theorem trqSlow_step_axis_two {q : ℕ} (hq : 2 ≤ q) {ε : ℕ → ℝ} {a δ Δ : ℝ} (ha : 2 ≤ a)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδΔ : δ ≤ Δ) (hε1 : trqSlowA a ≤ ε 1)
    (hε2 : ε 2 * δ < 4 * trqSlowA a) {d : ℕ → ℝ²} (hd1 : d 1 = slowPt (δ / 4) 0)
    (hd2 : d 2 = slowPt δ 0) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a 0))
      {e | slowPt a 0 + e ∈ trqSlowX} trqSlowParams.ς q ε δ Δ d 2 (slowPt δ 0) := by
  have ha0 : 0 < a := by linarith
  have hA := trqSlowA_pos ha0
  have hB := trqSlowB_mul_le ha hδ1
  refine ⟨Finset.mem_Icc.2 ⟨by norm_num, hq⟩, ?_, fun i hi hi2 => ?_, ⟨mem_closedBall_zero_iff.2
    ((norm_slowPt_le _ _).trans (by rw [abs_of_pos hδ, abs_zero, add_zero]; exact hδΔ)),
      slowPt_add_mem (by linarith)⟩, by rw [hd2]⟩
  · rw [hd2, trqSlow_ΔT2_pt ha0]
    change (1 / 4 : ℝ) * ε 2 * δ ^ 2 / ((2 : ℕ)! : ℝ) < _
    norm_num [Nat.factorial]
    nlinarith
  · have hi1 : i = 1 := by have := (Finset.mem_Icc.1 hi).1; omega
    subst hi1
    rw [hd1, trqSlow_ΔT1_pt ha0]
    change _ ≤ (1 / 4 : ℝ) * ε 1 * δ ^ 1 / ((1 : ℕ)! : ℝ)
    norm_num
    nlinarith

/-- **A first-order step off the axis**: at `(a, y)` with `ε_1 < 4y` the first order fails
(Step-1 displacement `(0, -δ)`), and the step is `(0, -δ)`. -/
theorem trqSlow_step_shrink {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ} {a y δ Δ : ℝ} (ha : 2 ≤ a)
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) (hε : ε 1 < 4 * y) {d : ℕ → ℝ²} (hd1 : d 1 = slowPt 0 (-δ)) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a y))
      {e | slowPt a y + e ∈ trqSlowX} trqSlowParams.ς q ε δ Δ d 1 (slowPt 0 (-δ)) := by
  have ha0 : 0 < a := by linarith
  refine ⟨Finset.mem_Icc.2 ⟨le_rfl, hq⟩, ?_, fun i hi hi1 => absurd hi1
    (by have := (Finset.mem_Icc.1 hi).1; omega), ⟨mem_closedBall_zero_iff.2
      ((norm_slowPt_le _ _).trans (by rw [abs_zero, abs_neg, abs_of_pos hδ, zero_add]; exact hδΔ)),
      slowPt_add_mem (by linarith)⟩, by rw [hd1]⟩
  rw [hd1, trqSlow_ΔT1_pt ha0]
  change (1 / 4 : ℝ) * ε 1 * δ ^ 1 / ((1 : ℕ)! : ℝ) < _
  norm_num
  nlinarith

/-- A step `(h, τ)` from the axis point `(a, 0)` with `0 < h ≤ 1/2`, `τ² ≤ A(a) h/4` and
predicted decrease `pred ∈ (0, A(a) h]` is successful. -/
theorem trqSlow_ratio_axis {a h τ pred : ℝ} (ha : 2 ≤ a) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2)
    (hp0 : 0 < pred) (hp : pred ≤ trqSlowA a * h) (hτ : τ ^ 2 ≤ trqSlowA a * h / 4) :
    trqSlowParams.η₁ ≤ Optimization.reductionRatio (phi2 trqSlowC) (slowPt a 0) (slowPt h τ) pred
      := by
  refine trqSlow_ratio_ge_quarter hp0 ?_
  rw [slowPt_add, phi2_trqSlowC_slowPt (by linarith), phi2_trqSlowC_slowPt (by linarith)]
  have := trqSlow_decrease_ge ha hh0 hh
  simp only [zero_add]
  nlinarith

/-- The step `(0, -δ)` from `(a, y)` with `2y ≤ δ` is unsuccessful. -/
theorem trqSlow_ratio_shrink_unsucc {a y δ : ℝ} (ha : 0 ≤ a) (hy : 0 < y) (hyδ : 2 * y ≤ δ) :
    Optimization.reductionRatio (phi2 trqSlowC) (slowPt a y) (slowPt 0 (-δ)) (y * δ) <
      trqSlowParams.η₁ := by
  refine trqSlow_ratio_lt_quarter (by nlinarith) ?_
  rw [slowPt_add, phi2_trqSlowC_slowPt ha, phi2_trqSlowC_slowPt (by linarith)]
  simp only [add_zero]
  nlinarith

/-- The step `(0, -y)` from `(a, y)` is successful. -/
theorem trqSlow_ratio_shrink_succ {a y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) :
    trqSlowParams.η₁ ≤
      Optimization.reductionRatio (phi2 trqSlowC) (slowPt a y) (slowPt 0 (-y)) (y * y) := by
  refine trqSlow_ratio_ge_quarter (by nlinarith) ?_
  rw [slowPt_add, phi2_trqSlowC_slowPt ha, phi2_trqSlowC_slowPt (by linarith)]
  simp only [add_zero]
  nlinarith

end Steps

section Phases

/-- The parameters `trqSlowParams` with initial radius `r ∈ (0, 1]`. -/
noncomputable abbrev trqSlowParamsAt (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1) : Optimization.TRqParams :=
  trqWithΔ₀ trqSlowParams r h0 h1

/-- `X` is closed. -/
theorem isClosed_trqSlowX : IsClosed trqSlowX :=
  isClosed_le continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)

/-- `(a, b) ∈ X` for `a ≥ 1`. -/
theorem slowPt_mem_trqSlowX {a b : ℝ} (ha : 1 ≤ a) : slowPt a b ∈ trqSlowX := ha

open Classical in
/-- **The slow phase.** From `(a, 0)`, `a ≥ 2`, with radius `δ ≤ 1/2`, `A(a) ≤ ε_1` and
`ε_2 δ < 4 A(a + k δ)` for `k < K`, the `K` steps `(δ, 0)` are successful second-order iterations;
any TRq-SC run continues afterwards. -/
theorem trqSlow_slow_phase {q : ℕ} (hq : 2 ≤ q) {ε : ℕ → ℝ} {a δ : ℝ} (ha : 2 ≤ a) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) (hε1 : trqSlowA a ≤ ε 1) {K : ℕ}
    (hK : ∀ k < K, ε 2 * δ < 4 * trqSlowA (a + k * δ)) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²), x 0 = slowPt a 0 ∧
      Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX
        (trqSlowParamsAt δ hδ0 (by linarith)) q ε 1 x s Δ jk d ∧
      (∀ k < K, ¬ Chapter12.trqStop (phi2 trqSlowC) (trqSlowParamsAt δ hδ0 (by linarith)) q ε 1 x
        Δ d k) ∧
      K ≤ ((Finset.range K).filter fun k =>
        (trqSlowParamsAt δ hδ0 (by linarith)).η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k).card
        := by
  obtain ⟨W, hW⟩ := trqSlow_exists_witness
  have hδ1' : δ ≤ 1 := by linarith
  set P := trqSlowParamsAt δ hδ0 hδ1' with hP
  have hak : ∀ k : ℕ, 2 ≤ a + k * δ := fun k => by
    have : 0 ≤ (k : ℝ) * δ := by positivity
    linarith
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k = slowPt (a + k * δ) 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k = fun j => if j = 1 then slowPt (δ / 4) 0
      else if j = 2 then slowPt δ 0 else W (xp k) δ j := ⟨_, fun _ => rfl⟩
  have hmin : min δ 1 = δ := min_eq_left hδ1'
  have hstep : ∀ k < K, Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (xp k))
      {e | xp k + e ∈ trqSlowX} P.ς q ε (min ((fun _ => δ) k) 1) ((fun _ => δ) k) (dp k)
      ((fun _ => 2) k) ((fun _ => slowPt δ 0) k) := fun k hk => by
    simp only [hmin, hxp]
    have hle : a ≤ a + k * δ := by have : 0 ≤ (k : ℝ) * δ := by positivity
                                   linarith
    exact trqSlow_step_axis_two hq (hak k) hδ0 hδ1' le_rfl
      ((trqSlowA_anti (by linarith) hle).trans hε1) (hK k hk)
      (by rw [hdp]; simp) (by rw [hdp]; simp)
  have hpred : ∀ k, 0 < (ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement 2 (slowPt δ 0) ∧
      (ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement 2 (slowPt δ 0) ≤
        trqSlowA (a + k * δ) * δ := fun k => by
    have h0 : 0 < a + k * δ := by linarith [hak k]
    rw [hxp, trqSlow_ΔT2_pt h0]
    have := trqSlowB_mul_le (hak k) hδ1'
    have := trqSlowA_pos h0
    have := trqSlowB_nonneg h0
    constructor <;> nlinarith
  have hacc : ∀ k < K, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio (phi2 trqSlowC) (xp k) ((fun _ => slowPt δ 0) k)
        ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement ((fun _ => 2) k)
          ((fun _ => slowPt δ 0) k)))
      (xp k) ((fun _ => slowPt δ 0) k) (xp (k + 1)) ((fun _ => δ) k) ((fun _ => δ) (k + 1)) :=
    fun k _ => by
    refine trqSlow_accept_succ hδ0.le ?_ (by rw [hxp, hxp, slowPt_add]; push_cast; ring_nf)
    have := hpred k
    rw [hxp] at this ⊢
    have hA := (trqSlowA_pos (by linarith [hak k] : (0 : ℝ) < a + k * δ)).le
    exact trqSlow_ratio_axis (hak k) hδ0.le hδ1 this.1 this.2 (by
      rw [zero_pow two_ne_zero]; positivity)
  have hwit : ∀ k < K, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement j) (min ((fun _ => δ) k) 1)
      {e | xp k + e ∈ trqSlowX} P.ς (dp k j) := fun k _ j _ => by
    simp only [hmin]
    rw [hdp]
    by_cases hj1 : j = 1
    · subst hj1; simp only [↓reduceIte]; rw [hxp]; exact trqSlow_wit_axis_one (hak k) hδ0.le
    · by_cases hj2 : j = 2
      · subst hj2; simp only [↓reduceIte]; rw [hxp]
        exact trqSlow_wit_axis_two (hak k) hδ0.le hδ1'
      · simp only [hj1, hj2, ↓reduceIte]
        exact hW _ _ _ (by rw [hxp]; exact slowPt_mem_trqSlowX (by linarith [hak k])) hδ0.le
  obtain ⟨y, sy, Δy, jy, dy, hy0, hy⟩ := exists_algorithm_12_2_1_feasible
    isClosed_trqSlowX (phi2 trqSlowC) (trqWithΔ₀ P δ hδ0 hδ1') q ε zero_le_one
    (show xp K ∈ trqSlowX by rw [hxp]; exact slowPt_mem_trqSlowX (by linarith [hak K]))
  obtain ⟨x, s, Δ, jk, d, hx0, hrun, hns, hcount, -, -⟩ := trq_splice (T := K) (T' := 0) (c := 0)
    (P := P) (F := phi2 trqSlowC) (X := trqSlowX) (q := q) (ε := ε) (ϑ := 1) (xp := xp)
    (sp := fun _ => slowPt δ 0) (Δp := fun _ => δ) (jp := fun _ => 2) (dp := dp) rfl rfl hδ0
    hδ1' hstep hacc hwit (fun _ _ => hδ1') hy0 hy (fun _ h => absurd h (Nat.not_lt_zero _))
    (Nat.zero_le _)
  refine ⟨x, s, Δ, jk, d, by rw [hx0, hxp]; simp, hrun, hns, le_trans ?_ hcount⟩
  rw [add_zero]
  refine le_of_eq ?_
  rw [Finset.filter_true_of_mem fun k hk => ?_, Finset.card_range]
  have := hpred k
  rw [hxp] at this ⊢
  have hA := (trqSlowA_pos (by linarith [hak k] : (0 : ℝ) < a + k * δ)).le
  exact trqSlow_ratio_axis (hak k) hδ0.le hδ1 this.1 this.2 (by
    rw [zero_pow two_ne_zero]; positivity)

open Classical in
/-- **The shrinking phase.** At `(a, y)`, `a ≥ 2`, `y = 2^{-N}`, `A(a) ≤ y`, `ε_1 < 4y`, starting
from the radius `1`: `N` unsuccessful first-order iterations `(0, -Δ)` halve the radius down to
`y`, and a successful one reaches `(a, 0)` keeping the radius `y`; any run from `(a, 0)` with
initial radius `y` continues. -/
theorem trqSlow_shrink_phase {q : ℕ} (hq : 2 ≤ q) {ε : ℕ → ℝ} {a y : ℝ} {N : ℕ} (ha : 2 ≤ a)
    (hyN : y = (1 / 2) ^ N) (hy0 : 0 < y) (hy1 : y ≤ 1) (hAy : trqSlowA a ≤ y)
    (hε : ε 1 < 4 * y) {xt st : ℕ → ℝ²} {Δt : ℕ → ℝ} {jt : ℕ → ℕ} {dt : ℕ → ℕ → ℝ²}
    (hxt0 : xt 0 = slowPt a 0)
    (hrun : Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX
      (trqSlowParamsAt y hy0 hy1) q ε 1 xt st Δt jt dt) {T' c : ℕ}
    (hns : ∀ k < T', ¬ Chapter12.trqStop (phi2 trqSlowC) (trqSlowParamsAt y hy0 hy1) q ε 1 xt Δt
      dt k)
    (hc : c ≤ ((Finset.range T').filter fun k =>
      (trqSlowParamsAt y hy0 hy1).η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) xt st jt k).card) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²), x 0 = slowPt a y ∧
      Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX
        (trqSlowParamsAt 1 one_pos le_rfl) q ε 1 x s Δ jk d ∧
      (∀ k < N + 1 + T', ¬ Chapter12.trqStop (phi2 trqSlowC) (trqSlowParamsAt 1 one_pos le_rfl) q
        ε 1 x Δ d k) ∧
      c ≤ ((Finset.range (N + 1 + T')).filter fun k =>
        (trqSlowParamsAt 1 one_pos le_rfl).η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k).card
        := by
  obtain ⟨W, hW⟩ := trqSlow_exists_witness
  set P := trqSlowParamsAt 1 one_pos le_rfl with hP
  have ha0 : 0 < a := by linarith
  have hmemy : slowPt a y ∈ trqSlowX := slowPt_mem_trqSlowX (by linarith)
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k = if k ≤ N then slowPt a y else slowPt a 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Δp, hΔp⟩ : ∃ Δp : ℕ → ℝ, ∀ k, Δp k = (1 / 2 : ℝ) ^ (min k N) := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k = fun j => if j = 1 then
      slowPt 0 (-(1 / 2 : ℝ) ^ k) else if j = 2 then
      slowPt ((1 / 2 : ℝ) ^ k / 2) (-min y ((1 / 2 : ℝ) ^ k / 2))
      else W (slowPt a y) ((1 / 2 : ℝ) ^ k) j := ⟨_, fun _ => rfl⟩
  have hxpl : ∀ k < N + 1, xp k = slowPt a y := fun k hk => by
    rw [hxp, ite_eq_left (by omega)]
  have hΔpl : ∀ k < N + 1, Δp k = (1 / 2 : ℝ) ^ k := fun k hk => by
    rw [hΔp, min_eq_left (by omega)]
  have hpow0 : ∀ k : ℕ, 0 < (1 / 2 : ℝ) ^ k := fun k => by positivity
  have hpow1 : ∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hyk : ∀ k < N + 1, y ≤ (1 / 2 : ℝ) ^ k := fun k hk => by
    rw [hyN]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hstep : ∀ k < N + 1, Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (xp k))
      {e | xp k + e ∈ trqSlowX} P.ς q ε (min (Δp k) 1) (Δp k) (dp k) ((fun _ => 1) k)
      ((fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) k) := fun k hk => by
    rw [hxpl k hk, hΔpl k hk, min_eq_left (hpow1 k)]
    exact trqSlow_step_shrink (by omega) ha (hpow0 k) le_rfl hε (by rw [hdp]; simp)
  have hacc : ∀ k < N + 1, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio (phi2 trqSlowC) (xp k) ((fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) k)
        ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement ((fun _ => 1) k)
          ((fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) k)))
      (xp k) ((fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) k) (xp (k + 1)) (Δp k) (Δp (k + 1)) :=
    fun k hk => by
    simp only
    rw [hxpl k hk, trqSlow_ΔT1_pt ha0, hΔpl k hk]
    have hpred : trqSlowA a * 0 - y * -(1 / 2 : ℝ) ^ k = y * (1 / 2 : ℝ) ^ k := by ring
    rw [hpred]
    rcases Nat.lt_or_ge k N with hkN | hkN
    · rw [hxpl (k + 1) (by omega), hΔpl (k + 1) (by omega), pow_succ, ← div_eq_mul_one_div]
      refine trqSlow_accept_unsucc (hpow0 k).le (trqSlow_ratio_shrink_unsucc ha0.le hy0 ?_)
      have := hyk (k + 1) (by omega)
      rw [pow_succ] at this
      linarith
    · have hkN' : k = N := by omega
      subst hkN'
      have e1 : xp (k + 1) = slowPt a 0 := by rw [hxp, ite_eq_right (by omega)]
      have e2 : Δp (k + 1) = (1 / 2 : ℝ) ^ k := by rw [hΔp, min_eq_right (by omega)]
      rw [e1, e2, ← hyN]
      exact trqSlow_accept_succ hy0.le (trqSlow_ratio_shrink_succ ha0.le hy0)
        (by rw [slowPt_add]; simp)
  have hwit : ∀ k < N + 1, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement j) (min (Δp k) 1)
      {e | xp k + e ∈ trqSlowX} P.ς (dp k j) := fun k hk j _ => by
    rw [hxpl k hk, hΔpl k hk, min_eq_left (hpow1 k), hdp]
    by_cases hj1 : j = 1
    · subst hj1; simp only [↓reduceIte]
      exact trqSlow_wit_shrink_one ha hy0.le hAy (hpow0 k).le
    · by_cases hj2 : j = 2
      · subst hj2; simp only [↓reduceIte]
        exact trqSlow_wit_shrink_two ha hy0.le (hyk k hk) (hpow1 k)
      · simp only [hj1, hj2, ↓reduceIte]
        exact hW _ _ _ hmemy (hpow0 k).le
  have hr : Δp (N + 1) = y := by rw [hΔp, min_eq_right (by omega), hyN]
  obtain ⟨x, s, Δ, jk, d, hx0, hrun', hns', hcount, -, -⟩ :=
    trq_splice (T := N + 1) (T' := T') (c := c)
    (P := P) (F := phi2 trqSlowC) (X := trqSlowX) (q := q) (ε := ε) (ϑ := 1) (xp := xp)
    (sp := fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) (Δp := Δp) (jp := fun _ => 1) (dp := dp)
    (by rw [hΔp]; simp; rfl) hr hy0 hy1 hstep hacc hwit
    (fun k _ => by rw [hΔp]; exact hpow1 _)
    (by rw [hxt0, hxp, ite_eq_right (by omega)]) hrun hns hc
  exact ⟨x, s, Δ, jk, d, by rw [hx0, hxpl 0 (by omega)], hrun', hns', le_trans (le_add_self) hcount⟩

open Classical in
/-- **The travel phase.** From `(a₀, 0)`, `a₀ ≥ 2`, with the radius `1`, `k₀ + 1` successful
first-order steps `(1/2, 0)` (the last one `(1/2, y)`) reach `(a₀ + (k₀ + 1)/2, y)`, provided
`ε_1 < A` at the points `(a₀ + k/2, 0)`, `k ≤ k₀`, `0 ≤ y ≤ 1/2` and `y² ≤ ε_1/8`; any run from
there with the radius `1` continues. -/
theorem trqSlow_travel_phase {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ} {a₀ y : ℝ} (ha₀ : 2 ≤ a₀) {k₀ : ℕ}
    (hA : ∀ k ≤ k₀, ε 1 < trqSlowA (a₀ + k / 2)) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hy2 : y ^ 2 ≤ ε 1 / 8) {xt st : ℕ → ℝ²} {Δt : ℕ → ℝ} {jt : ℕ → ℕ} {dt : ℕ → ℕ → ℝ²}
    (hxt0 : xt 0 = slowPt (a₀ + (k₀ + 1) / 2) y)
    (hrun : Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX
      (trqSlowParamsAt 1 one_pos le_rfl) q ε 1 xt st Δt jt dt) {T' c : ℕ}
    (hns : ∀ k < T', ¬ Chapter12.trqStop (phi2 trqSlowC) (trqSlowParamsAt 1 one_pos le_rfl) q ε 1
      xt Δt dt k)
    (hc : c ≤ ((Finset.range T').filter fun k =>
      (trqSlowParamsAt 1 one_pos le_rfl).η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) xt st jt k).card) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²), x 0 = slowPt a₀ 0 ∧
      Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX trqSlowParams q ε 1 x s Δ jk d ∧
      (∀ k < k₀ + 1 + T', ¬ Chapter12.trqStop (phi2 trqSlowC) trqSlowParams q ε 1 x Δ d k) ∧
      c ≤ ((Finset.range (k₀ + 1 + T')).filter fun k =>
        trqSlowParams.η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k).card := by
  obtain ⟨W, hW⟩ := trqSlow_exists_witness
  set P := trqSlowParams with hP
  have hak : ∀ k : ℕ, 2 ≤ a₀ + (k : ℝ) / 2 := fun k => by
    have : 0 ≤ (k : ℝ) / 2 := by positivity
    linarith
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k =
      if k ≤ k₀ then slowPt (a₀ + k / 2) 0 else slowPt (a₀ + (k₀ + 1) / 2) y := ⟨_, fun _ => rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ sp : ℕ → ℝ², ∀ k, sp k =
      if k < k₀ then slowPt (1 / 2) 0 else slowPt (1 / 2) y := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k = fun j => if j = 1 then slowPt (1 / 4) 0
      else if j = 2 then slowPt 1 0 else W (xp k) 1 j := ⟨_, fun _ => rfl⟩
  have hxpl : ∀ k < k₀ + 1, xp k = slowPt (a₀ + k / 2) 0 := fun k hk => by
    rw [hxp, ite_eq_left (by omega)]
  have hspτ : ∀ k < k₀ + 1, ∃ τ, sp k = slowPt (1 / 2) τ ∧ 0 ≤ τ ∧ τ ≤ y := fun k _ => by
    rw [hsp]
    split_ifs
    · exact ⟨0, rfl, le_rfl, hy0⟩
    · exact ⟨y, rfl, hy0, le_rfl⟩
  have hnext : ∀ k < k₀ + 1, xp (k + 1) = xp k + sp k := fun k hk => by
    rw [hxpl k hk, hsp]
    rcases Nat.lt_or_ge k k₀ with hkN | hkN
    · rw [hxpl (k + 1) (by omega), ite_eq_left hkN, slowPt_add]
      push_cast; ring_nf
    · have hkN' : k = k₀ := by omega
      subst hkN'
      rw [hxp, ite_eq_right (by omega), ite_eq_right (by omega), slowPt_add]
      ring_nf
  have hstep : ∀ k < k₀ + 1, Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (xp k))
      {e | xp k + e ∈ trqSlowX} P.ς q ε (min ((fun _ => (1 : ℝ)) k) 1) ((fun _ => (1 : ℝ)) k)
      (dp k) ((fun _ => 1) k) (sp k) := fun k hk => by
    obtain ⟨τ, hτ, hτ0, hτy⟩ := hspτ k hk
    simp only [min_self]
    rw [hxpl k hk, hτ]
    refine trqSlow_step_axis_one hq (hak k) one_pos (hA k (by omega)) (by norm_num)
      ((norm_slowPt_le _ _).trans ?_) (by rw [hdp]; simp)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg hτ0]
    linarith
  have hacc : ∀ k < k₀ + 1, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio (phi2 trqSlowC) (xp k) (sp k)
        ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement ((fun _ => 1) k) (sp k)))
      (xp k) (sp k) (xp (k + 1)) ((fun _ => (1 : ℝ)) k) ((fun _ => (1 : ℝ)) (k + 1)) :=
    fun k hk => by
    refine trqSlow_accept_succ zero_le_one ?_ (hnext k hk)
    obtain ⟨τ, hτ, hτ0, hτy⟩ := hspτ k hk
    have ha0 : 0 < a₀ + (k : ℝ) / 2 := by linarith [hak k]
    have hA0 := trqSlowA_pos ha0
    have hAk := hA k (by omega)
    simp only
    rw [hxpl k hk, hτ, trqSlow_ΔT1_pt ha0]
    have hτ2 : τ ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hτ0 hτy 2
    exact trqSlow_ratio_axis (hak k) (by norm_num) le_rfl (by nlinarith) (by nlinarith)
      (by nlinarith)
  have hwit : ∀ k < k₀ + 1, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement j) (min ((fun _ => (1 : ℝ)) k) 1)
      {e | xp k + e ∈ trqSlowX} P.ς (dp k j) := fun k hk j _ => by
    simp only [min_self]
    rw [hdp]
    by_cases hj1 : j = 1
    · subst hj1; simp only [↓reduceIte]; rw [hxpl k hk]
      exact trqSlow_wit_axis_one (hak k) zero_le_one
    · by_cases hj2 : j = 2
      · subst hj2; simp only [↓reduceIte]; rw [hxpl k hk]
        exact trqSlow_wit_axis_two (hak k) zero_le_one le_rfl
      · simp only [hj1, hj2, ↓reduceIte]
        exact hW _ _ _ (by rw [hxpl k hk]; exact slowPt_mem_trqSlowX (by linarith [hak k]))
          zero_le_one
  obtain ⟨x, s, Δ, jk, d, hx0, hrun', hns', hcount, -, -⟩ := trq_splice (T := k₀ + 1) (T' := T')
    (c := c) (P := P) (F := phi2 trqSlowC) (X := trqSlowX) (q := q) (ε := ε) (ϑ := 1) (xp := xp)
    (sp := sp) (Δp := fun _ => 1) (jp := fun _ => 1) (dp := dp) rfl rfl one_pos le_rfl hstep hacc
    hwit (fun _ _ => le_rfl) (by rw [hxt0, hxp, ite_eq_right (by omega)])
    hrun hns hc
  exact ⟨x, s, Δ, jk, d, by rw [hx0, hxpl 0 (by omega)]; norm_num, hrun', hns',
    le_trans (le_add_self) hcount⟩

end Phases

section LongRun

/-- `A(2^{4n}) = 2^{-5n}/8`. -/
theorem trqSlowA_two_pow (n : ℕ) : trqSlowA ((2 : ℝ) ^ (4 * n)) = (1 / 2) ^ (5 * n) / 8 := by
  unfold trqSlowA
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have e : ((4 * n : ℕ) : ℝ) * (-(5 / 4 : ℝ)) = -((5 * n : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div_pow, one_div]

/-- `A(x) ≤ 2^{-5n}/8` for `x ≥ 2^{4n}`. -/
theorem trqSlowA_le_of_ge (n : ℕ) {x : ℝ} (hx : (2 : ℝ) ^ (4 * n) ≤ x) :
    trqSlowA x ≤ (1 / 2) ^ (5 * n) / 8 :=
  (trqSlowA_anti (by positivity) hx).trans_eq (trqSlowA_two_pow n)

/-- `A(x) > 2^{-5n}/8` for `0 < x < 2^{4n}`. -/
theorem trqSlowA_gt_of_lt (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx : x < (2 : ℝ) ^ (4 * n)) :
    (1 / 2) ^ (5 * n) / 8 < trqSlowA x := by
  rw [← trqSlowA_two_pow n]
  unfold trqSlowA
  have := Real.rpow_lt_rpow_of_neg hx0 hx (by norm_num : (-(5 / 4 : ℝ)) < 0)
  linarith

/-- `2^{m+k} 2^{-k} = 2^m`. -/
theorem two_pow_add_mul_half_pow (m k : ℕ) :
    (2 : ℝ) ^ (m + k) * (1 / 2) ^ k = 2 ^ m := by
  rw [pow_add, mul_assoc, ← mul_pow]; norm_num

/-- **A long TRq-SC run on the fixed problem.** For `q ≥ 2`, `M ≥ 1`, tolerances with
`ε_1 = 2^{-10M}/2`, `ε_2 = 2^{-5M}/2`, and a starting point `(a₀, 0)` with `a₀ ≥ 2` and
`ε_1 < A(a₀)`, there is a TRq-SC run of `ν = ½‖c‖²` on `X` from `(a₀, 0)` (parameters
`trqSlowParams`, `ϑ = 1`) that does not terminate during its first `T` iterations, of which at
least `2^{22M} - 2^{18M} - 2^{10M}` are successful: the travel, shrinking and slow phases
(`trqSlow_travel_phase`, `trqSlow_shrink_phase`, `trqSlow_slow_phase`) with `y = 2^{-10M}` and
`K = 2^{22M} - 2^{18M} - 2^{10M}` slow steps. -/
theorem trqSlow_exists_long_run {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 1 ≤ M) {ε : ℕ → ℝ}
    (h1 : ε 1 = (1 / 2) ^ (10 * M) / 2) (h2 : ε 2 = (1 / 2) ^ (5 * M) / 2) {a₀ : ℝ} (ha₀ : 2 ≤ a₀)
    (hA₀ : ε 1 < trqSlowA a₀) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²) (T : ℕ), x 0 = slowPt a₀ 0 ∧
      Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX trqSlowParams q ε 1 x s Δ jk d ∧
      (∀ k < T, ¬ Chapter12.trqStop (phi2 trqSlowC) trqSlowParams q ε 1 x Δ d k) ∧
      2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) ≤ ((Finset.range T).filter fun k =>
        trqSlowParams.η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k).card := by
  classical
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = (1 / 2) ^ (10 * M) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hydef]; positivity
  have hy16 : y ≤ 1 / 16 := by
    rw [hydef]
    calc ((1 : ℝ) / 2) ^ (10 * M) ≤ (1 / 2) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have hy1 : y ≤ 1 := by linarith
  have hy10 : y ≤ 1 / 1024 := by
    rw [hydef]
    calc ((1 : ℝ) / 2) ^ (10 * M) ≤ (1 / 2) ^ 10 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 1024 := by norm_num
  have hE : ε 1 = y / 2 := by rw [h1, hydef]
  have hy8 : (1 / 2 : ℝ) ^ (5 * (2 * M)) / 8 = y / 8 := by
    rw [hydef, show 5 * (2 * M) = 10 * M by ring]
  -- the end of the travel phase
  have hex : ∃ k : ℕ, trqSlowA (a₀ + ((k : ℝ) + 1) / 2) ≤ ε 1 := by
    refine ⟨2 * 2 ^ (8 * M), (trqSlowA_le_of_ge (2 * M) ?_).trans ?_⟩
    · rw [show 4 * (2 * M) = 8 * M by ring]
      push_cast
      have : (0 : ℝ) ≤ 2 ^ (8 * M) := by positivity
      linarith
    · rw [hy8, hE]; linarith
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ = Nat.find hex := ⟨_, rfl⟩
  have hAs : trqSlowA (a₀ + ((k₀ : ℝ) + 1) / 2) ≤ ε 1 := hk₀ ▸ Nat.find_spec hex
  have hAk : ∀ k ≤ k₀, ε 1 < trqSlowA (a₀ + (k : ℝ) / 2) := fun k hk => by
    rcases k with _ | m
    · simpa using hA₀
    · have := Nat.find_min hex (show m < Nat.find hex by omega)
      push Not at this
      push_cast
      exact this
  -- `a_s < 2^{8M} + 1`
  have has : a₀ + ((k₀ : ℝ) + 1) / 2 < 2 ^ (8 * M) + 1 := by
    by_contra hcon
    push Not at hcon
    have h := hAk k₀ le_rfl
    have h' := trqSlowA_le_of_ge (2 * M) (x := a₀ + (k₀ : ℝ) / 2) (by
      rw [show 4 * (2 * M) = 8 * M by ring]; linarith)
    rw [hy8, hE] at *
    linarith
  set as := a₀ + ((k₀ : ℝ) + 1) / 2 with has_def
  have has2 : 2 ≤ as := by
    have : 0 ≤ ((k₀ : ℝ) + 1) / 2 := by positivity
    linarith
  -- the slow phase
  set K := 2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) with hKdef
  have hKle : 2 ^ (18 * M) + 2 ^ (10 * M) ≤ 2 ^ (22 * M) := by
    have a1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : 2 ^ (22 * M) = 2 * 2 ^ (22 * M - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hKs1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKs2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M) - 2 ^ (18 * M) :=
    Nat.le_sub_of_add_le (by rw [add_comm]; exact hKle)
  have hKr : (K : ℝ) * y = 2 ^ (12 * M) - 2 ^ (8 * M) - 1 := by
    rw [hKdef, Nat.cast_sub hKs2, Nat.cast_sub hKs1, hydef]
    push_cast
    rw [sub_mul, sub_mul, show 22 * M = 12 * M + 10 * M by ring,
      show 18 * M = 8 * M + 10 * M by ring, two_pow_add_mul_half_pow,
      two_pow_add_mul_half_pow, ← mul_pow]
    norm_num
  have hK : ∀ k < K, ε 2 * y < 4 * trqSlowA (as + k * y) := fun k hk => by
    have hkK : (k : ℝ) * y ≤ (K : ℝ) * y := by
      have : (k : ℝ) ≤ K := by exact_mod_cast hk.le
      nlinarith
    have hx : as + k * y < (2 : ℝ) ^ (4 * (3 * M)) := by
      rw [show 4 * (3 * M) = 12 * M by ring]
      linarith
    have hpos : 0 < as + k * y := by
      have : 0 ≤ (k : ℝ) * y := by positivity
      linarith
    have := trqSlowA_gt_of_lt (3 * M) hpos hx
    have e : ε 2 * y = (1 / 2) ^ (5 * (3 * M)) / 2 := by
      rw [h2, hydef, show 5 * (3 * M) = 5 * M + 10 * M by ring, pow_add]; ring
    rw [e]
    linarith
  obtain ⟨x3, s3, Δ3, j3, d3, hx3, hrun3, hns3, hc3⟩ :=
    trqSlow_slow_phase hq has2 hy0 (by linarith) (hAs.trans_eq rfl) hK
  -- the shrinking phase
  obtain ⟨x2, s2, Δ2, j2, d2, hx2, hrun2, hns2, hc2⟩ :=
    trqSlow_shrink_phase (N := 10 * M) hq has2 hydef hy0 hy1 (by linarith) (by linarith) hx3
      hrun3 hns3 hc3
  -- the travel phase
  obtain ⟨x1, s1, Δ1, j1, d1, hx1, hrun1, hns1, hc1⟩ :=
    trqSlow_travel_phase (by omega) ha₀ hAk hy0.le (by linarith) (by rw [hE]; nlinarith) hx2 hrun2
      hns2 hc2
  exact ⟨x1, s1, Δ1, j1, d1, _, hx1, hrun1, hns1, hc1⟩

end LongRun

section Assumptions

/-- f.D1pLB.X for `v ↦ g(v_i)` on `ℝⁿ` from derivative bounds of `g` on the `i`-th coordinates of
an open convex `X₀ ⊇ X` (orders `k ≥ 1`), with `B = C`, `L_j = C_{j+1}`. -/
theorem assumptionD1pLBX_comp_coord {n : ℕ} {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (i : Fin n) {X X₀ : Set (EuclideanSpace ℝ (Fin n))}
    (hX₀ : IsOpen X₀) (hcv : Convex ℝ X₀) (hXX : X ⊆ X₀) (hmem : ∀ v ∈ X₀, v i ∈ U) (p : ℕ)
    {C : ℕ → ℝ} (hC : ∀ k, 1 ≤ k → ∀ v ∈ X₀, |iteratedDeriv k g (v i)| ≤ C k) :
    AssumptionD1pLBX (fun v : EuclideanSpace ℝ (Fin n) => g (v i)) X X₀ p (fun j => C (j + 1))
      C := by
  have hcd : ∀ (m : ℕ), ∀ v ∈ X₀, ContDiffAt ℝ m (fun v : EuclideanSpace ℝ (Fin n) => g (v i))
      v := fun m v hv =>
    ((hg.contDiffAt (hU.mem_nhds (hmem v hv))).of_le (by exact_mod_cast le_top)).comp_coord i
  refine ⟨hX₀, hcv, hXX, fun v hv => (hcd p v hv).contDiffWithinAt, fun j hj => ?_,
    fun j hj v hv => (((hg.contDiffAt (hU.mem_nhds (hmem v hv))).of_le
      (by exact_mod_cast le_top)).norm_iteratedFDeriv_comp_coord_le (k := j) i).trans
      (hC j (Finset.mem_Icc.1 hj).1 v hv)⟩
  exact iteratedFDerivLipschitzOn_of_norm_le hcv (fun y hy => hcd (j + 1) y hy) fun v hv =>
    (((hg.contDiffAt (hU.mem_nhds (hmem v hv))).of_le
      (by exact_mod_cast le_top)).norm_iteratedFDeriv_comp_coord_le (k := j + 1) i).trans
      (hC (j + 1) (by omega) v hv)

/-- The bound on the derivatives of `g(t) = t^{-1/8}` on `t > 1/2`. -/
noncomputable def trqSlowCB (k : ℕ) : ℝ :=
  |(descPochhammer ℝ k).eval (-(1 / 8 : ℝ))| * (1 / 2 : ℝ) ^ (-(1 / 8 : ℝ) - k) + 1

/-- The derivative bounds are at least `1`. -/
theorem one_le_trqSlowCB (k : ℕ) : 1 ≤ trqSlowCB k := by
  unfold trqSlowCB
  have : 0 ≤ |(descPochhammer ℝ k).eval (-(1 / 8 : ℝ))| * (1 / 2 : ℝ) ^ (-(1 / 8 : ℝ) - k) := by
    positivity
  linarith

/-- `|g^{(k)}(t)| ≤ C_k` for `t > 1/2`. -/
theorem abs_iteratedDeriv_trqSlowG_le (k : ℕ) {t : ℝ} (ht : 1 / 2 < t) :
    |iteratedDeriv k trqSlowG t| ≤ trqSlowCB k := by
  have e : trqSlowG = fun t : ℝ => t ^ (-(1 / 8 : ℝ)) := rfl
  rw [iteratedDeriv_eq_iterate, e, Real.iter_deriv_rpow_const, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
  unfold trqSlowCB
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) ht.le
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith : -(1 / 8 : ℝ) - k ≤ 0)
  have := abs_nonneg ((descPochhammer ℝ k).eval (-(1 / 8 : ℝ)))
  nlinarith

/-- `X₀` is open. -/
theorem isOpen_trqSlowX₀ : IsOpen trqSlowX₀ :=
  isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)

/-- `X₀` is convex. -/
theorem convex_trqSlowX₀ : Convex ℝ trqSlowX₀ :=
  convex_halfSpace_gt (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).isLinear _

/-- `X ⊆ X₀`. -/
theorem trqSlowX_subset : trqSlowX ⊆ trqSlowX₀ := fun v hv => by
  change 1 ≤ v 0 at hv; change 1 / 2 < v 0; linarith

/-- **c.D1qLB.X for the constraint of the example**, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowC_assumption (q : ℕ) :
    AssumptionCD1pLBX trqSlowC trqSlowX trqSlowX₀ q (fun j => trqSlowCB (j + 1)) trqSlowCB := by
  refine ⟨isOpen_trqSlowX₀, convex_trqSlowX₀, trqSlowX_subset, fun i => ?_⟩
  fin_cases i
  · have e : (fun x : ℝ² => trqSlowC x 0) = fun v : ℝ² => (fun _ : ℝ => (1 : ℝ)) (v 0) := rfl
    simp only [Fin.zero_eta]
    rw [e]
    refine assumptionD1pLBX_comp_coord isOpen_univ contDiffOn_const 0 isOpen_trqSlowX₀
      convex_trqSlowX₀ trqSlowX_subset (fun _ _ => mem_univ _) q fun k hk v _ => ?_
    rw [iteratedDeriv_const, ite_eq_right (by omega), abs_zero]
    exact zero_le_one.trans (one_le_trqSlowCB k)
  · have e : (fun x : ℝ² => trqSlowC x 1) = fun v : ℝ² => trqSlowG (v 0) := rfl
    simp only [Fin.mk_one]
    rw [e]
    exact assumptionD1pLBX_comp_coord isOpen_Ioi (fun _ hx =>
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (mem_Ioi.1 hx))).contDiffWithinAt) 0
      isOpen_trqSlowX₀ convex_trqSlowX₀ trqSlowX_subset
      (fun v hv => mem_Ioi.2 (lt_trans (by norm_num) hv)) q
      fun k _ v hv => abs_iteratedDeriv_trqSlowG_le k hv
  · have e : (fun x : ℝ² => trqSlowC x 2) = fun v : ℝ² => (fun t : ℝ => t) (v 1) := rfl
    simp only [Fin.reduceFinMk]
    rw [e]
    refine assumptionD1pLBX_comp_coord isOpen_univ contDiffOn_id 1 isOpen_trqSlowX₀
      convex_trqSlowX₀ trqSlowX_subset (fun _ _ => mem_univ _) q fun k hk v _ => ?_
    change |iteratedDeriv k (fun t : ℝ => t) (v 1)| ≤ _
    rw [iteratedDeriv_fun_id, ite_eq_right (by omega)]
    have := one_le_trqSlowCB k
    split_ifs <;> simp <;> linarith

/-- f.D1qLB.X for the objective `f = 0`. -/
theorem trqSlowF_assumption (q : ℕ) :
    AssumptionD1pLBX (fun _ : ℝ² => (0 : ℝ)) trqSlowX trqSlowX₀ q (fun _ => 0) (fun _ => 0) := by
  have e : (fun _ : ℝ² => (0 : ℝ)) = fun v : ℝ² => (fun _ : ℝ => (0 : ℝ)) (v 0) := rfl
  rw [e]
  exact assumptionD1pLBX_comp_coord (C := fun _ => 0) isOpen_univ contDiffOn_const 0
    isOpen_trqSlowX₀ convex_trqSlowX₀ trqSlowX_subset (fun _ _ => mem_univ _) q fun k hk v _ => by
      rw [iteratedDeriv_const, ite_eq_right (by omega), abs_zero]

/-- f.B.Fb for `f = 0` (bounds `0`), on every `ℱ_β`. -/
theorem trqSlowF_assumptionBFb (βF : ℝ) :
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) trqSlowC trqSlowX βF 0 0 :=
  fun _ _ => ⟨le_rfl, le_rfl⟩

end Assumptions

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Step-2 iteration only depends on the Taylor decrements. -/
theorem isTRqStep_congr {D D' : FormalMultilinearSeries ℝ E ℝ}
    (h : ∀ j, D'.taylorDecrement j = D.taylorDecrement j) {S : Set E} {ς : ℝ} {q : ℕ}
    {ε : ℕ → ℝ} {δ Δ : ℝ} {d : ℕ → E} {j : ℕ} {s : E}
    (hs : Optimization.IsTRqStep D S ς q ε δ Δ d j s) :
    Optimization.IsTRqStep D' S ς q ε δ Δ d j s := by
  refine ⟨hs.order_mem, ?_, fun i hi hij => ?_, hs.mem, ?_⟩
  · rw [h]; exact hs.lt_taylorDecrement
  · rw [h]; exact hs.taylorDecrement_le_of_lt i hi hij
  · rw [h]; exact hs.taylorDecrement_le

/-- **Transfer of a TRq-SC run to a function with the same Taylor decrements and the same
differences on `X`** (e.g. a function differing by a constant near `X`): the run is a run for the
new function, with the same termination tests and ratios before termination. -/
theorem trq_run_congr {F G : E → ℝ} {X : Set E} {P : Optimization.TRqParams} {q : ℕ}
    {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E} {Δ : ℕ → ℝ} {jk : ℕ → ℕ} {d : ℕ → ℕ → E}
    (hT : ∀ y ∈ X, ∀ j, (ftaylorSeries ℝ G y).taylorDecrement j =
      (ftaylorSeries ℝ F y).taylorDecrement j)
    (hD : ∀ y ∈ X, ∀ z ∈ X, G y - G z = F y - F z) (hx0 : x 0 ∈ X)
    (h : Chapter12.algorithm_12_2_1_feasible F X P q ε ϑ x s Δ jk d) :
    Chapter12.algorithm_12_2_1_feasible G X P q ε ϑ x s Δ jk d ∧
      (∀ k, (∀ i < k, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i) →
        (Chapter12.trqStop G P q ε ϑ x Δ d k ↔ Chapter12.trqStop F P q ε ϑ x Δ d k)) ∧
      (∀ k, (∀ i ≤ k, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i) →
        Chapter12.trqRho G x s jk k = Chapter12.trqRho F x s jk k) := by
  have hmem := Chapter12.trq_mem h hx0
  have hiff : ∀ k, (∀ i < k, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i) →
      (Chapter12.trqStop G P q ε ϑ x Δ d k ↔ Chapter12.trqStop F P q ε ϑ x Δ d k) :=
    fun k hk => by
    change Optimization.MeasureTestPasses
      (fun j => (ftaylorSeries ℝ G (x k)).taylorDecrement j) q P.ς ε (fun _ => min (Δ k) ϑ)
        (d k) ↔ Optimization.MeasureTestPasses
      (fun j => (ftaylorSeries ℝ F (x k)).taylorDecrement j) q P.ς ε (fun _ => min (Δ k) ϑ) (d k)
    have e : (fun j => (ftaylorSeries ℝ G (x k)).taylorDecrement j) =
        fun j => (ftaylorSeries ℝ F (x k)).taylorDecrement j := funext (hT _ (hmem k hk))
    rw [e]
  have hnot : ∀ k, (∀ i < k, ¬ Chapter12.trqStop G P q ε ϑ x Δ d i) →
      ∀ i < k, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i := by
    intro k hk i
    induction i using Nat.strong_induction_on with
    | _ i ih => exact fun hi hF => hk i hi ((hiff i fun j hj => ih j hj (hj.trans hi)).2 hF)
  have hnot' : ∀ k, (∀ i ≤ k, ¬ Chapter12.trqStop G P q ε ϑ x Δ d i) →
      ∀ i ≤ k, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i := fun k hk i hi =>
    hnot (k + 1) (fun j hj => hk j (by omega)) i (by omega)
  have hrho : ∀ k, (∀ i ≤ k, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i) →
      Chapter12.trqRho G x s jk k = Chapter12.trqRho F x s jk k := fun k hk => by
    have hxk := hmem k fun i hi => hk i hi.le
    have hsk : x k + s k ∈ X := (h.isTRqStep hk).mem.2
    change Optimization.trqRatio G _ x s jk k = Optimization.trqRatio F _ x s jk k
    rw [Optimization.trqRatio_eq, Optimization.trqRatio_eq, Optimization.reductionRatio_def,
      Optimization.reductionRatio_def, hD _ hxk _ hsk, hT _ hxk]
  refine ⟨⟨⟨h.toIsTRRun.delta_zero, fun k hk => ?_, fun k hk => ?_⟩, fun k hk j hj => ?_,
    fun k hk => h.cap k (hnot' k hk)⟩, hiff, hrho⟩
  · exact isTRqStep_congr (hT _ (hmem k fun i hi => hnot' k hk i hi.le)) (h.step k (hnot' k hk))
  · have := h.accept k (hnot' k hk)
    change Optimization.TRAcceptance P.toTRParams (Chapter12.trqRho G x s jk k) (x k) (s k)
      (x (k + 1)) (Δ k) (Δ (k + 1))
    rw [hrho k (hnot' k hk)]
    exact this
  · have := h.witness k (hnot k hk) j hj
    change Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ G (x k)).taylorDecrement j) _ _ _ _
    rw [hT _ (hmem k (hnot k hk))]
    exact this

end Transfer

section TPqp

/-- `2^{-10M}/2 < A(2)` for `M ≥ 1`. -/
theorem trqSlow_tol_lt_A_two {M : ℕ} (hM : 1 ≤ M) : (1 / 2 : ℝ) ^ (10 * M) / 2 < trqSlowA 2 := by
  have h2 := trqSlowA_gt_of_lt 1 (x := 2) (by norm_num) (by norm_num)
  have : (1 / 2 : ℝ) ^ (10 * M) ≤ (1 / 2) ^ 10 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at h2 this ⊢
  linarith

/-- The Phase-1 constant `β₁ = 1/(2‖c(x₀)‖)` of the example (`x₀ = (2, 0)`), so that
`β₁ ‖c(x₀)‖ = 1/2`. -/
noncomputable def trqSlowβ₁ : ℝ := 1 / (2 * ‖trqSlowC (slowPt 2 0)‖)

/-- `β₁ ‖c(x₀)‖ = 1/2`. -/
theorem trqSlowβ₁_mul : trqSlowβ₁ * ‖trqSlowC (slowPt 2 0)‖ = 1 / 2 := by
  have := one_le_norm_trqSlowC (slowPt 2 0)
  unfold trqSlowβ₁
  field_simp

/-- `β₁ > 0`. -/
theorem trqSlowβ₁_pos : 0 < trqSlowβ₁ := by
  have := one_le_norm_trqSlowC (slowPt 2 0)
  unfold trqSlowβ₁; positivity

/-- `β₁ < 1`. -/
theorem trqSlowβ₁_lt_one : trqSlowβ₁ < 1 := by
  have h := one_le_norm_trqSlowC (slowPt 2 0)
  have h2 := trqSlowβ₁_mul
  have h3 := trqSlowβ₁_pos
  nlinarith

open Classical in
/-- **A long TPqp-GC run on the fixed problem** (`f = 0`, `c(v) = (1, v_1^{-1/8}, v_2)`,
`X = {v_1 ≥ 1}`, `x₀ = (2, 0)`, INNER = TRq-SC with `trqSlowParams` and `ϑ = 1`,
`β₁ = trqSlowβ₁`). For `q ≥ 2`, `M ≥ 1`, any `θ ∈ (0, 1)`, any `β`, and tolerances
`ε ∈ (0, 1]^{q+1}` with `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`, there is a run of `IsTPqpGCTRqSCRun`
that terminates in Phase 1 (`‖c(x₁)‖ > θ ε₀`) after a single INNER call with at least
`2^{22M} - 2^{18M} - 2^{10M} + 1` derivative evaluations. -/
theorem trqSlow_exists_tpqp_run {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 1 ≤ M) {θ β : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1)
    (h1 : ε 1 = (1 / 2) ^ (10 * M)) (h2 : ε 2 = (1 / 2) ^ (5 * M)) :
    ∃ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC trqSlowX q trqSlowParams 1 θ trqSlowβ₁ β ε
        (slowPt 2 0) xP δP k₁ D nF₁ nD₁ ∧ θ * ε 0 < ‖trqSlowC (xP k₁)‖ ∧
      (((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤
        ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ)) := by
  set x₀ := slowPt 2 0 with hx₀
  set ε' : ℕ → ℝ := fun j => trqSlowβ₁ * ‖trqSlowC x₀‖ * phase1Tol θ ε j with hε'
  have hε'j : ∀ j, j ≠ 0 → ε' j = ε j / 2 := fun j hj => by
    simp only [hε', phase1Tol_of_ne θ ε hj]
    rw [hx₀, trqSlowβ₁_mul]; ring
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  obtain ⟨x, s, Δ, jk, d, T, hx0, hrun, hns, hcount⟩ := trqSlow_exists_long_run hq hM
    (ε := ε') (by rw [hε'j 1 one_ne_zero, h1]) (by rw [hε'j 2 two_ne_zero, h2]) (a₀ := 2)
    le_rfl (by rw [hε'j 1 one_ne_zero, h1]; exact trqSlow_tol_lt_A_two hM)
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq (trqSlowC_assumption q)
  have hε'I : ∀ j ∈ Finset.Icc 1 q, ε' j ∈ Ioc 0 1 := fun j hj => by
    rw [hε'j j (by have := (Finset.mem_Icc.1 hj).1; omega)]
    have := hεI j hj
    exact ⟨by linarith, by linarith⟩
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hϑ' : Chapter12.finMin 1 ε' q ≤ 1 := (Chapter12.finMin_le h1q).trans (hε'I 1 h1q).2
  have hx0X : x 0 ∈ trqSlowX := by rw [hx0]; exact slowPt_mem_trqSlowX (by norm_num)
  have hA : ∀ z ∈ trqSlowX, phi2 trqSlowC z ≤ phi2 trqSlowC (x 0) →
      z ∈ nuSublevel trqSlowC trqSlowX x₀ := fun z hz hzx => by
    rw [hx0] at hzx
    exact ⟨hz, norm_le_of_phi2_le hzx⟩
  obtain ⟨kε, hhit, hmem, hrad, hcert, -, -⟩ := Chapter12.theorem_12_2_5_anchored (flow := 0)
    (fun z _ => by rw [phi2_apply]; positivity) (hν x₀).1 trqSlowX_subset hA hx0X hε'I hϑ' le_rfl
    hrun
  have hkT : T ≤ kε := by
    by_contra h
    exact hns kε (by omega) hhit.1
  -- the Phase-1 output
  set nD := Optimization.derivEvalCount
    (fun k => trqSlowParams.η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k) kε with hnD
  have hnDge : 2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) + 1 ≤ nD := by
    rw [hnD, Optimization.derivEvalCount]
    refine Nat.add_le_add_right (hcount.trans (Finset.card_le_card ?_)) 1
    exact Finset.filter_subset_filter _ (Finset.range_subset_range.2 hkT)
  obtain ⟨xP, hxP⟩ : ∃ xP : ℕ → ℝ², ∀ k, xP k = if k = 0 then x₀ else x kε := ⟨_, fun _ => rfl⟩
  have hxP0 : xP 0 = x₀ := by rw [hxP]; simp
  have hxP1 : xP 1 = x kε := by rw [hxP]; simp
  set δo : ℝ := min (Δ kε) 1 with hδo
  have hc1 : 1 ≤ ‖trqSlowC (xP 1)‖ := one_le_norm_trqSlowC _
  have hc0 : θ * ε 0 < 1 := by nlinarith
  have hstop1 : lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP (fun _ _ => δo) 1 := by
    refine Or.inr ⟨le_rfl, fun j hj => ?_⟩
    have hcj := hcert j hj
    rw [← hxP1] at hcj
    refine hcj.trans ?_
    rw [hε'j j (by have := (Finset.mem_Icc.1 hj).1; omega),
      phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
    have hεj := (hεI j hj).1
    have hδ0 : 0 ≤ δo := hrad.1.le
    have : ε j / 2 ≤ ε j * ‖trqSlowC (xP 1)‖ := by nlinarith
    gcongr
  have hnstop0 : ¬ lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP (fun _ _ => δo) 0 := by
    rintro (h | ⟨h, -⟩)
    · rw [phase1Tol_zero, hxP0] at h
      have := one_le_norm_trqSlowC x₀
      linarith
    · omega
  have hhit1 : Optimization.IsFirstHit (lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP
      (fun _ _ => δo)) 1 := ⟨hstop1, fun j hj => by
        obtain rfl : j = 0 := by omega
        exact hnstop0⟩
  have hbig : ∀ k, 2 ≤ k → ¬ (∀ i < k, ¬ lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP
      (fun _ _ => δo) i) := fun k hk h => h 1 (by omega) hstop1
  have hk1 : ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP
      (fun _ _ => δo) i) → k = 1 := fun k h1k h => by
    by_contra hne
    exact hbig k (by omega) h
  have hphase1 : algorithm_14_3_1 trqSlowC trqSlowX q (phase1Tol θ ε) trqSlowβ₁ xP
      (fun _ _ => δo) := by
    refine ⟨by rw [hxP0]; exact slowPt_mem_trqSlowX (by norm_num), fun j hj => ?_,
      fun j hj => ?_, trqSlowβ₁_pos, trqSlowβ₁_lt_one, by rw [hxP0, trqSlowβ₁_mul]; norm_num,
      fun k h1k h => ?_, fun k h1k h _ _ => ?_, fun k h1k h j hj => ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero]; exact mul_pos hθ0 hε₀.1
      · rw [phase1Tol_of_ne θ ε hj0.ne']; exact (hε j hj).1
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero]; nlinarith
      · rw [phase1Tol_of_ne θ ε hj0.ne']; exact (hε j hj).2
    · obtain rfl := hk1 k h1k h
      rw [hxP1]; exact hmem
    · exact hrad
    · obtain rfl := hk1 k h1k h
      have hcj := hcert j hj
      rw [← hxP1] at hcj
      simp only [Nat.sub_self, hxP0]
      exact hcj
  refine ⟨xP, fun _ _ => δo, 1, ⟨fun _ => x₀, fun _ => 0, fun _ _ => 0, fun _ _ => x₀,
    fun _ => 0, fun _ _ => False⟩, fun _ => Optimization.funEvalCount kε, fun _ => nD,
    ⟨⟨hxP0, hphase1, hhit1, fun h => absurd h (by linarith)⟩, fun k h1k hk1' => ?_,
      fun h => absurd h (by linarith)⟩, by linarith, ?_⟩
  · obtain rfl : k = 1 := by omega
    simp only [Nat.sub_self, hxP0]
    exact ⟨x, s, Δ, jk, d, kε, hrun, hhit, hx0, hxP1.symm, fun _ _ => rfl, rfl, rfl⟩
  · rw [Finset.Icc_self, Finset.sum_singleton]
    exact_mod_cast hnDge

end TPqp

section Phase2Data

/-- The constraint of the Phase-2 example: `c₂(v) = (v_1^{-1/8}, v_2)` (the constraint `trqSlowC`
without its constant component, so that `‖c₂‖` is small at `x₀ = (256, 0)` and Phase 1 ends at
once). -/
noncomputable def trqSlowC2 : ℝ² → ℝ² := fun v => WithLp.toLp 2 ![trqSlowG (v 0), v 1]

/-- `‖c₂(v)‖² = g(v_1)² + v_2²`. -/
theorem norm_trqSlowC2_sq (v : ℝ²) : ‖trqSlowC2 v‖ ^ 2 = trqSlowG (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [trqLog_norm_sq]; rfl

/-- With `f = 0`, `μ(v, t) = ½‖c(v)‖² - (1 - t²)/2` (`c = trqSlowC`). -/
theorem targetMerit_trqSlowC2 (t : ℝ) (v : ℝ²) :
    Constrained.targetMerit (fun _ => 0) trqSlowC2 t v = phi2 trqSlowC v - (1 - t ^ 2) / 2 := by
  rw [Constrained.targetMerit_def, norm_trqSlowC2_sq, phi2_apply, norm_trqSlowC_sq]; ring

/-- The Taylor decrements of `μ(·, t)` (`f = 0`, `c = c₂`) and of `½‖c‖²` (`c = trqSlowC`) agree on
the open half-plane `v_1 > 0`. -/
theorem taylorDecrement_targetMerit_trqSlowC2 (t : ℝ) {v : ℝ²} (hv : 0 < v 0) (j : ℕ) :
    (ftaylorSeries ℝ (Constrained.targetMerit (fun _ => 0) trqSlowC2 t) v).taylorDecrement j =
      (ftaylorSeries ℝ (phi2 trqSlowC) v).taylorDecrement j := by
  have hU : IsOpen {w : ℝ² | 0 < w 0} :=
    isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)
  have hev : Constrained.targetMerit (fun _ => 0) trqSlowC2 t =ᶠ[𝓝 v]
      fun w => trqSlowNu w - (1 - t ^ 2) / 2 := by
    filter_upwards [hU.mem_nhds hv] with w hw
    rw [targetMerit_trqSlowC2 t w, phi2_trqSlowC_eq (le_of_lt hw)]
  rw [(hev.ftaylorSeries ℝ).eq_of_nhds, ftaylorSeries_phi2_trqSlowC hv]
  funext s
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  change iteratedFDeriv ℝ i (fun w => trqSlowNu w - (1 - t ^ 2) / 2) v (fun _ => s) =
    iteratedFDeriv ℝ i trqSlowNu v (fun _ => s)
  rw [iteratedFDeriv_sub_const_apply (by have := (Finset.mem_Icc.1 hi).1; omega)
    (contDiffAt_trqSlowNu hv i)]

/-- **c.D1qLB.X for `c₂`**, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowC2_assumption (q : ℕ) :
    AssumptionCD1pLBX trqSlowC2 trqSlowX trqSlowX₀ q (fun j => trqSlowCB (j + 1)) trqSlowCB := by
  refine ⟨isOpen_trqSlowX₀, convex_trqSlowX₀, trqSlowX_subset, fun i => ?_⟩
  fin_cases i
  · have e : (fun x : ℝ² => trqSlowC2 x 0) = fun v : ℝ² => trqSlowG (v 0) := rfl
    simp only [Fin.zero_eta]
    rw [e]
    exact assumptionD1pLBX_comp_coord isOpen_Ioi (fun _ hx =>
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (mem_Ioi.1 hx))).contDiffWithinAt) 0
      isOpen_trqSlowX₀ convex_trqSlowX₀ trqSlowX_subset
      (fun v hv => mem_Ioi.2 (lt_trans (by norm_num) hv)) q
      fun k _ v hv => abs_iteratedDeriv_trqSlowG_le k hv
  · have e : (fun x : ℝ² => trqSlowC2 x 1) = fun v : ℝ² => (fun t : ℝ => t) (v 1) := rfl
    simp only [Fin.mk_one]
    rw [e]
    refine assumptionD1pLBX_comp_coord isOpen_univ contDiffOn_id 1 isOpen_trqSlowX₀
      convex_trqSlowX₀ trqSlowX_subset (fun _ _ => mem_univ _) q fun k hk v _ => ?_
    change |iteratedDeriv k (fun t : ℝ => t) (v 1)| ≤ _
    rw [iteratedDeriv_fun_id, ite_eq_right (by omega)]
    have := one_le_trqSlowCB k
    split_ifs <;> simp <;> linarith

/-- f.B.Fb for `f = 0` and `c₂`. -/
theorem trqSlowF_assumptionBFb2 (βF : ℝ) :
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 trqSlowX βF 0 0 :=
  fun _ _ => ⟨le_rfl, le_rfl⟩

/-- `g(256) = 1/2`. -/
theorem trqSlowG_256 : trqSlowG 256 = 1 / 2 := by
  rw [trqSlowG, show (256 : ℝ) = 2 ^ ((8 : ℕ) : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `‖c₂(256, 0)‖ = 1/2`. -/
theorem norm_trqSlowC2_x₀ : ‖trqSlowC2 (slowPt 256 0)‖ = 1 / 2 := by
  have h := norm_trqSlowC2_sq (slowPt 256 0)
  simp only [slowPt_apply_zero, slowPt_apply_one, trqSlowG_256] at h
  nlinarith [norm_nonneg (trqSlowC2 (slowPt 256 0))]

/-- `2^{-10M}/2 < A(256)` for `M ≥ 2`. -/
theorem trqSlow_tol_lt_A_256 {M : ℕ} (hM : 2 ≤ M) :
    (1 / 2 : ℝ) ^ (10 * M) / 2 < trqSlowA 256 := by
  have h := trqSlowA_two_pow 2
  rw [show (2 : ℝ) ^ (4 * 2) = 256 by norm_num] at h
  rw [h]
  have : (1 / 2 : ℝ) ^ (10 * M) ≤ (1 / 2) ^ 20 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at this ⊢
  linarith

end Phase2Data

section Phase2Run

open Classical in
/-- **A long TPqp-GC run that enters Phase 2** on the fixed problem `f = 0`,
`c₂(v) = (v_1^{-1/8}, v_2)`, `X = {v_1 ≥ 1}`, `x₀ = (256, 0)`, with `θ = β = 1/2`, any
`β₁ ∈ (0, 1)`, INNER = TRq-SC with `trqSlowParams` and `ϑ = 1`. For `q ≥ 2`, `M ≥ 2` and
tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ = 1`, `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`: Phase 1 ends at
once (`‖c₂(x₀)‖ = 1/2 = θ ε₀`), and Phase 2 consists of a single INNER call on `μ(·, t_1)`, which
differs from `½‖c‖²` (`c = trqSlowC`) by a constant, followed by a termination in case (c); every
termination index of Phase 2 has at least `2^{22M} - 2^{18M} - 2^{10M} + 1` derivative
evaluations. -/
theorem trqSlow_exists_tpqp_run_phase2 {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 2 ≤ M) {β₁ : ℝ}
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) (h0 : ε 0 = 1)
    (h1 : ε 1 = (1 / 2) ^ (10 * M)) (h2 : ε 2 = (1 / 2) ^ (5 * M)) :
    ∃ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC2 trqSlowX q trqSlowParams 1 (1 / 2) β₁ (1 / 2) ε
        (slowPt 256 0) xP δP k₁ D nF₁ nD₁ ∧ ‖trqSlowC2 (xP k₁)‖ ≤ 1 / 2 * ε 0 ∧
      ∀ kε, D.IsEnd (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε kε →
        (((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤ D.derivEvals kε) := by
  set x₀ := slowPt 256 0 with hx₀
  have hcx₀ : ‖trqSlowC2 x₀‖ = 1 / 2 := norm_trqSlowC2_x₀
  have hx₀X : x₀ ∈ trqSlowX := slowPt_mem_trqSlowX (by norm_num)
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ, t₁ = (fun _ : ℝ² => (0 : ℝ)) x₀ - √(ε 0 ^ 2 - ‖trqSlowC2 x₀‖ ^ 2) :=
    ⟨_, rfl⟩
  have ht₁sq : t₁ ^ 2 = 3 / 4 := by
    rw [ht₁, h0, hcx₀]
    simp only [zero_sub, neg_sq]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  set G := Constrained.targetMerit (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 t₁ with hG
  have hres_ge : ∀ v, 1 / 2 ≤ Constrained.targetResidual (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 t₁ v :=
    fun v => by
    have h := Constrained.targetResidual_sq (f := fun _ : ℝ² => (0 : ℝ)) (c := trqSlowC2) (t := t₁)
      (x := v)
    have hn := Constrained.targetResidual_nonneg (f := fun _ : ℝ² => (0 : ℝ)) (c := trqSlowC2)
      (t := t₁) (x := v)
    nlinarith [sq_nonneg ‖trqSlowC2 v‖]
  have hres0 : Constrained.targetResidual (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 t₁ x₀ = 1 := by
    have h := Constrained.targetResidual_sq (f := fun _ : ℝ² => (0 : ℝ)) (c := trqSlowC2) (t := t₁)
      (x := x₀)
    have hn := Constrained.targetResidual_nonneg (f := fun _ : ℝ² => (0 : ℝ)) (c := trqSlowC2)
      (t := t₁) (x := x₀)
    rw [hcx₀] at h
    nlinarith
  set ε' : ℕ → ℝ := fun j =>
    1 / 2 * Constrained.targetResidual (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 t₁ x₀ * ε j with hε'
  have hε'j : ∀ j, ε' j = ε j / 2 := fun j => by simp only [hε', hres0]; ring
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  -- the run of TRq-SC on `½‖c‖²`
  obtain ⟨x, s, Δ, jk, d, T, hx0, hrunF, hns, hcount⟩ := trqSlow_exists_long_run hq
    (by omega : 1 ≤ M) (ε := ε') (by rw [hε'j, h1]) (by rw [hε'j, h2]) (a₀ := 256) (by norm_num)
    (by rw [hε'j, h1]; exact trqSlow_tol_lt_A_256 hM)
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq (trqSlowC_assumption q)
  have hε'I : ∀ j ∈ Finset.Icc 1 q, ε' j ∈ Ioc 0 1 := fun j hj => by
    rw [hε'j]
    have := hεI j hj
    exact ⟨by linarith, by linarith⟩
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hϑ' : Chapter12.finMin 1 ε' q ≤ 1 := (Chapter12.finMin_le h1q).trans (hε'I 1 h1q).2
  have hx0X : x 0 ∈ trqSlowX := by rw [hx0]; exact hx₀X
  have hA : ∀ z ∈ trqSlowX, phi2 trqSlowC z ≤ phi2 trqSlowC (x 0) →
      z ∈ nuSublevel trqSlowC trqSlowX x₀ := fun z hz hzx => by
    rw [hx0] at hzx
    exact ⟨hz, norm_le_of_phi2_le hzx⟩
  obtain ⟨kε, hhit, hmem, hrad, hcert, -, -⟩ := Chapter12.theorem_12_2_5_anchored (flow := 0)
    (fun z _ => by rw [phi2_apply]; positivity) (hν x₀).1 trqSlowX_subset hA hx0X hε'I hϑ' le_rfl
    hrunF
  have hkT : T ≤ kε := by
    by_contra h
    exact hns kε (by omega) hhit.1
  -- the same run on `μ(·, t₁)`
  have hT : ∀ y ∈ trqSlowX, ∀ j, (ftaylorSeries ℝ G y).taylorDecrement j =
      (ftaylorSeries ℝ (phi2 trqSlowC) y).taylorDecrement j := fun y hy j =>
    taylorDecrement_targetMerit_trqSlowC2 t₁ (lt_of_lt_of_le one_pos hy) j
  have hD : ∀ y ∈ trqSlowX, ∀ z ∈ trqSlowX, G y - G z = phi2 trqSlowC y - phi2 trqSlowC z :=
    fun y _ z _ => by rw [hG, targetMerit_trqSlowC2, targetMerit_trqSlowC2]; ring
  obtain ⟨hrunG, hiff, hrho⟩ := trq_run_congr hT hD hx0X hrunF
  have hhitG : Optimization.IsFirstHit
      (Chapter12.trqStop G trqSlowParams q ε' 1 x Δ d) kε :=
    ⟨(hiff kε hhit.2).2 hhit.1, fun i hi hGi =>
      hhit.2 i hi ((hiff i fun j hj => hhit.2 j (hj.trans hi)).1 hGi)⟩
  set δo : ℝ := min (Δ kε) 1 with hδo
  -- the Phase-2 sequences
  obtain ⟨Dx, hDx⟩ : ∃ Dx : ℕ → ℝ², ∀ k, Dx k = if k ≤ 1 then x₀ else x kε := ⟨_, fun _ => rfl⟩
  set D : TPqpSeq 2 := ⟨Dx, fun _ => t₁, fun _ _ => δo, fun _ => x, fun _ => kε,
    fun _ i => trqSlowParams.η₁ ≤ Chapter12.trqRho G x s jk i⟩ with hDdef
  have hDx1 : D.x 1 = x₀ := by simp [hDdef, hDx]
  have hDx2 : D.x 2 = x kε := by simp [hDdef, hDx]
  have hnotKa : ¬ D.IsKa (fun _ => 0) trqSlowC2 (1 / 2) ε 1 := by
    change ¬ (Constrained.targetResidual _ _ t₁ (D.x 2) < 1 / 2 * ε 0)
    rw [h0, mul_one]
    exact not_lt.2 (hres_ge _)
  have hnotKb : ¬ D.IsKb (fun _ => 0) trqSlowC2 (1 / 2) ε 1 := by
    rintro ⟨-, hlt⟩
    change (0 : ℝ) < t₁ at hlt
    have : t₁ ≤ 0 := by rw [ht₁]; simp
    linarith
  have hstop1 : D.Stop (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε 1 := Or.inl ⟨hnotKa, hnotKb⟩
  have hbef : ∀ k, 1 ≤ k → D.Before (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε k → k = 1 :=
    fun k hk hb => by
    by_contra hne
    exact hb 1 le_rfl (by omega) hstop1
  have hcertG : ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ G (x kε)) j δo
      {e | x kε + e ∈ trqSlowX} ≤ ε j * Constrained.targetResidual (fun _ => 0) trqSlowC2 t₁
        (x kε) * δo ^ j / j ! := fun j hj => by
    have hcj := hcert j hj
    have e : Optimization.taylorMeasure (ftaylorSeries ℝ G (x kε)) j δo {e | x kε + e ∈ trqSlowX}
        = Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 trqSlowC) (x kε)) j δo
          {e | x kε + e ∈ trqSlowX} := by
      simp only [Optimization.taylorMeasure, hT _ hmem j]
    rw [e]
    refine hcj.trans ?_
    rw [hε'j]
    have hεj := (hεI j hj).1
    have hδ0 : 0 ≤ δo := hrad.1.le
    have := hres_ge (x kε)
    have : ε j / 2 ≤ ε j * Constrained.targetResidual (fun _ => 0) trqSlowC2 t₁ (x kε) := by
      nlinarith
    gcongr
  have hphase2 : IsTPqpGCPhase2 (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) (1 / 2) ε x₀ D := by
    refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, fun j hj => (hε j hj).1,
      fun j hj => (hε j hj).2, hx₀X, by rw [hcx₀, h0]; norm_num, hDx1, ht₁,
      fun k hk hb => ?_, fun k hk hb => ?_, fun k hk hb => ?_, fun k hk hb => ?_,
      fun k hk hb => ?_, fun k hk hb i hi => ?_, fun k hk hb i hi => ?_,
      fun k hk hb ha => ?_, fun k hk hb hb' => ?_⟩
    · obtain rfl := hbef k hk hb; rw [hDx2]; exact hmem
    · obtain rfl := hbef k hk hb; exact fun _ _ => hrad
    · obtain rfl := hbef k hk hb
      refine Or.inr (Or.inr fun j hj => ?_)
      rw [hDx2]
      exact hcertG j hj
    · obtain rfl := hbef k hk hb; rw [hDx1]; exact hx0
    · obtain rfl := hbef k hk hb; rw [hDx2]
    · obtain rfl := hbef k hk hb
      exact Chapter14.trq_step_le hrunG (fun j hj => (hε'I j hj).1.le) zero_le_one
        fun l hl => hhitG.2 l (lt_of_le_of_lt hl hi)
    · obtain rfl := hbef k hk hb
      rw [h0, mul_one]; exact hres_ge _
    · obtain rfl := hbef k hk hb; exact absurd ha hnotKa
    · obtain rfl := hbef k hk hb; exact absurd hb' hnotKb
  have hcalls : IsTRqSCPhase2Calls (fun _ => 0) trqSlowC2 trqSlowX q trqSlowParams 1 (1 / 2)
      (1 / 2) ε D := fun k hk hb => by
    obtain rfl := hbef k hk hb
    rw [hDx1]
    exact ⟨x, s, Δ, jk, d, kε, hrunG, hhitG, le_rfl, fun _ _ => rfl, fun _ _ => Iff.rfl,
      fun _ _ => rfl⟩
  -- Phase 1 ends at once
  have hstop0 : lenStop trqSlowC2 trqSlowX q (phase1Tol (1 / 2) ε) (fun _ => x₀)
      (fun _ _ => 1) 0 := Or.inl (by rw [phase1Tol_zero, hcx₀, h0]; norm_num)
  have hphase1 : algorithm_14_3_1 trqSlowC2 trqSlowX q (phase1Tol (1 / 2) ε) β₁ (fun _ => x₀)
      (fun _ _ => 1) := by
    refine ⟨hx₀X, fun j hj => ?_, fun j hj => ?_, hβ₁0, hβ₁1, by rw [hcx₀]; linarith,
      fun k _ h => absurd hstop0 (h 0 (by omega)), fun k _ h => absurd hstop0 (h 0 (by omega)),
      fun k _ h => absurd hstop0 (h 0 (by omega))⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero, h0]; norm_num
      · rw [phase1Tol_of_ne _ ε hj0.ne']; exact (hε j hj).1
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero, h0]; norm_num
      · rw [phase1Tol_of_ne _ ε hj0.ne']; exact (hε j hj).2
  refine ⟨fun _ => x₀, fun _ _ => 1, 0, D, fun _ => 0, fun _ => 0,
    ⟨⟨rfl, hphase1, ⟨hstop0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, fun _ => hphase2⟩,
      fun k hk hk0 => absurd hk (by omega), fun _ => hcalls⟩,
    by rw [hcx₀, h0]; norm_num, fun kε' hend => ?_⟩
  -- the derivative evaluations
  obtain rfl : kε' = 1 := hbef kε' hend.1 hend.2.2
  have hsucc : 2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) ≤ D.succCount 1 := by
    refine hcount.trans (Finset.card_le_card fun i hi => ?_)
    rw [Finset.mem_filter] at hi ⊢
    have hiT := Finset.mem_range.1 hi.1
    refine ⟨Finset.mem_range.2 (by change i < kε; omega), ?_⟩
    change trqSlowParams.η₁ ≤ Chapter12.trqRho G x s jk i
    rw [hrho i fun l hl => hhit.2 l (by omega)]
    exact hi.2
  rw [TPqpSeq.derivEvals, Finset.Icc_self, Finset.sum_singleton]
  push_cast
  have : ((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) ≤ (D.succCount 1 : ℝ) := by
    exact_mod_cast hsucc
  linarith

end Phase2Run

section Main

/-- The tolerances of the counterexample: `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`, `ε_j = 1` otherwise
(in particular `ε₀ = 1`). -/
noncomputable def trqSlowTol (M : ℕ) : ℕ → ℝ := fun j =>
  if j = 1 then (1 / 2) ^ (10 * M) else if j = 2 then (1 / 2) ^ (5 * M) else 1

/-- The tolerances `trqSlowTol M` lie in `(0, 1]`. -/
theorem trqSlowTol_mem (M : ℕ) (j : ℕ) : 0 < trqSlowTol M j ∧ trqSlowTol M j ≤ 1 := by
  unfold trqSlowTol
  split_ifs
  · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  · exact ⟨one_pos, le_rfl⟩

/-- `((1/2)^n)^{-k} = 2^{nk}`. -/
theorem half_pow_rpow_neg (n k : ℕ) : ((1 / 2 : ℝ) ^ n) ^ (-(k : ℝ)) = 2 ^ (n * k) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← pow_mul, one_div, inv_pow, inv_inv]

/-- For the tolerances `trqSlowTol M` (`q ≥ 2`), the printed function-evaluation order of
Theorem 14.3.9 is at most `2^{20M}`. -/
theorem tpqpOrderF_trqSlowTol_le {q : ℕ} (M : ℕ) :
    tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) ≤ 2 ^ (20 * M) := by
  have h0 : trqSlowTol M 0 = 1 := by simp [trqSlowTol]
  have h1M : (1 : ℝ) ≤ 2 ^ (20 * M) := one_le_pow₀ (by norm_num)
  refine Chapter12.finMax_le (by rw [h0, inv_one]; exact h1M) fun j hj => ?_
  rw [h0, Real.one_rpow, one_mul]
  have hj1 := (Finset.mem_Icc.1 hj).1
  by_cases hj1' : j = 1
  · subst hj1'
    have e : -((((1 : ℕ) : ℝ)) + 1) = -((2 : ℕ) : ℝ) := by norm_num
    rw [e, show trqSlowTol M 1 = (1 / 2) ^ (10 * M) by simp [trqSlowTol], half_pow_rpow_neg]
    rw [show 10 * M * 2 = 20 * M by ring]
  · by_cases hj2 : j = 2
    · subst hj2
      have e : -((((2 : ℕ) : ℝ)) + 1) = -((3 : ℕ) : ℝ) := by norm_num
      rw [e, show trqSlowTol M 2 = (1 / 2) ^ (5 * M) by simp [trqSlowTol], half_pow_rpow_neg]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    · rw [show trqSlowTol M j = 1 by simp [trqSlowTol, hj1', hj2], Real.one_rpow]
      exact h1M

/-- For the tolerances `trqSlowTol M` (`q ≥ 2`), the logarithmic factor of `theorem_14_3_9_trq`
is `|log(ε₀ ε_min)| = 10 M log 2 ≤ 10 M`. -/
theorem trqSCLogTerm_trqSlowTol_le {q : ℕ} (hq : 2 ≤ q) (M : ℕ) :
    trqSCLogTerm q (trqSlowTol M) ≤ 10 * M := by
  have h0 : trqSlowTol M 0 = 1 := by simp [trqSlowTol]
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hmin : Chapter12.finMin 1 (trqSlowTol M) q = (1 / 2) ^ (10 * M) := by
    refine le_antisymm ((Chapter12.finMin_le h1q).trans_eq (by simp [trqSlowTol]))
      (Chapter12.le_finMin (pow_le_one₀ (by norm_num) (by norm_num)) fun j hj => ?_)
    unfold trqSlowTol
    split_ifs
    · exact le_rfl
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · exact pow_le_one₀ (by norm_num) (by norm_num)
  unfold trqSCLogTerm
  rw [h0, one_mul, hmin, Real.log_pow, one_div, Real.log_inv, abs_mul, abs_neg,
    abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Nat.abs_cast]
  push_cast
  have : (0 : ℝ) ≤ 10 * M := by positivity
  nlinarith

/-- `|κ| (1 + 10M) 2^{20M} < 2^{22M}/2` for `M > 20|κ| + 20`. -/
theorem trqSlow_final_lt {κ : ℝ} {M : ℕ} (hM : 20 * |κ| + 20 < M) :
    |κ| * (1 + 10 * M) * 2 ^ (20 * M) < (2 : ℝ) ^ (22 * M) / 2 := by
  have h2M : (M : ℝ) + 1 ≤ 2 ^ M := by exact_mod_cast Nat.lt_two_pow_self
  have e : (2 : ℝ) ^ (22 * M) = (2 ^ M) ^ 2 * 2 ^ (20 * M) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  rw [e]
  have hB : (0 : ℝ) < 2 ^ (20 * M) := by positivity
  have hκ := abs_nonneg κ
  have hsq : ((M : ℝ) + 1) ^ 2 ≤ (2 ^ M) ^ 2 := pow_le_pow_left₀ (by positivity) h2M 2
  have key : 2 * (|κ| * (1 + 10 * M)) < ((M : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith

/-- `tpqpOrderD ≤ tpqpOrderF`. -/
theorem tpqpOrderD_le_tpqpOrderF {π : ℕ → ℝ} {q : ℕ} {ε : ℕ → ℝ} (h0 : 0 < ε 0) :
    tpqpOrderD π q ε ≤ tpqpOrderF π q ε :=
  Chapter12.finMax_le ((inv_nonneg.2 h0.le).trans inv_le_tpqpOrderF) fun _ hj =>
    term_le_tpqpOrderF hj

/-- **The count against the printed order**: for `M > 20|κ| + 20`, a count
`N ≥ 2^{22M} - 2^{18M} - 2^{10M} + 1` exceeds `κ (1 + |log(ε₀ ε_min)|) max[ε₀^{-1},
max_j ε₀^{-j} ε_j^{-(j+1)}]` at the tolerances `trqSlowTol M` (`q ≥ 2`). -/
theorem trqSlow_not_le_printed {q : ℕ} (hq : 2 ≤ q) {κ : ℝ} {M : ℕ} (hM : 20 * |κ| + 20 < M)
    {N : ℝ} (hN : ((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤ N) :
    ¬ N ≤ κ * (1 + trqSCLogTerm q (trqSlowTol M)) *
      tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) := by
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := by linarith [abs_nonneg κ]
    exact_mod_cast this.le
  have hΛ := trqSCLogTerm_trqSlowTol_le hq M
  have hΛ0 : 0 ≤ trqSCLogTerm q (trqSlowTol M) := abs_nonneg _
  have hO := tpqpOrderF_trqSlowTol_le (q := q) M
  have hO0 : 0 ≤ tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) :=
    zero_le_one.trans (one_le_tpqpOrderF (trqSlowTol_mem M 0).1 (trqSlowTol_mem M 0).2)
  have hR : κ * (1 + trqSCLogTerm q (trqSlowTol M)) *
      tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) ≤ |κ| * (1 + 10 * M) * 2 ^ (20 * M) := by
    have hX : 0 ≤ (1 + trqSCLogTerm q (trqSlowTol M)) *
        tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) := by positivity
    rw [mul_assoc, mul_assoc]
    refine (mul_le_mul_of_nonneg_right (le_abs_self κ) hX).trans
      (mul_le_mul_of_nonneg_left ?_ (abs_nonneg κ))
    exact mul_le_mul (by linarith) hO hO0 (by positivity)
  -- the count
  have hKs1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKle : 2 ^ (18 * M) + 2 ^ (10 * M) ≤ 2 ^ (22 * M) := by
    have a1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : 2 ^ (22 * M) = 2 * 2 ^ (22 * M - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hKs2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M) - 2 ^ (18 * M) :=
    Nat.le_sub_of_add_le (by rw [add_comm]; exact hKle)
  rw [Nat.cast_sub hKs2, Nat.cast_sub hKs1] at hN
  push_cast at hN
  have h18 : (2 : ℝ) ^ (18 * M) * 4 ≤ 2 ^ (22 * M) := by
    rw [show 22 * M = 18 * M + 2 + (4 * M - 2) by omega, pow_add, pow_add]
    have : (1 : ℝ) ≤ 2 ^ (4 * M - 2) := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) < 2 ^ (18 * M) := by positivity
    nlinarith
  have h10 : (2 : ℝ) ^ (10 * M) ≤ 2 ^ (18 * M) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfin := trqSlow_final_lt hM
  intro h
  linarith

/-- **Theorem 14.3.9 with a trust-region INNER fails in the printed order, `q ≥ 2`**
([cartis2022evaluation], Theorem 14.3.9 with the exponents `π_j = j + 1` of (14.2.12), OCR
l. 17583). For the fixed problem `f = 0`, `c(v) = (1, v_1^{-1/8}, v_2)`, `X = {v_1 ≥ 1}`,
`x₀ = (2, 0)` (which satisfies c.D1qLB.X, f.D1qLB.X and f.B.Fb, `trqSlowC_assumption`,
`trqSlowF_assumption`, `trqSlowF_assumptionBFb`), the fixed TRq parameters `trqSlowParams`,
`ϑ = 1`, `β₁ = trqSlowβ₁`, and every `θ ∈ (0, 1)` and `β`, there is no constant `κ` such that
every run of `IsTPqpGCTRqSCRun` that terminates in Phase 1 uses at most
`κ (1 + |log(ε₀ ε_min)|) max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}]` derivative evaluations, for all
tolerances `ε ∈ (0, 1]^{q+1}`. So the printed order fails even with the logarithmic factor and
even for the derivative evaluations alone (which are at most the function evaluations).

With `ε₀ = 1`, `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`, `ε_j = 1` (`j ≥ 3`) the printed order is
`2^{20M}`, while the run of `trqSlow_exists_tpqp_run` has at least `2^{22M}/2` successful
iterations: after the radius has been driven down to `≈ ε_1` (first-order failures across a
direction of unit curvature), the INNER run takes second-order steps of length `≈ ε_1` along the
first axis, where `ν` has slope `≈ v_1^{-5/4}` between `ε_2 ε_1` and `ε_1` and negligible
curvature; each decreases `ν` only by `≈ ε_2 ε_1²` and the first axis is long. -/
theorem theorem_14_3_9_trq_printed_false {q : ℕ} (hq : 2 ≤ q) {θ β : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    ¬ ∃ κ : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC trqSlowX q trqSlowParams 1 θ trqSlowβ₁ β ε
          (slowPt 2 0) xP δP k₁ D nF₁ nD₁ →
        θ * ε 0 < ‖trqSlowC (xP k₁)‖ →
        ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤
          κ * (1 + trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
  rintro ⟨κ, hκ⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (20 * |κ| + 20)
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := by linarith [abs_nonneg κ]
    exact_mod_cast this.le
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, hrun, hexit, hcount⟩ := trqSlow_exists_tpqp_run (β := β) hq hM1
    hθ0 hθ1 (ε := trqSlowTol M) (fun j _ => trqSlowTol_mem M j) (by simp [trqSlowTol])
    (by simp [trqSlowTol])
  have h := hκ (trqSlowTol M) (fun j _ => trqSlowTol_mem M j) xP δP k₁ D nF₁ nD₁ hrun hexit
  exact trqSlow_not_le_printed hq hM hcount h

/-- **The printed form of `theorem_14_3_9_trq` is false for every `q ≥ 2`.** The fixed problem of
`theorem_14_3_9_trq_printed_false` satisfies every hypothesis of `theorem_14_3_9_trq` (c.D1qLB.X,
f.D1qLB.X, f.B.Fb with `β_F = 1`, `ϑ = 1`, `θ ∈ (0, 1)`, `0 < β ≤ ϑ`, `β₁ ‖c(x₀)‖ ≤ ϑ`), but its
conclusion with the printed exponents `π_j = j + 1` in place of `q + 1` fails. -/
theorem theorem_14_3_9_trq_printed_false_conclusion {q : ℕ} (hq : 2 ≤ q) {θ β : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    AssumptionCD1pLBX trqSlowC trqSlowX trqSlowX₀ q (fun j => trqSlowCB (j + 1)) trqSlowCB ∧
    AssumptionD1pLBX (fun _ : ℝ² => (0 : ℝ)) trqSlowX trqSlowX₀ q (fun _ => 0) (fun _ => 0) ∧
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) trqSlowC trqSlowX 1 0 0 ∧
    (0 < β ∧ β ≤ 1) ∧ trqSlowβ₁ * ‖trqSlowC (slowPt 2 0)‖ ≤ 1 ∧
    ¬ ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ 1 →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC trqSlowX q trqSlowParams 1 θ trqSlowβ₁ β ε
          (slowPt 2 0) xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖trqSlowC (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) ∧
        (‖trqSlowC (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd (fun _ => 0) trqSlowC trqSlowX q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) := by
  refine ⟨trqSlowC_assumption q, trqSlowF_assumption q, trqSlowF_assumptionBFb 1, ⟨hβ0, hβ1⟩,
    by rw [trqSlowβ₁_mul]; norm_num, ?_⟩
  rintro ⟨κF, κL, κD, -, -, hκD, h⟩
  refine theorem_14_3_9_trq_printed_false hq (β := β) hθ0 hθ1 ⟨κD, fun ε hε xP δP k₁ D nF₁ nD₁ hrun
    hexit => ?_⟩
  have hε0 := hε 0 (by simp)
  have h1 := ((h ε hε hε0.2 xP δP k₁ D nF₁ nD₁ hrun).1 hexit).2
  have hDF := tpqpOrderD_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (q := q) hε0.1
  have hO1 := one_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (q := q) hε0.1 hε0.2
  have hΛ : 0 ≤ trqSCLogTerm q ε := abs_nonneg _
  calc _ ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε := h1
    _ ≤ κD * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := mul_le_mul_of_nonneg_left hDF hκD
    _ ≤ κD * (1 + trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
      rw [mul_assoc]
      gcongr
      nlinarith

/-- **Theorem 14.3.9 with a trust-region INNER fails in the printed order in Phase 2, `q ≥ 2`**
([cartis2022evaluation], Theorem 14.3.9, (14.2.12), OCR l. 17583). For the fixed problem `f = 0`,
`c₂(v) = (v_1^{-1/8}, v_2)`, `X = {v_1 ≥ 1}`, `x₀ = (256, 0)` (c.D1qLB.X, f.D1qLB.X, f.B.Fb:
`trqSlowC2_assumption`, `trqSlowF_assumption`, `trqSlowF_assumptionBFb2`), `θ = β = 1/2`, any
`β₁ ∈ (0, 1)`, the TRq parameters `trqSlowParams` and `ϑ = 1`, there is no `κ` such that every run
of `IsTPqpGCTRqSCRun` that enters Phase 2 reaches a termination index `k_ε` of Phase 2 with at most
`κ (1 + |log(ε₀ ε_min)|) max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}]` derivative evaluations in
Phase 2. The runs of `trqSlow_exists_tpqp_run_phase2` have a single INNER call on `μ(·, t_1)`,
the TRq-SC run of `trqSlow_exists_long_run` started at `(256, 0)`. -/
theorem theorem_14_3_9_trq_printed_false_phase2 {q : ℕ} (hq : 2 ≤ q) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) :
    ¬ ∃ κ : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC2 trqSlowX q trqSlowParams 1 (1 / 2) β₁ (1 / 2) ε
          (slowPt 256 0) xP δP k₁ D nF₁ nD₁ →
        ‖trqSlowC2 (xP k₁)‖ ≤ 1 / 2 * ε 0 →
        ∃ kε, D.IsEnd (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε kε ∧
          (D.derivEvals kε : ℝ) ≤
            κ * (1 + trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
  rintro ⟨κ, hκ⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (20 * |κ| + 20)
  have hM2 : 2 ≤ M := by
    have : (2 : ℝ) < M := by linarith [abs_nonneg κ]
    exact_mod_cast this.le
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, hrun, hph2, hcount⟩ := trqSlow_exists_tpqp_run_phase2 hq hM2
    hβ₁0 hβ₁1 (ε := trqSlowTol M) (fun j _ => trqSlowTol_mem M j) (by simp [trqSlowTol])
    (by simp [trqSlowTol]) (by simp [trqSlowTol])
  obtain ⟨kε, hend, h⟩ := hκ (trqSlowTol M) (fun j _ => trqSlowTol_mem M j) xP δP k₁ D nF₁ nD₁
    hrun hph2
  exact trqSlow_not_le_printed hq hM (hcount kε hend) h

/-- **The printed form of `theorem_14_3_9_trq` is false in Phase 2 for every `q ≥ 2`.** The fixed
problem of `theorem_14_3_9_trq_printed_false_phase2` satisfies every hypothesis of
`theorem_14_3_9_trq` (c.D1qLB.X, f.D1qLB.X, f.B.Fb with `β_F = 1`, `ϑ = 1`, `θ = β = 1/2`,
`β₁ ‖c₂(x₀)‖ = β₁/2 ≤ ϑ`), but its conclusion with the printed exponents `π_j = j + 1` fails,
through its Phase-2 part. -/
theorem theorem_14_3_9_trq_printed_false_conclusion_phase2 {q : ℕ} (hq : 2 ≤ q) {β₁ : ℝ}
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) :
    AssumptionCD1pLBX trqSlowC2 trqSlowX trqSlowX₀ q (fun j => trqSlowCB (j + 1)) trqSlowCB ∧
    AssumptionD1pLBX (fun _ : ℝ² => (0 : ℝ)) trqSlowX trqSlowX₀ q (fun _ => 0) (fun _ => 0) ∧
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 trqSlowX 1 0 0 ∧
    β₁ * ‖trqSlowC2 (slowPt 256 0)‖ ≤ 1 ∧
    ¬ ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ 1 →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC2 trqSlowX q trqSlowParams 1 (1 / 2) β₁ (1 / 2) ε
          (slowPt 256 0) xP δP k₁ D nF₁ nD₁ →
        (1 / 2 * ε 0 < ‖trqSlowC2 (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) ∧
        (‖trqSlowC2 (xP k₁)‖ ≤ 1 / 2 * ε 0 →
          ∃ kε, D.IsEnd (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) := by
  refine ⟨trqSlowC2_assumption q, trqSlowF_assumption q, trqSlowF_assumptionBFb2 1,
    by rw [norm_trqSlowC2_x₀]; linarith, ?_⟩
  rintro ⟨κF, κL, κD, -, -, hκD, h⟩
  refine theorem_14_3_9_trq_printed_false_phase2 hq hβ₁0 hβ₁1 ⟨κD, fun ε hε xP δP k₁ D nF₁ nD₁
    hrun hph2 => ?_⟩
  have hε0 := hε 0 (by simp)
  obtain ⟨kε, hend, -, h2⟩ := (h ε hε hε0.2 xP δP k₁ D nF₁ nD₁ hrun).2 hph2
  refine ⟨kε, hend, ?_⟩
  have hDF := tpqpOrderD_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (q := q) hε0.1
  have hO1 := one_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (q := q) hε0.1 hε0.2
  have hΛ : 0 ≤ trqSCLogTerm q ε := abs_nonneg _
  have hs : 0 ≤ ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  calc (D.derivEvals kε : ℝ) ≤ ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε := by linarith
    _ ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε := h2
    _ ≤ κD * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := mul_le_mul_of_nonneg_left hDF hκD
    _ ≤ κD * (1 + trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
      rw [mul_assoc]
      gcongr
      nlinarith

end Main

end CartisGouldToint.Chapter14
