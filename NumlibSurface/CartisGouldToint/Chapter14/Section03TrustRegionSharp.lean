import Numlib.Analysis.Calculus.MultivariateTaylor.Coord
import NumlibSurface.CartisGouldToint.Chapter14.Section03TrustRegion

/-!
# Cartis–Gould–Toint §14.2–§14.3: counterexamples for the trust-region INNER

Counterexamples for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Theorem 14.3.9 with INNER of
trust-region type (`Chapter14.Section03TrustRegion`).

The logarithmic factor of `theorem_14_3_9_trq` is needed for `q = 1`. Example: `n = 2`, `m = 1`,
`X = [0, 2] × [-1, 1]`, `f(x) = x_1`, `c(x) = x_2`, `x₀ = (2, 0)`, `ε_1 = 1/2`. Here
`μ(·, t) = ½ ‖r(·, t)‖²` is quadratic with unit Hessian and `‖∇μ‖ = ‖r‖ ≤ ε₀` at the start of
every INNER call, so a step of length `> 2‖r‖` increases `μ`. Every call restarts from the radius
`Δ₀` and spends `≈ log(1/ε₀)` unsuccessful iterations before a step can succeed (a call that does
not move fails every test of (14.3.32), since `x_1 ≥ 1` keeps the measure of (14.3.34) at
`≥ ‖r‖ δ/√2`). The targets decrease by at most `2ε₀` per outer iteration, so Phase 2 has at least
`⌊1/(4ε₀)⌋` outer iterations with `x_1 ≥ 1`. The example works for every `q ≥ 1` with
`ε_j = 1/2` (`j ≥ 1`): the first-order test fails at the start of every call, so the steps have
order `1`, and the runs use `≳ ε₀^{-1} log(1/ε₀)` evaluations, more than any `κ_F ε₀^{-1}`. For
`q ≥ 2` this does not show that the factor is needed: at these tolerances the printed order (and
the proved one) is at least `ε₀^{-2}`.

The per-iteration decrease (14.2.11) with the printed TRq-SC exponents `π_j = j + 1` of (14.2.12)
is false for `q = 2` with `κ_decr` depending only on the algorithm parameters, `ϑ` and the
constants of f.D1qLaB.X, as the book's explicit `κ_decr` of Lemma 12.2.4 / (12.2.14) does
(`lemma_14_2_2_trq_printed_false`, `lemma_14_2_2_trq_printed_false_uniform`). The example is a
family `f_a`, `a → 0`, with uniform constants; for a single fixed `f` this mechanism (a
stationary point of constant curvature) needs `q ≥ 3`, and a single fixed `f` is not treated
here. The trust-region radius is shared by all orders and is driven down to `≈ ε_min` by
unsuccessful first-order iterations; a second-order step at that radius then decreases `f` by
`≈ ε_2 ε_min²`, which can be much smaller than `min_j ε_j^{j+1}`. Example: `X = [-1, 1]²`,
`f_a(x) = x_1²/2 - a x_2²/2` (f.D1qLaB.X with constants `4` for every `a ∈ (0, 1]`), `ϑ = 1`,
fixed TRq parameters `trqSadP`, `ε_1 = r²`, `ε_2 = a = r`: the decrease is `r⁵/2`, against
`κ min(ε_1², ε_2³) = κ r⁴`. This agrees with the book's own Theorem 14.2.4, whose table lists
TRq-SC with the order `O(max_j ε_j^{-(q+1)})` (OCR l. 16351), and with the exponent `q + 1` of
Lemma 12.2.4 used in `Chapter14.Section03TrustRegion`.

## Main results

* `trqLog_assumptions`: the example satisfies X.CNe, c.D1qLB.X, f.D1qLB.X and f.B.Fb;
* `trqLog_call_stuck`, `trqLog_call_long`: every early INNER call has more than `L` iterations
  when `4ε₀/(ςβ) ≤ γ₁^L min(Δ₀, ϑ)` (any `q ≥ 1`);
* `trqLog_funEvals_ge`: Phase 2 uses at least `⌊1/(4ε₀)⌋ (L + 1)` evaluations (any `q ≥ 1`);
* `theorem_14_3_9_trq_log_necessary_inv`: for every `q ≥ 1`, no `κ_F` bounds the `(f, c)`
  evaluations of every run with TRq-SC calls by `κ_F ε₀^{-1}` when `ε_j = 1/2` (`j ≥ 1`);
* `theorem_14_3_9_trq_log_necessary`: no constant `κ_F` bounds the `(f, c)` evaluations of every
  run with TRq-SC calls by `κ_F max[ε₀^{-1}, ε₀^{-1} ε_1^{-2}]`, the printed order for `q = 1`;
* `inv_sq_le_tpqpOrderF_trqLogTol`: for `q ≥ 2` the printed order at these tolerances is at least
  `ε₀^{-2}`, so the example is not a counterexample there.
* `lemma_14_2_2_trq_printed_false`: for every `κ > 0` a TRq-SC run (`q = 2`, objective `f_a`
  with f.D1qLaB.X constants independent of `a`) has a successful iteration before termination
  decreasing `f_a` by less than `κ min_j ε_j^{j+1}`; `lemma_14_2_2_trq_printed_false_uniform`: no
  `κ > 0` uniform over the family works;
* `exists_algorithm_12_2_1_feasible` is used to continue the run after that iteration.
-/

open Set Metric
open scoped Nat ContDiff

namespace CartisGouldToint.Chapter14

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The objective `f(x) = x₁` of the example (`x₁ = v 0`). -/
noncomputable def trqLogF : ℝ² → ℝ := fun v => v 0

/-- The constraint `c(x) = x₂` of the example, as a map into `ℝ¹` (`x₂ = v 1`). -/
noncomputable def trqLogC : ℝ² → EuclideanSpace ℝ (Fin 1) := fun v => EuclideanSpace.single 0 (v 1)

/-- The feasible set `X = [0, 2] × [-1, 1]` of the example. -/
def trqLogX : Set ℝ² := {v | 0 ≤ v 0 ∧ v 0 ≤ 2 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1}

/-- The starting point `x₀ = (2, 0)` of the example. -/
noncomputable def trqLogX₀ : ℝ² := EuclideanSpace.single 0 2

/-- `‖c(v)‖ = |v₂|`. -/
theorem norm_trqLogC (v : ℝ²) : ‖trqLogC v‖ = |v 1| := by
  simp [trqLogC]

/-- `μ(v, t) = (v₂² + (v₁ - t)²)/2`. -/
theorem trqLogMerit_eq (t : ℝ) : Constrained.targetMerit trqLogF trqLogC t =
    fun v => ((v 1) ^ 2 + (v 0 - t) ^ 2) / 2 := by
  funext v
  simp [Constrained.targetMerit_def, norm_trqLogC, trqLogF, sq_abs]

/-- `‖r(v, t)‖ = √(v₂² + (v₁ - t)²)`. -/
theorem trqLogResid_eq (t : ℝ) (v : ℝ²) : Constrained.targetResidual trqLogF trqLogC t v =
    √((v 1) ^ 2 + (v 0 - t) ^ 2) := by
  simp [Constrained.targetResidual_def, norm_trqLogC, trqLogF, sq_abs]

/-- The derivative of `μ(·, t)`: `s ↦ v₂ s₂ + (v₁ - t) s₁`. -/
theorem hasFDerivAt_trqLogMerit (t : ℝ) (v : ℝ²) :
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
theorem taylorDecrement_trqLogMerit (t : ℝ) (v s : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v).taylorDecrement 1 s =
      -(v 1 * s 1 + (v 0 - t) * s 0) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply, trqLogMerit_eq]
  change -(iteratedFDeriv ℝ 1 _ v (fun _ => s)) = _
  rw [iteratedFDeriv_one_apply, (hasFDerivAt_trqLogMerit t v).fderiv]
  simp

/-- `‖s‖² = s₁² + s₂²` on `ℝ²`. -/
theorem trqLog_norm_sq (s : ℝ²) : ‖s‖ ^ 2 = (s 0) ^ 2 + (s 1) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [sq_abs]


/-- `μ(·, t)` is quadratic with unit Hessian:
`μ(v + s) = μ(v) + ∇μ(v)·s + ‖s‖²/2`. -/
theorem trqLogMerit_add (t : ℝ) (v s : ℝ²) :
    Constrained.targetMerit trqLogF trqLogC t (v + s) =
      Constrained.targetMerit trqLogF trqLogC t v +
      (v 1 * s 1 + (v 0 - t) * s 0) + ‖s‖ ^ 2 / 2 := by
  rw [trqLogMerit_eq, trqLog_norm_sq]
  simp only [PiLp.add_apply]
  ring

/-- `|∇μ(v)·s| ≤ ‖r(v, t)‖ ‖s‖` (Cauchy–Schwarz). -/
theorem trqLog_abs_lin_le (t : ℝ) (v s : ℝ²) :
    |v 1 * s 1 + (v 0 - t) * s 0| ≤ Constrained.targetResidual trqLogF trqLogC t v * ‖s‖ := by
  rw [trqLogResid_eq, ← Real.sqrt_sq (norm_nonneg s), trqLog_norm_sq,
    ← Real.sqrt_mul (by positivity)]
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (v 1 * s 0 - (v 0 - t) * s 1)]

/-- Membership in `X`. -/
theorem trqLogX_mem {v : ℝ²} : v ∈ trqLogX ↔ 0 ≤ v 0 ∧ v 0 ≤ 2 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1 := Iff.rfl

/-- The two coordinate directions give the lower bounds `(v₀ - t) δ` and `|v₁| δ` for the
first-order measure of `μ(·, t)` at `v ∈ X` with `t ≤ v₀` and `δ ≤ min(v₀, 1)`. -/
theorem trqLog_measure_ge {t δ : ℝ} {v : ℝ²} (hv : v ∈ trqLogX) (hδ0 : 0 ≤ δ) (hδv : δ ≤ v 0)
    (hδ1 : δ ≤ 1) :
    (v 0 - t) * δ ≤ Optimization.taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 δ {d | v + d ∈ trqLogX} ∧
      |v 1| * δ ≤ Optimization.taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 δ
          {d | v + d ∈ trqLogX} := by
  obtain ⟨h0, h2, h3, h4⟩ := hv
  constructor
  · have hd : ((-δ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ²) ∈
        closedBall (0 : ℝ²) δ ∩ {d | v + d ∈ trqLogX} := by
      refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
      · rw [norm_smul]; simp [abs_of_nonneg hδ0]
      · simp only [Set.mem_ofPred_eq, trqLogX_mem, PiLp.add_apply, PiLp.smul_apply,
          PiLp.single_apply]
        norm_num
        refine ⟨by linarith, by linarith, h3, h4⟩
    have := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 hd
    rw [taylorDecrement_trqLogMerit] at this
    simp only [PiLp.smul_apply, PiLp.single_apply] at this
    norm_num at this
    linarith
  · rcases le_total 0 (v 1) with hs | hs
    · have hd : ((-δ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ²) ∈
          closedBall (0 : ℝ²) δ ∩ {d | v + d ∈ trqLogX} := by
        refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
        · rw [norm_smul]; simp [abs_of_nonneg hδ0]
        · simp only [Set.mem_ofPred_eq, trqLogX_mem, PiLp.add_apply, PiLp.smul_apply,
            PiLp.single_apply]
          norm_num
          refine ⟨h0, h2, by linarith, by linarith⟩
      have := Optimization.taylorDecrement_le_taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 hd
      rw [taylorDecrement_trqLogMerit] at this
      simp only [PiLp.smul_apply, PiLp.single_apply] at this
      norm_num at this
      rw [abs_of_nonneg hs]
      linarith
    · have hd : (δ • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ²) ∈
          closedBall (0 : ℝ²) δ ∩ {d | v + d ∈ trqLogX} := by
        refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
        · rw [norm_smul]; simp [abs_of_nonneg hδ0]
        · simp only [Set.mem_ofPred_eq, trqLogX_mem, PiLp.add_apply, PiLp.smul_apply,
            PiLp.single_apply]
          norm_num
          refine ⟨h0, h2, by linarith, by linarith⟩
      have := Optimization.taylorDecrement_le_taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 hd
      rw [taylorDecrement_trqLogMerit] at this
      simp only [PiLp.smul_apply, PiLp.single_apply] at this
      norm_num at this
      rw [abs_of_nonpos hs]
      linarith

/-- (14.3.34) fails at every `v ∈ X` with `t ≤ v₀`, positive residual and radius
`δ ≤ min(v₀, 1)`, for `ε₁ = 1/2` and every `q ≥ 1` (its first-order part fails). -/
theorem trqLog_not_meritCrit {q : ℕ} (hq : 1 ≤ q) {t : ℝ} {v : ℝ²} {ε δo : ℕ → ℝ}
    (hε1 : ε 1 = 1 / 2) (hv : v ∈ trqLogX)
    (ht : t ≤ v 0) (hρ : 0 < Constrained.targetResidual trqLogF trqLogC t v) (hδ0 : 0 < δo 1)
    (hδv : δo 1 ≤ v 0) (hδ1 : δo 1 ≤ 1) : ¬ meritCrit trqLogF trqLogC trqLogX q ε t v δo := by
  intro hm
  have h := hm 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
  obtain ⟨ha, hb⟩ := trqLog_measure_ge (t := t) hv hδ0.le hδv hδ1
  rw [hε1] at h
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  set ρ := Constrained.targetResidual trqLogF trqLogC t v with hρdef
  have hsq : ρ ^ 2 = (v 1) ^ 2 + (v 0 - t) ^ 2 := by
    rw [hρdef, trqLogResid_eq, Real.sq_sqrt (by positivity)]
  have h1 : v 0 - t ≤ ρ / 2 := by nlinarith
  have h2 : |v 1| ≤ ρ / 2 := by nlinarith
  have h3 : (v 1) ^ 2 ≤ (ρ / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : (v 0 - t) ^ 2 ≤ (ρ / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  nlinarith


/-- At `v ∈ X` with `t ≤ v₁` and `v₁ ≥ 1`, positive residual `ρ`, radius `δ ∈ (0, 1]` and
`β ≤ 1`, the first-order measure of `μ(·, t)` exceeds `β ρ δ/2`: it is at least
`max(v₁ - t, |v₂|) δ ≥ ρ δ/√2` (`trqLog_measure_ge`). -/
theorem trqLog_measure_gt {t δ β : ℝ} {v : ℝ²} (hv : v ∈ trqLogX) (ht : t ≤ v 0) (hx1 : 1 ≤ v 0)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hβ1 : β ≤ 1)
    (hρ : 0 < Constrained.targetResidual trqLogF trqLogC t v) :
    β * Constrained.targetResidual trqLogF trqLogC t v * (1 / 2) * δ <
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1
        δ {d | v + d ∈ trqLogX} := by
  obtain ⟨ha, hb⟩ := trqLog_measure_ge (t := t) hv hδ0.le (hδ1.trans hx1) hδ1
  set M := Optimization.taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 δ {d | v + d ∈ trqLogX}
  set ρ := Constrained.targetResidual trqLogF trqLogC t v with hρdef
  have hsq : ρ ^ 2 = (v 1) ^ 2 + (v 0 - t) ^ 2 := by
    rw [hρdef, trqLogResid_eq, Real.sq_sqrt (by positivity)]
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

/-- **A TRq-SC call on `μ(·, t)` stays at its start for `L` iterations** (any `q ≥ 1`): if the
call starts at `x_{k,0} ∈ X` with `t ≤ (x_{k,0})_1` and `(x_{k,0})_1 ≥ 1`, the residual
`ρ₀ = ‖r(x_{k,0}, t)‖ ∈ (0, ε₀]`, the tolerance is `ε'_1 = β ρ₀/2` with `β ≤ 1`, `ϑ ≤ 1` and
`4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`, then every iteration `i < min(e, L)` is unsuccessful: the
first-order test fails at `x_{k,0}` (its measure is at least `ρ₀ δ/√2 > ε'_1 δ`), so the step has
order `1`; the radius is at least `4 ρ₀/(ς β)`, so the step has length `> 2 ρ₀` and increases
`μ(·, t)` (`μ` is quadratic with unit Hessian). Hence a call of length `e ≤ L` ends where it
started. -/
theorem trqLog_call_stuck {q : ℕ} (hq : 1 ≤ q) {P : Optimization.TRqParams} {ϑ β ε₀ t : ℝ}
    {xi : ℕ → ℝ²} {e : ℕ} {succ : ℕ → Prop} {δo ε' : ℕ → ℝ}
    (h : IsTRqSCCallOut (Constrained.targetMerit trqLogF trqLogC t) trqLogX q P ϑ ε' xi e succ δo)
    (hε' : ε' 1 = β * Constrained.targetResidual trqLogF trqLogC t (xi 0) * (1 / 2))
    (hρ : 0 < Constrained.targetResidual trqLogF trqLogC t (xi 0))
    (hρε : Constrained.targetResidual trqLogF trqLogC t (xi 0) ≤ ε₀) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hϑ : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) (hX : xi 0 ∈ trqLogX) (ht : t ≤ (xi 0) 0) (hx1 : 1 ≤ (xi 0) 0)
    {L : ℕ} (hL : 4 * ε₀ / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ) (he : e ≤ L) : xi e = xi 0 := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, hek, hxi, -, -⟩ := h
  set F := Constrained.targetMerit trqLogF trqLogC t with hF
  set ρ₀ := Constrained.targetResidual trqLogF trqLogC t (xi 0) with hρ₀
  have hγ0 := P.γ₁_pos
  have hγ1 := P.γ₁_le_one
  have hς := P.ς_pos
  have key : ∀ i ≤ e, x i = x 0 ∧ P.γ₁ ^ i * P.Δ₀ ≤ Δ i := by
    intro i
    induction i with
    | zero => intro _; exact ⟨rfl, by rw [pow_zero, one_mul, hr.toIsTRRun.delta_zero]⟩
    | succ i ih =>
      intro hi
      obtain ⟨hxi0, hΔi⟩ := ih (by omega)
      have hk : ∀ l ≤ i, ¬ Chapter12.trqStop F P q ε' ϑ x Δ d l :=
        fun l hl => hhit.2 l (by omega)
      have hst := Optimization.IsTRqRun.isTRqStep hr hk
      have hx0 : x 0 = xi 0 := (hxi 0 (Nat.zero_le _)).symm
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
        have hδpos : 0 < δ := lt_min hΔpos (by
          rcases hϑ.lt_or_eq with h' | h'
          · exact h'
          · exfalso
            have : min P.Δ₀ ϑ = 0 := by rw [← h']; exact min_eq_right P.Δ₀_pos.le
            rw [this, mul_zero] at hL
            have : 0 < 4 * ε₀ / (P.ς * β) := by
              have : 0 < ε₀ := hρ.trans_le hρε
              have := P.ς_pos
              positivity
            linarith)
        have hgt := trqLog_measure_gt hX ht hx1 hδpos ((min_le_right _ _).trans hϑ1) hβ1 hρ
        have hw' : P.ς * Optimization.taylorMeasure (ftaylorSeries ℝ F (xi 0)) 1 δ
            {d | xi 0 + d ∈ trqLogX} ≤ P.ς * (β * ρ₀ * (1 / 2) * δ) :=
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
      have hρ₀' : Constrained.targetResidual trqLogF trqLogC t (x i) = ρ₀ := by
        rw [hxi0, ← hxi 0 (Nat.zero_le _)]
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
        have := trqLog_abs_lin_le t (x i) (s i)
        rw [hρ₀'] at this
        rw [hPd, hF, taylorDecrement_trqLogMerit]
        exact (neg_le_abs _).trans this
      have hPd0 : 0 < Pd := lt_of_le_of_lt (by positivity) hPd_big
      have hs : 2 * ρ₀ < ‖s i‖ := by
        by_contra hc
        push Not at hc
        nlinarith [mul_le_mul_of_nonneg_left hc hρ.le]
      have hratio : Chapter12.trqRho F x s jk i < P.η₁ := by
        change Optimization.trqRatio F (fun k => ftaylorSeries ℝ F (x k)) x s jk i < P.η₁
        rw [Optimization.trqRatio_eq, hj, Optimization.reductionRatio_def, ← hPd]
        have hadd := trqLogMerit_add t (x i) (s i)
        rw [← hF] at hadd
        have hlin : (x i) 1 * (s i) 1 + ((x i) 0 - t) * (s i) 0 = -Pd := by
          rw [hPd, hF, taylorDecrement_trqLogMerit]; ring
        rw [hadd, hlin]
        have hnum : F (x i) - (F (x i) + -Pd + ‖s i‖ ^ 2 / 2) < 0 := by
          have : 2 * Pd < ‖s i‖ ^ 2 := by
            have := mul_le_mul_of_nonneg_left hPd_le (le_of_lt (by positivity : (0:ℝ) < 2))
            nlinarith
          linarith
        exact (div_neg_of_neg_of_pos hnum hPd0).trans P.η₁_pos
      have hacc := hr.accept i hk
      refine ⟨?_, ?_⟩
      · rw [hacc.eq_self hratio, hxi0]
      · have := (hacc.2.unsuccessful hratio).1
        calc P.γ₁ ^ (i + 1) * P.Δ₀ = P.γ₁ * (P.γ₁ ^ i * P.Δ₀) := by ring
          _ ≤ P.γ₁ * Δ i := mul_le_mul_of_nonneg_left hΔi hγ0.le
          _ ≤ Δ (i + 1) := this
  rw [hxi e le_rfl, hxi 0 (Nat.zero_le _), (key e le_rfl).1]


section Run

variable {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝ²} {D : TPqpSeq 2} {q : ℕ}

/-- `f(x_{k+1}) ≥ t_k - ε₀` along Phase 2. -/
theorem trqLog_f_succ_ge (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε x₁ D) {k : ℕ}
    (hk1 : 1 ≤ k)
    (hk : D.Before trqLogF trqLogC trqLogX q θ ε k) : D.t k - ε 0 ≤ trqLogF (D.x (k + 1)) := by
  have h1 := (Constrained.abs_sub_le_targetResidual (f := trqLogF) (c := trqLogC) (t := D.t k)
    (x := D.x (k + 1)))
  have h2' := h2.resid_succ_le hk1 hk
  have h3 := (h2.isTargetSequence hk).residual_le h2.θ_lt_one.le h2.ε₀_pos.le hk1 le_rfl
  have := neg_abs_le (trqLogF (D.x (k + 1)) - D.t k)
  linarith

/-- **The targets decrease by at most `2 ε₀` per outer iteration**: starting from
`x₁ = (2, 0)`, `t_k ≥ 2 - (2k - 1) ε₀` for every outer iteration `k ≥ 1` reached. -/
theorem trqLog_target_ge (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε trqLogX₀ D) :
    ∀ k, 1 ≤ k → D.Before trqLogF trqLogC trqLogX q θ ε k → 2 - (2 * k - 1) * ε 0 ≤ D.t k := by
  have hε₀ := h2.ε₀_pos
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    rw [h2.t_one]
    have hc : ‖trqLogC trqLogX₀‖ = 0 := by simp [norm_trqLogC, trqLogX₀]
    have hf : trqLogF trqLogX₀ = 2 := by simp [trqLogF, trqLogX₀]
    rw [hc, hf, show ε 0 ^ 2 - (0 : ℝ) ^ 2 = ε 0 ^ 2 by ring, Real.sqrt_sq hε₀.le]
    push_cast; linarith
  | succ k hk1 ih =>
    intro hK
    have hk := hK.mono k.le_succ
    have ihk := ih hk
    have hs : ¬ D.Stop trqLogF trqLogC trqLogX q θ ε k := hK k hk1 (Nat.lt_succ_self k)
    have hf := trqLog_f_succ_ge h2 hk1 hk
    push_cast
    rcases Constrained.TargetFollowingSeq.ka_or_kb_of_not_stop hs with ha | hb
    · rw [h2.t_succ_a k hk1 hk ha]
      have : √(ε 0 ^ 2 - ‖trqLogC (D.x (k + 1))‖ ^ 2) ≤ ε 0 := by
        calc √(ε 0 ^ 2 - ‖trqLogC (D.x (k + 1))‖ ^ 2) ≤ √(ε 0 ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (trqLogC (D.x (k + 1)))])
          _ = ε 0 := Real.sqrt_sq hε₀.le
      linarith
    · rw [h2.t_succ_b k hk1 hk hb]
      linarith

/-- **Phase 2 cannot stop early**: at an outer iteration `k ≥ 1` reached with
`(2k + 1) ε₀ ≤ 1`, the iterate `x_{k+1}` has `f ≥ 1`, so (14.3.34) fails there for every
target that Step 2 can produce, and the Step-1 output condition (14.3.32) excludes case (c). -/
theorem trqLog_not_stop (hq : 1 ≤ q)
    (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε trqLogX₀ D) (hε1 : ε 1 = 1 / 2)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before trqLogF trqLogC trqLogX q θ ε k)
    (hkε : (2 * k + 1) * ε 0 ≤ 1) : ¬ D.Stop trqLogF trqLogC trqLogX q θ ε k := by
  have hε₀ := h2.ε₀_pos
  have hθ := h2.θ_pos
  have ht := trqLog_target_ge h2 k hk1 hk
  have hf := trqLog_f_succ_ge h2 hk1 hk
  have hy1 : 1 ≤ (D.x (k + 1)) 0 := by
    change 1 ≤ trqLogF (D.x (k + 1)); nlinarith
  have hyX := h2.mem_succ k hk1 hk
  obtain ⟨hδ0, hδ1⟩ := h2.radius_mem k hk1 hk 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
  have hδy : D.δ (k + 1) 1 ≤ (D.x (k + 1)) 0 := hδ1.trans hy1
  have hθε : 0 < θ * ε 0 := mul_pos hθ hε₀
  rintro (⟨hna, hnb⟩ | ⟨hab, hm⟩)
  · -- case (c)
    have hge : θ * ε 0 ≤ Constrained.targetResidual trqLogF trqLogC (D.t k) (D.x (k + 1)) :=
      not_lt.1 hna
    have hft : D.t k ≤ trqLogF (D.x (k + 1)) := not_lt.1 fun hlt => hnb ⟨hge, hlt⟩
    rcases h2.output k hk1 hk with h | h | h
    · exact hna h
    · exact hnb ⟨hge, h⟩
    · exact trqLog_not_meritCrit hq hε1 hyX hft (hθε.trans_le hge) hδ0 hδy hδ1 h
  · change meritCrit trqLogF trqLogC trqLogX q ε (D.t (k + 1)) (D.x (k + 1)) (D.δ (k + 1)) at hm
    rcases hab with ha | hb
    · rw [h2.t_succ_a k hk1 hk ha] at hm
      have hc : ‖trqLogC (D.x (k + 1))‖ ≤ ε 0 :=
        Constrained.norm_le_targetResidual.trans (ha.le.trans
          (mul_le_of_le_one_left hε₀.le h2.θ_lt_one.le))
      refine trqLog_not_meritCrit hq hε1 hyX ?_ ?_ hδ0 hδy hδ1 hm
      · change _ ≤ trqLogF (D.x (k + 1)); linarith [Real.sqrt_nonneg
          (ε 0 ^ 2 - ‖trqLogC (D.x (k + 1))‖ ^ 2)]
      · rw [Constrained.targetResidual_sub_sqrt hε₀.le hc]; exact hε₀
    · rw [h2.t_succ_b k hk1 hk hb] at hm
      refine trqLog_not_meritCrit hq hε1 hyX ?_ ?_ hδ0 hδy hδ1 hm
      · change _ ≤ trqLogF (D.x (k + 1)); linarith [hb.2]
      · rw [Constrained.targetResidual_two_mul_sub]; exact hθε.trans_le hb.1

end Run


section Count

variable {P : Optimization.TRqParams} {ϑ θ β β₁ : ℝ} {ε : ℕ → ℝ} {xP : ℕ → ℝ²}
  {δP : ℕ → ℕ → ℝ} {k₁ : ℕ} {D : TPqpSeq 2} {q : ℕ} {nF₁ nD₁ : ℕ → ℕ}

/-- Phase 1 stops at once: `c(x₀) = 0`. -/
theorem trqLog_phase1 (h : algorithm_14_3_2 trqLogF trqLogC trqLogX q θ β₁ β ε trqLogX₀ xP δP k₁ D)
    (hθ : 0 < θ) : k₁ = 0 ∧ xP k₁ = trqLogX₀ := by
  have hε₀ : 0 < ε 0 := by
    have := h.phase1.ε_pos 0 (by simp)
    rw [phase1Tol_zero] at this
    exact pos_of_mul_pos_right this hθ.le
  have hstop : lenStop trqLogC trqLogX q (phase1Tol θ ε) xP δP 0 := by
    left
    rw [h.start, phase1Tol_zero]
    simp only [norm_trqLogC, trqLogX₀]
    simp only [PiLp.single_apply]
    norm_num
    positivity
  have hk : k₁ = 0 := by
    by_contra hne
    exact h.phase1_end.2 0 (Nat.pos_of_ne_zero hne) hstop
  exact ⟨hk, by rw [hk, h.start]⟩

/-- **Every call of an early outer iteration is long**: at an outer iteration `k ≥ 1` reached
with `(2k - 1) ε₀ ≤ 1`, a TRq-SC call has more than `L` iterations when
`4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`: otherwise it returns `x_{k+1} = x_k`, where no test of
(14.3.32) holds. -/
theorem trqLog_call_long (hq : 1 ≤ q)
    (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε trqLogX₀ D)
    (hcalls : IsTRqSCPhase2Calls trqLogF trqLogC trqLogX q P ϑ θ β ε D) (hε1 : ε 1 = 1 / 2)
    (hϑ : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) {L : ℕ} (hL : 4 * ε 0 / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before trqLogF trqLogC trqLogX q θ ε k) (hkε : (2 * k - 1) * ε 0 ≤ 1) :
    L < D.e k := by
  by_contra hle
  push Not at hle
  have hε₀ := h2.ε₀_pos
  have hθε : 0 < θ * ε 0 := mul_pos h2.θ_pos hε₀
  have hlo := h2.le_targetResidual k hk1 hk
  have hhi := (h2.isTargetSequence hk).residual_le h2.θ_lt_one.le hε₀.le hk1 le_rfl
  have h0 := h2.inner_zero k hk1 hk
  have ht := trqLog_target_ge h2 k hk1 hk
  have hft : D.t k ≤ trqLogF (D.x k) := by
    have := (h2.isTargetSequence hk).sub_target_nonneg hk1 le_rfl; linarith
  have hx1 : 1 ≤ (D.x k) 0 := by change 1 ≤ trqLogF (D.x k); linarith
  have hβ1 : β ≤ 1 := h2.β_le_θ.trans h2.θ_lt_one.le
  have hstuck := trqLog_call_stuck hq (hcalls k hk1 hk) (by rw [h0, hε1])
    (by rw [h0]; linarith) (by rw [h0]; exact hhi) h2.β_pos hβ1 hϑ hϑ1
    (by rw [h0]; exact h2.x_mem k hk1 hk) (by rw [h0]; exact hft) (by rw [h0]; exact hx1) hL hle
  have hx : D.x (k + 1) = D.x k := by rw [← h2.inner_end k hk1 hk, hstuck, h0]
  obtain ⟨hδ0, hδ1⟩ := h2.radius_mem k hk1 hk 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
  rcases h2.output k hk1 hk with h | h | h
  · rw [hx] at h; linarith
  · rw [hx] at h; linarith
  · rw [hx] at h
    exact trqLog_not_meritCrit hq hε1 (h2.x_mem k hk1 hk) hft (hθε.trans_le hlo) hδ0
      (hδ1.trans hx1) hδ1 h

/-- **The evaluation count of Phase 2 is at least `⌊1/(4ε₀)⌋ (L + 1)`** for every TPqp-GC run
with TRq-SC calls on this example, when `ε₀ ≤ 1/2` and `4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`. -/
theorem trqLog_funEvals_ge (hq : 1 ≤ q)
    (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε trqLogX₀ D)
    (hcalls : IsTRqSCPhase2Calls trqLogF trqLogC trqLogX q P ϑ θ β ε D) (hε1 : ε 1 = 1 / 2)
    (hε₀2 : ε 0 ≤ 1 / 2) (hϑ : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) {L : ℕ}
    (hL : 4 * ε 0 / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ) {kε : ℕ}
    (hend : D.IsEnd trqLogF trqLogC trqLogX q θ ε kε) :
    (⌊1 / (4 * ε 0)⌋₊ : ℝ) * (L + 1) ≤ D.funEvals kε := by
  have hε₀ := h2.ε₀_pos
  obtain ⟨hkε1, hstop, hbef⟩ := hend
  set N := ⌊1 / (4 * ε 0)⌋₊ with hN
  have hNle : (N : ℝ) ≤ 1 / (4 * ε 0) := Nat.floor_le (by positivity)
  -- `kε` is large
  have hbig : 1 < (2 * kε + 1) * ε 0 := by
    by_contra hc
    push Not at hc
    exact trqLog_not_stop hq h2 hε1 hkε1 hbef hc hstop
  have hNk : N ≤ kε := by
    have : (N : ℝ) ≤ kε := by
      have h1 : 1 / (4 * ε 0) ≤ (kε : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    exact_mod_cast this
  have hcount : ∀ k ∈ Finset.Icc 1 N, L + 1 ≤ D.e k := fun k hk => by
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    have hkb : D.Before trqLogF trqLogC trqLogX q θ ε k :=
      hbef.mono (hkN.trans hNk)
    have hkε : (2 * k - 1) * ε 0 ≤ 1 := by
      have : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have : (k : ℝ) * ε 0 ≤ 1 / 4 := by
        calc (k : ℝ) * ε 0 ≤ (1 / (4 * ε 0)) * ε 0 := by gcongr; linarith
          _ = 1 / 4 := by field_simp
      nlinarith
    exact trqLog_call_long hq h2 hcalls hε1 hϑ hϑ1 hL hk1 hkb hkε
  have hsum : N * (L + 1) ≤ ∑ j ∈ Finset.Icc 1 kε, D.e j := by
    calc N * (L + 1) = ∑ _j ∈ Finset.Icc 1 N, (L + 1) := by simp
      _ ≤ ∑ j ∈ Finset.Icc 1 N, D.e j := Finset.sum_le_sum hcount
      _ ≤ ∑ j ∈ Finset.Icc 1 kε, D.e j :=
          Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right hNk)
  unfold TPqpSeq.funEvals
  have : ((N * (L + 1) : ℕ) : ℝ) ≤ ((1 + ∑ j ∈ Finset.Icc 1 kε, D.e j : ℕ) : ℝ) := by
    exact_mod_cast hsum.trans (Nat.le_add_left _ _)
  push_cast at this ⊢
  exact this

end Count


section Data

/-- The coordinates are continuous. -/
theorem trqLog_continuous_coord (i : Fin 2) : Continuous (fun v : ℝ² => v i) :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).continuous

/-- The coordinates are smooth. -/
theorem trqLog_contDiff_coord (i : Fin 2) : ContDiff ℝ ∞ (fun v : ℝ² => v i) :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).contDiff

/-- `X` is closed. -/
theorem isClosed_trqLogX : IsClosed trqLogX := by
  have hc : ∀ a : ℝ, Continuous fun _ : ℝ² => a := fun a => continuous_const
  have h := ((isClosed_le (hc 0) (trqLog_continuous_coord 0)).inter
    (isClosed_le (trqLog_continuous_coord 0) (hc 2))).inter
    ((isClosed_le (hc (-1)) (trqLog_continuous_coord 1)).inter
    (isClosed_le (trqLog_continuous_coord 1) (hc 1)))
  convert h using 1
  ext v
  simp only [trqLogX, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- `x₀ ∈ X`. -/
theorem trqLogX₀_mem : trqLogX₀ ∈ trqLogX := by
  simp only [trqLogX_mem, trqLogX₀, PiLp.single_apply]
  norm_num

/-- `X` lies in the ball of radius `3`. -/
theorem trqLogX_subset_ball : trqLogX ⊆ ball (0 : ℝ²) 3 := by
  intro v hv
  obtain ⟨h0, h2, h3, h4⟩ := hv
  rw [mem_ball_zero_iff]
  have hs := trqLog_norm_sq v
  have : ‖v‖ ^ 2 < 3 ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this

/-- **The example satisfies the hypotheses of Theorem 14.3.9 with a trust-region INNER** (of the
printed statement, and of `theorem_14_3_9_trq_one`), for every `q`: `X` is closed, c.D1qLB.X
and f.D1qLB.X hold on the ball of radius `3` (with some constants), and f.B.Fb holds for every
`β_F` with `f_low = 0`, `f_up = 2`. -/
theorem trqLog_assumptions (q : ℕ) : IsClosed trqLogX ∧ trqLogX₀ ∈ trqLogX ∧
    (∃ Lc Bc : ℕ → ℝ, AssumptionCD1pLBX trqLogC trqLogX (ball 0 3) q Lc Bc) ∧
    (∃ Lf Bf : ℕ → ℝ, AssumptionD1pLBX trqLogF trqLogX (ball 0 3) q Lf Bf) ∧
    ∀ βF, Chapter07.AssumptionBFb trqLogF trqLogC trqLogX βF 0 2 := by
  refine ⟨isClosed_trqLogX, trqLogX₀_mem, ?_, ?_, fun βF x hx => ⟨hx.1.1, hx.1.2.1⟩⟩
  · obtain ⟨L, B, h⟩ := exists_assumptionD1pLBX_ball (trqLog_contDiff_coord 1) trqLogX_subset_ball q
    refine ⟨L, B, ⟨isOpen_ball, convex_ball 0 3, trqLogX_subset_ball, fun i => ?_⟩⟩
    have : (fun x => trqLogC x i) = fun v : ℝ² => v 1 := by
      funext x
      rw [Subsingleton.elim i 0]
      simp [trqLogC]
    rw [this]
    exact h
  · exact exists_assumptionD1pLBX_ball (trqLog_contDiff_coord 0) trqLogX_subset_ball q

end Data


/-- The tolerances `ε₀` and `ε_j = 1/2` (`j ≥ 1`) of the example. -/
noncomputable def trqLogTol (ε₀ : ℝ) : ℕ → ℝ := fun j => if j = 0 then ε₀ else 1 / 2

/-- The printed order of the `(f, c)` evaluations for `q = 1`, `π_1 = 2`, `ε_1 = 1/2` is at most
`4/ε₀`. -/
theorem tpqpOrderF_trqLogTol_le {ε₀ : ℝ} (h0 : 0 < ε₀) :
    tpqpOrderF (fun j => (j : ℝ) + 1) 1 (trqLogTol ε₀) ≤ 4 / ε₀ := by
  unfold tpqpOrderF
  refine Chapter12.finMax_le ?_ fun j hj => ?_
  · simp only [trqLogTol, ↓reduceIte]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by norm_num) h0.le
  · rw [Finset.Icc_self, Finset.mem_singleton] at hj
    subst hj
    simp only [trqLogTol, ↓reduceIte, one_ne_zero]
    norm_num
    rw [Real.rpow_neg_one, div_eq_mul_inv, mul_comm]

/-- **Every bound of the form `κ_F ε₀^{-1}` on the `(f, c)` evaluations fails for genuine runs
with TRq-SC calls, for every `q ≥ 1`** ([cartis2022evaluation], Theorem 14.3.9 with INNER of
trust-region type). On the example `n = 2`, `m = 1`, `X = [0, 2] × [-1, 1]`, `f(x) = x_1`,
`c(x) = x_2`, `x₀ = (2, 0)` (`trqLog_assumptions`), with the dual tolerances fixed at
`ε_j = 1/2` (`trqLogTol`), for all TRq parameters `P`, `0 < β ≤ θ < 1`, `β ≤ ϑ ≤ 1`,
`β₁ ∈ (0, 1)` and `β_F > 0`, there is no `κ_F` such that every run of `IsTPqpGCTRqSCRun`
entering Phase 2 terminates within `κ_F/ε₀` evaluations of `(f, c)` for all `ε₀ ∈ (0, 1]` with
`ε₀ ≤ β_F`: every call of the first `⌊1/(4ε₀)⌋` outer iterations restarts from `Δ₀` and needs
`≳ log(1/ε₀)` unsuccessful first-order iterations (`trqLog_call_long`, `trqLog_funEvals_ge`).

For `q = 1` this is the printed order (`theorem_14_3_9_trq_log_necessary`). For `q ≥ 2` it does
not contradict the printed order, nor the order with the exponents `q + 1`: at these tolerances
both are at least `ε₀^{-2}` (`inv_sq_le_tpqpOrderF_trqLogTol`), while the lower bound this
example gives is only of order `ε₀^{-1} log(1/ε₀)`. -/
theorem theorem_14_3_9_trq_log_necessary_inv {q : ℕ} (hq : 1 ≤ q) (P : Optimization.TRqParams)
    {ϑ θ β β₁ βF : ℝ} (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hβϑ : β ≤ ϑ) (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) (hβF : 0 < βF) :
    ¬ ∃ κF : ℝ, ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ε₀ ≤ βF →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun trqLogF trqLogC trqLogX q P ϑ θ β₁ β (trqLogTol ε₀) trqLogX₀ xP δP k₁ D
          nF₁ nD₁ →
        ‖trqLogC (xP k₁)‖ ≤ θ * ε₀ →
        ∃ kε, D.IsEnd trqLogF trqLogC trqLogX q θ (trqLogTol ε₀) kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF / ε₀ := by
  rintro ⟨κF, hκ⟩
  have hϑ0 : 0 < ϑ := hβ0.trans_le hβϑ
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ⌈8 * |κF|⌉₊ := ⟨_, rfl⟩
  have hL8 : 8 * |κF| ≤ L := hL ▸ Nat.le_ceil _
  obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ,
      ε₀ = min (min (1 / 8) βF) (P.γ₁ ^ L * min P.Δ₀ ϑ * P.ς * β / 4) := ⟨_, rfl⟩
  have hε₀ : 0 < ε₀ := by
    rw [hε₀def]
    have := P.ς_pos
    have := pow_pos P.γ₁_pos L
    have := lt_min P.Δ₀_pos hϑ0
    exact lt_min (lt_min (by norm_num) hβF) (by positivity)
  have hε₀8 : ε₀ ≤ 1 / 8 := hε₀def ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hε₀F : ε₀ ≤ βF := hε₀def ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hε₀L : ε₀ ≤ P.γ₁ ^ L * min P.Δ₀ ϑ * P.ς * β / 4 := hε₀def ▸ min_le_right _ _
  have hLcond : 4 * trqLogTol ε₀ 0 / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ := by
    simp only [trqLogTol, ↓reduceIte]
    have := P.ς_pos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hε : ∀ j ∈ Finset.range (q + 1), 0 < trqLogTol ε₀ j ∧ trqLogTol ε₀ j ≤ 1 := by
    intro j _
    by_cases hj : j = 0
    · simp only [trqLogTol, hj, ↓reduceIte]; exact ⟨hε₀, by linarith⟩
    · simp only [trqLogTol, hj, ↓reduceIte]; norm_num
  obtain ⟨-, -, ⟨Lc, Bc, hc⟩, ⟨Lf, Bf, hf⟩, -⟩ := trqLog_assumptions q
  have hc0 : ‖trqLogC trqLogX₀‖ = 0 := by simp [norm_trqLogC, trqLogX₀]
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, hR⟩ := exists_isTPqpGCTRqSCRun isClosed_trqLogX hq hc hf P
    hθ0 hθ1 hβ0 hβθ hβϑ hϑ1 hε hβ₁0 hβ₁1 trqLogX₀_mem (by rw [hc0]; linarith)
    (by rw [hc0]; linarith)
  obtain ⟨hk₁, hx₁⟩ := trqLog_phase1 hR.run hθ0
  have hc1 : ‖trqLogC (xP k₁)‖ ≤ θ * ε₀ := by
    rw [hx₁, hc0]; positivity
  obtain ⟨kε, hend, hbound⟩ := hκ ε₀ hε₀ (by linarith) hε₀F xP δP k₁ D nF₁ nD₁ hR hc1
  rw [hk₁] at hbound
  simp only [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0),
    Finset.sum_empty, zero_add] at hbound
  have hc1' : ‖trqLogC (xP k₁)‖ ≤ θ * trqLogTol ε₀ 0 := by simpa [trqLogTol] using hc1
  have h2 := hR.run.phase2 hc1'
  rw [hx₁] at h2
  have hlow := trqLog_funEvals_ge hq h2 (hR.phase2 hc1') (by simp [trqLogTol])
    (by simp only [trqLogTol, ↓reduceIte]; linarith) hϑ0.le hϑ1 hLcond hend
  simp only [trqLogTol, ↓reduceIte] at hlow
  -- the lower bound `⌊1/(4ε₀)⌋ (L + 1) ≥ (L + 1)/(8 ε₀)`
  have hN : 1 / (8 * ε₀) ≤ (⌊1 / (4 * ε₀)⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one (1 / (4 * ε₀))
    have h2 : 1 / (8 * ε₀) + 1 ≤ 1 / (4 * ε₀) := by
      rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hfin : (L + 1 : ℝ) / (8 * ε₀) ≤ D.funEvals kε := by
    calc (L + 1 : ℝ) / (8 * ε₀) = 1 / (8 * ε₀) * (L + 1) := by ring
      _ ≤ (⌊1 / (4 * ε₀)⌋₊ : ℝ) * (L + 1) := by gcongr
      _ ≤ _ := hlow
  have hcontra : κF / ε₀ < (L + 1 : ℝ) / (8 * ε₀) := by
    rw [div_lt_div_iff₀ hε₀ (by positivity)]
    nlinarith [le_abs_self κF, abs_nonneg κF]
  linarith

/-- **Theorem 14.3.9 with a trust-region INNER fails in the printed order without the
logarithmic factor (`q = 1`).** On the example `n = 2`, `m = 1`, `X = [0, 2] × [-1, 1]`,
`f(x) = x_1`, `c(x) = x_2`, `x₀ = (2, 0)` (which satisfies X.CNe, c.D1qLB.X, f.D1qLB.X and f.B.Fb,
`trqLog_assumptions`), for all TRq parameters `P`, `0 < β ≤ θ < 1`, `β ≤ ϑ ≤ 1`, `β₁ ∈ (0, 1)` and
`β_F > 0`, there is no constant `κ_F` such that every TPqp-GC run with TRq-SC calls
(`IsTPqpGCTRqSCRun`; such runs exist, `exists_isTPqpGCTRqSCRun`) entering Phase 2 terminates
within `κ_F max[ε₀^{-1}, ε₀^{-1} ε_1^{-2}]` evaluations of `(f, c)` for all `ε ∈ (0, 1]²` with
`ε₀ ≤ β_F`. With `ε_1 = 1/2`: every call of the first `⌊1/(4ε₀)⌋` outer iterations restarts from
`Δ₀` and needs more than `L` unsuccessful iterations whenever `4ε₀/(ςβ) ≤ γ₁^L min(Δ₀, ϑ)`
(`trqLog_call_long`), so Phase 2 uses `≳ ε₀^{-1} log(1/ε₀)` evaluations (`trqLog_funEvals_ge`,
`theorem_14_3_9_trq_log_necessary_inv`). The bound of `theorem_14_3_9_trq_one`, with the factor
`1 + |log(ε₀ ε_1)|`, holds on this example. -/
theorem theorem_14_3_9_trq_log_necessary (P : Optimization.TRqParams) {ϑ θ β β₁ βF : ℝ}
    (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ) (hβϑ : β ≤ ϑ)
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) (hβF : 0 < βF) :
    ¬ ∃ κF : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range 2, 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun trqLogF trqLogC trqLogX 1 P ϑ θ β₁ β ε trqLogX₀ xP δP k₁ D nF₁ nD₁ →
        ‖trqLogC (xP k₁)‖ ≤ θ * ε 0 →
        ∃ kε, D.IsEnd trqLogF trqLogC trqLogX 1 θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            κF * tpqpOrderF (fun j => (j : ℝ) + 1) 1 ε := by
  rintro ⟨κF, hκ⟩
  refine theorem_14_3_9_trq_log_necessary_inv le_rfl P hϑ1 hθ0 hθ1 hβ0 hβθ hβϑ hβ₁0 hβ₁1 hβF
    ⟨|κF| * 4, fun ε₀ hε₀ hε₀1 hε₀F xP δP k₁ D nF₁ nD₁ hR hc1 => ?_⟩
  have hε : ∀ j ∈ Finset.range 2, 0 < trqLogTol ε₀ j ∧ trqLogTol ε₀ j ≤ 1 := by
    intro j _
    by_cases hj : j = 0
    · simp only [trqLogTol, hj, ↓reduceIte]; exact ⟨hε₀, hε₀1⟩
    · simp only [trqLogTol, hj, ↓reduceIte]; norm_num
  have e0 : trqLogTol ε₀ 0 = ε₀ := by simp [trqLogTol]
  obtain ⟨kε, hend, hbound⟩ := hκ (trqLogTol ε₀) hε (by rw [e0]; exact hε₀F) xP δP k₁ D nF₁ nD₁
    hR (by rw [e0]; exact hc1)
  refine ⟨kε, hend, hbound.trans ?_⟩
  have hO := tpqpOrderF_trqLogTol_le hε₀
  have hO0 : 0 ≤ tpqpOrderF (fun j => (j : ℝ) + 1) 1 (trqLogTol ε₀) := by
    have h1 := inv_le_tpqpOrderF (π := fun j : ℕ => (j : ℝ) + 1) (q := 1) (ε := trqLogTol ε₀)
    rw [e0] at h1
    exact (inv_nonneg.2 hε₀.le).trans h1
  calc κF * tpqpOrderF (fun j => (j : ℝ) + 1) 1 (trqLogTol ε₀)
      ≤ |κF| * (4 / ε₀) :=
        (mul_le_mul_of_nonneg_right (le_abs_self κF) hO0).trans
          (mul_le_mul_of_nonneg_left hO (abs_nonneg _))
    _ = |κF| * 4 / ε₀ := by ring

/-- **Why the example does not refute the printed order for `q ≥ 2`**: with `ε_j = 1/2`
(`j ≥ 1`) the printed order `max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}]` of Theorem 14.3.9 with the
TRq-SC exponents `π_j = j + 1` is at least `ε₀^{-2}` (its term `j = 2`), which exceeds the lower
bound of order `ε₀^{-1} log(1/ε₀)` that the example gives. -/
theorem inv_sq_le_tpqpOrderF_trqLogTol {q : ℕ} (hq : 2 ≤ q) {ε₀ : ℝ} (h0 : 0 < ε₀) :
    (ε₀ ^ 2)⁻¹ ≤ tpqpOrderF (fun j => (j : ℝ) + 1) q (trqLogTol ε₀) := by
  refine le_trans ?_ (term_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (ε := trqLogTol ε₀)
    (Finset.mem_Icc.2 ⟨by norm_num, hq⟩ : (2 : ℕ) ∈ Finset.Icc 1 q))
  simp only [trqLogTol, ↓reduceIte, OfNat.ofNat_ne_zero]
  norm_num
  have : 0 < (ε₀ ^ 2)⁻¹ := by positivity
  linarith

/-! ### The TRq-SC row `j + 1` of (14.2.12) fails per iteration with uniform constants (`q = 2`) -/

section Decrease

/-- `t ↦ t²/2`. -/
noncomputable def trqSadSq : ℝ → ℝ := fun t => t ^ 2 / 2

/-- `(t²/2)' = t`. -/
theorem iteratedDeriv_trqSadSq_one (t : ℝ) : iteratedDeriv 1 trqSadSq t = t := by
  rw [iteratedDeriv_one]
  unfold trqSadSq
  have := ((hasDerivAt_pow 2 t).div_const 2)
  rw [this.deriv]; ring

/-- `(t²/2)' = t`. -/
theorem deriv_trqSadSq : deriv trqSadSq = fun t => t := by
  funext t
  unfold trqSadSq
  have := ((hasDerivAt_pow 2 t).div_const 2)
  rw [this.deriv]; ring

/-- `(t²/2)'' = 1`. -/
theorem iteratedDeriv_trqSadSq_two (t : ℝ) : iteratedDeriv 2 trqSadSq t = 1 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_trqSadSq, deriv_id'']

/-- `(t²/2)''' = 0`. -/
theorem iteratedDeriv_trqSadSq_three (t : ℝ) : iteratedDeriv 3 trqSadSq t = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, deriv_trqSadSq, deriv_id'']
  simp

/-- `t ↦ t²/2` is smooth. -/
theorem contDiff_trqSadSq : ContDiff ℝ ∞ trqSadSq := by
  unfold trqSadSq; fun_prop

/-- `‖∇ⁿ (w ↦ w_i²/2)(v)‖ ≤ |(t²/2)^{(n)}(v_i)|`. -/
theorem norm_iteratedFDeriv_trqSadSq_comp (i : Fin 2) (n : ℕ) (v : ℝ²) :
    ‖iteratedFDeriv ℝ n (fun w : ℝ² => trqSadSq (w i)) v‖ ≤ |iteratedDeriv n trqSadSq (v i)| :=
  ContDiffAt.norm_iteratedFDeriv_comp_coord_le i
    (contDiff_trqSadSq.contDiffAt.of_le (by exact_mod_cast le_top))


/-- `w ↦ w_i²/2` is smooth. -/
theorem trqSad_contDiff_coordSq (i : Fin 2) : ContDiff ℝ ∞ (fun w : ℝ² => trqSadSq (w i)) :=
  contDiff_trqSadSq.comp (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).contDiff

/-- The objective `f_a(x) = x_1²/2 - a x_2²/2` of the example
(`x_1 = v 0`, `x_2 = v 1`). -/
noncomputable def trqSadF (a : ℝ) : ℝ² → ℝ := fun v => trqSadSq (v 0) - a * trqSadSq (v 1)

/-- `f_a` as a difference of coordinate squares. -/
theorem trqSadF_eq (a : ℝ) :
    trqSadF a = (fun w : ℝ² => trqSadSq (w 0)) - a • (fun w : ℝ² => trqSadSq (w 1)) := by
  funext v; simp [trqSadF]

/-- `f_a` is smooth. -/
theorem contDiff_trqSadF (a : ℝ) : ContDiff ℝ ∞ (trqSadF a) := by
  rw [trqSadF_eq]; exact (trqSad_contDiff_coordSq 0).sub ((trqSad_contDiff_coordSq 1).const_smul a)

/-- `f_a` is `C^n` everywhere. -/
theorem contDiffAt_trqSadF (a : ℝ) (n : ℕ) (y : ℝ²) : ContDiffAt ℝ n (trqSadF a) y :=
  ((contDiff_trqSadF a).of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)).contDiffAt

/-- `‖∇ⁿ f_a(v)‖ ≤ |(t²/2)^{(n)}(v_1)| + a |(t²/2)^{(n)}(v_2)|` for `a ≥ 0`. -/
theorem norm_iteratedFDeriv_trqSadF_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (v : ℝ²) :
    ‖iteratedFDeriv ℝ n (trqSadF a) v‖ ≤
      |iteratedDeriv n trqSadSq (v 0)| + a * |iteratedDeriv n trqSadSq (v 1)| := by
  have h0 := ((trqSad_contDiff_coordSq 0).of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤
      ∞)).contDiffAt
    (x := v)
  have h1 := ((trqSad_contDiff_coordSq 1).of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤
      ∞)).contDiffAt
    (x := v)
  have h1' : ContDiffAt ℝ n (a • fun w : ℝ² => trqSadSq (w 1)) v := h1.const_smul a
  rw [trqSadF_eq, iteratedFDeriv_sub_apply h0 h1', iteratedFDeriv_const_smul_apply h1]
  refine (norm_sub_le _ _).trans (add_le_add (norm_iteratedFDeriv_trqSadSq_comp 0 n v) ?_)
  rw [norm_smul, Real.norm_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_trqSadSq_comp 1 n v) ha

/-- `∇² f_a` is constant (`0`-Lipschitz) for `a ≥ 0`. -/
theorem iteratedFDerivLipschitzOn_trqSadF_two {a : ℝ} (ha : 0 ≤ a) (C : Set ℝ²)
    (hC : Convex ℝ C) : IteratedFDerivLipschitzOn (trqSadF a) 2 0 C :=
  iteratedFDerivLipschitzOn_of_norm_le hC
    (fun y _ => contDiffAt_trqSadF a _ y)
    fun x _ => (norm_iteratedFDeriv_trqSadF_le ha 3 x).trans (by
      rw [iteratedDeriv_trqSadSq_three, iteratedDeriv_trqSadSq_three]; simp)

/-- `f_a` is quadratic: `ΔT_2(x, s) = f_a(x) - f_a(x + s)`. -/
theorem taylorDecrement_two_trqSadF {a : ℝ} (ha : 0 ≤ a) (x s : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) x).taylorDecrement 2 s = trqSadF a x - trqSadF a (x + s) := by
  rw [ftaylorSeries_taylorDecrement_eq]
  have := norm_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun y _ => contDiffAt_trqSadF a _ y)
    (iteratedFDerivLipschitzOn_trqSadF_two ha univ convex_univ) (mem_univ x) (mem_univ (x + s))
  simp only [zero_div, zero_mul] at this
  have h := norm_le_zero_iff.1 this
  rw [sub_eq_zero] at h
  rw [h]

/-- The derivative of `f_a`: `s ↦ x_1 s_1 - a x_2 s_2`. -/
theorem hasFDerivAt_trqSadF (a : ℝ) (v : ℝ²) :
    HasFDerivAt (trqSadF a)
      ((v 0) • (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ) - (a * v 1) • EuclideanSpace.proj 1) v := by
  have h1 : HasFDerivAt (fun w : ℝ² => w 1) (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have h0 : HasFDerivAt (fun w : ℝ² => w 0) (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have := ((h0.pow 2).mul_const (1 / 2 : ℝ)).sub (((h1.pow 2).mul_const (1 / 2 : ℝ)).const_mul a)
  convert this using 1
  · funext w; simp only [trqSadF, trqSadSq, Pi.sub_apply]; ring
  · ext s; simp; ring

/-- `ΔT_1(x, s) = -(x_1 s_1 - a x_2 s_2)`. -/
theorem taylorDecrement_one_trqSadF (a : ℝ) (x s : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) x).taylorDecrement 1 s = -(x 0 * s 0 - a * x 1 * s 1) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]
  change -(iteratedFDeriv ℝ 1 _ x (fun _ => s)) = _
  rw [iteratedFDeriv_one_apply, (hasFDerivAt_trqSadF a x).fderiv]
  simp


/-- The box `[-1, 1]²`. -/
def trqSadX : Set ℝ² := {v | -1 ≤ v 0 ∧ v 0 ≤ 1 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1}

/-- Membership in the box. -/
theorem trqSadX_mem {v : ℝ²} : v ∈ trqSadX ↔ -1 ≤ v 0 ∧ v 0 ≤ 1 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1 := Iff.rfl

/-- The box is closed. -/
theorem isClosed_trqSadX : IsClosed trqSadX := by
  have hc : ∀ a : ℝ, Continuous fun _ : ℝ² => a := fun a => continuous_const
  have h := ((isClosed_le (hc (-1)) (trqLog_continuous_coord 0)).inter
    (isClosed_le (trqLog_continuous_coord 0) (hc 1))).inter
    ((isClosed_le (hc (-1)) (trqLog_continuous_coord 1)).inter
    (isClosed_le (trqLog_continuous_coord 1) (hc 1)))
  convert h using 1
  ext v
  simp only [trqSadX, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- The box lies in the ball of radius `2`. -/
theorem trqSadX_subset_ball : trqSadX ⊆ ball (0 : ℝ²) 2 := by
  intro v hv
  obtain ⟨h0, h2, h3, h4⟩ := hv
  rw [mem_ball_zero_iff]
  have hs := trqLog_norm_sq v
  have : ‖v‖ ^ 2 < 2 ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this

/-- f.D1qLaB.X (`q = 2`) for `f_a` with `a ∈ [0, 1]`, on `X₀` the ball of radius `2`, with the
constants `L_j = B_j = 4` independent of `a` and of the anchor. -/
theorem trqSadF_assumption {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x₀ : ℝ²) :
    AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) x₀ 1 2 (fun _ => 4) (fun _ => 4) := by
  have hd : ∀ n, ∀ v, ‖iteratedFDeriv ℝ n (trqSadF a) v‖ ≤
      |iteratedDeriv n trqSadSq (v 0)| + a * |iteratedDeriv n trqSadSq (v 1)| :=
    fun n v => norm_iteratedFDeriv_trqSadF_le ha0 n v
  refine AssumptionD1qLaBX.of_lipschitzOn isOpen_ball (convex_ball 0 2) trqSadX_subset_ball
    (fun y _ => (contDiffAt_trqSadF a 2 y).contDiffWithinAt)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun j hj => ?_) (fun j hj x hx => ?_)
  · have hj' : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
    refine iteratedFDerivLipschitzOn_of_norm_le (convex_ball 0 2)
      (fun y _ => contDiffAt_trqSadF a _ y) fun x _ => (hd _ x).trans ?_
    rcases hj' with rfl | rfl
    · rw [iteratedDeriv_trqSadSq_two, iteratedDeriv_trqSadSq_two]; norm_num; linarith
    · rw [iteratedDeriv_trqSadSq_three, iteratedDeriv_trqSadSq_three]; norm_num
  · have hj' : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
    refine (hd _ x).trans ?_
    rcases hj' with rfl | rfl
    · rw [iteratedDeriv_trqSadSq_one, iteratedDeriv_trqSadSq_one]
      have hx' : ‖x‖ < 2 := mem_ball_zero_iff.1 hx
      have h0 := (EuclideanSpace.abs_apply_le_norm x 0).trans hx'.le
      have h1 := (EuclideanSpace.abs_apply_le_norm x 1).trans hx'.le
      nlinarith [abs_nonneg (x 1)]
    · rw [iteratedDeriv_trqSadSq_two, iteratedDeriv_trqSadSq_two]; norm_num; linarith


/-- The trust-region parameters of the example: `Δ₀ = Δ_max = 1`, `η₁ = 1/4`, `η₂ = 3/4`,
`γ₁ = 1/4`, `γ₂ = 1/2`, `γ₃ = 2`, `ς = 1/2`. -/
noncomputable def trqSadP : Optimization.TRqParams where
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
  ς := 1 / 2
  Δ₀_le_Δmax := le_rfl
  ς_pos := by norm_num
  ς_le_one := by norm_num

/-- The unit vector `e_i` of `ℝ²`. -/
noncomputable def trqSadE (i : Fin 2) : ℝ² := EuclideanSpace.single i 1

@[simp] theorem trqSadE_apply (i j : Fin 2) : trqSadE i j = if j = i then 1 else 0 := by
  simp [trqSadE, PiLp.single_apply]

/-- `‖c e_i‖ = |c|`. -/
theorem norm_smul_trqSadE (c : ℝ) (i : Fin 2) : ‖c • trqSadE i‖ = |c| := by
  rw [norm_smul]; simp [trqSadE]

/-- Unfolding `f_a`. -/
theorem trqSadF_apply (a : ℝ) (v : ℝ²) : trqSadF a v = (v 0) ^ 2 / 2 - a * ((v 1) ^ 2 / 2) := rfl

/-- At `p = b e_0`, `ΔT_1(d) = -b d_0`. -/
theorem trqSad_ΔT1_p (a b : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 d = -(b * d 0) := by
  rw [taylorDecrement_one_trqSadF]; simp

/-- At `0`, `ΔT_1 = 0`. -/
theorem trqSad_ΔT1_zero (a : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 1 d = 0 := by
  rw [taylorDecrement_one_trqSadF]; simp

/-- At `0`, `ΔT_2(d) = -d_0²/2 + a d_1²/2`. -/
theorem trqSad_ΔT2_zero {a : ℝ} (ha : 0 ≤ a) (d : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2 d = -((d 0) ^ 2 / 2) + a * ((d 1) ^ 2 / 2)
        := by
  rw [taylorDecrement_two_trqSadF ha, zero_add, trqSadF_apply, trqSadF_apply]; simp; ring


section Prefix

variable {a b Δ : ℝ} {ε : ℕ → ℝ}

/-- `b e_1 ∈ X` for `b ∈ [0, 1]` (`e_1 = trqSadE 0`, the first unit vector). -/
theorem trqSad_smul_e0_mem {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : b • trqSadE 0 ∈ trqSadX := by
  simp only [trqSadX_mem, PiLp.smul_apply, trqSadE_apply]
  norm_num
  exact ⟨by linarith, hb1⟩

/-- `b e_1 - Δ e_1 ∈ X` for `b, Δ ∈ [0, 1]`. -/
theorem trqSadE0_mem {b Δ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) :
    (-Δ) • trqSadE 0 ∈ {e | b • trqSadE 0 + e ∈ trqSadX} := by
  simp only [Set.mem_ofPred_eq, trqSadX_mem, PiLp.add_apply, PiLp.smul_apply, trqSadE_apply]
  norm_num
  refine ⟨by linarith, by linarith⟩

/-- The first-order Step 1 at `p = b e_0` with radius `Δ ≤ 1`: the displacement `-Δ e_0`
achieves the first-order measure `b Δ`. -/
theorem trqSad_witness_p (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) :
    Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE
        0)).taylorDecrement 1)
      (min Δ 1) {e | b • trqSadE 0 + e ∈ trqSadX} trqSadP.ς ((-Δ) • trqSadE 0) := by
  rw [min_eq_left hΔ1]
  refine ⟨⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_trqSadE, abs_neg, abs_of_nonneg hΔ0]),
    trqSadE0_mem hb0 hb1 hΔ0 hΔ1⟩, ?_⟩
  have hm : Optimization.decrementMeasure
      ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1) Δ
      {e | b • trqSadE 0 + e ∈ trqSadX} ≤ b * Δ := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hΔ0, by
      change b • trqSadE 0 + 0 ∈ trqSadX
      rw [add_zero]; exact trqSad_smul_e0_mem hb0 hb1⟩ fun d hd => ?_
    rw [trqSad_ΔT1_p]
    have h1 := EuclideanSpace.abs_apply_le_norm d 0
    have h2 := mem_closedBall_zero_iff.1 hd.1
    have h3 := mul_le_mul_of_nonneg_left (neg_le_abs (d 0)) hb0
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) hb0
    linarith
  rw [trqSad_ΔT1_p]
  simp only [PiLp.smul_apply, trqSadE_apply, ↓reduceIte, smul_eq_mul, mul_one]
  have hς : trqSadP.ς = 1 / 2 := rfl
  rw [hς]
  linarith [mul_nonneg hb0 hΔ0]



/-- The first-order step at `p = b e_0` with radius `Δ ≤ 1` (`ε_1 = b`): order `1` fails, the
step is the Step-1 displacement `-Δ e_0`. -/
theorem trqSad_step_p (hb : 0 < b) (hb1 : b ≤ 1) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) (hε1 : ε 1 = b)
    (W : ℕ → ℝ²) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)) {e | b • trqSadE 0 + e ∈
        trqSadX}
      trqSadP.ς 2 ε (min Δ 1) Δ (fun j => if j = 1 then (-Δ) • trqSadE 0 else W j) 1
      ((-Δ) • trqSadE 0) where
  order_mem := by simp
  lt_taylorDecrement := by
    simp only [↓reduceIte, trqSad_ΔT1_p, PiLp.smul_apply, trqSadE_apply, smul_eq_mul, mul_one,
      min_eq_left hΔ1, pow_one, Nat.factorial_one, Nat.cast_one, div_one, hε1]
    have hς : trqSadP.ς = 1 / 2 := rfl
    rw [hς]; nlinarith [mul_pos hb hΔ0]
  taylorDecrement_le_of_lt := fun i hi hlt => absurd hlt (by have := (Finset.mem_Icc.1 hi).1; omega)
  mem := ⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_trqSadE, abs_neg, abs_of_pos hΔ0]),
    trqSadE0_mem hb.le hb1 hΔ0.le hΔ1⟩
  taylorDecrement_le := le_of_eq (by simp)

/-- The first-order test fails at `p` (from the step). -/
theorem trqSad_not_test_p (hb : 0 < b) (hb1 : b ≤ 1) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) (hε1 : ε 1 = b)
    (W : ℕ → ℝ²) :
    ¬ Optimization.MeasureTestPasses
      (fun j => (ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement j) 2 trqSadP.ς ε
      (fun _ => min Δ 1) (fun j => if j = 1 then (-Δ) • trqSadE 0 else W j) := fun h =>
  absurd (h 1 (by simp)) (not_le.2 (trqSad_step_p (a := a) hb hb1 hΔ0 hΔ1 hε1 W).lt_taylorDecrement)

/-- `f_a(b e_1) = b²/2`. -/
theorem trqSadF_p (a b : ℝ) : trqSadF a (b • trqSadE 0) = b ^ 2 / 2 := by
  rw [trqSadF_apply]; simp

/-- `f_a(b e_1 - Δ e_1) = (b - Δ)²/2`. -/
theorem trqSadF_p_step (a b Δ : ℝ) : trqSadF a (b • trqSadE 0 + (-Δ) • trqSadE 0) = (b - Δ) ^ 2 /
    2 := by
  rw [trqSadF_apply]; simp; ring

/-- An unsuccessful first-order iteration at `p` with radius `Δ ≥ 4b`: the ratio is
`1 - Δ/(2b) ≤ -1`, the iterate stays and the radius is divided by `4`. -/
theorem trqSad_accept_p_unsucc (hb : 0 < b) (h4 : 4 * b ≤ Δ) :
    Optimization.TRAcceptance trqSadP.toTRParams
      (Optimization.reductionRatio (trqSadF a) (b • trqSadE 0) ((-Δ) • trqSadE 0)
        ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 ((-Δ) • trqSadE 0)))
      (b • trqSadE 0) ((-Δ) • trqSadE 0) (b • trqSadE 0) Δ (Δ / 4) := by
  have hΔ : 0 < Δ := by linarith
  have hρ : Optimization.reductionRatio (trqSadF a) (b • trqSadE 0) ((-Δ) • trqSadE 0)
      ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 ((-Δ) • trqSadE 0)) < 1 /
          4 := by
    rw [Optimization.reductionRatio_def, trqSadF_p, trqSadF_p_step, trqSad_ΔT1_p]
    simp only [PiLp.smul_apply, trqSadE_apply, ↓reduceIte, smul_eq_mul, mul_one]
    rw [div_lt_iff₀ (by nlinarith)]
    nlinarith
  refine ⟨?_, ⟨fun h => absurd h (not_le.2 (hρ.trans (by norm_num : (1 : ℝ) / 4 < 3 / 4))),
    fun h => absurd h (not_le.2 hρ), fun _ => ⟨by change 1 / 4 * Δ ≤ Δ / 4; linarith,
      by change Δ / 4 ≤ 1 / 2 * Δ; linarith⟩⟩⟩
  exact (ite_eq_right (not_le.2 hρ)).symm

/-- The successful first-order iteration at `p` with radius `b`: the ratio is `1/2`, the step
lands at `0` and the radius stays `b`. -/
theorem trqSad_accept_p_succ (hb : 0 < b) :
    Optimization.TRAcceptance trqSadP.toTRParams
      (Optimization.reductionRatio (trqSadF a) (b • trqSadE 0) ((-b) • trqSadE 0)
        ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 ((-b) • trqSadE 0)))
      (b • trqSadE 0) ((-b) • trqSadE 0) 0 b b := by
  have hρ : Optimization.reductionRatio (trqSadF a) (b • trqSadE 0) ((-b) • trqSadE 0)
      ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 ((-b) • trqSadE 0)) = 1 /
          2 := by
    rw [Optimization.reductionRatio_def, trqSadF_p, trqSadF_p_step, trqSad_ΔT1_p]
    simp only [PiLp.smul_apply, trqSadE_apply, ↓reduceIte, smul_eq_mul, mul_one]
    field_simp; ring
  rw [hρ]
  refine ⟨?_, ⟨fun h => absurd h (by change ¬ (3 / 4 : ℝ) ≤ 1 / 2; norm_num),
    fun _ _ => ⟨by change 1 / 2 * b ≤ b; linarith, le_rfl⟩,
    fun h => absurd h (by change ¬ (1 / 2 : ℝ) < 1 / 4; norm_num)⟩⟩
  rw [ite_eq_left (show trqSadP.η₁ ≤ (1 / 2 : ℝ) by change (1 / 4 : ℝ) ≤ 1 / 2; norm_num),
    ← add_smul, add_neg_cancel, zero_smul]

/-- The second-order Step 1 at `0` with radius `b ≤ 1`: `b e_2` achieves the measure
`a b²/2`. -/
theorem trqSad_witness_zero (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2)
      (min b 1) {e | (0 : ℝ²) + e ∈ trqSadX} trqSadP.ς (b • trqSadE 1) := by
  rw [min_eq_left hb1]
  have hmem : b • trqSadE 1 ∈ {e | (0 : ℝ²) + e ∈ trqSadX} := by
    simp only [Set.mem_ofPred_eq, zero_add, trqSadX_mem, PiLp.smul_apply, trqSadE_apply]
    norm_num; exact ⟨by linarith, hb1⟩
  refine ⟨⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_trqSadE, abs_of_nonneg hb0]), hmem⟩, ?_⟩
  have hm : Optimization.decrementMeasure ((ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2) b
      {e | (0 : ℝ²) + e ∈ trqSadX} ≤ a * (b ^ 2 / 2) := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hb0, by
      change (0 : ℝ²) + 0 ∈ trqSadX
      simp only [add_zero, trqSadX_mem, PiLp.zero_apply]; norm_num⟩ fun d hd => ?_
    rw [trqSad_ΔT2_zero ha]
    have h1 := EuclideanSpace.abs_apply_le_norm d 1
    have h2 := mem_closedBall_zero_iff.1 hd.1
    have h3 : (d 1) ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
    nlinarith [sq_nonneg (d 0)]
  have hval : (ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2 (b • trqSadE 1) = a * (b ^ 2 / 2)
      := by
    rw [trqSad_ΔT2_zero ha]; simp
  rw [hval]
  have hς : trqSadP.ς = 1 / 2 := rfl
  rw [hς]
  linarith [mul_nonneg ha (sq_nonneg b)]

/-- The second-order step at `0` with radius `b ≤ 1` (`ε_2 = a`): order `1` passes
(`∇f(0) = 0`), order `2` fails, the step is the Step-1 displacement `b e_2`. -/
theorem trqSad_step_zero (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1) (hε1 : 0 ≤ ε 1) (hε2 : ε 2 = a)
    (W : ℕ → ℝ²) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (trqSadF a) 0) {e | (0 : ℝ²) + e ∈ trqSadX}
      trqSadP.ς 2 ε (min b 1) b (fun j => if j = 2 then b • trqSadE 1 else W j) 2 (b • trqSadE 1)
          where
  order_mem := by simp
  lt_taylorDecrement := by
    simp only [↓reduceIte, trqSad_ΔT2_zero ha.le, PiLp.smul_apply, trqSadE_apply, smul_eq_mul,
      min_eq_left hb1, hε2]
    norm_num
    have hς : trqSadP.ς = 1 / 2 := rfl
    rw [hς]; nlinarith [mul_pos ha (pow_pos hb 2)]
  taylorDecrement_le_of_lt := fun i hi hlt => by
    have hi1 : i = 1 := by have := (Finset.mem_Icc.1 hi).1; omega
    subst hi1
    simp only [trqSad_ΔT1_zero, show ¬ ((1 : ℕ) = 2) by decide, ↓reduceIte]
    have := trqSadP.ς_pos
    have : 0 ≤ min b 1 := le_min hb.le zero_le_one
    positivity
  mem := ⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_trqSadE, abs_of_pos hb]), by
    simp only [Set.mem_ofPred_eq, zero_add, trqSadX_mem, PiLp.smul_apply, trqSadE_apply]
    norm_num; exact ⟨by linarith, hb1⟩⟩
  taylorDecrement_le := le_of_eq (by simp)

/-- The second-order test fails at `0`. -/
theorem trqSad_not_test_zero (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1) (hε1 : 0 ≤ ε 1)
    (hε2 : ε 2 = a) (W : ℕ → ℝ²) :
    ¬ Optimization.MeasureTestPasses (fun j => (ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement j)
      2 trqSadP.ς ε (fun _ => min b 1) (fun j => if j = 2 then b • trqSadE 1 else W j) := fun h =>
  absurd (h 2 (by simp)) (not_le.2 (trqSad_step_zero ha hb hb1 hε1 hε2 W).lt_taylorDecrement)

/-- `f_a(b e_2) = -a b²/2`. -/
theorem trqSadF_zero_step (a b : ℝ) : trqSadF a ((0 : ℝ²) + b • trqSadE 1) = -(a * (b ^ 2 / 2))
    := by
  rw [trqSadF_apply]; simp

/-- The very successful second-order iteration at `0` with radius `b`: the ratio is `1`, the
step lands at `b e_2` and the radius stays `b`. -/
theorem trqSad_ratio_zero (ha : 0 < a) (hb : 0 < b) :
    Optimization.reductionRatio (trqSadF a) 0 (b • trqSadE 1)
      ((ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2 (b • trqSadE 1)) = 1 := by
  have h : trqSadF a 0 - trqSadF a (0 + b • trqSadE 1) = a * (b ^ 2 / 2) := by
    rw [zero_add, trqSadF_apply, trqSadF_apply]; simp
  rw [Optimization.reductionRatio_def, taylorDecrement_two_trqSadF ha.le, h, div_self]
  positivity

/-- The very successful second-order iteration at `0` with radius `b`: the step lands at
`b e_2` and the radius stays `b`. -/
theorem trqSad_accept_zero (ha : 0 < a) (hb : 0 < b) :
    Optimization.TRAcceptance trqSadP.toTRParams
      (Optimization.reductionRatio (trqSadF a) 0 (b • trqSadE 1)
        ((ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2 (b • trqSadE 1)))
      0 (b • trqSadE 1) (b • trqSadE 1) b b := by
  rw [trqSad_ratio_zero ha hb]
  refine ⟨?_, ⟨fun _ => ⟨le_rfl, by change b ≤ 2 * b; linarith⟩,
    fun _ h => absurd h (by change ¬ (1 : ℝ) < 3 / 4; norm_num),
    fun h => absurd h (by change ¬ (1 : ℝ) < 1 / 4; norm_num)⟩⟩
  rw [ite_eq_left (show trqSadP.η₁ ≤ (1 : ℝ) by change (1 / 4 : ℝ) ≤ 1; norm_num), zero_add]

end Prefix


open Classical in
/-- **(14.2.11) with the printed TRq-SC exponents `π_j = j + 1` is false for `q = 2` with `κ_decr`
depending only on the algorithm parameters, `ϑ` and the f.D1qLaB.X constants**
([cartis2022evaluation], Lemma 14.2.2, (14.2.12); the dependence of the explicit `κ_decr` of Lemma
12.2.4 / (12.2.14)). The objective varies with `κ` within a family with uniform constants; a single
fixed `f` is not treated here. For the TRq parameters `trqSadP`,
the threshold `ϑ = 1`, the box `X = [-1, 1]²` and every `κ > 0` there are `a ∈ (0, 1]` (the
objective `f_a(x) = x_1²/2 - a x_2²/2`, which satisfies f.D1qLaB.X with constants `4` independent of
`a`), tolerances `ε ∈ (0, 1]²` and a TRq-SC run with a successful iteration `k` before termination
that decreases `f_a` by less than `κ min_j ε_j^{j+1}`. With `r = 2^{-N}`, `ε_1 = r²`, `ε_2 = a = r`:
`N` unsuccessful first-order iterations at `(r², 0)` shrink the radius from `1` to `r²`, a
successful step reaches `0`, where the gradient vanishes and the second-order test fails, and the
second-order step `r² e_2` decreases `f_a` by `r⁵/2`, against `κ min(ε_1², ε_2³) = κ r⁴`. The radius
is shared across the orders and is driven down by the first-order failures; the decrease proved in
Lemma 12.2.4 is `κ ε_min^{q+1}` (`Chapter14.lemma_14_2_2_trq`). -/
theorem lemma_14_2_2_trq_printed_false {κ : ℝ} (hκ : 0 < κ) :
    ∃ (a : ℝ) (ε : ℕ → ℝ) (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²) (k : ℕ),
      0 < a ∧ a ≤ 1 ∧ (∀ j ∈ Finset.Icc 1 2, ε j ∈ Ioc 0 1) ∧ x 0 ∈ trqSadX ∧
      AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) (x 0) 1 2 (fun _ => 4) (fun _ => 4) ∧
      Chapter12.algorithm_12_2_1_feasible (trqSadF a) trqSadX trqSadP 2 ε 1 x s Δ jk d ∧
      (∀ i ≤ k, ¬ Chapter12.trqStop (trqSadF a) trqSadP 2 ε 1 x Δ d i) ∧
      trqSadP.η₁ ≤ Chapter12.trqRho (trqSadF a) x s jk k ∧
      trqSadF a (x k) - trqSadF a (x (k + 1)) < κ * Chapter12.finMin 1 (fun j => ε j ^ (j + 1)) 2
          := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos two_pos hκ) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 / 2) ^ N := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ by positivity
  have hr1 : r ≤ 1 := hr ▸ pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = r ^ 2 := ⟨_, rfl⟩
  have hb : 0 < b := hbdef ▸ by positivity
  have hb1 : b ≤ 1 := hbdef ▸ pow_le_one₀ hr0.le hr1
  have hpowN : ((1 : ℝ) / 4) ^ N = b := by
    rw [hbdef, hr, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hq0 : ∀ k : ℕ, 0 < ((1 : ℝ) / 4) ^ k := fun k => by positivity
  have hq1 : ∀ k : ℕ, ((1 : ℝ) / 4) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun j => if j = 1 then b else r := ⟨_, rfl⟩
  have hε1 : ε 1 = b := by simp [hεdef]
  have hε2 : ε 2 = r := by simp [hεdef]
  -- the Step-1 displacements of the orders not used
  have hW : ∀ (y : ℝ²) (δ : ℝ) (j : ℕ), ∃ w : ℝ², y ∈ trqSadX → 0 ≤ δ →
      Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ (trqSadF r) y).taylorDecrement j) δ
        {e | y + e ∈ trqSadX} trqSadP.ς w := by
    intro y δ j
    by_cases h : y ∈ trqSadX ∧ 0 ≤ δ
    · obtain ⟨w, hw⟩ := Optimization.exists_isApproxMeasureStep_taylorDecrement
        (ftaylorSeries ℝ (trqSadF r) y) j
        (isClosed_trqSadX.preimage (continuous_const.add continuous_id))
        (by change y + 0 ∈ trqSadX; rw [add_zero]; exact h.1) h.2 trqSadP.ς_le_one
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose W hW using hW
  -- the tail: any TRq-SC run from `b e_2` with initial radius `b`
  let P' : Optimization.TRqParams :=
    { trqSadP with Δ₀ := b, Δ₀_pos := hb, Δ₀_le_Δmax := hb1 }
  have hq₀ : b • trqSadE 1 ∈ trqSadX := by
    simp only [trqSadX_mem, PiLp.smul_apply, trqSadE_apply]; norm_num; exact ⟨by linarith, hb1⟩
  obtain ⟨y, sy, Δy, jy, dy, hy0, hyr⟩ :=
    exists_algorithm_12_2_1_feasible isClosed_trqSadX (trqSadF r) P' 2 ε zero_le_one hq₀
  -- the run
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ², ∀ k, x k =
      if k ≤ N then b • trqSadE 0 else if k = N + 1 then 0 else y (k - (N + 2)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → ℝ, ∀ k, Δ k =
      if k ≤ N then ((1 : ℝ) / 4) ^ k else if k = N + 1 then b else Δy (k - (N + 2)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ², ∀ k, s k =
      if k ≤ N then (-((1 : ℝ) / 4) ^ k) • trqSadE 0 else if k = N + 1 then b • trqSadE 1
        else sy (k - (N + 2)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨jk, hjk⟩ : ∃ jk : ℕ → ℕ, ∀ k, jk k =
      if k ≤ N then 1 else if k = N + 1 then 2 else jy (k - (N + 2)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℕ → ℝ², ∀ k, d k =
      if k ≤ N then (fun j => if j = 1 then (-((1 : ℝ) / 4) ^ k) • trqSadE 0
        else W (b • trqSadE 0) (min (((1 : ℝ) / 4) ^ k) 1) j)
      else if k = N + 1 then (fun j => if j = 2 then b • trqSadE 1 else W 0 (min b 1) j)
      else dy (k - (N + 2)) :=
    ⟨_, fun _ => rfl⟩
  have hxp : ∀ k ≤ N, x k = b • trqSadE 0 := fun k hk => by simp [hx, hk]
  have hΔp : ∀ k ≤ N, Δ k = ((1 : ℝ) / 4) ^ k := fun k hk => by simp [hΔ, hk]
  have hsp : ∀ k ≤ N, s k = (-((1 : ℝ) / 4) ^ k) • trqSadE 0 := fun k hk => by simp [hs, hk]
  have hjp : ∀ k ≤ N, jk k = 1 := fun k hk => by simp [hjk, hk]
  have hdp : ∀ k ≤ N, d k = (fun j => if j = 1 then (-((1 : ℝ) / 4) ^ k) • trqSadE 0
      else W (b • trqSadE 0) (min (((1 : ℝ) / 4) ^ k) 1) j) := fun k hk => by simp [hd, hk]
  have hxN : x (N + 1) = 0 := by simp [hx]
  have hΔN : Δ (N + 1) = b := by simp [hΔ]
  have hsN : s (N + 1) = b • trqSadE 1 := by simp [hs]
  have hjN : jk (N + 1) = 2 := by simp [hjk]
  have hdN : d (N + 1) = (fun j => if j = 2 then b • trqSadE 1 else W 0 (min b 1) j) := by
    simp [hd]
  have hne : ∀ m, ¬ (m + (N + 2) ≤ N) ∧ ¬ (m + (N + 2) = N + 1) ∧ m + (N + 2) - (N + 2) = m :=
    fun m => ⟨by omega, by omega, by omega⟩
  have hxt : ∀ m, x (m + (N + 2)) = y m := fun m => by
    rw [hx]; simp only [(hne m).1, (hne m).2.1, ↓reduceIte, (hne m).2.2]
  have hΔt : ∀ m, Δ (m + (N + 2)) = Δy m := fun m => by
    rw [hΔ]; simp only [(hne m).1, (hne m).2.1, ↓reduceIte, (hne m).2.2]
  have hst : ∀ m, s (m + (N + 2)) = sy m := fun m => by
    rw [hs]; simp only [(hne m).1, (hne m).2.1, ↓reduceIte, (hne m).2.2]
  have hjt : ∀ m, jk (m + (N + 2)) = jy m := fun m => by
    rw [hjk]; simp only [(hne m).1, (hne m).2.1, ↓reduceIte, (hne m).2.2]
  have hdt : ∀ m, d (m + (N + 2)) = dy m := fun m => by
    rw [hd]; simp only [(hne m).1, (hne m).2.1, ↓reduceIte, (hne m).2.2]
  have hΔy0 : Δy 0 = b := hyr.toIsTRRun.delta_zero
  -- the tests
  have hnsp : ∀ k ≤ N, ¬ Chapter12.trqStop (trqSadF r) trqSadP 2 ε 1 x Δ d k := fun k hk => by
    change ¬ Optimization.MeasureTestPasses
      (fun j => (ftaylorSeries ℝ (trqSadF r) (x k)).taylorDecrement j) 2 trqSadP.ς ε
      (fun _ => min (Δ k) 1) (d k)
    rw [hxp k hk, hΔp k hk, hdp k hk]
    exact trqSad_not_test_p hb hb1 (hq0 k) (hq1 k) hε1 _
  have hnsN : ¬ Chapter12.trqStop (trqSadF r) trqSadP 2 ε 1 x Δ d (N + 1) := by
    change ¬ Optimization.MeasureTestPasses
      (fun j => (ftaylorSeries ℝ (trqSadF r) (x (N + 1))).taylorDecrement j) 2 trqSadP.ς ε
      (fun _ => min (Δ (N + 1)) 1) (d (N + 1))
    rw [hxN, hΔN, hdN]
    exact trqSad_not_test_zero hr0 hb hb1 (hε1 ▸ hb.le) hε2 _
  have htest : ∀ m, Chapter12.trqStop (trqSadF r) trqSadP 2 ε 1 x Δ d (m + (N + 2)) ↔
      Chapter12.trqStop (trqSadF r) P' 2 ε 1 y Δy dy m := fun m => by
    change Optimization.MeasureTestPasses
      (fun j => (ftaylorSeries ℝ (trqSadF r) (x (m + (N + 2)))).taylorDecrement j) 2 trqSadP.ς ε
      (fun _ => min (Δ (m + (N + 2))) 1) (d (m + (N + 2))) ↔ _
    rw [hxt, hΔt, hdt]
    rfl
  have hcases : ∀ k : ℕ, k ≤ N ∨ k = N + 1 ∨ ∃ m, k = m + (N + 2) := fun k => by
    rcases le_or_gt k N with h | h
    · exact Or.inl h
    · rcases Nat.lt_or_ge k (N + 2) with h' | h'
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr ⟨k - (N + 2), by omega⟩)
  have htail : ∀ m, (∀ i ≤ m + (N + 2), ¬ Chapter12.trqStop (trqSadF r) trqSadP 2 ε 1 x Δ d i) →
      ∀ i ≤ m, ¬ Chapter12.trqStop (trqSadF r) P' 2 ε 1 y Δy dy i := fun m hk i hi =>
    (htest i).not.1 (hk (i + (N + 2)) (by omega))
  have htail' : ∀ m, (∀ i < m + (N + 2), ¬ Chapter12.trqStop (trqSadF r) trqSadP 2 ε 1 x Δ d i) →
      ∀ i < m, ¬ Chapter12.trqStop (trqSadF r) P' 2 ε 1 y Δy dy i := fun m hk i hi =>
    (htest i).not.1 (hk (i + (N + 2)) (by omega))
  have hrun : Chapter12.algorithm_12_2_1_feasible (trqSadF r) trqSadX trqSadP 2 ε 1 x s Δ jk d := by
    refine ⟨⟨?_, fun k hk => ?_, fun k hk => ?_⟩, fun k hk j hj => ?_, fun k hk => ?_⟩
    · rw [hΔp 0 (Nat.zero_le _), pow_zero]; rfl
    · -- Step 2
      change Optimization.IsTRqStep (ftaylorSeries ℝ (trqSadF r) (x k)) {e | x k + e ∈ trqSadX}
          trqSadP.ς 2 ε
        (min (Δ k) 1) (Δ k) (d k) (jk k) (s k)
      rcases hcases k with h | h | ⟨m, rfl⟩
      · rw [hxp k h, hΔp k h, hdp k h, hjp k h, hsp k h]
        exact trqSad_step_p hb hb1 (hq0 k) (hq1 k) hε1 _
      · subst h
        rw [hxN, hΔN, hdN, hjN, hsN]
        exact trqSad_step_zero hr0 hb hb1 (hε1 ▸ hb.le) hε2 _
      · have := hyr.step m (htail m hk)
        rw [hxt, hΔt, hdt, hjt, hst]
        exact this
    · -- Steps 3–4
      change Optimization.TRAcceptance trqSadP.toTRParams
        (Optimization.trqRatio (trqSadF r) (fun k => ftaylorSeries ℝ (trqSadF r) (x k)) x s jk k)
        (x k) (s k) (x (k + 1)) (Δ k) (Δ (k + 1))
      rw [Optimization.trqRatio_eq]
      rcases hcases k with h | h | ⟨m, rfl⟩
      · rcases Nat.lt_or_ge k N with hkN | hkN
        · rw [hxp k h, hxp (k + 1) hkN, hsp k h, hΔp k h, hΔp (k + 1) hkN, hjp k h]
          have h4 : 4 * b ≤ ((1 : ℝ) / 4) ^ k := by
            rw [← hpowN]
            have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
              (show k + 1 ≤ N by omega)
            rw [pow_succ] at this
            linarith
          have e : ((1 : ℝ) / 4) ^ (k + 1) = ((1 : ℝ) / 4) ^ k / 4 := by rw [pow_succ]; ring
          rw [e]
          exact trqSad_accept_p_unsucc hb h4
        · have hkN' : k = N := le_antisymm h hkN
          subst hkN'
          rw [hxp k h, hxN, hsp k h, hΔp k h, hΔN, hjp k h, hpowN]
          exact trqSad_accept_p_succ hb
      · subst h
        have e : N + 1 + 1 = 0 + (N + 2) := by omega
        rw [hxN, e, hxt, hΔt, hy0, hΔy0, hsN, hΔN, hjN]
        exact trqSad_accept_zero hr0 hb
      · have := hyr.accept m (htail m hk)
        have e : m + (N + 2) + 1 = (m + 1) + (N + 2) := by omega
        rw [e, hxt, hxt, hΔt, hΔt, hst, hjt]
        exact this
    · -- Step 1: the displacements
      change Optimization.IsApproxMeasureStep
        ((ftaylorSeries ℝ (trqSadF r) (x k)).taylorDecrement j) (min (Δ k) 1)
        {e | x k + e ∈ trqSadX} trqSadP.ς (d k j)
      rcases hcases k with h | h | ⟨m, rfl⟩
      · rw [hxp k h, hΔp k h, hdp k h]
        by_cases hj1 : j = 1
        · subst hj1
          simp only [↓reduceIte]
          exact trqSad_witness_p hb.le hb1 (hq0 k).le (hq1 k)
        · simp only [hj1, ↓reduceIte]
          exact hW _ _ _ (trqSad_smul_e0_mem hb.le hb1) (le_min (hq0 k).le zero_le_one)
      · subst h
        rw [hxN, hΔN, hdN]
        by_cases hj2 : j = 2
        · subst hj2
          simp only [↓reduceIte]
          exact trqSad_witness_zero hr0.le hb.le hb1
        · simp only [hj2, ↓reduceIte]
          exact hW _ _ _ (by simp [trqSadX_mem]) (le_min hb.le zero_le_one)
      · have := hyr.witness m (htail' m hk) j hj
        rw [hxt, hΔt, hdt]
        exact this
    · -- the cap `Δ_{k+1} ≤ Δ_max`
      change Δ (k + 1) ≤ trqSadP.Δmax
      change Δ (k + 1) ≤ 1
      rcases hcases k with h | h | ⟨m, rfl⟩
      · rcases Nat.lt_or_ge k N with hkN | hkN
        · rw [hΔp (k + 1) hkN]; exact hq1 _
        · have hkN' : k = N := le_antisymm h hkN
          subst hkN'
          rw [hΔN]; exact hb1
      · subst h
        have e : N + 1 + 1 = 0 + (N + 2) := by omega
        rw [e, hΔt, hΔy0]; exact hb1
      · have := hyr.cap m (htail m hk)
        have e : m + (N + 2) + 1 = (m + 1) + (N + 2) := by omega
        rw [e, hΔt]
        exact this
  refine ⟨r, ε, x, s, Δ, jk, d, N + 1, hr0, hr1, fun j hj => ?_, ?_,
    trqSadF_assumption hr0.le hr1 (x 0), hrun, fun i hi => ?_, ?_, ?_⟩
  · have : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
    rcases this with rfl | rfl
    · rw [hε1]; exact ⟨hb, hb1⟩
    · rw [hε2]; exact ⟨hr0, hr1⟩
  · rw [hxp 0 (Nat.zero_le _)]; exact trqSad_smul_e0_mem hb.le hb1
  · rcases Nat.lt_or_ge i (N + 1) with h | h
    · exact hnsp i (by omega)
    · have : i = N + 1 := by omega
      subst this; exact hnsN
  · change trqSadP.η₁ ≤ Optimization.trqRatio (trqSadF r) (fun k => ftaylorSeries ℝ (trqSadF r) (x
      k)) x s jk
      (N + 1)
    rw [Optimization.trqRatio_eq, hxN, hsN, hjN, trqSad_ratio_zero hr0 hb]
    change (1 / 4 : ℝ) ≤ 1; norm_num
  · -- the decrease `r⁵/2` against `κ min_j ε_j^{j+1} ≥ κ r⁴`
    have e : N + 1 + 1 = 0 + (N + 2) := by omega
    rw [e, hxt, hy0, hxN]
    have hdec : trqSadF r 0 - trqSadF r (b • trqSadE 1) = r * (b ^ 2 / 2) := by
      rw [trqSadF_apply, trqSadF_apply]; simp
    rw [hdec]
    have hmin : b ^ 2 ≤ Chapter12.finMin 1 (fun j => ε j ^ (j + 1)) 2 := by
      refine Chapter12.le_finMin (pow_le_one₀ hb.le hb1) fun j hj => ?_
      have : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
      rcases this with rfl | rfl
      · rw [hε1]
      · rw [hε2, hbdef]
        have : r ^ 4 ≤ r ^ 3 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
        calc (r ^ 2) ^ 2 = r ^ 4 := by ring
          _ ≤ r ^ 3 := this
    have hrN : r < 2 * κ := hr ▸ hN
    have hb2 : 0 < b ^ 2 := by positivity
    calc r * (b ^ 2 / 2) < κ * b ^ 2 := by nlinarith
      _ ≤ κ * Chapter12.finMin 1 (fun j => ε j ^ (j + 1)) 2 :=
          mul_le_mul_of_nonneg_left hmin hκ.le

/-- **No uniform `κ_decr` for the TRq-SC row `j + 1`** ([cartis2022evaluation], (14.2.11)–(14.2.12),
`q = 2`): there is no `κ > 0` such that, for every `a ∈ (0, 1]`, every TRq-SC run (parameters
`trqSadP`, `ϑ = 1`, `X = [-1, 1]²`) on `f_a` satisfying f.D1qLaB.X with the constants `4`, every
`ε ∈ (0, 1]²` and every successful iteration `k` before termination,
`f_a(x_k) - f_a(x_{k+1}) ≥ κ min_j ε_j^{j+1}` (`lemma_14_2_2_trq_printed_false`). -/
theorem lemma_14_2_2_trq_printed_false_uniform :
    ¬ ∃ κ : ℝ, 0 < κ ∧ ∀ (a : ℝ) (ε : ℕ → ℝ) (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ)
      (d : ℕ → ℕ → ℝ²) (k : ℕ), 0 < a → a ≤ 1 → (∀ j ∈ Finset.Icc 1 2, ε j ∈ Ioc 0 1) →
      AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) (x 0) 1 2 (fun _ => 4) (fun _ => 4) →
      Chapter12.algorithm_12_2_1_feasible (trqSadF a) trqSadX trqSadP 2 ε 1 x s Δ jk d →
      (∀ i ≤ k, ¬ Chapter12.trqStop (trqSadF a) trqSadP 2 ε 1 x Δ d i) →
      trqSadP.η₁ ≤ Chapter12.trqRho (trqSadF a) x s jk k →
      κ * Chapter12.finMin 1 (fun j => ε j ^ (j + 1)) 2 ≤
        trqSadF a (x k) - trqSadF a (x (k + 1)) := by
  rintro ⟨κ, hκ, H⟩
  obtain ⟨a, ε, x, s, Δ, jk, d, k, ha0, ha1, hε, -, hA, hrun, hns, hsucc, hlt⟩ :=
    lemma_14_2_2_trq_printed_false hκ
  exact absurd (H a ε x s Δ jk d k ha0 ha1 hε hA hrun hns hsucc) (not_le.2 hlt)

end Decrease

end CartisGouldToint.Chapter14
