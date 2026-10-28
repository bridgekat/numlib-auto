import NumlibSurface.CartisGouldToint.Chapter14.Section03

/-!
# Cartis–Gould–Toint §14.3: Theorem 14.3.9 fails for a nonspecific INNER

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Theorem 14.3.9: the order of the
number of case-(b) outer iterations of TPqp-GC (Algorithm 14.3.2) whose INNER call ends at a point
passing INNER's own test (14.3.19).

For Phase-2 runs whose INNER calls satisfy the contract of Lemmas 14.2.2–14.2.3 keyed on INNER's
own test (`IsInnerPhaseRunStrong`), `IsTPqpGCPhase2.complexity_of_strong` bounds Phase 2 with an
extra term `(f_up - f_low + 1)/τ`, `τ ∼ min_j ε₀ ε_j ρ_j^{j-1}`, for those iterations; for
`q = 1` it is `O((ε₀ ε₁)^{-1})`. With the ARqp-SC exponent `π₁ = (p+1)/p` (`p ≥ 2`) this
exceeds the order `O(max(ε₀^{-1}, ε₀^{1-π₁} ε₁^{-π₁}))` claimed by Theorem 14.3.9 when
`ε₁ = ε₀^s` with `0 < s < p - 1`. This module shows that the extra term is attained and settles
the printed Theorem 14.3.9 for a nonspecific INNER, according to how its INNER hypotheses are read:

* **Per-call reading** (the hypotheses checked on the INNER calls of the run, as the library states
  its own theorems): the theorem is false for `π₁ ∈ [4/3, 3/2]` (the ARqp-SC exponent `(p+1)/p`
  for `p ∈ {2, 3}`): the INNER calls of the counterexample satisfy the output test (14.3.19), the
  cost bounds (14.3.20)–(14.3.21) with `ε`-independent constants and `f_low = 0`, and (14.2.11),
  (14.2.13) with `t`-independent constants, and the evaluation counts exceed the printed bounds for
  every choice of the theorem's constants (`theorem_14_3_9_false`).
* **Literal, uniform reading** ((14.3.20)–(14.3.21) bound every call of the algorithm for all
  admissible inputs with one `ε`-independent `κ_INNER`): on the same problem no INNER, ARqp-SC
  included, satisfies it for `π₁ < 2` (`theorem_14_3_9_cost_hypothesis_unsatisfiable`), so the
  printed theorem is vacuous there.

The corrected statement for INNER of regularization type is `IsTPqpGCPhase2.complexity_of_strong`
(the bound with an extra term `O(ε₀^{-1} + (ε₀ ε₁)^{-1})` for `q = 1`). For genuine regularization
INNERs (ARqp-SC run as ARqpC-SC with `c = 0`, `h = 0`), `Chapter14.Section03Genuine` proves
Theorem 14.3.9 in the printed order for every run with the exponents `j + 1`
(`theorem_14_3_9_arqpc`; the ARqpC-SC entry of (14.2.12) for `q ≥ 2` or `X` nonconvex) and with
the ARqp-SC exponents when `q = p` (`theorem_14_3_9_arqp`). In the case of this module,
`q = 1 < p` with `π₁ = (p+1)/p` (the ARqp-SC entry, and the ARqpC-SC entry for convex `X`), genuine
ARqp-SC runs also exceed the printed order when `p ≥ 4` (`Chapter14.Section03GenuineSharp`,
`theorem_14_3_9_arqp_counterexample`, with a tilted objective `f(x) = x₁ - x₂/16`), and for
every `p ≥ 2` (`Chapter14.Section03GenuineSharp2`, `theorem_14_3_9_arqp_counterexample_walk`).

## Main results

* `theorem_14_3_9_false`: Theorem 14.3.9 fails for a nonspecific INNER under the per-call reading
  of its INNER hypotheses. One problem
  satisfying the book's assumptions (as below, with `f_low = -2`, `f_up = 2`) such that for all
  `π₁ ∈ [4/3, 3/2]`, `β ∈ [2/3, θ]`, `β₁ ∈ (0, 1)` and every choice of the constants
  `κ^A_{INNER,2}`, `κ^C_{INNER,2}`, `κ^S_{INNER,2}`, `κ^{F,ν}_INNER`, `κ^{D,ν}_INNER`, there is a
  TPqp-GC run whose INNER calls satisfy (14.3.19) (`TPqpSeq.InnerTest`, output in `X`, radius
  `1`), (14.3.20)–(14.3.21) with `κ^F_INNER = κ^D_INNER = κ` for every `κ ≥ 8` and `f_low = 0`,
  and (14.2.11), (14.2.13) with `t`-independent constants (`IsInnerPhaseRunStrong`); Phase 1 makes
  no INNER call. Its numbers of evaluations of `(f, c)` and of their derivatives exceed the printed
  `#^F_INNER,1 + #^F_INNER,2` and `#^D_INNER,1 + #^D_INNER,2`.
* `theorem_14_3_9_cost_hypothesis_unsatisfiable`: on the same problem, for `π₁ < 2`, `β ∈ (0, 1)`
  and every `κ`, the first Phase-2 call for suitable admissible tolerances starts at a point
  failing INNER's test for every radius while its bound (14.3.20)–(14.3.21) is below `1`: the
  literal uniform reading of the cost hypothesis cannot be met by any INNER.
* `theorem_14_3_9_order_counterexample`: one problem (`n = 2`, `m = 1`, `q = 1`, `X = [-1, 1]²`,
  `f(x) = x₁ - x₂`, `c(x) = x₁²/2`, satisfying X.CNe (`AssumptionXCNe`), f.D1pLB.X and
  c.D1pLB.X for every `p`, f.B.Fb; `X` also convex) such that for every `C` there are
  tolerances `ε₀ ∼ 1/(2m²)`, `ε₁ = 3/(2m)` and a TPqp-GC run (`θ = 3/4`, `β ∈ [2/3, θ]`,
  unit radii) whose INNER calls
  satisfy `IsInnerPhaseRunStrong` for every `κ_decr` and all exponents `π`, with `μ(·, t_k)`
  decreasing strictly along each call, terminating after `k_ε = m³` outer iterations, all but the
  last of them case-(b) iterations ending at a point passing INNER's test, with
  `k_ε > C max(ε₀^{-1}, ε₀^{1-π} ε₁^{-π})` for every `π ≤ 3/2`.
* `Theorem1439OrderCex.not_innerTest_start`: INNER's test fails at the start of every call, so
  a genuine INNER must move;
* `Theorem1439OrderCex.two_le_innerEvalBound`: the cost bound (14.3.20)–(14.3.21) of every call is
  at least `2` for `κ ≥ 8` and `π₁ ≥ 4/3` (a call costs one evaluation, two counting the one at
  its starting point);
* `arqpPiOf_one_le`, `four_thirds_le_arqpPiOf_one`: the ARqp-SC exponent of order `1` is at most
  `3/2` for `p ≥ 2` and at least `4/3` for `p ≤ 3`.

The helpers (the data, the run and its properties) are in the namespace `Theorem1439OrderCex`.

## Mechanism

The constraint `c(x) = x₁²/2` is degenerate along the feasible line `x₁ = 0`: at `x₁ = u`,
`‖c‖ = u²/2 ∼ ε₀` while `‖∇ν‖ = u³/2 ∼ ε₀ ε₁`. The `k`-th INNER call moves from `x_k` along
`x₂` to `x_{k+1}` with `f(x_{k+1}) = t_k - E`, `E ≈ u³/2`; there the gradient
`∇μ(x_{k+1}, t_k) = ∇ν + (f - t_k) ∇f` nearly cancels in its first coordinate, so INNER's test
holds, while after the reflection `t_{k+1} = 2 f(x_{k+1}) - t_k` ((14.3.35)) the first coordinate
doubles and (14.3.34) fails. Each such iteration lowers the target by `2E ∼ ε₀ ε₁` only.

## Scope

The INNER calls are described by their iterates. The book's INNER is nonspecific (§14.3,
OCR ≈ 16893–16919): it is assumed to return a point of `X` with radii in `(0, 1]` satisfying
(14.3.19), within (14.3.20)–(14.3.21) evaluations, and (for Phase 2, OCR ≈ 17477, 21203–21295) to
satisfy (14.2.11), (14.2.13) with `t`-independent constants. Theorem 14.3.9 further assumes that
"the INNER algorithm is of regularization type" with the exponents `π_j` of (14.2.12), a table of
specific algorithms (ARqp-SC, ARqpC-SC, …); its proof uses about INNER only the properties just
listed, so "regularization type" is taken here to mean that contract with those exponents. The
calls here satisfy all of these properties on the run (`theorem_14_3_9_false`), but they are not
produced by a regularization algorithm of (14.2.12). The cost hypothesis is checked per call:
read uniformly over all admissible inputs it is unsatisfiable on this problem for `π₁ < 2`
(`theorem_14_3_9_cost_hypothesis_unsatisfiable`, the mechanism of
`exists_algorithm_14_3_1_cost_contract_counterexample`). The cost bound on the run needs
`π₁ ≥ 4/3`: a call costs one evaluation while its bound is `∼ κ u^{4 - 3π₁}` (`‖r‖ ∼ u²`,
`ε₁ ∼ u`); exponents in `(1, 4/3)` would need a flatter constraint (e.g. `c(x) = x₁^a/a`, giving
`ε₁ ∼ ε₀^{(a-1)/a}`), which is not formalized. The calls are not runs of ARqp-SC: for `p = 2`
the model minimizer of `μ(·, t_k)` at `x_k` (Hessian `[[1 + 3u²/2, -1], [-1, 1]]`, gradient
`(u³/2 + E, -E)`) cuts `x₁` by about `u/3`, and the pure-`x₂` step violates the step-termination
rule `‖∇m(s)‖ ≤ θ‖s‖^p` (`u³/2` against `u^{3p}`). Genuine ARqp-SC runs with `q = 1 < p` do
exceed the printed order under the per-call reading when `p ≥ 4`
(`Chapter14.Section03GenuineSharp`, `theorem_14_3_9_arqp_counterexample`): there the objective is
tilted (`f(x) = x₁ - x₂/16`) so that at the landing points only a gradient `≲ u³/32` remains and
the ARqp-SC model criticality (12.2.29) holds, the Taylor models of degree `p ≥ 4` of the quartic
`μ(·, t_k)` are exact, and each step is an approximate critical point of the model (Algorithm
14.1.2 started with a small `μ` at Step 2.1). For `p ∈ {2, 3}` they exceed it too
(`Chapter14.Section03GenuineSharp2`, with `c(x) = x₁⁴` and inexact Taylor models); under the
literal reading the theorem is vacuous for these runs when `π₁ < 2`.
-/

open Set Metric
open scoped Nat ContDiff

namespace CartisGouldToint.Chapter14

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

namespace Theorem1439OrderCex

/-- The simple constraint set `X = [-1, 1]²`. -/
def boxX : Set ℝ² := {x | |x 0| ≤ 1 ∧ |x 1| ≤ 1}

/-- The objective `f(x) = x₁ - x₂`. -/
noncomputable def objF : ℝ² → ℝ := fun x => x 0 - x 1

/-- The unit vector of `ℝ¹`. -/
noncomputable def unitE : ℝ¹ := EuclideanSpace.single 0 1

/-- The constraint `c(x) = x₁²/2`. -/
noncomputable def conC : ℝ² → ℝ¹ := fun x => (x 0 ^ 2 / 2) • unitE

/-- The point `(a, b)` of `ℝ²`. -/
noncomputable def pt (a b : ℝ) : ℝ² := EuclideanSpace.single 0 a + EuclideanSpace.single 1 b

/-- The first coordinate of `(a, b)`. -/
@[simp] theorem pt_zero (a b : ℝ) : pt a b 0 = a := by simp [pt]

/-- The second coordinate of `(a, b)`. -/
@[simp] theorem pt_one (a b : ℝ) : pt a b 1 = b := by simp [pt]

/-- `f(a, b) = a - b`. -/
theorem objF_pt (a b : ℝ) : objF (pt a b) = a - b := by simp [objF]

/-- `‖e‖ = 1`. -/
theorem norm_unitE : ‖unitE‖ = 1 := by simp [unitE]

/-- `‖c(y)‖ = y₁²/2`. -/
theorem norm_conC (y : ℝ²) : ‖conC y‖ = y 0 ^ 2 / 2 := by
  simp [conC, norm_smul, norm_unitE]

/-- The derivative of `f`. -/
theorem hasFDerivAt_objF (y : ℝ²) :
    HasFDerivAt objF (EuclideanSpace.proj (0 : Fin 2) - EuclideanSpace.proj (1 : Fin 2) :
      ℝ² →L[ℝ] ℝ) y :=
  (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).sub (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 1)

/-- The derivative of `c`: `d ↦ y₁ d₁ e`. -/
theorem hasFDerivAt_conC (y : ℝ²) :
    HasFDerivAt conC ((y 0 • (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)).smulRight unitE)
      y := by
  have h1 : HasFDerivAt (fun x : ℝ² => x 0 ^ 2 / 2)
      (y 0 • (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)) y := by
    have := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).pow 2).mul_const (1 / 2 : ℝ)
    convert this using 1
    · funext x; ring
    · ext d; simp; ring
  exact h1.smul_const unitE

/-- The first-order Taylor decrement of `μ(·, t)` at `y`:
`-∇μ(y, t)[d] = -(y₁³/2 + (f(y) - t)) d₁ + (f(y) - t) d₂`. -/
theorem decr (y : ℝ²) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit objF conC t) y).taylorDecrement 1 d =
      -(y 0 ^ 3 / 2 + (objF y - t)) * d 0 + (objF y - t) * d 1 := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [(Constrained.hasFDerivAt_targetMerit (t := t) (hasFDerivAt_objF y)
    (hasFDerivAt_conC y)).fderiv]
  simp [conC, unitE]
  ring

/-- An upper bound on the first-order measure with radius `1` (Cauchy–Schwarz). -/
theorem measure_le (y : ℝ²) (t : ℝ) {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit objF conC t) y) 1 1 S ≤
      √((y 0 ^ 3 / 2 + (objF y - t)) ^ 2 + (objF y - t) ^ 2) := by
  refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, h0⟩
    fun d hd => ?_
  rw [decr]
  have hd1 : ‖d‖ ^ 2 ≤ 1 := by
    have := mem_closedBall_zero_iff.1 hd.1
    nlinarith [norm_nonneg d]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs] at hd1
  set a := objF y - t
  set A := y 0 ^ 3 / 2 + a
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (A * d 1 + a * d 0), sq_nonneg a, sq_nonneg A]

/-- A lower bound on the first-order measure with radius `1`, along `d = -e₁`. -/
theorem le_measure (y : ℝ²) (t : ℝ) {S : Set ℝ²} (hS : EuclideanSpace.single 0 (-1) ∈ S) :
    y 0 ^ 3 / 2 + (objF y - t) ≤
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit objF conC t) y) 1 1
        S := by
  have := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit objF conC t) y) 1 (δ := 1)
    (d := EuclideanSpace.single 0 (-1)) ⟨by simp, hS⟩
  rw [decr] at this
  simpa using this

/-- `‖r(y, t)‖² = (y₁²/2)² + (f(y) - t)²`. -/
theorem resid_sq (y : ℝ²) (t : ℝ) :
    Constrained.targetResidual objF conC t y ^ 2 = (y 0 ^ 2 / 2) ^ 2 + (objF y - t) ^ 2 := by
  rw [Constrained.targetResidual_sq, norm_conC]

/-! #### The parameters and the run -/

section Run

variable (u : ℝ) (N : ℕ)

/-- The tolerances `ε₀ = u²/2 + u³/2`, `ε_j = 3u/2` (`j ≥ 1`). -/
noncomputable def eps : ℕ → ℝ := fun j => if j = 0 then u ^ 2 / 2 + u ^ 3 / 2 else 3 * u / 2

/-- The overshoot `E_j = (u³/2)(1 - j/(4(N + 1)))` of the `(j-1)`-th INNER call below its
target. -/
noncomputable def ov (j : ℕ) : ℝ := u ^ 3 / 2 * (1 - j / (4 * (N + 1)))

/-- The targets `t_k = 1 - ε₀ - u³ (k - 1) + u³ (k (k + 1) - 2)/(8 (N + 1))`, so that
`t_{k+1} = t_k - 2 E_{k+1}`. -/
noncomputable def tgt (k : ℕ) : ℝ :=
  1 - (u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * ((k : ℝ) - 1) +
    u ^ 3 * ((k : ℝ) * (k + 1) - 2) / (8 * (N + 1))

open Classical in
/-- The amount `t_k - f(x_{k+1})` of the `k`-th call: `E_{k+1}` for `k < N`, `0` for `k = N`. -/
noncomputable def gap (k : ℕ) : ℝ := if k < N then ov u N (k + 1) else 0

/-- The outer iterates: `x₁ = (0, -1)`, `x_{k+1} = (u, u - t_k + gap_k)` for `k ≥ 1`. -/
noncomputable def xs : ℕ → ℝ²
  | 0 => pt 0 (-1)
  | k + 1 => if k = 0 then pt 0 (-1) else pt u (u - (tgt u N k - gap u N k))

/-- The Phase-2 sequences: iterates `xs`, targets `tgt`, radii `1`, and the `k`-th INNER call
makes one successful iteration from `x_k` to `x_{k+1}`. -/
noncomputable def run : TPqpSeq 2 :=
  ⟨xs u N, tgt u N, fun _ _ => 1, fun k i => if i = 0 then xs u N k else xs u N (k + 1),
    fun _ => 1, fun _ _ => True⟩

end Run

section Facts

variable {u : ℝ} {N : ℕ}

/-- `ε₀ = u²/2 + u³/2`. -/
theorem eps_zero : eps u 0 = u ^ 2 / 2 + u ^ 3 / 2 := by simp [eps]

/-- `ε₁ = 3u/2`. -/
theorem eps_one : eps u 1 = 3 * u / 2 := by simp [eps]

/-- `t₁ = 1 - ε₀`. -/
theorem tgt_one : tgt u N 1 = 1 - (u ^ 2 / 2 + u ^ 3 / 2) := by simp [tgt]; norm_num

/-- The target update of case (b): `t_{k+1} = t_k - 2 E_{k+1}`. -/
theorem tgt_succ (k : ℕ) : tgt u N (k + 1) = tgt u N k - 2 * ov u N (k + 1) := by
  unfold tgt ov
  have : (8 * ((N : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `x₁ = (0, -1)`. -/
theorem xs_one : xs u N 1 = pt 0 (-1) := by simp [xs]

/-- `x_{k+1} = (u, u - t_k + gap_k)` for `k ≥ 1`. -/
theorem xs_succ {k : ℕ} (hk : 1 ≤ k) :
    xs u N (k + 1) = pt u (u - (tgt u N k - gap u N k)) := by
  simp [xs, show k ≠ 0 by omega]

/-- The first coordinate of `x_{k+1}`, `k ≥ 1`, is `u`. -/
theorem xs_succ_zero {k : ℕ} (hk : 1 ≤ k) : xs u N (k + 1) 0 = u := by
  rw [xs_succ hk, pt_zero]

/-- `f(x_{k+1}) = t_k - gap_k` for `k ≥ 1`. -/
theorem objF_xs_succ {k : ℕ} (hk : 1 ≤ k) : objF (xs u N (k + 1)) = tgt u N k - gap u N k := by
  rw [xs_succ hk, objF_pt]; ring

/-- `gap_k = E_{k+1}` for `k < N`. -/
theorem gap_of_lt {k : ℕ} (hk : k < N) : gap u N k = ov u N (k + 1) := by simp [gap, hk]

/-- `gap_N = 0`: the last call lands on its target. -/
theorem gap_self : gap u N N = 0 := by simp [gap]

variable (hu : 0 < u)
include hu

/-- `E_j ≤ u³/2`. -/
theorem ov_le (j : ℕ) : ov u N j ≤ u ^ 3 / 2 := by
  unfold ov
  have : 0 ≤ (j : ℝ) / (4 * (N + 1)) := by positivity
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_j ≥ 3u³/8` for `j ≤ N + 1`. -/
theorem le_ov {j : ℕ} (hj : j ≤ N + 1) : 3 / 4 * (u ^ 3 / 2) ≤ ov u N j := by
  unfold ov
  have hN : (0 : ℝ) < 4 * (N + 1) := by positivity
  have : (j : ℝ) / (4 * (N + 1)) ≤ 1 / 4 := by
    rw [div_le_iff₀ hN]
    have : (j : ℝ) ≤ N + 1 := by exact_mod_cast hj
    linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_{j+1} ≤ E_j`. -/
theorem ov_succ_le (j : ℕ) : ov u N (j + 1) ≤ ov u N j := by
  unfold ov
  have hN : (0 : ℝ) < 4 * (N + 1) := by positivity
  have : (j : ℝ) / (4 * (N + 1)) ≤ ((j + 1 : ℕ) : ℝ) / (4 * (N + 1)) := by
    gcongr; linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_{j+1} < E_j`. -/
theorem ov_succ_lt (j : ℕ) : ov u N (j + 1) < ov u N j := by
  unfold ov
  have hN : (0 : ℝ) < 4 * (N + 1) := by positivity
  have : (j : ℝ) / (4 * (N + 1)) < ((j + 1 : ℕ) : ℝ) / (4 * (N + 1)) := by
    gcongr; linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `gap_k < E_k` for `k ≤ N`. -/
theorem gap_lt_ov {k : ℕ} (hk : k ≤ N) : gap u N k < ov u N k := by
  unfold gap
  split_ifs with h
  · exact ov_succ_lt hu k
  · exact (by positivity : (0 : ℝ) < 3 / 4 * (u ^ 3 / 2)).trans_le (le_ov hu (by omega))

/-- `gap_k ≥ 0`. -/
theorem gap_nonneg (k : ℕ) : 0 ≤ gap u N k := by
  unfold gap
  split_ifs with h
  · exact (by positivity : (0 : ℝ) ≤ 3 / 4 * (u ^ 3 / 2)).trans (le_ov hu (by omega))
  · exact le_rfl

/-- `gap_k ≤ E_k` for `k ≤ N`. -/
theorem gap_le_ov {k : ℕ} (hk : k ≤ N) : gap u N k ≤ ov u N k := by
  unfold gap
  split_ifs with h
  · exact ov_succ_le hu k
  · exact (by positivity : (0 : ℝ) ≤ 3 / 4 * (u ^ 3 / 2)).trans (le_ov hu (by omega))

/-- `gap_k ≤ u³/2`. -/
theorem gap_le (k : ℕ) : gap u N k ≤ u ^ 3 / 2 := by
  unfold gap
  split_ifs
  · exact ov_le hu _
  · positivity

/-- `1 - ε₀ - u³ N ≤ t_k ≤ 1 - ε₀` for `k ∈ [1, N]`. -/
theorem tgt_mem {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    1 - (u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * N ≤ tgt u N k ∧
      tgt u N k ≤ 1 - (u ^ 2 / 2 + u ^ 3 / 2) := by
  unfold tgt
  have hN : (0 : ℝ) < 8 * (N + 1) := by positivity
  have hK1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hKN : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hu3 : 0 < u ^ 3 := by positivity
  have h0 : 0 ≤ u ^ 3 * ((k : ℝ) * (k + 1) - 2) / (8 * (N + 1)) := by
    apply div_nonneg _ hN.le
    apply mul_nonneg hu3.le
    nlinarith
  have h1 : u ^ 3 * ((k : ℝ) * (k + 1) - 2) / (8 * (N + 1)) ≤ u ^ 3 * ((k : ℝ) - 1) := by
    rw [div_le_iff₀ hN]
    have : ((k : ℝ) * (k + 1) - 2) ≤ ((k : ℝ) - 1) * (8 * (N + 1)) := by nlinarith
    nlinarith
  constructor <;> nlinarith

end Facts

section Run2

variable {u : ℝ} {N : ℕ} (hu : 0 < u) (hu7 : u ≤ 1 / 7) (hNu : u ^ 3 * N ≤ 1)
include hu

omit hu in
/-- `f(x_{k+1}) - t_{k+1} = E_{k+1}` for `k ∈ [1, N)`. -/
theorem objF_xs_sub {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    objF (xs u N (k + 1)) - tgt u N (k + 1) = ov u N (k + 1) := by
  rw [objF_xs_succ hk1, gap_of_lt hkN, tgt_succ]; ring

omit hu in
/-- `t_k - f(x_{k+1}) = gap_k`. -/
theorem tgt_sub_objF {k : ℕ} (hk1 : 1 ≤ k) :
    objF (xs u N (k + 1)) - tgt u N k = -gap u N k := by
  rw [objF_xs_succ hk1]; ring

include hu7 hNu in
/-- The iterates `x_k`, `k ∈ [1, N + 1]`, lie in `X`. -/
theorem xs_mem {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N + 1) : xs u N k ∈ boxX := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [xs_one]; simp [boxX]
  · rw [xs_succ hj]
    obtain ⟨h1, h2⟩ := tgt_mem hu hj (by omega : j ≤ N)
    have hg0 := gap_nonneg hu (N := N) j
    have hg1 := gap_le hu (N := N) j
    have hu2 : u ^ 2 ≤ u / 7 := by nlinarith
    have hu3 : u ^ 3 ≤ u ^ 2 / 7 := by nlinarith
    simp only [boxX, mem_ofPred_eq, pt_zero, pt_one]
    refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩

omit hu in
/-- `‖r(y, t)‖² = (u²/2)² + (f(y) - t)²` at the points with first coordinate `u`. -/
theorem resid_sq_of {y : ℝ²} (hy : y 0 = u) (t : ℝ) :
    Constrained.targetResidual objF conC t y ^ 2 = (u ^ 2 / 2) ^ 2 + (objF y - t) ^ 2 := by
  rw [resid_sq, hy]

omit hu in
/-- `‖r(x_{k+1}, t_k)‖² = (u²/2)² + gap_k²`. -/
theorem resid_end {k : ℕ} (hk1 : 1 ≤ k) :
    Constrained.targetResidual objF conC (tgt u N k) (xs u N (k + 1)) ^ 2 =
      (u ^ 2 / 2) ^ 2 + gap u N k ^ 2 := by
  rw [resid_sq_of (xs_succ_zero hk1), tgt_sub_objF hk1]; ring

omit hu in
/-- `‖r(x_{k+1}, t_{k+1})‖² = (u²/2)² + E_{k+1}²` for `k ∈ [1, N)`. -/
theorem resid_new {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    Constrained.targetResidual objF conC (tgt u N (k + 1)) (xs u N (k + 1)) ^ 2 =
      (u ^ 2 / 2) ^ 2 + ov u N (k + 1) ^ 2 := by
  rw [resid_sq_of (xs_succ_zero hk1), objF_xs_sub hk1 hkN]

/-- `‖r(x_k, t_k)‖² ≥ (u²/2)² + E_k²` for `k ∈ [1, N]`. -/
theorem resid_cur_sq {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (u ^ 2 / 2) ^ 2 + ov u N k ^ 2 ≤
      Constrained.targetResidual objF conC (tgt u N k) (xs u N k) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [resid_sq, xs_one, tgt_one, objF_pt]
    simp only [pt_zero]
    have h0 := le_ov hu (N := N) (j := 1) (by omega)
    have h1 := ov_le hu (N := N) 1
    have : 0 < u ^ 2 / 2 := by positivity
    nlinarith
  · rw [resid_new hj (by omega)]

/-- `‖r(x_k, t_k)‖ ≥ u²/2` for `k ∈ [1, N]`. -/
theorem resid_cur_ge {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    u ^ 2 / 2 ≤ Constrained.targetResidual objF conC (tgt u N k) (xs u N k) := by
  have h := resid_cur_sq hu hk1 hkN
  have := Constrained.targetResidual_nonneg (f := objF) (c := conC) (t := tgt u N k)
    (x := xs u N k)
  nlinarith [sq_nonneg (ov u N k), sq_nonneg (u ^ 2 / 2 -
    Constrained.targetResidual objF conC (tgt u N k) (xs u N k))]

omit hu in
/-- `‖r(x_{k+1}, t_k)‖ ≥ u²/2`. -/
theorem resid_end_ge {k : ℕ} (hk1 : 1 ≤ k) :
    u ^ 2 / 2 ≤ Constrained.targetResidual objF conC (tgt u N k) (xs u N (k + 1)) := by
  have h := resid_end (u := u) (N := N) hk1
  have := Constrained.targetResidual_nonneg (f := objF) (c := conC) (t := tgt u N k)
    (x := xs u N (k + 1))
  nlinarith [sq_nonneg (gap u N k)]

include hu7 hNu in
/-- **INNER's test (14.3.19) holds at the end of every call** `k ∈ [1, N]`, for `β ≥ 2/3`:
`‖∇μ(x_{k+1}, t_k)‖ ≤ u³/2 ≤ β ‖r(x_k, t_k)‖ ε₁`. -/
theorem innerTest {β : ℝ} (hβ : 2 / 3 ≤ β) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (run u N).InnerTest objF conC boxX 1 β (eps u) k := by
  intro j hj
  obtain rfl : j = 1 := by simpa using hj
  change Optimization.taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit objF conC (tgt u N k)) (xs u N (k + 1))) 1 1
      {d | xs u N (k + 1) + d ∈ boxX} ≤
    β * Constrained.targetResidual objF conC (tgt u N k) (xs u N k) * eps u 1 * 1 ^ 1 / (1 : ℕ)!
  have h0 : (0 : ℝ²) ∈ {d | xs u N (k + 1) + d ∈ boxX} := by
    simpa using xs_mem hu hu7 hNu (k := k + 1) (by omega) (by omega)
  refine (measure_le _ _ h0).trans ?_
  rw [xs_succ_zero hk1, tgt_sub_objF hk1, eps_one]
  have hg0 := gap_nonneg hu (N := N) k
  have hg1 := gap_le hu (N := N) k
  have hR := resid_cur_ge hu hk1 hkN
  have hs : √((u ^ 3 / 2 + -gap u N k) ^ 2 + (-gap u N k) ^ 2) ≤ u ^ 3 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  refine hs.trans ?_
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one]
  have : β * (u ^ 2 / 2) * (3 * u / 2) ≤
      β * Constrained.targetResidual objF conC (tgt u N k) (xs u N k) * (3 * u / 2) := by
    gcongr
  nlinarith

include hu7 hNu in
/-- **(14.3.34) fails at `(x_{k+1}, t_{k+1})`** for `k ∈ [1, N)`: along `d = -e₁` the decrease
is `u³/2 + E_{k+1} ≥ 7u³/8 > ε₁ ‖r(x_{k+1}, t_{k+1})‖`. -/
theorem not_meritCrit_new {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    ¬ meritCrit objF conC boxX 1 (eps u) (tgt u N (k + 1)) (xs u N (k + 1)) (fun _ => 1) := by
  intro h
  have h1 := h 1 (by simp)
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
  have hmem := xs_mem hu hu7 hNu (k := k + 1) (by omega) (by omega)
  have hS : EuclideanSpace.single 0 (-1) ∈ {d | xs u N (k + 1) + d ∈ boxX} := by
    simp only [boxX, mem_ofPred_eq] at hmem ⊢
    have e0 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 0 = -1 := by simp
    have e1 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 1 = 0 := by simp
    simp only [PiLp.add_apply, e0, e1, add_zero, xs_succ_zero hk1]
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, hmem.2⟩
  have hlow := le_measure (xs u N (k + 1)) (tgt u N (k + 1)) hS
  rw [xs_succ_zero hk1, objF_xs_sub hk1 hkN] at hlow
  rw [eps_one] at h1
  have hov := le_ov hu (N := N) (j := k + 1) (by omega)
  have hov1 := ov_le hu (N := N) (k + 1)
  have hR : Constrained.targetResidual objF conC (tgt u N (k + 1)) (xs u N (k + 1)) ≤
      u ^ 2 / 2 + u ^ 3 / 2 := by
    have hsq := resid_new (u := u) hk1 hkN
    have := Constrained.targetResidual_nonneg (f := objF) (c := conC) (t := tgt u N (k + 1))
      (x := xs u N (k + 1))
    have : 0 ≤ ov u N (k + 1) := (by positivity : (0 : ℝ) ≤ 3 / 4 * (u ^ 3 / 2)).trans hov
    nlinarith [sq_nonneg (Constrained.targetResidual objF conC (tgt u N (k + 1))
      (xs u N (k + 1)) - (u ^ 2 / 2 + u ^ 3 / 2))]
  have : 3 * u / 2 * Constrained.targetResidual objF conC (tgt u N (k + 1)) (xs u N (k + 1)) ≤
      3 * u / 2 * (u ^ 2 / 2 + u ^ 3 / 2) := by gcongr
  have hu3 : 0 < u ^ 3 := by positivity
  have hu4 : u ^ 4 ≤ u ^ 3 / 7 := by nlinarith
  have e : 3 * u / 2 * (u ^ 2 / 2 + u ^ 3 / 2) = 3 / 4 * u ^ 3 + 3 / 4 * u ^ 4 := by ring
  linarith

include hu7 hNu in
/-- The third test of (14.3.32) holds at `(x_{N+1}, t_N)`: `‖∇μ(x_{N+1}, t_N)‖ = u³/2 ≤
ε₁ ‖r(x_{N+1}, t_N)‖ = 3u³/4`. -/
theorem meritCrit_end (hN : 1 ≤ N) :
    meritCrit objF conC boxX 1 (eps u) (tgt u N N) (xs u N (N + 1)) (fun _ => 1) := by
  intro j hj
  obtain rfl : j = 1 := by simpa using hj
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one]
  have h0 : (0 : ℝ²) ∈ {d | xs u N (N + 1) + d ∈ boxX} := by
    simpa using xs_mem hu hu7 hNu (k := N + 1) (by omega) le_rfl
  refine (measure_le _ _ h0).trans ?_
  rw [xs_succ_zero hN, tgt_sub_objF hN, gap_self, eps_one]
  have hR := resid_end_ge (u := u) (N := N) hN
  have hs : √((u ^ 3 / 2 + -0) ^ 2 + (-0) ^ 2) ≤ u ^ 3 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  refine hs.trans ?_
  have : 3 * u / 2 * (u ^ 2 / 2) ≤
      3 * u / 2 * Constrained.targetResidual objF conC (tgt u N N) (xs u N (N + 1)) := by
    gcongr
  nlinarith

/-- **`μ(·, t_k)` decreases strictly along every call** `k ∈ [1, N]`. -/
theorem merit_lt {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Constrained.targetMerit objF conC (tgt u N k) (xs u N (k + 1)) <
      Constrained.targetMerit objF conC (tgt u N k) (xs u N k) := by
  rw [Constrained.targetMerit_eq, Constrained.targetMerit_eq, resid_end hk1]
  have h1 := resid_cur_sq hu hk1 hkN
  have h2 := gap_nonneg hu (N := N) k
  have h3 := gap_lt_ov hu (N := N) hkN
  nlinarith

include hu7 in
/-- `θ ε₀ ≤ u²/2` for `θ = 3/4`. -/
theorem theta_eps_le : 3 / 4 * eps u 0 ≤ u ^ 2 / 2 := by
  rw [eps_zero]; nlinarith [pow_pos hu 2]

omit hu in
/-- The tolerances are positive. -/
theorem eps_pos (hu : 0 < u) (j : ℕ) : 0 < eps u j := by
  unfold eps; split_ifs <;> positivity

include hu7 in
/-- The tolerances are at most `1`. -/
theorem eps_le_one (j : ℕ) : eps u j ≤ 1 := by
  unfold eps; split_ifs <;> nlinarith [pow_pos hu 2, pow_pos hu 3]

include hu7 in
/-- No outer iteration `k ≥ 1` is in `𝒦_a`. -/
theorem not_isKa {k : ℕ} (hk1 : 1 ≤ k) : ¬ (run u N).IsKa objF conC (3 / 4) (eps u) k := by
  unfold TPqpSeq.IsKa
  rw [not_lt]
  exact (theta_eps_le hu hu7).trans (resid_end_ge hk1)

include hu7 in
/-- The outer iterations `k ∈ [1, N)` are in `𝒦_b`. -/
theorem isKb {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    (run u N).IsKb objF conC (3 / 4) (eps u) k := by
  refine ⟨(theta_eps_le hu hu7).trans (resid_end_ge hk1), ?_⟩
  change objF (xs u N (k + 1)) < tgt u N k
  rw [objF_xs_succ hk1, gap_of_lt hkN]
  have := le_ov hu (N := N) (j := k + 1) (by omega)
  have : 0 < u ^ 3 := by positivity
  linarith

omit hu in
/-- The outer iteration `N` is not in `𝒦_b`: `f(x_{N+1}) = t_N`. -/
theorem not_isKb_self (hN : 1 ≤ N) : ¬ (run u N).IsKb objF conC (3 / 4) (eps u) N := by
  intro h
  have h2 := h.2
  change objF (xs u N (N + 1)) < tgt u N N at h2
  rw [objF_xs_succ hN, gap_self] at h2
  linarith

include hu7 in
/-- Phase 2 stops at `N` (case (c)). -/
theorem stop_self (hN : 1 ≤ N) : (run u N).Stop objF conC boxX 1 (3 / 4) (eps u) N :=
  Or.inl ⟨not_isKa hu hu7 hN, not_isKb_self hN⟩

include hu7 hNu in
/-- Phase 2 does not stop at `k ∈ [1, N)`. -/
theorem not_stop {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    ¬ (run u N).Stop objF conC boxX 1 (3 / 4) (eps u) k := by
  rintro (⟨-, hb⟩ | ⟨-, hm⟩)
  · exact hb (isKb hu hu7 hk1 hkN)
  · exact not_meritCrit_new hu hu7 hNu hk1 hkN hm

include hu7 hNu in
/-- Phase 2 does not stop before `N`. -/
theorem before_self : (run u N).Before objF conC boxX 1 (3 / 4) (eps u) N :=
  fun _ hj1 hjN => not_stop hu hu7 hNu hj1 hjN

include hu7 in
/-- Every outer iteration reached is at most `N`. -/
theorem le_of_before (hN : 1 ≤ N) {k : ℕ}
    (h : (run u N).Before objF conC boxX 1 (3 / 4) (eps u) k) : k ≤ N := by
  by_contra hk
  exact h N hN (by omega) (stop_self hu hu7 hN)

include hu7 hNu in
/-- Phase 2 terminates at the outer iteration `N`. -/
theorem isEnd (hN : 1 ≤ N) : (run u N).IsEnd objF conC boxX 1 (3 / 4) (eps u) N :=
  ⟨hN, stop_self hu hu7 hN, before_self hu hu7 hNu⟩

include hu7 hNu in
/-- **The sequences form a Phase-2 run of TPqp-GC** for `θ = 3/4` and every `β ∈ (0, θ]`. -/
theorem isTPqpGCPhase2 (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) (hβθ : β ≤ 3 / 4) :
    IsTPqpGCPhase2 objF conC boxX 1 (3 / 4) β (eps u) (pt 0 (-1)) (run u N) := by
  have hc1 : ‖conC (pt 0 (-1))‖ = 0 := by rw [norm_conC]; simp
  refine ⟨by norm_num, by norm_num, hβ, hβθ, fun j _ => eps_pos hu j,
    fun j _ => eps_le_one hu hu7 j, by simp [boxX],
    by rw [hc1]; exact (mul_pos (by norm_num) (eps_pos hu 0)).le, xs_one (u := u) (N := N), ?_,
    fun k hk1 hk => xs_mem hu hu7 hNu (by omega) (by have := le_of_before hu hu7 hN hk; omega),
    fun _ _ _ _ _ => ⟨one_pos, le_rfl⟩, fun k hk1 hk => ?_, fun k _ _ => by simp [run],
    fun k _ _ => by simp [run], fun k hk1 hk i hi => ?_, fun k hk1 hk i hi => ?_,
    fun k hk1 _ ha => absurd ha (not_isKa hu hu7 hk1), fun k hk1 hk hb => ?_⟩
  · change tgt u N 1 = objF (pt 0 (-1)) - √(eps u 0 ^ 2 - ‖conC (pt 0 (-1))‖ ^ 2)
    rw [hc1, tgt_one, objF_pt, eps_zero]
    rw [show (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 - (0 : ℝ) ^ 2 = (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    ring
  · have hkN := le_of_before hu hu7 hN hk
    rcases Nat.lt_or_ge k N with hlt | hge
    · exact Or.inr (Or.inl (isKb hu hu7 hk1 hlt).2)
    · obtain rfl : k = N := by omega
      exact Or.inr (Or.inr (meritCrit_end hu hu7 hNu hN))
  · change i < 1 at hi
    obtain rfl : i = 0 := by omega
    have hkN := le_of_before hu hu7 hN hk
    exact (merit_lt hu hk1 hkN).le
  · change i < 1 at hi
    obtain rfl : i = 0 := by omega
    change 3 / 4 * eps u 0 ≤ Constrained.targetResidual objF conC (tgt u N k) (xs u N k)
    exact (theta_eps_le hu hu7).trans (resid_cur_ge hu hk1 (le_of_before hu hu7 hN hk))
  · have hkN := le_of_before hu hu7 hN hk
    have hlt : k < N := lt_of_le_of_ne hkN fun h => not_isKb_self hN (h ▸ hb)
    change tgt u N (k + 1) = 2 * objF (xs u N (k + 1)) - tgt u N k
    rw [objF_xs_succ hk1, gap_of_lt hlt, tgt_succ]
    ring

include hu7 hNu in
/-- **The INNER calls satisfy the strong contract** `IsInnerPhaseRunStrong` for every `β ∈ [2/3,
3/4]`, every `κ_decr`, exponents `π`, `κ_uns + κ_unc ≥ 1` and radii `ρ₁ ≤ 1`: each call makes one
successful iteration and ends at a point passing INNER's test, so no decrease is required. -/
theorem isInnerPhaseRunStrong (hN : 1 ≤ N) {β : ℝ} (hβ : 2 / 3 ≤ β) {κdecr κuns κunc : ℝ}
    {π ρ : ℕ → ℝ} (hκ : 1 ≤ κuns + κunc) (hρ : ρ 1 ≤ 1) :
    IsInnerPhaseRunStrong objF conC boxX 1 (3 / 4) β (eps u) (run u N) κdecr κuns κunc π ρ := by
  refine ⟨fun k _ _ => ?_, fun k _ _ i _ hs => absurd trivial hs,
    fun k hk1 hk i hi _ hcont _ => ?_, fun k hk1 hk _ _ j hj => ?_⟩
  · have : (run u N).succCount k = 1 := by
      classical
      unfold TPqpSeq.succCount
      rw [Finset.card_eq_one]
      refine ⟨0, Finset.eq_singleton_iff_unique_mem.2
        ⟨Finset.mem_filter.2 ⟨by simp [run], trivial⟩, fun x hx => ?_⟩⟩
      have := (Finset.mem_filter.1 hx).1
      simpa [run] using this
    rw [this]
    change ((1 : ℕ) : ℝ) ≤ κuns * ((1 : ℕ) : ℝ) + κunc
    push_cast
    linarith
  · change i < 1 at hi
    obtain rfl : i = 0 := by omega
    rcases hcont with h | h
    · exact absurd h (by change ¬ 0 + 1 < 1; omega)
    · exact absurd (innerTest hu hu7 hNu hβ hk1 (le_of_before hu hu7 hN hk)) h
  · obtain rfl : j = 1 := by simpa using hj
    exact hρ

include hu7 hNu in
/-- **INNER's test fails at the start of every call** `k ∈ [1, N]` for `β ≤ 3/4`: along `-e₁` the
decrease of the linear model of `μ(·, t_k)` at `x_k` exceeds `β ‖r(x_k, t_k)‖ ε₁`. So a genuine
INNER must move in every call. -/
theorem not_innerTest_start {β : ℝ} (hβ : β ≤ 3 / 4) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    β * Constrained.targetResidual objF conC (tgt u N k) (xs u N k) * eps u 1 <
      Optimization.taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit objF conC (tgt u N k)) (xs u N k)) 1 1
        {d | xs u N k + d ∈ boxX} := by
  have hmem := xs_mem hu hu7 hNu (k := k) hk1 (by omega)
  have hS : EuclideanSpace.single 0 (-1) ∈ {d | xs u N k + d ∈ boxX} := by
    simp only [boxX, mem_ofPred_eq] at hmem ⊢
    have e0 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 0 = -1 := by simp
    have e1 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 1 = 0 := by simp
    simp only [PiLp.add_apply, e0, e1, add_zero]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [xs_one]; simp
    · rw [xs_succ_zero hj]
      exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, hmem.2⟩
  refine lt_of_lt_of_le ?_ (le_measure (xs u N k) (tgt u N k) hS)
  rw [eps_one]
  have hR0 := Constrained.targetResidual_nonneg (f := objF) (c := conC) (t := tgt u N k)
    (x := xs u N k)
  have hu3 : 0 < u ^ 3 := by positivity
  have hu4 : u ^ 4 ≤ u ^ 3 / 7 := by nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `x₁ = (0, -1)`: `‖r‖ = ε₀` and the decrease is `ε₀`
    have hR : Constrained.targetResidual objF conC (tgt u N 1) (xs u N 1) =
        u ^ 2 / 2 + u ^ 3 / 2 := by
      rw [Constrained.targetResidual_def, xs_one, norm_conC, tgt_one, objF_pt]
      simp only [pt_zero]
      rw [show ((0 : ℝ) ^ 2 / 2) ^ 2 + (0 - -1 - (1 - (u ^ 2 / 2 + u ^ 3 / 2))) ^ 2 =
        (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [hR, xs_one, objF_pt, tgt_one]
    simp only [pt_zero]
    have h2 : 0 < u ^ 2 / 2 + u ^ 3 / 2 := by positivity
    have : β * (u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2) ≤
        3 / 4 * (u ^ 2 / 2 + u ^ 3 / 2) * (3 / 14) := by
      have : 0 ≤ β * (u ^ 2 / 2 + u ^ 3 / 2) ∨ β * (u ^ 2 / 2 + u ^ 3 / 2) < 0 := le_or_gt _ _
      rcases this with h | h
      · calc β * (u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2)
            ≤ β * (u ^ 2 / 2 + u ^ 3 / 2) * (3 / 14) :=
              mul_le_mul_of_nonneg_left (by linarith) h
          _ ≤ 3 / 4 * (u ^ 2 / 2 + u ^ 3 / 2) * (3 / 14) := by gcongr
      · nlinarith
    nlinarith
  · -- `x_k = (u, ·)` with `f(x_k) - t_k = E_k`
    have hjN : j < N := by omega
    rw [xs_succ_zero hj, objF_xs_sub hj hjN]
    have hov := le_ov hu (N := N) (j := j + 1) (by omega)
    have hov1 := ov_le hu (N := N) (j + 1)
    have hR : Constrained.targetResidual objF conC (tgt u N (j + 1)) (xs u N (j + 1)) ≤
        u ^ 2 / 2 + u ^ 3 / 2 := by
      have hsq := resid_new (u := u) hj hjN
      have : 0 ≤ ov u N (j + 1) := (by positivity : (0 : ℝ) ≤ 3 / 4 * (u ^ 3 / 2)).trans hov
      nlinarith [sq_nonneg (Constrained.targetResidual objF conC (tgt u N (j + 1))
        (xs u N (j + 1)) - (u ^ 2 / 2 + u ^ 3 / 2))]
    have hb : β * Constrained.targetResidual objF conC (tgt u N (j + 1)) (xs u N (j + 1)) ≤
        3 / 4 * (u ^ 2 / 2 + u ^ 3 / 2) := by
      rcases le_or_gt 0 β with h | h
      · calc _ ≤ β * (u ^ 2 / 2 + u ^ 3 / 2) := by gcongr
          _ ≤ _ := by gcongr
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg h.le hR0]
    have : β * Constrained.targetResidual objF conC (tgt u N (j + 1)) (xs u N (j + 1)) *
        (3 * u / 2) ≤ 3 / 4 * (u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2) := by
      gcongr
    have e : 3 / 4 * (u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2) =
        9 / 16 * u ^ 3 + 9 / 16 * u ^ 4 := by ring
    linarith

/-- `‖r(x_k, t_k)‖ ≤ u²/2 + u³/2 = ε₀` for `k ∈ [1, N]`. -/
theorem resid_cur_le {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Constrained.targetResidual objF conC (tgt u N k) (xs u N k) ≤ u ^ 2 / 2 + u ^ 3 / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Constrained.targetResidual_def, xs_one, norm_conC, tgt_one, objF_pt]
    simp only [pt_zero]
    rw [show ((0 : ℝ) ^ 2 / 2) ^ 2 + (0 - -1 - (1 - (u ^ 2 / 2 + u ^ 3 / 2))) ^ 2 =
      (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  · have hjN : j < N := by omega
    have hov := le_ov hu (N := N) (j := j + 1) (by omega)
    have hov1 := ov_le hu (N := N) (j + 1)
    have hsq := resid_new (u := u) hj hjN
    have hR0 := Constrained.targetResidual_nonneg (f := objF) (c := conC)
      (t := tgt u N (j + 1)) (x := xs u N (j + 1))
    have : 0 ≤ ov u N (j + 1) := (by positivity : (0 : ℝ) ≤ 3 / 4 * (u ^ 3 / 2)).trans hov
    nlinarith [sq_nonneg (Constrained.targetResidual objF conC (tgt u N (j + 1))
      (xs u N (j + 1)) - (u ^ 2 / 2 + u ^ 3 / 2)), pow_pos hu 2, pow_pos hu 3]

include hu7 in
/-- **The cost bounds (14.3.20)–(14.3.21) hold for every call** `k ∈ [1, N]`: for `β ∈ (0, 3/4]`,
`κ ≥ 8` and `π₁ ≥ 4/3`, the bound `κ (μ(x_k, t_k) - 0) (β ‖r(x_k, t_k)‖ ε₁)^{-π₁}` of a call of
INNER on `μ(·, t_k)` from `x^S = x_k` with tolerance `β ‖r(x_k, t_k)‖ ε₁` (and `f_low = 0`, the
lower bound of `μ`) is at least `2`. With `R = ‖r(x_k, t_k)‖ ≥ u²/2` and `w = β R ε₁`, one has
`w ≤ 1` and `w⁴ ≤ (2R²)³`, so `w^{π₁} ≤ w^{4/3} ≤ 2R²` and the bound is `≥ κ/4`. -/
theorem two_le_innerEvalBound {β : ℝ} (hβ : 0 < β) (hβθ : β ≤ 3 / 4) {κ : ℝ} (hκ : 8 ≤ κ)
    {π : ℕ → ℝ} (hπ : 4 / 3 ≤ π 1) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    2 ≤ innerEvalBound κ π 1 (Constrained.targetMerit objF conC (tgt u N k) (xs u N k))
      (fun j => β * Constrained.targetResidual objF conC (tgt u N k) (xs u N k) * eps u j) := by
  rw [innerEvalBound_one]
  simp only [Constrained.targetMerit_eq, eps_one]
  set R := Constrained.targetResidual objF conC (tgt u N k) (xs u N k) with hR_def
  have hRlo := resid_cur_ge hu hk1 hkN
  have hRhi := resid_cur_le hu hk1 hkN
  have hR : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  have hu2 : u ^ 2 ≤ 2 * R := by linarith
  set w := β * R * (3 * u / 2) with hw_def
  have hw0 : 0 < w := by positivity
  have hwle : w ≤ 9 / 8 * R * u := by
    rw [hw_def]
    have : β * R ≤ 3 / 4 * R := by gcongr
    nlinarith
  have hw1 : w ≤ 1 := by
    have : R ≤ 1 := by nlinarith [pow_pos hu 2, pow_pos hu 3]
    nlinarith
  have hw4 : w ^ 4 ≤ (2 * R ^ 2) ^ 3 := by
    calc w ^ 4 ≤ (9 / 8 * R * u) ^ 4 := by gcongr
      _ = (9 / 8) ^ 4 * R ^ 4 * (u ^ 2) ^ 2 := by ring
      _ ≤ (9 / 8) ^ 4 * R ^ 4 * (2 * R) ^ 2 := by gcongr
      _ ≤ (2 * R ^ 2) ^ 3 := by nlinarith [pow_pos hR 6]
  have hw43 : w ^ (4 / 3 : ℝ) ≤ 2 * R ^ 2 := by
    have e : w ^ (4 / 3 : ℝ) = (w ^ (4 : ℕ)) ^ (((3 : ℕ) : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le]; norm_num
    rw [e, ← Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ 2 * R ^ 2) (by norm_num : 3 ≠ 0)]
    exact Real.rpow_le_rpow (by positivity) hw4 (by positivity)
  have hwπ : w ^ π 1 ≤ 2 * R ^ 2 := (Real.rpow_le_rpow_of_exponent_ge hw0 hw1 hπ).trans hw43
  have hwπ0 : 0 < w ^ π 1 := Real.rpow_pos_of_pos hw0 _
  rw [Real.rpow_neg hw0.le, ← div_eq_mul_inv, le_div_iff₀ hwπ0]
  nlinarith [sq_nonneg R]

end Run2

/-- Every INNER call makes one successful iteration. -/
theorem succCount_run (u : ℝ) (N j : ℕ) : (run u N).succCount j = 1 := by
  classical
  unfold TPqpSeq.succCount
  rw [Finset.card_eq_one]
  refine ⟨0, Finset.eq_singleton_iff_unique_mem.2
    ⟨Finset.mem_filter.2 ⟨by simp [run], trivial⟩, fun x hx => ?_⟩⟩
  have := (Finset.mem_filter.1 hx).1
  simpa [run] using this

/-- Every INNER call makes one (successful) iteration: `#F(k) = #D(k) = k + 1`. -/
theorem funEvals_run (u : ℝ) (N k : ℕ) : (run u N).funEvals k = k + 1 ∧
    (run u N).derivEvals k = k + 1 := by
  have hs : ∀ j, (run u N).succCount j = 1 := succCount_run u N
  constructor
  · unfold TPqpSeq.funEvals
    simp [run, add_comm]
  · unfold TPqpSeq.derivEvals
    simp [hs, add_comm]

/-! #### The data -/

/-- `X` is closed. -/
theorem isClosed_boxX : IsClosed boxX :=
  (isClosed_le (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2)).continuous)
    continuous_const).inter
  (isClosed_le (continuous_abs.comp (EuclideanSpace.proj (1 : Fin 2)).continuous)
    continuous_const)

/-- `X` is convex. -/
theorem convex_boxX : Convex ℝ boxX := by
  have e : boxX = (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ) ⁻¹' Icc (-1) 1 ∩
      (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ) ⁻¹' Icc (-1) 1 := by
    ext x; simp [boxX, abs_le]
  rw [e]
  exact ((convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap).inter
    ((convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap)

/-- `X ⊆ B(0, 2)`. -/
theorem boxX_subset_ball : boxX ⊆ ball 0 2 := by
  intro x hx
  obtain ⟨h0, h1⟩ := hx
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_lt' (by norm_num)]
  simp only [Real.norm_eq_abs, sq_abs]
  have := abs_le.1 h0
  have := abs_le.1 h1
  nlinarith

/-- `f` is smooth. -/
theorem contDiff_objF : ContDiff ℝ ⊤ objF :=
  (contDiff_piLp_apply (p := 2)).sub (contDiff_piLp_apply (p := 2))

/-- `c` is smooth. -/
theorem contDiff_conC : ContDiff ℝ ⊤ conC := by
  have h : ContDiff ℝ ⊤ (fun x : ℝ² => x 0 ^ 2 / 2) :=
    ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))).pow 2).div_const 2
  exact h.smul contDiff_const

/-- `‖∇f‖ ≤ 2`. -/
theorem deriv_objF_le (y : ℝ²) : ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i objF y‖ ≤ 2 := by
  intro i hi
  obtain rfl : i = 1 := by simpa using hi
  rw [norm_iteratedFDeriv_one, (hasFDerivAt_objF y).fderiv]
  refine (norm_sub_le _ _).trans ?_
  have h : ∀ j : Fin 2, ‖(EuclideanSpace.proj j : ℝ² →L[ℝ] ℝ)‖ ≤ 1 := fun j =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa using PiLp.norm_apply_le x j
  linarith [h 0, h 1]

/-- f.B.Fb on `ℱ_1`: `-2 ≤ f ≤ 2` on `X`. -/
theorem assumptionBFb : Chapter07.AssumptionBFb objF conC boxX 1 (-2) 2 := by
  intro x hx
  obtain ⟨⟨h0, h1⟩, -⟩ := hx
  have := abs_le.1 h0
  have := abs_le.1 h1
  simp only [objF]
  constructor <;> linarith

/-- f.D1pLB.X and c.D1pLB.X hold on `X₀ = B(0, 2)` for every `p`. -/
theorem assumptionD1pLBX (p : ℕ) :
    (∃ L B : ℕ → ℝ, AssumptionD1pLBX objF boxX (ball 0 2) p L B) ∧
      ∃ L B : ℕ → ℝ, AssumptionCD1pLBX conC boxX (ball 0 2) p L B := by
  refine ⟨exists_assumptionD1pLBX_ball (contDiff_objF.of_le le_top) boxX_subset_ball p, ?_⟩
  have hc0 : ContDiff ℝ ∞ (fun x => conC x 0) :=
    ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 1))).comp contDiff_conC).of_le le_top
  obtain ⟨L, B, h⟩ := exists_assumptionD1pLBX_ball hc0 boxX_subset_ball p
  exact ⟨L, B, isOpen_ball, convex_ball 0 2, boxX_subset_ball, fun i => by
    rw [Subsingleton.elim i 0]; exact h⟩

/-! #### The order -/

/-- With `u = 1/m`, `m ≥ 7`, and `π ≤ 3/2`, the book's order
`max(ε₀^{-1}, ε₀^{1-π} ε₁^{-π})` is at most `2 m² √m`. -/
theorem order_le {m : ℕ} (hm : 7 ≤ m) {π : ℝ} (hπ : π ≤ 3 / 2) :
    max (eps (1 / m) 0)⁻¹ (eps (1 / m) 0 ^ (1 - π) * eps (1 / m) 1 ^ (-π)) ≤
      2 * (m : ℝ) ^ 2 * √m := by
  have hm1 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set u : ℝ := 1 / m with hu_def
  have hu : 0 < u := by positivity
  have hum : u * m = 1 := by rw [hu_def]; field_simp
  rw [eps_zero, eps_one]
  set e0 := u ^ 2 / 2 + u ^ 3 / 2 with he0
  have he0pos : 0 < e0 := by positivity
  have he0inv : e0⁻¹ ≤ 2 * (m : ℝ) ^ 2 := by
    rw [inv_le_comm₀ he0pos (by positivity)]
    have : (2 * (m : ℝ) ^ 2)⁻¹ = u ^ 2 / 2 := by rw [hu_def]; field_simp
    rw [this]
    have : 0 < u ^ 3 := by positivity
    linarith
  have he0le : e0 ≤ 1 := by
    have : u ≤ 1 / 7 := by
      rw [hu_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
    nlinarith [pow_pos hu 2, pow_pos hu 3]
  have hsq1 : 1 ≤ √(m : ℝ) := by rw [Real.one_le_sqrt]; linarith
  -- `ε₀^{1-π} ≤ 2m`
  have hA : e0 ^ (1 - π) ≤ 2 * m := by
    rcases le_or_gt π 1 with h1 | h1
    · exact (Real.rpow_le_one he0pos.le he0le (by linarith)).trans (by linarith)
    · have hinv1 : 1 ≤ e0⁻¹ := one_le_inv_iff₀.2 ⟨he0pos, he0le⟩
      rw [show 1 - π = -(π - 1) by ring, Real.rpow_neg he0pos.le, ← Real.inv_rpow he0pos.le]
      calc e0⁻¹ ^ (π - 1) ≤ e0⁻¹ ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hinv1 (by linarith)
        _ = √(e0⁻¹) := (Real.sqrt_eq_rpow _).symm
        _ ≤ √((2 * m) ^ 2) := Real.sqrt_le_sqrt (he0inv.trans (by nlinarith))
        _ = 2 * m := Real.sqrt_sq (by positivity)
  -- `ε₁^{-π} ≤ m √m`
  have hB : (3 * u / 2) ^ (-π) ≤ m * √m := by
    have h3 : (3 * u / 2)⁻¹ = 2 * m / 3 := by rw [hu_def]; field_simp
    have h31 : 1 ≤ 2 * (m : ℝ) / 3 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), h3]
    calc (2 * (m : ℝ) / 3) ^ π ≤ (2 * m / 3) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h31 hπ
      _ ≤ (m : ℝ) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = m * √m := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm0, Real.rpow_one,
            ← Real.sqrt_eq_rpow]
  refine max_le (he0inv.trans (le_mul_of_one_le_right (by positivity) hsq1)) ?_
  calc e0 ^ (1 - π) * (3 * u / 2) ^ (-π) ≤ (2 * m) * (m * √m) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = 2 * (m : ℝ) ^ 2 * √m := by ring

/-- For `m > 4C²`, `C · 2 m² √m < m³`. -/
theorem lt_cube {m : ℕ} {C : ℝ} (hm : 7 ≤ m) (hC : 4 * C ^ 2 < m) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 2 * (m : ℝ) ^ 2 * √m) : C * x < ((m ^ 3 : ℕ) : ℝ) := by
  have hm7 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  push_cast
  rcases le_or_gt C 0 with h | h
  · nlinarith [pow_pos hm0 3, mul_nonpos_of_nonpos_of_nonneg h hx0]
  · have hs : 2 * C < √m := by
      rw [Real.lt_sqrt (by positivity)]; nlinarith
    have hsq : √(m : ℝ) * √m = m := Real.mul_self_sqrt hm0.le
    calc C * x ≤ C * (2 * (m : ℝ) ^ 2 * √m) := by gcongr
      _ = (2 * C) * √m * m ^ 2 := by ring
      _ < √m * √m * m ^ 2 := by
          have : 0 < √(m : ℝ) := Real.sqrt_pos.2 hm0
          gcongr
      _ = (m : ℝ) ^ 3 := by rw [hsq]; ring

/-! #### Phase 1 -/

/-- Phase 1 (LENq-SC on `ν`) stops at once at the feasible `x₀ = (0, -1)`. -/
theorem algorithm_14_3_2_run {u : ℝ} {N : ℕ} (hu : 0 < u) (hu7 : u ≤ 1 / 7)
    (hNu : u ^ 3 * N ≤ 1) (hN : 1 ≤ N) {β₁ β : ℝ} (hβ₁ : 0 < β₁) (hβ₁1 : β₁ < 1)
    (hβ : 0 < β) (hβθ : β ≤ 3 / 4) :
    algorithm_14_3_2 objF conC boxX 1 (3 / 4) β₁ β (eps u) (pt 0 (-1)) (fun _ => pt 0 (-1))
      (fun _ _ => 1) 0 (run u N) := by
  have hc1 : ‖conC (pt 0 (-1))‖ = 0 := by rw [norm_conC]; simp
  have hlen0 : lenStop conC boxX 1 (phase1Tol (3 / 4) (eps u)) (fun _ => pt 0 (-1))
      (fun _ _ => 1) 0 := Or.inl (by
        rw [hc1, phase1Tol_zero]; exact (mul_pos (by norm_num) (eps_pos hu 0)).le)
  have hmem : pt 0 (-1) ∈ boxX := by simp [boxX]
  refine ⟨rfl, ⟨hmem, fun j _ => ?_, fun j _ => ?_, hβ₁, hβ₁1, by rw [hc1]; norm_num,
    fun k _ h => absurd hlen0 (h 0 (by omega)), fun k _ h => absurd hlen0 (h 0 (by omega)),
    fun k _ h => absurd hlen0 (h 0 (by omega))⟩,
    ⟨hlen0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
    fun _ => isTPqpGCPhase2 hu hu7 hNu hN hβ hβθ⟩
  · unfold phase1Tol; split_ifs
    · exact mul_pos (by norm_num) (eps_pos hu 0)
    · exact eps_pos hu j
  · unfold phase1Tol; split_ifs
    · nlinarith [eps_le_one hu hu7 0, eps_pos hu 0]
    · exact eps_le_one hu hu7 j

/-- **The parameters for a constant `C`**: `u = 1/m`, `N = m³` with `m = ⌈4C²⌉ + 7`, so that
the tolerances vanish as `C` grows and `N > C max(ε₀^{-1}, ε₀^{1-π} ε₁^{-π})` for `π ≤ 3/2`. -/
theorem exists_params (C : ℝ) : ∃ (u : ℝ) (N : ℕ), 0 < u ∧ u ≤ 1 / 7 ∧ u ^ 3 * N ≤ 1 ∧ 1 ≤ N ∧
    (1 ≤ C → eps u 0 ≤ C⁻¹ ∧ eps u 1 ≤ C⁻¹) ∧
    ∀ π : ℝ, π ≤ 3 / 2 → C * max (eps u 0)⁻¹ (eps u 0 ^ (1 - π) * eps u 1 ^ (-π)) < N := by
  set m : ℕ := ⌈4 * C ^ 2⌉₊ + 7 with hm_def
  have hm : 7 ≤ m := by omega
  have hm7 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by linarith
  have hC : 4 * C ^ 2 < m := by
    have := Nat.le_ceil (4 * C ^ 2)
    rw [hm_def]; push_cast; linarith
  set u : ℝ := 1 / m with hu_def
  have hu : 0 < u := by positivity
  have hu7 : u ≤ 1 / 7 := by rw [hu_def, div_le_div_iff₀ hmR (by norm_num)]; linarith
  refine ⟨u, m ^ 3, hu, hu7, ?_, Nat.one_le_pow _ _ (by omega), fun hC1 => ?_, fun π hπ => ?_⟩
  · rw [hu_def]; push_cast; field_simp; exact le_rfl
  · have hmC : 2 * C ≤ m := by nlinarith
    have hε1 : eps u 1 ≤ C⁻¹ := by
      rw [eps_one, hu_def, le_inv_comm₀ (by positivity) (by linarith)]
      rw [show (3 * (1 / (m : ℝ)) / 2)⁻¹ = 2 * m / 3 by field_simp]
      linarith
    refine ⟨le_trans ?_ hε1, hε1⟩
    rw [eps_zero, eps_one]
    nlinarith [pow_pos hu 2, pow_pos hu 3]
  · have hx0 : 0 ≤ max (eps u 0)⁻¹ (eps u 0 ^ (1 - π) * eps u 1 ^ (-π)) :=
      (inv_pos.2 (eps_pos hu 0)).le.trans (le_max_left _ _)
    exact lt_cube hm hC hx0 (order_le hm hπ)

end Theorem1439OrderCex

open Theorem1439OrderCex in
/-- **The bad outer iterations of TPqp-GC are not bounded in the order of Theorem 14.3.9 by the
INNER contract** ([cartis2022evaluation], Theorem 14.3.9, with the exponents `π₁ ≤ 3/2`, in
particular the ARqp-SC exponent `π₁ = (p+1)/p` for `q = 1`, `p ≥ 2`, `arqpPiOf_one_le`).
There is one problem (`n = 2`, `m = 1`, `q = 1`) satisfying the book's assumptions — X.CNe
(`AssumptionXCNe`), `X` also convex and bounded; `f`, `c` polynomial, hence f.D1pLB.X and
c.D1pLB.X on `X₀ = B(0, 2)` for every `p`, `‖∇f‖ ≤ 2`; f.B.Fb on `ℱ_1` — such that for every
constant `C` there are tolerances `ε₀, ε₁ ∈ (0, 1]` and a TPqp-GC run (`algorithm_14_3_2` with
`θ = 3/4`, every `β ∈ [2/3, θ]`,
every Phase-1 constant `β₁`; Phase 2 entered at the feasible `x₀`, radii `1`) whose Phase-2
INNER calls satisfy the INNER contract keyed on INNER's own test (`IsInnerPhaseRunStrong`, the
form of Lemmas 14.2.2–14.2.3 that genuine INNER runs satisfy, for every `κ_decr`, every
exponents `π`, `κ_uns + κ_unc ≥ 1` and radii `ρ₁ ≤ 1`), which terminates at an outer iteration
`k_ε` with `#F = #D = k_ε + 1` evaluations, where
`k_ε > C max(ε₀^{-1}, ε₀^{1-π} ε₁^{-π})` for every `π ≤ 3/2`; the tolerances vanish as `C`
grows (`ε₀, ε₁ ≤ C⁻¹` for `C ≥ 1`). Every outer iteration `k ∈ [1, k_ε)` is a case-(b)
iteration whose call ends at a point passing INNER's test. The `decrease` field of the contract is
thus vacuous on this run (each call is one step after which INNER's test holds, the step
Lemma 14.2.2 exempts), while INNER's test fails at the start `(x_k, t_k)` of every call
(`not_innerTest_start`), so a genuine INNER must move in every call: the run exercises exactly the
exemption on which the book's proof of Lemma 14.3.8 rests.

So the evaluation bound `O(max(ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}))` of Theorem 14.3.9 cannot
be derived from the INNER contract with the ARqp-SC exponents (the book's proof uses nothing else
about INNER); the extra term `O(ε₀^{-1} + (ε₀ ε₁)^{-1})` of
`IsTPqpGCPhase2.complexity_of_strong` is attained in order (here `k_ε = m³` with
`ε₀ ε₁ ∼ 3/(4 m³)`). The INNER calls are given by their iterates, as the contract describes
them; they are not shown to be runs of ARqp-SC (whose model steps would not overshoot the
target along the level lines of `ν`).

The data: `X = [-1, 1]²`, `f(x) = x₁ - x₂`, `c(x) = x₁²/2`; for `m ≥ 7` (here
`m = ⌈4C²⌉ + 7`), `u = 1/m`, `ε₀ = u²/2 + u³/2`, `ε₁ = 3u/2`, `N = m³`. Phase 2 starts at
`x₁ = (0, -1)` with `t₁ = 1 - ε₀`; the `k`-th INNER call makes one successful iteration to
`x_{k+1} = (u, ·)` with `f(x_{k+1}) = t_k - E_{k+1}`, `E_j = (u³/2)(1 - j/(4(N + 1))) ∈
[3u³/8, u³/2]`, for `k < N`. At `x_{k+1}` the gradient `∇μ(x_{k+1}, t_k) = (u³/2 - E_{k+1},
E_{k+1})` has norm at most `u³/2 ≤ β ‖r(x_k, t_k)‖ ε₁` (INNER's test, using
`‖r(x_k, t_k)‖ ≥ u²/2`), while after the reflection (14.3.35) the decrease along `-e₁` is
`u³/2 + E_{k+1} ≥ 7u³/8 > ε₁ ‖r(x_{k+1}, t_{k+1})‖` ((14.3.34) fails). The targets drop by
`2E_{k+1} ≈ u³`, so `N ≈ 1/u³` such iterations fit in `X`; the last call lands on its target,
`f(x_{N+1}) = t_N`, where the third test of (14.3.32) holds (case (c)), and Phase 2 stops. The
merit `μ(·, t_k)` decreases strictly along every call. -/
theorem theorem_14_3_9_order_counterexample :
    ∃ (f : ℝ² → ℝ) (c : ℝ² → ℝ¹) (X : Set ℝ²),
      AssumptionXCNe X ∧ Convex ℝ X ∧ ContDiff ℝ ⊤ f ∧ ContDiff ℝ ⊤ c ∧
      (∀ p : ℕ, (∃ L B : ℕ → ℝ, AssumptionD1pLBX f X (ball 0 2) p L B) ∧
        ∃ L B : ℕ → ℝ, AssumptionCD1pLBX c X (ball 0 2) p L B) ∧
      (∀ y, ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i f y‖ ≤ 2) ∧
      Chapter07.AssumptionBFb f c X 1 (-2) 2 ∧
      ∀ C : ℝ, ∃ (ε : ℕ → ℝ) (x₀ : ℝ²) (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (D : TPqpSeq 2)
        (kε : ℕ),
        (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧ (1 ≤ C → ε 0 ≤ C⁻¹ ∧ ε 1 ≤ C⁻¹) ∧
        ‖c (xP 0)‖ = 0 ∧ (∀ k j, D.δ k j = 1) ∧
        D.IsEnd f c X 1 (3 / 4) ε kε ∧ D.funEvals kε = kε + 1 ∧ D.derivEvals kε = kε + 1 ∧
        (∀ k ∈ Finset.Icc 1 kε, Constrained.targetMerit f c (D.t k) (D.x (k + 1)) <
          Constrained.targetMerit f c (D.t k) (D.x k)) ∧
        (∀ π : ℝ, π ≤ 3 / 2 → C * max (ε 0)⁻¹ (ε 0 ^ (1 - π) * ε 1 ^ (-π)) < kε) ∧
        ∀ β₁ β : ℝ, 0 < β₁ → β₁ < 1 → 2 / 3 ≤ β → β ≤ 3 / 4 →
          algorithm_14_3_2 f c X 1 (3 / 4) β₁ β ε x₀ xP δP 0 D ∧
          (∀ (κdecr κuns κunc : ℝ) (π ρ : ℕ → ℝ), 1 ≤ κuns + κunc → ρ 1 ≤ 1 →
            IsInnerPhaseRunStrong f c X 1 (3 / 4) β ε D κdecr κuns κunc π ρ) ∧
          (∀ k ∈ Finset.Ico 1 kε, D.IsKb f c (3 / 4) ε k ∧ D.InnerTest f c X 1 β ε k) ∧
          ∀ k ∈ Finset.Icc 1 kε,
            β * Constrained.targetResidual f c (D.t k) (D.x k) * ε 1 <
              Optimization.taylorMeasure
                (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.x k)) 1 1
                {d | D.x k + d ∈ X} := by
  refine ⟨objF, conC, boxX, ⟨isClosed_boxX, ⟨pt 0 (-1), by simp [boxX]⟩⟩, convex_boxX,
    contDiff_objF, contDiff_conC, assumptionD1pLBX, deriv_objF_le, assumptionBFb, fun C => ?_⟩
  obtain ⟨u, N, hu, hu7, hNu, hN, hCε, hord⟩ := exists_params C
  have hc0 : ‖conC (pt 0 (-1))‖ = 0 := by rw [norm_conC]; simp
  refine ⟨eps u, pt 0 (-1), fun _ => pt 0 (-1), fun _ _ => 1, run u N, N,
    fun j => ⟨eps_pos hu j, eps_le_one hu hu7 j⟩, hCε, hc0, fun _ _ => rfl,
    isEnd hu hu7 hNu hN, (funEvals_run u _ _).1, (funEvals_run u _ _).2,
    fun k hk => merit_lt hu (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2, hord,
    fun β₁ β hβ₁ hβ₁1 hβ hβθ => ⟨algorithm_14_3_2_run hu hu7 hNu hN hβ₁ hβ₁1
      (by linarith) hβθ, fun κdecr κuns κunc π ρ hκ hρ =>
        isInnerPhaseRunStrong hu hu7 hNu hN hβ hκ hρ, fun k hk => ?_, fun k hk =>
        not_innerTest_start hu hu7 hNu hβθ (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2⟩⟩
  obtain ⟨hk1, hkN⟩ := Finset.mem_Ico.1 hk
  exact ⟨isKb hu hu7 hk1 hkN, innerTest hu hu7 hNu hβ hk1 hkN.le⟩

open Theorem1439OrderCex in
/-- **Theorem 14.3.9 of [cartis2022evaluation] fails for a nonspecific INNER under the per-call
reading of its INNER hypotheses** (they are checked on the INNER calls of the run; read uniformly
over all admissible inputs, the cost hypothesis cannot be met here for `π₁ < 2`, see
`theorem_14_3_9_cost_hypothesis_unsatisfiable`, and the theorem is vacuous under that reading).
There is a problem (`n = 2`, `m = 1`, `q = 1`, `X = [-1, 1]²`, `f(x) = x₁ - x₂`,
`c(x) = x₁²/2`) satisfying the book's assumptions of the theorem — X.CNe (`AssumptionXCNe`, `X`
also convex), f.D1pLB.X and c.D1pLB.X on `X₀ = B(0, 2)` for every `p`, and f.B.Fb on `ℱ_1` with
`f_low = -2`, `f_up = 2` — such that for all exponents `π₁ ∈ [4/3, 3/2]` (which contains the
ARqp-SC exponent `(p+1)/p` of (14.2.12) for `p ∈ {2, 3}`, `arqpPiOf_one_le`,
`four_thirds_le_arqpPiOf_one`), `θ = 3/4`, every
`β ∈ [2/3, θ]`, every Phase-1 constant `β₁ ∈ (0, 1)` and every choice of the constants
`κ^A_{INNER,2}`, `κ^C_{INNER,2}`, `κ^S_{INNER,2}`, `κ^{F,ν}_INNER`, `κ^{D,ν}_INNER` of the theorem,
there are tolerances `ε₀, ε₁ ∈ (0, 1]` and a TPqp-GC run (`algorithm_14_3_2`, Phase 2 entered at
the feasible `x₀`) terminating at `k_ε` (`TPqpSeq.IsEnd`) whose INNER calls satisfy every
hypothesis the book places on its nonspecific INNER:

* (14.3.19): each Phase-2 call `INNER(μ(·, t_k), X, 1, x_k, β ‖r(x_k, t_k)‖ ε)` returns
  `x_{k+1} ∈ X` with radius `δ = 1` passing INNER's own test (`TPqpSeq.InnerTest`);
* (14.3.20)–(14.3.21): its numbers of evaluations of `μ` (`e_k`) and of its derivatives
  (`succCount k`), even counting one more evaluation at `x^S = x_k`, are at most
  `κ_INNER (μ(x_k, t_k) - f_low) (β ‖r(x_k, t_k)‖ ε₁)^{-π₁}` with `f_low = 0` (the lower bound of
  `μ` the book suggests) and the `ε`-independent constants `κ^F_INNER = κ^D_INNER = κ` for every
  `κ ≥ 8`;
* (14.2.11) and (14.2.13) with constants independent of `t` (`IsInnerPhaseRunStrong`, the form of
  Lemmas 14.2.2–14.2.3 keyed on INNER's own test, for every `κ_decr`, `κ_uns + κ_unc ≥ 1`, radii
  `ρ₁ ≤ 1`);
* Phase 1 (LENq-SC) stops at `k₁ = 0` (`‖c(x₀)‖ = 0`) and makes no INNER call, so its INNER
  hypotheses hold vacuously;

and whose numbers of evaluations of `(f, c)` and of their derivatives exceed the printed bounds
`#^F_INNER,1 + #^F_INNER,2` and `#^D_INNER,1 + #^D_INNER,2`, with (14.3.65)–(14.3.66) for
Phase 1 (here `0`, as `‖c(x₀)‖ = 0`) and
`#^F_INNER,2 = (f_up - f_low - 1)(κ^A ε₀^{1-π₁} ε₁^{-π₁} + κ^C ε₀^{-1}) + 1`,
`#^D_INNER,2 = κ^S (f_up - f_low - 1) ε₀^{1-π₁} ε₁^{-π₁} + 1`.

The run is that of `theorem_14_3_9_order_counterexample`: its `k_ε ∼ (ε₀ ε₁)^{-1}` bad case-(b)
iterations each cost one evaluation, and the book's proof of Lemma 14.3.8 bounds them only
through decreases that Lemma 14.2.2 exempts at a step after which INNER's test holds. The
corrected statement is `IsTPqpGCPhase2.complexity_of_strong` (and the end-to-end
`exists_algorithm_14_3_2_complexity_strong`): the bound holds with an extra term
`O(ε₀^{-1} + (ε₀ ε₁)^{-1})`. The INNER calls are not runs of ARqp-SC (see the module doc):
they are not produced by a regularization algorithm of (14.2.12). Runs of ARqp-SC itself
exceed the printed order with `π₁ = (p+1)/p` (per-call reading) for `q = 1` and `p ≥ 4`
(`theorem_14_3_9_arqp_counterexample`, on a different problem) and for every `p ≥ 2`
(`theorem_14_3_9_arqp_counterexample_walk`) (for
`q = p`, and with the exponents `j + 1`, they attain it: `theorem_14_3_9_arqp`,
`theorem_14_3_9_arqpc`).

The construction needs `π₁ ≥ 4/3` for the cost bound: a call costs at least one evaluation while
`(μ(x_k, t_k)) (β ‖r‖ ε₁)^{-π₁} ∼ u^{4 - 3π₁}` (`‖r‖ ∼ u²`, `ε₁ ∼ u`), which tends to `0` for
`π₁ < 4/3`. The cost bound holds on the run for every `π₁ ≥ 4/3`; the upper limit `3/2` comes
only from the order comparison (`order_le`). -/
theorem theorem_14_3_9_false :
    ∃ (f : ℝ² → ℝ) (c : ℝ² → ℝ¹) (X : Set ℝ²) (flow fup : ℝ),
      AssumptionXCNe X ∧ Convex ℝ X ∧ ContDiff ℝ ⊤ f ∧ ContDiff ℝ ⊤ c ∧
      (∀ p : ℕ, (∃ L B : ℕ → ℝ, AssumptionD1pLBX f X (ball 0 2) p L B) ∧
        ∃ L B : ℕ → ℝ, AssumptionCD1pLBX c X (ball 0 2) p L B) ∧
      Chapter07.AssumptionBFb f c X 1 flow fup ∧
      ∀ (π : ℕ → ℝ), 4 / 3 ≤ π 1 → π 1 ≤ 3 / 2 →
      ∀ β₁ β : ℝ, 0 < β₁ → β₁ < 1 → 2 / 3 ≤ β → β ≤ 3 / 4 →
      ∀ κA κC κS κF₁ κD₁ : ℝ,
      ∃ (ε : ℕ → ℝ) (x₀ : ℝ²) (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (D : TPqpSeq 2) (kε : ℕ),
        (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧
        algorithm_14_3_2 f c X 1 (3 / 4) β₁ β ε x₀ xP δP 0 D ∧ ‖c x₀‖ = 0 ∧
        D.IsEnd f c X 1 (3 / 4) ε kε ∧
        -- (14.3.19) at the output of every Phase-2 call, radii `1`
        (∀ k ∈ Finset.Icc 1 kε, D.x (k + 1) ∈ X ∧ D.δ (k + 1) 1 = 1 ∧
          D.InnerTest f c X 1 β ε k) ∧
        -- (14.3.20)–(14.3.21) for every call, `f_low = 0`
        (∀ κ : ℝ, 8 ≤ κ → ∀ k ∈ Finset.Icc 1 kε,
          (D.e k : ℝ) + 1 ≤ innerEvalBound κ π 1 (Constrained.targetMerit f c (D.t k) (D.x k))
            (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) ∧
          (D.succCount k : ℝ) + 1 ≤
            innerEvalBound κ π 1 (Constrained.targetMerit f c (D.t k) (D.x k))
              (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j)) ∧
        -- (14.2.11), (14.2.13) with `t`-independent constants
        (∀ (κdecr κuns κunc : ℝ) (ρ : ℕ → ℝ), 1 ≤ κuns + κunc → ρ 1 ≤ 1 →
          IsInnerPhaseRunStrong f c X 1 (3 / 4) β ε D κdecr κuns κunc π ρ) ∧
        -- the printed bounds fail
        1 / 2 * κF₁ * ‖c x₀‖ * (β₁ ^ (1 - 2 * π 1) / (β₁ ^ (1 - π 1) - 1)) *
            (3 / 4 : ℝ) ^ (1 - π 1) * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) +
          ((fup - flow - 1) * (κA * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) + κC * (ε 0)⁻¹) + 1) <
            D.funEvals kε ∧
        1 / 2 * κD₁ * ‖c x₀‖ * (β₁ ^ (1 - 2 * π 1) / (β₁ ^ (1 - π 1) - 1)) *
            (3 / 4 : ℝ) ^ (1 - π 1) * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) +
          (κS * (fup - flow - 1) * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) + 1) <
            D.derivEvals kε := by
  refine ⟨objF, conC, boxX, -2, 2, ⟨isClosed_boxX, ⟨pt 0 (-1), by simp [boxX]⟩⟩, convex_boxX,
    contDiff_objF, contDiff_conC, assumptionD1pLBX, assumptionBFb,
    fun π hπ1 hπ2 β₁ β hβ₁ hβ₁1 hβ hβθ κA κC κS κF₁ κD₁ => ?_⟩
  obtain ⟨u, N, hu, hu7, hNu, hN, -, hord⟩ := exists_params (3 * (|κA| + |κC| + |κS|))
  have hc0 : ‖conC (pt 0 (-1))‖ = 0 := by rw [norm_conC]; simp
  have hβ0 : 0 < β := by linarith
  have hB := hord (π 1) hπ2
  set M := eps u 0 ^ (1 - π 1) * eps u 1 ^ (-π 1) with hM_def
  set E := (eps u 0)⁻¹ with hE_def
  have hM0 : 0 ≤ M := by have := eps_pos hu 0; have := eps_pos hu 1; positivity
  have hE0 : 0 ≤ E := (inv_pos.2 (eps_pos hu 0)).le
  have hMB : M ≤ max E M := le_max_right _ _
  have hEB : E ≤ max E M := le_max_left _ _
  have hA : κA * M ≤ |κA| * max E M :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hM0).trans
      (mul_le_mul_of_nonneg_left hMB (abs_nonneg _))
  have hC : κC * E ≤ |κC| * max E M :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hE0).trans
      (mul_le_mul_of_nonneg_left hEB (abs_nonneg _))
  have hS : κS * M ≤ |κS| * max E M :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hM0).trans
      (mul_le_mul_of_nonneg_left hMB (abs_nonneg _))
  have hB0 : 0 ≤ max E M := hE0.trans hEB
  have hAa := abs_nonneg κA
  have hCa := abs_nonneg κC
  have hSa := abs_nonneg κS
  refine ⟨eps u, pt 0 (-1), fun _ => pt 0 (-1), fun _ _ => 1, run u N, N,
    fun j => ⟨eps_pos hu j, eps_le_one hu hu7 j⟩,
    algorithm_14_3_2_run hu hu7 hNu hN hβ₁ hβ₁1 hβ0 hβθ, hc0, isEnd hu hu7 hNu hN,
    fun k hk => ?_, fun κ hκ k hk => ?_,
    fun κdecr κuns κunc ρ hκ hρ => isInnerPhaseRunStrong hu hu7 hNu hN hβ hκ hρ, ?_, ?_⟩
  · obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    exact ⟨xs_mem hu hu7 hNu (k := k + 1) (by omega) (by omega), rfl,
      innerTest hu hu7 hNu hβ hk1 hkN⟩
  · obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    have h2 := two_le_innerEvalBound hu hu7 hβ0 hβθ hκ hπ1 hk1 hkN (N := N)
    have he : ((run u N).e k : ℝ) = 1 := by simp [run]
    have hs : ((run u N).succCount k : ℝ) = 1 := by rw [succCount_run]; norm_num
    rw [he, hs]
    exact ⟨by norm_num; exact h2, by norm_num; exact h2⟩
  · rw [(funEvals_run u N N).1, hc0]
    push_cast
    nlinarith
  · rw [(funEvals_run u N N).2, hc0]
    push_cast
    nlinarith

open Theorem1439OrderCex in
/-- **The literal, uniform reading of the cost hypothesis (14.3.20)–(14.3.21) cannot be met on
the problem of `theorem_14_3_9_false` when `π₁ < 2`** ([cartis2022evaluation], §14.3,
(14.3.20)–(14.3.21) read as a bound, with one `ε`-independent `κ_INNER`, on the cost of every call
`INNER(μ(·, t), X, 1, x^S, β ‖r(x^S, t)‖ ε)` for all admissible tolerances). For every
`π₁ < 2`, `β ∈ (0, 1)` and `κ` there are admissible tolerances (`ε₁ = 1`, `ε₀ ∈ (0, 1]` small)
such that the first Phase-2 call (from `x^S = x₁ = (0, -1) ∈ X`, feasible, with the Step-0 target
`t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`) starts at a point failing INNER's test (14.3.19) for every
radius `δ ∈ (0, 1]` (the decrease along `-δ e₁` is `ε₀ δ > β ε₀ ε₁ δ`), so any INNER spends at
least one evaluation on it, while its bound `κ μ(x₁, t₁) (β ‖r(x₁, t₁)‖ ε₁)^{-π₁}
= (κ/2) β^{-π₁} ε₀^{2-π₁}` is below `1`. Under that reading no INNER (ARqp-SC included, compare
`exists_algorithm_14_3_1_cost_contract_counterexample`) satisfies the hypotheses of
Theorem 14.3.9 on this problem for `π₁ < 2`, and the printed theorem is vacuous there; under the
per-call reading (the hypotheses checked on the calls of the run) it is false for
`π₁ ∈ [4/3, 3/2]` (`theorem_14_3_9_false`). -/
theorem theorem_14_3_9_cost_hypothesis_unsatisfiable (π : ℕ → ℝ) (hπ : π 1 < 2) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (κ : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧ pt 0 (-1) ∈ boxX ∧ ‖conC (pt 0 (-1))‖ = 0 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        β * Constrained.targetResidual objF conC
            (objF (pt 0 (-1)) - √(ε 0 ^ 2 - ‖conC (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)) *
            ε 1 * δ ^ 1 / (1 : ℕ)! <
          Optimization.taylorMeasure
            (ftaylorSeries ℝ (Constrained.targetMerit objF conC
              (objF (pt 0 (-1)) - √(ε 0 ^ 2 - ‖conC (pt 0 (-1))‖ ^ 2))) (pt 0 (-1))) 1 δ
            {d | pt 0 (-1) + d ∈ boxX}) ∧
      innerEvalBound κ π 1
          (Constrained.targetMerit objF conC
            (objF (pt 0 (-1)) - √(ε 0 ^ 2 - ‖conC (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)))
          (fun j => β * Constrained.targetResidual objF conC
            (objF (pt 0 (-1)) - √(ε 0 ^ 2 - ‖conC (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)) * ε j) < 1 := by
  have hc0 : ‖conC (pt 0 (-1))‖ = 0 := by rw [norm_conC]; simp
  set a : ℝ := 2 - π 1 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set K : ℝ := |κ| / 2 * β ^ (-π 1) + 1 with hK_def
  have hK : 0 < K := by rw [hK_def]; positivity
  set e : ℝ := min 1 ((2 * K) ^ (-1 / a)) with he_def
  have he0 : 0 < e := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have he1 : e ≤ 1 := min_le_left _ _
  have hea : e ^ a ≤ (2 * K)⁻¹ := by
    calc e ^ a ≤ ((2 * K) ^ (-1 / a)) ^ a :=
          Real.rpow_le_rpow he0.le (min_le_right _ _) ha.le
      _ = (2 * K)⁻¹ := by
          rw [← Real.rpow_mul (by positivity), show -1 / a * a = -1 by field_simp,
            Real.rpow_neg_one]
  refine ⟨fun j => if j = 0 then e else 1, fun j => ?_, by simp [boxX], hc0, ?_⟩
  · dsimp only
    split_ifs
    · exact ⟨he0, he1⟩
    · exact ⟨one_pos, le_rfl⟩
  simp only [↓reduceIte, one_ne_zero, hc0]
  have ht : objF (pt 0 (-1)) - √(e ^ 2 - 0 ^ 2) = objF (pt 0 (-1)) - e := by
    rw [show e ^ 2 - (0 : ℝ) ^ 2 = e ^ 2 by ring, Real.sqrt_sq he0.le]
  rw [ht]
  have hR : Constrained.targetResidual objF conC (objF (pt 0 (-1)) - e) (pt 0 (-1)) = e := by
    rw [Constrained.targetResidual_def, hc0,
      show (0 : ℝ) ^ 2 + (objF (pt 0 (-1)) - (objF (pt 0 (-1)) - e)) ^ 2 = e ^ 2 by ring,
      Real.sqrt_sq he0.le]
  refine ⟨fun δ hδ hδ1 => ?_, ?_⟩
  · rw [hR]
    have hmem : EuclideanSpace.single (0 : Fin 2) (-δ) ∈
        closedBall (0 : ℝ²) δ ∩ {d | pt 0 (-1) + d ∈ boxX} := by
      refine ⟨by simp [abs_of_pos hδ], ?_⟩
      simp only [boxX, mem_ofPred_eq, PiLp.add_apply, pt_zero, pt_one]
      have e0 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 0 = -δ := by simp
      have e1 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 1 = 0 := by simp
      rw [e0, e1]
      exact ⟨by rw [abs_le]; constructor <;> linarith, by norm_num⟩
    have h := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit objF conC (objF (pt 0 (-1)) - e)) (pt 0 (-1))) 1
      hmem
    rw [decr] at h
    simp only [pt_zero] at h
    have e0 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 0 = -δ := by simp
    have e1 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 1 = 0 := by simp
    rw [e0, e1] at h
    refine lt_of_lt_of_le ?_ h
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, mul_one]
    have : β * e * δ < e * δ := by
      have := mul_pos he0 hδ
      nlinarith
    nlinarith
  · rw [innerEvalBound_one, Constrained.targetMerit_eq, hR]
    simp only [one_ne_zero, ↓reduceIte, mul_one]
    rw [Real.mul_rpow hβ.le he0.le]
    have hsplit : e ^ 2 / 2 * (β ^ (-π 1) * e ^ (-π 1)) = β ^ (-π 1) / 2 * e ^ a := by
      rw [ha_def, show 2 - π 1 = (2 : ℝ) + -π 1 by ring, Real.rpow_add he0,
        show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [mul_assoc, hsplit]
    have hb : 0 ≤ β ^ (-π 1) := (Real.rpow_pos_of_pos hβ _).le
    have hea0 : 0 ≤ e ^ a := (Real.rpow_pos_of_pos he0 _).le
    have h1 : κ * (β ^ (-π 1) / 2 * e ^ a) ≤ K * e ^ a := by
      rw [hK_def]
      have := le_abs_self κ
      nlinarith [mul_nonneg hb hea0, abs_nonneg κ]
    have h2 : K * e ^ a ≤ K * (2 * K)⁻¹ := mul_le_mul_of_nonneg_left hea hK.le
    have h3 : K * (2 * K)⁻¹ = 1 / 2 := by field_simp
    linarith

/-- The ARqp-SC exponent of order `1` ((14.2.12), either radii mode) is `(p+1)/p ≤ 3/2` for
`p ≥ 2`, so `theorem_14_3_9_order_counterexample` applies to it. -/
theorem arqpPiOf_one_le (unit : Prop) [Decidable unit] {p : ℕ} (hp : 2 ≤ p) :
    Chapter12.arqpPiOf unit p 1 ≤ 3 / 2 := by
  rw [arqpPiOf_one unit (by omega)]
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The ARqp-SC exponent of order `1` ((14.2.12), either radii mode) is `(p+1)/p ≥ 4/3` for
`1 ≤ p ≤ 3`; with `arqpPiOf_one_le` it lies in `[4/3, 3/2]` for `p ∈ {2, 3}`, the range of
`theorem_14_3_9_false`. -/
theorem four_thirds_le_arqpPiOf_one (unit : Prop) [Decidable unit] {p : ℕ} (hp1 : 1 ≤ p)
    (hp : p ≤ 3) : 4 / 3 ≤ Chapter12.arqpPiOf unit p 1 := by
  rw [arqpPiOf_one unit hp1]
  have h3 : (p : ℝ) ≤ 3 := by exact_mod_cast hp
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  rw [le_div_iff₀ (by linarith)]
  linarith

end CartisGouldToint.Chapter14
