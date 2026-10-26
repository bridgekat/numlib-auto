import NumlibSurface.CartisGouldToint.Chapter12.Section01
import NumlibSurface.CartisGouldToint.Chapter12.Section02
import NumlibSurface.CartisGouldToint.Chapter12.Section03

/-!
# Cartis–Gould–Toint, Chapter 12: Finding High-Order Approximate Minimizers

Surface of [cartis2022evaluation] Chapter 12, the first chapter of Part II: necessary conditions of
arbitrary order and their limits, the Taylor-decrement measure
`φ^δ_{f,j}(x) = f(x) - min_{‖d‖≤δ} T_{f,j}(x, d)` (`Optimization.taylorMeasure`) and
`(ε, δ)`-approximate `q`-th order minimizers (12.1.25) (`Optimization.IsEpsDeltaApprox`), the
trust-region method TRq and the regularization method ARqp with their complexity and its sharpness,
and inexact global model minimization. This module imports the section modules and adds nothing of
its own.

* §12.1, `Chapter12.Section01`: curve-based conditions, `φ^δ_{f,j}`, (12.1.25); Examples
  12.1.1–12.1.4, Theorems 12.1.1–12.1.8
* §12.2, `Chapter12.Section02`: TRq (Algorithm 12.2.1), ARqp (Algorithms 12.2.2–12.2.3); Lemmas
  12.2.1–12.2.4, 12.2.7–12.2.13, Theorems 12.2.5–12.2.6, 12.2.14–12.2.15, 12.2.17, Corollary
  12.2.16, Examples 12.2.1–12.2.2
* §12.3, `Chapter12.Section03`: the relaxed Step 2 of ARqp (no numbered results)

TRq and ARqp are the backbone run predicates `Optimization.IsTRqRun`, `Optimization.IsARqpRun`
with exact data `ftaylorSeries ℝ f (x k)`; tolerances and radii are vectors `ε δ : ℕ → ℝ` indexed
by the order. `Chapter12.Section02` also states the feasible-set versions used by Chapter 14
(`algorithm_12_2_1_feasible`, `algorithm_12_2_2_feasible`). Appendix B's Lemma B.12.1 is in
`AppendixB.Chapter12`.

## Deviations from the book

* **Theorem 12.1.5 is false as printed** (`theorem_12_1_5_counterexample`): an isolated minimizer
  of `T_{f,j}(x, ·)` need not be uniformly isolated. `theorem_12_1_5` assumes growth of order `j`.
* Example 12.1.2: the printed `κ₁ = 1`, `κ₂ = 2` give no saddle; `κ₁ = 3` (the book's figure) is
  used. Example 12.1.3 (iv) holds in one variable only; the `n`-dimensional claim fails.
  Theorem 12.1.6 (ii) needs `C²` and gets an explicit `κ(x)`; the chain of tolerances after
  Theorem 12.1.7 is reversed.
* ARqp, Step 1: the printed `≥` is `>` (with `≥` the sharpness examples never stop); Step 2 may
  terminate only at a global model minimizer `0`, as Algorithm 12.2.3 guarantees.
* Theorem 12.2.6: the slow data of Appendix B are inconsistent (Taylor decrease vs. function
  decrease, `ε^{q+1} k_ε ≤ 1` false); corrected data are `Optimization.exists_slowTRq_interpolant`.
* Lemma 12.2.11: the factor `1 - θ` must be `ς - θ`, requiring `θ < ς`. Lemma 12.2.12 (`q > 2`):
  `κ_{δ,min}` must be replaced by `κ̂ = min(κ_{δ,min}, τ_q/2)`. Lemma 12.2.13 needs f.D1pL and holds
  at successful iterations followed by a non-terminating one.
* Theorem 12.2.15 for `q ≥ 3`: its hypothesis "`δ_{s_k,j} = 1` is possible" fails for its own
  example (`theorem_12_2_15_counterexample`); the theorem is stated for the global-step scenario
  `IsARqpGlobalStepRun`, a genuine ARqp run for `q ≤ 2` (`corollary_12_2_16`).
* Example 12.2.2: the factorization of `s²(s - ½)²` is misprinted; the radius threshold is `¼`.
* (12.3.1) is read with the decrease `ΔT_{f,p}` and `ε_min^ω`.

## Not formalized

The weak approximate minimizers (12.1.40), the relaxation (12.1.24), the `O(ε₂)` remark after
Theorem 12.1.6, the discussion of §12.1.6; the `O(·)` restatements and Table 12.2.1; the
qualitative discussion of §12.3.
-/
