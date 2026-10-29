import NumlibSurface.CartisGouldToint.Chapter13.Section01
import NumlibSurface.CartisGouldToint.Chapter13.Section02
import NumlibSurface.CartisGouldToint.Chapter13.Section03

/-!
# Cartis–Gould–Toint, Chapter 13: Inexact Function Values and Derivatives

Surface of [cartis2022evaluation] Chapter 13: the high-order methods of Chapter 12 with inexact
derivatives (and, in §13.3, inexact function values) whose accuracy the algorithm controls. The
trust-region method TRqIDA and the regularization method ARqpIDA use exact values and derivative
estimates within `κ_{∇,i} h_{k,i}` of the true ones, for constants `κ_{∇,i}` unknown to the
algorithm (*implicit dynamic accuracy*); their explicit-dynamic-accuracy variants TRqEDA and
ARqpEDA also use inexact values and certify termination. Both families keep the orders of
complexity of TRq and ARqp. This module imports the section modules and adds nothing of its own.

* §13.1, `Chapter13.Section01`: TRqIDA (Algorithm 13.1.1, `algorithm_13_1_1`), ARqpIDA
  (Algorithm 13.1.2, `algorithm_13_1_2`); assumptions f.D0qL, f.D0pL (`AssumptionD0qL`,
  `AssumptionD0pL`) and f.D0qL on an open convex set (`AssumptionD0qLOn`, used by §14.2);
  Lemmas 13.1.1–13.1.7, Theorem 13.1.8, Lemmas 13.1.9–13.1.18, Theorem 13.1.19
  (`theorem_13_1_19_i`, `theorem_13_1_19_ii`); existence of runs (`exists_algorithm_13_1_1`,
  `exists_algorithm_13_1_2`)
* §13.2, `Chapter13.Section02`: finite derivative-approximation schemes from low-degree oracles
  (`FiniteDerivativeApproxScheme`, with the forward-difference gradient and Hessian
  `fdGradientScheme`, `fdHessianScheme`); the stencil formulas (13.2.1) for derivative tensors
  (`eq_13_2_1`, `eq_13_2_1_ida`) and the corresponding scheme (`stencilScheme`); multivariate
  interpolation (13.2.2)–(13.2.4) (`eq_13_2_2_card`, `eq_13_2_4`, `eq_13_2_4_scaled`,
  `interpolationScheme`); Theorem 13.2.1 (`theorem_13_2_1_i` for TRqIDA, `theorem_13_2_1_ii` for
  ARqpIDA)
* §13.3, `Chapter13.Section03`: TRqEDA (Algorithm 13.3.1, `algorithm_13_3_1`), ARqpEDA
  (Algorithm 13.3.2, `algorithm_13_3_2`); Lemmas 13.3.1–13.3.3, Theorem 13.3.4, Lemmas
  13.3.5–13.3.7, Theorem 13.3.8 (`theorem_13_3_8_i`, `theorem_13_3_8_ii`); existence of runs

The analyses are those of the library (`Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy`):
the runs `Optimization.IsTRqIDARun`, `Optimization.IsARqpIDARun`, `Optimization.IsTRqEDARun`,
`Optimization.IsARqpEDARun` on a feasible set `X`, analysed under the anchored assumption
`LipschitzDerivsAnchored f C A 0 p L` with an anchor set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` (which contains the iterates). The book's results are their instances
with `X = C = A = univ`; the feasible-set rows of §14.2 are in `Chapter14.Section02`.

Inexact derivatives at iteration `k` form a jet `D k : FormalMultilinearSeries ℝ ℝⁿ ℝ`, with
decrements `(D k).taylorDecrement j` and measures `Optimization.taylorMeasure (D k) j δ univ`
(`\overline{φ}^δ_{f,j}`, (13.1.5)); the error model (13.1.2) is `Optimization.JetApprox`. One
iteration of the TR (resp. AR) methods is the step predicate `TRqDAStep` (resp. `ARqpDAStep`),
shared by the IDA and EDA runs; iterations are successful, unsuccessful or accuracy-improving
(the Prop `acc k`). The IDA methods have no termination rule: their complexity theorems bound
the evaluations made before the first iterate that is truly approximately optimal. Function
values are counted as `Optimization.derivEvalCount (¬ acc ·)` in IDA (initial value plus one per
trial iteration) and as `edaFunEvalCount` (at most two per trial iteration) in EDA; derivative
estimates as `derivEvalCount` of the successful and accuracy-improving iterations. Appendix B
contains only proofs for this chapter, so there is no `AppendixB.Chapter13`.

## Deviations from the book

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* Algorithm 13.1.1, Step 0: **typo**, the trust-region update needs `0 < γ₁ ≤ γ₂ < 1 ≤ γ₃`
  (`TRqIDAParams`); Step 4's shortcut is covered, as the run predicate performs Step 1 at every
  iteration (`algorithm_13_1_1`).
* Lemmas 13.1.1, 13.1.9: **false** for `k = 0`; the radius (parameter) hypothesis is at `Δ_{k+1}`
  (`σ_{k+1}`) (`lemma_13_1_1`, `lemma_13_1_9`).
* Lemma 13.1.4: **reading**, proved for every lower bound of the trial measures (both printed
  cases); `κ_Δ` of (13.1.31) enters only through its properties (`IsTRKappaDelta`)
  (`lemma_13_1_4`).
* Theorems 13.1.8, 13.1.19, 13.3.4, 13.3.8: **false** derivative-estimate counts, which omit the
  initial estimate and the last accuracy-improving iteration: `κ^F + 2` (TR), `κ^F + 3` (AR);
  in Theorem 13.1.19 `κ^C` misses the factor `1 + |log γ₁|/log γ₂` on that `+ 1`
  (`theorem_13_1_8`, `theorem_13_1_19_ii`, `theorem_13_3_4`, `theorem_13_3_8_ii`).
* Theorem 13.3.4: **typo**, garbled constants; the factor `2` of its proof (`theorem_13_3_4`).
* Algorithm 13.1.2, Step 2: **gap**, it checks (13.1.46) only for `i ∈ [1, q]` and short steps;
  Lemmas 13.1.14, 13.1.16 need `i ∈ [1, p]` and long steps (`ARqpDAStep`), and `σ_max` of
  Lemmas 13.1.14, 13.3.5 uses `max(κ_s, κ_h)` (`lemma_13_1_14`, `lemma_13_3_5`).
* Lemma 13.1.17 (`q > 2`): **gap**, `κ_{δ,min}^{j-1}` is replaced by `κ̂^{j-1}`,
  `κ̂ = min(κ_{δ,min}, (1-θ)/(2 q! (L_{f,p} + σ_max + 3κ_{∇,max}κ_s)))`, also in Lemma 13.1.18 and
  Theorem 13.1.19; Lemma 13.1.18 holds at successful iterations whose successor is not
  approximately optimal (`lemma_13_1_17`, `lemma_13_1_18`).
* Theorem 13.1.19: **gap**, the radius-one conclusion `φ^1_{f,j}(x_ε) ≤ ε_j/j!` is not what the
  proof gives (it conflates `δ^{(0)}_k` and `δ^{(1)}_k`); stated for some radii in `(0, 1]^q`
  (`theorem_13_1_19_i`), with radius one for `q ≤ 2` (`isEpsDeltaApprox_one_of_le_two`).
* (13.2.2): **typo**, `d = ∑_{i=0}^p C(n+i-1, i)` interpolation points, not `d + 1`
  (`eq_13_2_2_card`). Theorem 13.2.1, (13.2.5)–(13.2.7): **typo**, `O(min_j …)` is `O(max_j …)`
  (`theorem_13_2_1_i`, `theorem_13_2_1_ii`).
* Lemma 13.3.7, Theorem 13.3.8 (ARqpEDA): **gap**, the reused Lemmas 13.1.16–13.1.17 need
  "`x_{k+1}` is not approximately optimal", which does not follow from non-termination; the
  corrected argument uses the inexact Step-1 test at `x_{k+1}` and needs `θ < ς/2`, with
  `ς/2 - θ` for `1 - θ` and `4κ_s` for `3κ_{∇,max}κ_s` in the constants, and counts the successful
  iterations followed by an accuracy-improving one; the orders in `ε` are unchanged
  (`lemma_13_3_7`, `theorem_13_3_8_i`, `theorem_13_3_8_ii`).

## Not formalized

The derivative-free discussion of §13.2; the `O(·)` restatements.
-/
