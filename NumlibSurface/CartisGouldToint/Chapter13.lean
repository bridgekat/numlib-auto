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
  `AssumptionD0pL`); Lemmas 13.1.1–13.1.7, Theorem 13.1.8, Lemmas 13.1.9–13.1.18, Theorem
  13.1.19 (`theorem_13_1_19_i`, `theorem_13_1_19_ii`); existence of runs
  (`exists_algorithm_13_1_1`, `exists_algorithm_13_1_2`)
* §13.2, `Chapter13.Section02`: finite derivative-approximation schemes from low-degree oracles
  (`FiniteDerivativeApproxScheme`, with the forward-difference gradient and Hessian
  `fdGradientScheme`, `fdHessianScheme`); Theorem 13.2.1 (`theorem_13_2_1_i` for TRqIDA,
  `theorem_13_2_1_ii` for ARqpIDA)
* §13.3, `Chapter13.Section03`: TRqEDA (Algorithm 13.3.1, `algorithm_13_3_1`), ARqpEDA
  (Algorithm 13.3.2, `algorithm_13_3_2`); Lemmas 13.3.1–13.3.3, Theorem 13.3.4, Lemmas
  13.3.5–13.3.7, Theorem 13.3.8 (`theorem_13_3_8_i`, `theorem_13_3_8_ii`); existence of runs

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

* Algorithm 13.1.1, Step 0 prints the AR convention `0 < γ₁ < 1 < γ₂ < γ₃`; the trust-region
  update needs `0 < γ₁ ≤ γ₂ < 1 ≤ γ₃` (`TRqIDAParams` extends `Optimization.TRParams`). Step 4's
  shortcut back to Step 2 after an unsuccessful iteration is covered: every book run is a run of
  the predicate, which performs Step 1 at every iteration.
* Lemmas 13.1.1 and 13.1.9 need their radius (parameter) hypothesis at `Δ_{k+1}` (`σ_{k+1}`), not
  at `Δ_k` (`σ_k`); the printed statements are false for `k = 0`.
* Lemma 13.1.4 is proved for every lower bound of the trial measures, which contains both printed
  cases; the constant `κ_Δ` of (13.1.31) is used only through its properties (`IsTRKappaDelta`).
* **Evaluation counts.** The derivative-estimate bounds of Theorems 13.1.8, 13.1.19, 13.3.4 and
  13.3.8 omit the initial estimate and the last accuracy-improving iteration: `κ^F + 2` (TR) and
  `κ^F + 3` (AR, also counting the `+1` of `|𝒮_k| ≤ |𝒮_{k-1}| + 1`). In Theorem 13.1.19, `κ^C`
  misses the factor `1 + |log γ₁|/log γ₂` on that `+1`. The garbled constants of Theorem 13.3.4
  are replaced by the factor `2` of its proof (at most two value evaluations per trial
  iteration); the OCR-damaged exponents of (13.1.86) are restored from Lemma 13.1.18.
* Algorithm 13.1.2, Step 2 checks (13.1.46) only for `i ∈ [1, q]` and only for short steps; the
  proofs of Lemmas 13.1.14 and 13.1.16 need `i ∈ [1, p]` and long steps too. `ARqpDAStep` checks
  `i ∈ [1, p]`, and `σ_max` of Lemma 13.1.14 (and Lemma 13.3.5) uses `max(κ_s, κ_h)` for `κ_s`.
* Lemma 13.1.17 (`q > 2`): `κ_{δ,min}^{j-1}` is replaced by `κ̂^{j-1}`,
  `κ̂ = min(κ_{δ,min}, (1-θ)/(2 q! (L_{f,p} + σ_max + 3κ_{∇,max}κ_s)))`, which the book's
  derivation needs; Lemma 13.1.18 and Theorem 13.1.19 use `κ̂`. Lemma 13.1.18 holds (and is used)
  at successful iterations whose successor is not approximately optimal, not at every trial
  iteration.
* **Theorem 13.1.19**: the radius-one conclusion `φ^1_{f,j}(x_ε) ≤ ε_j/j!` is not what the proof
  gives (the radii certified at the end of Step 1 may be smaller than one; the proof conflates
  `δ^{(0)}_k` and `δ^{(1)}_k`). The first-hit index is that of approximate optimality for *some*
  radii in `(0, 1]^q`; for `q ≤ 2` the radius-one conclusion follows
  (`isEpsDeltaApprox_one_of_le_two`).
* Theorem 13.2.1, (13.2.5)–(13.2.7): `O(min_j ε_j^{-…})` must be `O(max_j ε_j^{-…})`.
* **ARqpEDA (Lemma 13.3.7, Theorem 13.3.8)**: the book reuses Lemmas 13.1.16–13.1.17, whose
  hypothesis "`x_{k+1}` is not approximately optimal" does not follow from non-termination of
  ARqpEDA. The corrected argument uses the inexact Step-1 test at `x_{k+1}` and needs
  `θ < ς/2`; `1 - θ` becomes `ς/2 - θ` and `3κ_{∇,max}κ_s` becomes `4κ_s` in the constants, and
  the successful iterations followed by an accuracy-improving one (logarithmically many) are
  added to the count. The orders in `ε` are unchanged.

## Not formalized

The general stencil claim (13.2.1) (unproved in the literature), the interpolation bound
(13.2.4) and the derivative-free discussion of §13.2; the `O(·)` restatements.
-/
