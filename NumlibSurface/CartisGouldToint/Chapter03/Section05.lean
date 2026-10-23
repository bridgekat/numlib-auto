import Numlib.Optimization.SecondOrder.OracleMethod
import Numlib.Optimization.SecondOrder.QuadraticConvergence

/-!
# Cartis–Gould–Toint, Section 3.5: the second-order method class

The class consists of actual shifted Newton residual equations, accepted point
updates, PSD shifted Hessians and a least-eigenvalue upper bound. Lemma 3.5.1
corrects the self-reference in the printed coefficient: the radicand uses the
proportional-shift constant `B`, which is the source's barred kappa-lambda.
The step estimate uses the source's weaker reciprocal coefficient, valid because
the bracket is greater than one. Multipliers are nonnegative as in (3.5.3).
-/

namespace CartisGouldToint

/-- Accepted actual inexact shifted-Newton equations (3.5.1)–(3.5.2), with
nonnegative multipliers. No spectral estimate or convergence is assumed. -/
abbrev inexactSecondOrderTrace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x s r : ℕ → E)
    (ℓ : ℕ → ℝ) (κrg κrs : ℝ) (N : ℕ) : Prop :=
  ShiftedNewton.Trace f x s r ℓ κrg κrs N

/-- The second-order method class M, (3.5.1)–(3.5.4), on a finite accepted prefix.
The Hessian and gradient are actual derivatives and the least eigenpair is
certified by its actual eigenvector equation and all unit Rayleigh quotients. -/
abbrev secondOrderMethodClass {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x s r u : ℕ → E)
    (ℓ μ : ℕ → ℝ) (κrg κrs κℓ : ℝ) (N : ℕ) : Prop :=
  ShiftedNewton.MethodClass f x s r u ℓ μ κrg κrs κℓ N

/-- **Lemma 3.5.1.** The proportional multiplier bound (3.5.6) implies all of
(3.5.4) with coefficient `2*sqrt(B*(1+κrg))`. The source's self-reference in the
radicand is corrected to its given proportional-shift constant. -/
theorem lemma_3_5_1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {x s r u : ℕ → E}
    {ℓ μ : ℕ → ℝ} {κrg κrs B : ℝ} {N : ℕ}
    (h : inexactSecondOrderTrace f x s r ℓ κrg κrs N) (hB : 1 < B)
    (hs : ∀ i < N, s i ≠ 0)
    (he : ∀ i < N, SecondOrderTrustRegion.IsLeastEigenpair f (x i) (μ i) (u i))
    (hpsd : ∀ i < N, ShiftedNewton.ShiftedPSD f (x i) (ℓ i))
    (hℓ : ∀ i < N, ℓ i ≤ B * ‖s i‖) :
    secondOrderMethodClass f x s r u ℓ μ κrg κrs (2 * Real.sqrt (B * (1 + κrg))) N :=
  h.to_methodClass hB hs he hpsd hℓ

/-- **Lemma 3.5.2.** Actual Hessian Lipschitz continuity and (3.5.6) imply
(3.5.7) at every next accepted iterate. The coefficient is the printed reciprocal
of `L/2+κrs+B`; boundedness below and gradient Lipschitz continuity are unnecessary. -/
theorem lemma_3_5_2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {x s r : ℕ → E}
    {ℓ : ℕ → ℝ} {κrg κrs L B : ℝ} {N : ℕ}
    (h : inexactSecondOrderTrace f x s r ℓ κrg κrs N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L) (hB : 1 < B)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hℓ : ∀ i < N, ℓ i ≤ B * ‖s i‖) :
    ∀ i < N, (L / 2 + κrs + B)⁻¹ * Real.sqrt ‖gradient f (x (i + 1))‖ ≤ ‖s i‖ :=
  h.step_lower hf hL hB hlip hℓ

/-- **Lemma 3.5.3.** A bounded nonnegative multiplier and quadratic convergence
of actual gradient norms force (3.5.7), with the explicit positive coefficient
from the appendix. Nonnegativity is the method-class convention (3.5.3), needed
for the appendix's bound on the shifted Hessian norm. Boundedness below and
Hessian Lipschitz continuity are unnecessary for this implication. -/
theorem lemma_3_5_3 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {x s r : ℕ → E}
    {ℓ : ℕ → ℝ} {κrg κrs H B C : ℝ} {N : ℕ}
    (h : inexactSecondOrderTrace f x s r ℓ κrg κrs N)
    (hH : 0 ≤ H) (hB : 0 < B) (hC : 0 < C)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ H * ‖y - z‖)
    (hℓ : ∀ i < N, ℓ i ≤ B)
    (hnext : ∀ i < N, ‖gradient f (x (i + 1))‖ ≤ C * ‖gradient f (x i)‖ ^ 2) :
    0 < (1 - κrg) / ((H + B) * Real.sqrt C) ∧
      ∀ i < N, (1 - κrg) / ((H + B) * Real.sqrt C) *
        Real.sqrt ‖gradient f (x (i + 1))‖ ≤ ‖s i‖ :=
  h.step_lower_of_quadratic hH hB hC hlip hℓ hnext

/-- A scalar second-order method is an actual deterministic finite-oracle-history
controller, with its recursively defined execution initialized at zero. -/
abbrev secondOrderOracleMethod := ShiftedNewton.ScalarMethod

/-- The primitive scalar method class applies the actual residual, PSD and
spectral conditions to every nonterminated execution on the source objective
class. It assumes no progress, trajectory support, stopping time or complexity. -/
abbrev secondOrderOracleMethodClass := ShiftedNewton.IsScalarMethodClass

end CartisGouldToint
