import Numlib.Nonlinear.PowerTransform
import Numlib.Nonlinear.Scalar.Monotone

/-!
# Cartis–Gould–Toint, Appendix B.8: transformed secular Newton steps

Lemma B.8.2 is stated for every differentiable scalar function with positive value and
negative derivative at the current point. These are the properties of the nondegenerate
secular function needed by its proof; in the secular specialization the right-hand
side vector must be nonzero. A root or a position relative to it is unnecessary.
For nonzero exponent the residual is exactly `π^β - (Δ²)^β = π^β - Δ^(2β)`.
At exponent zero that residual is identically zero, so the logarithmic residual is used
instead. Its Newton step is the continuous extension of the steps at nonzero exponents.
-/

namespace CartisGouldToint

/-- All Newton and secant convergence conclusions of Lemma B.8.1: interval
invariance, increasing iterates, the explicit global Q-linear factor, convergence,
ultimate Q-superlinear error ratios, and the conditional Q-quadratic Newton bound.
These use the actual Newton and secant updates, fixed at a root after termination. -/
abbrev scalarNewtonSecantConvergence (f f' : ℝ → ℝ) (a b : ℝ) : Prop :=
  MonotoneRoot.Convergence f f' a b

/-- **Lemma B.8.1 (Newton and secant rates).** Both the convex decreasing and
concave increasing cases satisfy all the source convergence conclusions. A simple
root is required: the source's missing nonzero derivative condition is essential
for its superlinear and quadratic rates. In the concave increasing case, the
initial values are negative before the root, correcting the source's positive sign.
The factor is exactly `1 - θ'(b)/θ'(a)` in both cases. -/
theorem lemma_B_8_1 {θ : ℝ → ℝ} {a b : ℝ} {D : Set ℝ}
    (hab : a < b) (hD : IsOpen D) (hsub : Set.Icc a b ⊆ D)
    (hθ : ContDiffOn ℝ 1 θ D) (hroot : θ b = 0)
    (hshape : (ConvexOn ℝ (Set.Icc a b) θ ∧ deriv θ b < 0) ∨
      (ConcaveOn ℝ (Set.Icc a b) θ ∧ 0 < deriv θ b)) :
    scalarNewtonSecantConvergence θ (deriv θ) a b := by
  have hlocal : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 1 θ x :=
    fun x hx => hθ.contDiffAt (hD.mem_nhds (hsub hx))
  exact MonotoneRoot.convergence_of_convex_or_concave hab.le
    (fun x hx => ((hlocal x hx).differentiableAt (by norm_num)).hasDerivAt)
    (fun x hx => (hlocal x hx).continuousAt_deriv.continuousWithinAt) hroot hshape


/-- The transformed secular step (B.8.7), with its removable value `-A log μ` at `β = 0`. -/
noncomputable def transformedSecularStep (A μ β : ℝ) : ℝ :=
  A * Real.normalizedRpowDifference μ β

/-- The explicit nonzero-exponent expression in (B.8.7). -/
theorem transformedSecularStep_of_ne (A μ : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    transformedSecularStep A μ β = A * (1 - μ ^ β) / β := by
  simp [transformedSecularStep, hβ, mul_div_assoc]

/-- The zero-exponent transformed step is logarithmic. -/
@[simp] theorem transformedSecularStep_zero (A μ : ℝ) :
    transformedSecularStep A μ 0 = -A * Real.log μ := by
  simp [transformedSecularStep, mul_neg, neg_mul]

/-- The transformed-step formula decreases with the exponent, including exponent zero. -/
theorem transformedSecularStep_antitone {A μ : ℝ} (hA : 0 ≤ A) (hμ : 0 < μ) :
    Antitone (transformedSecularStep A μ) := by
  intro a b hab
  exact mul_le_mul_of_nonneg_left (Real.antitone_normalizedRpowDifference hμ hab) hA

/-- The logarithmic step is the continuous extension at zero exponent. -/
theorem transformedSecularStep_continuousAt_zero (A : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ContinuousAt (transformedSecularStep A μ) 0 :=
  continuousAt_const.mul (Real.continuousAt_normalizedRpowDifference_zero hμ)

/-- **Lemma B.8.2 (monotonicity of transformed secular Newton steps).**
The genuine Newton steps have nonzero denominators, satisfy (B.8.7), and are antitone
in the exponent. The scalar function need only be differentiable at the current point,
with positive value and negative derivative. The exponent-zero equation is logarithmic,
which corrects the removable singularity in the source's quotient. -/
theorem lemma_B_8_2 {φ : ℝ → ℝ} {Δ c d : ℝ} (hφ : HasDerivAt φ d c)
    (hΔ : 0 < Δ) (hv : 0 < φ c) (hd : d < 0) :
    (∀ β : ℝ, deriv (Real.powerTransformDifference φ (Δ ^ 2) β) c ≠ 0) ∧
    (∀ β : ℝ,
      -(Real.powerTransformDifference φ (Δ ^ 2) β c) /
          deriv (Real.powerTransformDifference φ (Δ ^ 2) β) c =
        transformedSecularStep (-φ c / d) (Δ ^ 2 / φ c) β) ∧
    Antitone (fun β : ℝ => -(Real.powerTransformDifference φ (Δ ^ 2) β c) /
      deriv (Real.powerTransformDifference φ (Δ ^ 2) β) c) :=
  ⟨Real.deriv_powerTransformDifference_ne_zero hφ hv hd.ne,
    fun β => Real.newton_powerTransformDifference hφ (sq_pos_of_pos hΔ) hv hd.ne β,
    Real.antitone_newton_powerTransformDifference hφ (sq_pos_of_pos hΔ) hv hd⟩

end CartisGouldToint
