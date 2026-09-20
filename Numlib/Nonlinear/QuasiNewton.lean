import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# Broyden's method for nonlinear systems

The rank-one secant update of Broyden ([quarteroni2000numerical] §7.1.4, (7.14); Dennis–Schnabel,
*Numerical Methods for Unconstrained Optimization and Nonlinear Equations*, Chapter 8) on a real
inner product space `E`,

  `Broyden.update Q s y = Q + ((y - Q s) ⊗ s) / ⟪s, s⟫`,

written with Mathlib's `InnerProductSpace.rankOne`, and its three defining properties: the secant
condition `Q₊ s = y` (`Broyden.update_apply_self`), invariance on `s^⊥`
(`Broyden.update_sub_apply_of_inner_eq_zero`, the least-change reading of the book's derivation:
`Q₊ - Q` vanishes on every direction orthogonal to the step), and least change in the operator
norm among all operators satisfying the secant condition (`Broyden.norm_update_sub_le`, with the
exact value `‖Q₊ - Q‖ = ‖y - Q s‖ / ‖s‖`). The iteration (7.11)–(7.14) is the state machine
`Broyden.step` on the pair `(x, Q)`, with `Broyden.iterate` its orbit; the step solves `Q δ = -F x`
with the junk-valued `ContinuousLinearMap.inverse`, as `Newton.step` does, so that a singular `Q`
leaves the state unchanged rather than breaking the definition.

On `Matrix n n ℝ` the update is `Matrix.broydenUpdate`, bridged to the operator form through
`Matrix.toEuclideanCLM`, with the least-change property in the Frobenius norm
(`Matrix.frobenius_norm_broydenUpdate_sub_le`, Dennis–Schnabel Lemma 8.1.1) and the
**bounded deterioration** estimate
`‖Q₊ - J(z)‖_F ≤ ‖Q - J(z)‖_F + (L / 2) (‖x₊ - z‖ + ‖x - z‖)`
(`Matrix.frobenius_norm_broydenUpdate_sub_le_add`, Dennis–Schnabel Lemma 8.2.1), the first
step of every superlinear convergence proof for Broyden's method. The superlinear convergence
theorem itself ([quarteroni2000numerical] Property 7.2, the Dennis–Moré theory) is
`Broyden.exists_superlinear` of `Numlib/Nonlinear/DennisMore`.

The estimates rest on two auxiliary facts: the mean value inequality with the derivative frozen
at a *third* point, `‖F y - F x - F' z (y - x)‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`
(Dennis–Schnabel Lemma 4.1.15, `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add` of
`Numlib/Analysis/Calculus/MeanValue`), and the Frobenius-norm contraction of the projection off a
line, `‖A (1 - s sᵀ / sᵀ s)‖_F ≤ ‖A‖_F` (`Matrix.frobenius_norm_mul_one_sub_le` of
`Numlib/Analysis/Matrix/OperatorNorm`, Pythagoras in the trace form `‖A‖_F² = tr(Aᵀ A)`).
-/

open scoped InnerProductSpace

namespace Broyden

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Broyden's update** ([quarteroni2000numerical] (7.14)): `Q₊ = Q + ((y - Q s) ⊗ s) / ⟪s, s⟫`,
where `(u ⊗ s) v = ⟪s, v⟫ u` is Mathlib's `InnerProductSpace.rankOne ℝ u s`. In the book's
notation `s = δx_k` is the last step and `y = b_k = F x_k - F x_{k-1}` the corresponding change of
`F`; the update is the rank-one correction of `Q` that enforces the secant condition `Q₊ s = y`
while leaving `Q` unchanged on the orthogonal complement of `s`. For `s = 0` the coefficient
`1 / ⟪s, s⟫` is the junk value `0` and `Q₊ = Q`. -/
noncomputable def update (Q : E →L[ℝ] E) (s y : E) : E →L[ℝ] E :=
  Q + (1 / ⟪s, s⟫_ℝ) • InnerProductSpace.rankOne ℝ (y - Q s) s

/-- The update applied to a vector: `Q₊ v = Q v + (⟪s, v⟫ / ⟪s, s⟫) (y - Q s)`. -/
theorem update_apply (Q : E →L[ℝ] E) (s y v : E) :
    update Q s y v = Q v + (⟪s, v⟫_ℝ / ⟪s, s⟫_ℝ) • (y - Q s) := by
  simp only [update, add_apply, smul_apply, InnerProductSpace.rankOne_apply, smul_smul, one_div,
    inv_mul_eq_div]

/-- The correction made by the update is the scaled rank-one operator `((y - Q s) ⊗ s) / ⟪s, s⟫`. -/
theorem update_sub (Q : E →L[ℝ] E) (s y : E) :
    update Q s y - Q = (1 / ⟪s, s⟫_ℝ) • InnerProductSpace.rankOne ℝ (y - Q s) s := by
  simp [update]

/-- **The secant condition** ([quarteroni2000numerical] (7.12) with `j = 1`): for `s ≠ 0`,
`Q₊ s = y`. -/
theorem update_apply_self (Q : E →L[ℝ] E) {s : E} (hs : s ≠ 0) (y : E) : update Q s y s = y := by
  rw [update_apply, div_self (inner_self_ne_zero.2 hs), one_smul]
  abel

/-- **The update changes `Q` only along `s`**: `(Q₊ - Q) v = 0` for every `v ⟂ s`. Together with
the secant condition this is the characterization of (7.14) in [quarteroni2000numerical] §7.1.4:
`(Q_k - Q_{k-1}) s` vanishes for every `s` orthogonal to `δx_k`. -/
theorem update_sub_apply_of_inner_eq_zero (Q : E →L[ℝ] E) (s y : E) {v : E}
    (hv : ⟪s, v⟫_ℝ = 0) : (update Q s y - Q) v = 0 := by
  simp [update_sub, InnerProductSpace.rankOne_apply, hv]

/-- The size of the correction: `‖Q₊ - Q‖ = ‖y - Q s‖ / ‖s‖` (both sides are `0` when
`s = 0`). -/
theorem norm_update_sub (Q : E →L[ℝ] E) (s y : E) : ‖update Q s y - Q‖ = ‖y - Q s‖ / ‖s‖ := by
  rw [update_sub, norm_smul, InnerProductSpace.norm_rankOne, Real.norm_eq_abs,
    real_inner_self_eq_norm_sq, abs_of_nonneg (by positivity)]
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · have h : 0 < ‖s‖ := norm_pos_iff.2 hs
    field_simp

/-- **Least change in the operator norm** (Dennis–Schnabel §8.1): among all operators `Q'`
satisfying the secant condition `Q' s = y`, Broyden's update is the closest to `Q`, since
`‖Q₊ - Q‖ = ‖(Q' - Q) s‖ / ‖s‖ ≤ ‖Q' - Q‖`. -/
theorem norm_update_sub_le (Q Q' : E →L[ℝ] E) {s : E} (hs : s ≠ 0) {y : E} (hQ' : Q' s = y) :
    ‖update Q s y - Q‖ ≤ ‖Q' - Q‖ := by
  rw [norm_update_sub, div_le_iff₀ (norm_pos_iff.2 hs), ← hQ', ← sub_apply]
  exact (Q' - Q).le_opNorm s

/-! ### The iteration -/

/-- The state of Broyden's iteration: the current point `x` and the current approximation `Q` of
the Jacobian. -/
structure State (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The current iterate. -/
  x : E
  /-- The current Jacobian approximation. -/
  Q : E →L[ℝ] E

/-- One step of Broyden's method ([quarteroni2000numerical] (7.11)–(7.14)): solve `Q δ = -F x`
(with the junk-valued `ContinuousLinearMap.inverse`, `δ = 0` when `Q` is singular), move to
`x₊ = x + δ`, and update `Q` with the secant pair `(δ, F x₊ - F x)`. -/
noncomputable def step (Fn : E → E) (σ : State E) : State E where
  x := σ.x - σ.Q.inverse (Fn σ.x)
  Q := update σ.Q (-(σ.Q.inverse (Fn σ.x))) (Fn (σ.x - σ.Q.inverse (Fn σ.x)) - Fn σ.x)

/-- The point component of a Broyden step, `x₊ = x - Q⁻¹ (F x)`. -/
theorem step_x (Fn : E → E) (σ : State E) : (step Fn σ).x = σ.x - σ.Q.inverse (Fn σ.x) :=
  rfl

/-- The operator component of a Broyden step is the update with `s = x₊ - x` and
`y = F x₊ - F x`. -/
theorem step_Q (Fn : E → E) (σ : State E) :
    (step Fn σ).Q = update σ.Q ((step Fn σ).x - σ.x) (Fn (step Fn σ).x - Fn σ.x) := by
  simp only [step, sub_sub_cancel_left]

/-- **The secant condition along the iteration** ([quarteroni2000numerical] (7.12) with `j = 1`):
whenever the step is nonzero, `Q₊ (x₊ - x) = F x₊ - F x`. -/
theorem step_Q_apply_sub (Fn : E → E) (σ : State E) (h : (step Fn σ).x ≠ σ.x) :
    (step Fn σ).Q ((step Fn σ).x - σ.x) = Fn (step Fn σ).x - Fn σ.x := by
  rw [step_Q]
  exact update_apply_self _ (sub_ne_zero.2 h) _

/-- The linear system solved by a step ([quarteroni2000numerical] (7.11)): when `Q` is
invertible, `Q (x₊ - x) = -F x`. -/
theorem apply_step_x_sub (Fn : E → E) (σ : State E) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = σ.Q) : σ.Q ((step Fn σ).x - σ.x) = -Fn σ.x := by
  rw [step_x, sub_sub_cancel_left, map_neg, ← he, ContinuousLinearMap.inverse_equiv]
  simp

/-- A root is a fixed point of the point component: at `F x = 0` the step does not move. -/
theorem step_x_eq_self_of_eq_zero (Fn : E → E) (σ : State E) (hx : Fn σ.x = 0) :
    (step Fn σ).x = σ.x := by
  simp [step_x, hx]

/-- The orbit of Broyden's method from the initial point `x₀` and the initial approximation
`Q₀`. -/
noncomputable def iterate (Fn : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) (k : ℕ) : State E :=
  (step Fn)^[k] ⟨x₀, Q₀⟩

/-- The initial state. -/
@[simp] theorem iterate_zero (Fn : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) :
    iterate Fn x₀ Q₀ 0 = ⟨x₀, Q₀⟩ :=
  rfl

/-- The recurrence: the next state is the step taken at the last one. -/
theorem iterate_succ (Fn : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) (k : ℕ) :
    iterate Fn x₀ Q₀ (k + 1) = step Fn (iterate Fn x₀ Q₀ k) :=
  Function.iterate_succ_apply' _ _ _

end Broyden

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

open WithLp

/-- **Broyden's update in matrix form** ([quarteroni2000numerical] (7.14)):
`Q₊ = Q + ((y - Q s) sᵀ) / (sᵀ s)`. -/
noncomputable def broydenUpdate (Q : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  Q + (1 / (s ⬝ᵥ s)) • vecMulVec (y - Q *ᵥ s) s

omit [DecidableEq n] in
/-- Broyden's update with a zero step does not move: `broydenUpdate Q 0 y = Q`. -/
theorem broydenUpdate_zero_left (Q : Matrix n n ℝ) (y : n → ℝ) :
    broydenUpdate Q 0 y = Q := by
  simp [broydenUpdate]

/-- The matrix update is the operator update: `toEuclideanCLM (broydenUpdate Q s y)` is
`Broyden.update` of `toEuclideanCLM Q` with the secant pair read in `EuclideanSpace ℝ n`. -/
theorem toEuclideanCLM_broydenUpdate (Q : Matrix n n ℝ) (s y : n → ℝ) :
    toEuclideanCLM (𝕜 := ℝ) (broydenUpdate Q s y)
      = Broyden.update (toEuclideanCLM (𝕜 := ℝ) Q) (toLp 2 s) (toLp 2 y) := by
  rw [broydenUpdate, Broyden.update, map_add, map_smul, toEuclideanCLM_vecMulVec,
    EuclideanSpace.inner_toLp_toLp, star_trivial, toEuclideanCLM_toLp, ← toLp_sub]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Least change in the Frobenius norm** (Dennis–Schnabel Lemma 8.1.1): among all matrices
`Q'` satisfying the secant condition `Q' s = y`, Broyden's update is the closest to `Q`, since
`Q₊ - Q = ((Q' - Q) s) sᵀ / (sᵀ s)` has Frobenius norm `‖(Q' - Q) s‖ / ‖s‖ ≤ ‖Q' - Q‖_F`. -/
theorem frobenius_norm_broydenUpdate_sub_le (Q Q' : Matrix n n ℝ) {s y : n → ℝ} (hs : s ≠ 0)
    (hQ's : Q' *ᵥ s = y) : ‖broydenUpdate Q s y - Q‖ ≤ ‖Q' - Q‖ := by
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  rw [broydenUpdate, add_sub_cancel_left, norm_smul, ← hQ's, ← sub_mulVec, Real.norm_eq_abs,
    dotProduct_self_eq_norm_sq, abs_of_nonneg (by positivity)]
  calc 1 / ‖toLp 2 s‖ ^ 2 * ‖vecMulVec ((Q' - Q) *ᵥ s) s‖
      ≤ 1 / ‖toLp 2 s‖ ^ 2 * (‖toLp 2 ((Q' - Q) *ᵥ s)‖ * ‖toLp 2 s‖) := by
        gcongr
        exact frobenius_norm_vecMulVec_le _ _
    _ ≤ 1 / ‖toLp 2 s‖ ^ 2 * (‖Q' - Q‖ * ‖toLp 2 s‖ * ‖toLp 2 s‖) := by
        gcongr
        exact frobenius_norm_mulVec_le _ _
    _ = ‖Q' - Q‖ := by field_simp

/-- **Bounded deterioration of Broyden's update** (Dennis–Schnabel Lemma 8.2.1): if
`F` has Jacobian `J` on a convex set `D` containing `x` and `x₊ = x + s`, with
`‖J w - J z‖ ≤ L ‖w - z‖` on `D` in the operator norm of `EuclideanSpace ℝ n`, and
`y = F x₊ - F x`, then in the Frobenius norm

  `‖Q₊ - J z‖_F ≤ ‖Q - J z‖_F + (L / 2) (‖x₊ - z‖ + ‖x - z‖)`.

The decomposition is `Q₊ - J z = (Q - J z) (1 - P) + ((y - J z s) sᵀ) / (sᵀ s)` with
`P = s sᵀ / (sᵀ s)`; the first term is bounded by `Matrix.frobenius_norm_mul_one_sub_le` and the
second by `‖y - J z s‖ / ‖s‖` and the third-point mean value inequality
`Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add`. This is the estimate every
superlinear convergence proof for Broyden's method (the Dennis–Moré theory,
[quarteroni2000numerical] Property 7.2) starts from. -/
theorem frobenius_norm_broydenUpdate_sub_le_add {F : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {J : EuclideanSpace ℝ n → Matrix n n ℝ} {D : Set (EuclideanSpace ℝ n)} (hD : Convex ℝ D)
    (hF : ∀ w ∈ D, HasFDerivAt F (toEuclideanCLM (𝕜 := ℝ) (J w)) w) {z : EuclideanSpace ℝ n}
    {L : ℝ}
    (hL : ∀ w ∈ D, ‖toEuclideanCLM (𝕜 := ℝ) (J w) - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ L * ‖w - z‖)
    {x : EuclideanSpace ℝ n} (hx : x ∈ D) {s : n → ℝ} (hs : s ≠ 0) (hxs : x + toLp 2 s ∈ D)
    (Q : Matrix n n ℝ) :
    ‖broydenUpdate Q s (ofLp (F (x + toLp 2 s) - F x)) - J z‖
      ≤ ‖Q - J z‖ + L / 2 * (‖x + toLp 2 s - z‖ + ‖x - z‖) := by
  set y : n → ℝ := ofLp (F (x + toLp 2 s) - F x) with hy
  set w : n → ℝ := y - J z *ᵥ s with hw
  set P : Matrix n n ℝ := (1 / (s ⬝ᵥ s)) • vecMulVec s s with hPdef
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  -- the decomposition
  have hdecomp : broydenUpdate Q s y - J z
      = (Q - J z) * (1 - P) + (1 / (s ⬝ᵥ s)) • vecMulVec w s := by
    rw [broydenUpdate, hPdef, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec,
      hw, sub_mulVec, show y - Q *ᵥ s = (y - J z *ᵥ s) - (Q *ᵥ s - J z *ᵥ s) by abel,
      sub_vecMulVec, smul_sub]
    abel
  -- the mean value estimate for the secant residual
  have hmv : ‖toLp 2 w‖ ≤ L / 2 * (‖x - z‖ + ‖x + toLp 2 s - z‖) * ‖toLp 2 s‖ := by
    have h := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add hD hF
      (y := x + toLp 2 s) hx hxs hL
    rw [add_sub_cancel_left] at h
    refine le_of_eq_of_le ?_ h
    rw [hw, hy, toLp_sub, toLp_ofLp, toEuclideanCLM_toLp]
  have hsecond : ‖(1 / (s ⬝ᵥ s)) • vecMulVec w s‖
      ≤ L / 2 * (‖x + toLp 2 s - z‖ + ‖x - z‖) := by
    rw [norm_smul, Real.norm_eq_abs, dotProduct_self_eq_norm_sq, abs_of_nonneg (by positivity)]
    calc 1 / ‖toLp 2 s‖ ^ 2 * ‖vecMulVec w s‖
        ≤ 1 / ‖toLp 2 s‖ ^ 2 * (‖toLp 2 w‖ * ‖toLp 2 s‖) := by
          gcongr
          exact frobenius_norm_vecMulVec_le _ _
      _ ≤ 1 / ‖toLp 2 s‖ ^ 2
            * (L / 2 * (‖x - z‖ + ‖x + toLp 2 s - z‖) * ‖toLp 2 s‖ * ‖toLp 2 s‖) := by
          gcongr
      _ = L / 2 * (‖x + toLp 2 s - z‖ + ‖x - z‖) := by
          field_simp
          ring
  calc ‖broydenUpdate Q s y - J z‖
      = ‖(Q - J z) * (1 - P) + (1 / (s ⬝ᵥ s)) • vecMulVec w s‖ := by rw [hdecomp]
    _ ≤ ‖(Q - J z) * (1 - P)‖ + ‖(1 / (s ⬝ᵥ s)) • vecMulVec w s‖ := norm_add_le _ _
    _ ≤ ‖Q - J z‖ + L / 2 * (‖x + toLp 2 s - z‖ + ‖x - z‖) :=
        add_le_add (frobenius_norm_mul_one_sub_le _ hs) hsecond

end Frobenius

end Matrix
