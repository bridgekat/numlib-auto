import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Nonlinear.QuasiNewton

/-!
# Local convergence of Broyden's method: the Dennis–Moré theory

The local superlinear convergence of Broyden's method ([quarteroni2000numerical] Property 7.2;
Dennis–Moré, *A characterization of superlinear convergence and its application to quasi-Newton
methods*, 1974; Dennis–Schnabel, *Numerical Methods for Unconstrained Optimization and Nonlinear
Equations*, Theorem 8.2.2), on `EuclideanSpace ℝ n`, for the iteration `Broyden.iterate` of
`Numlib/Nonlinear/QuasiNewton`. The proof has three layers.

* **The Frobenius geometry of the update.** With `P = s sᵀ / (sᵀ s)` the projector onto the step,
  Pythagoras `‖A (1 - P)‖_F² + ‖A P‖_F² = ‖A‖_F²`
  (`Matrix.frobenius_norm_sq_mul_one_sub_add_sq_mul`) and `‖A s‖ ≤ ‖A P‖_F ‖s‖` give the
  **Dennis–Moré inequality** `‖A s‖² / ‖s‖² ≤ 2 ‖A‖_F (‖A‖_F - ‖A (1 - P)‖_F)`
  (`Matrix.sq_norm_mulVec_div_le_frobenius`),
  and for Broyden's update `Q₊ = Q + ((y - Q s) sᵀ) / (sᵀ s)` with `E = Q - J`, `E₊ = Q₊ - J`,
  `‖E s‖² / ‖s‖² ≤ 2 ‖E‖_F (‖E‖_F - ‖E₊‖_F + ‖y - J s‖ / ‖s‖)`
  (`Matrix.sq_norm_sub_mulVec_div_le_broydenUpdate`): the update cannot decrease the Frobenius
  error much without the error along the step being small.
* **Bounded deterioration and linear convergence** (Dennis–Schnabel Theorem 8.2.2, the
  two-sequence induction). Under `Broyden.LipschitzJacobianRoot` — `F` differentiable on a convex
  `D` with Jacobian `J`, Lipschitz at the root `z` — and `‖J z⁻¹‖ ≤ β`, one step from a `Q`
  within `1 / (3β)` of `J z` is well defined and contracts,
  `‖x₊ - z‖ ≤ (3β / 2) (‖Q - J z‖ + (L / 2) ‖x - z‖) ‖x - z‖` (`Broyden.norm_step_x_sub_le`);
  the bounded deterioration `‖M_{k+1} - J z‖_F ≤ ‖M_k - J z‖_F + (L / 2) (‖x_{k+1} - z‖ +
  ‖x_k - z‖)` of `Matrix.frobenius_norm_broydenUpdate_sub_le_add` along the iteration
  (`Broyden.frobenius_norm_symm_iterate_succ_sub_le`) and the invariant `‖x_k - z‖ ≤ ε / 2ᵏ`,
  `‖M_k - J z‖_F ≤ 2δ` (`Broyden.norm_iterate_sub_le_and_frobenius_norm_le`) follow by
  induction under the thresholds `12 β δ ≤ 1`, `3 L ε ≤ 2δ`.
* **The Dennis–Moré condition and superlinear convergence.** Summing the Dennis–Moré inequality
  along the iteration telescopes the Frobenius errors, so the quotients
  `η_k = ‖(Q_k - J z) s_k‖ / ‖s_k‖` (`Broyden.dennisMoreQuotient`) are square-summable and tend
  to zero (`Broyden.tendsto_dennisMoreQuotient`); the secant equation `Q_k s_k = -F x_k` then
  gives `‖x_{k+1} - z‖ ≤ 4β (η_k + L ‖x_k - z‖) ‖x_k - z‖` (`Broyden.norm_iterate_succ_sub_le_mul`),
  which is superlinear convergence with the explicit constants `c_k = 4β (η_k + L ε / 2ᵏ) → 0`
  (`Broyden.superlinear_of_le`, and `Broyden.exists_superlinear` in the book's existential form,
  with the hypothesis on `Q₀` in the operator norm).

The Jacobian is carried as a matrix-valued `J : E → Matrix n n ℝ`, because the deterioration
estimate lives in the Frobenius norm; the operators of `Broyden.iterate` are read back as
matrices through `Matrix.toEuclideanCLM.symm` (`Broyden.symm_iterate_succ_Q`), and the two norms
are compared by `Matrix.norm_toEuclideanCLM_le_frobenius_norm` and
`Matrix.frobenius_norm_le_sqrt_card_mul_norm_toEuclideanCLM`. Whether `Q_k → J z` is not
claimed: it fails in general ([quarteroni2000numerical] Example 7.3).
-/

open scoped InnerProductSpace
open Filter Topology WithLp

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- The Frobenius norm squared of a real matrix is the trace of `Aᵀ A`. -/
private theorem frobenius_norm_sq_eq_trace_transpose' (A : Matrix n n ℝ) :
    ‖A‖ ^ 2 = trace (Aᵀ * A) := by
  have h := frobenius_norm_sq_eq_trace (𝕜 := ℝ) A
  simpa [conjTranspose_eq_transpose_of_trivial] using h

/-- **Pythagoras for the projector onto a line**: with `P = s sᵀ / (sᵀ s)`,
`‖A (1 - P)‖_F² + ‖A P‖_F² = ‖A‖_F²`, in the trace form `‖M‖_F² = tr(Mᵀ M)`, since `P` is
symmetric and idempotent. -/
theorem frobenius_norm_sq_mul_one_sub_add_sq_mul (A : Matrix n n ℝ) {s : n → ℝ} (hs : s ≠ 0) :
    ‖A * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s)‖ ^ 2 + ‖A * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)‖ ^ 2
      = ‖A‖ ^ 2 := by
  set P : Matrix n n ℝ := (1 / (s ⬝ᵥ s)) • vecMulVec s s with hPdef
  have hss : s ⬝ᵥ s ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (by simpa using hs))
  have hPt : Pᵀ = P := by
    rw [hPdef, transpose_smul, transpose_vecMulVec]
  have hPP : P * P = P := by
    rw [hPdef, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, vecMulVec_smul,
      smul_smul, smul_smul]
    congr 1
    field_simp
  have hQt : (1 - P)ᵀ = 1 - P := by rw [transpose_sub, transpose_one, hPt]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hPP]
    abel
  have h1 : ‖A * (1 - P)‖ ^ 2 = trace (Aᵀ * A * (1 - P)) := by
    rw [frobenius_norm_sq_eq_trace_transpose', transpose_mul, hQt, Matrix.mul_assoc,
      trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hQQ, ← Matrix.mul_assoc]
  have h2 : ‖A * P‖ ^ 2 = trace (Aᵀ * A * P) := by
    rw [frobenius_norm_sq_eq_trace_transpose', transpose_mul, hPt, Matrix.mul_assoc,
      trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hPP, ← Matrix.mul_assoc]
  have h3 : ‖A‖ ^ 2 = trace (Aᵀ * A) := frobenius_norm_sq_eq_trace_transpose' A
  rw [h1, h2, h3, ← trace_add, ← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]

omit [DecidableEq n] in
/-- The projector `P = s sᵀ / (sᵀ s)` fixes `s`. -/
theorem smul_vecMulVec_mulVec_self {s : n → ℝ} (hs : s ≠ 0) :
    ((1 / (s ⬝ᵥ s)) • vecMulVec s s) *ᵥ s = s := by
  have hss : s ⬝ᵥ s ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (by simpa using hs))
  rw [smul_mulVec, vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul, smul_smul, one_div,
    inv_mul_cancel₀ hss, one_smul]

/-- **The projected part of `A` sees `A s`**: `‖A s‖₂ ≤ ‖A P‖_F ‖s‖₂` for `P = s sᵀ / (sᵀ s)`,
since `(A P) s = A s`. -/
theorem norm_mulVec_le_frobenius_norm_mul_proj (A : Matrix n n ℝ) {s : n → ℝ} (hs : s ≠ 0) :
    ‖toLp 2 (A *ᵥ s)‖ ≤ ‖A * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)‖ * ‖toLp 2 s‖ := by
  have h := frobenius_norm_mulVec_le (A * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)) s
  rwa [← mulVec_mulVec, smul_vecMulVec_mulVec_self hs] at h

/-- **The Dennis–Moré inequality for the projection off a line**:
`‖A s‖₂² / ‖s‖₂² ≤ 2 ‖A‖_F (‖A‖_F - ‖A (1 - P)‖_F)` with `P = s sᵀ / (sᵀ s)`. From Pythagoras,
`‖A s‖² / ‖s‖² ≤ ‖A P‖_F² = ‖A‖_F² - ‖A (1 - P)‖_F²
= (‖A‖_F - ‖A (1 - P)‖_F)(‖A‖_F + ‖A (1 - P)‖_F)` and `‖A (1 - P)‖_F ≤ ‖A‖_F`. This is the
quantitative form of "the update cannot decrease the Frobenius error along `s` without paying
for it" behind the superlinear convergence of
Broyden's method (Dennis–Schnabel, *Numerical Methods for Unconstrained Optimization and
Nonlinear Equations*, proof of Theorem 8.2.2). -/
theorem sq_norm_mulVec_div_le_frobenius (A : Matrix n n ℝ) {s : n → ℝ} (hs : s ≠ 0) :
    ‖toLp 2 (A *ᵥ s)‖ ^ 2 / ‖toLp 2 s‖ ^ 2
      ≤ 2 * ‖A‖ * (‖A‖ - ‖A * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s)‖) := by
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  have hpyth := frobenius_norm_sq_mul_one_sub_add_sq_mul A hs
  have hproj := norm_mulVec_le_frobenius_norm_mul_proj A hs
  have hle := frobenius_norm_mul_one_sub_le A hs
  set a := ‖A‖
  set c := ‖A * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s)‖
  set b := ‖A * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)‖
  have hq : ‖toLp 2 (A *ᵥ s)‖ ^ 2 / ‖toLp 2 s‖ ^ 2 ≤ b ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ ‖toLp 2 (A *ᵥ s)‖ := norm_nonneg _
    have hb0 : 0 ≤ b * ‖toLp 2 s‖ := by positivity
    calc ‖toLp 2 (A *ᵥ s)‖ ^ 2 ≤ (b * ‖toLp 2 s‖) ^ 2 := pow_le_pow_left₀ h0 hproj 2
      _ = b ^ 2 * ‖toLp 2 s‖ ^ 2 := by ring
  have hc0 : 0 ≤ c := norm_nonneg _
  nlinarith

/-- **The Dennis–Moré inequality for Broyden's update** (Dennis–Schnabel, proof of Theorem
8.2.2): for `s ≠ 0`, with `E = Q - J` the current error and `E₊ = Q₊ - J` the error after the
update `Q₊ = broydenUpdate Q s y`,

`‖E s‖₂² / ‖s‖₂² ≤ 2 ‖E‖_F (‖E‖_F - ‖E₊‖_F + ‖y - J s‖₂ / ‖s‖₂)`.

From `E₊ = E (1 - P) + ((y - J s) sᵀ) / (sᵀ s)`, `‖E₊‖_F ≤ ‖E (1 - P)‖_F + ‖y - J s‖ / ‖s‖`, and
`sq_norm_mulVec_div_le_frobenius`. Summed along Broyden's iteration, where `‖y - J s‖ / ‖s‖` is
`O(‖x - z‖)` and the Frobenius errors are bounded, this forces `‖E_k s_k‖ / ‖s_k‖ → 0`, the
Dennis–Moré condition for superlinear convergence. -/
theorem sq_norm_sub_mulVec_div_le_broydenUpdate (Q J : Matrix n n ℝ) {s y : n → ℝ}
    (hs : s ≠ 0) :
    ‖toLp 2 ((Q - J) *ᵥ s)‖ ^ 2 / ‖toLp 2 s‖ ^ 2
      ≤ 2 * ‖Q - J‖ * (‖Q - J‖ - ‖broydenUpdate Q s y - J‖
          + ‖toLp 2 (y - J *ᵥ s)‖ / ‖toLp 2 s‖) := by
  set P : Matrix n n ℝ := (1 / (s ⬝ᵥ s)) • vecMulVec s s with hPdef
  set w : n → ℝ := y - J *ᵥ s with hw
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  have hdecomp : broydenUpdate Q s y - J = (Q - J) * (1 - P) + (1 / (s ⬝ᵥ s)) • vecMulVec w s := by
    rw [broydenUpdate, hPdef, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec,
      hw, sub_mulVec, show y - Q *ᵥ s = (y - J *ᵥ s) - (Q *ᵥ s - J *ᵥ s) by abel,
      sub_vecMulVec, smul_sub]
    abel
  have hsecond : ‖(1 / (s ⬝ᵥ s)) • vecMulVec w s‖ ≤ ‖toLp 2 w‖ / ‖toLp 2 s‖ := by
    rw [norm_smul, Real.norm_eq_abs, dotProduct_self_eq_norm_sq, abs_of_nonneg (by positivity)]
    calc 1 / ‖toLp 2 s‖ ^ 2 * ‖vecMulVec w s‖
        ≤ 1 / ‖toLp 2 s‖ ^ 2 * (‖toLp 2 w‖ * ‖toLp 2 s‖) := by
          gcongr
          exact frobenius_norm_vecMulVec_le _ _
      _ = ‖toLp 2 w‖ / ‖toLp 2 s‖ := by
          field_simp
  have h1 : ‖broydenUpdate Q s y - J‖ ≤ ‖(Q - J) * (1 - P)‖ + ‖toLp 2 w‖ / ‖toLp 2 s‖ := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hsecond)
  have h2 := sq_norm_mulVec_div_le_frobenius (Q - J) hs
  have h3 : 0 ≤ ‖Q - J‖ := norm_nonneg _
  refine h2.trans ?_
  rw [← hPdef]
  nlinarith

/-- The Euclidean operator norm of a real matrix is at most its Frobenius norm. -/
theorem norm_toEuclideanCLM_le_frobenius_norm (A : Matrix n n ℝ) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have h := frobenius_norm_mulVec_le A (ofLp x)
  rwa [toLp_ofLp] at h

/-- The Frobenius norm of a real matrix is at most `√n` times its Euclidean operator norm. -/
theorem frobenius_norm_le_sqrt_card_mul_norm_toEuclideanCLM (A : Matrix n n ℝ) :
    ‖A‖ ≤ √(Fintype.card n : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) A‖ := by
  have h1 := frobenius_norm_le_sqrt_rank_mul_l2_opNorm A
  have h2 : lpOpNorm 2 A = ‖toEuclideanCLM (𝕜 := ℝ) A‖ := by
    rw [lpOpNorm]
    congr 1
  have h3 : (A.rank : ℝ) ≤ Fintype.card n := by exact_mod_cast A.rank_le_card_width
  calc ‖A‖ ≤ √(A.rank : ℝ) * lpOpNorm 2 A := h1
    _ ≤ √(Fintype.card n : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) A‖ := by
        rw [h2]
        gcongr

end Frobenius

end Matrix

namespace Broyden

open Matrix Metric

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "E" => EuclideanSpace ℝ n

/-- **The standing hypotheses of the local convergence theory** (Dennis–Schnabel Theorem 8.2.2,
[quarteroni2000numerical] Theorem 7.1): `F` is differentiable on a convex set `D` with Jacobian
matrix `J w` at `w ∈ D`, `z ∈ D` is a root, `F z = 0`, and the Jacobian is Lipschitz at `z` on
`D` with constant `L`, `‖J w - J z‖ ≤ L ‖w - z‖`, in the Euclidean operator norm. -/
structure LipschitzJacobianRoot (F : E → E) (J : E → Matrix n n ℝ) (D : Set E) (z : E)
    (L : ℝ) : Prop where
  /-- `D` is convex. -/
  convex : Convex ℝ D
  /-- `F` has Jacobian `J w` at every `w ∈ D`. -/
  hasFDerivAt : ∀ w ∈ D, HasFDerivAt F (toEuclideanCLM (𝕜 := ℝ) (J w)) w
  /-- `z` is a root. -/
  root : F z = 0
  /-- `z ∈ D`. -/
  mem : z ∈ D
  /-- The Jacobian is Lipschitz at `z` on `D`. -/
  lipschitz : ∀ w ∈ D,
    ‖toEuclideanCLM (𝕜 := ℝ) (J w) - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ L * ‖w - z‖
  /-- The Lipschitz constant is nonnegative (automatic unless `D = {z}`). -/
  nonneg : 0 ≤ L

-- the local notation `E` must not be used in `variable` lines (it elaborates to `sorry` there)
variable {F : EuclideanSpace ℝ n → EuclideanSpace ℝ n} {J : EuclideanSpace ℝ n → Matrix n n ℝ}
  {D : Set (EuclideanSpace ℝ n)} {z : EuclideanSpace ℝ n} {L : ℝ}

/-- The quadratic remainder at the root: `‖F x - J z (x - z)‖ ≤ (L / 2) ‖x - z‖²` for `x ∈ D`
(the third-point mean value inequality with `x = z` as base point). -/
theorem LipschitzJacobianRoot.norm_sub_apply_le (h : LipschitzJacobianRoot F J D z L) {x : E}
    (hx : x ∈ D) : ‖F x - toEuclideanCLM (𝕜 := ℝ) (J z) (x - z)‖ ≤ L / 2 * ‖x - z‖ ^ 2 := by
  have hmv := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add h.convex h.hasFDerivAt
    (x := z) (y := x) h.mem hx h.lipschitz
  rw [h.root, sub_zero, sub_self, norm_zero, zero_add] at hmv
  linarith [sq ‖x - z‖]

/-- The secant remainder: `‖F y - F x - J z (y - x)‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖` for
`x, y ∈ D`. -/
theorem LipschitzJacobianRoot.norm_sub_sub_apply_le (h : LipschitzJacobianRoot F J D z L)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    ‖F y - F x - toEuclideanCLM (𝕜 := ℝ) (J z) (y - x)‖ ≤ L / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖ :=
  Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add h.convex h.hasFDerivAt hx hy
    h.lipschitz

/-- **One Broyden step near the root** (Dennis–Schnabel, proof of Theorem 8.2.2): if `Q` is
within `1 / (3β)` of `J z` in the operator norm, where `‖J z⁻¹‖ ≤ β`, then `Q` is invertible
with `‖Q⁻¹‖ ≤ 3β / 2` (the perturbation theorem
`ContinuousLinearEquiv.exists_symm_norm_le_of_add`) and the point `x₊ = x - Q⁻¹ F x` of
`Broyden.step` satisfies

`‖x₊ - z‖ ≤ (3β / 2) (‖Q - J z‖ + (L / 2) ‖x - z‖) ‖x - z‖`,

from `x₊ - z = Q⁻¹ ((Q - J z) (x - z) - (F x - J z (x - z)))`. -/
theorem norm_step_x_sub_le (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {x : E} (hx : x ∈ D) {Q : E →L[ℝ] E}
    (hQ : 3 * (β * ‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖) ≤ 1) :
    (∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = Q ∧ ‖(e'.symm : E →L[ℝ] E)‖ ≤ 3 * β / 2) ∧
      ‖(step F ⟨x, Q⟩).x - z‖
        ≤ 3 * β / 2 * (‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ + L / 2 * ‖x - z‖) * ‖x - z‖ := by
  set Js : E →L[ℝ] E := toEuclideanCLM (𝕜 := ℝ) (J z) with hJs
  set t : E →L[ℝ] E := Q - Js with ht
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg _
  have hes : ‖(e.symm : E →L[ℝ] E)‖ * ‖t‖ ≤ β * ‖t‖ := mul_le_mul_of_nonneg_right hβ ht0
  have hlt : ‖(e.symm : E →L[ℝ] E)‖ * ‖t‖ < 1 := by linarith
  obtain ⟨e', he', he'inv, -⟩ := ContinuousLinearEquiv.exists_symm_norm_le_of_add e t hlt
  have he'Q : (e' : E →L[ℝ] E) = Q := by rw [he', he, ht]; abel
  have hinv : ‖(e'.symm : E →L[ℝ] E)‖ ≤ 3 * β / 2 := by
    refine he'inv.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (e.symm : E →L[ℝ] E)]
  refine ⟨⟨e', he'Q, hinv⟩, ?_⟩
  have hstep : (step F ⟨x, Q⟩).x - z = e'.symm (Q (x - z) - F x) := by
    rw [step_x]
    change x - Q.inverse (F x) - z = e'.symm (Q (x - z) - F x)
    rw [← he'Q, ContinuousLinearMap.inverse_equiv, map_sub]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    abel
  have hmv := h.norm_sub_apply_le hx
  have hdecomp : Q (x - z) - F x = t (x - z) - (F x - Js (x - z)) := by
    rw [ht, _root_.sub_apply]
    abel
  calc ‖(step F ⟨x, Q⟩).x - z‖ = ‖e'.symm (Q (x - z) - F x)‖ := by rw [hstep]
    _ ≤ ‖(e'.symm : E →L[ℝ] E)‖ * ‖Q (x - z) - F x‖ := (e'.symm : E →L[ℝ] E).le_opNorm _
    _ ≤ 3 * β / 2 * (‖t‖ * ‖x - z‖ + L / 2 * ‖x - z‖ ^ 2) := by
        refine mul_le_mul hinv ?_ (norm_nonneg _) (by positivity)
        rw [hdecomp]
        exact (norm_sub_le _ _).trans (add_le_add (t.le_opNorm _) hmv)
    _ = 3 * β / 2 * (‖t‖ + L / 2 * ‖x - z‖) * ‖x - z‖ := by ring

/-! ### The iteration: bounded deterioration and linear convergence -/

section Iteration

open scoped Matrix.Norms.Frobenius

/-- **The matrix recurrence of Broyden's iteration**: with `M_k` the matrix of the operator
`Q_k` of `Broyden.iterate`, `M_{k+1} = broydenUpdate M_k s_k y_k` for the secant pair
`s_k = x_{k+1} - x_k`, `y_k = F x_{k+1} - F x_k` (`Broyden.step_Q` read through
`Matrix.toEuclideanCLM_broydenUpdate`). -/
theorem symm_iterate_succ_Q (F : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) (k : ℕ) :
    (toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ (k + 1)).Q
      = broydenUpdate ((toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q)
          (ofLp ((iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x))
          (ofLp (F (iterate F x₀ Q₀ (k + 1)).x - F (iterate F x₀ Q₀ k).x)) := by
  rw [StarAlgEquiv.symm_apply_eq, toEuclideanCLM_broydenUpdate, StarAlgEquiv.apply_symm_apply,
    toLp_ofLp, toLp_ofLp, iterate_succ, step_Q]

omit [DecidableEq n] in
/-- Broyden's update with a zero step does not move: `broydenUpdate Q 0 y = Q`. -/
theorem _root_.Matrix.broydenUpdate_zero_left (Q : Matrix n n ℝ) (y : n → ℝ) :
    broydenUpdate Q 0 y = Q := by
  simp [broydenUpdate]

/-- The operator error of the iteration is the image of the matrix error. -/
theorem iterate_Q_sub_eq (F : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) (k : ℕ) (M : Matrix n n ℝ) :
    (iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) M
      = toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - M) := by
  rw [map_sub, StarAlgEquiv.apply_symm_apply]

/-- **Bounded deterioration along Broyden's iteration** (Dennis–Schnabel Lemma 8.2.1 at every
step): if `x_k, x_{k+1} ∈ D` then, in the Frobenius norm,
`‖M_{k+1} - J z‖_F ≤ ‖M_k - J z‖_F + (L / 2) (‖x_{k+1} - z‖ + ‖x_k - z‖)`; a zero step leaves
`M_k` unchanged. -/
theorem frobenius_norm_symm_iterate_succ_sub_le (h : LipschitzJacobianRoot F J D z L)
    {x₀ : E} {Q₀ : E →L[ℝ] E} {k : ℕ} (hk : (iterate F x₀ Q₀ k).x ∈ D)
    (hk1 : (iterate F x₀ Q₀ (k + 1)).x ∈ D) :
    ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ (k + 1)).Q - J z‖
      ≤ ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - J z‖
        + L / 2 * (‖(iterate F x₀ Q₀ (k + 1)).x - z‖ + ‖(iterate F x₀ Q₀ k).x - z‖) := by
  set x : E := (iterate F x₀ Q₀ k).x with hx
  set x' : E := (iterate F x₀ Q₀ (k + 1)).x with hx'
  set M : Matrix n n ℝ := (toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q with hM
  rw [symm_iterate_succ_Q, ← hx, ← hx', ← hM]
  have hpos : 0 ≤ L / 2 * (‖x' - z‖ + ‖x - z‖) := by
    have := h.nonneg
    positivity
  by_cases hs : ofLp (x' - x) = 0
  · rw [hs, Matrix.broydenUpdate_zero_left]
    linarith
  · have hxs : x + toLp 2 (ofLp (x' - x)) ∈ D := by
      rwa [toLp_ofLp, add_sub_cancel]
    have := frobenius_norm_broydenUpdate_sub_le_add h.convex h.hasFDerivAt h.lipschitz hk hs hxs M
    simpa only [toLp_ofLp, add_sub_cancel] using this

/-- **The two-sequence induction of Dennis–Schnabel Theorem 8.2.2** (local linear convergence of
Broyden's method). With `‖J z⁻¹‖ ≤ β` and thresholds `ε`, `δ` such that `12 β δ ≤ 1`,
`3 L ε ≤ 2 δ` (so `3 β L ε ≤ 1 / 6`) and `closedBall z ε ⊆ D`, every start with `‖x₀ - z‖ ≤ ε` and
`‖M₀ - J z‖_F ≤ δ` gives, for all `k`,

`‖x_k - z‖ ≤ ε / 2ᵏ` and `‖M_k - J z‖_F ≤ δ + (3 L / 2) ε (1 - 1 / 2ᵏ)` (in particular `≤ 2δ`).

The step estimate `norm_step_x_sub_le` halves the error because
`(3β / 2) (2δ + L ε / 2) ≤ 1 / 2`, and the bounded deterioration adds at most
`(L / 2) (3 / 2) ε / 2ᵏ` to the Frobenius error, whose sum stays below `δ`. -/
theorem norm_iterate_sub_le_and_frobenius_norm_le (h : LipschitzJacobianRoot F J D z L)
    (e : E ≃L[ℝ] E) (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {ε δ : ℝ} (hε : 0 ≤ ε) (hβδ : 12 * β * δ ≤ 1)
    (hLε : 3 * L * ε ≤ 2 * δ) (hball : closedBall z ε ⊆ D) {x₀ : E} {Q₀ : E →L[ℝ] E}
    (hx₀ : ‖x₀ - z‖ ≤ ε)
    (hQ₀ : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ) (k : ℕ) :
    ‖(iterate F x₀ Q₀ k).x - z‖ ≤ ε / 2 ^ k ∧
      ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - J z‖
        ≤ δ + 3 * L / 2 * ε * (1 - 1 / 2 ^ k) := by
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  have hL0 : 0 ≤ L := h.nonneg
  induction k with
  | zero => simpa using ⟨hx₀, hQ₀⟩
  | succ k ih =>
    obtain ⟨ihx, ihM⟩ := ih
    set x : E := (iterate F x₀ Q₀ k).x with hx
    set Q : E →L[ℝ] E := (iterate F x₀ Q₀ k).Q with hQ
    set M : Matrix n n ℝ := (toEuclideanCLM (𝕜 := ℝ)).symm Q with hM
    have hpow : (0 : ℝ) < 2 ^ k := by positivity
    have ha0 : 0 ≤ ε / 2 ^ k := by positivity
    have haε : ε / 2 ^ k ≤ ε := div_le_self hε (one_le_pow₀ (by norm_num))
    have hsucc : ε / 2 ^ (k + 1) = ε / 2 ^ k / 2 := by rw [pow_succ, div_div]
    have h2k : (1 : ℝ) / 2 ^ (k + 1) = 1 / 2 ^ k / 2 := by rw [pow_succ, div_div]
    have hxD : x ∈ D := hball (by
      rw [mem_closedBall, dist_eq_norm]
      exact ihx.trans haε)
    -- the operator error is at most the Frobenius error, at most `2δ`
    have hM2 : ‖M - J z‖ ≤ 2 * δ := by
      have : 3 * L / 2 * ε * (1 - 1 / 2 ^ k) ≤ 3 * L / 2 * ε := by
        have h1 : 0 ≤ 3 * L / 2 * ε := by positivity
        have h2 : 0 ≤ (1 : ℝ) / 2 ^ k := by positivity
        nlinarith
      linarith
    have hQJ : ‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ 2 * δ := by
      rw [hQ, iterate_Q_sub_eq, ← hQ, ← hM]
      exact (norm_toEuclideanCLM_le_frobenius_norm _).trans hM2
    have hQJ0 : 0 ≤ ‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ := norm_nonneg _
    -- one step
    obtain ⟨-, hstep⟩ := norm_step_x_sub_le h e he hβ hxD (Q := Q) (by nlinarith)
    have hxk1 : (iterate F x₀ Q₀ (k + 1)).x = (step F ⟨x, Q⟩).x := by
      rw [iterate_succ]
    have hx' : ‖(iterate F x₀ Q₀ (k + 1)).x - z‖ ≤ ε / 2 ^ (k + 1) := by
      rw [hxk1, hsucc]
      refine hstep.trans ?_
      have hxz : 0 ≤ ‖x - z‖ := norm_nonneg _
      have hcoef : 3 * β / 2 * (‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ + L / 2 * ‖x - z‖) ≤ 1 / 2 := by
        have h1 : ‖x - z‖ ≤ ε := ihx.trans haε
        nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hβ0 hL0)]
      calc 3 * β / 2 * (‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ + L / 2 * ‖x - z‖) * ‖x - z‖
          ≤ 1 / 2 * ‖x - z‖ := mul_le_mul_of_nonneg_right hcoef hxz
        _ ≤ 1 / 2 * (ε / 2 ^ k) := mul_le_mul_of_nonneg_left ihx (by norm_num)
        _ = ε / 2 ^ k / 2 := by ring
    refine ⟨hx', ?_⟩
    -- bounded deterioration
    have hx'D : (iterate F x₀ Q₀ (k + 1)).x ∈ D := hball (by
      rw [mem_closedBall, dist_eq_norm]
      refine hx'.trans ?_
      rw [hsucc]
      linarith)
    have hdet := frobenius_norm_symm_iterate_succ_sub_le h hxD hx'D
    rw [← hx, ← hQ, ← hM] at hdet
    refine hdet.trans ?_
    rw [hsucc] at hx'
    have hrest : L / 2 * (‖(iterate F x₀ Q₀ (k + 1)).x - z‖ + ‖x - z‖)
        ≤ L / 2 * (ε / 2 ^ k / 2 + ε / 2 ^ k) :=
      mul_le_mul_of_nonneg_left (add_le_add hx' ihx) (by positivity)
    have hgeom : δ + 3 * L / 2 * ε * (1 - 1 / 2 ^ k) + L / 2 * (ε / 2 ^ k / 2 + ε / 2 ^ k)
        = δ + 3 * L / 2 * ε * (1 - 1 / 2 ^ (k + 1)) := by
      rw [h2k]
      field_simp
      ring
    linarith

end Iteration

/-! ### The Dennis–Moré condition and superlinear convergence -/

section Superlinear

open scoped Matrix.Norms.Frobenius

/-- **The Dennis–Moré inequality along Broyden's iteration**: with `η_k = ‖(Q_k - J z) s_k‖ / ‖s_k‖`
the relative error of the Jacobian approximation along the step `s_k = x_{k+1} - x_k`, and
`x_k, x_{k+1} ∈ D`,

`η_k² ≤ 2 ‖M_k - J z‖_F (‖M_k - J z‖_F - ‖M_{k+1} - J z‖_F + (L / 2) (‖x_k - z‖ + ‖x_{k+1} - z‖))`.

This is `Matrix.sq_norm_sub_mulVec_div_le_broydenUpdate` with the secant remainder bounded by the
mean value inequality; a zero step gives `η_k = 0` and `M_{k+1} = M_k`. -/
theorem sq_norm_iterate_sub_apply_div_le (h : LipschitzJacobianRoot F J D z L) {x₀ : E}
    {Q₀ : E →L[ℝ] E} {k : ℕ} (hk : (iterate F x₀ Q₀ k).x ∈ D)
    (hk1 : (iterate F x₀ Q₀ (k + 1)).x ∈ D) :
    (‖((iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) (J z))
        ((iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x)‖
        / ‖(iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x‖) ^ 2
      ≤ 2 * ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - J z‖
        * (‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - J z‖
            - ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ (k + 1)).Q - J z‖
            + L / 2 * (‖(iterate F x₀ Q₀ k).x - z‖ + ‖(iterate F x₀ Q₀ (k + 1)).x - z‖)) := by
  set x : E := (iterate F x₀ Q₀ k).x with hx
  set x' : E := (iterate F x₀ Q₀ (k + 1)).x with hx'
  set Q : E →L[ℝ] E := (iterate F x₀ Q₀ k).Q with hQ
  set M : Matrix n n ℝ := (toEuclideanCLM (𝕜 := ℝ)).symm Q with hM
  set Js : E →L[ℝ] E := toEuclideanCLM (𝕜 := ℝ) (J z) with hJs
  have hM' : (toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ (k + 1)).Q
      = broydenUpdate M (ofLp (x' - x)) (ofLp (F x' - F x)) := symm_iterate_succ_Q F x₀ Q₀ k
  rw [hM']
  have hnn : 0 ≤ 2 * ‖M - J z‖ := by positivity
  have hL0 := h.nonneg
  by_cases hs : x' - x = 0
  · have hs0 : ofLp (x' - x) = 0 := by rw [hs]; rfl
    rw [hs0, hs, broydenUpdate_zero_left, map_zero, norm_zero, div_zero, sub_self, zero_add,
      zero_pow two_ne_zero]
    have : 0 ≤ ‖x - z‖ + ‖x' - z‖ := by positivity
    positivity
  · have hs' : ofLp (x' - x) ≠ 0 := fun h0 => hs (by simpa using congrArg (toLp 2) h0)
    have key := sq_norm_sub_mulVec_div_le_broydenUpdate M (J z) (y := ofLp (F x' - F x)) hs'
    have e1 : toLp 2 ((M - J z) *ᵥ ofLp (x' - x)) = (Q - Js) (x' - x) := by
      rw [← toEuclideanCLM_toLp, toLp_ofLp]
      congr 1
      rw [map_sub, hM, StarAlgEquiv.apply_symm_apply]
    have e3 : toLp 2 (ofLp (F x' - F x) - J z *ᵥ ofLp (x' - x)) = F x' - F x - Js (x' - x) := by
      rw [toLp_sub, toLp_ofLp, ← toEuclideanCLM_toLp, toLp_ofLp]
    rw [e1, toLp_ofLp, e3] at key
    rw [div_pow]
    refine key.trans ?_
    have hmv := h.norm_sub_sub_apply_le hk hk1
    have hs0 : 0 < ‖x' - x‖ := norm_pos_iff.2 hs
    have hq : ‖F x' - F x - Js (x' - x)‖ / ‖x' - x‖ ≤ L / 2 * (‖x - z‖ + ‖x' - z‖) := by
      rw [div_le_iff₀ hs0]
      exact hmv
    gcongr

/-- The Dennis–Moré quotient `η_k = ‖(Q_k - J z) s_k‖ / ‖s_k‖` of Broyden's iteration. -/
noncomputable def dennisMoreQuotient (F : E → E) (J : E → Matrix n n ℝ) (z x₀ : E)
    (Q₀ : E →L[ℝ] E) (k : ℕ) : ℝ :=
  ‖((iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) (J z))
      ((iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x)‖
    / ‖(iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x‖

/-- The Dennis–Moré quotient is nonnegative. -/
theorem dennisMoreQuotient_nonneg (F : E → E) (J : E → Matrix n n ℝ) (z x₀ : E)
    (Q₀ : E →L[ℝ] E) (k : ℕ) : 0 ≤ dennisMoreQuotient F J z x₀ Q₀ k :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- `‖(Q_k - J z) s_k‖ ≤ η_k ‖s_k‖`, with equality unless `s_k = 0`. -/
theorem norm_sub_apply_le_dennisMoreQuotient_mul (F : E → E) (J : E → Matrix n n ℝ) (z x₀ : E)
    (Q₀ : E →L[ℝ] E) (k : ℕ) :
    ‖((iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) (J z))
        ((iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x)‖
      ≤ dennisMoreQuotient F J z x₀ Q₀ k
        * ‖(iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x‖ := by
  rw [dennisMoreQuotient]
  by_cases hs : (iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x = 0
  · rw [hs, map_zero, norm_zero, div_zero, zero_mul]
  · rw [div_mul_cancel₀ _ (norm_ne_zero_iff.2 hs)]

/-- **The Dennis–Moré condition holds along Broyden's iteration** (Dennis–Schnabel, proof of
Theorem 8.2.2): under the thresholds of `norm_iterate_sub_le_and_frobenius_norm_le`,
`η_k = ‖(Q_k - J z) s_k‖ / ‖s_k‖ → 0`. Summing `sq_norm_iterate_sub_apply_div_le` telescopes
the Frobenius errors, whose total variation is at most `‖M₀ - J z‖_F + (L / 2) ∑ (‖x_k - z‖ +
‖x_{k+1} - z‖) ≤ δ + 2 L ε`, so `∑ η_k² ≤ 4δ (δ + 2 L ε) < ∞`. -/
theorem tendsto_dennisMoreQuotient (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {ε δ : ℝ} (hε : 0 ≤ ε) (hβδ : 12 * β * δ ≤ 1)
    (hLε : 3 * L * ε ≤ 2 * δ) (hball : closedBall z ε ⊆ D) {x₀ : E} {Q₀ : E →L[ℝ] E}
    (hx₀ : ‖x₀ - z‖ ≤ ε) (hQ₀ : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ) :
    Tendsto (dennisMoreQuotient F J z x₀ Q₀) atTop (𝓝 0) := by
  have hinv := norm_iterate_sub_le_and_frobenius_norm_le h e he hβ hε hβδ hLε hball hx₀ hQ₀
  have hL0 := h.nonneg
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hQ₀
  set η := dennisMoreQuotient F J z x₀ Q₀ with hη
  set xs : ℕ → E := fun k => (iterate F x₀ Q₀ k).x with hxs
  set Ms : ℕ → Matrix n n ℝ := fun k => (toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q
    with hMs
  have hpow : ∀ k, ε / 2 ^ k = ε * (1 / 2 : ℝ) ^ k := fun k => by
    rw [_root_.one_div_pow, div_eq_mul_one_div]
  have hxk : ∀ k, xs k ∈ D := fun k => hball (by
    rw [mem_closedBall, dist_eq_norm]
    exact (hinv k).1.trans (div_le_self hε (one_le_pow₀ (by norm_num))))
  have hM2 : ∀ k, ‖Ms k - J z‖ ≤ 2 * δ := fun k => by
    have h1 : 3 * L / 2 * ε * (1 - 1 / 2 ^ k) ≤ 3 * L / 2 * ε := by
      have : 0 ≤ 3 * L / 2 * ε := by positivity
      have : 0 ≤ (1 : ℝ) / 2 ^ k := by positivity
      nlinarith
    linarith [(hinv k).2]
  -- the bracket of the Dennis–Moré inequality, nonnegative by bounded deterioration
  set b : ℕ → ℝ := fun k => ‖Ms k - J z‖ - ‖Ms (k + 1) - J z‖
    + L / 2 * (‖xs k - z‖ + ‖xs (k + 1) - z‖) with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    have := frobenius_norm_symm_iterate_succ_sub_le h (hxk k) (hxk (k + 1))
    simp only [hb]
    linarith
  have hη2 : ∀ k, η k ^ 2 ≤ 4 * δ * b k := fun k => by
    have h1 := sq_norm_iterate_sub_apply_div_le h (hxk k) (hxk (k + 1))
    have h2 : 2 * ‖Ms k - J z‖ * b k ≤ 4 * δ * b k := by
      have := hM2 k
      have := hb0 k
      nlinarith
    exact h1.trans h2
  -- the partial sums of the bracket telescope
  have hsum : ∀ N, ∑ k ∈ Finset.range N, b k ≤ δ + 2 * L * ε := fun N => by
    have htel : ∑ k ∈ Finset.range N, (‖Ms k - J z‖ - ‖Ms (k + 1) - J z‖)
        = ‖Ms 0 - J z‖ - ‖Ms N - J z‖ := Finset.sum_range_sub' (fun k => ‖Ms k - J z‖) N
    have hgeo : ∑ k ∈ Finset.range N, (‖xs k - z‖ + ‖xs (k + 1) - z‖) ≤ 4 * ε := by
      calc ∑ k ∈ Finset.range N, (‖xs k - z‖ + ‖xs (k + 1) - z‖)
          ≤ ∑ k ∈ Finset.range N, 2 * ε * (1 / 2 : ℝ) ^ k := by
            refine Finset.sum_le_sum fun k _ => ?_
            have h1 := (hinv k).1
            have h2 := (hinv (k + 1)).1
            rw [hpow] at h1 h2
            have h3 : ε * (1 / 2 : ℝ) ^ (k + 1) ≤ ε * (1 / 2 : ℝ) ^ k := by
              rw [pow_succ]
              have : 0 ≤ ε * (1 / 2 : ℝ) ^ k := by positivity
              linarith
            linarith
        _ = 2 * ε * ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
        _ ≤ 2 * ε * 2 := by gcongr; exact sum_geometric_two_le N
        _ = 4 * ε := by ring
    have hM0 : ‖Ms 0 - J z‖ ≤ δ := hQ₀
    have hMN : 0 ≤ ‖Ms N - J z‖ := norm_nonneg _
    calc ∑ k ∈ Finset.range N, b k
        = ∑ k ∈ Finset.range N, (‖Ms k - J z‖ - ‖Ms (k + 1) - J z‖)
          + L / 2 * ∑ k ∈ Finset.range N, (‖xs k - z‖ + ‖xs (k + 1) - z‖) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ ≤ δ + L / 2 * (4 * ε) := by
          rw [htel]
          gcongr
          linarith
      _ = δ + 2 * L * ε := by ring
  have hsum2 : ∀ N, ∑ k ∈ Finset.range N, η k ^ 2 ≤ 4 * δ * (δ + 2 * L * ε) := fun N =>
    (Finset.sum_le_sum fun k _ => hη2 k).trans (by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hsum N) (by positivity))
  have hsumm : Summable fun k => η k ^ 2 :=
    summable_of_sum_range_le (fun k => sq_nonneg _) hsum2
  have h0 := hsumm.tendsto_atTop_zero.sqrt
  rw [Real.sqrt_zero] at h0
  exact h0.congr fun k => Real.sqrt_sq (dennisMoreQuotient_nonneg F J z x₀ Q₀ k)

/-- **The superlinear step bound** (Dennis–Schnabel Lemma 8.2.3 / Theorem 8.2.4, the "if" half
of the Dennis–Moré characterization, made quantitative): under the thresholds of
`norm_iterate_sub_le_and_frobenius_norm_le`,

`‖x_{k+1} - z‖ ≤ 4β (η_k + L ‖x_k - z‖) ‖x_k - z‖`.

From `Q_k s_k = -F x_k`, `F x_{k+1} = (F x_{k+1} - F x_k - J z s_k) - (Q_k - J z) s_k`, so
`‖F x_{k+1}‖ ≤ (η_k + L ‖x_k - z‖) ‖s_k‖` with `‖s_k‖ ≤ 2 ‖x_k - z‖`, while
`‖x_{k+1} - z‖ ≤ β ‖J z (x_{k+1} - z)‖ ≤ β (‖F x_{k+1}‖ + (L / 2) ‖x_{k+1} - z‖²)` and
`β L ‖x_{k+1} - z‖ ≤ 1 / 3`. -/
theorem norm_iterate_succ_sub_le_mul (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {ε δ : ℝ} (hε : 0 ≤ ε) (hβδ : 12 * β * δ ≤ 1)
    (hLε : 3 * L * ε ≤ 2 * δ) (hball : closedBall z ε ⊆ D) {x₀ : E} {Q₀ : E →L[ℝ] E}
    (hx₀ : ‖x₀ - z‖ ≤ ε) (hQ₀ : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ) (k : ℕ) :
    ‖(iterate F x₀ Q₀ (k + 1)).x - z‖
      ≤ 4 * β * (dennisMoreQuotient F J z x₀ Q₀ k + L * ‖(iterate F x₀ Q₀ k).x - z‖)
        * ‖(iterate F x₀ Q₀ k).x - z‖ := by
  have hinv := norm_iterate_sub_le_and_frobenius_norm_le h e he hβ hε hβδ hLε hball hx₀ hQ₀
  have hL0 := h.nonneg
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hQ₀
  set x : E := (iterate F x₀ Q₀ k).x with hx
  set x' : E := (iterate F x₀ Q₀ (k + 1)).x with hx'
  set Q : E →L[ℝ] E := (iterate F x₀ Q₀ k).Q with hQ
  set Js : E →L[ℝ] E := toEuclideanCLM (𝕜 := ℝ) (J z) with hJs
  set η : ℝ := dennisMoreQuotient F J z x₀ Q₀ k with hηdef
  have hη0 : 0 ≤ η := dennisMoreQuotient_nonneg F J z x₀ Q₀ k
  have hηs : ‖(Q - Js) (x' - x)‖ ≤ η * ‖x' - x‖ :=
    norm_sub_apply_le_dennisMoreQuotient_mul F J z x₀ Q₀ k
  have hxε : ‖x - z‖ ≤ ε := (hinv k).1.trans (div_le_self hε (one_le_pow₀ (by norm_num)))
  have hx'ε : ‖x' - z‖ ≤ ε := (hinv (k + 1)).1.trans (div_le_self hε (one_le_pow₀ (by norm_num)))
  have hxD : x ∈ D := hball (by rw [mem_closedBall, dist_eq_norm]; exact hxε)
  have hx'D : x' ∈ D := hball (by rw [mem_closedBall, dist_eq_norm]; exact hx'ε)
  -- the operator error is at most `2δ`, so the step lemma applies
  have hQJ : ‖Q - Js‖ ≤ 2 * δ := by
    have h1 : 3 * L / 2 * ε * (1 - 1 / 2 ^ k) ≤ 3 * L / 2 * ε := by
      have : 0 ≤ 3 * L / 2 * ε := by positivity
      have : 0 ≤ (1 : ℝ) / 2 ^ k := by positivity
      nlinarith
    rw [hQ, hJs, iterate_Q_sub_eq]
    exact (norm_toEuclideanCLM_le_frobenius_norm _).trans (by linarith [(hinv k).2])
  have hQJ0 : 0 ≤ ‖Q - Js‖ := norm_nonneg _
  obtain ⟨⟨e', he'Q, -⟩, hstep⟩ := norm_step_x_sub_le h e he hβ hxD (Q := Q) (by nlinarith)
  have hxk1 : x' = (step F ⟨x, Q⟩).x := by rw [hx', iterate_succ]
  -- `‖x' - z‖ ≤ ‖x - z‖ / 2`
  have hhalf : ‖x' - z‖ ≤ ‖x - z‖ / 2 := by
    rw [hxk1]
    refine hstep.trans ?_
    have hxz : 0 ≤ ‖x - z‖ := norm_nonneg _
    have hcoef : 3 * β / 2 * (‖Q - Js‖ + L / 2 * ‖x - z‖) ≤ 1 / 2 := by
      have h1 : β * ‖Q - Js‖ ≤ β * (2 * δ) := mul_le_mul_of_nonneg_left hQJ hβ0
      have h2 : β * L * ‖x - z‖ ≤ β * L * ε := mul_le_mul_of_nonneg_left hxε (mul_nonneg hβ0 hL0)
      have h3 : β * (3 * L * ε) ≤ β * (2 * δ) := mul_le_mul_of_nonneg_left hLε hβ0
      linarith
    calc 3 * β / 2 * (‖Q - Js‖ + L / 2 * ‖x - z‖) * ‖x - z‖
        ≤ 1 / 2 * ‖x - z‖ := mul_le_mul_of_nonneg_right hcoef hxz
      _ = ‖x - z‖ / 2 := by ring
  -- the secant equation of the step: `Q s = -F x`
  have hsec : Q (x' - x) = -F x := by
    rw [hxk1]
    exact apply_step_x_sub F ⟨x, Q⟩ e' he'Q
  -- the residual at `x'`
  have hFx' : F x' = (F x' - F x - Js (x' - x)) - (Q - Js) (x' - x) := by
    rw [_root_.sub_apply, hsec]
    abel
  have hmv := h.norm_sub_sub_apply_le hxD hx'D
  have hs : ‖x' - x‖ ≤ 2 * ‖x - z‖ := by
    have : x' - x = (x' - z) - (x - z) := by abel
    rw [this]
    linarith [norm_sub_le (x' - z) (x - z), norm_nonneg (x - z)]
  have hFbound : ‖F x'‖ ≤ (η + L * ‖x - z‖) * (2 * ‖x - z‖) := by
    rw [hFx']
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖F x' - F x - Js (x' - x)‖ ≤ L * ‖x - z‖ * ‖x' - x‖ := by
      refine hmv.trans ?_
      have : L / 2 * (‖x - z‖ + ‖x' - z‖) ≤ L * ‖x - z‖ := by
        linarith [mul_le_mul_of_nonneg_left hhalf hL0, mul_nonneg hL0 (norm_nonneg (x - z))]
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hs0 : 0 ≤ ‖x' - x‖ := norm_nonneg _
    have hxz : 0 ≤ ‖x - z‖ := norm_nonneg _
    linarith [mul_le_mul_of_nonneg_left hs (add_nonneg hη0 (mul_nonneg hL0 hxz))]
  -- the lower bound `‖x' - z‖ ≤ β (‖F x'‖ + (L / 2) ‖x' - z‖²)`
  have hlow : ‖x' - z‖ ≤ β * (‖F x'‖ + L / 2 * ‖x' - z‖ ^ 2) := by
    have h2 : e (x' - z) = Js (x' - z) := by rw [← he]; rfl
    have h3 : Js (x' - z) = F x' - (F x' - Js (x' - z)) := by abel
    have h4 := h.norm_sub_apply_le hx'D
    calc ‖x' - z‖ = ‖(e.symm : E →L[ℝ] E) (e (x' - z))‖ := by simp
      _ ≤ ‖(e.symm : E →L[ℝ] E)‖ * ‖e (x' - z)‖ := (e.symm : E →L[ℝ] E).le_opNorm _
      _ ≤ β * ‖e (x' - z)‖ := mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
      _ ≤ β * (‖F x'‖ + L / 2 * ‖x' - z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hβ0
          rw [h2, h3]
          exact (norm_sub_le _ _).trans (add_le_add le_rfl h4)
  -- `β L ‖x' - z‖ ≤ 1 / 3`
  have hβL : 3 * (β * L * ‖x' - z‖) ≤ 1 := by
    have h1 : β * L * ‖x' - z‖ ≤ β * L * ε := mul_le_mul_of_nonneg_left hx'ε (by positivity)
    have h2 : β * (3 * L * ε) ≤ β * (2 * δ) := mul_le_mul_of_nonneg_left hLε hβ0
    linarith
  have hx'z : 0 ≤ ‖x' - z‖ := norm_nonneg _
  have hxz : 0 ≤ ‖x - z‖ := norm_nonneg _
  have hF0 : 0 ≤ ‖F x'‖ := norm_nonneg _
  -- `(5 / 6) ‖x' - z‖ ≤ β ‖F x'‖`
  have h56 : 5 / 6 * ‖x' - z‖ ≤ β * ‖F x'‖ := by
    have h1 : β * L * ‖x' - z‖ * ‖x' - z‖ ≤ 1 / 3 * ‖x' - z‖ :=
      mul_le_mul_of_nonneg_right (by linarith) hx'z
    have h2 : β * (L / 2 * ‖x' - z‖ ^ 2) ≤ 1 / 6 * ‖x' - z‖ := by linarith
    linarith
  calc ‖x' - z‖ ≤ 6 / 5 * (β * ‖F x'‖) := by linarith
    _ ≤ 6 / 5 * (β * ((η + L * ‖x - z‖) * (2 * ‖x - z‖))) := by gcongr
    _ ≤ 4 * β * (η + L * ‖x - z‖) * ‖x - z‖ := by
        have : 0 ≤ β * ((η + L * ‖x - z‖) * ‖x - z‖) := by positivity
        linarith

end Superlinear

/-! ### The convergence theorem -/

section Main

open scoped Matrix.Norms.Frobenius

/-- `ε / 2ᵏ → 0`. -/
theorem tendsto_div_two_pow (ε : ℝ) : Tendsto (fun k : ℕ => ε / 2 ^ k) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- **Local superlinear convergence of Broyden's method, quantitative form** (Dennis–Moré 1974;
Dennis–Schnabel Theorem 8.2.2; [quarteroni2000numerical] Property 7.2). Let `F` have a
Lipschitz Jacobian at a root `z` on a convex `D` (`LipschitzJacobianRoot`), with
`‖J z⁻¹‖ ≤ β`, and let `ε`, `δ` satisfy `12 β δ ≤ 1`, `3 L ε ≤ 2 δ` and `closedBall z ε ⊆ D`.
Then for every start `x₀` with `‖x₀ - z‖ ≤ ε` and every `Q₀` whose matrix is within `δ` of
`J z` in the Frobenius norm, Broyden's iteration `Broyden.iterate F x₀ Q₀` is well defined
(every `Q_k` is invertible), converges to `z` at least linearly, `‖x_k - z‖ ≤ ε / 2ᵏ`, and
superlinearly: `‖x_{k+1} - z‖ ≤ c_k ‖x_k - z‖` with `c_k = 4β (η_k + L ε / 2ᵏ) → 0`, where
`η_k → 0` is the Dennis–Moré quotient (`tendsto_dennisMoreQuotient`). -/
theorem superlinear_of_le (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {ε δ : ℝ} (hε : 0 ≤ ε) (hβδ : 12 * β * δ ≤ 1)
    (hLε : 3 * L * ε ≤ 2 * δ) (hball : closedBall z ε ⊆ D) {x₀ : E} {Q₀ : E →L[ℝ] E}
    (hx₀ : ‖x₀ - z‖ ≤ ε) (hQ₀ : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ) :
    (∀ k, ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = (iterate F x₀ Q₀ k).Q) ∧
      (∀ k, ‖(iterate F x₀ Q₀ k).x - z‖ ≤ ε / 2 ^ k) ∧
      Tendsto (fun k => (iterate F x₀ Q₀ k).x) atTop (𝓝 z) ∧
      ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧
        ∀ k, ‖(iterate F x₀ Q₀ (k + 1)).x - z‖ ≤ c k * ‖(iterate F x₀ Q₀ k).x - z‖ := by
  have hinv := norm_iterate_sub_le_and_frobenius_norm_le h e he hβ hε hβδ hLε hball hx₀ hQ₀
  have hL0 := h.nonneg
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hQ₀
  -- every `Q_k` is invertible
  have hunit : ∀ k, ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = (iterate F x₀ Q₀ k).Q := fun k => by
    have hxD : (iterate F x₀ Q₀ k).x ∈ D := hball (by
      rw [mem_closedBall, dist_eq_norm]
      exact (hinv k).1.trans (div_le_self hε (one_le_pow₀ (by norm_num))))
    have hQJ : ‖(iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ 2 * δ := by
      have h1 : 3 * L / 2 * ε * (1 - 1 / 2 ^ k) ≤ 3 * L / 2 * ε := by
        have : 0 ≤ 3 * L / 2 * ε := by positivity
        have : 0 ≤ (1 : ℝ) / 2 ^ k := by positivity
        nlinarith
      rw [iterate_Q_sub_eq]
      exact (norm_toEuclideanCLM_le_frobenius_norm _).trans (by linarith [(hinv k).2])
    have hQJ0 : 0 ≤ ‖(iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ := norm_nonneg _
    obtain ⟨⟨e', he', -⟩, -⟩ := norm_step_x_sub_le h e he hβ hxD (Q := (iterate F x₀ Q₀ k).Q)
      (by nlinarith)
    exact ⟨e', he'⟩
  -- convergence
  have hlim : Tendsto (fun k => (iterate F x₀ Q₀ k).x) atTop (𝓝 z) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hinv k).1) (tendsto_div_two_pow ε)
  refine ⟨hunit, fun k => (hinv k).1, hlim,
    ⟨fun k => 4 * β * (dennisMoreQuotient F J z x₀ Q₀ k + L * (ε / 2 ^ k)), ?_, fun k => ?_⟩⟩
  · have h1 := tendsto_dennisMoreQuotient h e he hβ hε hβδ hLε hball hx₀ hQ₀
    have h2 := ((h1.add ((tendsto_div_two_pow ε).const_mul L)).const_mul (4 * β))
    simpa using h2
  · refine (norm_iterate_succ_sub_le_mul h e he hβ hε hβδ hLε hball hx₀ hQ₀ k).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
      (norm_nonneg _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hinv k).1 hL0)

/-- **Local superlinear convergence of Broyden's method** (Dennis–Moré 1974; Dennis–Schnabel
Theorem 8.2.2; [quarteroni2000numerical] Property 7.2), existential form. Let `F` have a
Lipschitz Jacobian at a root `z` on a convex `D ⊇ ball z R` (`LipschitzJacobianRoot`), with
`J z` invertible and `‖J z⁻¹‖ ≤ β`, `β > 0`, `R > 0`. Then there are `ε, γ > 0` such that for every
`x₀` with `‖x₀ - z‖ ≤ ε` and every `Q₀` with `‖Q₀ - J z‖ ≤ γ` (operator norm), Broyden's
iteration from `(x₀, Q₀)` is well defined, converges to `z` with `‖x_k - z‖ ≤ ε / 2ᵏ`, and
converges superlinearly: `‖x_{k+1} - z‖ ≤ c_k ‖x_k - z‖` with `c_k → 0`. The thresholds are
`δ = 1 / (12 β)`, `ε = min (R / 2) (2δ / (3 (L + 1)))`, `γ = δ / (√n + 1)`, the last converting
the operator-norm hypothesis to the Frobenius one of `superlinear_of_le`. -/
theorem exists_superlinear (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) (hβ0 : 0 < β) {R : ℝ} (hR : 0 < R)
    (hRD : ball z R ⊆ D) :
    ∃ ε > 0, ∃ γ > 0, ∀ (x₀ : E) (Q₀ : E →L[ℝ] E), ‖x₀ - z‖ ≤ ε →
      ‖Q₀ - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ γ →
      (∀ k, ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = (iterate F x₀ Q₀ k).Q) ∧
        (∀ k, ‖(iterate F x₀ Q₀ k).x - z‖ ≤ ε / 2 ^ k) ∧
        Tendsto (fun k => (iterate F x₀ Q₀ k).x) atTop (𝓝 z) ∧
        ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧
          ∀ k, ‖(iterate F x₀ Q₀ (k + 1)).x - z‖ ≤ c k * ‖(iterate F x₀ Q₀ k).x - z‖ := by
  have hL0 := h.nonneg
  set δ : ℝ := 1 / (12 * β) with hδ
  have hδ0 : 0 < δ := by positivity
  set ε : ℝ := min (R / 2) (2 * δ / (3 * (L + 1))) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  set c : ℝ := √(Fintype.card n : ℝ) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  set γ : ℝ := δ / (c + 1) with hγ
  have hγ0 : 0 < γ := by positivity
  refine ⟨ε, hε0, γ, hγ0, fun x₀ Q₀ hx₀ hQ₀ => ?_⟩
  have hβδ : 12 * β * δ ≤ 1 := by
    rw [hδ, mul_one_div, div_self (by positivity)]
  have hLε : 3 * L * ε ≤ 2 * δ := by
    have h1 : ε ≤ 2 * δ / (3 * (L + 1)) := min_le_right _ _
    have h2 : 3 * L * ε ≤ 3 * L * (2 * δ / (3 * (L + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine h2.trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hball : closedBall z ε ⊆ D := by
    refine (closedBall_subset_ball ?_).trans hRD
    have := min_le_left (R / 2) (2 * δ / (3 * (L + 1)))
    linarith
  have hQ₀' : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ := by
    have h1 := frobenius_norm_le_sqrt_card_mul_norm_toEuclideanCLM
      ((toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z)
    rw [map_sub, StarAlgEquiv.apply_symm_apply] at h1
    refine h1.trans ?_
    calc c * ‖Q₀ - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ c * γ :=
          mul_le_mul_of_nonneg_left hQ₀ hc0
      _ = δ * (c / (c + 1)) := by rw [hγ]; ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) hδ0.le
      _ = δ := mul_one δ
  exact superlinear_of_le h e he hβ hε0.le hβδ hLε hball hx₀ hQ₀'

end Main

end Broyden
