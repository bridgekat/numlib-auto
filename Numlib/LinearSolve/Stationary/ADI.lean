import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.LinearSolve.Stationary.Splitting

/-!
# The alternating direction implicit iteration

The Peaceman–Rachford sweep splits a two-term operator `H + V` into two half-steps, each of
which inverts only one of the terms:

`(H + r) x_{k+1/2} = (r - V) x_k + b`,   `(V + r) x_{k+1} = (r - H) x_{k+1/2} + b`.

Composing them is the affine iteration `x ↦ P x + f` with
`P = (V + r)⁻¹ (H - r) (H + r)⁻¹ (V - r)` (`Stationary.peacemanRachford`) and
`f = (V + r)⁻¹ (1 - (H - r)(H + r)⁻¹) b` (`Stationary.peacemanRachfordConst`), and it comes from
the splitting `H + V = M - N` with `M = (2r)⁻¹ (H + r)(V + r)` and `N = (2r)⁻¹ (H - r)(V - r)`
(`Stationary.peacemanRachfordSplitting`).

**The whole convergence proof is one inequality.**  For `A` with `re ⟪A x, x⟫ ≥ c ‖x‖²` and
`r > 0`,

`‖A x - r x‖² + 4 r c ‖x‖² ≤ ‖A x + r x‖²`,

which is nothing but the expansion of both sides
(`Stationary.norm_sub_smul_sq_add_le_norm_add_smul_sq`).  It says that the Cayley transform
`(A - r)(A + r)⁻¹` is a strict contraction, with the explicit factor
`1 - 4 r c / (‖A‖ + r)²` (`Stationary.norm_cayley_lt_one`).  Conjugating `P` by `V + r` turns it
into the product of the two Cayley transforms of `H` and of `V`, so that product is a strict
contraction, `P` is similar to it, and the iterates converge from any starting vector
(`Stationary.tendsto_peacemanRachford`).

Three things the usual framing obscures.

* **No commutativity of `H` and `V` is used anywhere.**  The commutativity hypothesis of the
  literature belongs to the theory of the optimal parameter *sequence*, which is not treated
  here; the splitting identity `M - N = H + V` needs none of it either, the `H V` terms
  cancelling on their own.
* **No symmetry is used either.**  Coercivity alone — `re ⟪H x, x⟫ ≥ c ‖x‖²` with `c > 0`,
  which is what "symmetric positive definite" gives — carries the whole argument, so the
  theorem covers nonsymmetric `H` and `V` as well.
* **`‖P‖ < 1` is false in general**, and only the *conjugated* operator
  `(V + r) P (V + r)⁻¹` is a contraction in the operator norm
  (`Stationary.norm_conj_peacemanRachford_lt_one`).  What `P` itself satisfies is the spectral
  radius bound `Stationary.spectralRadius_peacemanRachford_lt_one`, and that is what convergence
  rests on.

Everything is stated in an inner product space, complete where an inverse is needed; matrices
reach it through `Matrix.toEuclideanCLM`.  The Cayley inequality is an upstreaming candidate on
its own and should move beside the coercivity API as soon as a second consumer appears.

This is Saad, *Iterative Methods for Sparse Linear Systems*[^saad-iterative], §4.3: Algorithm 4.3
and the identities (4.50)–(4.52).  The book states no numbered result there and asserts the
convergence claim in one sentence.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

open Filter Topology

namespace Stationary

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### The Cayley contraction inequality -/

/-- The inequality behind every statement in this file: for `A` coercive with constant `c` and
`r > 0`, `‖A x - r x‖² + 4 r c ‖x‖² ≤ ‖A x + r x‖²`.  Both sides expand to
`‖A x‖² ± 2 r re ⟪A x, x⟫ + r² ‖x‖²`, so the whole content is that the cross term is bounded
below by coercivity.  Neither symmetry, nor completeness, nor finite dimension is used. -/
theorem norm_sub_smul_sq_add_le_norm_add_smul_sq {A : E →ₗ[𝕜] E} {c : ℝ}
    (hA : A.IsCoerciveWith c) {r : ℝ} (hr : 0 < r) (x : E) :
    ‖A x - (r : 𝕜) • x‖ ^ 2 + 4 * r * c * ‖x‖ ^ 2 ≤ ‖A x + (r : 𝕜) • x‖ ^ 2 := by
  have h1 : RCLike.re (inner 𝕜 (A x) ((r : 𝕜) • x)) = r * RCLike.re (inner 𝕜 (A x) x) := by
    rw [inner_smul_right, RCLike.re_ofReal_mul]
  have h2 : ‖((r : 𝕜) • x)‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hr, mul_pow]
  rw [norm_add_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜), h1, h2]
  nlinarith [hA x]

/-- The strict form of the Cayley inequality away from the origin. -/
theorem norm_sub_smul_lt_norm_add_smul {A : E →ₗ[𝕜] E} {c : ℝ} (hA : A.IsCoerciveWith c)
    (hc : 0 < c) {r : ℝ} (hr : 0 < r) {x : E} (hx : x ≠ 0) :
    ‖A x - (r : 𝕜) • x‖ < ‖A x + (r : 𝕜) • x‖ := by
  have hx' : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
  have h := norm_sub_smul_sq_add_le_norm_add_smul_sq hA hr x
  have hpos : (0 : ℝ) < 4 * r * c * ‖x‖ ^ 2 := by positivity
  have hlt : ‖A x - (r : 𝕜) • x‖ ^ 2 < ‖A x + (r : 𝕜) • x‖ ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt

/-- `A + r` is coercive with constant `c + r`, since the shift adds `r ‖x‖²` to the quadratic
form. -/
theorem isCoerciveWith_add_smul_one {A : E →L[𝕜] E} {c : ℝ}
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {r : ℝ} :
    ((A + (r : 𝕜) • (1 : E →L[𝕜] E) : E →L[𝕜] E) : E →ₗ[𝕜] E).IsCoerciveWith (c + r) := by
  intro x
  have happ : (A + (r : 𝕜) • (1 : E →L[𝕜] E)) x = A x + (r : 𝕜) • x := by simp
  have h1 : RCLike.re (inner 𝕜 ((r : 𝕜) • x) x) = r * ‖x‖ ^ 2 := by
    rw [inner_smul_left, RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul, RCLike.ofReal_re]
  have hq : c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x) := hA x
  rw [ContinuousLinearMap.coe_coe, happ, inner_add_left, map_add, h1, add_mul]
  linarith

/-! ### The Cayley transform of a coercive operator -/

section Cayley

variable [CompleteSpace E]

/-- `A + r` is invertible for a coercive `A` and `r > 0`: it is coercive with constant `c + r`,
and Lax–Milgram supplies the inverse. -/
theorem isUnit_add_smul_one {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {r : ℝ} (hr : 0 < r) :
    IsUnit (A + (r : 𝕜) • (1 : E →L[𝕜] E)) := by
  obtain ⟨e, he, -⟩ := ContinuousLinearMap.exists_equiv_of_isCoerciveWith
    (by linarith : (0 : ℝ) < c + r) (isCoerciveWith_add_smul_one hA (r := r))
  refine ⟨(ContinuousLinearEquiv.unitsEquiv 𝕜 E).symm e, ?_⟩
  rw [← he]
  ext x
  rw [← ContinuousLinearEquiv.unitsEquiv_apply 𝕜 E, MulEquiv.apply_symm_apply]
  rfl

/-- The Cayley transform is a pointwise strict contraction, with the explicit factor
`1 - 4 r c / (‖A‖ + r)²`.  Applying the Cayley inequality at `x = (A + r)⁻¹ y` and using
`‖y‖ ≤ (‖A‖ + r) ‖x‖` is the whole proof. -/
theorem norm_cayley_apply_sq_le {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {r : ℝ} (hr : 0 < r) (y : E) :
    ‖((A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)) y‖ ^ 2
      ≤ (1 - 4 * r * c / (‖A‖ + r) ^ 2) * ‖y‖ ^ 2 := by
  have hu : IsUnit (A + (r : 𝕜) • (1 : E →L[𝕜] E)) := isUnit_add_smul_one hc hA hr
  have hSx : (A + (r : 𝕜) • (1 : E →L[𝕜] E)) (Ring.inverse (A + (r : 𝕜) • 1) y) = y := by
    have h := Ring.mul_inverse_cancel _ hu
    calc (A + (r : 𝕜) • (1 : E →L[𝕜] E)) (Ring.inverse (A + (r : 𝕜) • 1) y)
        = ((A + (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)) y := rfl
      _ = y := by rw [h]; rfl
  set x : E := Ring.inverse (A + (r : 𝕜) • 1) y with hxdef
  have hsum : A x + (r : 𝕜) • x = y := by simpa using hSx
  have hLHS : ((A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)) y = A x - (r : 𝕜) • x := by
    simp [hxdef]
  have hkey : ‖A x - (r : 𝕜) • x‖ ^ 2 + 4 * r * c * ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    have h := norm_sub_smul_sq_add_le_norm_add_smul_sq hA hr x
    simp only [ContinuousLinearMap.coe_coe] at h
    rwa [hsum] at h
  have hd : (0 : ℝ) < ‖A‖ + r := by positivity
  have hnormS : ‖A + (r : 𝕜) • (1 : E →L[𝕜] E)‖ ≤ ‖A‖ + r := by
    refine (norm_add_le _ _).trans ?_
    have hone : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have : ‖(r : 𝕜) • (1 : E →L[𝕜] E)‖ ≤ r := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hr]
      nlinarith
    linarith
  have hlow : ‖y‖ ≤ (‖A‖ + r) * ‖x‖ := by
    rw [← hSx]
    calc ‖(A + (r : 𝕜) • (1 : E →L[𝕜] E)) x‖
        ≤ ‖A + (r : 𝕜) • (1 : E →L[𝕜] E)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ x
      _ ≤ (‖A‖ + r) * ‖x‖ := by gcongr
  have hy2 : ‖y‖ ^ 2 ≤ (‖A‖ + r) ^ 2 * ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg y, norm_nonneg x]
  have h4rc : (0 : ℝ) ≤ 4 * r * c := by positivity
  have hq : 4 * r * c / (‖A‖ + r) ^ 2 * ‖y‖ ^ 2 ≤ 4 * r * c * ‖x‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hy2 h4rc]
  rw [hLHS, sub_mul, one_mul]
  linarith

/-- The Cayley transform `(A - r)(A + r)⁻¹` of a coercive operator is a strict contraction.
This is the Mathlib-shaped statement of the file, and an upstreaming candidate on its own. -/
theorem norm_cayley_lt_one {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {r : ℝ} (hr : 0 < r) :
    ‖(A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)‖ < 1 := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hz : ((A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)) = 0 := by
      ext x; exact Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact zero_lt_one
  · obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hv' : (0 : ℝ) < ‖v‖ := norm_pos_iff.2 hv
    have hcA : c ≤ ‖A‖ := by
      have h1 : c * ‖v‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A v) v) := hA v
      have h2 : RCLike.re (inner 𝕜 (A v) v) ≤ ‖A‖ * ‖v‖ ^ 2 :=
        calc RCLike.re (inner 𝕜 (A v) v) ≤ ‖inner 𝕜 (A v) v‖ := RCLike.re_le_norm _
          _ ≤ ‖A v‖ * ‖v‖ := norm_inner_le_norm _ _
          _ ≤ ‖A‖ * ‖v‖ * ‖v‖ := by gcongr; exact A.le_opNorm v
          _ = ‖A‖ * ‖v‖ ^ 2 := by ring
      exact le_of_mul_le_mul_right (by linarith) (by positivity : (0 : ℝ) < ‖v‖ ^ 2)
    have hd : (0 : ℝ) < ‖A‖ + r := by positivity
    have hq0 : (0 : ℝ) ≤ 1 - 4 * r * c / (‖A‖ + r) ^ 2 := by
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith [sq_nonneg (‖A‖ - r), norm_nonneg A]
    have hq1 : 1 - 4 * r * c / (‖A‖ + r) ^ 2 < 1 := by
      have : (0 : ℝ) < 4 * r * c / (‖A‖ + r) ^ 2 := by positivity
      linarith
    have hbound : ‖(A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)‖
        ≤ Real.sqrt (1 - 4 * r * c / (‖A‖ + r) ^ 2) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
      refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num)
        (by positivity) ?_
      rw [mul_pow, Real.sq_sqrt hq0]
      exact norm_cayley_apply_sq_le hc hA hr y
    have hsq : Real.sqrt (1 - 4 * r * c / (‖A‖ + r) ^ 2) < 1 := by
      have h := Real.sqrt_lt_sqrt hq0 hq1
      rwa [Real.sqrt_one] at h
    linarith

end Cayley

/-! ### The Peaceman–Rachford sweep -/

/-- Saad's (4.50): the iteration operator of one Peaceman–Rachford sweep with parameter `r`. -/
noncomputable def peacemanRachford (H V : E →L[𝕜] E) (r : ℝ) : E →L[𝕜] E :=
  Ring.inverse (V + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) *
    (V - (r : 𝕜) • 1)

/-- Saad's (4.51): the affine part of one Peaceman–Rachford sweep. -/
noncomputable def peacemanRachfordConst (H V : E →L[𝕜] E) (r : ℝ) (b : E) : E :=
  Ring.inverse (V + (r : 𝕜) • 1) ((1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) b)

/-- One sweep of Saad's Algorithm 4.3 written as its two half-steps: solve
`(H + r) x_{k+1/2} = (r - V) x_k + b`, then `(V + r) x_{k+1} = (r - H) x_{k+1/2} + b`. -/
noncomputable def peacemanRachfordSweep (H V : E →L[𝕜] E) (r : ℝ) (b x : E) : E :=
  Ring.inverse (V + (r : 𝕜) • 1)
    (((r : 𝕜) • 1 - H) (Ring.inverse (H + (r : 𝕜) • 1) (((r : 𝕜) • 1 - V) x + b)) + b)

/-- The two half-steps of Algorithm 4.3, composed, are the affine step of (4.50)–(4.51). -/
theorem peacemanRachford_step_eq (H V : E →L[𝕜] E) (r : ℝ) (b x : E) :
    step (peacemanRachford H V r) (peacemanRachfordConst H V r b) x
      = peacemanRachfordSweep H V r b x := by
  simp only [step, peacemanRachford, peacemanRachfordConst, peacemanRachfordSweep,
    mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self, map_add, map_sub, map_smul]
  module

/-! ### The Peaceman–Rachford splitting -/

section Splitting

variable {H V : E →L[𝕜] E} {r : ℝ}

/-- A nonzero scalar multiple of a unit is a unit. -/
private theorem isUnit_smul {c : 𝕜} (hc : c ≠ 0) {X : E →L[𝕜] E} (hX : IsUnit X) :
    IsUnit (c • X) := by
  have h1 : IsUnit (c • (1 : E →L[𝕜] E)) :=
    ⟨⟨c • 1, c⁻¹ • 1, by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hc, one_smul],
      by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hc, one_smul]⟩, rfl⟩
  simpa [smul_mul_assoc] using h1.mul hX

/-- A scalar shift is central. -/
private theorem smul_one_mul_comm (c : 𝕜) (T : E →L[𝕜] E) :
    (c • (1 : E →L[𝕜] E)) * T = T * (c • (1 : E →L[𝕜] E)) := by
  ext y
  simp

/-- `H + r` and `H - r` commute.  This is the only commutation used anywhere in the file, and it
involves `H` alone — never `H` together with `V`. -/
private theorem commute_add_sub_smul_one (H : E →L[𝕜] E) (r : ℝ) :
    (H + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) = (H - (r : 𝕜) • 1) * (H + (r : 𝕜) • 1) := by
  simp only [mul_sub, sub_mul, add_mul, mul_add, smul_one_mul_comm]
  abel

/-- Saad's (4.52): the splitting `H + V = M - N` behind the Peaceman–Rachford sweep, with
`M = (2r)⁻¹ (H + r)(V + r)`.  The identity `M - N = H + V` is pure ring algebra: the `H V` terms
cancel, so no commutativity of `H` and `V` is used. -/
noncomputable def peacemanRachfordSplitting (H V : E →L[𝕜] E) {r : ℝ} (hr : r ≠ 0)
    (hH : IsUnit (H + (r : 𝕜) • 1)) (hV : IsUnit (V + (r : 𝕜) • 1)) :
    Splitting (H + V) :=
  ⟨(2 * (r : 𝕜))⁻¹ • ((H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1)),
    isUnit_smul (inv_ne_zero (mul_ne_zero two_ne_zero (RCLike.ofReal_ne_zero.2 hr)))
      (hH.mul hV)⟩

variable {hr : r ≠ 0} {hH : IsUnit (H + (r : 𝕜) • 1)} {hV : IsUnit (V + (r : 𝕜) • 1)}

theorem peacemanRachfordSplitting_m :
    (peacemanRachfordSplitting H V hr hH hV).m
      = (2 * (r : 𝕜))⁻¹ • ((H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1)) := rfl

/-- The complementary part of Saad's (4.52).  The `H V` terms cancel in `M - (H + V)`, which is
why the splitting needs no commutativity. -/
theorem peacemanRachfordSplitting_n :
    (peacemanRachfordSplitting H V hr hH hV).n
      = (2 * (r : 𝕜))⁻¹ • ((H - (r : 𝕜) • 1) * (V - (r : 𝕜) • 1)) := by
  have hs : (2 * (r : 𝕜)) ≠ 0 := mul_ne_zero two_ne_zero (RCLike.ofReal_ne_zero.2 hr)
  have hn : (peacemanRachfordSplitting H V hr hH hV).n
      = (2 * (r : 𝕜))⁻¹ • ((H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1)) - (H + V) := rfl
  have hexp : (H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1) - (2 * (r : 𝕜)) • (H + V)
      = (H - (r : 𝕜) • 1) * (V - (r : 𝕜) • 1) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_one]
    module
  rw [hn, ← hexp, smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- The iteration operator of Saad's splitting (4.52) is the sweep operator (4.50).  The two
differ by `(H + r)⁻¹ (H - r) = (H - r)(H + r)⁻¹`, a commutation of `H` with itself. -/
theorem peacemanRachfordSplitting_iterationOperator :
    (peacemanRachfordSplitting H V hr hH hV).iterationOperator = peacemanRachford H V r := by
  have hmu := (peacemanRachfordSplitting H V hr hH hV).isUnit
  refine hmu.mul_left_cancel ?_
  rw [Splitting.iterationOperator_eq, ← mul_assoc, Ring.mul_inverse_cancel _ hmu, one_mul,
    peacemanRachfordSplitting_n, peacemanRachfordSplitting_m, peacemanRachford, smul_mul_assoc]
  congr 1
  symm
  calc (H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1) *
        (Ring.inverse (V + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) *
          (V - (r : 𝕜) • 1))
      = (H + (r : 𝕜) • 1) * ((V + (r : 𝕜) • 1) * Ring.inverse (V + (r : 𝕜) • 1)) *
          ((H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) * (V - (r : 𝕜) • 1)) := by
        noncomm_ring
    _ = (H + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) *
          (Ring.inverse (H + (r : 𝕜) • 1) * (V - (r : 𝕜) • 1)) := by
        rw [Ring.mul_inverse_cancel _ hV]; noncomm_ring
    _ = (H - (r : 𝕜) • 1) * ((H + (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) *
          (V - (r : 𝕜) • 1) := by
        rw [commute_add_sub_smul_one]; noncomm_ring
    _ = (H - (r : 𝕜) • 1) * (V - (r : 𝕜) • 1) := by
        rw [Ring.mul_inverse_cancel _ hH]; noncomm_ring

/-- Saad's Problem P-4.5: the preconditioner of the splitting inverts to
`2 r (V + r)⁻¹ (H + r)⁻¹`. -/
theorem peacemanRachfordSplitting_ringInverse_m :
    Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m
      = Ring.inverse (V + (r : 𝕜) • 1) *
          (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) := by
  have hs : (2 * (r : 𝕜)) ≠ 0 := mul_ne_zero two_ne_zero (RCLike.ofReal_ne_zero.2 hr)
  have hmu := (peacemanRachfordSplitting H V hr hH hV).isUnit
  have hmk : (peacemanRachfordSplitting H V hr hH hV).m *
      (Ring.inverse (V + (r : 𝕜) • 1) *
        (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1))) = 1 := by
    rw [peacemanRachfordSplitting_m, smul_mul_assoc]
    have hkey : (H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1) *
        (Ring.inverse (V + (r : 𝕜) • 1) *
          (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)))
        = (2 * (r : 𝕜)) • (1 : E →L[𝕜] E) := by
      calc (H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1) *
            (Ring.inverse (V + (r : 𝕜) • 1) *
              (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)))
          = (H + (r : 𝕜) • 1) * ((V + (r : 𝕜) • 1) * Ring.inverse (V + (r : 𝕜) • 1)) *
              (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) := by noncomm_ring
        _ = (H + (r : 𝕜) • 1) -
              (H + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) := by
            rw [Ring.mul_inverse_cancel _ hV]; noncomm_ring
        _ = (H + (r : 𝕜) • 1) -
              (H - (r : 𝕜) • 1) * ((H + (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) := by
            rw [commute_add_sub_smul_one]; noncomm_ring
        _ = (2 * (r : 𝕜)) • (1 : E →L[𝕜] E) := by
            rw [Ring.mul_inverse_cancel _ hH, mul_one]
            module
    rw [hkey, smul_smul, inv_mul_cancel₀ hs, one_smul]
  calc Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m
      = Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m *
          ((peacemanRachfordSplitting H V hr hH hV).m *
            (Ring.inverse (V + (r : 𝕜) • 1) *
              (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)))) := by
        rw [hmk, mul_one]
    _ = Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m *
          (peacemanRachfordSplitting H V hr hH hV).m *
          (Ring.inverse (V + (r : 𝕜) • 1) *
            (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1))) := by rw [mul_assoc]
    _ = _ := by rw [Ring.inverse_mul_cancel _ hmu, one_mul]

/-- The affine part (4.51) of the sweep is `M⁻¹ b` for the splitting's preconditioner `M`
(Saad, Problem P-4.5). -/
theorem peacemanRachfordSplitting_const (b : E) :
    Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m b
      = peacemanRachfordConst H V r b := by
  rw [peacemanRachfordSplitting_ringInverse_m, mul_apply_eq_comp, peacemanRachfordConst]

end Splitting

/-! ### Convergence -/

section Convergence

variable [CompleteSpace E] {H V : E →L[𝕜] E} {r : ℝ}

omit [CompleteSpace E] in
/-- Conjugating the sweep operator (4.50) by `V + r` turns it into the product of the two Cayley
transforms, of `H` and of `V`. -/
theorem peacemanRachford_conj (hV : IsUnit (V + (r : 𝕜) • (1 : E →L[𝕜] E))) :
    (V + (r : 𝕜) • 1) * peacemanRachford H V r * Ring.inverse (V + (r : 𝕜) • 1)
      = ((H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) *
        ((V - (r : 𝕜) • 1) * Ring.inverse (V + (r : 𝕜) • 1)) := by
  rw [peacemanRachford]
  calc (V + (r : 𝕜) • 1) *
        (Ring.inverse (V + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) *
          (V - (r : 𝕜) • 1)) * Ring.inverse (V + (r : 𝕜) • 1)
      = ((V + (r : 𝕜) • 1) * Ring.inverse (V + (r : 𝕜) • 1)) *
          ((H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) * (V - (r : 𝕜) • 1) *
            Ring.inverse (V + (r : 𝕜) • 1)) := by noncomm_ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ hV, one_mul]; noncomm_ring

/-- The convergence theorem Saad asserts in §4.3 without proof, in its sharp operator form: the
sweep operator conjugated by `V + r` — the product of the two Cayley transforms — is a strict
contraction.  Neither symmetry nor commutativity of `H` and `V` is used.  The *unconjugated*
`Stationary.peacemanRachford` need not have norm below one, which is why the statement is made
here and the spectral radius bound is derived from it. -/
theorem norm_conj_peacemanRachford_lt_one (hH : (H : E →ₗ[𝕜] E).IsCoercive)
    (hV : (V : E →ₗ[𝕜] E).IsCoercive) (hr : 0 < r) :
    ‖(V + (r : 𝕜) • 1) * peacemanRachford H V r * Ring.inverse (V + (r : 𝕜) • 1)‖ < 1 := by
  obtain ⟨c₁, hc₁, hH'⟩ := hH
  obtain ⟨c₂, hc₂, hV'⟩ := hV
  rw [peacemanRachford_conj (isUnit_add_smul_one hc₂ hV' hr)]
  have h1 := norm_cayley_lt_one hc₁ hH' hr
  have h2 := norm_cayley_lt_one hc₂ hV' hr
  refine lt_of_le_of_lt (norm_mul_le _ _) ?_
  nlinarith [norm_nonneg ((H - (r : 𝕜) • (1 : E →L[𝕜] E)) * Ring.inverse (H + (r : 𝕜) • 1)),
    norm_nonneg ((V - (r : 𝕜) • (1 : E →L[𝕜] E)) * Ring.inverse (V + (r : 𝕜) • 1))]

omit [CompleteSpace E] in
/-- A conjugate of a power is the power of the conjugate. -/
private theorem pow_conj {u : (E →L[𝕜] E)ˣ} {P Q : E →L[𝕜] E}
    (hP : (↑u⁻¹ : E →L[𝕜] E) * Q * ↑u = P) (k : ℕ) :
    P ^ k = (↑u⁻¹ : E →L[𝕜] E) * Q ^ k * ↑u := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, u.inv_mul]
  | succ k ih =>
    rw [pow_succ, ih, ← hP, pow_succ]
    calc ((↑u⁻¹ : E →L[𝕜] E) * Q ^ k * ↑u) * ((↑u⁻¹ : E →L[𝕜] E) * Q * ↑u)
        = (↑u⁻¹ : E →L[𝕜] E) * Q ^ k * ((u : E →L[𝕜] E) * ↑u⁻¹) * Q * ↑u := by noncomm_ring
      _ = (↑u⁻¹ : E →L[𝕜] E) * (Q ^ k * Q) * ↑u := by rw [u.mul_inv]; noncomm_ring

omit [CompleteSpace E] in
private theorem norm_pow_conj_le {u : (E →L[𝕜] E)ˣ} {P Q : E →L[𝕜] E}
    (hP : (↑u⁻¹ : E →L[𝕜] E) * Q * ↑u = P) (k : ℕ) :
    ‖P ^ k‖ ≤ ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖Q‖ ^ k * ‖(u : E →L[𝕜] E)‖ := by
  have hQ : ∀ j : ℕ, ‖Q ^ j‖ ≤ ‖Q‖ ^ j := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ j ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (by gcongr)
  rw [pow_conj hP k]
  calc ‖(↑u⁻¹ : E →L[𝕜] E) * Q ^ k * ↑u‖
      ≤ ‖(↑u⁻¹ : E →L[𝕜] E) * Q ^ k‖ * ‖(u : E →L[𝕜] E)‖ := norm_mul_le _ _
    _ ≤ ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖Q ^ k‖ * ‖(u : E →L[𝕜] E)‖ := by
        gcongr
        exact norm_mul_le _ _
    _ ≤ ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖Q‖ ^ k * ‖(u : E →L[𝕜] E)‖ := by gcongr; exact hQ k

/-- The sweep operator has spectral radius below one: it is similar to the product of two Cayley
transforms, and similarity preserves the spectrum. -/
theorem spectralRadius_peacemanRachford_lt_one (hH : (H : E →ₗ[𝕜] E).IsCoercive)
    (hV : (V : E →ₗ[𝕜] E).IsCoercive) (hr : 0 < r) :
    spectralRadius 𝕜 (peacemanRachford H V r) < 1 := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have : Subsingleton (E →L[𝕜] E) := ⟨fun _ _ => by ext x; exact Subsingleton.elim _ _⟩
    simp [spectralRadius]
  · obtain ⟨c₂, hc₂, hV'⟩ := hV
    obtain ⟨u, hu⟩ := isUnit_add_smul_one hc₂ hV' hr
    have hQ : ‖(u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)‖ < 1 := by
      have h := norm_conj_peacemanRachford_lt_one hH ⟨c₂, hc₂, hV'⟩ hr
      rwa [← hu, Ring.inverse_unit] at h
    have hle : spectralRadius 𝕜 (peacemanRachford H V r)
        ≤ ‖(u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)‖₊ := by
      rw [spectralRadius, ← spectrum.units_conjugate (a := peacemanRachford H V r) (u := u),
        ← spectralRadius]
      exact spectrum.spectralRadius_le_nnnorm _
    refine lt_of_le_of_lt hle ?_
    rwa [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_one, coe_nnnorm]

/-- Convergence of the Peaceman–Rachford iteration from any starting vector and for any
parameter `r > 0`: the theorem Saad asserts in §4.3 in one sentence.  The iterates of one sweep
converge to the solution of `(H + V) x = b`.  No commutativity of `H` and `V` is used, and no
symmetry either. -/
theorem tendsto_peacemanRachford (hH : (H : E →ₗ[𝕜] E).IsCoercive)
    (hV : (V : E →ₗ[𝕜] E).IsCoercive) (hr : 0 < r) {b x : E} (hx : (H + V) x = b) (x₀ : E) :
    Tendsto (fun k => (step (peacemanRachford H V r) (peacemanRachfordConst H V r b))^[k] x₀)
      atTop (𝓝 x) := by
  obtain ⟨c₁, hc₁, hH'⟩ := hH
  obtain ⟨c₂, hc₂, hV'⟩ := hV
  have hHu : IsUnit (H + (r : 𝕜) • (1 : E →L[𝕜] E)) := isUnit_add_smul_one hc₁ hH' hr
  have hVu : IsUnit (V + (r : 𝕜) • (1 : E →L[𝕜] E)) := isUnit_add_smul_one hc₂ hV' hr
  -- the solution of `(H + V) x = b` is a fixed point of the sweep
  have hfix : peacemanRachford H V r x + peacemanRachfordConst H V r b = x := by
    have h1 : (1 : E →L[𝕜] E) - peacemanRachford H V r
        = Ring.inverse (peacemanRachfordSplitting H V hr.ne' hHu hVu).m * (H + V) := by
      rw [← peacemanRachfordSplitting_iterationOperator (hr := hr.ne') (hH := hHu) (hV := hVu)]
      exact Splitting.one_sub_iterationOperator _
    have h2 := congrArg (fun T : E →L[𝕜] E => T x) h1
    simp only [sub_apply, one_apply_eq_self, mul_apply_eq_comp] at h2
    rw [hx, peacemanRachfordSplitting_const] at h2
    rw [← h2]
    abel
  -- the sweep operator is similar to a strict contraction
  obtain ⟨u, hu⟩ := hVu
  have hP : (↑u⁻¹ : E →L[𝕜] E) *
      ((u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)) * ↑u
      = peacemanRachford H V r := by
    calc (↑u⁻¹ : E →L[𝕜] E) *
          ((u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)) * ↑u
        = ((↑u⁻¹ : E →L[𝕜] E) * ↑u) * peacemanRachford H V r *
            ((↑u⁻¹ : E →L[𝕜] E) * ↑u) := by noncomm_ring
      _ = peacemanRachford H V r := by rw [u.inv_mul, one_mul, mul_one]
  have hQnorm : ‖(u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)‖ < 1 := by
    have h := norm_conj_peacemanRachford_lt_one ⟨c₁, hc₁, hH'⟩ ⟨c₂, hc₂, hV'⟩ hr
    rwa [← hu, Ring.inverse_unit] at h
  -- and so the errors go to zero
  rw [← tendsto_sub_nhds_zero_iff]
  simp only [step_iterate_sub _ _ hfix]
  refine squeeze_zero_norm (fun k => (peacemanRachford H V r ^ k).le_opNorm _) ?_
  have hlim : Tendsto (fun k : ℕ => ‖(↑u⁻¹ : E →L[𝕜] E)‖ *
      ‖(u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)‖ ^ k *
      ‖(u : E →L[𝕜] E)‖ * ‖x₀ - x‖) atTop (𝓝 0) := by
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hQnorm
    simpa using ((h0.const_mul ‖(↑u⁻¹ : E →L[𝕜] E)‖).mul_const
      ‖(u : E →L[𝕜] E)‖).mul_const ‖x₀ - x‖
  refine squeeze_zero (fun k => by positivity) (fun k => ?_) hlim
  exact mul_le_mul_of_nonneg_right (norm_pow_conj_le hP k) (norm_nonneg _)

end Convergence

end Stationary
