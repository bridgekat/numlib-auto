import Numlib.Optimization.Complexity.MeasureDominated
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Powers of the norm of a residual

For a residual map `r : E → F` between real inner product spaces (the book's `r : ℝⁿ → ℝᵐ`) and
a real `ℓ`, `Optimization.residualPow r ℓ x = ‖r x‖^ℓ / ℓ` is the objective `Φ_ℓ` of
[cartis2022evaluation], (5.1.3); least squares is `ℓ = 2`.

## Main statements

* `Optimization.contDiff_residualPow`: Lemma 5.1.1, `Φ_ℓ` is `C^p` when `r` is, for `ℓ` an even
  integer or `ℓ ≥ 2p`;
* `Optimization.gradient_residualPow`, `Optimization.norm_fderiv_residualPow`,
  `Optimization.norm_fderiv_residualPow_div`, `Optimization.norm_fderiv_residualPow_div_eq_two`:
  the gradient `∇Φ_ℓ = ‖r‖^{ℓ-2} J^* r` and (5.1.63),
  `‖∇Φ_ℓ‖ / ‖r‖^{ℓ-1} = ‖∇Φ_2‖ / ‖r‖ = ‖J^* r‖ / ‖r‖` (independent of `ℓ`);
* `Optimization.norm_fderiv_residualPow_ge`: (5.1.64), (5.3.2), a lower bound `s₀` on the
  Jacobian's adjoint (in finite dimension, its smallest singular value) gives
  `‖∇Φ_ℓ‖ ≥ s₀ ‖r‖^{ℓ-1}`;
* `Optimization.residualPow_le_of_norm_fderiv_ge`, `Optimization.isMeasureDominated_residualPow`:
  (5.3.3), `Φ_ℓ` is then measure dominated of level `ℓ/(ℓ-1)` for `ψ = ‖∇Φ_ℓ‖`;
* `Optimization.rpow_inv_two_pow_sub_ge`: Lemma 5.1.3 (cascading differences);
* `Optimization.rpow_inv_two_pow_sub_ge_min`: the resulting decrease of the potential
  `‖r‖^{1/2^i}` on a successful iteration (Lemma 5.1.4, (5.1.20) and (5.1.27); display (6.3.3)),
  stated for reals so that the unconstrained measure `‖∇Φ_ℓ‖` and the constrained
  `ω_{Φ_ℓ,𝒞,1}` are both instances.
-/

open scoped InnerProductSpace

namespace Optimization

section Def

variable {E F : Type*} [NormedAddCommGroup F]

/-- The objective `Φ_ℓ(x) = ‖r(x)‖^ℓ / ℓ` of [cartis2022evaluation], (5.1.3), with a real
exponent `ℓ`. The book uses `ℓ ≥ 1` (the results here assume `ℓ > 1` or `ℓ ≥ 2p`); for the
degenerate exponent `ℓ = 0` Lean's division gives `residualPow r 0 = 0`, and for `ℓ < 0` the
function is not a meaningful objective. -/
noncomputable def residualPow (r : E → F) (ℓ : ℝ) (x : E) : ℝ :=
  ‖r x‖ ^ ℓ / ℓ

theorem residualPow_def (r : E → F) (ℓ : ℝ) (x : E) : residualPow r ℓ x = ‖r x‖ ^ ℓ / ℓ :=
  rfl

/-- For a natural exponent, `Φ_ℓ` is the natural power. -/
@[simp]
theorem residualPow_natCast (r : E → F) (n : ℕ) (x : E) :
    residualPow r n x = ‖r x‖ ^ n / n := by
  simp [residualPow, Real.rpow_natCast]

theorem residualPow_nonneg (r : E → F) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x : E) : 0 ≤ residualPow r ℓ x :=
  div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hℓ

end Def

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- **Lemma 5.1.1** ([cartis2022evaluation]): if `r` is `C^p`, so is `Φ_ℓ`, provided `ℓ` is an
even integer or a real with `ℓ ≥ 2p`. This slightly strengthens the book, which assumes the
strict `ℓ > 2p`: its proof writes `Φ_ℓ = (‖r‖²)^{ℓ/2}/ℓ` and only needs `t ↦ t^{ℓ/2}` to be `C^p`,
which holds for `ℓ/2 ≥ p` (`Real.contDiff_rpow_const_of_le`). (The book's remark that `ℓ > p`
suffices is not proved there and not formalized.) -/
theorem contDiff_residualPow {r : E → F} {p : ℕ} {ℓ : ℝ} (hr : ContDiff ℝ p r)
    (hℓ : (∃ m : ℕ, ℓ = 2 * m) ∨ 2 * (p : ℝ) ≤ ℓ) : ContDiff ℝ p (residualPow r ℓ) := by
  have hsq : ContDiff ℝ p fun x => ‖r x‖ ^ 2 := hr.norm_sq ℝ
  rcases hℓ with ⟨m, rfl⟩ | hℓ
  · have : residualPow r (2 * m) = fun x => (‖r x‖ ^ 2) ^ m / (2 * m) := by
      funext x
      rw [residualPow, show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, pow_mul]
    rw [this]
    exact (hsq.pow m).div_const _
  · have : residualPow r ℓ = fun x => (‖r x‖ ^ 2) ^ (ℓ / 2) / ℓ := by
      funext x
      rw [residualPow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 2
      push_cast
      ring
    rw [this]
    exact ((Real.contDiff_rpow_const_of_le (by linarith)).comp hsq).div_const _

/-- The derivative of `Φ_ℓ` (`ℓ > 1`) along a differentiable residual:
`DΦ_ℓ(x) = ‖r(x)‖^{ℓ-2} ⟪r(x), r'(·)⟫`. -/
theorem hasFDerivAt_residualPow {r : E → F} {r' : E →L[ℝ] F} {x : E} {ℓ : ℝ}
    (hr : HasFDerivAt r r' x) (hℓ : 1 < ℓ) :
    HasFDerivAt (residualPow r ℓ) (‖r x‖ ^ (ℓ - 2) • (innerSL ℝ (r x)).comp r') x := by
  have h := ((hasFDerivAt_norm_rpow (r x) hℓ).comp x hr).mul_const ℓ⁻¹
  have hℓ0 : ℓ ≠ 0 := by positivity
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    field_simp
  · simp [residualPow, div_eq_mul_inv]

/-- **The gradient of `Φ_ℓ`** ([cartis2022evaluation], (5.1.63)): for `ℓ > 1` and `r`
differentiable at `x`, `DΦ_ℓ(x) = ‖r(x)‖^{ℓ-2} ⟪r(x), J(x)·⟫`, i.e.
`∇Φ_ℓ(x) = ‖r(x)‖^{ℓ-2} J(x)^* r(x)`. -/
theorem gradient_residualPow {r : E → F} {x : E} {ℓ : ℝ} (hr : DifferentiableAt ℝ r x)
    (hℓ : 1 < ℓ) :
    fderiv ℝ (residualPow r ℓ) x = ‖r x‖ ^ (ℓ - 2) • (innerSL ℝ (r x)).comp (fderiv ℝ r x) :=
  (hasFDerivAt_residualPow hr.hasFDerivAt hℓ).fderiv

theorem differentiableAt_residualPow {r : E → F} {x : E} {ℓ : ℝ} (hr : DifferentiableAt ℝ r x)
    (hℓ : 1 < ℓ) : DifferentiableAt ℝ (residualPow r ℓ) x :=
  (hasFDerivAt_residualPow hr.hasFDerivAt hℓ).differentiableAt

/-- `⟪v, A ·⟫` is the functional `⟪A^* v, ·⟫`, of norm `‖A^* v‖`. -/
theorem norm_innerSL_comp [CompleteSpace E] [CompleteSpace F] (A : E →L[ℝ] F) (v : F) :
    ‖(innerSL ℝ v).comp A‖ = ‖(ContinuousLinearMap.adjoint A) v‖ := by
  have : (innerSL ℝ v).comp A = innerSL ℝ ((ContinuousLinearMap.adjoint A) v) := by
    ext u
    simp [ContinuousLinearMap.adjoint_inner_left]
  rw [this, innerSL_apply_norm]

/-- The norm of the gradient of `Φ_ℓ`: `‖∇Φ_ℓ(x)‖ = ‖r(x)‖^{ℓ-2} ‖J(x)^* r(x)‖` (`ℓ > 1`). -/
theorem norm_fderiv_residualPow [CompleteSpace E] [CompleteSpace F] {r : E → F} {x : E} {ℓ : ℝ}
    (hr : DifferentiableAt ℝ r x) (hℓ : 1 < ℓ) :
    ‖fderiv ℝ (residualPow r ℓ) x‖ =
      ‖r x‖ ^ (ℓ - 2) * ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) (r x)‖ := by
  rw [gradient_residualPow hr hℓ, norm_smul, norm_innerSL_comp, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

/-- **(5.1.63)** ([cartis2022evaluation]): off the zeros of `r`, the scaled gradient norm
`ψ_{ℓ,1}(x) = ‖∇Φ_ℓ(x)‖ / ‖r(x)‖^{ℓ-1}` equals `‖J(x)^* r(x)‖ / ‖r(x)‖` for every `ℓ > 1` (in
particular it equals `‖∇Φ_2(x)‖ / ‖r(x)‖`). -/
theorem norm_fderiv_residualPow_div [CompleteSpace E] [CompleteSpace F] {r : E → F} {x : E}
    {ℓ : ℝ} (hr : DifferentiableAt ℝ r x) (hℓ : 1 < ℓ) (hrx : r x ≠ 0) :
    ‖fderiv ℝ (residualPow r ℓ) x‖ / ‖r x‖ ^ (ℓ - 1) =
      ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) (r x)‖ / ‖r x‖ := by
  have hpos : 0 < ‖r x‖ := norm_pos_iff.2 hrx
  rw [norm_fderiv_residualPow hr hℓ, show ℓ - 1 = (ℓ - 2) + 1 by ring,
    Real.rpow_add_one hpos.ne']
  have : 0 < ‖r x‖ ^ (ℓ - 2) := Real.rpow_pos_of_pos hpos _
  field_simp

/-- **(5.1.63)**, the middle equality ([cartis2022evaluation]): off the zeros of `r`, the scaled
gradient norm of `Φ_ℓ` is that of the least-squares objective `Φ_2`,
`‖∇Φ_ℓ(x)‖ / ‖r(x)‖^{ℓ-1} = ‖∇Φ_2(x)‖ / ‖r(x)‖`. -/
theorem norm_fderiv_residualPow_div_eq_two [CompleteSpace E] [CompleteSpace F] {r : E → F}
    {x : E} {ℓ : ℝ} (hr : DifferentiableAt ℝ r x) (hℓ : 1 < ℓ) (hrx : r x ≠ 0) :
    ‖fderiv ℝ (residualPow r ℓ) x‖ / ‖r x‖ ^ (ℓ - 1) =
      ‖fderiv ℝ (residualPow r 2) x‖ / ‖r x‖ := by
  rw [norm_fderiv_residualPow_div hr hℓ hrx]
  have := norm_fderiv_residualPow_div hr one_lt_two hrx
  norm_num at this
  rw [this]

/-- **(5.1.64), (5.3.2)** ([cartis2022evaluation]): if the adjoint of the Jacobian satisfies
`s₀ ‖v‖ ≤ ‖J(x)^* v‖` for all `v` (in finite dimension: `s₀` is at most its smallest singular
value) and `ℓ > 1`, then `s₀ ‖r(x)‖^{ℓ-1} ≤ ‖∇Φ_ℓ(x)‖`, i.e. `ψ_{ℓ,1}(x) ≥ s₀` ((5.1.62)). -/
theorem norm_fderiv_residualPow_ge [CompleteSpace E] [CompleteSpace F] {r : E → F} {x : E}
    {ℓ s₀ : ℝ} (hr : DifferentiableAt ℝ r x) (hℓ : 1 < ℓ)
    (hs : ∀ v, s₀ * ‖v‖ ≤ ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) v‖) :
    s₀ * ‖r x‖ ^ (ℓ - 1) ≤ ‖fderiv ℝ (residualPow r ℓ) x‖ := by
  rw [norm_fderiv_residualPow hr hℓ]
  rcases eq_or_ne (r x) 0 with h0 | h0
  · rw [h0, norm_zero, Real.zero_rpow (by linarith), mul_zero]
    positivity
  · have hpos : 0 < ‖r x‖ := norm_pos_iff.2 h0
    rw [show ℓ - 1 = (ℓ - 2) + 1 by ring, Real.rpow_add_one hpos.ne']
    have := mul_le_mul_of_nonneg_left (hs (r x)) (Real.rpow_nonneg hpos.le (ℓ - 2))
    linarith

omit [InnerProductSpace ℝ F] in
/-- **(5.3.3)** ([cartis2022evaluation]): if `ℓ > 1`, `ψmin > 0` and
`‖∇Φ_ℓ(x)‖ ≥ ψmin ‖r(x)‖^{ℓ-1}`, then
`Φ_ℓ(x) ≤ (1/ℓ) ψmin^{-ℓ/(ℓ-1)} ‖∇Φ_ℓ(x)‖^{ℓ/(ℓ-1)}`. -/
theorem residualPow_le_of_norm_fderiv_ge {r : E → F} {x : E} {ℓ ψmin : ℝ} (hℓ : 1 < ℓ)
    (hψ : 0 < ψmin) (h : ψmin * ‖r x‖ ^ (ℓ - 1) ≤ ‖fderiv ℝ (residualPow r ℓ) x‖) :
    residualPow r ℓ x ≤
      ψmin ^ (-(ℓ / (ℓ - 1))) / ℓ * ‖fderiv ℝ (residualPow r ℓ) x‖ ^ (ℓ / (ℓ - 1)) := by
  set G := ‖fderiv ℝ (residualPow r ℓ) x‖
  have hℓ1 : 0 < ℓ - 1 := by linarith
  have ha : 0 ≤ ‖r x‖ ^ (ℓ - 1) := Real.rpow_nonneg (norm_nonneg _) _
  have hle : ‖r x‖ ^ (ℓ - 1) ≤ G / ψmin := by rw [le_div_iff₀ hψ]; linarith
  have hpow : ‖r x‖ ^ ℓ ≤ (G / ψmin) ^ (ℓ / (ℓ - 1)) := by
    calc ‖r x‖ ^ ℓ = (‖r x‖ ^ (ℓ - 1)) ^ (ℓ / (ℓ - 1)) := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hℓ1.ne']
      _ ≤ _ := Real.rpow_le_rpow ha hle (by positivity)
  rw [Real.div_rpow (norm_nonneg _) hψ.le] at hpow
  rw [residualPow, div_le_iff₀ (by linarith)]
  calc ‖r x‖ ^ ℓ ≤ G ^ (ℓ / (ℓ - 1)) / ψmin ^ (ℓ / (ℓ - 1)) := hpow
    _ = _ := by
      have : 0 < ψmin ^ (ℓ / (ℓ - 1)) := Real.rpow_pos_of_pos hψ _
      rw [Real.rpow_neg hψ.le]
      field_simp

omit [InnerProductSpace ℝ F] in
/-- **Measure domination of `Φ_ℓ`** ([cartis2022evaluation], (5.3.3)): on any set `A` where
`‖∇Φ_ℓ‖ ≥ ψmin ‖r‖^{ℓ-1}` (e.g. under the full-rank condition (5.1.62), by
`Optimization.norm_fderiv_residualPow_ge`), `Φ_ℓ` is measure dominated of level `ℓ/(ℓ-1)` for
`ψ = ‖∇Φ_ℓ‖`, with `f_* = 0` and `κψ = ψmin^{-ℓ/(ℓ-1)}/ℓ`. -/
theorem isMeasureDominated_residualPow {r : E → F} {ℓ ψmin : ℝ} {A : Set E} (hℓ : 1 < ℓ)
    (hψ : 0 < ψmin)
    (h : ∀ x ∈ A, ψmin * ‖r x‖ ^ (ℓ - 1) ≤ ‖fderiv ℝ (residualPow r ℓ) x‖) :
    IsMeasureDominated (residualPow r ℓ) (fun x => ‖fderiv ℝ (residualPow r ℓ) x‖) 0
      (ℓ / (ℓ - 1)) (ψmin ^ (-(ℓ / (ℓ - 1))) / ℓ) A := fun x hx =>
  ⟨residualPow_nonneg r (by linarith) x,
    by rw [sub_zero]; exact residualPow_le_of_norm_fderiv_ge hℓ hψ (h x hx)⟩

end Calculus

/-! ### Cascading differences -/

section Cascade

/-- `a^{n+1} - b^{n+1} ≤ (n+1) a^n (a - b)` for `0 ≤ b ≤ a`. -/
theorem pow_succ_sub_pow_succ_le {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (n : ℕ) :
    a ^ (n + 1) - b ^ (n + 1) ≤ (n + 1) * a ^ n * (a - b) := by
  have ha : 0 ≤ a := hb.trans hba
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + b ^ (n + 1) * (a - b) := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left ih ha
    have h2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hba (n + 1)) (sub_nonneg.2 hba)
    calc _ ≤ a * ((n + 1) * a ^ n * (a - b)) + a ^ (n + 1) * (a - b) := add_le_add h1 h2
      _ = _ := by push_cast; ring

/-- Concavity of `t ↦ t^α` (`α ∈ [0, 1]`) at `a > 0`: `α a^{α-1} (a - b) ≤ a^α - b^α` for
`0 ≤ b`. -/
theorem mul_rpow_sub_one_mul_le_rpow_sub {a b α : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : α * a ^ (α - 1) * (a - b) ≤ a ^ α - b ^ α := by
  have h := rpow_one_add_le_one_add_mul_self (s := b / a - 1)
    (by have := div_nonneg hb ha.le; linarith) hα0 hα1
  rw [add_sub_cancel, Real.div_rpow hb ha.le, div_le_iff₀ (Real.rpow_pos_of_pos ha α)] at h
  rw [Real.rpow_sub_one ha.ne']
  have : (1 + α * (b / a - 1)) * a ^ α = a ^ α - α * (a ^ α / a) * (a - b) := by
    field_simp
    ring
  linarith

/-- **Lemma 5.1.3** (cascading differences, [cartis2022evaluation]): for `a ≥ b ≥ 0` and
naturals `i` and `ℓ ≥ 1`,
`a^{1/2^i} - b^{1/2^i} ≥ (a^ℓ - b^ℓ) / (2^i ℓ a^{(2^i-1)/2^i + ℓ - 1})`. -/
theorem rpow_inv_two_pow_sub_ge {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (i : ℕ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) :
    (a ^ ℓ - b ^ ℓ) / (2 ^ i * ℓ * a ^ (((2 : ℝ) ^ i - 1) / 2 ^ i + ℓ - 1)) ≤
      a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) := by
  rcases (hb.trans hba).lt_or_eq with ha | ha
  · obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
    set α : ℝ := 1 / 2 ^ i with hαdef
    have h2 : (0 : ℝ) < 2 ^ i := by positivity
    have hα0 : 0 ≤ α := by positivity
    have hα1 : α ≤ 1 := by
      rw [hαdef, div_le_one h2]; exact one_le_pow₀ (by norm_num)
    have hα2 : α * 2 ^ i = 1 := by rw [hαdef]; field_simp
    have hexp : ((2 : ℝ) ^ i - 1) / 2 ^ i + ((n + 1 : ℕ) : ℝ) - 1 = (1 - α) + n := by
      rw [hαdef]; push_cast; field_simp; ring
    rw [hexp, Real.rpow_add ha, Real.rpow_natCast]
    have hAB : a ^ (α - 1) * a ^ (1 - α) = 1 := by
      rw [← Real.rpow_add ha]; simp
    have hB : 0 < a ^ (1 - α) := Real.rpow_pos_of_pos ha _
    have hD : 0 < 2 ^ i * ((n + 1 : ℕ) : ℝ) * (a ^ (1 - α) * a ^ n) := by positivity
    rw [div_le_iff₀ hD]
    calc a ^ (n + 1) - b ^ (n + 1) ≤ (n + 1) * a ^ n * (a - b) := pow_succ_sub_pow_succ_le hb hba n
      _ = α * a ^ (α - 1) * (a - b) * (2 ^ i * ((n + 1 : ℕ) : ℝ) * (a ^ (1 - α) * a ^ n)) := by
        have : α * a ^ (α - 1) * (a - b) * (2 ^ i * ((n + 1 : ℕ) : ℝ) * (a ^ (1 - α) * a ^ n)) =
            (α * 2 ^ i) * (a ^ (α - 1) * a ^ (1 - α)) * ((n + 1) * a ^ n * (a - b)) := by
          push_cast; ring
        rw [this, hα2, hAB, one_mul, one_mul]
      _ ≤ (a ^ α - b ^ α) * (2 ^ i * ((n + 1 : ℕ) : ℝ) * (a ^ (1 - α) * a ^ n)) :=
        mul_le_mul_of_nonneg_right (mul_rpow_sub_one_mul_le_rpow_sub ha hb hα0 hα1) hD.le
  · have hb0 : b = 0 := le_antisymm (ha ▸ hba) hb
    subst hb0
    rw [← ha]
    simp [zero_pow (by omega : ℓ ≠ 0)]

/-- **Decrease of the potential `‖r‖^{1/2^i}`** on a successful iteration that does not
terminate ([cartis2022evaluation], Lemma 5.1.4, (5.1.20), (5.1.27) and (5.1.28); display (6.3.3)
for ARpLE-CC). Let `p, ℓ ≥ 1` and `i` be naturals with
`ι₁ = (2^i - 1)/2^i - (ℓ - 1)/p ≥ 0` (5.1.21), `β ∈ (0, 1)`, `κ₁, ε₀, ε₁ > 0`, and reals
`R ≥ a ≥ b > ε₀` (`a = ‖r(x_k)‖`, `b = ‖r(x_{k+1})‖`, `R = ‖r(x_0)‖`) and `ω > ε₁ b^{ℓ-1}` (the
first-order measure of `Φ_ℓ` at `x_{k+1}`, which fails the termination test) with
`a^ℓ - b^ℓ ≥ ℓ κ₁ ω^{(p+1)/p}` (the decrease of Lemma 4.1.4 / 6.2.4 for `Φ_ℓ`). Then
`a^{1/2^i} - b^{1/2^i} ≥ min(κr0, κr1) min(ε₀^{1/2^i}, ε₁^{(p+1)/p}) / max(1, R^{ι₁})` with
`κr0 = 1 - β^{1/2^i}` and `κr1 = κ₁ β^{(ℓ-1)(p+1)/p} / 2^i`.

This is a packaged convenience, not a numbered item of the book: it combines the two cases
(5.1.20) and (5.1.27) of Lemma 5.1.4, bounding the `ε`-dependent quantities as in the proofs of
Theorems 5.1.7 and 6.3.1. -/
theorem rpow_inv_two_pow_sub_ge_min {p ℓ i : ℕ} (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ)
    (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p) {β κ₁ ε₀ ε₁ R a b ω : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ₁ : 0 < κ₁) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) (hRa : a ≤ R)
    (hba : b ≤ a) (hb : ε₀ < b) (hω : ε₁ * b ^ (ℓ - 1) < ω)
    (hdec : ℓ * κ₁ * ω ^ (((p : ℝ) + 1) / p) ≤ a ^ ℓ - b ^ ℓ) :
    min (1 - β ^ (1 / 2 ^ i : ℝ)) (κ₁ * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i) *
        min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) /
        max 1 (R ^ (((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p)) ≤
      a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) := by
  set α : ℝ := 1 / 2 ^ i with hαdef
  set ν : ℝ := ((p : ℝ) + 1) / p with hνdef
  set ι : ℝ := ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p with hιdef
  set κr0 := 1 - β ^ α
  set κr1 := κ₁ * β ^ (((ℓ : ℝ) - 1) * ν) / 2 ^ i
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hb0 : 0 < b := hε₀.trans hb
  have ha : 0 < a := hb0.trans_le hba
  have hα0 : 0 < α := by positivity
  have hν0 : 0 < ν := by positivity
  have hℓ1 : (0 : ℝ) ≤ (ℓ : ℝ) - 1 := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hκr0 : 0 < κr0 := by
    have : β ^ α < 1 := Real.rpow_lt_one hβ0.le hβ1 hα0
    linarith
  have hκr1 : 0 < κr1 := by positivity
  have hM : 1 ≤ max 1 (R ^ ι) := le_max_left _ _
  have hMpos : 0 < max 1 (R ^ ι) := one_pos.trans_le hM
  have hEps : 0 ≤ min (ε₀ ^ α) (ε₁ ^ ν) := le_min (by positivity) (by positivity)
  have hK : 0 ≤ min κr0 κr1 := le_min hκr0.le hκr1.le
  rcases le_or_gt b (β * a) with hcase | hcase
  · -- (5.1.26)–(5.1.27): the residual drops by the factor `β`
    have hbα : b ^ α ≤ β ^ α * a ^ α := by
      rw [← Real.mul_rpow hβ0.le ha.le]
      exact Real.rpow_le_rpow hb0.le hcase hα0.le
    have hba' : b ^ α ≤ a ^ α := Real.rpow_le_rpow hb0.le hba hα0.le
    have hε : ε₀ ^ α ≤ b ^ α := Real.rpow_le_rpow hε₀.le hb.le hα0.le
    calc min κr0 κr1 * min (ε₀ ^ α) (ε₁ ^ ν) / max 1 (R ^ ι)
        ≤ min κr0 κr1 * min (ε₀ ^ α) (ε₁ ^ ν) := div_le_self (mul_nonneg hK hEps) hM
      _ ≤ κr0 * ε₀ ^ α := mul_le_mul (min_le_left _ _) (min_le_left _ _) hEps hκr0.le
      _ ≤ κr0 * b ^ α := mul_le_mul_of_nonneg_left hε hκr0.le
      _ ≤ κr0 * a ^ α := mul_le_mul_of_nonneg_left hba' hκr0.le
      _ ≤ a ^ α - b ^ α := by
        have : κr0 * a ^ α = a ^ α - β ^ α * a ^ α := by ring
        linarith
  · -- (5.1.19)–(5.1.20): Lemma 5.1.3 and the decrease
    have hcasc := rpow_inv_two_pow_sub_ge hb0.le hba i hℓ
    -- the exponent of `a` splits as `(ℓ - 1) ν + ι`
    have hsplit : ((2 : ℝ) ^ i - 1) / 2 ^ i + ℓ - 1 = ((ℓ : ℝ) - 1) * ν + ι := by
      rw [hνdef, hιdef]; field_simp; ring
    rw [hsplit, Real.rpow_add ha] at hcasc
    have hA : 0 < a ^ (((ℓ : ℝ) - 1) * ν) := Real.rpow_pos_of_pos ha _
    have hI : 0 < a ^ ι := Real.rpow_pos_of_pos ha _
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    -- lower bound on `ω^ν`
    have hω0 : 0 ≤ ε₁ * b ^ (ℓ - 1) := by positivity
    have hων : ε₁ ^ ν * β ^ (((ℓ : ℝ) - 1) * ν) * a ^ (((ℓ : ℝ) - 1) * ν) ≤ ω ^ ν := by
      have e1 : (ε₁ * b ^ (ℓ - 1)) ^ ν = ε₁ ^ ν * b ^ (((ℓ : ℝ) - 1) * ν) := by
        rw [Real.mul_rpow hε₁.le (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul hb0.le, Nat.cast_sub hℓ, Nat.cast_one]
      have e2 : β ^ (((ℓ : ℝ) - 1) * ν) * a ^ (((ℓ : ℝ) - 1) * ν) =
          (β * a) ^ (((ℓ : ℝ) - 1) * ν) := (Real.mul_rpow hβ0.le ha.le).symm
      have h1 : (β * a) ^ (((ℓ : ℝ) - 1) * ν) ≤ b ^ (((ℓ : ℝ) - 1) * ν) :=
        Real.rpow_le_rpow (by positivity) hcase.le (by positivity)
      have h2' : (ε₁ * b ^ (ℓ - 1)) ^ ν ≤ ω ^ ν := Real.rpow_le_rpow hω0 hω.le hν0.le
      rw [e1] at h2'
      rw [mul_assoc, e2]
      exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2'
    have hIR : a ^ ι ≤ max 1 (R ^ ι) :=
      (Real.rpow_le_rpow ha.le hRa hι).trans (le_max_right _ _)
    calc min κr0 κr1 * min (ε₀ ^ α) (ε₁ ^ ν) / max 1 (R ^ ι)
        ≤ κr1 * ε₁ ^ ν / a ^ ι := by
          apply div_le_div₀ (by positivity)
            (mul_le_mul (min_le_right _ _) (min_le_right _ _) hEps hκr1.le) hI hIR
      _ = ℓ * κ₁ * (ε₁ ^ ν * β ^ (((ℓ : ℝ) - 1) * ν) * a ^ (((ℓ : ℝ) - 1) * ν)) /
            (2 ^ i * ℓ * (a ^ (((ℓ : ℝ) - 1) * ν) * a ^ ι)) := by
          simp only [κr1]
          field_simp
      _ ≤ ℓ * κ₁ * ω ^ ν / (2 ^ i * ℓ * (a ^ (((ℓ : ℝ) - 1) * ν) * a ^ ι)) := by
          gcongr
      _ ≤ (a ^ ℓ - b ^ ℓ) / (2 ^ i * ℓ * (a ^ (((ℓ : ℝ) - 1) * ν) * a ^ ι)) := by
          gcongr
      _ ≤ _ := hcasc

end Cascade

end Optimization
