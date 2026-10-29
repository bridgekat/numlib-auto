import Numlib.Optimization.Complexity.SlowExample.ARp

/-!
# The slit example: a hyperplane and a parallel half-space

Slow examples on a *constrained* feasible set. In a real inner product space `E`, let `e₁ ⊥ e₂`
be unit vectors and let `slitSet e₂ ρ = {v | ⟪e₂, v⟫ = 0} ∪ {v | ρ ≤ ⟪e₂, v⟫}` be a hyperplane
together with a parallel half-space at distance `ρ`. A function `G(⟪e₁, ·⟫) + H(⟪e₂, ·⟫)` whose
one-dimensional profiles have gradient spikes `G' = -β`, `H' = -1` at a point of the hyperplane
has Taylor decrements `β ⟪e₁, d⟫ + ⟪e₂, d⟫`. Displacements of norm `δ < ρ` stay in the hyperplane
and see the decrease `β δ` only, while displacements of norm `δ ≥ ρ` reach the half-space and
see a decrease at least `ρ`. Choosing `ρ` slightly above the tolerance makes the criterion "the
point is `(ε, δ)`-approximately optimal for *some* radii `δ`" fail exactly as long as `β` is
above its final value, which on the hyperplane alone cannot be arranged (the measure at radius
`1` is then small). This is the mechanism of the sharpness of the ARqpIDA-SC row of Table 14.2.1
of [cartis2022evaluation] in the lower-bound mode of the radius policy.

## Main definitions and results

* `Optimization.slitSet e ρ`: the hyperplane `⟪e, ·⟫ = 0` and the half-space `ρ ≤ ⟪e, ·⟫`.
* `Optimization.taylorPolynomial_ridge_add_ridge`, `Optimization.taylorDecrement_ridge_add_ridge`:
  Taylor data of a sum of two ridges with gradient spikes.
* `Optimization.regularizedModel_ridge_add_ridge`,
  `Optimization.taylorDecrement_regularizedModel_ridge_add_ridge`: on the hyperplane the
  regularized Taylor model is the one-dimensional model `-α t + σ |t|^{p+1}/(p+1)!` along `e₁`.
* `Optimization.taylorMeasure_slitSet_of_lt`, `Optimization.le_taylorMeasure_slitSet`: the
  measures of the decrement `β ⟪e₁, d⟫ + ⟪e₂, d⟫` below and above the radius `ρ`.
* `Optimization.not_isEpsDeltaApprox_slitSet`, `Optimization.isEpsDeltaApprox_slitSet`: the
  approximate-optimality criterion fails at every radius for large gradients, and holds at the
  radius `ε` for small ones.
-/

open Set Metric
open scoped Nat RealInnerProductSpace

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}

/-! ### Sums of two ridges at gradient spikes -/

section RidgeAddRidge

variable {p : ℕ} {G H : ℝ → ℝ} {x : E} {α γ : ℝ}

/-- The Taylor polynomials of `G(⟪e₁, ·⟫) + H(⟪e₂, ·⟫)` at a point where `G` and `H` have
gradient spikes `-α` and `-γ`: `T_j(x, w) = G(⟪e₁, x⟫) + H(⟪e₂, x⟫) - α ⟪e₁, w⟫ - γ ⟪e₂, w⟫`
(`1 ≤ j ≤ p`). -/
theorem taylorPolynomial_ridge_add_ridge (hG : ContDiff ℝ p G) (hH : ContDiff ℝ p H)
    (hdG : IsSpikeJetOf p G 1 ⟪e₁, x⟫ α) (hdH : IsSpikeJetOf p H 1 ⟪e₂, x⟫ γ) {j : ℕ}
    (hj1 : 1 ≤ j) (hjp : j ≤ p) (w : E) :
    taylorPolynomial (ridge G e₁ + ridge H e₂) j x w =
      G ⟪e₁, x⟫ + H ⟪e₂, x⟫ - α * ⟪e₁, w⟫ - γ * ⟪e₂, w⟫ := by
  have hGj : ContDiff ℝ j G := hG.of_le (by exact_mod_cast hjp)
  have hHj : ContDiff ℝ j H := hH.of_le (by exact_mod_cast hjp)
  have hsum : taylorPolynomial (ridge G e₁ + ridge H e₂) j x w =
      taylorPolynomial (ridge G e₁) j x w + taylorPolynomial (ridge H e₂) j x w := by
    rw [taylorPolynomial_apply, taylorPolynomial_apply, taylorPolynomial_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : (i : WithTop ℕ∞) ≤ j := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [iteratedFDeriv_add_apply ((contDiff_ridge hGj).contDiffAt.of_le hij)
      ((contDiff_ridge hHj).contDiffAt.of_le hij), add_apply, smul_add]
  rw [hsum, taylorPolynomial_ridge_spike hGj le_rfl hj1 (hdG.mono hjp),
    taylorPolynomial_ridge_spike hHj le_rfl hj1 (hdH.mono hjp)]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

/-- The Taylor decrements of `G(⟪e₁, ·⟫) + H(⟪e₂, ·⟫)` at a point with gradient spikes:
`ΔT_j(x, w) = α ⟪e₁, w⟫ + γ ⟪e₂, w⟫` (`1 ≤ j ≤ p`). -/
theorem taylorDecrement_ridge_add_ridge (hG : ContDiff ℝ p G) (hH : ContDiff ℝ p H)
    (hdG : IsSpikeJetOf p G 1 ⟪e₁, x⟫ α) (hdH : IsSpikeJetOf p H 1 ⟪e₂, x⟫ γ) {j : ℕ}
    (hj1 : 1 ≤ j) (hjp : j ≤ p) (w : E) :
    (ftaylorSeries ℝ (ridge G e₁ + ridge H e₂) x).taylorDecrement j w =
      α * ⟪e₁, w⟫ + γ * ⟪e₂, w⟫ := by
  rw [ftaylorSeries_taylorDecrement_eq, taylorPolynomial_ridge_add_ridge hG hH hdG hdH hj1 hjp,
    Pi.add_apply, ridge_apply, ridge_apply]
  ring

/-- The regularized Taylor model of `G(⟪e₁, ·⟫) + H(⟪e₂, ·⟫)` at a point with gradient spikes, on
the hyperplane `⟪e₂, w⟫ = 0`, when the norm there is `|⟪e₁, ·⟫|`: it is
`G(⟪e₁, x⟫) + H(⟪e₂, x⟫) + m₁(⟪e₁, w⟫)` with the one-dimensional model
`m₁ t = -α t + σ |t|^{p+1}/(p+1)!`. -/
theorem regularizedModel_ridge_add_ridge (hspan : ∀ v : E, ⟪e₂, v⟫ = 0 → ‖v‖ = |⟪e₁, v⟫|)
    (hp : 1 ≤ p) (hG : ContDiff ℝ p G) (hH : ContDiff ℝ p H) (hdG : IsSpikeJetOf p G 1 ⟪e₁, x⟫ α)
    (hdH : IsSpikeJetOf p H 1 ⟪e₂, x⟫ γ) (σ : ℝ) {w : E} (hw : ⟪e₂, w⟫ = 0) :
    regularizedModel (ftaylorSeries ℝ (ridge G e₁ + ridge H e₂) x) p σ w =
      G ⟪e₁, x⟫ + H ⟪e₂, x⟫ + negMonomialRegModel p 1 σ α ⟪e₁, w⟫ := by
  rw [regularizedModel_def, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_ridge_add_ridge hG hH hdG hdH hp le_rfl, hw, hspan w hw, negMonomialRegModel]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

/-- The Taylor decrements of the regularized model of `G(⟪e₁, ·⟫) + H(⟪e₂, ·⟫)` at a point
`t e₁` of the hyperplane, along a direction `d` of the hyperplane, are those of the
one-dimensional model `m₁` at `t` along `⟪e₁, d⟫` (orders `ℓ ≤ p`). -/
theorem taylorDecrement_regularizedModel_ridge_add_ridge (he₁ : ‖e₁‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0)
    (hspan : ∀ v : E, ⟪e₂, v⟫ = 0 → ‖v‖ = |⟪e₁, v⟫|) (hp : 1 ≤ p) (hG : ContDiff ℝ p G)
    (hH : ContDiff ℝ p H) (hdG : IsSpikeJetOf p G 1 ⟪e₁, x⟫ α)
    (hdH : IsSpikeJetOf p H 1 ⟪e₂, x⟫ γ) (σ t : ℝ) {d : E} (hd : ⟪e₂, d⟫ = 0) {ℓ : ℕ}
    (hℓ : ℓ ≤ p) :
    (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ (ridge G e₁ + ridge H e₂) x) p σ)
      (t • e₁)).taylorDecrement ℓ d =
      (ftaylorSeries ℝ (negMonomialRegModel p 1 σ α) t).taylorDecrement ℓ ⟪e₁, d⟫ := by
  have he₁₁ : ⟪e₁, e₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he₁, one_pow]
  have hline : ∀ τ : ℝ, regularizedModel (ftaylorSeries ℝ (ridge G e₁ + ridge H e₂) x) p σ
      (t • e₁ + τ • d) = (G ⟪e₁, x⟫ + H ⟪e₂, x⟫) +
        negMonomialRegModel p 1 σ α (t + τ * ⟪e₁, d⟫) := fun τ => by
    have h1 : ⟪e₂, t • e₁ + τ • d⟫ = 0 := by
      rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_comm, h12, hd]; ring
    rw [regularizedModel_ridge_add_ridge hspan hp hG hH hdG hdH σ h1, inner_add_right,
      inner_smul_right, inner_smul_right, he₁₁, mul_one]
  rw [taylorDecrement_eq_of_line contDiff_regularizedModel
    (contDiff_const.add (contDiff_negMonomialRegModel p 1 σ α)) hline hℓ, taylorDecrement_real,
    taylorDecrement_real]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [iteratedDeriv_const_add (by have := (Finset.mem_Icc.1 hi).1; omega)]

end RidgeAddRidge

/-! ### The slit set -/

section SlitSet

variable {e : E} {ρ : ℝ} {x d : E}

/-- The **slit set** `{v | ⟪e, v⟫ = 0} ∪ {v | ρ ≤ ⟪e, v⟫}`: for a unit vector `e` and `ρ > 0`, a
hyperplane together with a parallel closed half-space at distance `ρ`. -/
def slitSet (e : E) (ρ : ℝ) : Set E :=
  {v | ⟪e, v⟫ = 0} ∪ {v | ρ ≤ ⟪e, v⟫}

theorem mem_slitSet : x ∈ slitSet e ρ ↔ ⟪e, x⟫ = 0 ∨ ρ ≤ ⟪e, x⟫ :=
  Iff.rfl

theorem isClosed_slitSet (e : E) (ρ : ℝ) : IsClosed (slitSet e ρ) :=
  (isClosed_eq (continuous_const.inner continuous_id) continuous_const).union
    (isClosed_le continuous_const (continuous_const.inner continuous_id))

theorem add_mem_slitSet_iff (hx : ⟪e, x⟫ = 0) :
    x + d ∈ slitSet e ρ ↔ ⟪e, d⟫ = 0 ∨ ρ ≤ ⟪e, d⟫ := by
  rw [mem_slitSet, inner_add_right, hx, zero_add]

theorem add_mem_slitSet_of_inner_eq_zero (hx : ⟪e, x⟫ = 0) (hd : ⟪e, d⟫ = 0) :
    x + d ∈ slitSet e ρ :=
  (add_mem_slitSet_iff hx).2 (Or.inl hd)

/-- Near a point of the hyperplane, the slit set is the hyperplane: feasible displacements
shorter than `ρ` are orthogonal to `e` (`‖e‖ ≤ 1`). -/
theorem inner_eq_zero_of_add_mem_slitSet (he : ‖e‖ ≤ 1) (hx : ⟪e, x⟫ = 0)
    (hd : x + d ∈ slitSet e ρ) (hρ : ‖d‖ < ρ) : ⟪e, d⟫ = 0 := by
  rcases (add_mem_slitSet_iff hx).1 hd with h | h
  · exact h
  · have : ⟪e, d⟫ ≤ ‖d‖ :=
      (real_inner_le_norm e d).trans (mul_le_of_le_one_left (norm_nonneg _) he)
    exact absurd (h.trans this) (not_le.2 hρ)

end SlitSet

/-! ### Measures on the slit set -/

section SlitMeasure

variable {D : FormalMultilinearSeries ℝ E ℝ} {j : ℕ} {β ρ δ : ℝ} {x : E}

/-- On radii `δ < ρ` the measure of the decrement `β ⟪e₁, d⟫ + ⟪e₂, d⟫` (`β ≥ 0`) at a point of
the hyperplane, over the slit set, is `β δ`. -/
theorem taylorMeasure_slitSet_of_lt (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ ≤ 1) (h12 : ⟪e₁, e₂⟫ = 0)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hδρ : δ < ρ) (hx : ⟪e₂, x⟫ = 0)
    (hdec : ∀ d, D.taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫) :
    taylorMeasure D j δ {d | x + d ∈ slitSet e₂ ρ} = β * δ := by
  have h21 : ⟪e₂, e₁⟫ = 0 := by rw [real_inner_comm, h12]
  have hmem : ∀ c : ℝ, x + c • e₁ ∈ slitSet e₂ ρ := fun c =>
    add_mem_slitSet_of_inner_eq_zero hx (by rw [inner_smul_right, h21, mul_zero])
  refine le_antisymm (decrementMeasure_le ⟨0, mem_closedBall_self hδ, by
    simpa using hmem 0⟩ fun d hd => ?_) ?_
  · have hdn : ‖d‖ ≤ δ := mem_closedBall_zero_iff.1 hd.1
    rw [hdec, inner_eq_zero_of_add_mem_slitSet he₂ hx hd.2 (hdn.trans_lt hδρ), add_zero]
    refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans ?_) hβ
    exact (abs_real_inner_le_norm e₁ d).trans (by rw [he₁, one_mul]; exact hdn)
  · have := taylorDecrement_le_taylorMeasure D j (S := {d | x + d ∈ slitSet e₂ ρ}) (δ := δ)
      (d := δ • e₁) ⟨by rw [mem_closedBall_zero_iff, norm_smul, he₁, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hδ], hmem δ⟩
    rwa [hdec, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, he₁, h21, one_pow,
      mul_one, mul_zero, add_zero] at this

/-- On radii `δ ≥ ρ ≥ 0` the half-space is reached: the measure of the decrement
`β ⟪e₁, d⟫ + ⟪e₂, d⟫` at a point of the hyperplane, over the slit set, is at least `ρ`. -/
theorem le_taylorMeasure_slitSet (he₂ : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (hρ : 0 ≤ ρ) (hρδ : ρ ≤ δ)
    (hx : ⟪e₂, x⟫ = 0) (hdec : ∀ d, D.taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫) :
    ρ ≤ taylorMeasure D j δ {d | x + d ∈ slitSet e₂ ρ} := by
  have he₂₂ : ⟪e₂, ρ • e₂⟫ = ρ := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq, he₂, one_pow, mul_one]
  have := taylorDecrement_le_taylorMeasure D j (S := {d | x + d ∈ slitSet e₂ ρ}) (δ := δ)
    (d := ρ • e₂) ⟨by rw [mem_closedBall_zero_iff, norm_smul, he₂, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hρ]; exact hρδ, (add_mem_slitSet_iff hx).2 (Or.inr he₂₂.ge)⟩
  rwa [hdec, inner_smul_right, h12, he₂₂, mul_zero, mul_zero, zero_add] at this

end SlitMeasure

/-! ### The approximate-optimality criterion on the slit set -/

section SlitTest

variable {D : FormalMultilinearSeries ℝ E ℝ} {q : ℕ} {ε β ρ c : ℝ} {x : E}

/-- **The slit example fails the criterion at every radius** when `q ≥ 1`, `c > 0`, the
half-space is at distance `ρ = ε (1 + c)^{1/n}`, `n = max(q - 1, 1)`, and the gradient is
`β ≥ ε^q (1 + c)/q!`: on radii `δ < ρ` the measure of order `q` is `β δ > ε δ^q/q!`, and on radii
`δ ≥ ρ` it is at least `ρ > ε`. -/
theorem not_isEpsDeltaApprox_slitSet (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0)
    (hε : 0 < ε) (hερ : ε < ρ) (hρpow : ρ ^ max (q - 1) 1 = ε ^ max (q - 1) 1 * (1 + c))
    (hc : 0 < c) (hβ0 : 0 ≤ β) (hβ : ε ^ q * (1 + c) / q ! ≤ β) (hx : ⟪e₂, x⟫ = 0) (hq : 1 ≤ q)
    (hdec : ∀ j ∈ Finset.Icc 1 q, ∀ d, D.taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫)
    {δ' : ℕ → ℝ} (hδ' : ∀ j ∈ Finset.Icc 1 q, δ' j ∈ Set.Ioc 0 1) :
    ¬ IsEpsDeltaApprox D {d | x + d ∈ slitSet e₂ ρ} q (fun _ => ε) δ' := by
  intro ht
  have hqm : q ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  have h1 := ht q hqm
  obtain ⟨hδ0, hδ1⟩ := hδ' q hqm
  have hqf : (0 : ℝ) < q ! := by positivity
  set δq := δ' q
  rcases lt_or_ge δq ρ with hδρ | hδρ
  · rw [taylorMeasure_slitSet_of_lt he₁ he₂.le h12 hβ0 hδ0.le hδρ hx (hdec q hqm)] at h1
    rcases hq.eq_or_lt with rfl | hq2
    · have h2 : ε ^ 1 * (1 + c) / (1 : ℕ)! * δq ≤ ε * δq ^ 1 / (1 : ℕ)! :=
        (mul_le_mul_of_nonneg_right hβ hδ0.le).trans h1
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h2
      nlinarith [mul_pos (mul_pos hε hδ0) hc]
    have hq0 : q - 1 ≠ 0 := by omega
    have hmax : max (q - 1) 1 = q - 1 := max_eq_left (by omega)
    rw [hmax] at hρpow
    have hqq : q = (q - 1) + 1 := by omega
    have e1 : ε ^ q = ε ^ (q - 1) * ε := by rw [← pow_succ, ← hqq]
    have e2 : δq ^ q = δq ^ (q - 1) * δq := by rw [← pow_succ, ← hqq]
    have h2 : ε ^ q * (1 + c) / q ! * δq ≤ ε * δq ^ q / q ! :=
      (mul_le_mul_of_nonneg_right hβ hδ0.le).trans h1
    have h3 : ε ^ (q - 1) * (1 + c) * (ε * δq) ≤ δq ^ (q - 1) * (ε * δq) := by
      rw [e1, e2] at h2
      calc ε ^ (q - 1) * (1 + c) * (ε * δq) =
            ε ^ (q - 1) * ε * (1 + c) / q ! * δq * q ! := by field_simp
        _ ≤ ε * (δq ^ (q - 1) * δq) / q ! * q ! := mul_le_mul_of_nonneg_right h2 hqf.le
        _ = δq ^ (q - 1) * (ε * δq) := by field_simp
    have h4 := le_of_mul_le_mul_right h3 (mul_pos hε hδ0)
    rw [← hρpow] at h4
    exact absurd h4 (not_le.2 (pow_lt_pow_left₀ hδρ hδ0.le hq0))
  · have h2 := le_taylorMeasure_slitSet he₂ h12 (hε.trans hερ).le hδρ hx (hdec q hqm)
    have h3 : ε * δq ^ q / q ! ≤ ε := by
      have hδq : δq ^ q ≤ 1 := pow_le_one₀ hδ0.le hδ1
      have : (1 : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_pos _
      calc ε * δq ^ q / q ! ≤ ε * δq ^ q := div_le_self (by positivity) this
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hδq hε.le
        _ = ε := mul_one ε
    exact absurd (h2.trans (h1.trans h3)) (not_le.2 hερ)

/-- **The slit example meets the criterion with radii `ε`** when `ε < ρ` and the gradient is
`β ≤ ε^q/q!`: the measures at radius `ε` are `β ε ≤ ε ε^j/j!`. -/
theorem isEpsDeltaApprox_slitSet (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ ≤ 1) (h12 : ⟪e₁, e₂⟫ = 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hερ : ε < ρ) (hβ0 : 0 ≤ β) (hβ : β ≤ ε ^ q / q !)
    (hx : ⟪e₂, x⟫ = 0)
    (hdec : ∀ j ∈ Finset.Icc 1 q, ∀ d, D.taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫) :
    IsEpsDeltaApprox D {d | x + d ∈ slitSet e₂ ρ} q (fun _ => ε) (fun _ => ε) := by
  intro j hj
  rw [taylorMeasure_slitSet_of_lt he₁ he₂ h12 hβ0 hε.le hερ hx (hdec j hj)]
  have hj := Finset.mem_Icc.1 hj
  have h1 : ε ^ q ≤ ε ^ j := pow_le_pow_of_le_one hε.le hε1 hj.2
  have h2 : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hj.2
  have h3 : ε ^ q / q ! ≤ ε ^ j / j ! := div_le_div₀ (by positivity) h1 (by positivity) h2
  calc β * ε ≤ ε ^ j / j ! * ε := mul_le_mul_of_nonneg_right (hβ.trans h3) hε.le
    _ = ε * ε ^ j / j ! := by ring

end SlitTest

end Optimization
