import Numlib.Optimization.TrustRegion.SecondOrder.Finite

/-!
# Least-Hessian perturbation and an explicit positive-curvature region

The actual second derivative tensor controls differences of its quadratic forms
on unit directions. Genuine unit least eigenpairs then give the operator-norm
perturbation bound and its Lipschitz consequence. Positive least curvature
persists on the explicit ball of radius lambda divided by four times the
Hessian Lipschitz constant.
-/

namespace SecondOrderTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A genuine unit Hessian eigenvector attains its eigenvalue as a second
Taylor coefficient. -/
theorem IsLeastEigenpair.hessian_value {f : E → ℝ} {x u : E} {μ : ℝ}
    (h : IsLeastEigenpair f x μ u) :
    iteratedFDeriv ℝ 2 f x (fun _ => u) = μ := by
  have hh := TaylorModel.inner_hessianOperator f x u u
  have he : (![u, u] : Fin 2 → E) = fun _ => u := by
    ext i
    fin_cases i <;> rfl
  rw [he, h.eigenvector, real_inner_smul_left, real_inner_self_eq_norm_sq, h.unit] at hh
  simpa using hh.symm

omit [CompleteSpace E] in
/-- The norm of the difference of genuine Hessian tensors controls their
quadratic forms on every unit vector. -/
theorem hessian_difference_unit_le (f : E → ℝ) (x y v : E) (hv : ‖v‖ = 1) :
    |iteratedFDeriv ℝ 2 f x (fun _ => v) -
      iteratedFDeriv ℝ 2 f y (fun _ => v)| ≤
        ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ := by
  have hh := (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y).le_opNorm (fun _ => v)
  simpa only [sub_apply, Real.norm_eq_abs, hv,
    Finset.prod_const_one, mul_one] using hh

/-- Actual least Hessian eigenvalues satisfy the operator-norm perturbation bound. -/
theorem IsLeastEigenpair.sub_le_norm {f : E → ℝ} {x y u v : E} {μ ν : ℝ}
    (hx : IsLeastEigenpair f x μ u) (hy : IsLeastEigenpair f y ν v) :
    |μ - ν| ≤ ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ := by
  have hxy := hessian_difference_unit_le f x y v hy.unit
  have hyx := hessian_difference_unit_le f x y u hx.unit
  have hxv := hx.least v hy.unit
  have hyu := hy.least u hx.unit
  rw [hy.hessian_value] at hxy
  rw [hx.hessian_value] at hyx
  rw [abs_le] at hxy hyx ⊢
  constructor <;> linarith

/-- A Lipschitz bound on the actual second jet transfers to the actual least
Hessian eigenvalues without selecting arbitrary derivative data. -/
theorem IsLeastEigenpair.sub_le_lipschitz {f : E → ℝ} {x y u v : E} {μ ν L : ℝ}
    (hx : IsLeastEigenpair f x μ u) (hy : IsLeastEigenpair f y ν v)
    (hL : ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖) :
    |μ - ν| ≤ L * ‖x - y‖ := (hx.sub_le_norm hy).trans hL

/-- Positive least curvature persists on the explicit local strong-convexity
ball of radius lambda divided by four times the Hessian Lipschitz constant. -/
theorem IsLeastEigenpair.ge_half_on_ball {f : E → ℝ} {xstar ustar : E} {ℓ L : ℝ}
    (hstar : IsLeastEigenpair f xstar ℓ ustar) (hℓ : 0 < ℓ) (hL : 0 < L)
    (hlip : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖)
    {x u : E} {μ : ℝ} (hx : ‖x - xstar‖ ≤ ℓ / (4 * L))
    (he : IsLeastEigenpair f x μ u) : ℓ / 2 ≤ μ := by
  have hh := he.sub_le_lipschitz hstar (hlip x xstar)
  have hd := (le_div_iff₀ (by positivity : 0 < 4 * L)).mp hx
  have hab := (abs_le.mp hh).1
  nlinarith

/-- The same explicit ball bounds the actual Hessian in every unit direction,
without requiring an eigenpair at the perturbed point. -/
theorem IsLeastEigenpair.curvature_ge_half_on_ball {f : E → ℝ} {xstar ustar : E}
    {ℓ L : ℝ} (hstar : IsLeastEigenpair f xstar ℓ ustar) (hℓ : 0 < ℓ) (hL : 0 < L)
    (hlip : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖)
    {x : E} (hx : ‖x - xstar‖ ≤ ℓ / (4 * L)) (v : E) (hv : ‖v‖ = 1) :
    ℓ / 2 ≤ iteratedFDeriv ℝ 2 f x (fun _ => v) := by
  have hh := (hessian_difference_unit_le f x xstar v hv).trans (hlip x xstar)
  have hd := (le_div_iff₀ (by positivity : 0 < 4 * L)).mp hx
  have hbase := hstar.least v hv
  have hab := (abs_le.mp hh).1
  nlinarith

end SecondOrderTrustRegion
