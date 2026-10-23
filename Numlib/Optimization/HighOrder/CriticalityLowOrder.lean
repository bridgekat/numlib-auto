import Numlib.Optimization.HighOrder.CriticalityApproximate
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Numlib.Analysis.Normed.Multilinear.DiagonalNorm

/-!
# Low-order Taylor criticality and projected cubic derivatives

The common kernel is built from the actual first and second Fréchet derivatives.
For a positive semidefinite symmetric Hessian its linear kernel agrees with the zero set
of its quadratic form. Cubic tensors are measured by the diagonal norm in (A.7), using
the equivalent closed-unit-ball formulation, including a zero-dimensional subspace.
-/

open Set
open ContinuousMultilinearMap
open scoped Topology
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The common linear kernel of the first derivative and the curried Hessian. -/
noncomputable def secondOrderKernel (f : E → ℝ) (x : E) : Submodule ℝ E :=
  (fderiv ℝ f x).ker ⊓ (fderiv ℝ (fderiv ℝ f) x).ker

/-- Membership in the common derivative kernel. -/
@[simp] theorem mem_secondOrderKernel (f : E → ℝ) (x v : E) :
    v ∈ secondOrderKernel f x ↔
      fderiv ℝ f x v = 0 ∧ fderiv ℝ (fderiv ℝ f) x v = 0 := Iff.rfl

/-- A positive semidefinite Hessian vanishes as a linear functional in every direction
where its quadratic form vanishes. -/
theorem hessian_apply_eq_zero_of_quadratic_eq_zero {f : E → ℝ} {x v : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hpos : ∀ w : E, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => w))
    (hv : iteratedFDeriv ℝ 2 f x (fun _ => v) = 0) :
    fderiv ℝ (fderiv ℝ f) x v = 0 := by
  let B := fderiv ℝ (fderiv ℝ f) x
  have hB (w : E) : 0 ≤ B w w := by
    simpa [B, iteratedFDeriv_two_apply] using hpos w
  have hv' : B v v = 0 := by simpa [B, iteratedFDeriv_two_apply] using hv
  have hsym (a b : E) : B a b = B b a :=
    (hf.isSymmSndFDerivAt (by norm_num)).eq a b
  ext w
  change B v w = 0
  have hmin : IsLocalMin (fun t : ℝ =>
      t * (B v w + B w v) + t ^ 2 * B w w) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have hp := hB (v + t • w)
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hv'] at hp
    simpa using (show (0 : ℝ) ≤ t * (B v w + B w v) + t ^ 2 * B w w by nlinarith [hp])
  have hd : HasDerivAt (fun t : ℝ => t * (B v w + B w v) + t ^ 2 * B w w)
      (B v w + B w v) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const (B v w + B w v)).add
      ((hasDerivAt_pow 2 0).mul_const (B w w)) using 1 <;> norm_num [Pi.add_def]
  have hz := hmin.hasDerivAt_eq_zero hd
  rw [hsym w v] at hz
  linarith

/-- Under Hessian positivity, the linear common kernel is exactly the intersection
of the first- and second-order homogeneous kernels from (A.8). -/
theorem mem_secondOrderKernel_iff_diagonal {f : E → ℝ} {x v : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hpos : ∀ w : E, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => w)) :
    v ∈ secondOrderKernel f x ↔
      iteratedFDeriv ℝ 1 f x (fun _ => v) = 0 ∧
      iteratedFDeriv ℝ 2 f x (fun _ => v) = 0 := by
  rw [mem_secondOrderKernel]
  simp only [iteratedFDeriv_one_apply]
  constructor
  · rintro ⟨h1,h2⟩
    refine ⟨h1, ?_⟩
    simp [iteratedFDeriv_two_apply, h2]
  · rintro ⟨h1,h2⟩
    exact ⟨h1, hessian_apply_eq_zero_of_quadratic_eq_zero hf hpos h2⟩

variable [FiniteDimensional ℝ E]

/-- The true third derivative tensor projected orthogonally onto the common kernel
in all three arguments. -/
noncomputable def projectedThirdDerivative (f : E → ℝ) (x : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ :=
  (iteratedFDeriv ℝ 3 f x).compContinuousLinearMap
    (fun _ => (secondOrderKernel f x).starProjection)

/-- Evaluation of the actual orthogonally projected third derivative. -/
@[simp] theorem projectedThirdDerivative_apply (f : E → ℝ) (x : E) (v : Fin 3 → E) :
    projectedThirdDerivative f x v = iteratedFDeriv ℝ 3 f x
      (fun i => (secondOrderKernel f x).starProjection (v i)) := rfl

omit [FiniteDimensional ℝ E] in
/-- On the common first/second derivative kernel, the cubic decrement consists solely
of its cubic term. -/
theorem decrement_three_smul_of_mem_kernel (f : E → ℝ) (x u : E)
    (hu : u ∈ secondOrderKernel f x) (t : ℝ) :
    decrement f 3 x (t • u) = -t ^ 3 * iteratedFDeriv ℝ 3 f x (fun _ => u) / 6 := by
  obtain ⟨h1,h2⟩ := (mem_secondOrderKernel f x u).1 hu
  have h1' : iteratedFDeriv ℝ 1 f x (fun _ => u) = 0 := by
    simpa [iteratedFDeriv_one_apply] using h1
  have h2' : iteratedFDeriv ℝ 2 f x (fun _ => u) = 0 := by
    simp [iteratedFDeriv_two_apply, h2]
  have hh := eval_three_smul f x u t
  rw [h1',h2'] at hh
  rw [decrement_eq]
  linarith

/-- Both opposite cubic displacements bound the absolute cubic derivative on every
unit-ball direction in the common kernel. -/
theorem cubic_abs_le_criticality (f : E → ℝ) (x u : E)
    (hu : u ∈ secondOrderKernel f x) (hun : ‖u‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    |iteratedFDeriv ℝ 3 f x (fun _ => u)| ≤ criticality f 3 x δ / (δ ^ 3 / 6) := by
  have hfeas (t : ℝ) (ht : |t| = δ) : ‖t • u‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs, ht]
    nlinarith
  have hp := decrement_le_criticality f 3 x (hfeas δ (abs_of_pos hδ))
  have hm := decrement_le_criticality f 3 x (hfeas (-δ) (by simp [abs_of_pos hδ]))
  rw [decrement_three_smul_of_mem_kernel f x u hu] at hp hm
  rw [abs_le]
  constructor
  · have hh : -iteratedFDeriv ℝ 3 f x (fun _ => u) ≤ criticality f 3 x δ / (δ ^ 3 / 6) := by
      apply (le_div_iff₀ (show 0 < δ ^ 3 / 6 by positivity)).2
      nlinarith
    linarith
  · apply (le_div_iff₀ (show 0 < δ ^ 3 / 6 by positivity)).2
    nlinarith

/-- The projected third derivative obeys the exact criticality bound (12.1.13). -/
theorem projectedThirdDerivative_diagonalNorm_le (f : E → ℝ) (x : E)
    {δ : ℝ} (hδ : 0 < δ) :
    diagonalNorm (projectedThirdDerivative f x) ≤ criticality f 3 x δ / (δ ^ 3 / 6) := by
  apply diagonalNorm_le
  intro v hv
  rw [projectedThirdDerivative_apply]
  exact cubic_abs_le_criticality f x _
    ((secondOrderKernel f x).starProjection_apply_mem v)
    (((secondOrderKernel f x).norm_starProjection_apply_le v).trans hv) hδ

/-- If cubic criticality is little-o of the radius cubed, the true projected cubic
tensor vanishes in every repeated direction. -/
theorem projectedThirdDerivative_zero_of_tendsto (f : E → ℝ) (x : E)
    (hlim : Filter.Tendsto (fun δ : ℝ => criticality f 3 x δ / δ ^ 3)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    diagonalNorm (projectedThirdDerivative f x) = 0 := by
  have hlim' : Filter.Tendsto (fun δ : ℝ => 6 * (criticality f 3 x δ / δ ^ 3))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hlim.const_mul 6
  apply le_antisymm _ (diagonalNorm_nonneg _)
  apply ge_of_tendsto hlim'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hh := projectedThirdDerivative_diagonalNorm_le f x hδ
  convert hh using 1
  ring

/-- The limiting cubic criticality condition forces the actual third derivative to
vanish on the common first/second-order kernel. -/
theorem third_derivative_zero_on_kernel_of_tendsto (f : E → ℝ) (x : E)
    (hlim : Filter.Tendsto (fun δ : ℝ => criticality f 3 x δ / δ ^ 3)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ v : E, v ∈ secondOrderKernel f x → iteratedFDeriv ℝ 3 f x (fun _ => v) = 0 := by
  intro v hv
  have hz := (diagonalNorm_eq_zero_iff _).1
    (projectedThirdDerivative_zero_of_tendsto f x hlim) v
  rw [projectedThirdDerivative_apply] at hz
  simpa [(secondOrderKernel f x).starProjection_eq_self_iff.mpr hv] using hz

/-- Vanishing quadratic criticality forces zero gradient and a positive semidefinite
actual Hessian. The eigenvalue consequence follows from the Riesz Hessian bridge. -/
theorem first_second_order_of_criticality_two_eq_zero (f : E → ℝ) (x : E)
    {δ : ℝ} (hδ : 0 < δ) (hc : criticality f 2 x δ = 0) :
    gradient f x = 0 ∧ (∀ v : E, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => v)) ∧
    (∀ (μ : ℝ) (v : E), v ≠ 0 → hessianOperator f x v = μ • v → 0 ≤ μ) := by
  have hcrit : criticality f 2 x δ ≤ 0 * δ ^ 2 / 2 := by simp [hc]
  have hg := gradient_norm_le_of_criticality_two f x hδ (by norm_num) (by norm_num) hcrit
  have hgz : gradient f x = 0 := by simpa using norm_le_zero_iff.mp (by simpa using hg)
  refine ⟨hgz, ?_, ?_⟩
  · intro v
    simpa using curvature_ge_neg_mul_sq f x hδ hcrit v
  · intro μ v hv he
    simpa using eigenvalue_ge_neg_of_criticality_two f x hδ hcrit v hv he

end TaylorModel
