import Numlib.Optimization.TrustRegion.FirstOrder
import Numlib.Optimization.HighOrder.CriticalityApproximate
import Numlib.Analysis.Calculus.ContDiff.Lipschitz

/-!
# First-order complexity interfaces for second-order trust-region methods

The canonical Riesz Hessian has exactly the actual second-derivative tensor norm.
Its quadratic model is the true second-degree Taylor polynomial. A uniformly
bounded Hessian gives Lipschitz continuity of the actual gradient by the iterated
derivative mean-value equivalence.

The operational trace covers precisely TR2 with its second-order test explicitly
set to infinity. Its Cauchy point minimizes the actual Taylor polynomial on the
negative-gradient ray. This trace converts to TR1 with the canonical Hessian as
model operator. Derivative counts include initialization and accepted trial points.
The complete finite-second-order-test TR2 algorithm is a separate specification.

Scalar constant identities recover the printed TR2 successful-iteration coefficient
and its initial-gradient-dependent logarithmic allowance from the TR1 estimates.
-/

open Set
namespace SecondOrderTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual Hessian as a continuous linear operator through Riesz duality. -/
noncomputable def hessian (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (fderiv ℝ (fderiv ℝ f) x)

/-- The Hessian operator is the Riesz representative of the actual second derivative. -/
@[simp] theorem hessian_apply (f : E → ℝ) (x v : E) :
    hessian f x v = TaylorModel.hessianOperator f x v := rfl

/-- The Hessian operator norm is bounded by the true second-derivative tensor norm. -/
theorem norm_hessian_le (f : E → ℝ) (x : E) :
    ‖hessian f x‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
  have hn : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
    rw [←norm_iteratedFDeriv_one (fderiv ℝ f),norm_iteratedFDeriv_fderiv]
  rw [←hn]
  apply (hessian f x).opNorm_le_bound (norm_nonneg (fderiv ℝ (fderiv ℝ f) x))
  intro v
  change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) x v)‖ ≤ _
  rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
  exact (fderiv ℝ (fderiv ℝ f) x).le_opNorm v

/-- Riesz duality and bilinear currying preserve the exact Hessian norm. -/
@[simp] theorem norm_hessian (f : E → ℝ) (x : E) :
    ‖hessian f x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  apply le_antisymm (norm_hessian_le f x)
  rw [←norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one]
  apply (fderiv ℝ (fderiv ℝ f) x).opNorm_le_bound (norm_nonneg _)
  intro v
  rw [←(InnerProductSpace.toDual ℝ E).symm.norm_map]
  exact (hessian f x).le_opNorm v

/-- The quadratic model built from the actual gradient and Hessian is the Taylor polynomial. -/
theorem model_eq_taylor (f : E → ℝ) (x s : E) :
    QuadraticTrustRegion.model (f x) (gradient f x) (hessian f x) s =
      TaylorModel.eval f 2 x s := by
  have he := TaylorModel.eval_two f x s
  rw [iteratedFDeriv_one_apply,←inner_gradient_left] at he
  have hv : (![s,s] : Fin 2 → E) = (fun _ => s) := by ext i; fin_cases i <;> rfl
  have hH := TaylorModel.inner_hessianOperator f x s s
  rw [hv] at hH
  have hdiag : inner ℝ s (hessian f x s) =
      iteratedFDeriv ℝ 2 f x (fun _ => s) := by
    rw [real_inner_comm,hessian_apply]
    exact hH
  simp only [QuadraticTrustRegion.model,hdiag]
  linarith

/-- A uniformly bounded actual Hessian makes the actual gradient globally Lipschitz. -/
theorem gradient_lipschitz_of_hessian_bound {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {H : ℝ} (hH : 0 ≤ H) (hbound : ∀ x, ‖hessian f x‖ ≤ H) :
    ∀ x y, ‖gradient f x - gradient f y‖ ≤ H * ‖x - y‖ := by
  have hLip : LipschitzOnWith ⟨H,hH⟩ (iteratedFDeriv ℝ 1 f) univ :=
    (lipschitzOnWith_iteratedFDeriv_iff_norm_le isOpen_univ convex_univ hf.contDiffOn).2
      (fun x _ => by
        change ‖iteratedFDeriv ℝ 2 f x‖ ≤ H
        rw [←norm_hessian]
        exact hbound x)
  intro x y
  have ht := hLip.norm_sub_le (mem_univ x) (mem_univ y)
  rw [←(InnerProductSpace.toDual ℝ E).norm_map (gradient f x - gradient f y),
    map_sub,toDual_gradient,toDual_gradient]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he := (iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y).le_opNorm (fun _ => v)
  have hm := mul_le_mul_of_nonneg_right ht (norm_nonneg v)
  have he' : ‖(fderiv ℝ f x - fderiv ℝ f y) v‖ ≤
      ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ * ‖v‖ := by
    simpa [Fin.prod_const] using he
  exact he'.trans hm

/-- Actual Cauchy minimization for the quadratic Taylor polynomial. -/
def IsCauchyPoint (f : E → ℝ) (x : E) (Δ : ℝ) (sC : E) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ ‖t • gradient f x‖ ≤ Δ ∧ sC = -(t • gradient f x) ∧
    IsMinOn (fun u : ℝ => TaylorModel.eval f 2 x (-(u • gradient f x)))
      {u | 0 ≤ u ∧ ‖u • gradient f x‖ ≤ Δ} t

/-- The actual-Taylor and explicit quadratic Cauchy-point specifications agree. -/
theorem isCauchyPoint_iff (f : E → ℝ) (x : E) (Δ : ℝ) (sC : E) :
    IsCauchyPoint f x Δ sC ↔
      QuadraticTrustRegion.IsCauchyPoint (f x) (gradient f x) (hessian f x) Δ sC := by
  simp only [IsCauchyPoint,QuadraticTrustRegion.IsCauchyPoint,model_eq_taylor]

/-- A Cauchy point exists for every nonnegative radius. -/
theorem exists_cauchyPoint (f : E → ℝ) (x : E) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ sC, IsCauchyPoint f x Δ sC := by
  obtain ⟨sC,hsC⟩ := QuadraticTrustRegion.exists_cauchyPoint
    (f x) (gradient f x) (hessian f x) hΔ
  exact ⟨sC,(isCauchyPoint_iff f x Δ sC).mpr hsC⟩

/-- The complete operational TR2 rules in the explicitly disabled-second-test mode. -/
structure FirstOrderRun (f : E → ℝ) (x s sC : ℕ → E) (Δ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ ε₁ : ℝ) (ε₂ : WithTop ℝ) (N : ℕ) : Prop where
  second_order_disabled : ε₂ = ⊤
  updates : EvaluationComplexity.TrustRegionRadiusUpdates Δ ρ η₁ η₂ γ₁ γ₂ γ₃ N
  accuracy_pos : 0 < ε₁
  not_terminated : ∀ i < N, ε₁ < ‖gradient f (x i)‖
  cauchy : ∀ i < N, IsCauchyPoint f (x i) (Δ i) (sC i)
  feasible_step : ∀ i < N, ‖s i‖ ≤ Δ i
  model_step : ∀ i < N, TaylorModel.eval f 2 (x i) (s i) ≤ TaylorModel.eval f 2 (x i) (sC i)
  ratio : ∀ i < N, ρ i = (f (x i) - f (x i + s i)) /
    (TaylorModel.eval f 2 (x i) 0 - TaylorModel.eval f 2 (x i) (s i))
  step : ∀ i < N, x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i

/-- A TR2 prefix with its second-order test disabled is a genuine TR1 prefix
with the actual Hessian as its quadratic model operator. -/
theorem FirstOrderRun.to_firstOrder {f : E → ℝ} {x s sC : ℕ → E} {Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ ε₁ : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}
    (h : FirstOrderRun f x s sC Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) :
    FirstOrderTrustRegion.Run f (gradient f) x s sC (fun i => hessian f (x i))
      Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ N where
  derivative := by
    intro y
    convert ((hf.differentiable (by norm_num)) y).hasFDerivAt using 1
    ext v
    simp [innerSL_apply_apply,inner_gradient_left]
  updates := h.updates
  accuracy_pos := h.accuracy_pos
  not_terminated := h.not_terminated
  cauchy := fun i hi => (isCauchyPoint_iff f (x i) (Δ i) (sC i)).mp (h.cauchy i hi)
  feasible_step := h.feasible_step
  model_step := fun i hi => by simpa only [model_eq_taylor] using h.model_step i hi
  ratio := fun i hi => by simpa only [model_eq_taylor] using h.ratio i hi
  step := h.step
/-- Function calls comprise the initial objective and one call per trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Gradient and Hessian calls comprise initialization and accepted trial points. -/
noncomputable def derivativeEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  (EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} N).card + 1
/-- Gradient evaluations follow the accepted-point count. -/
noncomputable abbrev gradientEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  derivativeEvaluations ρ η₁ N

/-- Hessian evaluations follow the same accepted-point count, as required by TR2. -/
noncomputable abbrev hessianEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  derivativeEvaluations ρ η₁ N
end SecondOrderTrustRegion

namespace FirstOrderTrustRegion
/-- With exact Hessians, the radius coefficient is the smaller term in the
Cauchy-decrease constant, giving the explicit second-order-method constant. -/
theorem decreaseConstant_self {G Δ η γ H : ℝ}
    (hG : 0 < G) (hΔ : 0 < Δ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hH : 1 ≤ H) :
    decreaseConstant G Δ η γ H H = γ * (1 - η) / (8 * H) * min 1 (Δ / G) := by
  have hHp : 0 < H := by linarith
  have hc : 0 ≤ γ * (1 - η) / (4 * H) := by positivity
  have hmul : γ * (1 - η) ≤ 1 := by nlinarith
  have hm : 0 ≤ min 1 (Δ / G) := le_min (by norm_num) (div_nonneg hΔ.le hG.le)
  have hrad : radiusConstant G Δ η γ H H ≤ 1 / (1 + H) := by
    calc
      radiusConstant G Δ η γ H H = γ * (1 - η) / (4 * H) * min 1 (Δ / G) := by
        unfold radiusConstant
        ring
      _ ≤ γ * (1 - η) / (4 * H) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left 1 (Δ / G)) hc
      _ ≤ 1 / (4 * H) := div_le_div_of_nonneg_right hmul (by positivity)
      _ ≤ 1 / (1 + H) := one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [decreaseConstant,min_eq_right hrad]
  unfold radiusConstant
  ring

/-- Simplifying the successful-iteration coefficient for an exact Hessian model. -/
theorem inv_decreaseConstant_self {G Δ η₁ η₂ γ H : ℝ}
    (hG : 0 < G) (hΔ : 0 < Δ) (hη₁ : 0 < η₁) (hη₂0 : 0 ≤ η₂) (hη₂1 : η₂ < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hH : 1 ≤ H) :
    1 / (η₁ * decreaseConstant G Δ η₂ γ H H) =
      8 * H / (γ * η₁ * (1 - η₂)) * max 1 (G / Δ) := by
  rw [decreaseConstant_self hG hΔ hη₂0 hη₂1 hγ0 hγ1 hH]
  by_cases hd : Δ ≤ G
  · have hmin : Δ / G ≤ 1 := (div_le_one hG).mpr hd
    have hmax : 1 ≤ G / Δ := (le_div_iff₀ hΔ).mpr (by simpa using hd)
    rw [min_eq_right hmin,max_eq_right hmax]
    field_simp
  · have hmin : 1 ≤ Δ / G := (le_div_iff₀ hG).mpr (by linarith)
    have hmax : G / Δ ≤ 1 := (div_le_one hΔ).mpr (by linarith)
    rw [min_eq_left hmin,max_eq_left hmax]
    field_simp

/-- The radius coefficient from the initial gradient gives at least the
logarithmic allowance supplied by the uniform small-radius threshold. -/
theorem log_initial_radius_le {G Δ c : ℝ} (hG : 0 < G) (hΔ : 0 < Δ) (hc : 0 < c) :
    |Real.log (min Δ c / Δ)| ≤ |Real.log (c * min 1 (Δ / G) / Δ)| := by
  by_cases hd : Δ ≤ c
  · rw [min_eq_left hd,div_self hΔ.ne',Real.log_one,abs_zero]
    exact abs_nonneg _
  · have hdc : c < Δ := by linarith
    have hrp : 0 < c / Δ := div_pos hc hΔ
    have hrp1 : c / Δ ≤ 1 := (div_le_one hΔ).mpr hdc.le
    have hms : 0 < min 1 (Δ / G) := lt_min (by norm_num) (div_pos hΔ hG)
    have hrs : 0 < c * min 1 (Δ / G) / Δ := div_pos (mul_pos hc hms) hΔ
    have hrs_le : c * min 1 (Δ / G) / Δ ≤ c / Δ := by
      exact div_le_div_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left 1 (Δ / G)) hc.le)
        hΔ.le
    rw [min_eq_right hdc.le,abs_of_nonpos (Real.log_nonpos hrp.le hrp1),
      abs_of_nonpos (Real.log_nonpos hrs.le (hrs_le.trans hrp1))]
    exact neg_le_neg (Real.log_le_log hrs hrs_le)
end FirstOrderTrustRegion
