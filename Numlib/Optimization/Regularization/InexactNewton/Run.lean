import Numlib.Optimization.TrustRegion.Regularized.Run
import Numlib.Optimization.TrustRegion.Regularized.Hessian

/-!
# Operational inexact regularized Newton executions

The two regularization bounds follow the coupled source updates. Model slope,
model derivative and subspace-curvature checks use actual derivatives of the
quadratically shifted Taylor model. Projected least curvature is a genuine
minimum of the actual Hessian Rayleigh form on unit vectors in the subspace.
Finite-mode endpoint step computations precede the projected stopping check.
-/

namespace InexactRegularizedNewton
open TaylorModel Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual quadratic Taylor model with its nonnegative multiplier shift. -/
noncomputable abbrev model (f : E → ℝ) (x : E) (ℓ : ℝ) (s : E) : ℝ :=
  RegularizedTrustRegion.model f x ℓ s

/-- The least actual Hessian curvature on a subspace is attained on its unit
sphere and bounds the Rayleigh value of every unit vector in that subspace. -/
structure IsLeastCurvatureOn (f : E → ℝ) (x : E) (V : Submodule ℝ E) (μ : ℝ) : Prop where
  attains : ∃ v : E, v ∈ V ∧ ‖v‖ = 1 ∧ iteratedFDeriv ℝ 2 f x (fun _ => v) = μ
  least : ∀ v : E, v ∈ V → ‖v‖ = 1 → μ ≤ iteratedFDeriv ℝ 2 f x (fun _ => v)

/-- The actual least subspace curvature is unique whenever its unit sphere
is nonempty, as witnessed by either least-curvature certificate. -/
theorem IsLeastCurvatureOn.unique {f : E → ℝ} {x : E} {V : Submodule ℝ E} {μ ν : ℝ}
    (hμ : IsLeastCurvatureOn f x V μ) (hν : IsLeastCurvatureOn f x V ν) : μ = ν := by
  obtain ⟨v, hv, hvn, hval⟩ := hμ.attains
  obtain ⟨w, hw, hwn, hwal⟩ := hν.attains
  exact le_antisymm (by simpa only [hwal] using hμ.least w hw hwn)
    (by simpa only [hval] using hν.least v hv hvn)

/-- Compactness of a nontrivial subspace unit sphere supplies a genuine least
actual Hessian Rayleigh value, without assuming any spectral certificate. -/
theorem exists_leastCurvatureOn (f : E → ℝ) (x : E) (V : Submodule ℝ E)
    [ProperSpace V] [Nontrivial V] : ∃ μ : ℝ, IsLeastCurvatureOn f x V μ := by
  let ψ : V → ℝ := fun v => iteratedFDeriv ℝ 2 f x (fun _ => (v : E))
  have hc : Continuous ψ := (iteratedFDeriv ℝ 2 f x).cont.comp
    (continuous_pi (fun _ => continuous_subtype_val))
  obtain ⟨v, hv⟩ := exists_norm_eq V (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨w, hw, hm⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
    (show (sphere (0 : V) 1).Nonempty from ⟨v, by simpa using hv⟩) hc.continuousOn
  refine ⟨ψ w, ⟨?_, ?_⟩⟩
  · refine ⟨w, w.property, ?_, rfl⟩
    change ‖w‖ = 1
    simpa only [mem_sphere, dist_zero_right] using hw
  · intro z hz hzn
    exact hm (show (⟨z, hz⟩ : V) ∈ sphere (0 : V) 1 by simpa using hzn)

/-- Primitive actual step conditions: feasibility, both slope controls and
model first-derivative control. No step-length lower bound is assumed. -/
structure Step (f : E → ℝ) (x s : E) (ℓ σL σU κ₁ κ₂ κ₃ : ℝ) : Prop where
  multiplier_nonneg : 0 ≤ ℓ
  lower : σL * ‖s‖ ≤ ℓ
  upper : ℓ ≤ σU * ‖s‖
  slope : fderiv ℝ (model f x ℓ) s s ≤ min (κ₁ * ‖s‖ ^ 2)
    ((iteratedFDeriv ℝ 2 (model f x ℓ) s (fun _ => s)) / 2 + κ₂ / 2 * ‖s‖ ^ 3)
  stationary : ‖fderiv ℝ (model f x ℓ) s‖ ≤ ℓ * ‖s‖ + κ₃ * ‖s‖ ^ 2

variable [CompleteSpace E]

/-- Full finite iRN executions, including both stopping modes, actual projected
curvature tests, all coupled parameter updates and every actual trial ratio. -/
structure Run (f : E → ℝ) (x s : ℕ → E) (V : ℕ → Submodule ℝ E)
    (μ ℓ σL σU ρ : ℕ → ℝ)
    (η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ : ℝ)
    (ε₂ : WithTop ℝ) (N : ℕ) : Prop where
  eta_pos : 0 < η
  eta_lt_one : η < 1
  gamma1_gt_one : 1 < γ₁
  gamma1_le_gamma2 : γ₁ ≤ γ₂
  sigmaMin_pos : 0 < σmin
  sigmaMin_le_max : σmin ≤ σmax
  kappa1_pos : 0 < κ₁
  kappa2_pos : 0 < κ₂
  kappa3_pos : 0 < κ₃
  kappa4_pos : 0 < κ₄
  first_accuracy_pos : 0 < ε₁
  first_accuracy_le_one : ε₁ ≤ 1
  second_mode : ε₂ = ⊤ ∨ ∃ e : ℝ, 0 < e ∧ ε₂ = (e : WithTop ℝ)
  lower_initial : σL 0 = 0
  upper_initial : σU 0 ∈ Icc σmin σmax
  step : ∀ i ≤ N, i < N ∨ ε₂ ≠ ⊤ →
    Step f (x i) (s i) (ℓ i) (σL i) (σU i) κ₁ κ₂ κ₃
  least_curvature : ∀ i ≤ N, ε₂ ≠ ⊤ → IsLeastCurvatureOn f (x i) (V i) (μ i)
  curvature : ∀ i ≤ N, ε₂ ≠ ⊤ → ∀ v : E, v ∈ V i → ‖v‖ = 1 →
    -κ₄ * ‖s i‖ ≤ iteratedFDeriv ℝ 2 (model f (x i) (ℓ i)) (s i) (fun _ => v)
  not_terminated : ∀ i < N, ¬RegularizedTrustRegion.Stopped f (x i) (μ i) ε₁ ε₂
  ratio : ∀ i < N, ρ i = (f (x i) - f (x i + s i)) / ‖s i‖ ^ 3
  point_update : ∀ i < N, x (i + 1) = if η ≤ ρ i then x i + s i else x i
  update : ∀ i < N,
    if η ≤ ρ i then σL (i + 1) = 0 ∧ σU (i + 1) = σU i
    else if ℓ i < σmin * ‖s i‖ then
      σL (i + 1) ∈ Icc σmin σmax ∧ σU (i + 1) ∈ Icc (σL (i + 1)) σmax
    else σL (i + 1) = γ₁ * (ℓ i / ‖s i‖) ∧ σU (i + 1) = γ₂ * (ℓ i / ‖s i‖)

/-- A zero computed step forces both its actual current gradient and multiplier
to vanish, directly from feasibility and the model-derivative test. -/
theorem Step.gradient_zero_of_step_zero {f : E → ℝ} {x s : E}
    {ℓ σL σU κ₁ κ₂ κ₃ : ℝ} (h : Step f x s ℓ σL σU κ₁ κ₂ κ₃)
    (hf : ContDiffAt ℝ 2 f x) (hs : s = 0) : gradient f x = 0 ∧ ℓ = 0 := by
  have hℓ : ℓ = 0 := le_antisymm (by simpa only [hs, norm_zero, mul_zero] using h.upper)
    h.multiplier_nonneg
  have hd := h.stationary
  rw [hs, RegularizedTrustRegion.fderiv_model hf] at hd
  simp only [quadraticDerivative, map_zero, add_zero, smul_zero, norm_zero, mul_zero,
    zero_pow (by decide : 2 ≠ 0)] at hd
  have hz : fderiv ℝ f x = 0 := norm_eq_zero.mp (le_antisymm hd (norm_nonneg _))
  have hh := congrArg (InnerProductSpace.toDual ℝ E).symm hz
  have hg : gradient f x = 0 := by
    simpa only [← toDual_gradient, LinearIsometryEquiv.symm_apply_apply, map_zero] using hh
  exact ⟨hg, hℓ⟩

/-- Every nonterminal actual iRN trial step is nonzero. In finite mode the
projected curvature test excludes a zero step when the gradient test passes. -/
theorem Run.step_ne_zero {f : E → ℝ} {x s : ℕ → E} {V : ℕ → Submodule ℝ E}
    {μ ℓ σL σU ρ : ℕ → ℝ}
    {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ : ℝ}
    {ε₂ : WithTop ℝ} {N : ℕ}
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) {i : ℕ} (hi : i < N) : s i ≠ 0 := by
  intro hs
  obtain ⟨hg, hℓ⟩ := (h.step i hi.le (Or.inl hi)).gradient_zero_of_step_zero hf.contDiffAt hs
  have hgrad : ‖gradient f (x i)‖ ≤ ε₁ := by
    rw [hg, norm_zero]
    exact h.first_accuracy_pos.le
  rcases h.second_mode with htop | ⟨e, he, heq⟩
  · apply h.not_terminated i hi
    apply (RegularizedTrustRegion.stopped_iff _ _ _ _ _).mpr
    refine ⟨hgrad, fun e hh => ?_⟩
    rw [htop] at hh
    exact (WithTop.top_ne_coe hh).elim
  · have hnotop : ε₂ ≠ ⊤ := by simp [heq]
    obtain ⟨v, hv, hvn, hval⟩ := (h.least_curvature i hi.le hnotop).attains
    have hc := h.curvature i hi.le hnotop v hv hvn
    rw [RegularizedTrustRegion.iteratedFDeriv_two_model_diag hf.contDiffAt, hvn] at hc
    rw [hs, norm_zero, mul_zero, hℓ, zero_mul, add_zero, hval] at hc
    apply h.not_terminated i hi
    apply (RegularizedTrustRegion.stopped_iff _ _ _ _ _).mpr
    refine ⟨hgrad, ?_⟩
    intro a ha
    have hae : e = a := WithTop.coe_injective (heq.symm.trans ha)
    linarith

end InexactRegularizedNewton
