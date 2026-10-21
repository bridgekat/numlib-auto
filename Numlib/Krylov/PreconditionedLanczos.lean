import Numlib.Krylov.Preconditioned
import Numlib.Krylov.Lanczos

/-!
# Legal executions of the preconditioned Lanczos recurrence

The residual, inverse application, normalization, and Hessian product are explicit cached
data. A prefix has obligations only before stopping, so breakdown never requires dividing
by zero. A completed execution stops either at breakdown or at its finite iteration budget.
Preconditioning is identified with the existing energy-space geometry.
-/

noncomputable section
open scoped InnerProductSpace
namespace Krylov.PreconditionedLanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The current unnormalized dual residual and the previous normalized dual vector. -/
structure State (E : Type*) where
  residual : E
  previous : E

/-- Cached data from one iteration, with a separate inverse and Hessian application. -/
structure Trial (E : Type*) where
  inverse : E
  gamma : ℝ
  dual : E
  primal : E
  hessian : E
  rho : ℝ

/-- One evaluation of the literal preconditioned recurrence. A legal active iteration
requires its normalization coefficient to be nonzero. -/
def evaluate (H Minv : E →ₗ[ℝ] E) (s : State E) : Trial E :=
  let y := Minv s.residual
  let gamma := Real.sqrt ⟪s.residual, y⟫_ℝ
  let w := gamma⁻¹ • s.residual
  let q := gamma⁻¹ • y
  let Hq := H q
  ⟨y, gamma, w, q, Hq, ⟪q, Hq⟫_ℝ⟩

/-- The residual update uses the cached product and normalized vectors. -/
def next (s : State E) (t : Trial E) : State E :=
  ⟨t.hessian - t.rho • t.dual - t.gamma • s.previous, t.dual⟩

/-- A legal prefix of the preconditioned Lanczos algorithm. No orthogonality, residual
bound, or termination theorem is assumed as a field. -/
structure Prefix (H Minv : E →ₗ[ℝ] E) (g : E) (states : ℕ → State E)
    (trials : ℕ → Trial E) (N : ℕ) : Prop where
  initial : states 0 = ⟨g, 0⟩
  oracle : ∀ k < N, trials k = evaluate H Minv (states k)
  active : ∀ k < N, (trials k).gamma ≠ 0
  update : ∀ k < N, states (k + 1) = next (states k) (trials k)

/-- An execution ends at breakdown, before normalization, or at the iteration budget. -/
structure Execution (H Minv : E →ₗ[ℝ] E) (g : E) (states : ℕ → State E)
    (trials : ℕ → Trial E) (budget N : ℕ) : Prop extends Prefix H Minv g states trials N where
  within_budget : N ≤ budget
  endpoint : N = budget ∨
    ((trials N).inverse = Minv (states N).residual ∧
      (trials N).gamma = Real.sqrt ⟪(states N).residual, (trials N).inverse⟫_ℝ ∧
      (trials N).gamma = 0)

/-- The actual Hessian-product arguments: one at every completed active iteration. -/
def hessianQueries (trials : ℕ → Trial E) (N : ℕ) : List E :=
  List.ofFn (fun i : Fin N => (trials i).primal)

/-- The actual inverse-product arguments. An early breakdown needs one final inverse call
but no final Hessian call. -/
def inverseQueries (states : ℕ → State E) (budget N : ℕ) : List E :=
  List.ofFn (fun i : Fin (N + if N < budget then 1 else 0) => (states i).residual)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The oracle records count exactly the completed Hessian products. -/
@[simp] theorem length_hessianQueries (trials : ℕ → Trial E) (N : ℕ) :
    (hessianQueries trials N).length = N := by simp [hessianQueries]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The inverse count includes an early breakdown test. -/
@[simp] theorem length_inverseQueries (states : ℕ → State E) (budget N : ℕ) :
    (inverseQueries states budget N).length = N + if N < budget then 1 else 0 := by
  simp [inverseQueries]

/-- Each recorded inverse result is the actual inverse-operator application. -/
theorem Prefix.inverse_oracle {H Minv : E →ₗ[ℝ] E} {g : E} {states : ℕ → State E}
    {trials : ℕ → Trial E} {N k : ℕ} (h : Prefix H Minv g states trials N) (hk : k < N) :
    (trials k).inverse = Minv (states k).residual := by
  rw [h.oracle k hk]
  rfl

/-- Each recorded Hessian result is the actual Hessian application at its query argument. -/
theorem Prefix.hessian_oracle {H Minv : E →ₗ[ℝ] E} {g : E} {states : ℕ → State E}
    {trials : ℕ → Trial E} {N k : ℕ} (h : Prefix H Minv g states trials N) (hk : k < N) :
    (trials k).hessian = H (trials k).primal := by
  rw [h.oracle k hk]
  rfl

/-- Every shorter initial segment of a legal prefix is legal. -/
theorem Prefix.mono {H Minv : E →ₗ[ℝ] E} {g : E} {states : ℕ → State E}
    {trials : ℕ → Trial E} {N K : ℕ} (h : Prefix H Minv g states trials N) (hKN : K ≤ N) :
    Prefix H Minv g states trials K :=
  ⟨h.initial, fun k hk => h.oracle k (hk.trans_le hKN),
    fun k hk => h.active k (hk.trans_le hKN), fun k hk => h.update k (hk.trans_le hKN)⟩

/-- The unnormalized residual equals the coefficient times the normalized dual vector
whenever that iteration is active. -/
theorem Prefix.residual_eq_gamma_smul_dual {H Minv : E →ₗ[ℝ] E} {g : E}
    {states : ℕ → State E} {trials : ℕ → Trial E} {N k : ℕ}
    (h : Prefix H Minv g states trials N) (hk : k < N) :
    (states k).residual = (trials k).gamma • (trials k).dual := by
  have hg := h.active k hk
  rw [h.oracle k hk] at hg ⊢
  change (states k).residual = (evaluate H Minv (states k)).gamma •
    ((evaluate H Minv (states k)).gamma⁻¹ • (states k).residual)
  rw [smul_smul, mul_inv_cancel₀ hg, one_smul]

/-- Applying the inverse metric to the normalized dual vector gives the normalized primal
vector, without any invertibility assumption. -/
theorem inverse_dual (H Minv : E →ₗ[ℝ] E) (s : State E) :
    Minv (evaluate H Minv s).dual = (evaluate H Minv s).primal := by
  change Minv ((evaluate H Minv s).gamma⁻¹ • s.residual) =
    (evaluate H Minv s).gamma⁻¹ • Minv s.residual
  rw [map_smul]

variable {M Minv : E →ₗ[ℝ] E} (hM : Krylov.IsPreconditioner M Minv)
include hM

/-- The source square-root normalization is the genuine energy norm of the primal residual. -/
theorem gamma_eq_norm (H : E →ₗ[ℝ] E) (s : State E) :
    (evaluate H Minv s).gamma = ‖hM.toEnergy (Minv s.residual)‖ := by
  have hs : ‖hM.toEnergy (Minv s.residual)‖ ^ 2 = ⟪s.residual, Minv s.residual⟫_ℝ := by
    simpa only [RCLike.re_to_real, hM.apply_inv] using hM.norm_toEnergy_sq (Minv s.residual)
  change Real.sqrt ⟪s.residual, Minv s.residual⟫_ℝ = _
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

/-- Breakdown occurs exactly at a zero residual, including the initial zero gradient. -/
theorem gamma_eq_zero_iff (H : E →ₗ[ℝ] E) (s : State E) :
    (evaluate H Minv s).gamma = 0 ↔ s.residual = 0 := by
  rw [gamma_eq_norm hM, norm_eq_zero, LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    simpa only [hM.apply_inv, map_zero] using congrArg M h
  · intro h; simp [h]

/-- Normalization produces a unit vector in the original metric. -/
theorem norm_primal_eq_one (H : E →ₗ[ℝ] E) (s : State E)
    (hg : (evaluate H Minv s).gamma ≠ 0) :
    ‖hM.toEnergy (evaluate H Minv s).primal‖ = 1 := by
  change ‖hM.toEnergy ((evaluate H Minv s).gamma⁻¹ • Minv s.residual)‖ = 1
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (show 0 ≤ (evaluate H Minv s).gamma from Real.sqrt_nonneg _),
    ← gamma_eq_norm hM H s, inv_mul_cancel₀ hg]

/-- The normalized dual vector is the metric applied to the primal vector. -/
theorem metric_primal (H : E →ₗ[ℝ] E) (s : State E) :
    M (evaluate H Minv s).primal = (evaluate H Minv s).dual := by
  change M ((evaluate H Minv s).gamma⁻¹ • Minv s.residual) =
    (evaluate H Minv s).gamma⁻¹ • s.residual
  rw [map_smul, hM.apply_inv]

/-- The cached Rayleigh quotient is the energy-space Lanczos quotient. -/
theorem rho_eq_energy_inner (H : E →ₗ[ℝ] E) (s : State E) :
    (evaluate H Minv s).rho =
      ⟪hM.toEnergy (evaluate H Minv s).primal,
        hM.energyEnd (Minv ∘ₗ H) (hM.toEnergy (evaluate H Minv s).primal)⟫_ℝ := by
  rw [hM.inner_energyEnd_right]
  rfl

end Krylov.PreconditionedLanczos
