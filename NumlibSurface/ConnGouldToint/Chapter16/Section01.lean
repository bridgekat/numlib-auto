import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Nonlinear equations and nonlinear least squares -/

open scoped BigOperators

namespace ConnGouldToint.Chapter16

variable {E F ι : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The least-squares objective (16.1.4). -/
noncomputable def leastSquaresObjective (c : E → F) (x : E) : ℝ :=
  ‖c x‖ ^ 2 / 2

/-- The affine Gauss–Newton residual (16.1.6), in step coordinates. -/
def gaussNewtonResidual (c₀ : F) (A : E →L[ℝ] F) (s : E) : F :=
  c₀ + A s

/-- The Newton least-squares model (16.1.7), in step coordinates. -/
noncomputable def newtonLeastSquaresModel [Fintype ι] (c₀ : EuclideanSpace ℝ ι)
    (A : E →L[ℝ] EuclideanSpace ℝ ι) (H : ι → E [×2]→L[ℝ] ℝ) (s : E) : ℝ :=
  ‖c₀‖ ^ 2 / 2 + inner ℝ c₀ (A s) + ‖A s‖ ^ 2 / 2 +
    (∑ i : ι, c₀ i * H i (fun _ ↦ s)) / 2

/-- The quadratic residual model (16.1.8), in step coordinates. -/
noncomputable def quadraticResidual [Fintype ι] (c₀ : EuclideanSpace ℝ ι)
    (A : E →L[ℝ] EuclideanSpace ℝ ι) (H : ι → E [×2]→L[ℝ] ℝ) (s : E) :
    EuclideanSpace ℝ ι :=
  c₀ + A s + (1 / 2 : ℝ) • WithLp.toLp 2 (fun i ↦ H i (fun _ ↦ s))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem leastSquaresObjective_eq_sum [Fintype ι] (c : E → EuclideanSpace ℝ ι) :
    leastSquaresObjective c = fun x ↦ ∑ i : ι, c x i ^ 2 / 2 := by
  funext x
  unfold leastSquaresObjective
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
  simp [Real.norm_eq_abs, sq_abs]

private theorem fderiv_residual_component [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    {x : E} (hc : DifferentiableAt ℝ c x) (i : ι) :
    fderiv ℝ (fun y ↦ c y i) x = (PiLp.proj _ _ i).comp (fderiv ℝ c x) := by
  let p : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj _ _ i
  exact (p.hasFDerivAt.comp x hc.hasFDerivAt).fderiv

private theorem norm_iteratedFDeriv_two_half_sq_le {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    {K : ℝ} (hK : 0 ≤ K)
    (h₀ : ‖u x‖ ≤ K) (h₁ : ‖fderiv ℝ u x‖ ≤ K)
    (h₂ : ‖iteratedFDeriv ℝ 2 u x‖ ≤ K) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ u y ^ 2 / 2) x‖ ≤ 2 * K ^ 2 := by
  have hu' : ContDiffWithinAt ℝ 2 u Set.univ x := hu.contDiffWithinAt
  obtain ⟨s, hs, hx, hus⟩ := hu'.contDiffOn' le_rfl (by norm_num)
  have huOn : ContDiffOn ℝ 2 u s := by simpa using hus
  have h := norm_iteratedFDerivWithin_mul_le huOn huOn (hs.uniqueDiffOn) hx (n := 2)
    (by norm_num)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hs hx] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one] at h
  norm_num at h
  change _ ≤ |u x| * ‖iteratedFDeriv ℝ 2 u x‖ +
    2 * ‖fderiv ℝ u x‖ * ‖iteratedFDeriv ℝ 1 u x‖ +
    ‖iteratedFDeriv ℝ 2 u x‖ * ‖iteratedFDeriv ℝ 0 u x‖ at h
  rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one, ← Real.norm_eq_abs] at h
  have hb : ‖iteratedFDeriv ℝ 2 (fun y ↦ u y * u y) x‖ ≤ 4 * K ^ 2 := by
    have h02 := mul_le_mul h₀ h₂ (norm_nonneg _) hK
    have h11 := mul_le_mul h₁ h₁ (norm_nonneg _) hK
    nlinarith
  have heq : (fun y ↦ u y ^ 2 / 2) = (1 / 2 : ℝ) • (fun y ↦ u y * u y) := by
    funext y
    simp [Pi.smul_apply, div_eq_mul_inv, pow_two, mul_comm]
  rw [heq, iteratedFDeriv_const_smul_apply (hu.mul hu), norm_smul]
  norm_num [Real.norm_eq_abs]
  linarith

private theorem norm_leastSquares_hessian_le [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    {x : E} (hc : ContDiffAt ℝ 2 c x) {K : ℝ} (hK : 0 ≤ K)
    (hval : ‖c x‖ ≤ K) (hjac : ‖fderiv ℝ c x‖ ≤ K)
    (hhess : ∀ i, ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) x‖ ≤ K) :
    ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) x‖ ≤ 2 * (Fintype.card ι : ℝ) * K ^ 2 := by
  let p (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj _ _ i
  have hp (i : ι) : ‖p i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa [p] using PiLp.norm_apply_le z i
  have hci (i : ι) : ContDiffAt ℝ 2 (fun y ↦ c y i) x :=
    (p i).contDiff.contDiffAt.comp x hc
  have hi (i : ι) : ‖fderiv ℝ (fun y ↦ c y i) x‖ ≤ K := by
    rw [fderiv_residual_component (hc.differentiableAt (by norm_num))]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _))).trans (by simpa using hjac)
  rw [leastSquaresObjective_eq_sum,
    iteratedFDeriv_fun_sum_apply fun i _ ↦ ((hci i).pow 2).div_const 2]
  refine (norm_sum_le _ _).trans ?_
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) fun i _ ↦
    norm_iteratedFDeriv_two_half_sq_le (hci i) hK
      ((PiLp.norm_apply_le (c x) i).trans hval) (hi i) (hhess i)
  refine hsum.trans ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- Theorem 16.1.1. A twice continuously differentiable residual with uniformly bounded
values, Jacobian, and component Hessians yields a twice continuously differentiable,
bounded-below least-squares objective with uniformly bounded Hessian. -/
theorem theorem_16_1_1 [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    (hc : ContDiff ℝ 2 c) {K : ℝ} (hK : 0 < K)
    (hval : ∀ x, ‖c x‖ ≤ K) (hjac : ∀ x, ‖fderiv ℝ c x‖ ≤ K)
    (hhess : ∀ i x, ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) x‖ ≤ K) :
    ContDiff ℝ 2 (leastSquaresObjective c) ∧
      (∀ x, 0 ≤ leastSquaresObjective c x) ∧
      ∃ C > 0, ∀ x, ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) x‖ ≤ C := by
  refine ⟨(hc.norm_sq ℝ).div_const 2, fun x ↦ by unfold leastSquaresObjective; positivity,
    2 * (Fintype.card ι : ℝ) * K ^ 2 + 1, by positivity, fun x ↦ ?_⟩
  exact (norm_leastSquares_hessian_le hc.contDiffAt hK.le (hval x) (hjac x)
    (fun i ↦ hhess i x)).trans (le_add_of_nonneg_right zero_le_one)

private theorem fderiv_half_sq {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y ↦ u y ^ 2 / 2) x = u x • fderiv ℝ u x := by
  rw [show (fun y ↦ u y ^ 2 / 2) = (fun y ↦ u y ^ 2 * (2 : ℝ)⁻¹) by simp [div_eq_mul_inv]]
  have h := ((hu.hasFDerivAt.pow 2).mul_const (2 : ℝ)⁻¹).fderiv
  rw [h]
  ext v
  simp only [smul_apply, smul_eq_mul]
  ring

open Filter Topology in
private theorem hessian_half_sq_apply {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (fun y ↦ u y ^ 2 / 2) x v =
      u x * iteratedFDeriv ℝ 2 u x v + fderiv ℝ u x (v 0) * fderiv ℝ u x (v 1) := by
  have hd := hu.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y ↦ u y ^ 2 / 2) =ᶠ[𝓝 x] fun y ↦ u y • fderiv ℝ u y :=
    (hu.eventually (by norm_num)).mono fun _ hy ↦ fderiv_half_sq (hy.differentiableAt (by norm_num))
  rw [iteratedFDeriv_two_apply, heq.fderiv_eq,
    (hd.hasFDerivAt.fun_smul hdd.hasFDerivAt).fderiv, iteratedFDeriv_two_apply]
  simp

/-- Formula (16.1.5) applied to a pair of directions. -/
theorem leastSquares_hessian_apply [Fintype ι] {c : E → EuclideanSpace ℝ ι} {x : E}
    (hc : ContDiffAt ℝ 2 c x) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (leastSquaresObjective c) x v =
      ∑ i : ι, (c x i * iteratedFDeriv ℝ 2 (fun y ↦ c y i) x v +
        fderiv ℝ c x (v 0) i * fderiv ℝ c x (v 1) i) := by
  let p (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj _ _ i
  have hci (i : ι) : ContDiffAt ℝ 2 (fun y ↦ c y i) x :=
    (p i).contDiff.contDiffAt.comp x hc
  rw [leastSquaresObjective_eq_sum,
    iteratedFDeriv_fun_sum_apply (fun i _ ↦ ((hci i).pow 2).div_const 2), sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hessian_half_sq_apply (hci i),
    fderiv_residual_component (hc.differentiableAt (by norm_num))]
  rfl

/-- Formula (16.1.5) for the Hessian discrepancy at a point of first-order agreement. -/
theorem leastSquares_hessian_sub [Fintype ι] {c m : E → EuclideanSpace ℝ ι} {x : E}
    (hc : ContDiffAt ℝ 2 c x) (hm : ContDiffAt ℝ 2 m x) (hval : m x = c x)
    (hjac : fderiv ℝ m x = fderiv ℝ c x) :
    iteratedFDeriv ℝ 2 (leastSquaresObjective c) x -
        iteratedFDeriv ℝ 2 (leastSquaresObjective m) x =
      ∑ i : ι, c x i • (iteratedFDeriv ℝ 2 (fun y ↦ c y i) x -
        iteratedFDeriv ℝ 2 (fun y ↦ m y i) x) := by
  ext v
  rw [sub_apply, leastSquares_hessian_apply hc, leastSquares_hessian_apply hm,
    ← Finset.sum_sub_distrib, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_apply, sub_apply, hval, hjac]
  change _ = c x i * _
  ring

private theorem fderiv_leastSquaresObjective {c : E → F} {x : E}
    (hc : DifferentiableAt ℝ c x) :
    fderiv ℝ (leastSquaresObjective c) x = (innerSL ℝ (c x)).comp (fderiv ℝ c x) := by
  have h := (hc.hasFDerivAt.norm_sq.const_smul ((2 : ℝ)⁻¹)).fderiv
  have heq : (2 : ℝ)⁻¹ • (fun y ↦ ‖c y‖ ^ 2) = leastSquaresObjective c := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, leastSquaresObjective, div_eq_mul_inv, mul_comm]
  rw [← heq, h]
  ext v
  simp only [smul_apply, two_smul, add_apply, smul_eq_mul]
  ring

open Filter Topology in
/-- Theorem 16.1.2 with uniform bounds on residual values and Jacobians throughout the
model regions. Bounds just at the centers do not control the least-squares Hessians
throughout unbounded trust regions. In AM.5e the stationarity test uses the full residual
vector, so it is exactly the test on the least-squares gradient. -/
theorem theorem_16_1_2 [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    {m : ℕ → E → EuclideanSpace ℝ ι} {x : ℕ → E} {B : ℕ → Set E}
    (hc : ∀ k, ContDiffAt ℝ 2 c (x k)) (hx : ∀ k, x k ∈ B k)
    (hm : ∀ k y, y ∈ B k → ContDiffAt ℝ 2 (m k) y)
    (hval : ∀ k, m k (x k) = c (x k))
    (hjac : ∀ k, fderiv ℝ (m k) (x k) = fderiv ℝ c (x k))
    {K : ℝ} (hK : 0 ≤ K)
    (hboundVal : ∀ k y, y ∈ B k → ‖m k y‖ ≤ K)
    (hboundJac : ∀ k y, y ∈ B k → ‖fderiv ℝ (m k) y‖ ≤ K)
    (hboundHess : ∀ k y, y ∈ B k →
      ∀ i, ‖iteratedFDeriv ℝ 2 (fun z ↦ m k z i) y‖ ≤ K) :
    (∀ k y, y ∈ B k → ContDiffAt ℝ 2 (leastSquaresObjective (m k)) y) ∧
    (∀ k, leastSquaresObjective (m k) (x k) = leastSquaresObjective c (x k)) ∧
    (∀ k, fderiv ℝ (leastSquaresObjective (m k)) (x k) =
      fderiv ℝ (leastSquaresObjective c) (x k)) ∧
    (∀ k y, y ∈ B k → ‖iteratedFDeriv ℝ 2 (leastSquaresObjective (m k)) y‖ ≤
      2 * (Fintype.card ι : ℝ) * K ^ 2) ∧
    ((Tendsto (fun k ↦ ‖fderiv ℝ (leastSquaresObjective c) (x k)‖) atTop (𝓝 0) →
      ∀ i, Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) (x k) -
        iteratedFDeriv ℝ 2 (fun y ↦ m k y i) (x k)‖) atTop (𝓝 0)) →
      Tendsto (fun k ↦ ‖fderiv ℝ (leastSquaresObjective c) (x k)‖) atTop (𝓝 0) →
      Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) (x k) -
        iteratedFDeriv ℝ 2 (leastSquaresObjective (m k)) (x k)‖) atTop (𝓝 0)) := by
  refine ⟨fun k y hy ↦ ((hm k y hy).norm_sq ℝ).div_const 2,
    fun k ↦ by simp only [leastSquaresObjective, hval k], ?_,
    fun k y hy ↦ norm_leastSquares_hessian_le (hm k y hy) hK
      (hboundVal k y hy) (hboundJac k y hy) (hboundHess k y hy), ?_⟩
  · intro k
    rw [fderiv_leastSquaresObjective ((hm k (x k) (hx k)).differentiableAt (by norm_num)),
      fderiv_leastSquaresObjective ((hc k).differentiableAt (by norm_num)), hval, hjac]
  · intro ham5 hgrad
    let gap (i : ι) (k : ℕ) := iteratedFDeriv ℝ 2 (fun y ↦ c y i) (x k) -
      iteratedFDeriv ℝ 2 (fun y ↦ m k y i) (x k)
    have ht : Tendsto (fun k ↦ ∑ i : ι, K * ‖gap i k‖) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun i _ ↦ (ham5 hgrad i).const_mul K
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) ht
    rw [leastSquares_hessian_sub (hc k) (hm k (x k) (hx k)) (hval k) (hjac k)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    change ‖c (x k) i • gap i k‖ ≤ K * ‖gap i k‖
    rw [norm_smul]
    have hv := hboundVal k (x k) (hx k)
    rw [hval] at hv
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le _ i).trans hv) (norm_nonneg _)

open Filter Topology in
/-- Theorem 16.1.3. The Gauss–Newton Hessian discrepancy vanishes along any sequence
with residuals tending to zero. This applies to a subsequence approaching a root, as
in (16.1.9). To conclude the full-sequence version of AM.5 by this argument, require
the residuals on that sequence to tend to zero. -/
theorem theorem_16_1_3 [Fintype ι] {c : E → EuclideanSpace ℝ ι} (hc : ContDiff ℝ 2 c)
    {x : ℕ → E} (hres : Tendsto (fun k ↦ c (x k)) atTop (𝓝 0)) {K : ℝ}
    (hhess : ∀ i k, ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) (x k)‖ ≤ K) :
    Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) (x k) -
      iteratedFDeriv ℝ 2 (leastSquaresObjective
        (fun y ↦ gaussNewtonResidual (c (x k)) (fderiv ℝ c (x k)) (y - x k))) (x k)‖)
      atTop (𝓝 0) := by
  let m (k : ℕ) (y : E) :=
    gaussNewtonResidual (c (x k)) (fderiv ℝ c (x k)) (y - x k)
  have hm (k : ℕ) : ContDiff ℝ 2 (m k) :=
    contDiff_const.add ((fderiv ℝ c (x k)).contDiff.comp (contDiff_id.sub contDiff_const))
  have hmval (k : ℕ) : m k (x k) = c (x k) := by
    simp [m, gaussNewtonResidual]
  have hmjac (k : ℕ) (y : E) : fderiv ℝ (m k) y = fderiv ℝ c (x k) := by
    have h := ((fderiv ℝ c (x k)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const (x k))).const_add (c (x k))
    simpa [m, gaussNewtonResidual] using h.fderiv
  have hmhess (k : ℕ) (i : ι) : iteratedFDeriv ℝ 2 (fun y ↦ m k y i) (x k) = 0 := by
    have hfun : fderiv ℝ (fun y ↦ m k y i) =
        fun _ ↦ (PiLp.proj _ _ i).comp (fderiv ℝ c (x k)) := by
      funext y
      rw [fderiv_residual_component ((hm k).differentiable (by norm_num) y), hmjac]
    ext v
    rw [iteratedFDeriv_two_apply, hfun]
    simp
  change Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) (x k) -
    iteratedFDeriv ℝ 2 (leastSquaresObjective (m k)) (x k)‖) atTop (𝓝 0)
  have ht : Tendsto (fun k ↦ (Fintype.card ι : ℝ) * (‖c (x k)‖ * K)) atTop (𝓝 0) := by
    simpa using (hres.norm.mul_const K).const_mul (Fintype.card ι : ℝ)
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) ht
  rw [leastSquares_hessian_sub hc.contDiffAt (hm k).contDiffAt (hmval k) (hmjac k (x k))]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : ι, ‖c (x k)‖ * K := by
      apply Finset.sum_le_sum
      intro i _
      rw [hmhess, sub_zero, norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le (c (x k)) i) (hhess i k)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp

open Filter Topology in
/-- Equation (16.1.9) on a sequence converging to a zero of the residual. -/
theorem theorem_16_1_3_of_tendsto_root [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    (hc : ContDiff ℝ 2 c) {x : ℕ → E} {xStar : E}
    (hx : Tendsto x atTop (𝓝 xStar)) (hroot : c xStar = 0) {K : ℝ}
    (hhess : ∀ i k, ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) (x k)‖ ≤ K) :
    Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) (x k) -
      iteratedFDeriv ℝ 2 (leastSquaresObjective
        (fun y ↦ gaussNewtonResidual (c (x k)) (fderiv ℝ c (x k)) (y - x k))) (x k)‖)
      atTop (𝓝 0) := by
  apply theorem_16_1_3 hc _ hhess
  rw [← hroot]
  exact hc.continuous.continuousAt.tendsto.comp hx

/-- The residual (c=0) and scalar model (m_k(t)=t^2) agree to first order at
every center (x_k=0). The model Hessians are bounded by two, while the Hessians
of the least-squares models are unbounded over the balls of radii (k). -/
theorem theorem_16_1_2_unbounded_radii_counterexample :
    (fun t : ℝ ↦ t ^ 2) 0 = (fun _ : ℝ ↦ (0 : ℝ)) 0 ∧
    fderiv ℝ (fun t : ℝ ↦ t ^ 2) 0 = fderiv ℝ (fun _ : ℝ ↦ (0 : ℝ)) 0 ∧
    (∀ t : ℝ, ‖iteratedFDeriv ℝ 2 (fun y : ℝ ↦ y ^ 2) t‖ ≤ 2) ∧
    ¬ ∃ K : ℝ, ∀ (k : ℕ) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) k →
      ‖iteratedFDeriv ℝ 2 (leastSquaresObjective (fun y : ℝ ↦ y ^ 2)) t‖ ≤ K := by
  have hsq : ContDiff ℝ 2 (fun y : ℝ ↦ y ^ 2) := contDiff_id.pow 2
  have hderiv (t : ℝ) : fderiv ℝ (fun y : ℝ ↦ y ^ 2) t =
      (2 * t) • ContinuousLinearMap.id ℝ ℝ := by
    have h := ((hasFDerivAt_id (𝕜 := ℝ) t).pow 2).fderiv
    change fderiv ℝ (fun y : ℝ ↦ y ^ 2) t = _ at h
    rw [h]
    congr 1
    simp [two_mul]
  have hid (t : ℝ) (v : Fin 2 → ℝ) : iteratedFDeriv ℝ 2 id t v = 0 := by
    have hf : fderiv ℝ (id : ℝ → ℝ) = fun _ ↦ ContinuousLinearMap.id ℝ ℝ :=
      funext fun y ↦ (hasFDerivAt_id y).fderiv
    rw [iteratedFDeriv_two_apply, hf]
    simp
  have hess (t : ℝ) (v : Fin 2 → ℝ) :
      iteratedFDeriv ℝ 2 (fun y : ℝ ↦ y ^ 2) t v = 2 * v 0 * v 1 := by
    have heq : (fun y : ℝ ↦ y ^ 2) = (2 : ℝ) • (fun y : ℝ ↦ y ^ 2 / 2) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hhalf := hessian_half_sq_apply (x := t) (u := id) contDiff_id.contDiffAt v
    change iteratedFDeriv ℝ 2 (fun y : ℝ ↦ y ^ 2 / 2) t v = _ at hhalf
    rw [heq, iteratedFDeriv_const_smul_apply ((hsq.div_const 2).contDiffAt),
      smul_apply, hhalf, hid]
    rw [(hasFDerivAt_id (𝕜 := ℝ) t).fderiv]
    simp [mul_assoc]
  refine ⟨by simp, by simp [hderiv], fun t ↦ ?_, ?_⟩
  · apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
    intro v
    rw [hess, Fin.prod_univ_two]
    simp [norm_mul, mul_assoc]
  · rintro ⟨K, hK⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (max K 1)
    have hk₀ : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk₁ : (1 : ℝ) < k := (le_max_right K 1).trans_lt hk
    have hball : (k : ℝ) ∈ Metric.closedBall (0 : ℝ) k := by
      simp [Metric.mem_closedBall]
    let v : Fin 2 → ℝ := fun _ ↦ 1
    have hl := (iteratedFDeriv ℝ 2 (leastSquaresObjective (fun y : ℝ ↦ y ^ 2))
      (k : ℝ)).le_opNorm v
    have hval : iteratedFDeriv ℝ 2 (leastSquaresObjective (fun y : ℝ ↦ y ^ 2))
        (k : ℝ) v = 6 * (k : ℝ) ^ 2 := by
      have heq : leastSquaresObjective (fun y : ℝ ↦ y ^ 2) =
          (fun y : ℝ ↦ (y ^ 2) ^ 2 / 2) := by
        funext y
        simp [leastSquaresObjective, Real.norm_eq_abs]
      rw [heq, hessian_half_sq_apply hsq.contDiffAt, hess, hderiv]
      simp [v]
      ring
    rw [hval] at hl
    have hle : 6 * (k : ℝ) ^ 2 ≤ K := by
      simpa [v, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 6 * (k : ℝ) ^ 2)]
        using hl.trans (by simpa [v] using hK k k hball)
    have hlt := (le_max_left K 1).trans_lt hk
    nlinarith [mul_nonneg (sub_nonneg.mpr hk₁.le) hk₀]

end ConnGouldToint.Chapter16
