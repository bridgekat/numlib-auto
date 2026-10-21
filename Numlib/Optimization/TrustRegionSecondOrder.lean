import Numlib.Optimization.TrustRegion
import Numlib.Optimization.HessianCurvature
import Numlib.Optimization.CubicRegularization
import Numlib.Analysis.Calculus.Gradient

/-!
# Trust-region methods with the true Hessian

The quadratic model uses the Riesz representation of the actual second derivative. The
optional curvature condition compares the trial to the signed least-curvature boundary point.
For negative curvature that point minimizes the model on its feasible nonnegative ray.
-/
open scoped Nat
noncomputable section
namespace Optimization.TrustRegionSecondOrder
open InnerProductSpace QuadraticSubproblem
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Riesz-represented actual Hessian. -/
def hessianOperator (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ f) x)

/-- Least Rayleigh curvature of the actual Hessian. -/
def curvature (f : E → ℝ) (x : E) : ℝ :=
  leastCurvature (fderiv ℝ (fderiv ℝ f) x)

/-- A lawful second-order trust-region trace. A Boolean switches the eigenpoint condition
on or off; stopping tolerances are tested separately and never encoded by an infinity sentinel. -/
structure IsRun (p : TrustRegion.Parameters) (second : Bool) (f : E → ℝ)
    (x s : ℕ → E) (delta : ℕ → ℝ) : Prop extends
    TrustRegion.IsRun p f (gradient f) (fun k => hessianOperator f (x k)) x s delta where
  eigen : second = true → ∀ k, curvature f (x k) < 0 → ∃ u : E,
    ‖u‖ = 1 ∧ fderiv ℝ (fderiv ℝ f) (x k) u u = curvature f (x k) ∧
    inner ℝ (gradient f (x k)) u ≤ 0 ∧
    quadratic (gradient f (x k)) (hessianOperator f (x k)) (s k) ≤
      quadratic (gradient f (x k)) (hessianOperator f (x k)) (delta k • u)

/-- The quadratic model agrees exactly with the canonical second-order Taylor polynomial. -/
theorem taylorModel_eq (f : E → ℝ) (x s : E) :
    RegularizedTaylorModel.taylorModel f 2 x s =
      f x + quadratic (gradient f x) (hessianOperator f x) s := by
  rw [show RegularizedTaylorModel.taylorModel f 2 x s =
    RegularizedTaylorModel.taylorModel f 1 x s +
      (2! : ℝ)⁻¹ • iteratedFDeriv ℝ 2 f x (fun _ => s)
      from RegularizedTaylorModel.taylorModel_succ f 1 x s]
  simp only [RegularizedTaylorModel.taylorModel_one, iteratedFDeriv_two_apply, smul_eq_mul]
  rw [fderiv_eq_innerSL_gradient]
  dsimp [quadratic, hessianOperator]
  have hi : inner ℝ s (continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ f) x) s) =
      fderiv ℝ (fderiv ℝ f) x s s := by
    rw [real_inner_comm]
    exact continuousLinearMapOfBilin_apply _ _ _
  rw [hi]
  norm_num
  ring

/-- A signed normalized eigenvector for the actual minimum Hessian eigenvalue. -/
theorem exists_signed_eigenvector [FiniteDimensional ℝ E] [Nontrivial E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∃ u : E, ‖u‖ = 1 ∧ hessianOperator f x u = curvature f x • u ∧
      inner ℝ (gradient f x) u ≤ 0 := by
  obtain ⟨v, hv, hv0⟩ := (hasEigenvalue_leastCurvature (hessian_symmetric hf)).exists_hasEigenvector
  have he : hessianOperator f x v = curvature f x • v :=
    Module.End.mem_eigenspace_iff.mp hv
  let u := NormedSpace.normalize v
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hv0
  have heu : hessianOperator f x u = curvature f x • u := by
    simp only [u, NormedSpace.normalize, map_smul, he, smul_smul]
    rw [mul_comm]
  by_cases hs : inner ℝ (gradient f x) u ≤ 0
  · exact ⟨u, hu, heu, hs⟩
  · exact ⟨-u, by simpa using hu, by simpa using congrArg Neg.neg heu,
      by simpa using (neg_nonpos.mpr (le_of_not_ge hs))⟩

/-- A signed unit direction attaining the least Hessian curvature exists in finite dimension. -/
theorem exists_signed_unit [FiniteDimensional ℝ E] [Nontrivial E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∃ u : E, ‖u‖ = 1 ∧ fderiv ℝ (fderiv ℝ f) x u u = curvature f x ∧
      inner ℝ (gradient f x) u ≤ 0 := by
  obtain ⟨u, hu, he, hg⟩ := exists_signed_eigenvector hf
  refine ⟨u, hu, ?_, hg⟩
  rw [← continuousLinearMapOfBilin_apply _ u u]
  change inner ℝ (hessianOperator f x u) u = _
  rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
  ring

/-- On a signed negative-curvature unit ray, its boundary point is an exact ray minimizer. -/
theorem quadratic_boundary_le {g : E} {B : E →L[ℝ] E →L[ℝ] ℝ} {u : E}
    {lambda delta t : ℝ} (hgu : inner ℝ g u ≤ 0) (hB : B u u = lambda)
    (hl : lambda < 0) (ht : 0 ≤ t) (htd : t ≤ delta) :
    quadratic g (continuousLinearMapOfBilin B) (delta • u) ≤
      quadratic g (continuousLinearMapOfBilin B) (t • u) := by
  have hdt : 0 ≤ delta := ht.trans htd
  have h1 := mul_le_mul_of_nonpos_right htd hgu
  have h2 := mul_le_mul_of_nonpos_right (show t ^ 2 ≤ delta ^ 2 by nlinarith) hl.le
  simp only [quadratic, real_inner_smul_left, real_inner_smul_right, map_smul]
  have hi : inner ℝ u (continuousLinearMapOfBilin B u) = lambda := by
    rw [real_inner_comm]
    exact (continuousLinearMapOfBilin_apply B u u).trans hB
  rw [hi]
  nlinarith only [h1, h2]

/-- Eigenpoint dominance yields the standard negative-curvature model reduction. -/
theorem IsRun.curvature_decrease
    {p : TrustRegion.Parameters} {f : E → ℝ} {x s : ℕ → E} {delta : ℕ → ℝ}
    (h : IsRun p true f x s delta) (k : ℕ)
    (hl : curvature f (x k) < 0) :
    (1 / 2 : ℝ) * |curvature f (x k)| * delta k ^ 2 ≤
      quadratic (gradient f (x k)) (hessianOperator f (x k)) 0 -
        quadratic (gradient f (x k)) (hessianOperator f (x k)) (s k) := by
  obtain ⟨u, _hu, hB, hgu, he⟩ := h.eigen rfl k hl
  have hd := h.toIsRun.radius_pos k
  have hi : inner ℝ u (hessianOperator f (x k) u) = curvature f (x k) := by
    rw [real_inner_comm, hessianOperator, continuousLinearMapOfBilin_apply, hB]
  simp only [quadratic, map_smul, real_inner_smul_left, real_inner_smul_right] at he ⊢
  rw [hi] at he
  rw [abs_of_neg hl]
  have hlin := mul_nonpos_of_nonneg_of_nonpos hd.le hgu
  simp only [inner_zero_right, map_zero, mul_zero, add_zero, zero_sub]
  nlinarith only [he, hlin]

/-- Riesz representation preserves the operator norm of the bilinear Hessian. -/
theorem norm_hessianOperator (f : E → ℝ) (x : E) :
    ‖hessianOperator f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  apply ContinuousLinearMap.opNorm_ext
  intro u
  exact (toDual ℝ E).symm.norm_map _

/-- A uniform actual Hessian bound gives the same Lipschitz bound for the gradient. -/
theorem gradient_lipschitz_of_hessian_bound {f : E → ℝ} {B : ℝ}
    (hf : ContDiff ℝ 2 f) (hB : ∀ y, ‖hessianOperator f y‖ ≤ B) (x y : E) :
    ‖gradient f x - gradient f y‖ ≤ B * ‖x - y‖ := by
  have hc : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ f) := hc.differentiable (by norm_num)
  have ht := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (Set.univ : Set E)) => hd z)
    (fun z (_ : z ∈ (Set.univ : Set E)) => by rw [← norm_hessianOperator]; exact hB z)
    (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ y) (Set.mem_univ x)
  have he : ‖gradient f x - gradient f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
    change ‖(toDual ℝ E).symm (fderiv ℝ f x) - (toDual ℝ E).symm (fderiv ℝ f y)‖ = _
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  rwa [he]

/-- A sufficiently small radius is very successful in the negative-curvature case, even if
its gradient vanishes. The multiplicative form also covers zero Hessian Lipschitz constant. -/
theorem IsRun.ratio_ge_of_curvature_radius
    {p : TrustRegion.Parameters} {f : E → ℝ} {x s : ℕ → E} {delta : ℕ → ℝ}
    (h : IsRun p true f x s delta) {L : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (k : ℕ)
    (hl : curvature f (x k) < 0)
    (hsmall : L * delta k ≤ 3 * (1 - p.eta2) * |curvature f (x k)|) :
    p.eta2 ≤ TrustRegion.ratio f (gradient f (x k)) (hessianOperator f (x k))
      (x k) (s k) := by
  have hd := h.toIsRun.radius_pos k
  have hc := h.curvature_decrease k hl
  have ha : 0 < |curvature f (x k)| := abs_pos.mpr hl.ne
  have hp : 0 < quadratic (gradient f (x k)) (hessianOperator f (x k)) 0 -
      quadratic (gradient f (x k)) (hessianOperator f (x k)) (s k) :=
    (mul_pos (mul_pos (by norm_num) ha) (sq_pos_of_pos hd)).trans_le hc
  unfold TrustRegion.ratio
  rw [le_div_iff₀ hp]
  have ht := (abs_le.mp (hf.value_remainder (x k) (s k))).2
  rw [taylorModel_eq] at ht
  have hs3 : ‖s k‖ ^ 3 ≤ delta k ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (h.toIsRun.feasible k) 3
  have he := mul_le_mul_of_nonneg_left hs3 (div_nonneg hf.nonneg (by norm_num : (0 : ℝ) ≤ 6))
  have hsc := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (delta k))
  have hpc := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr p.eta2_lt_one.le)
  simp only [quadratic_zero] at *
  nlinarith only [ht, he, hsc, hpc]

/-- The first-order complexity bound specializes to exact Hessian models, with constants
independent of the positive gradient tolerance. -/
theorem IsRun.exists_firstOrder_complexity_constants
    {p : TrustRegion.Parameters} {second : Bool} {f : E → ℝ}
    {x s : ℕ → E} {delta : ℕ → ℝ} (h : IsRun p second f x s delta)
    {B low : ℝ} (hf : ContDiff ℝ 2 f) (hB : 1 ≤ B)
    (hbound : ∀ y, ‖hessianOperator f y‖ ≤ B) (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kB kC : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kB ∧ 0 < kC ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ,
        ‖gradient f (x K)‖ ≤ epsilon ∧
        (∀ j < K, epsilon < ‖gradient f (x j)‖) ∧
        (K : ℝ) + 1 ≤ kA * ((f (x 0) - low) / epsilon ^ 2) +
          kB * |Real.log epsilon| + kC ∧
        (ParameterUpdates.successCount
          (fun k => p.eta1 ≤ TrustRegion.ratio f (gradient f (x k))
            (hessianOperator f (x k)) (x k) (s k)) K : ℝ) + 1 ≤
          kS * ((f (x 0) - low) / epsilon ^ 2) + 1 := by
  apply h.toIsRun.exists_complexity_constants
    (L := B) (B := B) ?_ (gradient_lipschitz_of_hessian_bound hf hbound) hB
    (fun k => hbound (x k)) hlow
  intro y
  rw [← fderiv_eq_innerSL_gradient]
  exact (hf.differentiable (by norm_num) y).hasFDerivAt

/-- The joint gradient/curvature stopping test. -/
def Stationary (f : E → ℝ) (epsilon1 epsilon2 : ℝ) (y : E) : Prop :=
  ‖gradient f y‖ ≤ epsilon1 ∧ -epsilon2 ≤ curvature f y

/-- Failure of the joint test is the gradient or negative-curvature alternative. -/
theorem not_stationary_iff {f : E → ℝ} {epsilon1 epsilon2 : ℝ} {y : E} :
    ¬Stationary f epsilon1 epsilon2 y ↔
      epsilon1 < ‖gradient f y‖ ∨ curvature f y < -epsilon2 := by
  simp only [Stationary, not_and_or, not_le]

/-- A small radius relative to a failed joint test makes the trial very successful. -/
theorem IsRun.ratio_ge_of_joint_radius
    {p : TrustRegion.Parameters} {f : E → ℝ} {x s : ℕ → E} {delta : ℕ → ℝ}
    (h : IsRun p true f x s delta) {B L epsilon1 epsilon2 : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hB : 1 ≤ B)
    (hbound : ∀ y, ‖hessianOperator f y‖ ≤ B)
    (he2 : 0 < epsilon2) (k : ℕ)
    (htest : ¬Stationary f epsilon1 epsilon2 (x k))
    (hsmall1 : delta k < ((1 - p.eta2) / (4 * B)) * min epsilon1 epsilon2)
    (hsmall2 : delta k < (3 * (1 - p.eta2) / (L + 1)) * min epsilon1 epsilon2) :
    p.eta2 ≤ TrustRegion.ratio f (gradient f (x k)) (hessianOperator f (x k))
      (x k) (s k) := by
  have heta : 0 < 1 - p.eta2 := sub_pos.mpr p.eta2_lt_one
  rcases not_stationary_iff.mp htest with hg | hc
  · have hderiv : ∀ y, HasFDerivAt f (innerSL ℝ (gradient f y)) y := by
      intro y
      rw [← fderiv_eq_innerSL_gradient]
      exact (hf.smooth.differentiable (by norm_num) y).hasFDerivAt
    apply h.toIsRun.ratio_ge_of_radius_lt (L := B) (B := B) hderiv
      (gradient_lipschitz_of_hessian_bound hf.smooth hbound) hB (fun k => hbound (x k)) k
    have hh := mul_le_mul_of_nonneg_left ((min_le_left epsilon1 epsilon2).trans hg.le)
      (div_nonneg heta.le (by positivity : (0 : ℝ) ≤ 4 * B))
    convert hsmall1.trans_le hh using 1; ring
  · apply h.ratio_ge_of_curvature_radius hf k (hc.trans (neg_neg_of_pos he2))
    have hmin : min epsilon1 epsilon2 ≤ |curvature f (x k)| := by
      rw [abs_of_neg (hc.trans (neg_neg_of_pos he2))]
      linarith only [min_le_right epsilon1 epsilon2, hc]
    have hh : delta k * (L + 1) < 3 * (1 - p.eta2) * min epsilon1 epsilon2 := by
      apply (lt_div_iff₀ (by linarith [hf.nonneg] : 0 < L + 1)).mp
      convert hsmall2 using 1; ring
    have hm := mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ 3 * (1 - p.eta2))
    have hd := h.toIsRun.radius_pos k
    nlinarith only [hh, hm, hd]

/-- Any positive radius coefficient compatible with the two success thresholds bounds every
prefix whose earlier iterates fail the joint stopping test. -/
theorem IsRun.radius_lower_before_joint_test
    {p : TrustRegion.Parameters} {f : E → ℝ} {x s : ℕ → E} {delta : ℕ → ℝ}
    (h : IsRun p true f x s delta) {B L c epsilon1 epsilon2 : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hB : 1 ≤ B)
    (hbound : ∀ y, ‖hessianOperator f y‖ ≤ B)
    (he1 : 0 < epsilon1) (he2 : 0 < epsilon2)
    (hinit : c * min epsilon1 epsilon2 ≤ delta 0)
    (hc1 : c ≤ p.gamma1 * ((1 - p.eta2) / (4 * B)))
    (hc2 : c ≤ p.gamma1 * (3 * (1 - p.eta2) / (L + 1)))
    (n : ℕ) (htest : ∀ j < n, ¬Stationary f epsilon1 epsilon2 (x j)) :
    c * min epsilon1 epsilon2 ≤ delta n := by
  have hm : 0 < min epsilon1 epsilon2 := lt_min he1 he2
  induction n with
  | zero => exact hinit
  | succ n ih =>
    have hi := ih (fun j hj => htest j (by omega))
    by_cases hs : p.eta2 ≤ TrustRegion.ratio f (gradient f (x n))
        (hessianOperator f (x n)) (x n) (s n)
    · have hu := h.toIsRun.update n
      rw [ite_eq_left hs] at hu
      exact hi.trans hu.1
    · have ht := htest n (by omega)
      by_contra hn
      have hu := h.toIsRun.radius_update_lower n (h.toIsRun.radius_pos n).le
      have ha : delta n < ((1 - p.eta2) / (4 * B)) * min epsilon1 epsilon2 := by
        have hh := mul_le_mul_of_nonneg_right hc1 hm.le
        by_contra hnsmall
        have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hnsmall) p.gamma1_pos.le
        have hh' := (lt_of_not_ge hn).trans_le hh
        rw [mul_assoc] at hh'
        exact (not_lt_of_ge (hmul.trans hu)) hh'
      have hb : delta n < (3 * (1 - p.eta2) / (L + 1)) * min epsilon1 epsilon2 := by
        have hh := mul_le_mul_of_nonneg_right hc2 hm.le
        by_contra hnsmall
        have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hnsmall) p.gamma1_pos.le
        have hh' := (lt_of_not_ge hn).trans_le hh
        rw [mul_assoc] at hh'
        exact (not_lt_of_ge (hmul.trans hu)) hh'
      exact hs (h.ratio_ge_of_joint_radius hf hB hbound he2 n ht ha hb)

/-- The common second-order decrease scale. -/
def accuracyScale (epsilon1 epsilon2 : ℝ) : ℝ :=
  epsilon2 * (min epsilon1 epsilon2) ^ 2

/-- The common scale is the minimum of the two familiar mixed powers. -/
theorem accuracyScale_eq {epsilon1 epsilon2 : ℝ} (he1 : 0 ≤ epsilon1)
    (he2 : 0 ≤ epsilon2) :
    accuracyScale epsilon1 epsilon2 = min (epsilon1 ^ 2 * epsilon2) (epsilon2 ^ 3) := by
  rcases le_total epsilon1 epsilon2 with h | h
  · rw [accuracyScale, min_eq_left h, min_eq_left]
    · ring
    · nlinarith [mul_le_mul_of_nonneg_right (show epsilon1 ^ 2 ≤ epsilon2 ^ 2 by nlinarith) he2]
  · rw [accuracyScale, min_eq_right h, min_eq_right]
    · ring
    · nlinarith [mul_le_mul_of_nonneg_right (show epsilon2 ^ 2 ≤ epsilon1 ^ 2 by nlinarith) he2]

/-- A uniform radius lower bound converts either failed stopping condition into the same
positive model decrease scale. The first tolerance need not be at most one. -/
theorem IsRun.predicted_decrease_before_joint_test
    {p : TrustRegion.Parameters} {f : E → ℝ} {x s : ℕ → E} {delta : ℕ → ℝ}
    (h : IsRun p true f x s delta) {B c epsilon1 epsilon2 : ℝ}
    (hB : 1 ≤ B)
    (hbound : ∀ y, ‖hessianOperator f y‖ ≤ B)
    (he1 : 0 < epsilon1) (he2 : 0 < epsilon2) (he2one : epsilon2 ≤ 1)
    (hc : 0 < c) (hcone : c ≤ 1) (k : ℕ)
    (hradius : c * min epsilon1 epsilon2 ≤ delta k)
    (htest : ¬Stationary f epsilon1 epsilon2 (x k)) :
    ((1 / 2 : ℝ) * min (1 / (1 + B)) (c ^ 2)) * accuracyScale epsilon1 epsilon2 ≤
      quadratic (gradient f (x k)) (hessianOperator f (x k)) 0 -
        quadratic (gradient f (x k)) (hessianOperator f (x k)) (s k) := by
  let m := min epsilon1 epsilon2
  let a := min (1 / (1 + B)) (c ^ 2)
  have hm : 0 < m := lt_min he1 he2
  have ha : 0 < a := lt_min (by positivity) (sq_pos_of_pos hc)
  have hac : a ≤ c := (min_le_right _ _).trans (by nlinarith : c ^ 2 ≤ c)
  rcases not_stationary_iff.mp htest with hg | hl
  · have hpred := h.toIsRun.predicted_decrease k
    have hfirst : a * m ≤ ‖gradient f (x k)‖ / (1 + ‖hessianOperator f (x k)‖) := by
      calc
        a * m ≤ (1 / (1 + B)) * ‖gradient f (x k)‖ :=
          mul_le_mul (min_le_left _ _)
            ((min_le_left epsilon1 epsilon2).trans hg.le) hm.le (by positivity)
        _ = ‖gradient f (x k)‖ / (1 + B) := by ring
        _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          (by linarith [hbound (x k)])
    have hsecond : a * m ≤ delta k :=
      (mul_le_mul_of_nonneg_right hac hm.le).trans hradius
    have hmin := le_min hfirst hsecond
    have hprod := mul_le_mul_of_nonneg_left hmin
      (by positivity : 0 ≤ (1 / 2 : ℝ) * ‖gradient f (x k)‖)
    have hgm : epsilon2 * m ≤ ‖gradient f (x k)‖ :=
      (mul_le_of_le_one_left hm.le he2one).trans ((min_le_left _ _).trans hg.le)
    have hlast := mul_le_mul_of_nonneg_right hgm (mul_nonneg ha.le hm.le)
    dsimp [accuracyScale]
    change (1 / 2 : ℝ) * a * (epsilon2 * m ^ 2) ≤ _
    nlinarith only [hpred, hprod, hlast]
  · have hneg : curvature f (x k) < 0 := hl.trans (neg_neg_of_pos he2)
    have hpred := h.curvature_decrease k hneg
    have he : epsilon2 ≤ |curvature f (x k)| := by rw [abs_of_neg hneg]; linarith
    have hsq : (c * m) ^ 2 ≤ delta k ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hc.le hm.le) hradius 2
    have h1 := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ |curvature f (x k)|)
    have h2 := mul_le_mul_of_nonneg_right he (sq_nonneg (c * m))
    have h3 := mul_le_mul_of_nonneg_right (min_le_right (1 / (1 + B)) (c ^ 2))
      (mul_nonneg he2.le (sq_nonneg m))
    dsimp [accuracyScale]
    change (1 / 2 : ℝ) * a * (epsilon2 * m ^ 2) ≤ _
    dsimp [a] at *
    nlinarith only [hpred, h1, h2, h3]

/-- A tolerance-independent coefficient compatible with both success thresholds and
initialization. The cap one half ensures the elementary mixed-power comparison. -/
def jointRadiusCoefficient (p : TrustRegion.Parameters) (B L delta0 : ℝ) : ℝ :=
  min (1 / 2 : ℝ) (min delta0 (min
    (p.gamma1 * ((1 - p.eta2) / (4 * B)))
    (p.gamma1 * (3 * (1 - p.eta2) / (L + 1)))))

/-- The joint radius coefficient is positive and satisfies all four required upper bounds. -/
theorem jointRadiusCoefficient_spec (p : TrustRegion.Parameters) {B L delta0 : ℝ}
    (hB : 1 ≤ B) (hL : 0 ≤ L) (hd : 0 < delta0) :
    0 < jointRadiusCoefficient p B L delta0 ∧
    jointRadiusCoefficient p B L delta0 ≤ 1 ∧
    jointRadiusCoefficient p B L delta0 ≤ delta0 ∧
    jointRadiusCoefficient p B L delta0 ≤ p.gamma1 * ((1 - p.eta2) / (4 * B)) ∧
    jointRadiusCoefficient p B L delta0 ≤ p.gamma1 * (3 * (1 - p.eta2) / (L + 1)) := by
  have ha : 0 < p.gamma1 * ((1 - p.eta2) / (4 * B)) := by
    exact mul_pos p.gamma1_pos (div_pos (sub_pos.mpr p.eta2_lt_one) (by positivity))
  have hb : 0 < p.gamma1 * (3 * (1 - p.eta2) / (L + 1)) := by
    exact mul_pos p.gamma1_pos
      (div_pos (mul_pos (by norm_num) (sub_pos.mpr p.eta2_lt_one)) (by positivity))
  unfold jointRadiusCoefficient
  refine ⟨lt_min (by norm_num) (lt_min hd (lt_min ha hb)), ?_, ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans (by norm_num)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)

/-- Successful trials before the first joint test consume a fixed amount of objective gap. -/
theorem IsRun.joint_success_count_le
    {p : TrustRegion.Parameters} {f : E → ℝ} {x s : ℕ → E} {delta : ℕ → ℝ}
    (h : IsRun p true f x s delta) {B L low epsilon1 epsilon2 : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hB : 1 ≤ B)
    (hbound : ∀ y, ‖hessianOperator f y‖ ≤ B)
    (he1 : 0 < epsilon1) (he2 : 0 < epsilon2) (he2one : epsilon2 ≤ 1)
    (n : ℕ) (hlow : low ≤ f (x n))
    (htest : ∀ j < n, ¬Stationary f epsilon1 epsilon2 (x j)) :
    (ParameterUpdates.successCount
      (fun k => p.eta1 ≤ TrustRegion.ratio f (gradient f (x k))
        (hessianOperator f (x k)) (x k) (s k)) n : ℝ) ≤
      (f (x 0) - low) / (p.eta1 * ((1 / 2 : ℝ) *
        min (1 / (1 + B)) ((jointRadiusCoefficient p B L (delta 0)) ^ 2)) *
          accuracyScale epsilon1 epsilon2) := by
  classical
  let c := jointRadiusCoefficient p B L (delta 0)
  obtain ⟨hc, hc1, hcd, hca, hcb⟩ :=
    jointRadiusCoefficient_spec p hB hf.nonneg (h.toIsRun.radius_pos 0)
  have hm : 0 < min epsilon1 epsilon2 := lt_min he1 he2
  have hD : 0 < (1 / 2 : ℝ) * min (1 / (1 + B)) (c ^ 2) :=
    mul_pos (by norm_num) (lt_min (by positivity) (sq_pos_of_pos hc))
  have hscale : 0 < accuracyScale epsilon1 epsilon2 :=
    mul_pos he2 (sq_pos_of_pos hm)
  have hden : 0 < p.eta1 * ((1 / 2 : ℝ) * min (1 / (1 + B)) (c ^ 2)) *
      accuracyScale epsilon1 epsilon2 := mul_pos (mul_pos p.eta1_pos hD) hscale
  apply (le_div_iff₀ hden).mpr
  unfold ParameterUpdates.successCount
  apply EvaluationComplexity.card_mul_le_gap (u := fun k => f (x k))
    (Finset.filter_subset _ _) hlow (fun k _ => h.toIsRun.objective_nonincrease k)
  intro k hk
  obtain ⟨hkn, hks⟩ := Finset.mem_filter.mp hk
  have hkn' := Finset.mem_range.mp hkn
  have hinit : c * min epsilon1 epsilon2 ≤ delta 0 :=
    (mul_le_of_le_one_right hc.le ((min_le_right _ _).trans he2one)).trans hcd
  have hr := h.radius_lower_before_joint_test hf hB hbound he1 he2 hinit hca hcb k
    (fun j hj => htest j (by omega))
  have hp := h.predicted_decrease_before_joint_test hB hbound he1 he2 he2one
    hc hc1 k hr (htest k hkn')
  have hh := mul_le_mul_of_nonneg_left hp p.eta1_pos.le
  have ha := h.toIsRun.accepted_decrease k hks
  nlinarith only [hh, ha]

/-- The total number of trials in an unterminated joint-test prefix is bounded using the
same multiplicative radius counting argument as the first-order trust-region method. -/
theorem IsRun.joint_prefix_count_le
    {p : TrustRegion.Parameters} {f : E → ℝ} {x s : ℕ → E} {delta : ℕ → ℝ}
    (h : IsRun p true f x s delta) {B L low epsilon1 epsilon2 : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hB : 1 ≤ B)
    (hbound : ∀ y, ‖hessianOperator f y‖ ≤ B)
    (he1 : 0 < epsilon1) (he2 : 0 < epsilon2) (he2one : epsilon2 ≤ 1)
    (n : ℕ) (hlow : low ≤ f (x n))
    (htest : ∀ j < n, ¬Stationary f epsilon1 epsilon2 (x j)) :
    (n : ℝ) ≤ (f (x 0) - low) / (p.eta1 * ((1 / 2 : ℝ) *
        min (1 / (1 + B)) ((jointRadiusCoefficient p B L (delta 0)) ^ 2)) *
          accuracyScale epsilon1 epsilon2) *
        (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
      (|Real.log (jointRadiusCoefficient p B L (delta 0) / delta 0)| +
        |Real.log (min epsilon1 epsilon2)|) / |Real.log p.gamma2| := by
  let c := jointRadiusCoefficient p B L (delta 0)
  obtain ⟨hc, _, hcd, hca, hcb⟩ :=
    jointRadiusCoefficient_spec p hB hf.nonneg (h.toIsRun.radius_pos 0)
  have hm : 0 < min epsilon1 epsilon2 := lt_min he1 he2
  have hZ : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  have hC : 0 ≤ 1 + Real.log p.gamma3 / |Real.log p.gamma2| :=
    add_nonneg zero_le_one (div_nonneg (Real.log_pos p.one_lt_gamma3).le hZ.le)
  have hinit : c * min epsilon1 epsilon2 ≤ delta 0 :=
    (mul_le_of_le_one_right hc.le ((min_le_right _ _).trans he2one)).trans hcd
  have hr := h.radius_lower_before_joint_test hf hB hbound he1 he2 hinit hca hcb n htest
  have ht := h.toIsRun.total_count_le n (mul_pos hc hm) hr
  have hs := h.joint_success_count_le hf hB hbound he1 he2 he2one n hlow htest
  have hlogeq : Real.log (delta 0 / (c * min epsilon1 epsilon2)) =
      -(Real.log (c / delta 0) + Real.log (min epsilon1 epsilon2)) := by
    rw [Real.log_div (h.toIsRun.radius_pos 0).ne' (mul_pos hc hm).ne',
      Real.log_mul hc.ne' hm.ne', Real.log_div hc.ne' (h.toIsRun.radius_pos 0).ne']
    ring
  have hlogbound : Real.log (delta 0 / (c * min epsilon1 epsilon2)) ≤
      |Real.log (c / delta 0)| + |Real.log (min epsilon1 epsilon2)| := by
    rw [hlogeq]
    linarith only [neg_le_abs (Real.log (c / delta 0)),
      neg_le_abs (Real.log (min epsilon1 epsilon2))]
  have h1 := mul_le_mul_of_nonneg_right hs hC
  have h2 := div_le_div_of_nonneg_right hlogbound hZ.le
  linarith only [ht, h1, h2]

/-- Tolerance-independent positive constants bound the first joint stationary iterate and its
objective, gradient and Hessian oracle costs. Both derivative oracles are cached on rejection. -/
theorem IsRun.exists_joint_complexity_constants
    {p : TrustRegion.Parameters} {f : E → ℝ} {x s : ℕ → E} {delta : ℕ → ℝ}
    (h : IsRun p true f x s delta) {B L low : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hB : 1 ≤ B)
    (hbound : ∀ y, ‖hessianOperator f y‖ ≤ B) (hlow : ∀ y, low ≤ f y) :
    ∃ kT kD kE kF : ℝ, 0 < kT ∧ 0 < kD ∧ 0 < kE ∧ 0 < kF ∧
      ∀ epsilon1 epsilon2 : ℝ, 0 < epsilon1 → 0 < epsilon2 → epsilon2 ≤ 1 →
      ∃ K : ℕ, Stationary f epsilon1 epsilon2 (x K) ∧
        (∀ j < K, ¬Stationary f epsilon1 epsilon2 (x j)) ∧
        (K : ℝ) + 1 ≤ kD * ((f (x 0) - low) / accuracyScale epsilon1 epsilon2) +
          kE * |Real.log (min epsilon1 epsilon2)| + kF ∧
        (ParameterUpdates.successCount
          (fun k => p.eta1 ≤ TrustRegion.ratio f (gradient f (x k))
            (hessianOperator f (x k)) (x k) (s k)) K : ℝ) + 1 ≤
          kT * ((f (x 0) - low) / accuracyScale epsilon1 epsilon2) + 1 := by
  classical
  let c := jointRadiusCoefficient p B L (delta 0)
  have hc := (jointRadiusCoefficient_spec p hB hf.nonneg (h.toIsRun.radius_pos 0)).1
  let D := (1 / 2 : ℝ) * min (1 / (1 + B)) (c ^ 2)
  have hD : 0 < D := mul_pos (by norm_num) (lt_min (by positivity) (sq_pos_of_pos hc))
  have hZ : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  let C := 1 + Real.log p.gamma3 / |Real.log p.gamma2|
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (Real.log_pos p.one_lt_gamma3).le hZ.le)
  have hkT : 0 < 1 / (p.eta1 * D) := div_pos zero_lt_one (mul_pos p.eta1_pos hD)
  refine ⟨1 / (p.eta1 * D), 1 / (p.eta1 * D) * C, 1 / |Real.log p.gamma2|,
    |Real.log (c / delta 0)| / |Real.log p.gamma2| + 1,
    hkT, mul_pos hkT hC, div_pos zero_lt_one hZ,
    add_pos_of_nonneg_of_pos (div_nonneg (abs_nonneg _) hZ.le) zero_lt_one, ?_⟩
  intro epsilon1 epsilon2 he1 he2 he2one
  obtain ⟨K, _, hk, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound
    (P := fun k => Stationary f epsilon1 epsilon2 (x k))
    (fun n hn => h.joint_prefix_count_le hf hB hbound he1 he2 he2one n (hlow _) hn)
  have hfun := h.joint_prefix_count_le hf hB hbound he1 he2 he2one K (hlow _) hfirst
  have hderiv := h.joint_success_count_le hf hB hbound he1 he2 he2one K (hlow _) hfirst
  have hbudget : (f (x 0) - low) / (p.eta1 * D * accuracyScale epsilon1 epsilon2) =
      (1 / (p.eta1 * D)) * ((f (x 0) - low) / accuracyScale epsilon1 epsilon2) := by ring
  change (K : ℝ) ≤ (f (x 0) - low) / (p.eta1 * D * accuracyScale epsilon1 epsilon2) * C +
    (|Real.log (c / delta 0)| + |Real.log (min epsilon1 epsilon2)|) / |Real.log p.gamma2| at hfun
  change _ ≤ (f (x 0) - low) / (p.eta1 * D * accuracyScale epsilon1 epsilon2) at hderiv
  rw [hbudget] at hfun hderiv
  refine ⟨K, hk, hfirst, ?_, by linarith only [hderiv]⟩
  calc
    (K : ℝ) + 1 ≤ (1 / (p.eta1 * D)) * ((f (x 0) - low) / accuracyScale epsilon1 epsilon2) * C +
        (|Real.log (c / delta 0)| + |Real.log (min epsilon1 epsilon2)|) / |Real.log p.gamma2| + 1 :=
      by linarith only [hfun]
    _ = _ := by ring

/-- The eigenpoint uses a signed normalized least-eigenvalue direction at negative curvature
and is zero at nonnegative curvature. -/
def eigenpoint [FiniteDimensional ℝ E] [Nontrivial E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (delta : ℝ) : E :=
  if curvature f x < 0 then delta • Classical.choose (exists_signed_eigenvector hf) else 0

/-- At negative curvature the eigenpoint is a feasible exact minimizer on a signed normalized
minimum-eigenvector ray. -/
theorem eigenpoint_spec [FiniteDimensional ℝ E] [Nontrivial E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) {delta : ℝ} (hd : 0 ≤ delta) (hl : curvature f x < 0) :
    ∃ u : E, ‖u‖ = 1 ∧ hessianOperator f x u = curvature f x • u ∧
      inner ℝ (gradient f x) u ≤ 0 ∧ eigenpoint hf delta = delta • u ∧
      ‖eigenpoint hf delta‖ ≤ delta ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ delta →
        quadratic (gradient f x) (hessianOperator f x) (eigenpoint hf delta) ≤
          quadratic (gradient f x) (hessianOperator f x) (t • u) := by
  obtain ⟨hu, he, hg⟩ := Classical.choose_spec (exists_signed_eigenvector hf)
  let u := Classical.choose (exists_signed_eigenvector hf)
  have hp : eigenpoint hf delta = delta • u := by simp only [eigenpoint, ite_eq_left hl]; rfl
  have hB : fderiv ℝ (fderiv ℝ f) x u u = curvature f x := by
    rw [← continuousLinearMapOfBilin_apply _ u u]
    change inner ℝ (hessianOperator f x u) u = _
    rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
    ring
  refine ⟨u, hu, he, hg, hp, ?_, ?_⟩
  · rw [hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd, hu, mul_one]
  · intro t ht htd
    rw [hp]
    exact quadratic_boundary_le hg hB hl ht htd

end Optimization.TrustRegionSecondOrder
