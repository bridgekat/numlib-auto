import Numlib.Optimization.Constrained.TwoPhase.Target
import Numlib.Optimization.HighOrder.ConstrainedCriticality
import Numlib.Analysis.Calculus.TaylorModel.Perturbation

/-!
# Actual Taylor changes under target updates

Changing the target changes every positive derivative tensor of the true
least-squares merit by the target difference times the objective tensor.
Consequently every finite Taylor decrement and its actual constrained
criticality have an explicit target-perturbation bound.
-/

noncomputable section
namespace Constrained
open scoped BigOperators
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The exact difference of two true merits is affine in the objective. -/
theorem targetMerit_sub (f : E → ℝ) (c : E → F) (t u : ℝ) :
    targetMerit f c t - targetMerit f c u =
      (u - t) • f + fun _ => (t ^ 2 - u ^ 2) / 2 := by
  funext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, targetMerit]
  ring

variable [InnerProductSpace ℝ F]

/-- Finite pointwise smoothness of the objective and constraints gives the
same finite pointwise smoothness of the genuine target merit. -/
theorem contDiffAt_targetMerit {f : E → ℝ} {c : E → F} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x) (t : ℝ) :
    ContDiffAt ℝ p (targetMerit f c t) x := by
  have hshift : ContDiffAt ℝ p (fun z => f z - t) x := hf.sub contDiffAt_const
  have hh := ((hc.norm_sq (𝕜 := ℝ)).const_smul (1 / 2 : ℝ)).add
    ((hshift.pow 2).const_smul (1 / 2 : ℝ))
  convert hh using 1
  funext z
  simp only [targetMerit, smul_eq_mul]
  ring

/-- The actual positive-order merit tensors change by the target difference
multiplying the actual objective tensor. No derivative identity is assumed. -/
theorem iteratedFDeriv_targetMerit_sub {f : E → ℝ} {c : E → F} {p j : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    (hj : 1 ≤ j) (hjp : j ≤ p) (t u : ℝ) :
    iteratedFDeriv ℝ j (targetMerit f c t) x -
      iteratedFDeriv ℝ j (targetMerit f c u) x =
        (u - t) • iteratedFDeriv ℝ j f x := by
  have hfj : ContDiffAt ℝ j f x := hf.of_le (by exact_mod_cast hjp)
  have hcj : ContDiffAt ℝ j c x := hc.of_le (by exact_mod_cast hjp)
  rw [←iteratedFDeriv_sub_apply (contDiffAt_targetMerit hfj hcj t)
    (contDiffAt_targetMerit hfj hcj u), targetMerit_sub]
  change iteratedFDeriv ℝ j ((fun z => (u - t) • f z) +
    fun _ => (t ^ 2 - u ^ 2) / 2) x = _
  rw [iteratedFDeriv_add_apply (hfj.const_smul (u - t))
    (show ContDiffAt ℝ j (fun _ : E => (t ^ 2 - u ^ 2) / 2) x from contDiffAt_const),
    iteratedFDeriv_const_smul_apply' hfj,
    iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
  simp only [Pi.zero_apply, add_zero]

/-- The true finite Taylor decrement changes by the target difference times
its actual objective decrement; the constant merit difference cancels. -/
theorem decrement_targetMerit_sub {f : E → ℝ} {c : E → F} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    (t u : ℝ) (d : E) :
    TaylorModel.decrement (targetMerit f c t) p x d -
      TaylorModel.decrement (targetMerit f c u) p x d =
        (u - t) * TaylorModel.decrement f p x d := by
  change TaylorModel.jetDecrement (ftaylorSeries ℝ (targetMerit f c t) x) p d -
    TaylorModel.jetDecrement (ftaylorSeries ℝ (targetMerit f c u) x) p d =
      (u - t) * TaylorModel.jetDecrement (ftaylorSeries ℝ f x) p d
  rw [←TaylorModel.jetDecrement_sub]
  simp only [TaylorModel.jetDecrement_eq_sum, FormalMultilinearSeries.sub_apply,
    ftaylorSeries, sub_apply]
  have he (i : ℕ) (hi : i ∈ Finset.range p) :
      iteratedFDeriv ℝ (i + 1) (targetMerit f c t) x -
        iteratedFDeriv ℝ (i + 1) (targetMerit f c u) x =
          (u - t) • iteratedFDeriv ℝ (i + 1) f x :=
    iteratedFDeriv_targetMerit_sub hf hc (by omega) (by simpa using hi) t u
  have hsum : (∑ i ∈ Finset.range p,
      (((i + 1).factorial : ℝ)⁻¹) •
        ((iteratedFDeriv ℝ (i + 1) (targetMerit f c t) x -
          iteratedFDeriv ℝ (i + 1) (targetMerit f c u) x) (fun _ => d))) =
      (u - t) * ∑ i ∈ Finset.range p,
        (((i + 1).factorial : ℝ)⁻¹) •
          iteratedFDeriv ℝ (i + 1) f x (fun _ => d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi]
    simp only [smul_apply, smul_eq_mul]
    ring
  simp only [sub_apply] at hsum
  rw [hsum]
  ring

/-- The true positive-order objective tensor bound for its Taylor decrement
on a displacement ball. This quantity contains no merit or criticality bound. -/
def targetTaylorBound (f : E → ℝ) (p : ℕ) (x : E) (δ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range p,
    ‖iteratedFDeriv ℝ (i + 1) f x‖ * δ ^ (i + 1) / (i + 1).factorial

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
/-- The finite objective tensor bound is nonnegative on nonnegative balls. -/
theorem targetTaylorBound_nonneg (f : E → ℝ) (p : ℕ) (x : E) {δ : ℝ}
    (hδ : 0 ≤ δ) : 0 ≤ targetTaylorBound f p x δ := by
  unfold targetTaylorBound
  exact Finset.sum_nonneg (fun _ _ => by positivity)

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
/-- Every actual objective Taylor decrement on the ball is bounded by its
finite sum of genuine positive-order tensor norms. -/
theorem abs_decrement_le_targetTaylorBound (f : E → ℝ) (p : ℕ) (x : E)
    {δ : ℝ} {d : E} (hd : ‖d‖ ≤ δ) :
    |TaylorModel.decrement f p x d| ≤ targetTaylorBound f p x δ := by
  have hb := TaylorModel.norm_jetDecrement_le (ftaylorSeries ℝ f x) p d
  change ‖TaylorModel.decrement f p x d‖ ≤ _ at hb
  rw [Real.norm_eq_abs] at hb
  apply hb.trans
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg d) hd (i + 1))
      (norm_nonneg _)) (Nat.cast_nonneg _)

/-- Actual Taylor-decrement perturbations are bounded on the displacement
ball by the target change and the original objective tensor norms. -/
theorem abs_decrement_targetMerit_sub_le {f : E → ℝ} {c : E → F}
    {p : ℕ} {x : E} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    (t u : ℝ) {δ : ℝ} {d : E} (hd : ‖d‖ ≤ δ) :
    |TaylorModel.decrement (targetMerit f c t) p x d -
      TaylorModel.decrement (targetMerit f c u) p x d| ≤
        |u - t| * targetTaylorBound f p x δ := by
  rw [decrement_targetMerit_sub hf hc t u, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_decrement_le_targetTaylorBound f p x hd)
    (abs_nonneg _)

variable [ProperSpace E]

/-- Compact attainment transfers the actual target perturbation bound to
constrained criticality on any closed feasible set. -/
theorem constrainedCriticality_targetMerit_le {f : E → ℝ} {c : E → F}
    {p : ℕ} {x : E} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    (t u : ℝ) {X : Set E} (hX : IsClosed X) (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    TaylorModel.constrainedCriticality (targetMerit f c t) p X x δ ≤
      TaylorModel.constrainedCriticality (targetMerit f c u) p X x δ +
        |u - t| * targetTaylorBound f p x δ := by
  obtain ⟨d, hfeas, hd, he⟩ := TaylorModel.exists_decrement_eq_constrainedCriticality
    (targetMerit f c t) p hX hx hδ
  have hb := abs_decrement_targetMerit_sub_le hf hc t u hd
  have hu := TaylorModel.decrement_le_constrainedCriticality
    (targetMerit f c u) p hX hfeas hd
  rw [←he]
  linarith [(abs_le.mp hb).2]

/-- Changing the target changes the genuine constrained criticality by at
most its actual Taylor-decrement perturbation. -/
theorem abs_constrainedCriticality_targetMerit_sub_le {f : E → ℝ} {c : E → F}
    {p : ℕ} {x : E} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    (t u : ℝ) {X : Set E} (hX : IsClosed X) (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    |TaylorModel.constrainedCriticality (targetMerit f c t) p X x δ -
      TaylorModel.constrainedCriticality (targetMerit f c u) p X x δ| ≤
        |u - t| * targetTaylorBound f p x δ := by
  have htu := constrainedCriticality_targetMerit_le hf hc t u hX hx hδ
  have hut := constrainedCriticality_targetMerit_le hf hc u t hX hx hδ
  rw [abs_sub_comm t u] at hut
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Literal target reflection perturbs constrained criticality by at most
twice the actual objective-target gap times the objective Taylor bound. -/
theorem abs_constrainedCriticality_reflect_sub_le {f : E → ℝ} {c : E → F}
    {p : ℕ} {x : E} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    (t : ℝ) {X : Set E} (hX : IsClosed X) (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    |TaylorModel.constrainedCriticality
        (targetMerit f c (TwoPhase.reflectTarget f t x)) p X x δ -
      TaylorModel.constrainedCriticality (targetMerit f c t) p X x δ| ≤
        2 * |f x - t| * targetTaylorBound f p x δ := by
  have hb := abs_constrainedCriticality_targetMerit_sub_le hf hc
    (TwoPhase.reflectTarget f t x) t hX hx hδ
  have he : |t - TwoPhase.reflectTarget f t x| = 2 * |f x - t| := by
    unfold TwoPhase.reflectTarget
    rw [show t - (2 * f x - t) = -2 * (f x - t) by ring, abs_mul]
    norm_num
  simpa only [he] using hb

/-- If an old-target certificate passes but its reflected-target test fails,
the actual target gap must account for their strict criticality separation. -/
theorem reflection_gap_bound_of_criticality_failure {f : E → ℝ} {c : E → F}
    {p : ℕ} {x : E} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    {t β tol : ℝ} {X : Set E} (hX : IsClosed X) (hx : x ∈ X)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hold : TaylorModel.constrainedCriticality (targetMerit f c t) p X x δ ≤ β * tol)
    (hnew : tol < TaylorModel.constrainedCriticality
      (targetMerit f c (TwoPhase.reflectTarget f t x)) p X x δ) :
    (1 - β) * tol < 2 * |f x - t| * targetTaylorBound f p x δ := by
  have hb := (abs_le.mp (abs_constrainedCriticality_reflect_sub_le
    hf hc t hX hx hδ)).2
  nlinarith

end Constrained
