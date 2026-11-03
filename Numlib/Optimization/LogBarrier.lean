import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Boundary behavior of the logarithmic barrier -/

open Filter Metric
open scoped BigOperators Topology ContDiff

namespace Optimization

variable {ι : Type*} [Fintype ι]

/-- The log barrier on the strictly positive orthant. -/
noncomputable def logBarrier (μ : ℝ) (x : ι → ℝ) : ℝ :=
  -μ * ∑ i, Real.log (x i)

/-- The closed nonnegative orthant. -/
def nonnegativeOrthant (ι : Type*) : Set (ι → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ici 0

omit [Fintype ι] in
/-- The boundary of the nonnegative orthant has a zero coordinate. -/
theorem mem_frontier_nonnegativeOrthant [Finite ι] {x : ι → ℝ} :
    x ∈ frontier (nonnegativeOrthant ι) ↔ (∀ i, 0 ≤ x i) ∧ ∃ i, x i = 0 := by
  classical
  have hclosed : IsClosed (nonnegativeOrthant ι) :=
    isClosed_set_pi fun _ _ ↦ isClosed_Ici
  rw [frontier, hclosed.closure_eq]
  unfold nonnegativeOrthant
  rw [interior_pi_set Set.finite_univ]
  simp only [Set.mem_sdiff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici,
    interior_Ici, Set.mem_Ioi]
  constructor
  · rintro ⟨hn, hp⟩
    push Not at hp
    obtain ⟨i, hi⟩ := hp
    exact ⟨hn, i, le_antisymm hi (hn i)⟩
  · rintro ⟨hn, i, hi⟩
    exact ⟨hn, fun h ↦ (h i).ne' hi⟩

private theorem exists_coordinate_le_boundary_distance [Nonempty ι] {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) :
    ∃ i, x i ≤ infDist x (frontier (nonnegativeOrthant ι)) := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  have hfront : (frontier (nonnegativeOrthant ι)).Nonempty := by
    exact ⟨0, mem_frontier_nonnegativeOrthant.mpr ⟨fun _ ↦ le_rfl, i, rfl⟩⟩
  refine ⟨i, (le_infDist hfront).mpr fun y hy ↦ ?_⟩
  obtain ⟨-, j, hj⟩ := mem_frontier_nonnegativeOrthant.mp hy
  calc
    x i ≤ x j := hi j (Finset.mem_univ j)
    _ = dist (x j) (y j) := by rw [hj, Real.dist_eq, sub_zero, abs_of_pos (hx j)]
    _ ≤ dist x y := (dist_pi_le_iff dist_nonneg).mp le_rfl j

/-- The logarithmic barrier diverges along a uniformly bounded positive path whose
distance to the orthant boundary tends to zero. -/
theorem tendsto_logBarrier_of_bounded_of_infDist_frontier [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) {x : ℕ → ι → ℝ}
    (hx : ∀ n i, 0 < x n i) (hbounded : ∀ n i, x n i ≤ M)
    (ht : Tendsto (fun n ↦ infDist (x n) (frontier (nonnegativeOrthant ι))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ logBarrier μ (x n)) atTop atTop := by
  classical
  let d (n : ℕ) := infDist (x n) (frontier (nonnegativeOrthant ι))
  let B := (Fintype.card ι : ℝ) * max 0 (Real.log M)
  have hd (n : ℕ) : 0 < d n := by
    obtain ⟨i, hi⟩ := exists_coordinate_le_boundary_distance (hx n)
    exact (hx n i).trans_le hi
  have hlog : Tendsto (fun n ↦ Real.log (d n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp <| tendsto_nhdsWithin_iff.mpr
      ⟨ht, Eventually.of_forall hd⟩
  have hsum (n : ℕ) : (∑ i, Real.log (x n i)) ≤ Real.log (d n) + B := by
    obtain ⟨i, hi⟩ := exists_coordinate_le_boundary_distance (hx n)
    have hothers : (∑ j ∈ Finset.univ.erase i, Real.log (x n j)) ≤ B := by
      calc
        _ ≤ ∑ _ ∈ Finset.univ.erase i, max 0 (Real.log M) :=
          Finset.sum_le_sum fun j _ ↦
            (Real.log_le_log (hx n j) (hbounded n j)).trans (le_max_right _ _)
        _ ≤ B := by
          simp only [Finset.sum_const, nsmul_eq_mul, B]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _)
            (le_max_left _ _)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact add_le_add hothers (Real.log_le_log (hx n i) hi) |>.trans_eq (add_comm _ _)
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_atBot.mp hlog (-b / μ - B)] with n hn
  have hs : (∑ i, Real.log (x n i)) ≤ -b / μ := by linarith [hsum n]
  have hs' := (le_div_iff₀ hμ).mp hs
  unfold logBarrier
  nlinarith only [hs']

private def coordinate (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

private noncomputable def logBarrierFDeriv (μ : ℝ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  (-μ) • ∑ i, (x i)⁻¹ • coordinate i

/-- The log barrier is smooth at every strictly positive vector. -/
theorem contDiffAt_logBarrier (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) {n : ℕ∞ω} :
    ContDiffAt ℝ n (logBarrier μ) x := by
  have hi (i : ι) : ContDiffAt ℝ n (fun y : ι → ℝ ↦ Real.log (y i)) x :=
    (coordinate i).contDiff.contDiffAt.log (hx i).ne'
  exact (ContDiffAt.sum fun i (_ : i ∈ Finset.univ) ↦ hi i).const_smul (-μ)

private theorem hasFDerivAt_logBarrier (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    HasFDerivAt (logBarrier μ) (logBarrierFDeriv μ x) x := by
  have hi (i : ι) : HasFDerivAt (fun y : ι → ℝ ↦ Real.log (y i))
      ((x i)⁻¹ • coordinate i) x :=
    let h : HasDerivAt Real.log (x i)⁻¹ (coordinate i x) :=
      Real.hasDerivAt_log (hx i).ne'
    h.comp_hasFDerivAt x (coordinate i).hasFDerivAt
  exact (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) ↦ hi i).const_smul (-μ)

/-- The directional derivative of the logarithmic barrier. -/
theorem fderiv_logBarrier_apply (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) (d : ι → ℝ) :
    fderiv ℝ (logBarrier μ) x d = -μ * ∑ i, (x i)⁻¹ * d i := by
  rw [(hasFDerivAt_logBarrier μ hx).fderiv]
  simp [logBarrierFDeriv, coordinate]

/-- The log-barrier Hessian is diagonal, with entries `μ / xᵢ²`. -/
theorem fderiv_fderiv_logBarrier_apply (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (d e : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (logBarrier μ)) x d e =
      μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * e i := by
  have hU : Set.univ.pi (fun _ : ι ↦ Set.Ioi (0 : ℝ)) ∈ 𝓝 x :=
    (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi).mem_nhds (by simpa using hx)
  have hEq : fderiv ℝ (logBarrier μ) =ᶠ[𝓝 x] logBarrierFDeriv μ := by
    filter_upwards [hU] with y hy
    exact (hasFDerivAt_logBarrier μ (by simpa using hy)).fderiv
  have hi (i : ι) : HasFDerivAt (fun y : ι → ℝ ↦ (y i)⁻¹)
      (-((x i) ^ 2)⁻¹ • coordinate i) x :=
    (hasDerivAt_inv (hx i).ne').comp_hasFDerivAt x (coordinate i).hasFDerivAt
  have hD := (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) ↦
    (hi i).smul_const (coordinate i)).const_smul (-μ)
  rw [hEq.fderiv_eq]
  change fderiv ℝ ((-μ) • fun y : ι → ℝ ↦
    ∑ i, (y i)⁻¹ • coordinate i) x d e = _
  rw [hD.fderiv]
  simp [coordinate, Finset.sum_neg_distrib, mul_assoc]

/-- Each coordinate of a positive vector bounds its distance to the orthant boundary. -/
theorem infDist_frontier_le_coordinate {x : ι → ℝ} (hx : ∀ i, 0 < x i) (i : ι) :
    infDist x (frontier (nonnegativeOrthant ι)) ≤ x i := by
  classical
  let y := Function.update x i 0
  have hy : y ∈ frontier (nonnegativeOrthant ι) := by
    apply mem_frontier_nonnegativeOrthant.mpr
    refine ⟨fun j ↦ ?_, i, Function.update_self i 0 x⟩
    by_cases hj : j = i
    · subst j
      rw [show y i = 0 from Function.update_self i 0 x]
    · rw [show y j = x j from Function.update_of_ne hj 0 x]
      exact (hx j).le
  refine (infDist_le_dist_of_mem hy).trans ((dist_pi_le_iff (hx i).le).mpr fun j ↦ ?_)
  by_cases hj : j = i
  · subst j
    rw [show y i = 0 from Function.update_self i 0 x, Real.dist_eq, sub_zero, abs_of_pos (hx i)]
  · rw [show y j = x j from Function.update_of_ne hj 0 x, dist_self]
    exact (hx i).le

/-- A coordinate lower bound gives a uniform operator-norm bound on the Hessian. -/
theorem norm_fderiv_fderiv_logBarrier_le (μ : ℝ) {x : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hx : ∀ i, ε ≤ x i) :
    ‖fderiv ℝ (fderiv ℝ (logBarrier μ)) x‖ ≤ |μ| * Fintype.card ι * (ε ^ 2)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro e
  rw [fderiv_fderiv_logBarrier_apply μ (fun i ↦ hε.trans_le (hx i)), Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |μ| * ∑ i, |((x i) ^ 2)⁻¹ * d i * e i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |μ| * ∑ _ : ι, (ε ^ 2)⁻¹ * ‖d‖ * ‖e‖ := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      have hi : ((x i) ^ 2)⁻¹ ≤ (ε ^ 2)⁻¹ :=
        (inv_le_inv₀ (pow_pos (hε.trans_le (hx i)) 2) (pow_pos hε 2)).mpr
          (pow_le_pow_left₀ hε.le (hx i) 2)
      simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (x i))), ← Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul hi (norm_le_pi_norm d i) (norm_nonneg _) (by positivity))
        (norm_le_pi_norm e i) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Optimization
