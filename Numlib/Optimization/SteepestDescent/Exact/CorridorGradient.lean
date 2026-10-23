import Numlib.Optimization.SteepestDescent.Exact.CorridorEuclidean
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The genuine source corridor gradient at the finite grid nodes

The source central quadratic identifies the vertical derivative even at the
closed corridor wall. Uniqueness of the one-sided derivative at each wall,
together with global twice differentiability, supplies the genuine derivative.
-/

open Set
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- The actual vertical profile derivative is the quadratic derivative at every
central point, including both closed corridor walls. -/
theorem fderiv_profile_vertical {δ z : ℝ} (hδ : 0 < δ)
    (hz : z ∈ Icc (-δ / 2) (δ / 2)) :
    fderiv ℝ (fun w : ℝ × ℝ => profile w.1 w.2) (δ,z) (0,1) = 2*z := by
  have hp : HasDerivAt (fun u : ℝ => u^2) (2*z) z := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using (hasDerivAt_pow 2 z)
  have hs : HasDerivWithinAt (fun u => profile δ u) (2*z) (Icc (-δ / 2) (δ / 2)) z :=
    hp.hasDerivWithinAt.congr (fun u hu => profile_central hu) (profile_central hz)
  have hu : UniqueDiffWithinAt ℝ (Icc (-δ / 2) (δ / 2)) z :=
    uniqueDiffOn_Icc (by linarith) z hz
  have hf := (contDiff_profile.differentiable (by norm_num) (δ,z)).hasFDerivAt
  have hv := (hasDerivAt_const z δ).prodMk (hasDerivAt_id z)
  have hh := hf.comp_hasDerivAt z hv
  exact (hh.hasDerivWithinAt.derivWithin hu).symm.trans (hs.derivWithin hu)

/-- The genuine curve has the prescribed first derivative at every source node. -/
theorem curve_hasDerivAt_node (P : Parameters) (i : Fin 3) {k : ℕ}
    (hk : k ≤ P.horizon) :
    HasDerivAt (curve P i) (curveJet P i k 1) (horizontal P k) := by
  apply ((curve_spec P i).1.differentiable (by norm_num) _).hasDerivAt.congr_deriv
  simpa only [iteratedDeriv_one] using (curve_spec P i).2.1 k hk 1 (by omega)

/-- The actual scalar objective preserves the prescribed slope at all source nodes. -/
theorem scalarObjective_hasDerivAt_node (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    HasDerivAt (scalarObjective P) (-amplitude P k) (horizontal P k) := by
  apply ((contDiff_scalarObjective P).differentiable (by norm_num) _).hasDerivAt.congr_deriv
  have ht : horizontal P k ≤ horizontal P P.horizon := by
    rcases lt_or_eq_of_le hk with hk | rfl
    · exact (horizontal_increasing P k P.horizon hk le_rfl).le
    · exact le_rfl
  rw [← iteratedDeriv_one, scalarObjective_left P (by omega) ht,
    (curve_spec P 2).2.1 k hk 1 (by omega)]
  simp [curveJet,scalarJet]

/-- Both genuine wall-coordinate curves have zero differential at every source node. -/
theorem curve_flat_hasFDerivAt_node (P : Parameters) {i : Fin 3} (hi : i ≠ 2)
    {k : ℕ} (hk : k ≤ P.horizon) (y : ℝ) :
    HasFDerivAt (fun w : ℝ × ℝ => curve P i w.1)
      (0 : (ℝ × ℝ) →L[ℝ] ℝ) (horizontal P k,y) := by
  have he := (curve_hasDerivAt_node P i hk).congr_deriv
    (curveJet_flat P hi k 1 (by omega))
  have hh : HasFDerivAt (fun w : ℝ × ℝ => curve P i w.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) (horizontal P k,y) :=
    he.hasFDerivAt.comp (horizontal P k,y) (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp

/-- The genuine coordinate-map differential is the pure vertical coordinate
at each source node; width and center first jets vanish exactly. -/
theorem corridorCoordinates_hasFDerivAt_node (P : Parameters) {k : ℕ}
    (hk : k ≤ P.horizon) (y : ℝ) :
    HasFDerivAt (corridorCoordinates P)
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ))
      (horizontal P k,y) := by
  have hw := curve_flat_hasFDerivAt_node P (by decide : (0 : Fin 3) ≠ 2) hk y
  have hc := curve_flat_hasFDerivAt_node P (by decide : (1 : Fin 3) ≠ 2) hk y
  have hv := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.sub hc
  have hh := hw.prodMk hv
  convert hh using 1
  · funext w; rfl
  · simp only [sub_zero]

/-- The actual coordinate map at a node uses the prescribed width and center. -/
theorem corridorCoordinates_node (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon)
    (y : ℝ) : corridorCoordinates P (horizontal P k,y) =
      (amplitude P k,y - centerValue P k) := by
  have hw := (curve_spec P 0).2.1 k hk 0 (by omega)
  have hc := (curve_spec P 1).2.1 k hk 0 (by omega)
  simp only [iteratedDeriv_zero,curveJet,Matrix.cons_val_zero,widthJet,ite_true] at hw
  simp only [iteratedDeriv_zero,curveJet,Matrix.cons_val_one,Matrix.cons_val_zero,
    centerJet,ite_true] at hc
  simp only [corridorCoordinates,hw,hc]

/-- The actual corridor differential is a pure vertical quadratic differential
at each central node, including the two corridor walls. -/
theorem residualCorridor_hasFDerivAt_node (P : Parameters) {k : ℕ}
    (hk : k ≤ P.horizon) {y : ℝ}
    (hy : y - centerValue P k ∈ Icc (-amplitude P k / 2) (amplitude P k / 2)) :
    HasFDerivAt (residualCorridor P)
      ((2*(y - centerValue P k)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (horizontal P k,y) := by
  have hm := corridorCoordinates_hasFDerivAt_node P hk y
  have hp := (contDiff_profile.differentiable (by norm_num)
    (corridorCoordinates P (horizontal P k,y))).hasFDerivAt
  have hh := hp.comp (horizontal P k,y) hm
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    zero_apply,smul_apply,smul_eq_mul]
  rw [corridorCoordinates_node P hk y]
  have hv : ((0 : ℝ),v.2) = v.2 • ((0 : ℝ),(1 : ℝ)) := by ext <;> simp
  change fderiv ℝ (fun w : ℝ × ℝ => profile w.1 w.2)
    (amplitude P k,y - centerValue P k) (0,v.2) = _
  rw [hv,map_smul,fderiv_profile_vertical (amplitude_pos P hk) hy]
  simp [smul_eq_mul,mul_comm]

/-- The scalar coordinate differential carries the exact source negative slope. -/
theorem scalarObjective_lift_hasFDerivAt_node (P : Parameters) {k : ℕ}
    (hk : k ≤ P.horizon) (y : ℝ) :
    HasFDerivAt (fun w : ℝ × ℝ => scalarObjective P w.1)
      ((-amplitude P k) • ContinuousLinearMap.fst ℝ ℝ ℝ) (horizontal P k,y) := by
  have hh := (scalarObjective_hasDerivAt_node P hk).hasFDerivAt.comp
    (horizontal P k,y) (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [ContinuousLinearMap.toSpanSingleton_apply,mul_comm]

/-- The actual objective differential on a central source node. -/
theorem objective_hasFDerivAt_node (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon)
    {y : ℝ} (hy : y - centerValue P k ∈ Icc (-amplitude P k / 2) (amplitude P k / 2)) :
    HasFDerivAt (objective P)
      ((1/Real.sqrt 2) • ((-amplitude P k) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2*(y - centerValue P k)) • ContinuousLinearMap.snd ℝ ℝ ℝ))
      (horizontal P k,y) := by
  have hh := ((scalarObjective_lift_hasFDerivAt_node P hk y).add
    (residualCorridor_hasFDerivAt_node P hk hy)).const_smul (1/Real.sqrt 2)
  convert hh using 1
  funext w
  simp only [objective,Pi.smul_apply,smul_eq_mul,Pi.add_apply]
  ring

/-- The source prescribed points on the genuine Euclidean plane. -/
def gridPoint (P : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![horizontal P k,vertical P k]

/-- The alternating unit-coordinate direction of the source zig-zag. -/
def gridDirection (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![1,(-1 : ℝ)^k]

/-- The actual vertical offset at a source point is its signed half-width. -/
theorem vertical_sub_center (P : Parameters) (k : ℕ) :
    vertical P k-centerValue P k = -((-1 : ℝ)^k)*amplitude P k / 2 := by
  unfold centerValue
  ring

/-- Source grid points lie on the two closed corridor walls. -/
theorem vertical_sub_center_mem (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    vertical P k-centerValue P k ∈ Icc (-amplitude P k / 2) (amplitude P k / 2) := by
  have ha := (amplitude_pos P hk).le
  have hs : -1 ≤ (-1 : ℝ)^k ∧ (-1 : ℝ)^k ≤ 1 := by
    simpa only [abs_le] using (show |(-1 : ℝ)^k| ≤ 1 by simp)
  rw [vertical_sub_center]
  constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ 1-(-1 : ℝ)^k) ha,
    mul_nonneg (by linarith : 0 ≤ 1+(-1 : ℝ)^k) ha]

/-- The genuine Euclidean gradient is exactly the source alternating gradient. -/
theorem euclideanObjective_gradient_node (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    gradient (euclideanObjective P) (gridPoint P k) =
      (-amplitude P k / Real.sqrt 2) • gridDirection k := by
  have hh := (objective_hasFDerivAt_node P hk (vertical_sub_center_mem P hk)).comp
    (gridPoint P k) euclideanCoordinates.hasFDerivAt
  have hg : HasGradientAt (euclideanObjective P)
      ((-amplitude P k / Real.sqrt 2) • gridDirection k) (gridPoint P k) := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,smul_apply,add_apply,
      smul_eq_mul,InnerProductSpace.toDual_apply_apply]
    rw [vertical_sub_center]
    simp [euclideanCoordinates,gridDirection,PiLp.inner_apply,Fin.sum_univ_two]
    ring
  exact hg.gradient

/-- The alternating source direction has constant Euclidean norm square root two. -/
theorem norm_gridDirection (k : ℕ) : ‖gridDirection k‖ = Real.sqrt 2 := by
  rw [norm_eq_sqrt_real_inner]
  have hs : ((-1 : ℝ)^k)^2 = 1 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  congr 1
  simp only [gridDirection,PiLp.inner_apply,Fin.sum_univ_two]
  simpa only [WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_one,
    RCLike.inner_apply,starRingEnd_apply,star_trivial,one_mul] using
      (show (1 : ℝ)+(-1 : ℝ)^k*(-1 : ℝ)^k=2 by nlinarith [hs])

/-- The genuine gradient norm at each source node is its prescribed amplitude. -/
theorem norm_euclideanObjective_gradient_node (P : Parameters) {k : ℕ}
    (hk : k ≤ P.horizon) :
    ‖gradient (euclideanObjective P) (gridPoint P k)‖ = amplitude P k := by
  rw [euclideanObjective_gradient_node P hk,norm_smul,norm_gridDirection,
    Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos (amplitude_pos P hk),
    abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)),div_mul_cancel₀]
  positivity

/-- The prescribed source update is the actual negative-gradient step of length square root two. -/
theorem gridPoint_succ (P : Parameters) {k : ℕ} (hk : k < P.horizon) :
    gridPoint P (k+1) = gridPoint P k - Real.sqrt 2 •
      gradient (euclideanObjective P) (gridPoint P k) := by
  rw [euclideanObjective_gradient_node P hk.le]
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [gridPoint,gridDirection,horizontal_succ,vertical_succ,PiLp.smul_apply,
      PiLp.sub_apply]
  all_goals field_simp
  all_goals ring

/-- The canonical rounded horizon is the exact first gradient-tolerance index. -/
theorem gradient_first_stop (P : Parameters) :
    (∀ k < P.horizon,
      P.accuracy < ‖gradient (euclideanObjective P) (gridPoint P k)‖) ∧
    ‖gradient (euclideanObjective P) (gridPoint P P.horizon)‖ = P.accuracy := by
  constructor
  · intro k hk
    rw [norm_euclideanObjective_gradient_node P hk.le]
    exact amplitude_gt_accuracy P hk
  · rw [norm_euclideanObjective_gradient_node P le_rfl,amplitude_horizon]

/-- The actual source sequence starts at the Euclidean origin. -/
theorem gridPoint_zero (P : Parameters) : gridPoint P 0 = 0 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [gridPoint,horizontal,vertical]

end ExactSteepestDescent.Corridor
