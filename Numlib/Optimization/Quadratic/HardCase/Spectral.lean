import Numlib.Optimization.Quadratic.HardCase.Iteration
import Numlib.Optimization.Quadratic.HardCase.Solutions

/-!
# Metric coordinates of genuine normalized inverse iterates

A generalized metric-orthonormal basis diagonalizes the actual shifted solve.
Ratios of its true coordinates cancel every normalization factor. The
Rayleigh value and its nonnegative spectral error are actual quadratic forms.
-/

open scoped BigOperators
namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] {H M : E →L[ℝ] E}
  (B : PencilBasis (ι := ι) H M)

omit [Fintype ι] in
/-- Generalized metric inner products are the actual basis coordinates. -/
theorem coordinate_eq_metric_inner [Finite ι] (v : E) (i : ι) :
    B.basis.repr v i = inner ℝ (M v) (B.basis i) := by
  let := Fintype.ofFinite ι
  conv_rhs => arg 2; rw [← B.basis.sum_repr v]
  exact (B.inner_metric_sum _ _).symm

/-- The true metric norm square is the sum of squared actual coordinates. -/
theorem metric_norm_sq_coordinates (hM : M.toLinearMap.IsSymmetricCoercive) (v : E) :
    energyNorm M.toLinearMap v ^ 2 = ∑ i, (B.basis.repr v i) ^ 2 := by
  rw [hM.energyNorm_sq]
  conv_lhs => rw [← B.basis.sum_repr v]
  exact B.metric_norm_sq_sum _

/-- The actual Rayleigh evaluation is the spectral weighted coordinate square sum. -/
theorem rayleigh_eq_sum_coordinates (v : E) :
    HardCase.rayleighValue H v = ∑ i, B.eigenvalue i * (B.basis.repr v i) ^ 2 := by
  rw [HardCase.rayleighValue_apply, real_inner_comm]
  conv_lhs => rw [← B.basis.sum_repr v]
  simp only [map_sum, map_smul, B.eigenvector, sum_inner, real_inner_smul_left,
    inner_sum, real_inner_smul_right, B.orthonormal]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype ι] in
/-- The actual shifted inverse has the coordinate obtained by the true diagonal solve. -/
theorem raw_inverse_coordinate [Finite ι] (τ : ℝ) (hInv : (H + τ • M).IsInvertible)
    (hτ : ∀ i, τ + B.eigenvalue i ≠ 0) (v : E) (i : ι) :
    B.basis.repr ((H + τ • M).inverse (M v)) i =
      B.basis.repr v i / (τ + B.eigenvalue i) := by
  apply (eq_div_iff (hτ i)).mpr
  rw [← B.shifted_apply_inner, hInv.self_apply_inverse, ← B.coordinate_eq_metric_inner]

omit [Fintype ι] in
/-- The actual normalized inverse coordinate contains exactly its true metric normalization. -/
theorem inverseStep_coordinate [Finite ι] (τ : ℝ) (hInv : (H + τ • M).IsInvertible)
    (hτ : ∀ i, τ + B.eigenvalue i ≠ 0) (v : E) (i : ι) :
    B.basis.repr (HardCase.inverseStep H M τ v) i =
      (energyNorm M.toLinearMap ((H + τ • M).inverse (M v)))⁻¹ *
        (B.basis.repr v i / (τ + B.eigenvalue i)) := by
  rw [HardCase.inverseStep_eq]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul,
    B.raw_inverse_coordinate τ hInv hτ]

omit [Fintype ι] in
private theorem inverse_ne_zero [Finite ι] (τ : ℝ) (hInv : (H + τ • M).IsInvertible)
    (hτ : ∀ i, τ + B.eigenvalue i ≠ 0) {v : E} {l : ι}
    (hl : B.basis.repr v l ≠ 0) : (H + τ • M).inverse (M v) ≠ 0 := by
  intro hz
  have hh := B.raw_inverse_coordinate τ hInv hτ v l
  rw [hz, map_zero, Finsupp.zero_apply] at hh
  exact (div_ne_zero hl (hτ l)) hh.symm

omit [Fintype ι] in
/-- A genuine normalized inverse iterate is metric-unit whenever its input has
one nonzero coordinate and the shifted solve is nonsingular. -/
theorem inverseStep_unit [Finite ι] (hM : M.toLinearMap.IsSymmetricCoercive)
    (τ : ℝ) (hInv : (H + τ • M).IsInvertible) (hτ : ∀ i, τ + B.eigenvalue i ≠ 0)
    {v : E} {l : ι} (hl : B.basis.repr v l ≠ 0) :
    energyNorm M.toLinearMap (HardCase.inverseStep H M τ v) = 1 := by
  have hu := hM.energyNorm_pos (B.inverse_ne_zero τ hInv hτ hl)
  change ‖WithEnergy.equiv M.toLinearMap hM (HardCase.inverseStep H M τ v)‖ = 1
  rw [HardCase.inverseStep_eq, map_smul, norm_smul, WithEnergy.norm_equiv,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu), inv_mul_cancel₀ hu.ne']

omit [Fintype ι] in
/-- Nonsingular inverse normalization preserves every nonzero input coordinate. -/
theorem inverseStep_coordinate_ne_zero [Finite ι] (hM : M.toLinearMap.IsSymmetricCoercive)
    (τ : ℝ) (hInv : (H + τ • M).IsInvertible) (hτ : ∀ i, τ + B.eigenvalue i ≠ 0)
    {v : E} {l : ι} (hl : B.basis.repr v l ≠ 0) :
    B.basis.repr (HardCase.inverseStep H M τ v) l ≠ 0 := by
  rw [B.inverseStep_coordinate τ hInv hτ]
  exact mul_ne_zero (inv_ne_zero (hM.energyNorm_pos
    (B.inverse_ne_zero τ hInv hτ hl)).ne') (div_ne_zero hl (hτ l))

omit [Fintype ι] in
/-- Coordinate ratios remove the genuine inverse-step metric normalization. -/
theorem inverseStep_coordinate_ratio [Finite ι] (hM : M.toLinearMap.IsSymmetricCoercive)
    (τ : ℝ) (hInv : (H + τ • M).IsInvertible) (hτ : ∀ i, τ + B.eigenvalue i ≠ 0)
    {v : E} {l : ι} (hl : B.basis.repr v l ≠ 0) (i : ι) :
    B.basis.repr (HardCase.inverseStep H M τ v) i /
      B.basis.repr (HardCase.inverseStep H M τ v) l =
      (B.basis.repr v i / B.basis.repr v l) *
        ((τ + B.eigenvalue l) / (τ + B.eigenvalue i)) := by
  rw [B.inverseStep_coordinate τ hInv hτ, B.inverseStep_coordinate τ hInv hτ]
  have hn := (hM.energyNorm_pos (B.inverse_ne_zero τ hInv hτ hl)).ne'
  field_simp

omit [Fintype ι] in
/-- Every actual fixed-shift block has the exact power coordinate-ratio formula. -/
theorem inverseBlock_coordinate_ratio [Finite ι] (hM : M.toLinearMap.IsSymmetricCoercive)
    (τ : ℝ) (hInv : (H + τ • M).IsInvertible) (hτ : ∀ i, τ + B.eigenvalue i ≠ 0)
    (w : ℕ → E) (n : ℕ)
    (hw : ∀ j < n, w (j + 1) = HardCase.inverseStep H M τ (w j))
    {l : ι} (hl : B.basis.repr (w 0) l ≠ 0) :
    B.basis.repr (w n) l ≠ 0 ∧
      ∀ i, B.basis.repr (w n) i / B.basis.repr (w n) l =
        (B.basis.repr (w 0) i / B.basis.repr (w 0) l) *
          ((τ + B.eigenvalue l) / (τ + B.eigenvalue i)) ^ n := by
  induction n with
  | zero => exact ⟨hl, fun i => by simp⟩
  | succ n ih =>
      obtain ⟨hn, hratio⟩ := ih (fun j hj => hw j (by omega))
      rw [hw n (by omega)]
      refine ⟨B.inverseStep_coordinate_ne_zero hM τ hInv hτ hn, ?_⟩
      intro i
      rw [B.inverseStep_coordinate_ratio hM τ hInv hτ hn i, hratio, pow_succ]
      ring

/-- The actual Rayleigh error of a metric-unit vector is the nonnegative
spectral-gap weighted coordinate sum. -/
theorem rayleigh_error_nonneg (hM : M.toLinearMap.IsSymmetricCoercive)
    (least : ℝ) (hmin : ∀ i, least ≤ B.eigenvalue i) {v : E}
    (hv : energyNorm M.toLinearMap v = 1) :
    HardCase.rayleighValue H v - least =
      ∑ i, (B.eigenvalue i - least) * (B.basis.repr v i) ^ 2 ∧
      0 ≤ HardCase.rayleighValue H v - least := by
  have hsum := B.metric_norm_sq_coordinates hM v
  rw [hv, one_pow] at hsum
  have he : HardCase.rayleighValue H v - least =
      ∑ i, (B.eigenvalue i - least) * (B.basis.repr v i) ^ 2 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hsum, mul_one,
      B.rayleigh_eq_sum_coordinates]
  refine ⟨he, ?_⟩
  rw [he]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hmin i)) (sq_nonneg _))

omit [Fintype ι] in
/-- Every positive-length actual normalized inverse block ends on the metric
unit sphere. -/
theorem inverseBlock_unit [Finite ι] (hM : M.toLinearMap.IsSymmetricCoercive)
    (τ : ℝ) (hInv : (H + τ • M).IsInvertible) (hτ : ∀ i, τ + B.eigenvalue i ≠ 0)
    (w : ℕ → E) (n : ℕ) (hn : 1 ≤ n)
    (hw : ∀ j < n, w (j + 1) = HardCase.inverseStep H M τ (w j))
    {l : ι} (hl : B.basis.repr (w 0) l ≠ 0) : energyNorm M.toLinearMap (w n) = 1 := by
  have hp := (B.inverseBlock_coordinate_ratio hM τ hInv hτ w (n - 1)
    (fun j hj => hw j (by omega)) hl).1
  have he : n = (n - 1) + 1 := by omega
  rw [he, hw (n - 1) (by omega)]
  exact B.inverseStep_unit hM τ hInv hτ hp

omit [Fintype ι] in
/-- Each coordinate of a metric-unit vector is controlled by its ratio to any
nonzero reference coordinate. -/
theorem coordinate_sq_le_ratio_sq [Finite ι] (hM : M.toLinearMap.IsSymmetricCoercive)
    {v : E} (hv : energyNorm M.toLinearMap v = 1) {l : ι}
    (hl : B.basis.repr v l ≠ 0) (i : ι) :
    (B.basis.repr v i) ^ 2 ≤ (B.basis.repr v i / B.basis.repr v l) ^ 2 := by
  let := Fintype.ofFinite ι
  have hs := B.metric_norm_sq_coordinates hM v
  rw [hv, one_pow] at hs
  have hle : (B.basis.repr v l) ^ 2 ≤ 1 := by
    rw [hs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (B.basis.repr v j)) (Finset.mem_univ l)
  have he : B.basis.repr v i = (B.basis.repr v i / B.basis.repr v l) *
      B.basis.repr v l := (div_mul_cancel₀ _ hl).symm
  calc
    _ = (B.basis.repr v i / B.basis.repr v l) ^ 2 * (B.basis.repr v l) ^ 2 := by
      nth_rw 1 [he]
      rw [mul_pow]
    _ ≤ _ := mul_le_of_le_one_right (sq_nonneg _) hle

/-- Actual finite spectral coefficient of a normalized inverse block. -/
noncomputable def rayleighCoefficient (least : ℝ) (R : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, (B.eigenvalue i - least) * R i ^ 2 / (B.eigenvalue i - least) ^ (2 * n)

/-- A common positive spectral coefficient precedes every shift and bounded
inverse-block length. -/
noncomputable def rayleighBoundConstant (least : ℝ) (R : ι → ℝ) (N : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (N + 1), B.rayleighCoefficient least R n

private theorem rayleighCoefficient_nonneg (least : ℝ) (hmin : ∀ i, least ≤ B.eigenvalue i)
    (R : ι → ℝ) (n : ℕ) : 0 ≤ B.rayleighCoefficient least R n :=
  Finset.sum_nonneg (fun i _ => div_nonneg
    (mul_nonneg (sub_nonneg.mpr (hmin i)) (sq_nonneg _))
      (pow_nonneg (sub_nonneg.mpr (hmin i)) _))

/-- Genuine nonnegative spectral gaps make the common coefficient positive. -/
theorem rayleighBoundConstant_pos (least : ℝ) (hmin : ∀ i, least ≤ B.eigenvalue i)
    (R : ι → ℝ) (N : ℕ) : 0 < B.rayleighBoundConstant least R N := by
  have hh : 0 ≤ ∑ n ∈ Finset.range (N + 1), B.rayleighCoefficient least R n :=
    Finset.sum_nonneg (fun n _ => B.rayleighCoefficient_nonneg least hmin R n)
  dsimp [rayleighBoundConstant]
  linarith

/-- Every bounded block coefficient is bounded by the fixed common one. -/
theorem rayleighCoefficient_le_bound (least : ℝ) (hmin : ∀ i, least ≤ B.eigenvalue i)
    (R : ι → ℝ) {n N : ℕ} (hn : n ≤ N) :
    B.rayleighCoefficient least R n ≤ B.rayleighBoundConstant least R N := by
  have hh := Finset.single_le_sum
    (fun j _ => B.rayleighCoefficient_nonneg least hmin R j)
      (Finset.mem_range.mpr (show n < N + 1 by omega))
  dsimp [rayleighBoundConstant]
  linarith

/-- An actual normalized inverse block preserves the nonzero least-eigenspace
component, contracts all relative coordinates, and has a higher-order genuine
Rayleigh error with a fixed finite spectral bound. -/
theorem inverseBlock_rayleigh_bound (hM : M.toLinearMap.IsSymmetricCoercive)
    (least : ℝ) (hmin : ∀ i, least ≤ B.eigenvalue i) {l : ι}
    (hl : B.eigenvalue l = least) (τ : ℝ) (hτ : -least < τ)
    (hInv : (H + τ • M).IsInvertible) (w : ℕ → E) {n N : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (hw : ∀ j < n, w (j + 1) = HardCase.inverseStep H M τ (w j))
    (hne : B.basis.repr (w 0) l ≠ 0) (R : ι → ℝ)
    (hR : ∀ i, |B.basis.repr (w 0) i / B.basis.repr (w 0) l| ≤ R i) :
    energyNorm M.toLinearMap (w n) = 1 ∧ B.basis.repr (w n) l ≠ 0 ∧
      (∀ i, |B.basis.repr (w n) i / B.basis.repr (w n) l| ≤ R i) ∧
      0 ≤ HardCase.rayleighValue H (w n) - least ∧
      HardCase.rayleighValue H (w n) - least ≤
        B.rayleighBoundConstant least R N * (τ + least) ^ (2 * n) := by
  have hden (i : ι) : 0 < τ + B.eigenvalue i := by linarith [hmin i]
  have hdne : ∀ i, τ + B.eigenvalue i ≠ 0 := fun i => (hden i).ne'
  obtain ⟨hnewne, hratio⟩ := B.inverseBlock_coordinate_ratio hM τ hInv hdne w n hw hne
  have hunit := B.inverseBlock_unit hM τ hInv hdne w n hn hw hne
  have he : 0 < τ + least := by linarith
  have hR0 (i : ι) : 0 ≤ R i := (abs_nonneg _).trans (hR i)
  have hrat (i : ι) : |B.basis.repr (w n) i / B.basis.repr (w n) l| ≤ R i := by
    rw [hratio i, hl, abs_mul, abs_pow, abs_of_pos (div_pos he (hden i))]
    have hq : (τ + least) / (τ + B.eigenvalue i) ≤ 1 :=
      (div_le_one (hden i)).mpr (by linarith [hmin i])
    have hp := pow_le_one₀ (n := n) (div_nonneg he.le (hden i).le) hq
    exact (mul_le_of_le_one_right (abs_nonneg _) hp).trans (hR i)
  have hδ := B.rayleigh_error_nonneg hM least hmin hunit
  refine ⟨hunit, hnewne, hrat, hδ.2, ?_⟩
  rw [hδ.1]
  calc
    _ ≤ ∑ i, ((B.eigenvalue i - least) * R i ^ 2 /
        (B.eigenvalue i - least) ^ (2 * n)) * (τ + least) ^ (2 * n) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hgap : B.eigenvalue i = least
      · simp [hgap]
      have hg : 0 < B.eigenvalue i - least := lt_of_le_of_ne
        (sub_nonneg.mpr (hmin i)) (sub_ne_zero.mpr hgap).symm
      have hq : (τ + least) / (τ + B.eigenvalue i) ≤
          (τ + least) / (B.eigenvalue i - least) :=
        div_le_div_of_nonneg_left he.le hg (by linarith)
      have hp := pow_le_pow_left₀ (div_nonneg he.le (hden i).le) hq (2 * n)
      have hold : (B.basis.repr (w 0) i / B.basis.repr (w 0) l) ^ 2 ≤ R i ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hR0 i)).mpr (hR i)
      have hr2 : (B.basis.repr (w n) i / B.basis.repr (w n) l) ^ 2 =
          (B.basis.repr (w 0) i / B.basis.repr (w 0) l) ^ 2 *
            ((τ + least) / (τ + B.eigenvalue i)) ^ (2 * n) := by
        rw [hratio i, hl, mul_pow, ← pow_mul]
        rw [Nat.mul_comm n 2]
      have hci := B.coordinate_sq_le_ratio_sq hM hunit hnewne i
      rw [hr2] at hci
      have hh := hci.trans (mul_le_mul hold hp (pow_nonneg (div_nonneg he.le (hden i).le) _)
        (sq_nonneg _))
      calc
        _ ≤ (B.eigenvalue i - least) *
            (R i ^ 2 * ((τ + least) / (B.eigenvalue i - least)) ^ (2 * n)) :=
          mul_le_mul_of_nonneg_left hh hg.le
        _ = _ := by rw [div_pow]; ring
    _ = B.rayleighCoefficient least R n * (τ + least) ^ (2 * n) := by
      rw [rayleighCoefficient, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (B.rayleighCoefficient_le_bound least hmin R hnN)
      (pow_nonneg he.le _)

end QuadraticSecular.PencilBasis
