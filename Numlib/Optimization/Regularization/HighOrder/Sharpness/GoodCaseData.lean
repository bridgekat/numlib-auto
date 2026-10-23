import Numlib.Optimization.Regularization.HighOrder.Sharpness.Cancellation

/-!
# Fixed spatial scales for all-order unit-radius sharpness

The scale and regularization parameter are fixed before accuracy. Cancellation of the highest
tested derivative leaves a uniformly small factor in every lower model jet.
-/

namespace HighOrderRegularization.Sharpness
/-- A positive spatial scale depending only on the model degree and criticality order. -/
noncomputable def goodScale (p q : ℕ) : ℝ :=
  1 / (8 * q.factorial * (q : ℝ) * (1 + (p + 1 - q).factorial))
/-- A fixed monomial amplitude balancing the requested criticality after spatial scaling. -/
noncomputable def goodAmplitude (p q : ℕ) : ℝ :=
  (4 / 3) / goodScale p q ^ balance p q
/-- The fixed regularization parameter that cancels the highest tested model derivative. -/
noncomputable def goodParameter (p q : ℕ) : ℝ :=
  goodAmplitude p q * (p + 1 - q).factorial
/-- The accuracy-dependent spacing with a fixed spatial scale. -/
noncomputable def goodStep (p q : ℕ) (ε : ℝ) : ℝ := goodScale p q * root p q ε
/-- The spatial scale is positive for every positive criticality order. -/
theorem goodScale_pos {p q : ℕ} (hq : 0 < q) : 0 < goodScale p q := by
  unfold goodScale
  positivity
/-- The fixed spatial scale is at most one. -/
theorem goodScale_le_one {p q : ℕ} (hq : 0 < q) : goodScale p q ≤ 1 := by
  unfold goodScale
  apply (div_le_one (by positivity : (0 : ℝ) < _)).mpr
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hf : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hg : (1 : ℝ) ≤ (p + 1 - q).factorial := by exact_mod_cast Nat.factorial_pos _
  calc (1 : ℝ) ≤ 8 * 1 * 1 * (1 + 1) := by norm_num
    _ ≤ _ := by gcongr
/-- The monomial amplitude is strictly positive. -/
theorem goodAmplitude_pos {p q : ℕ} (hq : 0 < q) : 0 < goodAmplitude p q := by
  unfold goodAmplitude
  exact div_pos (by norm_num) (pow_pos (goodScale_pos hq) _)
/-- The fixed regularization parameter is strictly positive. -/
theorem goodParameter_pos {p q : ℕ} (hq : 0 < q) : 0 < goodParameter p q := by
  unfold goodParameter
  exact mul_pos (goodAmplitude_pos hq) (by positivity)
/-- The chosen parameter has exactly the required cancellation amplitude. -/
theorem cancellationAmplitude_goodParameter {p q : ℕ} :
    cancellationAmplitude p q (goodParameter p q) = goodAmplitude p q := by
  unfold cancellationAmplitude goodParameter
  exact mul_div_cancel_right₀ _ (by positivity)
/-- Every positive accuracy gives positive spacing. -/
theorem goodStep_pos {p q : ℕ} {ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    0 < goodStep p q ε := mul_pos (goodScale_pos hq) (root_pos p q hε)
/-- Unit-bounded accuracy keeps the step below the fixed spatial scale. -/
theorem goodStep_le_scale {p q : ℕ} {ε : ℝ} (hq : 0 < q) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    goodStep p q ε ≤ goodScale p q :=
  mul_le_of_le_one_right (goodScale_pos hq).le (root_le_one p q hε hε1)
/-- The actual critical derivative is exactly four thirds of the requested accuracy. -/
theorem goodAmplitude_step_power {p q : ℕ} {ε : ℝ} (hq : 0 < q) (hε : 0 ≤ ε) :
    goodAmplitude p q * goodStep p q ε ^ balance p q = (4 / 3) * ε := by
  have hd : balance p q ≠ 0 := by dsimp [balance]; omega
  have hu : root p q ε ^ balance p q = ε := Real.rpow_inv_natCast_pow hε hd
  rw [goodStep, mul_pow, hu, goodAmplitude]
  have hc : goodScale p q ^ balance p q ≠ 0 := pow_ne_zero _ (goodScale_pos hq).ne'
  field_simp
/-- The fixed scale makes every actual unit-radius model criticality test pass. -/
theorem good_model_test_bound {p q : ℕ} {ε : ℝ} (hq : 0 < q)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (q : ℝ) * ((cancellationAmplitude p q (goodParameter p q) + goodParameter p q) *
      goodStep p q ε ^ balance p q * goodStep p q ε) ≤ (1 / 2) * ε / q.factorial := by
  rw [cancellationAmplitude_goodParameter]
  have he : (goodAmplitude p q + goodParameter p q) * goodStep p q ε ^ balance p q =
      (4 / 3) * ε * (1 + (p + 1 - q).factorial) := by
    rw [goodParameter]
    calc _ = (goodAmplitude p q * goodStep p q ε ^ balance p q) *
          (1 + (p + 1 - q).factorial) := by ring
      _ = _ := by rw [goodAmplitude_step_power hq hε]
  rw [he]
  have ht := goodStep_le_scale (p := p) hq hε hε1
  calc _ ≤ (q : ℝ) * ((4 / 3) * ε * (1 + (p + 1 - q).factorial) * goodScale p q) := by
        gcongr
    _ = ε / (6 * q.factorial) := by
        unfold goodScale
        have hq0 : (q : ℝ) ≠ 0 := by positivity
        have hf : (q.factorial : ℝ) ≠ 0 := by positivity
        have hg : (1 + ((p + 1 - q).factorial : ℝ)) ≠ 0 := by positivity
        field_simp
        ring
    _ ≤ _ := by
        have hf : (0 : ℝ) < q.factorial := by positivity
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * q.factorial) hf).mpr
        nlinarith

end HighOrderRegularization.Sharpness
