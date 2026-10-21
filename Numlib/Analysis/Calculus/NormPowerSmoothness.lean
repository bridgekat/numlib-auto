import Numlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-!
# Finite smoothness of radial powers at the origin

Homogeneity bounds on the punctured space extend the iterated derivatives continuously
through zero below the radial exponent. This requires no sharp derivative constants.
-/

open Filter Asymptotics Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A radial power with exponent greater than one is little-o of the displacement. -/
theorem norm_rpow_isLittleO_id {r : ℝ} (hr : 1 < r) :
    (fun x : E => ‖x‖ ^ r) =o[𝓝 (0 : E)] (fun x => x) := by
  rw [← isLittleO_norm_right]
  have he : (fun x : E => ‖x‖ ^ r) =
      (fun x : E => ‖x‖ * ‖x‖ ^ (r - 1)) := by
    funext x
    rw [mul_comm, ← Real.rpow_add_one' (norm_nonneg x)
      (by linarith : r - 1 + 1 ≠ 0)]
    congr 1
    ring
  rw [he]
  have hc : ContinuousAt (fun x : E => ‖x‖ ^ (r - 1)) 0 := by
    fun_prop (discharger := positivity)
  have ht : Tendsto (fun x : E => ‖x‖ ^ (r - 1)) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero, Real.zero_rpow (by linarith : r - 1 ≠ 0)] using hc.tendsto
  simpa using (isBigO_refl (fun x : E => ‖x‖) (𝓝 0)).mul_isLittleO
    ((isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr ht)

/-- A zero jet whose radial order exceeds one has zero derivative at the origin. -/
theorem hasFDerivAt_iteratedFDeriv_norm_rpow_zero {r : ℝ} {j : ℕ}
    (hj : (j : ℝ) + 1 < r)
    (hz : iteratedFDeriv ℝ j (fun x : E => ‖x‖ ^ r) 0 = 0) :
    HasFDerivAt (𝕜 := ℝ) (iteratedFDeriv ℝ j (fun x : E => ‖x‖ ^ r)) 0 0 := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_normRpow_le (E := E) r j
  have hb : (iteratedFDeriv ℝ j (fun x : E => ‖x‖ ^ r)) =O[𝓝 0]
      (fun x : E => C * ‖x‖ ^ (r - j)) := by
    apply IsBigO.of_norm_le
    intro x
    by_cases hx : x = 0
    · subst x
      rw [hz, norm_zero]
      positivity
    · exact hbound x hx
  have hlo : (fun x : E => C * ‖x‖ ^ (r - j)) =o[𝓝 (0 : E)] (fun x => x) :=
    (norm_rpow_isLittleO_id (by linarith : 1 < r - j)).const_mul_left C
  apply HasFDerivAt.of_isLittleO
  simpa only [hz, sub_zero, zero_apply] using hb.trans_isLittleO hlo

/-- Below the radial exponent every iterated derivative vanishes at the origin. -/
theorem iteratedFDeriv_norm_rpow_zero_of_lt {r : ℝ} {j : ℕ} (hj : (j : ℝ) < r) :
    iteratedFDeriv ℝ j (fun x : E => ‖x‖ ^ r) 0 = 0 := by
  induction j with
  | zero =>
    ext v
    simp [iteratedFDeriv_zero_apply, Real.zero_rpow (by linarith : r ≠ 0)]
  | succ j ih =>
    have hjr : (j : ℝ) < r := by push_cast at hj; linarith
    have hd := hasFDerivAt_iteratedFDeriv_norm_rpow_zero
      (by simpa only [Nat.cast_add, Nat.cast_one] using hj) (ih hjr)
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hd.fderiv]
    simp

/-- Any iterated derivative strictly below the exponent is continuous through zero. -/
theorem continuous_iteratedFDeriv_norm_rpow_of_lt {r : ℝ} {j : ℕ}
    (hj : (j : ℝ) < r) :
    Continuous (iteratedFDeriv ℝ j (fun x : E => ‖x‖ ^ r)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_normRpow_le (E := E) r j
    have hz := iteratedFDeriv_norm_rpow_zero_of_lt (E := E) hj
    rw [ContinuousAt, hz, tendsto_zero_iff_norm_tendsto_zero]
    have hc : ContinuousAt (fun x : E => C * ‖x‖ ^ (r - j)) 0 := by
      fun_prop (discharger := positivity)
    have ht : Tendsto (fun x : E => C * ‖x‖ ^ (r - j)) (𝓝 0) (𝓝 0) := by
      simpa only [norm_zero, Real.zero_rpow (by linarith : r - j ≠ 0), mul_zero]
        using hc.tendsto
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun x => norm_nonneg _)
    intro x
    by_cases hx : x = 0
    · subst x
      dsimp
      rw [hz, norm_zero]
      positivity
    · exact hbound x hx
  · exact ((contDiffOn_normRpow r j).contDiffAt
      (isOpen_compl_singleton.mem_nhds hx)).continuousAt_iteratedFDeriv le_rfl

/-- Radial powers are globally Cⁿ whenever the exponent is strictly greater than n. -/
theorem contDiff_norm_rpow_of_lt {r : ℝ} {n : ℕ} (hn : (n : ℝ) < r) :
    ContDiff ℝ n (fun x : E => ‖x‖ ^ r) := by
  rw [contDiff_nat_iff_continuous_differentiable]
  constructor
  · intro j hj
    exact continuous_iteratedFDeriv_norm_rpow_of_lt
      ((show (j : ℝ) ≤ n by exact_mod_cast hj).trans_lt hn)
  · intro j hj x
    by_cases hx : x = 0
    · subst x
      apply HasFDerivAt.differentiableAt
        (hasFDerivAt_iteratedFDeriv_norm_rpow_zero (by
          have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
          linarith) (iteratedFDeriv_norm_rpow_zero_of_lt
            ((show (j : ℝ) < n by exact_mod_cast hj).trans hn)))
    · exact ((contDiffOn_normRpow r (j + 1)).contDiffAt
        (isOpen_compl_singleton.mem_nhds hx)).differentiableAt_iteratedFDeriv (by
          exact_mod_cast Nat.lt_succ_self j)
