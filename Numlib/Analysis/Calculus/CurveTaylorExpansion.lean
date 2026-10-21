import Numlib.Analysis.Calculus.CurveTaylor
import Numlib.Optimization.TaylorCriticalityCriteria

/-!
# Taylor expansion along polynomial curves

Multilinearity identifies the coefficients of a Taylor model on a polynomial curve with
positive ordered compositions. The local Taylor remainder then transfers the sign of the
first nonvanishing coefficient from a local minimum.
-/

noncomputable section
open scoped Nat ContDiff
open Filter Topology Asymptotics
namespace CurveTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive composition terms can be indexed in any ambient interval containing their sum. -/
theorem sum_compositionIndices_eq {d n k : ℕ} (hdn : d ≤ n)
    (A : (Fin k → ℕ) → ℝ) :
    (∑ l ∈ compositionIndices d k, A (fun i => (l i).val)) =
      ∑ l : Fin k → Fin (n + 1),
        if (∀ i, 1 ≤ (l i).val) ∧ ∑ i, (l i).val = d then
          A (fun i => (l i).val) else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun l _ i => (l i).castLE (Nat.add_le_add_right hdn 1))
  · intro l hl
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE] using
      mem_compositionIndices.mp hl
  · intro l hl m hm he
    funext i
    apply Fin.ext
    exact congrArg (fun l => (l i).val) he
  · intro l hl
    have hl' := (Finset.mem_filter.mp hl).2
    have hb (i : Fin k) : (l i).val ≤ d := by
      rw [← hl'.2]
      exact Finset.single_le_sum (f := fun i => (l i).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    refine ⟨fun i => ⟨(l i).val, Nat.lt_succ_of_le (hb i)⟩, ?_, ?_⟩
    · exact mem_compositionIndices.mpr hl'
    · funext i
      exact Fin.ext rfl
  · intro l hl
    rfl

/-- The polynomial displacement specified by a finite jet. -/
def displacement (n : ℕ) (s : ℕ → E) (t : ℝ) : E :=
  ∑ i : Fin (n + 1), if i.val = 0 then 0 else t ^ i.val • s i.val

/-- Polynomial curves start at zero displacement. -/
@[simp] theorem displacement_zero (n : ℕ) (s : ℕ → E) : displacement n s 0 = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · rfl
  · simp [zero_pow hi]

/-- The displacement polynomial is smooth of every order. -/
theorem contDiff_displacement (n : ℕ) (s : ℕ → E) (r : ℕ∞ω) :
    ContDiff ℝ r (displacement n s) := by
  classical
  apply ContDiff.sum
  intro i _
  by_cases hi : i.val = 0
  · simp only [hi, ite_true]
    exact contDiff_const
  · simp only [hi, ite_false]
    exact (contDiff_id.pow _).smul contDiff_const

/-- The polynomial curve is continuous. -/
theorem continuous_displacement (n : ℕ) (s : ℕ → E) : Continuous (displacement n s) :=
  (contDiff_displacement n s 0).continuous

/-- Multilinear expansion on a finite polynomial curve, indexed by positive tuples. -/
theorem multilinear_displacement (n k : ℕ)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (s : ℕ → E) (t : ℝ) :
    M (fun _ => displacement n s t) =
      ∑ l : Fin k → Fin (n + 1),
        if ∀ i, 1 ≤ (l i).val then
          t ^ (∑ i, (l i).val) * M (fun i => s (l i).val) else 0 := by
  classical
  unfold displacement
  rw [M.map_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : ∀ i, 1 ≤ (l i).val
  · rw [ite_eq_left hl]
    have he : (fun i => if (l i).val = 0 then (0 : E) else t ^ (l i).val • s (l i).val) =
        (fun i => t ^ (l i).val • s (l i).val) := by
      funext i
      rw [ite_eq_right (by have := hl i; omega)]
    rw [he, M.map_smul_univ, ← Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  · rw [ite_eq_right hl]
    push Not at hl
    obtain ⟨i, hi⟩ := hl
    apply M.map_coord_zero i
    simp [show (l i).val = 0 by omega]

/-- The degree coefficient after substitution into a Taylor model of order `n`. -/
def modelCoefficient (f : E → ℝ) (x : E) (n d : ℕ) (s : ℕ → E) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, ((k ! : ℝ)⁻¹) *
    ∑ l : Fin k → Fin (n + 1),
      if (∀ i, 1 ≤ (l i).val) ∧ ∑ i, (l i).val = d then
        iteratedFDeriv ℝ k f x (fun i => s (l i).val) else 0

/-- A positive tuple has at least as many units as entries. -/
theorem length_le_sum {n k : ℕ} {l : Fin k → Fin (n + 1)}
    (hl : ∀ i, 1 ≤ (l i).val) : k ≤ ∑ i, (l i).val := by
  calc
    k = ∑ _ : Fin k, 1 := by simp
    _ ≤ ∑ i, (l i).val := Finset.sum_le_sum (fun i _ => hl i)

/-- Substitution preserves every coefficient within the Taylor truncation order. -/
theorem modelCoefficient_eq_coefficient (f : E → ℝ) (x : E) {d n : ℕ}
    (hdn : d ≤ n) (s : ℕ → E) : modelCoefficient f x n d s = coefficient f x d s := by
  classical
  unfold modelCoefficient coefficient
  rw [← Finset.sum_subset (show Finset.Icc 1 d ⊆ Finset.Icc 1 n from
    fun k hk => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2.trans hdn⟩)]
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    exact (sum_compositionIndices_eq hdn
      (fun l => iteratedFDeriv ℝ k f x (fun i => s (l i)))).symm
  · intro k hk hkd
    have hdk : d < k := by simp only [Finset.mem_Icc, not_and, not_le] at *; omega
    have hz : (∑ l : Fin k → Fin (n + 1),
        if (∀ i, 1 ≤ (l i).val) ∧ ∑ i, (l i).val = d then
          iteratedFDeriv ℝ k f x (fun i => s (l i).val) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      rw [ite_eq_right]
      rintro ⟨hl, he⟩
      have := length_le_sum hl
      omega
    rw [hz, mul_zero]

/-- Every degree of the substituted model is bounded by the product of the two degrees. -/
theorem taylorModel_displacement (f : E → ℝ) (x : E) (n : ℕ) (s : ℕ → E) (t : ℝ) :
    Optimization.RegularizedTaylorModel.taylorModel f n x (displacement n s t) =
      f x + ∑ d ∈ Finset.range (n * n + 1), t ^ d * modelCoefficient f x n d s := by
  classical
  have hsplit : Optimization.RegularizedTaylorModel.taylorModel f n x (displacement n s t) =
      f x + ∑ k ∈ Finset.Icc 1 n, ((k ! : ℝ)⁻¹) *
        iteratedFDeriv ℝ k f x (fun _ => displacement n s t) := by
    unfold Optimization.RegularizedTaylorModel.taylorModel
    rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < n + 1)]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
      iteratedFDeriv_zero_apply, smul_eq_mul, Finset.Ico_add_one_right_eq_Icc]
  rw [hsplit]
  congr 1
  simp only [modelCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [multilinear_displacement, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.range (n * n + 1))
    (g := fun l : Fin k → Fin (n + 1) => ∑ i, (l i).val) ?_]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    by_cases he : (∑ i, (l i).val) = d
    · by_cases hp : ∀ i, 1 ≤ (l i).val
      · simp [he, hp, mul_left_comm]
      · simp [he, hp]
    · simp [he]
  · intro l _
    apply Finset.mem_range.mpr
    have hb : ∑ i, (l i).val ≤ k * n := by
      calc
        _ ≤ ∑ _ : Fin k, n := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (l i).isLt)
        _ = k * n := by simp [Nat.mul_comm]
    have := Nat.mul_le_mul_right n (Finset.mem_Icc.mp hk).2
    omega

/-- A polynomial displacement is at most linear near its origin. -/
theorem displacement_isBigO (n : ℕ) (s : ℕ → E) :
    displacement n s =O[𝓝 0] (fun t : ℝ => t) := by
  simpa using ((contDiff_displacement n s 1).differentiable (by simp) 0).isBigO_sub

/-- The actual local Taylor error remains of little-o order after polynomial substitution. -/
theorem remainder_displacement_isLittleO {f : E → ℝ} {x : E} {n : ℕ}
    (hn : 1 ≤ n) (hf : ContDiffAt ℝ n f x) (s : ℕ → E) :
    (fun t => f (x + displacement n s t) -
      Optimization.RegularizedTaylorModel.taylorModel f n x (displacement n s t))
      =o[𝓝 0] (fun t : ℝ => t ^ n) := by
  have hr : (fun y : E => f (x + y) -
      Optimization.RegularizedTaylorModel.taylorModel f n x y) =o[𝓝 0]
        (fun y => ‖y‖ ^ n) := by
    apply isLittleO_iff.mpr
    intro ε hε
    obtain ⟨r, hr, hb⟩ :=
      Optimization.TaylorCriticality.exists_taylorModel_remainder_le hn hf hε
    filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with y hy
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hb y
      (by simpa only [Metric.mem_ball, dist_zero_right] using hy)
  have hc : Tendsto (displacement n s) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_displacement n s).tendsto 0
  exact (hr.comp_tendsto hc).trans_isBigO ((displacement_isBigO n s).norm_left.pow n)

/-- The first potentially nonzero coefficient is the one-sided normalized polynomial limit. -/
theorem tendsto_polynomial_div_pow {a : ℕ → ℝ} {N j : ℕ} (hjN : j ≤ N)
    (ha : ∀ d, d < j → a d = 0) :
    Tendsto (fun t : ℝ => (∑ d ∈ Finset.range (N + 1), t ^ d * a d) / t ^ j)
      (𝓝[>] 0) (𝓝 (a j)) := by
  classical
  have hterm (d : ℕ) : Tendsto (fun t : ℝ => t ^ d * a d / t ^ j)
      (𝓝[>] 0) (𝓝 (if d = j then a j else 0)) := by
    rcases lt_trichotomy d j with hd | rfl | hd
    · simp only [ha d hd, mul_zero, zero_div, ite_eq_right (ne_of_lt hd)]
      exact tendsto_const_nhds
    · simp only [ite_true]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      field_simp [ne_of_gt (show (0 : ℝ) < t from ht)]
    · have he : (fun t : ℝ => t ^ d * a d / t ^ j) =ᶠ[𝓝[>] 0]
          (fun t => t ^ (d - j) * a d) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [pow_sub₀ t (ne_of_gt (show (0 : ℝ) < t from ht)) hd.le]
        ring
      have hp := ((tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)).pow (d - j)).mul_const (a d)
      simpa [ne_of_gt hd, zero_pow (by omega : d - j ≠ 0)] using hp.congr' he.symm
  have hs := tendsto_finsetSum (Finset.range (N + 1)) (fun d _ => hterm d)
  have he : (∑ d ∈ Finset.range (N + 1), if d = j then a j else 0) = a j := by
    simp [Finset.mem_range.mpr (Nat.lt_succ_of_le hjN)]
  simpa only [he, Finset.sum_div] using hs

/-- Vanishing lower composition coefficients give the normalized limit of the actual model. -/
theorem tendsto_taylorModel_displacement_div_pow (f : E → ℝ) (x : E) {n : ℕ}
    (hn : 1 ≤ n) (s : ℕ → E)
    (hs : ∀ d, 1 ≤ d → d < n → coefficient f x d s = 0) :
    Tendsto (fun t : ℝ =>
      (Optimization.RegularizedTaylorModel.taylorModel f n x (displacement n s t) - f x) /
        t ^ n) (𝓝[>] 0) (𝓝 (coefficient f x n s)) := by
  have h0 : ∀ d, d < n → modelCoefficient f x n d s = 0 := by
    intro d hd
    rw [modelCoefficient_eq_coefficient f x hd.le]
    by_cases hd0 : d = 0
    · simp [hd0]
    · exact hs d (by omega) hd
  have hnn : n ≤ n * n := by simpa using Nat.mul_le_mul_left n hn
  have ht := tendsto_polynomial_div_pow hnn h0
  simpa only [taylorModel_displacement, add_sub_cancel_left,
    modelCoefficient_eq_coefficient f x le_rfl] using ht

/-- The normalized objective difference tends to its first potentially nonzero curve
coefficient. This identifies the finite composition formula with the actual local expansion. -/
theorem tendsto_objective_displacement_div_pow {f : E → ℝ} {x : E} {n : ℕ}
    (hn : 1 ≤ n) (hf : ContDiffAt ℝ n f x) (s : ℕ → E)
    (hs : ∀ d, 1 ≤ d → d < n → coefficient f x d s = 0) :
    Tendsto (fun t : ℝ => (f (x + displacement n s t) - f x) / t ^ n)
      (𝓝[>] 0) (𝓝 (coefficient f x n s)) := by
  have hr := ((remainder_displacement_isLittleO hn hf s).tendsto_div_nhds_zero).mono_left
    (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have ht := tendsto_taylorModel_displacement_div_pow f x hn s hs
  convert hr.add ht using 1
  · ext t
    ring
  · simp

/-- At a locally smooth local minimum, the first potentially nonzero coefficient on every
polynomial curve is nonnegative. No nonzero-jet or finite-dimensional assumption is needed. -/
theorem coefficient_nonneg_of_isLocalMin {f : E → ℝ} {x : E} {n : ℕ}
    (hn : 1 ≤ n) (hf : ContDiffAt ℝ n f x) (hmin : IsLocalMin f x)
    (s : ℕ → E) (hs : ∀ d, 1 ≤ d → d < n → coefficient f x d s = 0) :
    0 ≤ coefficient f x n s := by
  apply ge_of_tendsto (tendsto_objective_displacement_div_pow hn hf s hs)
  have hc : Tendsto (fun t => x + displacement n s t) (𝓝[>] 0) (𝓝 x) := by
    have ht : Tendsto (displacement n s) (𝓝[>] 0) (𝓝 0) := by
      simpa only [displacement_zero] using
        ((continuous_displacement n s).tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [add_zero] using ht.const_add x
  filter_upwards [hc.eventually hmin, self_mem_nhdsWithin] with t hm ht
  exact div_nonneg (sub_nonneg.mpr hm) (pow_nonneg (le_of_lt ht) n)

/-- Every locally `C^q` local minimum satisfies all the curve-order sign conditions. -/
theorem isOrderMinimizer_of_isLocalMin {f : E → ℝ} {x : E} {q : ℕ}
    (hf : ContDiffAt ℝ q f x) (hmin : IsLocalMin f x) : IsOrderMinimizer f x q := by
  intro j hj hjq s hs
  exact coefficient_nonneg_of_isLocalMin hj
    (hf.of_le (by exact_mod_cast hjq)) hmin s hs

end CurveTaylor
