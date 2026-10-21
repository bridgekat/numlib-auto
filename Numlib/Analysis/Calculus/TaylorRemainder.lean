import Numlib.Analysis.Calculus.Taylor

/-!
# Taylor remainders centered at the highest derivative

The integral identities use oriented interval integrals, so negative increments require no
reflection convention. Smoothness at every point of the segment determines the ordinary,
two-sided derivatives, including at its endpoints.
-/

open Set
open scoped Nat NNReal

/-- Taylor's integral remainder after subtracting the highest Taylor term. -/
theorem sub_sum_taylor_eq_integral_deriv_sub {f : ℝ → ℝ} {x y : ℝ} {n : ℕ}
    (hf : ∀ u ∈ uIcc x y, ContDiffAt ℝ (n + 1) f u) :
    f y - ∑ k ∈ Finset.range (n + 1 + 1),
      (y - x) ^ k / (k ! : ℝ) * iteratedDeriv k f x =
      ∫ u in x..y, (y - u) ^ n / (n ! : ℝ) *
        (iteratedDeriv (n + 1) f u - iteratedDeriv (n + 1) f x) := by
  rcases eq_or_ne x y with rfl | hne
  · rw [Finset.sum_range_succ']
    simp
  have hcont : ContDiffOn ℝ (n + 1) f (uIcc x y) := fun u hu =>
    (hf u hu).contDiffWithinAt
  have hW : ∀ u ∈ uIcc x y,
      iteratedDerivWithin (n + 1) f (uIcc x y) u = iteratedDeriv (n + 1) f u := by
    intro u hu
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne) (hf u hu) hu
  have hD : ContinuousOn (iteratedDeriv (n + 1) f) (uIcc x y) := by
    exact (hcont.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_uIcc hne)).congr
      (fun u hu => (hW u hu).symm)
  have hI : IntervalIntegrable
      (fun u => (y - u) ^ n / (n ! : ℝ) * iteratedDeriv (n + 1) f u)
      MeasureTheory.volume x y :=
    (ContinuousOn.mul (by fun_prop) hD).intervalIntegrable
  have hC : IntervalIntegrable
      (fun u => (y - u) ^ n / (n ! : ℝ) * iteratedDeriv (n + 1) f x)
      MeasureTheory.volume x y := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hT := taylor_integral_remainder hcont
  rw [taylorWithinEval_eq_sum_of_contDiffAt hne
    ((hf x left_mem_uIcc).of_le (by exact_mod_cast Nat.le_succ n))] at hT
  have hT' : f y - ∑ k ∈ Finset.range (n + 1),
      (y - x) ^ k / (k ! : ℝ) * iteratedDeriv k f x =
      ∫ u in x..y, (y - u) ^ n / (n ! : ℝ) * iteratedDeriv (n + 1) f u := by
    rw [hT]
    exact intervalIntegral.integral_congr fun u hu => by rw [hW u hu, smul_eq_mul]
  rw [show (fun u => (y - u) ^ n / (n ! : ℝ) *
        (iteratedDeriv (n + 1) f u - iteratedDeriv (n + 1) f x)) =
      (fun u => (y - u) ^ n / (n ! : ℝ) * iteratedDeriv (n + 1) f u -
        (y - u) ^ n / (n ! : ℝ) * iteratedDeriv (n + 1) f x) from
      funext fun _ => mul_sub _ _ _, intervalIntegral.integral_sub hI hC,
    intervalIntegral.integral_mul_const, integral_taylor_kernel, ← hT',
    Finset.sum_range_succ]
  ring

/-- On an open convex set, an iterated derivative is Lipschitz precisely when the next
Fréchet derivative has bounded operator norm. The norm of the curried derivative equals the
multilinear operator norm by `norm_fderiv_iteratedFDeriv`. -/
theorem lipschitzOnWith_iteratedFDeriv_iff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} {p : ℕ} {L : ℝ≥0}
    (hs : IsOpen s) (hconv : Convex ℝ s) (hf : ContDiffOn ℝ (p + 1) f s) :
    LipschitzOnWith L (iteratedFDeriv ℝ p f) s ↔
      ∀ x ∈ s, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L := by
  constructor
  · intro hL x hx
    rw [← norm_fderiv_iteratedFDeriv]
    exact norm_fderiv_le_of_lipschitzOn ℝ (hs.mem_nhds hx) hL
  · intro hL
    apply hconv.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro x hx
      exact (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_self p)
    · intro x hx
      exact_mod_cast (norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := f) (x := x) (n := p)).trans_le
        (hL x hx)

/-- A multilinear operator norm bound is equivalent to its bound on tuples of unit vectors.
This is the mixed-vector characterization of the induced tensor norm. -/
theorem ContinuousMultilinearMap.opNorm_le_iff_unit_norm {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : ContinuousMultilinearMap ℝ (fun _ : ι => E) F} {L : ℝ} (hL : 0 ≤ L) :
    ‖A‖ ≤ L ↔ ∀ v : ι → E, (∀ i, ‖v i‖ = 1) → ‖A v‖ ≤ L := by
  constructor
  · intro h v hv
    simpa only [hv, Finset.prod_const_one, mul_one] using A.le_of_opNorm_le h v
  · intro h
    apply A.opNorm_le_bound hL
    intro v
    by_cases hz : ∃ i, v i = 0
    · obtain ⟨i, hi⟩ := hz
      rw [A.map_coord_zero i hi]
      simpa only [norm_zero] using mul_nonneg hL
        (Finset.prod_nonneg fun i _ => norm_nonneg (v i))
    have hn : ∀ i, ‖v i‖ ≠ 0 := fun i => norm_ne_zero_iff.mpr (by
      intro hi
      exact hz ⟨i, hi⟩)
    let u : ι → E := fun i => ‖v i‖⁻¹ • v i
    have hu : ∀ i, ‖u i‖ = 1 := by
      intro i
      simp [u, norm_smul, hn i]
    have hv : v = fun i => ‖v i‖ • u i := by
      funext i
      simp [u, smul_smul, hn i]
    have hscale : A v = (∏ i, ‖v i‖) • A u := by
      conv_lhs => rw [hv]
      exact A.map_smul_univ _ _
    rw [hscale, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg (v i)), mul_comm]
    exact mul_le_mul_of_nonneg_right (h u hu) (Finset.prod_nonneg fun i _ => norm_nonneg (v i))
