import Numlib.Analysis.InnerProductSpace.NormPow.Smoothness

/-!
# Lipschitz highest derivatives of natural norm powers

The actual order-`n` derivative of the norm power `n+1` has linear growth and a
bounded derivative off the origin. A ball avoiding the origin gives a mean-value
bound; near the origin its actual growth bound gives the global estimate.
-/

open Metric Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual order-`n` derivative of the natural norm power `n+1` is
globally Lipschitz, including at the origin. The constant is independent of
points or optimization accuracies. -/
theorem exists_lipschitz_iteratedFDeriv_normPow (n : ℕ) :
    ∃ L ≥ 0, ∀ x y : E,
      ‖iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ (n + 1)) x -
        iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ (n + 1)) y‖ ≤ L * ‖x - y‖ := by
  let lam : ℝ := (n + 1 : ℕ)
  let f : E → ℝ := fun z => ‖z‖ ^ lam
  obtain ⟨B, hB, hBg⟩ := exists_norm_iteratedFDeriv_normRpow_le (E := E) lam n
  obtain ⟨C, hC, hCg⟩ := exists_norm_iteratedFDeriv_normRpow_le (E := E) lam (n + 1)
  have hzero : iteratedFDeriv ℝ n f 0 = 0 :=
    iteratedFDeriv_normRpow_zero_of_lt (by dsimp [lam]; push_cast; linarith)
  have hg : ∀ x : E, ‖iteratedFDeriv ℝ n f x‖ ≤ B * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp only [hzero, norm_zero, mul_zero, le_refl]
    · have hb := hBg x hx
      have he : lam - n = 1 := by dsimp [lam]; push_cast; ring
      simpa only [he, Real.rpow_one] using hb
  have hdiff : ∀ x : E, x ≠ 0 → DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x := by
    intro x hx
    exact ((contDiffOn_normRpow lam (n + 1)).contDiffAt
      (isOpen_compl_singleton.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_self n)
  have hbound : ∀ x : E, x ≠ 0 → ‖fderiv ℝ (iteratedFDeriv ℝ n f) x‖ ≤ C := by
    intro x hx
    rw [norm_fderiv_iteratedFDeriv]
    have hb := hCg x hx
    have he : lam - (n + 1 : ℕ) = 0 := sub_self _
    simpa only [he, Real.rpow_zero, mul_one] using hb
  refine ⟨max (5 * B) C, le_trans (by positivity) (le_max_left _ _), ?_⟩
  intro x y
  have h := norm_sub_le_of_growth_and_fderiv_bound hB hg hdiff hbound x y
  simpa only [f, lam, Real.rpow_natCast] using h
