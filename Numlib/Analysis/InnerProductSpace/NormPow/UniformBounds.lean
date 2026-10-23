import Numlib.Analysis.InnerProductSpace.NormPow.Smoothness

/-!
# Common finite bounds on all derivatives of a norm power

Homogeneity and compactness give one finite bound for every derivative through
order `p` of the power `p+1` on the unit ball, including at the origin.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every derivative through order `p` of the natural norm power `p+1` has a
common finite bound on the unit ball, including at its origin. -/
theorem exists_uniform_normPow_derivative_bound (p : ℕ) :
    ∃ P ≥ 0, ∀ n ≤ p, ∀ x : E, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ (p + 1)) x‖ ≤ P := by
  classical
  have hex := fun n => exists_norm_iteratedFDeriv_normRpow_le (E := E)
    ((p + 1 : ℕ) : ℝ) n
  choose C hC hbound using hex
  refine ⟨∑ n ∈ Finset.range (p + 1), C n, Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro n hn x hx
  have hCn : C n ≤ ∑ i ∈ Finset.range (p + 1), C i :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (by omega))
  apply le_trans _ hCn
  by_cases hx0 : x = 0
  · subst x
    have hnp : (n : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hn
    have hz := iteratedFDeriv_normRpow_zero_of_lt (E := E) hnp
    have hz' : iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ (p + 1)) 0 = 0 := by
      simpa only [Real.rpow_natCast] using hz
    rw [hz', norm_zero]
    exact hC n
  · have hb := hbound n x hx0
    have hpow : ‖x‖ ^ (((p + 1 : ℕ) : ℝ) - n) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) hx (sub_nonneg.mpr (by exact_mod_cast Nat.le_succ_of_le hn))
    have hc := mul_le_mul_of_nonneg_left hpow (hC n)
    simpa only [Real.rpow_natCast, mul_one] using hb.trans hc

