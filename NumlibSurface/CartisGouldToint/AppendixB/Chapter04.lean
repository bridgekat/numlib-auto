import Numlib.Analysis.InnerProductSpace.NormPow.FiniteBounds
import Numlib.Analysis.InnerProductSpace.NormPow.Diagonal
import Numlib.Analysis.SpecialFunctions.FiniteFactorial.Falling
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Corrected norm estimates for Appendix B.4

The exact operator-norm expression (B.4.3) fails for fractional exponents.
A positive constant, fixed before every point and derivative order, gives the
valid homogeneous upper bound. The lower derivative jets include the origin.
The full correction also retains the exact radial formula and the convexity
clauses throughout their valid finite derivative-order range.
-/

namespace CartisGouldToint

/-- **Norm-bound correction of Lemma B.4.1.** Replace the false fractional
operator-norm equality by a uniform homogeneous upper bound. Its constant may
depend on the fixed dimension, p and beta, but precedes every point and order.
Global finite smoothness and all lower zero-origin jets are derived as well. -/
theorem lemma_B_4_1_norm_bound_corrected {n p : ℕ} {β : ℝ}
    (hβ : 0 < β) (_hβ1 : β ≤ 1) :
    ContDiff ℝ p (fun s : EuclideanSpace ℝ (Fin n) => ‖s‖ ^ ((p : ℝ) + β)) ∧
    (∀ j ≤ p, iteratedFDeriv ℝ j
      (fun s : EuclideanSpace ℝ (Fin n) => ‖s‖ ^ ((p : ℝ) + β)) 0 = 0) ∧
    ∃ K > 0,
      (∀ j ≤ p, ∀ s : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ j (fun z => ‖z‖ ^ ((p : ℝ) + β)) s‖ ≤
          K * ‖s‖ ^ ((p : ℝ) + β - j)) ∧
      (∀ s : EuclideanSpace ℝ (Fin n), s ≠ 0 →
        ‖iteratedFDeriv ℝ (p + 1) (fun z => ‖z‖ ^ ((p : ℝ) + β)) s‖ ≤
          K * ‖s‖ ^ (β - 1)) := by
  have hp : (p : ℝ) < (p : ℝ) + β := by linarith
  obtain ⟨K, hK, hlo, hhi⟩ := exists_global_normRpow_derivative_bound
    (E := EuclideanSpace ℝ (Fin n)) hp
  refine ⟨contDiff_normRpow_of_nat_lt hp, ?_, K, hK, hlo, ?_⟩
  · intro j hj
    exact iteratedFDeriv_normRpow_zero_of_lt
      ((show (j : ℝ) ≤ p by exact_mod_cast hj).trans_lt hp)
  · intro s hs
    simpa only [show (p : ℝ) + β - ((p : ℝ) + 1) = β - 1 by ring] using hhi s hs

/-- **Corrected Lemma B.4.1.** The false exact operator-norm claims are replaced
by uniform homogeneous upper bounds. The exact shifted-factorial radial
formula is retained, as are orthogonal and even radial convexity. The latter
hold through order p+1 off the origin, and through order p everywhere.
Unrestricted higher-order convexity is not asserted. -/
theorem lemma_B_4_1_corrected {n p : ℕ} {β : ℝ}
    (hβ : 0 < β) (_hβ1 : β ≤ 1) :
    ContDiff ℝ p (fun s : EuclideanSpace ℝ (Fin n) => ‖s‖ ^ ((p : ℝ) + β)) ∧
    (∀ j ≤ p, iteratedFDeriv ℝ j
      (fun s : EuclideanSpace ℝ (Fin n) => ‖s‖ ^ ((p : ℝ) + β)) 0 = 0) ∧
    (∃ K > 0, ∀ j ≤ p + 1, ∀ s : EuclideanSpace ℝ (Fin n),
      s ≠ 0 ∨ j ≤ p →
      ‖iteratedFDeriv ℝ j (fun z => ‖z‖ ^ ((p : ℝ) + β)) s‖ ≤
        K * ‖s‖ ^ ((p : ℝ) + β - j)) ∧
    (∀ j ≤ p, ∀ s : EuclideanSpace ℝ (Fin n),
      iteratedFDeriv ℝ j (fun z => ‖z‖ ^ ((p : ℝ) + β)) s (fun _ => s) =
        Real.shiftedFactorial p β / Real.shiftedFactorial (p - j) β *
          ‖s‖ ^ ((p : ℝ) + β)) ∧
    (∀ j ≤ p, ∀ s : EuclideanSpace ℝ (Fin n),
      ConvexOn ℝ {d | inner ℝ s d = 0}
        (fun d => iteratedFDeriv ℝ j (fun z => ‖z‖ ^ ((p : ℝ) + β)) s (fun _ => d)) ∧
      (Even j → ConvexOn ℝ (Submodule.span ℝ {s} : Set (EuclideanSpace ℝ (Fin n)))
        (fun d => iteratedFDeriv ℝ j (fun z => ‖z‖ ^ ((p : ℝ) + β)) s
          (fun _ => d)))) ∧
    (∀ j ≤ p + 1, ∀ s : EuclideanSpace ℝ (Fin n), s ≠ 0 →
      ConvexOn ℝ {d | inner ℝ s d = 0}
        (fun d => iteratedFDeriv ℝ j (fun z => ‖z‖ ^ ((p : ℝ) + β)) s (fun _ => d)) ∧
      (Even j → ConvexOn ℝ (Submodule.span ℝ {s} : Set (EuclideanSpace ℝ (Fin n)))
        (fun d => iteratedFDeriv ℝ j (fun z => ‖z‖ ^ ((p : ℝ) + β)) s
          (fun _ => d)))) := by
  have hp : (p : ℝ) < (p : ℝ) + β := by linarith
  have hzero (j : ℕ) (hj : j ≤ p) : iteratedFDeriv ℝ j
      (fun s : EuclideanSpace ℝ (Fin n) => ‖s‖ ^ ((p : ℝ) + β)) 0 = 0 :=
    iteratedFDeriv_normRpow_zero_of_lt
      ((show (j : ℝ) ≤ p by exact_mod_cast hj).trans_lt hp)
  have hconv (j : ℕ) (hj : j ≤ p + 1) (s : EuclideanSpace ℝ (Fin n)) (hs : s ≠ 0) :
      ConvexOn ℝ {d | inner ℝ s d = 0}
        (fun d => iteratedFDeriv ℝ j (fun z => ‖z‖ ^ ((p : ℝ) + β)) s (fun _ => d)) ∧
      (Even j → ConvexOn ℝ (Submodule.span ℝ {s} : Set (EuclideanSpace ℝ (Fin n)))
        (fun d => iteratedFDeriv ℝ j (fun z => ‖z‖ ^ ((p : ℝ) + β)) s
          (fun _ => d))) := by
    have he : (j : ℝ) - 1 < (p : ℝ) + β := by
      have hh : (j : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hj
      linarith
    exact ⟨convexOn_iteratedFDeriv_normRpow_perp _ _ he hs,
      fun h => convexOn_iteratedFDeriv_normRpow_span_even _ _ h he hs⟩
  refine ⟨contDiff_normRpow_of_nat_lt hp, hzero, ?_, ?_, ?_, hconv⟩
  · obtain ⟨K, hK, hbound⟩ := exists_common_normRpow_derivative_bound
      (E := EuclideanSpace ℝ (Fin n)) ((p : ℝ) + β) (p + 1)
    refine ⟨K, hK, fun j hj s hs => ?_⟩
    by_cases hs0 : s = 0
    · subst s
      rw [hzero j (hs.resolve_left (not_ne_iff.mpr rfl)), norm_zero]
      positivity
    · exact hbound j hj s hs0
  · intro j hj s
    by_cases hs : s = 0
    · subst s
      rw [hzero j hj]
      simp [Real.zero_rpow (ne_of_gt (lt_of_le_of_lt (Nat.cast_nonneg p) hp))]
    · rw [iteratedFDeriv_normRpow_apply_radial _ _ hs,
        Real.prod_falling_eq_shiftedFactorial_div hj hβ.le]
  · intro j hj s
    by_cases hs : s = 0
    · subst s
      simp only [hzero j hj, zero_apply]
      exact ⟨convexOn_const _
          ((innerSL ℝ (0 : EuclideanSpace ℝ (Fin n))).toLinearMap.ker.convex),
        fun _ => convexOn_const _ (Submodule.span ℝ {0}).convex⟩
    · exact hconv j (hj.trans (Nat.le_succ p)) s hs

end CartisGouldToint
