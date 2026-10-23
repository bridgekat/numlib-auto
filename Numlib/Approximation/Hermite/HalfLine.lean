import Numlib.Approximation.Hermite.Global
import Numlib.Analysis.Calculus.ContDiff.Piecewise
import Numlib.Analysis.Calculus.IteratedDeriv.Bounded

/-!
# Bounded smooth extension of a real half-line tail

A genuine finite Hermite interpolant matches every prescribed endpoint jet.
Gluing its bounded global extension to the given tail preserves finite smoothness
and the Lipschitz highest derivative, with global bounds on all lower derivatives.
-/

open Set
namespace Hermite

/-- A globally smooth tail whose jets are bounded on a closed right half-line and whose
highest derivative is Lipschitz there admits a bounded global extension agreeing with
all actual tail jets. The proof constructs an actual Hermite interpolant and glues
matching endpoint derivatives. -/
theorem exists_bounded_extension {f : ℝ → ℝ} {p : ℕ} (hf : ContDiff ℝ p f)
    (c C : ℝ) (hC : 1 ≤ C)
    (hb : ∀ j, j ≤ p → ∀ x, c ≤ x → |iteratedDeriv j f x| ≤ C)
    (hLip : LipschitzOnWith ⟨C, by linarith⟩ (iteratedDeriv p f) (Ici c)) :
    ∃ g : ℝ → ℝ, ∃ (L : ℝ) (hL : 0 < L), ∃ B > 0, ContDiff ℝ p g ∧
      LipschitzWith ⟨L, hL.le⟩ (iteratedDeriv p g) ∧
      (∀ j, j ≤ p → ∀ x, |iteratedDeriv j g x| ≤ B) ∧
      (∀ j, j ≤ p → ∀ x, c ≤ x → iteratedDeriv j g x = iteratedDeriv j f x) := by
  classical
  obtain ⟨L, hL, B, hB, hex⟩ := exists_uniform_interpolant p C (by linarith)
  let x : ℕ → ℝ := fun k => c - 1 + k
  let a : ℕ → ℕ → ℝ := fun k j => if k = 0 then 0 else iteratedDeriv j f c
  have hinc : ∀ i j, i < j → j ≤ 1 → x i < x j := by
    intro i j hij hj
    have hi : i = 0 := by omega
    have hj1 : j = 1 := by omega
    subst i; subst j
    dsimp [x]
    norm_num
  have hP : initialPolynomial p (a 0) = 0 := by
    simp [initialPolynomial, a, jetPoly]
  have hres : ∀ k < 1, ∀ j ≤ p,
      |a (k + 1) j - (Polynomial.derivative^[j] (initialPolynomial p (a k))).eval
        (x (k + 1) - x k)| ≤ C * (x (k + 1) - x k) ^ (p - j + 1) := by
    intro k hk j hj
    obtain rfl : k = 0 := by omega
    simp only [hP, Polynomial.iterate_derivative_zero, Polynomial.eval_zero, sub_zero]
    simp only [a, x, Nat.cast_zero, Nat.reduceEqDiff, reduceIte]
    norm_num only [add_zero, add_sub_cancel_left, one_pow, mul_one]
    exact hb j hj c le_rfl
  obtain ⟨v, hv, hLv, hjet, hbv⟩ := hex 1 (by omega) x a hinc hres
  have hbound : ∀ j, j ≤ p → ∀ t, |iteratedDeriv j v t| ≤ B := hbv ⟨by
    intro k hk j hj
    obtain rfl : k = 0 := by omega
    simpa only [a, reduceIte, abs_zero] using (show 0 ≤ C by linarith), by
    intro k hk
    obtain rfl : k = 0 := by omega
    simpa only [x, Nat.reduceAdd, Nat.cast_one, Nat.cast_zero, add_zero,
      add_sub_cancel_left] using hC⟩
  have hjoin : ∀ j ≤ p, iteratedDeriv j v c = iteratedDeriv j f c := by
    intro j hj
    have hh := hjet 1 le_rfl j hj
    simpa [x, a] using hh
  let g := (Iic c).piecewise v f
  have hg : ContDiff ℝ p g := contDiff_piecewise_Iic hv hf hjoin
  let M := max L C
  have hM : 0 < M := hL.trans_le (le_max_left _ _)
  have hD : iteratedDeriv p g = (Iic c).piecewise (iteratedDeriv p v)
      (iteratedDeriv p f) := iteratedDeriv_piecewise_Iic hv hf hjoin le_rfl
  have hLg : LipschitzWith ⟨M, hM.le⟩ (iteratedDeriv p g) := by
    rw [hD]
    apply lipschitzOnWith_univ.mp
    apply LipschitzOnWith.piecewise_Iic _ _ (mem_univ c) (hjoin p le_rfl)
    · apply (lipschitzOnWith_iff_norm_sub_le).mpr
      intro u hu w hw
      exact (hLv.norm_sub_le u w).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · apply (lipschitzOnWith_iff_norm_sub_le).mpr
      intro u hu w hw
      exact (hLip.norm_sub_le hu.2 hw.2).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  refine ⟨g, M, hM, max B C, hB.trans_le (le_max_left _ _), hg, hLg, ?_, ?_⟩
  · intro j hj t
    rw [show iteratedDeriv j g = (Iic c).piecewise (iteratedDeriv j v)
      (iteratedDeriv j f) from iteratedDeriv_piecewise_Iic hv hf hjoin hj]
    by_cases ht : t ≤ c
    · rw [piecewise_eq_of_mem (Iic c) _ _ ht]
      exact (hbound j hj t).trans (le_max_left _ _)
    · rw [piecewise_eq_of_notMem (Iic c) _ _ ht]
      exact (hb j hj t (le_of_not_ge ht)).trans (le_max_right _ _)
  · intro j hj t ht
    rw [show iteratedDeriv j g = (Iic c).piecewise (iteratedDeriv j v)
      (iteratedDeriv j f) from iteratedDeriv_piecewise_Iic hv hf hjoin hj]
    by_cases he : t ≤ c
    · have heq : t = c := le_antisymm he ht
      subst t
      simpa only [piecewise_eq_of_mem (Iic c) _ _ (le_refl c)] using hjoin j hj
    · exact piecewise_eq_of_notMem (Iic c) _ _ he

/-- A bounded extension of a right half-line tail has uniform global operator Lipschitz
bounds in every derivative order through its finite smoothness order, as well as a
global objective bound. All actual tail jets are preserved. -/
theorem exists_bounded_extension_tensor {f : ℝ → ℝ} {p : ℕ} (hf : ContDiff ℝ p f)
    (c C : ℝ) (hC : 1 ≤ C)
    (hb : ∀ j, j ≤ p → ∀ x, c ≤ x → |iteratedDeriv j f x| ≤ C)
    (hLip : LipschitzOnWith ⟨C, by linarith⟩ (iteratedDeriv p f) (Ici c)) :
    ∃ g : ℝ → ℝ, ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧ ContDiff ℝ p g ∧
      (∀ x, |g x| ≤ B) ∧
      (∀ j, j ≤ p → ∀ x y,
        ‖iteratedFDeriv ℝ j g x - iteratedFDeriv ℝ j g y‖ ≤ L * ‖x - y‖) ∧
      (∀ j, j ≤ p → ∀ x, c ≤ x → iteratedDeriv j g x = iteratedDeriv j f x) := by
  obtain ⟨g, L, hL, B, hB, hg, hLg, hbound, heq⟩ := exists_bounded_extension hf c C hC hb hLip
  refine ⟨g, max 1 (max B L), B, le_max_left _ _, hB, hg, ?_, ?_, heq⟩
  · intro x
    simpa only [iteratedDeriv_zero] using hbound 0 (Nat.zero_le _) x
  · intro j hj x y
    exact (norm_iteratedFDeriv_sub_le_of_bounded_jets hg hB.le
      (fun a ha z => by simpa only [Real.norm_eq_abs] using hbound a ha z)
      hLg.norm_sub_le j hj x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end Hermite
