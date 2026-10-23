import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Numlib.Analysis.Calculus.ContDiff.Lipschitz

/-!
# Uniform Lipschitz constants from bounded scalar jets

For a finite-smoothness curve, bounded derivatives give Lipschitz estimates for
all preceding derivatives. A supplied Lipschitz estimate for the highest
actual scalar derivative completes the finite family, with one common constant.
The equivalent Fréchet derivative tensors satisfy exactly the same estimates.
-/

open Set

/-- Bounded finite jets and a Lipschitz highest derivative give one common
Lipschitz constant for every actual Fréchet derivative through the given order.
The curve may take values in any real normed space. -/
theorem norm_iteratedFDeriv_sub_le_of_bounded_jets
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {q : ℕ} {B L : ℝ} (hf : ContDiff ℝ q f) (hB : 0 ≤ B)
    (hjets : ∀ j ≤ q, ∀ x, ‖iteratedDeriv j f x‖ ≤ B)
    (hL : ∀ x y, ‖iteratedDeriv q f x - iteratedDeriv q f y‖ ≤ L * ‖x - y‖) :
    ∀ j ≤ q, ∀ x y,
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ max B L * ‖x - y‖ := by
  intro j hj x y
  by_cases heq : j = q
  · subst j
    rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub]
    exact (hL x y).trans (mul_le_mul_of_nonneg_right (le_max_right B L) (norm_nonneg _))
  · have hjq : j + 1 ≤ q := by omega
    let C : NNReal := ⟨max B L, hB.trans (le_max_left _ _)⟩
    have hcont : ContDiffOn ℝ (j + 1) f univ :=
      (hf.of_le (by exact_mod_cast hjq)).contDiffOn
    have hlip : LipschitzOnWith C (iteratedFDeriv ℝ j f) univ :=
      (lipschitzOnWith_iteratedFDeriv_iff_norm_le isOpen_univ (convex_univ : Convex ℝ (univ : Set ℝ)) hcont).2
        (fun z _ => by
          change ‖iteratedFDeriv ℝ (j + 1) f z‖ ≤ max B L
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
          exact (hjets (j + 1) hjq z).trans (le_max_left _ _))
    exact hlip.norm_sub_le (mem_univ x) (mem_univ y)
