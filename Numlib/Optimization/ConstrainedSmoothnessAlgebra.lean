import Numlib.Optimization.ConstrainedRegularization

/-!
# Algebra of smooth objectives on a constraint set

Open extensions are preserved under finite affine combinations. The Lipschitz constants
for the highest derivatives combine using the absolute values of scalar coefficients.
-/

noncomputable section
namespace Optimization.ConstrainedRegularization

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {C : Set E} {p : ℕ} {L M : ℝ}

/-- Increasing a nonnegative highest-derivative bound preserves smoothness. -/
theorem SmoothOn.mono_constant (hf : SmoothOn f C p L) (hLM : L ≤ M) :
    SmoothOn f C p M where
  degree_pos := hf.degree_pos
  nonneg := hf.nonneg.trans hLM
  neighborhood := hf.neighborhood
  lipschitz x hx y hy := (hf.lipschitz x hx y hy).trans
    (mul_le_mul_of_nonneg_right hLM (norm_nonneg _))

/-- Constant functions have zero highest-derivative Lipschitz constant. -/
theorem smoothOn_const (hp : 1 ≤ p) (a : ℝ) : SmoothOn (fun _ : E => a) C p 0 where
  degree_pos := hp
  nonneg := le_rfl
  neighborhood := ⟨Set.univ, isOpen_univ, Set.subset_univ _, contDiffOn_const⟩
  lipschitz x _ y _ := by
    simp only [iteratedFDeriv_const_of_ne (by omega : p ≠ 0), Pi.zero_apply,
      sub_self, norm_zero, zero_mul, le_refl]

/-- The sum of two objectives has the sum of their derivative Lipschitz constants. -/
theorem SmoothOn.add (hf : SmoothOn f C p L) (hg : SmoothOn g C p M) :
    SmoothOn (fun x => f x + g x) C p (L + M) where
  degree_pos := hf.degree_pos
  nonneg := add_nonneg hf.nonneg hg.nonneg
  neighborhood := by
    obtain ⟨U, hU, hCU, hfU⟩ := hf.neighborhood
    obtain ⟨V, hV, hCV, hgV⟩ := hg.neighborhood
    exact ⟨U ∩ V, hU.inter hV, fun x hx => ⟨hCU hx, hCV hx⟩,
      (hfU.mono Set.inter_subset_left).add (hgV.mono Set.inter_subset_right)⟩
  lipschitz x hx y hy := by
    rw [fun_iteratedFDeriv_add_apply (hf.contDiffAt hx) (hg.contDiffAt hx),
      fun_iteratedFDeriv_add_apply (hf.contDiffAt hy) (hg.contDiffAt hy)]
    calc
      _ = ‖(iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y) +
          (iteratedFDeriv ℝ p g x - iteratedFDeriv ℝ p g y)‖ := by congr 1; abel
      _ ≤ ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ +
          ‖iteratedFDeriv ℝ p g x - iteratedFDeriv ℝ p g y‖ := norm_add_le _ _
      _ ≤ L * ‖x - y‖ + M * ‖x - y‖ := add_le_add
        (hf.lipschitz x hx y hy) (hg.lipschitz x hx y hy)
      _ = _ := by ring

/-- Scalar multiplication scales the derivative Lipschitz constant by its absolute value. -/
theorem SmoothOn.const_mul (hf : SmoothOn f C p L) (a : ℝ) :
    SmoothOn (fun x => a * f x) C p (|a| * L) where
  degree_pos := hf.degree_pos
  nonneg := mul_nonneg (abs_nonneg _) hf.nonneg
  neighborhood := by
    obtain ⟨U, hU, hCU, hfU⟩ := hf.neighborhood
    exact ⟨U, hU, hCU, contDiffOn_const.mul hfU⟩
  lipschitz x hx y hy := by
    simp only [← smul_eq_mul,
      iteratedFDeriv_const_smul_apply' (hf.contDiffAt hx),
      iteratedFDeriv_const_smul_apply' (hf.contDiffAt hy), ← smul_sub, norm_smul,
      Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hf.lipschitz x hx y hy) (abs_nonneg a)).trans_eq
      (by ring)

/-- Adding a constant leaves the derivative Lipschitz bound unchanged. -/
theorem SmoothOn.add_const (hf : SmoothOn f C p L) (a : ℝ) :
    SmoothOn (fun x => f x + a) C p L := by
  simpa only [add_zero] using hf.add (smoothOn_const hf.degree_pos a)

end Optimization.ConstrainedRegularization
