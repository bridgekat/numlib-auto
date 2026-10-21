import Numlib.Nonlinear.ScalarNewton
import Numlib.Analysis.SpecialFunctions.Pow.Secant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Newton corrections for power-transformed equations

At a positive value of a decreasing differentiable function, the actual Newton correction
for its power-transformed positive target equation decreases as the nonzero exponent grows.
-/

namespace Newton

/-- The actual Newton increment for a nonzero power transform, with positive function
value and target. Its derivative is the actual derivative, not a supplied oracle. -/
theorem power_scalarStep_sub {f : ℝ → ℝ} {x a β : ℝ} (hf : DifferentiableAt ℝ f x)
    (hfx : 0 < f x) (ha : 0 < a) (hβ : β ≠ 0) (hdf : deriv f x ≠ 0) :
    scalarStep (fun t => f t ^ β - a ^ β)
      (deriv (fun t => f t ^ β - a ^ β)) x - x =
      (-f x / deriv f x) * ((1 - (a / f x) ^ β) / β) := by
  have hd := ((hf.hasDerivAt.rpow_const (p := β) (Or.inl hfx.ne')).sub_const (a ^ β)).deriv
  have hr : f x ^ (β - 1) = f x ^ β / f x := by
    rw [Real.rpow_sub hfx, Real.rpow_one]
  have hq := Real.div_rpow ha.le hfx.le β
  have hp : f x ^ β ≠ 0 := (Real.rpow_pos_of_pos hfx β).ne'
  simp only [scalarStep, hd, hr, hq]
  field_simp [hβ, hdf, hfx.ne', hp]
  ring

/-- Actual power-transformed Newton corrections are antitone in the nonzero exponent
when the original function is positive and has strictly negative derivative. -/
theorem antitoneOn_power_scalarStep_sub {f : ℝ → ℝ} {x a : ℝ}
    (hf : DifferentiableAt ℝ f x) (hfx : 0 < f x) (ha : 0 < a)
    (hdf : deriv f x < 0) :
    AntitoneOn (fun β : ℝ => scalarStep (fun t => f t ^ β - a ^ β)
      (deriv (fun t => f t ^ β - a ^ β)) x - x) ({0}ᶜ : Set ℝ) := by
  intro b hb c hc hbc
  change scalarStep (fun t => f t ^ c - a ^ c)
    (deriv (fun t => f t ^ c - a ^ c)) x - x ≤
    scalarStep (fun t => f t ^ b - a ^ b) (deriv (fun t => f t ^ b - a ^ b)) x - x
  rw [power_scalarStep_sub hf hfx ha (by simpa using hc) hdf.ne,
    power_scalarStep_sub hf hfx ha (by simpa using hb) hdf.ne]
  exact mul_le_mul_of_nonneg_left
    (Real.antitoneOn_one_sub_rpow_div (div_pos ha hfx) hb hc hbc)
    (div_nonneg_of_nonpos (neg_nonpos.mpr hfx.le) hdf.le)

end Newton
