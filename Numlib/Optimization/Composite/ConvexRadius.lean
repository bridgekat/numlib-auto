import Numlib.Optimization.Composite.TaylorDecrease

/-!
# Unit-radius first-order composite certificates

Convexity of the outer function makes a scaled first-order generalized Taylor
decrement at least the scaled original decrement. Thus a normalized first-order
certificate at any radius in `(0,1]` gives the unit-radius certificate.
-/

namespace Composite
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Convexity of the outer function gives the exact scaled first-order
Taylor-decrement inequality, without differentiability of the outer function. -/
theorem mul_decrement_one_le_smul (f : E → ℝ) (c : E → F) {h : F → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (x d : E) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * decrement f c h 1 x d ≤ decrement f c h 1 x (t • d) := by
  have hh := hconv.2 (Set.mem_univ (c x)) (Set.mem_univ (c x + fderiv ℝ c x d))
    (show 0 ≤ 1 - t by linarith) ht (by ring : 1 - t + t = 1)
  have he : (1 - t) • c x + t • (c x + fderiv ℝ c x d) =
      c x + t • fderiv ℝ c x d := by module
  rw [he] at hh
  simp only [smul_eq_mul] at hh
  rw [decrement_eq, decrement_eq, taylorModel_one, taylorModel_one]
  simp only [map_smul, smul_eq_mul]
  linarith

/-- A positive-radius first-order normalized certificate for a convex outer
function already certifies the actual unit-radius criticality. -/
theorem criticality_one_unit_le_of_radius [ProperSpace E]
    (f : E → ℝ) (c : E → F) {h : F → ℝ} (hh : Continuous h)
    (hconv : ConvexOn ℝ Set.univ h) (x : E) {δ ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcrit : criticality f c h 1 x δ ≤ ε * δ) :
    criticality f c h 1 x 1 ≤ ε := by
  obtain ⟨d, hd, he⟩ := exists_decrement_eq_criticality f c hh 1 x zero_le_one
  rw [← he]
  change decrement f c h 1 x d ≤ ε
  apply (mul_le_mul_iff_right₀ hδ).mp
  have hnorm : ‖δ • d‖ ≤ δ := by
    rw [norm_smul, Real.norm_of_nonneg hδ.le]
    exact (mul_le_mul_of_nonneg_left hd hδ.le).trans_eq (mul_one δ)
  have hb := (mul_decrement_one_le_smul f c hconv x d hδ.le hδ1).trans
    ((decrement_le_criticality f c hh 1 x hnorm).trans hcrit)
  convert hb using 1
  ring

end Composite
