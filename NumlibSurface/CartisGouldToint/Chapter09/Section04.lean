import Numlib.Optimization.BallValueCertificates
import NumlibSurface.CartisGouldToint.Chapter09.Section03

/-!
# Chapter 9, Section 4: trust-region value certificates

Actual minimizers on larger and smaller weighted balls supply value bounds. Boundary
points rescale to feasible trial steps, including when the quadratic model is indefinite.
-/

open scoped InnerProductSpace
open CartisGouldToint.Chapter08.Section01
namespace CartisGouldToint.Chapter09.Section04
variable {n : ℕ} {g s t : EuclideanSpace ℝ (Fin n)}
  {H M : Matrix (Fin n) (Fin n) ℝ}

/-- The source weighted norm is the norm in the existing energy space. -/
theorem weightedNorm_eq_norm_toEnergy (hM : M.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    weightedNorm M x = ‖hM.isPreconditioner_toEuclideanLin.toEnergy x‖ := by
  rw [WithEnergy.norm_equiv, weightedNorm_eq_energyNorm]

/-- Radial scaling of a weighted boundary point gives exactly the target radius. -/
theorem weightedNorm_rescale_boundary (hM : M.PosDef) {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 < ε) (ht : weightedNorm M t = ε) :
    weightedNorm M ((δ / ε) • t) = δ := by
  simp only [weightedNorm_eq_norm_toEnergy hM, map_smul] at ht ⊢
  exact Optimization.norm_rescale_boundary hδ hε ht

/-- Increasing the trust-region radius decreases its attained minimum value, the valid
forward implication in (9.4.5). -/
theorem trustRegion_value_antitone {δ ε : ℝ}
    (hs : trustRegionMinimizer g H M δ s) (ht : trustRegionMinimizer g H M ε t)
    (hδε : δ ≤ ε) : quadraticModel g H t ≤ quadraticModel g H s :=
  ht.2 (hs.1.trans hδε)

/-- A boundary minimizer on any positive-radius ball gives a feasible rescaled trial value. -/
theorem trustRegion_value_le_rescale (hM : M.PosDef) {δ ε : ℝ}
    (hs : trustRegionMinimizer g H M δ s) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (ht : weightedNorm M t = ε) :
    quadraticModel g H s ≤ quadraticModel g H ((δ / ε) • t) :=
  hs.2 (le_of_eq (weightedNorm_rescale_boundary hM hδ hε ht))

/-- The boundary multiplier bounds (9.4.1), with nonnegativity included in the lower
bracket. The multiplier comes from the complete optimality theorem; the separate interior
clause identifies the zero multiplier without assuming a positive definite shift. -/
theorem trustRegionMultiplierBracket (hH : H.IsSymm) (hM : M.PosDef) {δ a b : ℝ}
    (hδ : 0 < δ) (hs : trustRegionMinimizer g H M δ s)
    (hlo : ∀ i, a ≤ CartisGouldToint.Chapter08.Section02.secularEigenvalues hH hM i)
    (hup : ∀ i, CartisGouldToint.Chapter08.Section02.secularEigenvalues hH hM i ≤ b) :
    ∃ t : ℝ, 0 ≤ t ∧ Matrix.toEuclideanLin (H + t • M) s = -g ∧
      (H + t • M).PosSemidef ∧
      (weightedNorm M s = δ →
        max 0 (weightedNorm M⁻¹ g / δ - b) ≤ t ∧ t ≤ weightedNorm M⁻¹ g / δ - a) ∧
      (weightedNorm M s < δ → t = 0) := by
  obtain ⟨_, t, ht, hstat, hp, hc⟩ :=
    (CartisGouldToint.Chapter08.Section02.theorem_8_2_7 hH hM hδ).1.mp hs
  refine ⟨t, ht, hstat, hp, ?_, ?_⟩
  · intro hboundary
    have hh := Section03.stationary_weightedNorm_bounds hH hM hstat hp hlo hup
    rw [hboundary] at hh
    have hleft : weightedNorm M⁻¹ g / δ ≤ t + b := (div_le_iff₀ hδ).mpr hh.2
    have hright : t + a ≤ weightedNorm M⁻¹ g / δ := (le_div_iff₀ hδ).mpr hh.1
    exact ⟨max_le ht (by linarith), by linarith⟩
  · intro hinterior
    have hn : 0 ≤ weightedNorm M s := Real.sqrt_nonneg _
    have hsq : weightedNorm M s ^ 2 - δ ^ 2 < 0 := by nlinarith
    exact (mul_eq_zero.mp hc).resolve_right (ne_of_lt hsq)

/-- The two-sided larger-ball value certificate (9.4.6), the smaller-ball certificate
(9.4.7), and their stopping implications (9.4.3)–(9.4.4). Values are the actual objective
at the supplied global minimizers, with no assumed minimum-value oracle. -/
theorem trustRegionValueCertificates (hM : M.PosDef) {δ δplus δminus : ℝ}
    {splus sminus : EuclideanSpace ℝ (Fin n)}
    (hδ : 0 ≤ δ) (hminus : 0 < δminus) (hsmall : δminus ≤ δ) (hlarge : δ < δplus)
    (hs : trustRegionMinimizer g H M δ s)
    (hplus : trustRegionMinimizer g H M δplus splus)
    (hminusMin : trustRegionMinimizer g H M δminus sminus)
    (hplusBoundary : weightedNorm M splus = δplus)
    (hminusBoundary : weightedNorm M sminus = δminus) :
    (quadraticModel g H splus ≤ quadraticModel g H s ∧
      quadraticModel g H s ≤ quadraticModel g H ((δ / δplus) • splus)) ∧
    quadraticModel g H s ≤ min (quadraticModel g H ((δ / δminus) • sminus))
      (quadraticModel g H sminus) ∧
    (∀ L, quadraticModel g H ((δ / δplus) • splus) ≤ L → quadraticModel g H s ≤ L) ∧
    (∀ U, U ≤ quadraticModel g H splus → U ≤ quadraticModel g H s) ∧
    (∀ L, min (quadraticModel g H ((δ / δminus) • sminus))
      (quadraticModel g H sminus) ≤ L → quadraticModel g H s ≤ L) := by
  have hlow := trustRegion_value_antitone hs hplus hlarge.le
  have hupp := trustRegion_value_le_rescale hM hs hδ (hδ.trans_lt hlarge) hplusBoundary
  have hsmallBound := le_min
    (trustRegion_value_le_rescale hM hs hδ hminus hminusBoundary)
    (trustRegion_value_antitone hminusMin hs hsmall)
  exact ⟨⟨hlow, hupp⟩, hsmallBound, fun _ h => hupp.trans h,
    fun _ h => h.trans hlow, fun _ h => hsmallBound.trans h⟩

end CartisGouldToint.Chapter09.Section04
