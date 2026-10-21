import Numlib.Optimization.SteepestDescentValleyProfiles

/-!
# Actual scalar and strip components of the SDEX construction

The explicit quintic has the boundary conditions in (B.2.20), and the symmetric profile
has all five branches in (B.2.19). The derivative bound here concerns the independent width
and outward-strip parameters. `FiniteValley` and `FiniteValleySmooth` supply the finite
chain, its scalar interpolants and tails, and the trajectory and local ray-minimum
arguments. The parent `Chapter02` module gives the complete finite source statements.
-/

noncomputable section

open Set Optimization.SteepestDescentValley

namespace CartisGouldToint.AppendixB.Chapter02

/-- The lower-strip polynomial satisfies exactly the boundary data in (B.2.20). -/
theorem lower_strip_boundary_conditions (d : ℝ) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (fun q => strip d (1 - q)) 0 = (if j = 0 then 8 * d ^ 2 else 0) ∧
      iteratedDeriv j (fun q => strip d (1 - q)) 1 =
        (if j = 0 then d ^ 2 / 4 else if j = 1 then -d else 2) :=
  lower_strip_endpoint_jets d hj

/-- The five branches in (B.2.19) hold for the actual symmetric width-dependent profile. -/
theorem valley_profile_branches {d z : ℝ} (hd : 0 ≤ d) :
    (z ≤ -d / 2 - 1 → profile d z = 8 * d ^ 2) ∧
    (-z - d / 2 ∈ Icc (0 : ℝ) 1 → profile d z = strip d (-z - d / 2)) ∧
    (-d / 2 ≤ z → z ≤ d / 2 → profile d z = z ^ 2) ∧
    (z - d / 2 ∈ Icc (0 : ℝ) 1 → profile d z = strip d (z - d / 2)) ∧
    (d / 2 + 1 ≤ z → profile d z = 8 * d ^ 2) := by
  exact ⟨fun hz => profile_lower_plateau hd (by linarith), profile_lower_strip hd,
    fun hl hu => profile_core hl hu, profile_upper_strip hd,
    fun hz => profile_upper_plateau hd (by linarith)⟩

/-- Actual parameter derivatives of the strip have one uniform bound through order two.
Composing with the actual width and midpoint still requires their separate derivative bounds. -/
theorem strip_parameter_derivatives_bounded :
    ∃ C > 0, ∀ j ≤ 2, ∀ p ∈ (Icc (0 : ℝ) 2) ×ˢ (Icc (0 : ℝ) 1),
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => strip p.1 p.2) p‖ ≤ C :=
  exists_strip_derivative_bound

end CartisGouldToint.AppendixB.Chapter02
