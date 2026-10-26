import Numlib.Optimization.Constrained.TargetResidual

/-!
# Cartis–Gould–Toint, Appendix B: Appendix to Chapter 7

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Appendix B, "Appendix to
Chapter 7": Lemma B.7.1, the two-variable global minimization used for the target decrease
(7.2.30) in the proof of Lemma 7.2.3.

The inequality behind the lemma is the backbone `neg_add_sqrt_sq_sub_sq_ge`, which also covers
the boundary cases `ω = 0` and `ω = ε` needed in the proof of Lemma 7.2.3 (where `ω ∈ [0, ε₀]`);
the lemma as printed assumes `0 < ω < ε`. The book's KKT-based proof is replaced by an elementary
monotonicity argument.
-/

namespace CartisGouldToint.AppendixB

/-- The objective `ψ(f, c) = -f + √(ε² - c²)` of (B.7.1). -/
noncomputable def psiB71 (ε : ℝ) (p : ℝ × ℝ) : ℝ := -p.1 + √(ε ^ 2 - p.2 ^ 2)

/-- If `0 ≤ ω < ε`, `u² + v² ≤ ω²` and `-u + √(ε² - v²) = ε - ω`, then `(u, v) = (ω, 0)`: the
minimum of (B.7.1) is attained only at `(ω, 0)`. -/
theorem eq_of_neg_add_sqrt_sq_sub_sq_eq {ω ε u v : ℝ} (hω : 0 ≤ ω) (hωε : ω < ε)
    (huv : u ^ 2 + v ^ 2 ≤ ω ^ 2) (heq : -u + √(ε ^ 2 - v ^ 2) = ε - ω) : u = ω ∧ v = 0 := by
  set A := √(ε ^ 2 - v ^ 2) with hA
  set B := √(ω ^ 2 - v ^ 2) with hB
  have hvω : v ^ 2 ≤ ω ^ 2 := by nlinarith
  have hA2 : A ^ 2 = ε ^ 2 - v ^ 2 := Real.sq_sqrt (by nlinarith)
  have hB2 : B ^ 2 = ω ^ 2 - v ^ 2 := Real.sq_sqrt (by linarith)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBω : B ≤ ω := by
    rw [hB, Real.sqrt_le_left hω]
    nlinarith
  have huB : u ≤ B := (le_abs_self u).trans (Real.abs_le_sqrt (by linarith))
  -- `A - B ≤ ε - ω` and `(A - B)(A + B) = (ε - ω)(ε + ω)` force `A + B ≥ ε + ω`, hence `A ≥ ε`.
  have hAB : A - B ≤ ε - ω := by linarith
  have hprod : (A - B) * (A + B) = (ε - ω) * (ε + ω) := by nlinarith
  have hApos : B < A := by nlinarith
  have hsum : ε + ω ≤ A + B := by
    by_contra hlt
    push Not at hlt
    have : (A - B) * (A + B) < (ε - ω) * (ε + ω) :=
      mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hAB hlt (by linarith) (by linarith)
    linarith
  have hεA : ε ≤ A := by linarith
  have hv : v = 0 := by nlinarith
  subst hv
  have hBeq : B = ω := by rw [hB]; simp [Real.sqrt_sq hω]
  have hAeq : A = ε := by rw [hA]; simp [Real.sqrt_sq (hω.trans hωε.le)]
  exact ⟨by linarith, rfl⟩

/-- **Lemma B.7.1** of [cartis2022evaluation]. For `0 < ω < ε`, the global minimum of
`ψ(f, c) = -f + √(ε² - c²)` over the disc `f² + c² ≤ ω²` (B.7.1) is attained at `(ω, 0)`, with
value `ψ(ω, 0) = ε - ω`; moreover `(ω, 0)` is the only minimizer. -/
theorem lemma_B_7_1 {ω ε : ℝ} (hω : 0 < ω) (hωε : ω < ε) :
    let K : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ ω ^ 2}
    (ω, 0) ∈ K ∧ IsMinOn (psiB71 ε) K (ω, 0) ∧ psiB71 ε (ω, 0) = ε - ω ∧
      ∀ p ∈ K, psiB71 ε p = ε - ω → p = (ω, 0) := by
  intro K
  have hval : psiB71 ε (ω, 0) = ε - ω :=
    neg_add_sqrt_sq_sub_zero_sq (hω.le.trans hωε.le)
  refine ⟨by simp [K], fun p hp => ?_, hval, fun p hp hpeq => ?_⟩
  · simp only [Set.mem_ofPred_eq, hval]
    exact neg_add_sqrt_sq_sub_sq_ge hω.le hωε.le hp
  · obtain ⟨h1, h2⟩ := eq_of_neg_add_sqrt_sq_sub_sq_eq hω.le hωε hp hpeq
    exact Prod.ext h1 h2

end CartisGouldToint.AppendixB
