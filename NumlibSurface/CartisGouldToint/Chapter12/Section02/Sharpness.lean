import Numlib.Optimization.HigherOrderTrustRegionSharpness
import NumlibSurface.CartisGouldToint.Chapter12.Section02.TRq

/-!
# Chapter 12, Section 2: sharpness of TRq

The arbitrary-order lower bound uses bounded actual objectives, actual derivative tensors,
and legal algorithm executions. All objective and smoothness bounds precede the accuracy
quantifier. The construction explicitly starts with radius equal to the accuracy, as in
Appendix B's proof of Theorem 12.2.6.
-/

noncomputable section
open scoped Nat NNReal
namespace CartisGouldToint.Chapter12.Section02
open Optimization HigherOrderTrustRegion TaylorCriticality Metric Set
open HigherOrderTrustRegionSharpness

/-- Theorem 12.2.6: for every positive optimality order, TRq can require the inverse
`(q+1)` accuracy power of iterations and actual evaluation batches. The objective has bounded
range and all positive derivatives through order `q` are globally Lipschitz, with constants
independent of accuracy. Before the first stop, every positive testing radius fails the
highest-order objective criterion. The permitted initial trust-region radius equals `ε`. -/
theorem theorem_12_2_6 (q : ℕ) (hq : 1 ≤ q) :
    ∃ (L : ℝ) (B : ℝ≥0), 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (q.factorial : ℝ) →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (t : Trace (EuclideanSpace ℝ (Fin 1))),
        LipschitzDerivativeFamily f q (fun _ => L) ∧
        (∀ x, |f x| ≤ B) ∧ (∀ x, -(B : ℝ) ≤ f x) ∧
        f 0 = 0 ∧ t.point 0 = 0 ∧ t.radius 0 = ε ∧
        algorithm_12_2_1 parameters q (fun j => j.factorial * ε) f t ∧
        (∀ k < N, ¬Stops parameters q (fun j => j.factorial * ε) f t k) ∧
        Stops parameters q (fun j => j.factorial * ε) f t N ∧
        (∀ k < N, ∀ δ : ℝ, 0 < δ →
          (q.factorial : ℝ) * ε * δ ^ q / q.factorial <
            gapOn (taylorDecrement f q (t.point k)) (closedBall 0 δ)) ∧
        (∀ j, 1 ≤ j → j ≤ q →
          gapOn (taylorDecrement f j (t.point N)) (closedBall 0 (testRadius parameters t N)) ≤
            (j.factorial : ℝ) * ε * testRadius parameters t N ^ j / j.factorial) ∧
        functionEvaluations N = N + 1 ∧
        derivativeBatches parameters f t N = N + 1 ∧
        ⌊1 / ε ^ (q + 1)⌋₊ ≤ N := by
  obtain ⟨L, B, hc⟩ := exists_hard_family q hq
  refine ⟨max (L : ℝ) 1, B, le_max_right _ _, ?_⟩
  intro ε hε hεsmall
  have hfac : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hε1 : ε ≤ 1 := hεsmall.trans ((div_le_one (by positivity)).mpr hfac)
  obtain ⟨f, N, hf, hLip, hb, hf0, ht0, hr0, hrun, hnot, hstop, hgap, hfe, hde, hN⟩ :=
    hc ε hε hε1
  have he (j : ℕ) (hj : 1 ≤ j) (hjq : j ≤ q) :
      0 < (j.factorial : ℝ) * ε ∧ (j.factorial : ℝ) * ε ≤ 1 := by
    refine ⟨by positivity, ?_⟩
    have hfacs : (j.factorial : ℝ) ≤ q.factorial := by
      exact_mod_cast Nat.factorial_le hjq
    have hm := mul_le_mul_of_nonneg_left hεsmall (show 0 ≤ (q.factorial : ℝ) by positivity)
    have hid : (q.factorial : ℝ) * (1 / q.factorial) = 1 := by field_simp
    rw [hid] at hm
    exact (mul_le_mul_of_nonneg_right hfacs hε.le).trans hm
  refine ⟨f, N, trace q ε, ?_, hb, fun x => (abs_le.mp (hb x)).1,
    hf0, ht0, hr0, ?_, hnot, hstop, hgap, ?_, hfe, hde, ?_⟩
  · refine ⟨⟨hf, fun _ _ _ => (L.coe_nonneg.trans (le_max_left _ _)), ?_⟩,
      fun _ _ _ => le_max_right _ _⟩
    intro j _ hj x y d
    apply (HigherOrderRegularization.DiagonalLipschitz.of_operator
      (hf.of_le (by exact_mod_cast hj)) (L.coe_nonneg.trans (le_max_left _ _)) ?_).bound x y d
    intro a b
    have hh := (hLip j hj).dist_le_mul a b
    simp only [dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · refine ⟨hq, he, ?_, hrun⟩
    exact (TRq.epsilonMinimum_le (fun j => (j.factorial : ℝ) * ε) le_rfl hq).trans
      (by simpa [parameters] using hε1)
  · exact (hrun N hnot).gaps_at_stop hstop
  · exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ 1 / ε ^ (q + 1))).trans hN

end CartisGouldToint.Chapter12.Section02
