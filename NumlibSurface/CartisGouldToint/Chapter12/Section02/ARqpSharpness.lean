import NumlibSurface.CartisGouldToint.Chapter12.Section02
import Numlib.Optimization.HigherOrderApproximateRegularizationSharpness

/-!
# Chapter 12, Section 2: sharp approximate regularization

The scalar constructions are the one-dimensional examples in the source. Every objective is
uniformly bounded and has uniformly Lipschitz derivatives of all positive orders through `p`.
Actual legal outer executions include their cache costs and first stopping test.
-/
noncomputable section
open scoped Nat NNReal
namespace CartisGouldToint.Chapter12.Section02
open Optimization HigherOrderApproximateRegularization HigherOrderSharpness TaylorCriticality
open HigherOrderApproximateRegularizationSharpness Metric Set

/-- Theorem 12.2.15: arbitrary-order good-case sharpness. The assumption that the chosen global
model minimizers permit unit model radii is retained explicitly. All actual objective gaps
fail before the endpoint, and the endpoint has zero gaps. -/
theorem theorem_12_2_15 (p q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ (L : ℝ) (B : ℝ≥0), 1 ≤ L ∧
      ∀ ε : ℝ, (hε : 0 < ε) → (hεsmall : ε ≤ 1 / 2) →
      let P := parameters p q hq hqp ε (sigma p q) hε (by linarith) (sigma_pos p q)
      ∃ (f : ℝ → ℝ) (N : ℕ) (h : ℝ),
        HigherOrderDerivativeFamily f p (fun _ => L) ∧
        (∀ x, |f x| ≤ B) ∧ (∀ x, -(B : ℝ) ≤ f x) ∧ f 0 = 0 ∧
        0 < h ∧ h ≤ 1 ∧ N = ⌈1 / ε ^ sharpExponent p q⌉₊ ∧
        (∀ k < N, ∀ t, model f p ((k : ℝ) * h) (sigma p q) h ≤
          model f p ((k : ℝ) * h) (sigma p q) t) ∧
        (∀ k < N, ε / (q.factorial : ℝ) <
          gapOn (taylorDecrement f q ((k : ℝ) * h)) (closedBall 0 1)) ∧
        (∀ j, 1 ≤ j → j ≤ q →
          gapOn (taylorDecrement f j ((N : ℝ) * h)) (closedBall 0 1) = 0) ∧
        ((∀ k < N, ModelQuality P f ((k : ℝ) * h) h (sigma p q) 1) →
          ∃ run : OuterExecution P f 0 (sigma p q) (fun _ => 1) N,
            run.state = state (sigma p q) 1 h ∧
            run.last = .stopTest (run.state N) ∧
            (∀ k < N,
              ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
            run.functionCount = N + 1 ∧ run.derivativeCount = N * p + q ∧
            ⌊1 / ε ^ sharpExponent p q⌋₊ ≤ N ∧
            ⌊1 / ε ^ sharpExponent p q⌋₊ ≤ run.functionCount ∧
            ⌊1 / ε ^ sharpExponent p q⌋₊ ≤ run.derivativeCount) := by
  obtain ⟨L, B, hc⟩ := exists_good_family p q hq hqp
  refine ⟨max (L : ℝ) 1, B, le_max_right _ _, ?_⟩
  intro ε hε hεsmall
  obtain ⟨f, N, h, hf, hLip, hb, hf0, hh, hh1, hN, hmin, hgap, hend, hrun⟩ :=
    hc ε hε hεsmall
  refine ⟨f, N, h, ?_, hb, fun x => (abs_le.mp (hb x)).1,
    hf0, hh, hh1, hN, hmin, hgap, hend, ?_⟩
  · refine ⟨hf, fun _ _ _ => L.coe_nonneg.trans (le_max_left _ _), ?_⟩
    intro j _ hj x y d
    apply (HigherOrderRegularization.DiagonalLipschitz.of_operator
      (hf.of_le (by exact_mod_cast hj))
      (L.coe_nonneg.trans (le_max_left _ _)) ?_).bound x y d
    intro a b
    have hd := (hLip j hj).dist_le_mul a b
    simp only [dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro hquality
    obtain ⟨run, hs, hl, hn, hfun, hder⟩ := hrun hquality
    have hflo : ⌊1 / ε ^ sharpExponent p q⌋₊ ≤ N := by
      rw [hN]
      exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ 1 / ε ^ sharpExponent p q)).trans
        (Nat.le_ceil _)
    have hp : 1 ≤ p := hq.trans hqp
    have hnle : N ≤ N * p := by nlinarith
    exact ⟨run, hs, hl, hn, hfun, hder, hflo, by omega, by omega⟩

/-- Corollary 12.2.16: for orders one and two, unit model radii are unconditional. The exact
ceiling iteration count forces the displayed floor lower bounds for both oracle costs. -/
theorem corollary_12_2_16 (p q : ℕ) (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ (L : ℝ) (B : ℝ≥0), 1 ≤ L ∧
      ∀ ε : ℝ, (hε : 0 < ε) → (hεsmall : ε ≤ 1 / 2) →
      let P := parameters p q hq hqp ε (sigma p q) hε (by linarith) (sigma_pos p q)
      ∃ (f : ℝ → ℝ) (N : ℕ) (h : ℝ)
        (run : OuterExecution P f 0 (sigma p q) (fun _ => 1) N),
        HigherOrderDerivativeFamily f p (fun _ => L) ∧
        (∀ x, |f x| ≤ B) ∧ (∀ x, -(B : ℝ) ≤ f x) ∧ f 0 = 0 ∧
        0 < h ∧ h ≤ 1 ∧ N = ⌈1 / ε ^ sharpExponent p q⌉₊ ∧
        (∀ k < N, ε / (q.factorial : ℝ) <
          gapOn (taylorDecrement f q ((k : ℝ) * h)) (closedBall 0 1)) ∧
        (∀ j, 1 ≤ j → j ≤ q →
          gapOn (taylorDecrement f j ((N : ℝ) * h)) (closedBall 0 1) = 0) ∧
        run.state = state (sigma p q) 1 h ∧ run.last = .stopTest (run.state N) ∧
        (∀ k < N, ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
        run.functionCount = N + 1 ∧ run.derivativeCount = N * p + q ∧
        ⌊1 / ε ^ sharpExponent p q⌋₊ ≤ N ∧
        ⌊1 / ε ^ sharpExponent p q⌋₊ ≤ run.functionCount ∧
        ⌊1 / ε ^ sharpExponent p q⌋₊ ≤ run.derivativeCount := by
  obtain ⟨L, B, hc⟩ := exists_low_family p q hq hq2 hqp
  refine ⟨max (L : ℝ) 1, B, le_max_right _ _, ?_⟩
  intro ε hε hεsmall
  obtain ⟨f, N, h, run, hf, hLip, hb, hf0, hh, hh1, hN, hgap, hend,
    hs, hl, hn, hfun, hder⟩ := hc ε hε hεsmall
  refine ⟨f, N, h, run, ?_, hb, fun x => (abs_le.mp (hb x)).1,
    hf0, hh, hh1, hN, hgap, hend, hs, hl, hn, hfun, hder, ?_, ?_, ?_⟩
  · refine ⟨hf, fun _ _ _ => L.coe_nonneg.trans (le_max_left _ _), ?_⟩
    intro j _ hj x y d
    apply (HigherOrderRegularization.DiagonalLipschitz.of_operator
      (hf.of_le (by exact_mod_cast hj))
      (L.coe_nonneg.trans (le_max_left _ _)) ?_).bound x y d
    intro a b
    have hd := (hLip j hj).dist_le_mul a b
    simp only [dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  all_goals
    have hflo : ⌊1 / ε ^ sharpExponent p q⌋₊ ≤ N := by
      rw [hN]
      exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ 1 / ε ^ sharpExponent p q)).trans
        (Nat.le_ceil _)
    have hp : 1 ≤ p := hq.trans hqp
    have hnle : N ≤ N * p := by nlinarith
    omega

end CartisGouldToint.Chapter12.Section02
