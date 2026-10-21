import NumlibSurface.CartisGouldToint.Chapter12.Section02
import Numlib.Optimization.HigherOrderAffineRegularizationSharpness

/-!
# Chapter 12, Section 2: small-radius regularization sharpness

The scalar examples in the source admit uniformly bounded objectives of arbitrarily high
finite smoothness. Their actual regularization executions use accuracy radii, and attain
the claimed evaluation exponent with a true first stopping test.
-/
noncomputable section
open scoped Nat NNReal
namespace CartisGouldToint.Chapter12.Section02
open Optimization HigherOrderApproximateRegularization TaylorCriticality
open HigherOrderApproximateRegularizationSharpness HigherOrderAffineRegularizationSharpness
open Metric Set

/-- Theorem 12.2.17: for every `1 ≤ q ≤ p ≤ r`, even uniform extra available smoothness
permits the exact small-radius lower complexity exponent. The radii equal `ε`, hence meet
every lower-radius requirement `κ ε` with `κ ≤ 1`, including (12.2.51). -/
theorem theorem_12_2_17 (p q r : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p) (hpr : p ≤ r) :
    ∃ (L : ℝ) (B : ℝ≥0), 1 ≤ L ∧
      ∀ ε : ℝ, (hε : 0 < ε) → (hεsmall : ε ≤ 1 / 2) →
      let P := parameters p q hq hqp ε (affineSigma p q) hε (by linarith)
        (affineSigma_pos (hq.trans hqp) q)
      ∃ (f : ℝ → ℝ) (N : ℕ) (h : ℝ)
        (run : OuterExecution P f 0 (affineSigma p q) (fun _ => ε) N),
        HigherOrderDerivativeFamily f r (fun _ => L) ∧
        (∀ x, |f x| ≤ B) ∧ (∀ x, -(B : ℝ) ≤ f x) ∧ f 0 = 0 ∧ 0 < h ∧
        N = ⌈1 / ε ^ affineExponent p q⌉₊ ∧
        (∀ k < N, ε * ε ^ q / (q.factorial : ℝ) <
          gapOn (taylorDecrement f q ((k : ℝ) * h)) (closedBall 0 ε)) ∧
        (∀ j, 1 ≤ j → j ≤ q →
          gapOn (taylorDecrement f j ((N : ℝ) * h)) (closedBall 0 ε) <
            ε * ε ^ j / (j.factorial : ℝ)) ∧
        run.state = state (affineSigma p q) ε h ∧ run.last = .stopTest (run.state N) ∧
        (∀ k < N, ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
        (∀ κ : ℝ, κ ≤ 1 → ∀ k j, κ * ε ≤ (run.state k).radii j) ∧
        run.functionCount = N + 1 ∧ run.derivativeCount = N * p + q ∧
        ⌊1 / ε ^ affineExponent p q⌋₊ ≤ N ∧
        ⌊1 / ε ^ affineExponent p q⌋₊ ≤ run.functionCount ∧
        ⌊1 / ε ^ affineExponent p q⌋₊ ≤ run.derivativeCount := by
  obtain ⟨L, B, hc⟩ := HigherOrderAffineRegularizationSharpness.exists_hard_family p q r hq hqp hpr
  refine ⟨max (L : ℝ) 1, B, le_max_right _ _, ?_⟩
  intro ε hε hεsmall
  obtain ⟨f, N, h, run, hf, hLip, hb, hf0, hh, hN, hgap, hend,
    hs, hl, hn, hfun, hder⟩ := hc ε hε hεsmall
  refine ⟨f, N, h, run, ?_, hb, fun x => (abs_le.mp (hb x)).1,
    hf0, hh, hN, hgap, hend, hs, hl, hn, ?_, hfun, hder, ?_, ?_, ?_⟩
  · refine ⟨hf, fun _ _ _ => L.coe_nonneg.trans (le_max_left _ _), ?_⟩
    intro j _ hj x y d
    apply (HigherOrderRegularization.DiagonalLipschitz.of_operator
      (hf.of_le (by exact_mod_cast hj))
      (L.coe_nonneg.trans (le_max_left _ _)) ?_).bound x y d
    intro a b
    have hd := (hLip j hj).dist_le_mul a b
    simp only [dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro κ hκ k j
    rw [hs]
    change κ * ε ≤ ε
    exact mul_le_of_le_one_left hε.le hκ
  all_goals
    have hflo : ⌊1 / ε ^ affineExponent p q⌋₊ ≤ N := by
      rw [hN]
      exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ 1 / ε ^ affineExponent p q)).trans
        (Nat.le_ceil _)
    have hp : 1 ≤ p := hq.trans hqp
    have hnle : N ≤ N * p := by nlinarith
    omega

end CartisGouldToint.Chapter12.Section02
