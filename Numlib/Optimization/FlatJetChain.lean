import Numlib.Algebra.Polynomial.Derivative
import Numlib.Analysis.Calculus.FiniteHermiteInterpolation

/-!
# Uniform finite chains with constant first derivatives

A finite linear-value chain with constant nonzero first derivative, zero higher derivatives,
and a stationary last knot admits a globally bounded Hermite extension. All regularity
constants precede the length and scale of the chain.
-/
noncomputable section
namespace Optimization.LowerBound
open Polynomial
open scoped NNReal

/-- Linear objective values and a first derivative switched off at the last knot. -/
def flatJet (N : ℕ) (G h : ℝ) (k j : ℕ) : ℝ :=
  if j = 0 then -(k : ℝ) * G * h else if j = 1 then if k < N then -G else 0 else 0

/-- Before the last knot the prescribed Taylor polynomial is affine. -/
theorem endpointTaylor_flatJet {N p k : ℕ} {G h : ℝ} (hp : 1 ≤ p) (hk : k < N) :
    Hermite.endpointTaylor p (flatJet N G h k) = C (-(k : ℝ) * G * h) + C (-G) * X := by
  classical
  unfold Hermite.endpointTaylor Hermite.jetPoly
  simp only [C_0, sub_zero]
  rw [Finset.sum_range_succ']
  have he : ∑ x ∈ Finset.range p, C (flatJet N G h k (x + 1) / ((x + 1).factorial : ℝ)) *
      X ^ (x + 1) = C (-G) * X := by
    rw [Finset.sum_eq_single 0]
    · simp [flatJet, hk]
    · intro i hi hi0
      simp [flatJet, hi0]
    · intro hz
      exact (hz (by simp; omega)).elim
  rw [he]
  simp [flatJet, add_comm]

/-- Flat-chain endpoint jets satisfy the scaled Taylor discrepancy inequalities. -/
theorem flatJet_compatible {N p : ℕ} {G h κ : ℝ} (hp : 1 ≤ p) (hG : 0 ≤ G)
    (hh : 0 < h) (hκ : 0 ≤ κ) (hscale : G ≤ κ * h ^ p) :
    ∀ k < N, ∀ j ≤ p,
      |flatJet N G h (k + 1) j -
        (derivative^[j] (Hermite.endpointTaylor p (flatJet N G h k))).eval h| ≤
        κ * h ^ (p + 1 - j) := by
  intro k hk j hj
  rw [endpointTaylor_flatJet hp hk, eval_iterate_derivative_affine]
  by_cases hj0 : j = 0
  · subst j
    simp only [flatJet, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    have he : -((k : ℝ) + 1) * G * h - (-(k : ℝ) * G * h + -G * h) = 0 := by ring
    rw [he, abs_zero]
    positivity
  · by_cases hj1 : j = 1
    · subst j
      simp only [flatJet, Nat.one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      split_ifs
      · simpa using hG.trans hscale
      · simpa [abs_of_nonneg hG] using hscale
    · simp only [flatJet, ite_eq_right hj0, ite_eq_right hj1, sub_self, abs_zero]
      exact mul_nonneg hκ (pow_nonneg hh.le _)

/-- Initial flat-chain jets are bounded whenever the total value drop and slope are bounded. -/
theorem abs_flatJet_le {N : ℕ} {G h κ : ℝ} (hG : 0 ≤ G) (hh : 0 ≤ h)
    (hκ : 0 ≤ κ) (hdrop : (N : ℝ) * G * h ≤ κ) (hslope : G ≤ κ) :
    ∀ k < N, ∀ j : ℕ, |flatJet N G h k j| ≤ κ := by
  intro k hk j
  have hkn : (k : ℝ) ≤ N := by exact_mod_cast hk.le
  by_cases hj0 : j = 0
  · subst j
    simp only [flatJet, ↓reduceIte]
    rw [show -(k : ℝ) * G * h = -((k : ℝ) * G * h) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkn hG) hh).trans hdrop
  · by_cases hj1 : j = 1
    · subst j
      simpa [flatJet, hk, abs_of_nonneg hG] using hslope
    · simpa [flatJet, hj0, hj1] using hκ

/-- Uniform global extensions of arbitrary-length flat chains. The same constants work for
all chain lengths, positive spacings and slopes satisfying the four scalar bounds. -/
theorem exists_flatJet_chain (p : ℕ) (hp : 1 ≤ p) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L B : ℝ≥0, ∀ (N : ℕ), 0 < N → ∀ (G h : ℝ), 0 ≤ G → 0 < h →
      G ≤ κ * h ^ p → (N : ℝ) * G * h ≤ κ → G ≤ κ → h ≤ κ →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
        (∀ k ≤ N, ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) = flatJet N G h k j) ∧
        (∀ j ≤ p, ∀ t : ℝ, |iteratedDeriv j f t| ≤ B) := by
  obtain ⟨L, B, hjet⟩ := Hermite.exists_contDiff_lipschitz_iteratedDeriv_of_finite_jets p κ hκ
  refine ⟨L, B, ?_⟩
  intro N hN G h hG hh hscale hdrop hslope hspacing
  have hdiff (k : ℕ) : ((k + 1 : ℕ) : ℝ) * h - (k : ℝ) * h = h := by push_cast; ring
  obtain ⟨f, hf, hLip, he, hb⟩ := hjet N hN (fun k => (k : ℝ) * h) (flatJet N G h)
    (fun k _ => by push_cast; nlinarith)
    (fun k hk j hj => by rw [hdiff]; exact flatJet_compatible hp hG hh hκ hscale k hk j hj)
  exact ⟨f, hf, hLip, he, hb (fun k hk j _ => abs_flatJet_le hG hh.le hκ hdrop hslope k hk j)
    (fun k _ => by simpa only [hdiff] using hspacing)⟩

end Optimization.LowerBound
