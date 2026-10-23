import NumlibSurface.CartisGouldToint.Chapter04.Section01
import Numlib.Optimization.HighOrder.ModelDecrease
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Model-decrement lower bounds for TRq

The local Step 1 and Step 2 conditions of Algorithm 12.2.1 suffice for the prefix minimum bound
and the trial-step bound of Lemma 12.2.1. Taylor decrements are evaluated from the actual
iterated Fréchet derivatives, and the scaled gap is the expression in equation (12.2.8).
-/

namespace CartisGouldToint

/-- The scaled approximate criticality gap of equation (12.2.8). -/
noncomputable def scaledTaylorGap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (j : ℕ) (x d : E) (δ : ℝ) : ℝ :=
  ModelDecrease.scaled (taylorDecrement f j x d) δ j

/-- Lemma 12.2.1: before termination, every scaled criticality gap, and hence its prefix minimum,
is at least `ς ε_min`. The trial step also achieves the rescaled criticality gap. The hypotheses
are precisely the failing Step 1 test and the Step 2 model comparison, for each iteration in
the prefix. No global decrease or criticality estimate is assumed. -/
theorem lemma_12_2_1 {n q k : ℕ} (hq : 1 ≤ q)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℕ → ℝ) {ς : ℝ} (hς : 0 ≤ ς)
    (x d s : Fin (k + 1) → EuclideanSpace ℝ (Fin n))
    (j : Fin (k + 1) → ℕ) (δ : Fin (k + 1) → ℝ)
    (hj : ∀ i, j i ∈ Finset.Icc 1 q) (hδ : ∀ i, 0 < δ i)
    (htest : ∀ i, ς * ε (j i) * δ i ^ j i / ((j i).factorial : ℝ) <
      taylorDecrement f (j i) (x i) (d i))
    (hstep : ∀ i, taylorDecrement f (j i) (x i) (d i) ≤
      taylorDecrement f (j i) (x i) (s i)) :
    ς * (Finset.Icc 1 q).inf' (Finset.nonempty_Icc.mpr hq) ε ≤
        Finset.univ.inf' Finset.univ_nonempty
          (fun i => scaledTaylorGap f (j i) (x i) (d i) (δ i)) ∧
      scaledTaylorGap f (j (Fin.last k)) (x (Fin.last k)) (d (Fin.last k))
          (δ (Fin.last k)) * δ (Fin.last k) ^ j (Fin.last k) /
          ((j (Fin.last k)).factorial : ℝ) ≤
        taylorDecrement f (j (Fin.last k)) (x (Fin.last k)) (s (Fin.last k)) := by
  constructor
  · apply (Finset.le_inf'_iff _ _).mpr
    intro i _
    exact (mul_le_mul_of_nonneg_left (Finset.inf'_le ε (hj i)) hς).trans
      (ModelDecrease.le_scaled_of_test (j i) (hδ i) (htest i))
  · unfold scaledTaylorGap
    rw [ModelDecrease.scaled_mul_radius _ (hδ (Fin.last k))]
    exact hstep (Fin.last k)

end CartisGouldToint
