import Numlib.Optimization.TrustRegion.HighOrder.Trial
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

namespace CartisGouldToint

/-- The fixed, finite-order parameters in Step 0 of Algorithm 12.2.1. -/
abbrev trqParameters (q : ℕ) := HighOrderTrustRegion.Parameters q

/-- A genuine nonterminal trial of Algorithm 12.2.1, with actual Taylor approximations,
the first failed test, actual objective ratio, and capped three-case radius update. -/
abbrev trqTrial {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : trqParameters q)
    (x : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) (d : Fin q → EuclideanSpace ℝ (Fin n))
    (j : Fin q) (s xnext : EuclideanSpace ℝ (Fin n)) (Δnext ρ : ℝ) : Prop :=
  HighOrderTrustRegion.Trial f P x Δ d j s xnext Δnext ρ

/-- The actual maximum per-order Lipschitz constant `L_f` in equation (12.2.6). -/
noncomputable abbrev trqLipschitzConstant {q : ℕ} (P : trqParameters q) (L : Fin q → ℝ) : ℝ :=
  HighOrderTrustRegion.maxLipschitzConstant P L

/-- **Lemma 12.2.2 (condition for success).** The exact small-radius condition
(12.2.11), using the genuine scaled Taylor gap and the actual maximum Lipschitz
constant, makes the objective-to-model ratio at least `η₂` and prevents contraction
of the radius. The trial predicate retains the two distinct radii and the capped
update rule, including the allowed enlargement factor `γ₃ = 1`. -/
theorem lemma_12_2_2 {n q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : trqParameters q}
    {x s xnext : EuclideanSpace ℝ (Fin n)} {Δ Δnext ρ : ℝ}
    {d : Fin q → EuclideanSpace ℝ (Fin n)} {j : Fin q}
    (h : trqTrial f P x Δ d j s xnext Δnext ρ)
    (hf : ContDiff ℝ q f) (L : Fin q → ℝ) (hL : ∀ a, 1 ≤ L a)
    (hlip : ∀ a y z,
      ‖iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f y -
        iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f z‖ ≤ L a * ‖y - z‖)
    (hsmall : Δ ≤ min P.theta ((1 - P.eta2) / trqLipschitzConstant P L *
      scaledTaylorGap f (HighOrderTrustRegion.modelOrder j) x (d j)
        (HighOrderTrustRegion.optimalityRadius P Δ))) :
    P.eta2 ≤ ρ ∧ Δ ≤ Δnext := by
  apply h.very_successful hf (HighOrderTrustRegion.maxLipschitzConstant_pos P L hL)
  · intro y z
    exact (hlip j y z).trans (mul_le_mul_of_nonneg_right
      (HighOrderTrustRegion.le_maxLipschitzConstant P L j) (norm_nonneg _))
  · exact hsmall

end CartisGouldToint
