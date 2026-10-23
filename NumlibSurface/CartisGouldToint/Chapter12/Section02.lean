import Numlib.Optimization.TrustRegion.HighOrder.Radius
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

namespace CartisGouldToint

/-- A finite nonterminal prefix of Algorithm 12.2.1, with initialized radius and actual
trials. Its rules contain no radius floor, model-decrease floor, or complexity estimate. -/
abbrev trqRun {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : trqParameters q)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (d : ℕ → Fin q → EuclideanSpace ℝ (Fin n))
    (j : ℕ → Fin q) (Δ ρ : ℕ → ℝ) (N : ℕ) : Prop :=
  HighOrderTrustRegion.Run f P x s d j Δ ρ N

/-- The minimum accuracy `ε_min` of equation (12.2.7). -/
noncomputable abbrev trqMinimumAccuracy {q : ℕ} (P : trqParameters q) : ℝ :=
  HighOrderTrustRegion.minimumAccuracy P

/-- The true finite prefix minimum of the scaled gaps in equation (12.2.8). -/
noncomputable abbrev trqPrefixGap {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : trqParameters q) (x : ℕ → EuclideanSpace ℝ (Fin n)) (Δ : ℕ → ℝ)
    (d : ℕ → Fin q → EuclideanSpace ℝ (Fin n)) (j : ℕ → Fin q) (k : ℕ) : ℝ :=
  HighOrderTrustRegion.prefixGap f P x Δ d j k

/-- The exact `κ_Δ` of equation (12.2.14). Its arguments consist only of the fixed
parameters, initial radius, initial point and objective derivatives: no accuracy is an
argument. The printed `2q!` denotes `2 · q!`, as in the source reciprocal-factorial proof. -/
noncomputable abbrev trqRadiusConstant {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (q : ℕ) (hq : 0 < q)
    (x₀ : EuclideanSpace ℝ (Fin n)) (Δ₀ theta eta2 gamma1 L : ℝ) : ℝ :=
  HighOrderTrustRegion.radiusConstant f q hq x₀ Δ₀ theta eta2 gamma1 L

/-- **Lemma 12.2.3 (lower bound on the trust-region radius).** The exact coefficient
(12.2.14) is strictly between zero and one, and the uniform prefix bound (12.2.13)
holds at every nonterminal trial. The initial scaled-gap estimate is derived from the
actual Taylor coefficients; the floor follows from the actual preceding updates.
The enlargement factor may equal one. -/
theorem lemma_12_2_3 {n q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : trqParameters q}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d : ℕ → Fin q → EuclideanSpace ℝ (Fin n)}
    {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ} {N k : ℕ}
    (h : trqRun f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    (L : Fin q → ℝ) (hL : ∀ a, 1 ≤ L a)
    (hlip : ∀ a y z,
      ‖iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f y -
        iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f z‖ ≤ L a * ‖y - z‖)
    (hk : k < N) :
    let κ := trqRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1
      (trqLipschitzConstant P L)
    κ ∈ Set.Ioo (0 : ℝ) 1 ∧ κ < P.gamma1 ∧
      min (P.gamma1 * P.theta) (κ * trqPrefixGap f P x Δ d j k) ≤ Δ k := by
  have hmax : 1 ≤ trqLipschitzConstant P L :=
    (hL ⟨0,P.order_pos⟩).trans (HighOrderTrustRegion.le_maxLipschitzConstant P L _)
  have hc := h.radiusConstant_pos_lt_gamma1 (by omega) hmax
  refine ⟨⟨hc.1, hc.2.trans (P.gamma1_le_gamma2.trans_lt P.gamma2_lt_one)⟩, hc.2, ?_⟩
  apply h.radius_lower hf hmax _ hk
  intro a y z
  exact (hlip a y z).trans (mul_le_mul_of_nonneg_right
    (HighOrderTrustRegion.le_maxLipschitzConstant P L a) (norm_nonneg _))

/-- **Lemma 12.2.4 (model and function decreases).** The model floor (12.2.18) holds
at every actual nonterminal trial, and every accepted trial attains (12.2.19).
The coefficient is an explicit function of the fixed initial data and parameters;
accuracies occur only as `ε_min^(q+1)`. Both statements use the actual Taylor model
and the actual objective values at the algorithm's successive iterates. -/
theorem lemma_12_2_4 {n q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : trqParameters q}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d : ℕ → Fin q → EuclideanSpace ℝ (Fin n)}
    {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ} {N k : ℕ}
    (h : trqRun f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    (L : Fin q → ℝ) (hL : ∀ a, 1 ≤ L a)
    (hlip : ∀ a y z,
      ‖iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f y -
        iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f z‖ ≤ L a * ‖y - z‖)
    (hk : k < N) :
    let κ := trqRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1
      (trqLipschitzConstant P L)
    (P.zeta * κ) ^ (q + 1) / q.factorial * trqMinimumAccuracy P ^ (q + 1) ≤
        taylorDecrement f (HighOrderTrustRegion.modelOrder (j k)) (x k) (s k) ∧
      (P.eta1 ≤ ρ k →
        P.eta1 * (P.zeta * κ) ^ (q + 1) / q.factorial * trqMinimumAccuracy P ^ (q + 1) ≤
          f (x k) - f (x (k + 1))) := by
  have hmax : 1 ≤ trqLipschitzConstant P L :=
    (hL ⟨0,P.order_pos⟩).trans (HighOrderTrustRegion.le_maxLipschitzConstant P L _)
  have hcommon : ∀ (a : Fin q) y z,
      ‖iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f y -
        iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f z‖ ≤
        trqLipschitzConstant P L * ‖y - z‖ := by
    intro a y z
    exact (hlip a y z).trans (mul_le_mul_of_nonneg_right
      (HighOrderTrustRegion.le_maxLipschitzConstant P L a) (norm_nonneg _))
  exact ⟨h.model_decrease hf hmax hcommon hk,
    fun hs => h.function_decrease hf hmax hcommon hk hs⟩

end CartisGouldToint
