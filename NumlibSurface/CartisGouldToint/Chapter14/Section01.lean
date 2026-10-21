import Numlib.Optimization.CompositeModelDecrease
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Chapter 14, Section 1: composite objectives and generalized Taylor models

The objective is `w = f + h ∘ c` on Euclidean space. The composition `h` is retained exactly
in every generalized model and may be nonsmooth. This file supplies the problem assumptions,
optimality measures, regularized models, and the first-order necessary condition. The algorithm
and its remaining complexity analysis are still planned separately.
-/

noncomputable section

open scoped Nat NNReal ContDiff Topology
open Optimization.CompositeTaylorModels Optimization.TaylorCriticality

namespace CartisGouldToint.Chapter14.Section01

/-- The data and assumptions of (14.1.1), f.D1pL, c.D1pL, h.L, h.S0 and w.Bb.
The component derivative constants use the Euclidean domain norm. Vector `C^p` regularity is
equivalent to componentwise `C^p` regularity. Convexity of `h` is a separate assumption. -/
structure CompositeProblem (n m p : ℕ) where
  f : EuclideanSpace ℝ (Fin n) → ℝ
  c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)
  h : LipschitzSubadditiveComposition (EuclideanSpace ℝ (Fin m))
  f_contDiff : ContDiff ℝ p f
  c_contDiff : ContDiff ℝ p c
  Lf : ℕ → ℝ≥0
  Lc : ℕ → ℝ≥0
  f_deriv_lipschitz : ∀ j ∈ Finset.Icc 1 p, LipschitzWith (Lf j) (iteratedFDeriv ℝ j f)
  c_deriv_lipschitz : ∀ j ∈ Finset.Icc 1 p, ∀ i : Fin m,
    LipschitzWith (Lc j) (iteratedFDeriv ℝ j (fun x ↦ c x i))
  lower : ℝ
  bounded_below : ∀ x, lower ≤ f x + h (c x)

variable {n m p : ℕ}

/-- The composite objective in (14.1.1). -/
def CompositeProblem.objective (P : CompositeProblem n m p) (x : EuclideanSpace ℝ (Fin n)) :
    ℝ := P.f x + P.h (P.c x)

/-- The generalized Taylor model (14.1.5). This is not the Taylor polynomial of `w`. -/
def compositeTaylorModel (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (j : ℕ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  model f c h j x s

/-- The vector Taylor polynomial in (14.1.5) has exactly the scalar component polynomials
specified in the source. -/
theorem taylorModel_component {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {j : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hc : ContDiffAt ℝ j c x)
    (s : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    Optimization.RegularizedTaylorModel.taylorModel c j x s i =
      Optimization.RegularizedTaylorModel.taylorModel (fun y ↦ c y i) j x s :=
  Optimization.RegularizedTaylorModel.taylorModel_euclidean_component hc s i

/-- Componentwise Euclidean remainder bounds produce the source's `√m` composition factor.
Only the Lipschitz assumption on `h` is used. -/
theorem compositeTaylorModel_error_le {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {h : EuclideanSpace ℝ (Fin m) → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h)
    {x s : EuclideanSpace ℝ (Fin n)} (hc : ContDiffAt ℝ p c x) {A B : ℝ} (hB : 0 ≤ B)
    (hf : |f (x + s) - Optimization.RegularizedTaylorModel.taylorModel f p x s| ≤
      A * ‖s‖ ^ (p + 1))
    (hcomp : ∀ i : Fin m,
      |c (x + s) i - Optimization.RegularizedTaylorModel.taylorModel (fun y ↦ c y i) p x s| ≤
        B * ‖s‖ ^ (p + 1)) :
    |f (x + s) + h (c (x + s)) - compositeTaylorModel f c h p x s| ≤
      (A + Real.sqrt m * K * B) * ‖s‖ ^ (p + 1) := by
  have hvec : ‖c (x + s) - Optimization.RegularizedTaylorModel.taylorModel c p x s‖ ≤
      (Real.sqrt m * B) * ‖s‖ ^ (p + 1) := by
    rw [EuclideanSpace.norm_eq]
    calc
      _ ≤ Real.sqrt (∑ _ : Fin m, (B * ‖s‖ ^ (p + 1)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        simpa only [PiLp.sub_apply, taylorModel_component hc, Real.norm_eq_abs] using hcomp i
      _ = (Real.sqrt m * B) * ‖s‖ ^ (p + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg m),
          Real.sqrt_sq (mul_nonneg hB (pow_nonneg (norm_nonneg s) (p + 1)))]
        ring
  calc
    _ ≤ (A + K * (Real.sqrt m * B)) * ‖s‖ ^ (p + 1) := model_error_le hh hf hvec
    _ = _ := by ring

/-- The decrement following (14.1.10), measured relative to the zero step. -/
def compositeTaylorDecrement (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (j : ℕ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  decrement f c h j x s

/-- The generalized gap (14.1.6), as the supremum of feasible decrements.
Continuity and compactness identify this with the objective minus the minimum model value. -/
def compositeTaylorGap (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (j : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (δ : ℝ) : ℝ :=
  gapOn (compositeTaylorDecrement f c h j x) (Metric.closedBall 0 δ)

/-- The closed-ball generalized model minimum is attained, and its decrease is the gap. -/
theorem compositeTaylorGap_attained {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {h : EuclideanSpace ℝ (Fin m) → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ d ∈ Metric.closedBall 0 δ,
      IsMinOn (compositeTaylorModel f c h j x) (Metric.closedBall 0 δ) d ∧
      compositeTaylorGap f c h j x δ =
        f x + h (c x) - compositeTaylorModel f c h j x d := by
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall 0 δ := by simpa using hδ
  have hcont := (continuous_decrement f c hh j x).continuousOn
    (s := Metric.closedBall 0 δ)
  obtain ⟨d, hd, heq⟩ := exists_eq_gapOn (isCompact_closedBall 0 δ) ⟨0, h0⟩ hcont
  refine ⟨d, hd, ?_, ?_⟩
  · intro y hy
    have hle := le_gapOn (isCompact_closedBall 0 δ) hcont hy
    rw [← heq] at hle
    change model f c h j x d ≤ model f c h j x y
    dsimp [decrement] at hle
    linarith
  · exact heq.symm.trans (decrement_eq f c h j x d)

/-- The supremum definition agrees with the minimum-model formulation in (14.1.6). -/
theorem compositeTaylorGap_eq_sub_sInf {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {h : EuclideanSpace ℝ (Fin m) → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) {δ : ℝ} (hδ : 0 ≤ δ) :
    compositeTaylorGap f c h j x δ = f x + h (c x) -
      sInf (compositeTaylorModel f c h j x '' Metric.closedBall 0 δ) := by
  obtain ⟨d, hd, hmin, hgap⟩ := compositeTaylorGap_attained hh j x hδ
  have hleast : IsLeast (compositeTaylorModel f c h j x '' Metric.closedBall 0 δ)
      (compositeTaylorModel f c h j x d) := by
    refine ⟨Set.mem_image_of_mem _ hd, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  rw [hleast.csInf_eq]
  exact hgap

/-- All generalized order conditions (14.1.9), with positive accuracies and radii in `(0,1]`. -/
def IsCompositeApproxOrderMinimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (q : ℕ) (ε δ : ℕ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ 0 < δ j ∧ δ j ≤ 1 ∧
    compositeTaylorGap f c h j x (δ j) ≤ ε j * δ j ^ j / j !

/-- A feasible approximate maximizer satisfying the two bounds in (14.1.10).
The positive factor `varsigma` is required in the implication to the exact gap criterion. -/
def IsCompositeGapWitness (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (j : ℕ) (x d : EuclideanSpace ℝ (Fin n))
    (varsigma ε δ : ℝ) : Prop :=
  ‖d‖ ≤ δ ∧ varsigma * compositeTaylorGap f c h j x δ ≤
    compositeTaylorDecrement f c h j x d ∧
    compositeTaylorDecrement f c h j x d ≤ varsigma * (ε * δ ^ j / j !)

/-- A positive-factor witness certifies the corresponding exact generalized gap bound. -/
theorem IsCompositeGapWitness.gap_le {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {h : EuclideanSpace ℝ (Fin m) → ℝ} {j : ℕ} {x d : EuclideanSpace ℝ (Fin n)}
    {varsigma ε δ : ℝ} (hw : IsCompositeGapWitness f c h j x d varsigma ε δ)
    (hvarsigma : 0 < varsigma) :
    compositeTaylorGap f c h j x δ ≤ ε * δ ^ j / j ! :=
  (mul_le_mul_iff_right₀ hvarsigma).mp (hw.2.1.trans hw.2.2)

/-- The regularized composite model (14.1.11). -/
def compositeRegularizedModel (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (p : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  regularizedModel f c h p x σ s

/-- The generalized Taylor model underlying (14.1.14). Only the scalar smooth part,
vector smooth part, and regularizer are expanded; `h` remains exact. -/
def compositeRegularizedTaylorModel (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (p j : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (σ : ℝ) (s d : EuclideanSpace ℝ (Fin n)) : ℝ :=
  model (fun u ↦ Optimization.RegularizedTaylorModel.taylorModel f p x u +
    σ * ‖u‖ ^ (p + 1) / (p + 1)!)
    (Optimization.RegularizedTaylorModel.taylorModel c p x) h j s d

/-- Lemma 14.1.1: at a global minimum of a convex-composite objective, zero globally minimizes
its first generalized model and every positive-radius first-order gap vanishes. The assumptions
on `f` and `c` are weakened to differentiability at the minimizer. -/
theorem lemma_14_1_1 {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : LipschitzSubadditiveComposition (EuclideanSpace ℝ (Fin m)))
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (hh : ConvexOn ℝ Set.univ h)
    (hx : ∀ y, f x + h (c x) ≤ f y + h (c y)) :
    (∀ s, compositeTaylorModel f c h 1 x 0 ≤ compositeTaylorModel f c h 1 x s) ∧
      ∀ δ > 0, compositeTaylorGap f c h 1 x δ = 0 := by
  have hmin : IsLocalMin (fun y ↦ f y + h (c y)) x := Filter.Eventually.of_forall hx
  have hm := first_model_min_of_convex_localMin hf hc h.lipschitz hh hmin
  refine ⟨hm, fun δ hδ ↦ ?_⟩
  apply (gapOn_eq_zero_iff (isCompact_closedBall 0 δ) ?_ ?_ ?_).mpr
  · intro d _
    exact sub_nonpos.mpr (hm d)
  · exact (continuous_decrement f c h.lipschitz 1 x).continuousOn
  · simpa using hδ.le
  · exact decrement_zero f c h 1 x

/-- Lemma 14.1.5: the model nonincrease condition (14.1.12) alone implies the claimed
lower bound on the predicted decrement, before imposing any other algorithmic step conditions. -/
theorem lemma_14_1_5 {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {h : EuclideanSpace ℝ (Fin m) → ℝ} {x s : EuclideanSpace ℝ (Fin n)} {σ : ℝ}
    (hs : compositeRegularizedModel f c h p x σ s ≤
      compositeRegularizedModel f c h p x σ 0) :
    σ * ‖s‖ ^ (p + 1) / (p + 1)! ≤ compositeTaylorDecrement f c h p x s :=
  regularized_decrement_lower_bound hs

end CartisGouldToint.Chapter14.Section01
