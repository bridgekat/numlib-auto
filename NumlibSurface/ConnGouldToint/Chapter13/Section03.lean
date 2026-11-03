import NumlibSurface.ConnGouldToint.Chapter06.Section06
import NumlibSurface.ConnGouldToint.Chapter13.Section02

/-! # Constrained Cauchy and eigenpoints -/

open Filter Metric Set
open scoped Topology

namespace ConnGouldToint.Chapter13

open Chapter06

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The effective radius of the arcs in (13.3.3) and (13.3.20), in the common norm
used for the trust region and boundary distance in the displayed bounds. -/
def constrainedBarrierRadius (Δ σ d : ℝ) : ℝ := min Δ ((1 - σ) * d)

/-- The displacement of the constrained Cauchy point (13.3.5)–(13.3.6). -/
def IsConstrainedBarrierCauchyStep (m : E → ℝ) (g : E) (Δ σ d : ℝ) (s : E) : Prop :=
  IsCauchyPoint m (normSeminorm ℝ E) g (constrainedBarrierRadius Δ σ d) s

/-- The first- and second-order decrease test (13.3.2). -/
def HasConstrainedBarrierDecrease (m : E → ℝ) (x s g : E) (β Δ σ d τ κ : ℝ) : Prop :=
  κ * max (‖g‖ * min (‖g‖ / β) (constrainedBarrierRadius Δ σ d))
    (-τ * min (τ ^ 2) (constrainedBarrierRadius Δ σ d ^ 2)) ≤ m x - m (x + s)

/-- A fixed-parameter run of Algorithm 13.3.1. Each trial must satisfy (13.3.1)
before the acceptance ratio is computed. The ratio and radius rules then agree
with the first primal barrier run. Here `g`, `β` and `τ` are the gradient, curvature
bound and nonpositive least-curvature measure of the total model. -/
structure SecondPrimalBarrierInnerRun [CompleteSpace E] (P : BTRParams) (C : Set E) (σ : ℝ) (φ : E → ℝ)
    extends PrimalBarrierInnerRun P C σ φ where
  fraction : σ ∈ Ioo (0 : ℝ) 1
  objectiveModel : ℕ → E → ℝ
  barrierModel : ℕ → E → ℝ
  model_split : ∀ j, model j = objectiveModel j + barrierModel j
  g : ℕ → E
  β : ℕ → ℝ
  τ : ℕ → ℝ
  κ : ℝ
  decrease_constant : 0 < κ
  gradient_model : ∀ j, g j = gradient (model j) (x j)
  curvature_model : ∀ j, β j = 1 + sSup
    ((fun y ↦ ‖fderiv ℝ (fderiv ℝ (model j)) y‖) '' closedBall (x j) (Δ j))
  nonpositive_least_curvature : ∀ j, τ j = min 0
    (sInf ((fun v ↦ fderiv ℝ (fderiv ℝ (model j)) (x j) v v) '' sphere 0 1))
  trial_admissible : ∀ j, BarrierAdmissibleTrial C σ (x j) (x j + s j)
  sufficient_decrease : ∀ j,
    HasConstrainedBarrierDecrease (model j) (x j) (s j) (g j) (β j) (Δ j) σ
      (infDist (x j) (frontier C)) (τ j) κ

/-- Theorem 13.3.1. The constrained Cauchy decrease is the ordinary quadratic
Cauchy decrease with the reduced radius. -/
theorem theorem_13_3_1 (c : ℝ) (g : E) (H : E →L[ℝ] E) {Δ σ d : ℝ}
    (hΔ : 0 ≤ Δ) (hσ : σ ≤ 1) (hd : 0 ≤ d) {s : E}
    (hs : IsConstrainedBarrierCauchyStep (quadraticModel c g H.toLinearMap) g Δ σ d s) :
    (1 / 2) * ‖g‖ * min (‖g‖ / quadraticCurvatureBound H) (constrainedBarrierRadius Δ σ d) ≤
      c - quadraticModel c g H.toLinearMap s := by
  by_cases hg : g = 0
  · obtain ⟨t, _, rfl, _⟩ := hs.2
    simp [hg, quadraticModel]
  have h := theorem_6_3_1 c g H (normSeminorm ℝ E)
    (fun _ hv ↦ norm_eq_zero.mp hv)
    (le_min hΔ (mul_nonneg (sub_nonneg.mpr hσ) hd)) hs
  simpa [constrainedBarrierRadius, cauchyNormRatio, norm_ne_zero_iff.mpr hg] using h

/-- Corollary 13.3.2, with the corrected lower-bound hypothesis of Theorem
13.2.1. The truncated gradient measure satisfies the AA.1b decrease bound. -/
theorem corollary_13_3_2 [CompleteSpace E] {P : BTRParams} {C : Set E} {σ : ℝ} {f b : E → ℝ}
    (r : SecondPrimalBarrierInnerRun P C σ (f + b)) {L : ℝ} (hf : ∀ j, L ≤ f (r.x j))
    (hb : BarrierDivergesAtBoundary C b) (H : ℕ → E →L[ℝ] E)
    (hm : ∀ j v, r.model j (r.x j + v) =
      quadraticModel (r.model j (r.x j)) (r.g j) (H j).toLinearMap v)
    (sC : ℕ → E)
    (hs : ∀ j, IsConstrainedBarrierCauchyStep (fun v ↦ r.model j (r.x j + v)) (r.g j)
      (r.Δ j) σ (infDist (r.x j) (frontier C)) (sC j)) :
    ∃ κmdc > 0, ∃ κmdb > 0, ∀ j, κmdb ≤ infDist (r.x j) (frontier C) ∧
      let π := min ‖r.g j‖ ((1 - σ) * κmdb)
      κmdc * π * min (π / quadraticCurvatureBound (H j)) (r.Δ j) ≤
        r.model j (r.x j) - r.model j (r.x j + sC j) := by
  obtain ⟨ε, hε, hdist⟩ := r.toPrimalBarrierInnerRun.boundary_separation hf hb
  refine ⟨1 / 2, by norm_num, ε, hε.1, fun j ↦ ⟨hdist j, ?_⟩⟩
  dsimp only
  let π := min ‖r.g j‖ ((1 - σ) * ε)
  let β := quadraticCurvatureBound (H j)
  have hβ : 1 ≤ β := by unfold β quadraticCurvatureBound; linarith [norm_nonneg (H j)]
  have hβ' : 0 < β := zero_lt_one.trans_le hβ
  have hΔ := (norm_nonneg _).trans (r.step_feasible j)
  have hπ : 0 ≤ π := le_min (norm_nonneg _) (by positivity [r.fraction.2, hε.1])
  have hbound : π / β ≤ (1 - σ) * infDist (r.x j) (frontier C) := calc
    π / β ≤ π := (div_le_self hπ hβ)
    _ ≤ (1 - σ) * ε := min_le_right _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hdist j) (sub_nonneg.mpr r.fraction.2.le)
  have hmin : min (π / β) (r.Δ j) ≤
      min (‖r.g j‖ / β) (constrainedBarrierRadius (r.Δ j) σ (infDist (r.x j) (frontier C))) := by
    exact le_min ((min_le_left _ _).trans (div_le_div_of_nonneg_right (min_le_left _ _) hβ'.le))
      (le_min (min_le_right _ _) ((min_le_left _ _).trans hbound))
  have hmodel : (fun v ↦ r.model j (r.x j + v)) =
      quadraticModel (r.model j (r.x j)) (r.g j) (H j).toLinearMap := funext (hm j)
  have hsj := hs j
  rw [hmodel] at hsj
  have hc := theorem_13_3_1 (r.model j (r.x j)) (r.g j) (H j) hΔ r.fraction.2.le
    infDist_nonneg hsj
  rw [← hm] at hc
  exact (mul_le_mul (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)) hmin
    (le_min (div_nonneg hπ hβ'.le) hΔ) (by positivity)).trans hc

/-- A constrained eigenstep minimizes the displacement model on the segment
from the origin to the chosen direction. -/
def IsConstrainedBarrierEigenstep (m : E → ℝ) (u s : E) : Prop :=
  IsMinOn m ((fun t : ℝ ↦ t • u) '' Icc 0 1) s ∧ s ∈ (fun t : ℝ ↦ t • u) '' Icc 0 1

/-- Theorem 13.3.3. The decrease at the constrained eigenpoint dominates
the decrease at the end of the negative-curvature segment. The model
direction hypotheses are precisely the conditions in (13.3.20) and the
inequality that follows it. -/
theorem theorem_13_3_3 (c : ℝ) (g u : E) (H : E →ₗ[ℝ] E) {Δ σ d κ τ : ℝ}
    (_hκ : κ ∈ Ioc (0 : ℝ) 1) (_hτ : τ < 0)
    (hg : inner ℝ u g ≤ 0) (_hu : ‖u‖ = constrainedBarrierRadius Δ σ d)
    (hh : inner ℝ u (H u) ≤ κ * τ * constrainedBarrierRadius Δ σ d ^ 2)
    {s : E} (hs : IsConstrainedBarrierEigenstep (quadraticModel c g H) u s) :
    -(1 / 2 : ℝ) * κ * τ * constrainedBarrierRadius Δ σ d ^ 2 ≤ c - quadraticModel c g H s := by
  have hmin : quadraticModel c g H s ≤ quadraticModel c g H u :=
    isMinOn_iff.mp hs.1 _ ⟨1, ⟨zero_le_one, le_rfl⟩, one_smul ℝ u⟩
  rw [real_inner_comm] at hg
  simp only [quadraticModel] at hmin ⊢
  linarith

end ConnGouldToint.Chapter13
