import Numlib.Optimization.Quadratic.Secular.Transform
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Geometry and endpoint limits of transformed secular functions

Positive powers are strictly decreasing and strictly convex. Negative powers are
strictly increasing, and exponents from minus one half to zero give concavity.
The limits at infinity are zero and positive infinity respectively. The lower
spectral endpoint is represented by an actual extended-real right-hand limit.
-/

open scoped BigOperators Topology
open Filter
namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [FiniteDimensional ℝ E]
  {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The actual inverse-defined transform equals the real power of its proved spectral
expression above the edge. -/
theorem transformed_eq (g : E) (β : ℝ) {z : ℝ} (hz : B.edge < z) :
    transformed H M g β z = (B.spectralSum g z)^β := by
  unfold transformed
  rw [B.secular_eq_sum z (fun i => ne_of_gt (B.denominator_pos hz i)) g]
  rfl

/-- The actual transformed function is continuously differentiable to every finite order above
the edge when the gradient is nonzero. -/
theorem contDiffAt_transformed {g : E} (hg : g ≠ 0) (β : ℝ) (n : ℕ)
    {z : ℝ} (hz : B.edge < z) : ContDiffAt ℝ n (transformed H M g β) z := by
  apply ((B.contDiffAt_spectralSum g n hz).rpow_const_of_ne
    (p := β) (B.spectralSum_pos hg hz).ne').congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  exact B.transformed_eq g β hy

/-- Positive powers of the actual secular function are strictly decreasing above the edge for
a nonzero gradient. -/
theorem strictAntiOn_transformed {g : E} (hg : g ≠ 0) {β : ℝ} (hβ : 0 < β) :
    StrictAntiOn (transformed H M g β) (Set.Ioi B.edge) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi B.edge)
    (fun z hz => (B.contDiffAt_transformed hg β 1 hz).continuousAt.continuousWithinAt)
  intro z hz
  exact (((B.transformed_derivative_signs g β (interior_subset hz)).1 hβ).2.2 hg).1

/-- Negative powers of the actual secular function are strictly increasing above the edge for
a nonzero gradient. -/
theorem strictMonoOn_transformed {g : E} (hg : g ≠ 0) {β : ℝ} (hβ : β < 0) :
    StrictMonoOn (transformed H M g β) (Set.Ioi B.edge) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi B.edge)
    (fun z hz => (B.contDiffAt_transformed hg β 1 hz).continuousAt.continuousWithinAt)
  intro z hz
  exact ((B.transformed_derivative_signs g β (interior_subset hz)).2 hβ hg).1

/-- Every positive power of the actual secular function is strictly convex on the entire open
spectral interval for a nonzero gradient. -/
theorem strictConvexOn_transformed {g : E} (hg : g ≠ 0) {β : ℝ} (hβ : 0 < β) :
    StrictConvexOn ℝ (Set.Ioi B.edge) (transformed H M g β) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi B.edge)
    (fun z hz => (B.contDiffAt_transformed hg β 1 hz).continuousAt.continuousWithinAt)
  intro z hz
  rw [← iteratedDeriv_eq_iterate]
  exact (((B.transformed_derivative_signs g β hz).1 hβ).2.2 hg).2

/-- The actual transformed function is concave for exponents from minus one half to zero and a
nonzero gradient. -/
theorem concaveOn_transformed {g : E} (hg : g ≠ 0) {β : ℝ}
    (hβ : β < 0) (hβlow : -(1 / 2 : ℝ) ≤ β) :
    ConcaveOn ℝ (Set.Ioi B.edge) (transformed H M g β) := by
  apply concaveOn_of_deriv2_nonpos' (convex_Ioi B.edge)
    (fun z hz => (B.contDiffAt_transformed hg β 1 hz).differentiableAt_one.differentiableWithinAt)
    (fun z hz => ((B.contDiffAt_transformed hg β 2 hz).derivWithin
      (m := 1) (by norm_num)).differentiableAt_one.differentiableWithinAt)
  intro z hz
  rw [← iteratedDeriv_eq_iterate]
  exact (((B.transformed_derivative_signs g β hz).2 hβ hg).2 hβlow).1

/-- The actual transformed function is strictly concave for exponents strictly between minus
one half and zero and a nonzero gradient. -/
theorem strictConcaveOn_transformed {g : E} (hg : g ≠ 0) {β : ℝ}
    (hβ : β < 0) (hβlow : -(1 / 2 : ℝ) < β) :
    StrictConcaveOn ℝ (Set.Ioi B.edge) (transformed H M g β) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi B.edge)
    (fun z hz => (B.contDiffAt_transformed hg β 1 hz).continuousAt.continuousWithinAt)
  intro z hz
  rw [← iteratedDeriv_eq_iterate]
  exact ((((B.transformed_derivative_signs g β hz).2 hβ hg).2 hβlow.le).2.1 hβlow)

include B in
omit [Fintype ι] in
/-- Every positive power of the actual secular function tends to zero at infinity. -/
theorem transformed_tendsto_zero [Finite ι] (g : E) {β : ℝ} (hβ : 0 < β) :
    Tendsto (transformed H M g β) atTop (𝓝 0) := by
  let := Fintype.ofFinite ι
  have hh := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.comp
    (B.tendsto_spectralSum_zero g)
  rw [Real.zero_rpow hβ.ne'] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop B.edge] with y hy
  exact (B.transformed_eq g β hy).symm

include B in
omit [Fintype ι] in
/-- Every negative power of a nonzero actual secular function tends to positive infinity. -/
theorem transformed_tendsto_atTop [Finite ι] {g : E} (hg : g ≠ 0) {β : ℝ} (hβ : β < 0) :
    Tendsto (transformed H M g β) atTop atTop := by
  let := Fintype.ofFinite ι
  have hp : Tendsto (B.spectralSum g) atTop (𝓝[Set.Ioi 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨B.tendsto_spectralSum_zero g, ?_⟩
    filter_upwards [eventually_gt_atTop B.edge] with y hy
    exact B.spectralSum_pos hg hy
  have hh := (tendsto_rpow_neg_nhdsGT_zero hβ).comp hp
  apply hh.congr'
  filter_upwards [eventually_gt_atTop B.edge] with y hy
  exact (B.transformed_eq g β hy).symm

/-- For every nonzero exponent and gradient the actual transform has an extended-real right-
hand limit at the spectral endpoint; no singular inverse is evaluated there. -/
theorem transformed_right_limit {g : E} (hg : g ≠ 0) {β : ℝ} (hβ : β ≠ 0) :
    ∃ l : EReal, Tendsto (fun z => (transformed H M g β z : EReal))
      (𝓝[Set.Ioi B.edge] B.edge) (𝓝 l) := by
  have hne : (Set.Ioo B.edge (B.edge + 1)).Nonempty :=
    ⟨B.edge + 1 / 2, by constructor <;> linarith⟩
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  · have hm : MonotoneOn (fun z => (transformed H M g β z : EReal))
        (Set.Ioo B.edge (B.edge + 1)) := by
      intro u hu v hv huv
      exact EReal.coe_le_coe_iff.mpr ((B.strictMonoOn_transformed hg hneg).monotoneOn
        hu.1 hv.1 huv)
    exact ⟨_, hm.tendsto_nhdsWithin_Ioo_right hne ⟨⊥, fun _ _ => bot_le⟩⟩
  · have hm : AntitoneOn (fun z => (transformed H M g β z : EReal))
        (Set.Ioo B.edge (B.edge + 1)) := by
      intro u hu v hv huv
      exact EReal.coe_le_coe_iff.mpr ((B.strictAntiOn_transformed hg hpos).antitoneOn
        hu.1 hv.1 huv)
    exact ⟨_, hm.tendsto_nhdsWithin_Ioo_right hne ⟨⊤, fun _ _ => le_top⟩⟩

end QuadraticSecular.PencilBasis
