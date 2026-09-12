import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.Interpolation
import Numlib.IntegralEquations.Basic
import Numlib.IntegralEquations.L2Kernel

/-!
# The `L²` projections onto the piecewise linear functions

The piecewise linear functions of a partition `a = x₀ < x₁ < ⋯ < x_{n+1} = b`, seen inside `L²(a,
b)`, form a finite-dimensional subspace, and the orthogonal projection onto it is the **Galerkin
projection** of the partition: the best `L²` approximation by piecewise linear functions.  It is
what a Galerkin method for an equation of the second kind discretizes with, and it is cheaper to
control than the interpolation projection of `Numlib/Approximation/Interpolation`, because an
orthogonal projection has norm one whatever the mesh.

Two trial spaces are built here, differing only in whether continuity at the breakpoints is
imposed: `piecewiseLinearLp` is spanned by the constant function and the clamped ramps of the
subintervals, and `discPiecewiseLinearLp` is spanned by the constant and the coordinate function
restricted to each panel separately, so that it contains the first.  The
point of the discontinuous space is that it is an orthogonal direct sum over the panels, so that
its Galerkin matrix is block diagonal; the point of the continuous one is that it is half the size.

Both facts a projection method asks for come from interpolation, through one lemma,
`norm_sub_starProjection_le_of_iccToLp_mem`: the orthogonal projection onto a subspace of
`L²(a, b)` is at least as good as *any* continuous function whose class lies in that subspace, and
a uniform bound is an `L²` bound (`IntegralOperator.norm_iccToLp_le`).  Applied to the continuous
piecewise linear interpolant, which lies in both spaces, it gives

* `‖f - P_n f‖_{L²} ≤ √(b - a) ‖f - I_n f‖_∞` for either projection;
* hence `P_n → 1` pointwise on the continuous functions, and, the projections having norm one and
  the continuous functions being dense in `L²`, on the whole of `L²(a, b)`.

The last section turns the first of these into an operator estimate: for a kernel operator `K` on
`L²(a, b)` and a self-adjoint `Q`, `‖K Q‖ ≤ √(b - a) sup_x ‖Q k(x, ·)‖`, because
`K Q v (x) = ⟪Q k(x, ·), v⟫`.  With `Q = I - P_n` and a kernel twice continuously differentiable in
its second variable this reads `‖K (I - P_n)‖ = 𝒪(h²)`, which is what a superconvergence argument
for an iterated Galerkin method needs.

## Main definitions

* `IntegralOperator.iccIndicatorLp a b hs g` — the class in `L²(a, b)` of a continuous function cut
  down to a measurable set, the building block of a discontinuous trial space.
* `meshPanel x i` — the half-open panel `[x i, x (i + 1))` of a partition; the panels of
  `x 0, …, x (n + 1)` partition `[a, b)` up to a null set, which is `sum_iccIndicatorLp_meshPanel`.
* `piecewiseLinearLp a b n x` — the continuous trial space: the span, inside `L²(a, b)`, of the
  constant function and the clamped ramps `piecewiseLinearRamp` of the subintervals, which is the
  image of the range of `piecewiseLinearInterpCLM`.
* `discPiecewiseLinearLp a b n x` — the discontinuous trial space: the span of the constant and the
  coordinate function restricted to each panel.
* `piecewiseLinearProjCLM a b n x` and `discPiecewiseLinearProjCLM a b n x` — the orthogonal
  projections onto them.

## Main statements

* `isIdempotentElem_piecewiseLinearProjCLM`, `norm_piecewiseLinearProjCLM_le_one` and their
  discontinuous twins, together with `isSelfAdjoint_discPiecewiseLinearProjCLM` — each is a
  projection of norm at most one, self-adjoint because orthogonal.
* `norm_sub_piecewiseLinearProjCLM_le` and `norm_sub_discPiecewiseLinearProjCLM_le` —
  `‖f - P_n f‖_{L²} ≤ √(b - a) ‖f - I_n f‖_∞`, the approximation property of either projection.
* `tendsto_piecewiseLinearProjCLM` and `tendsto_discPiecewiseLinearProjCLM` — for a sequence of
  partitions of vanishing mesh the projections converge pointwise to the identity on the whole of
  `L²(a, b)`; both are instances of `tendsto_starProjection_of_piecewiseLinearInterpCLM_mem`.
* `norm_l2KernelCLM_comp_le` — `‖K Q‖ ≤ √(b - a) sup_x ‖Q k(x, ·)‖` for a self-adjoint `Q`, and
  `norm_l2KernelCLM_comp_sub_discPiecewiseLinearProjCLM_le`, its consequence
  `‖K (I - P_n)‖ ≤ (b - a) h² ‖∂²_y k‖ / 8` for the discontinuous Galerkin projection.

## References

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009 ([han2009theoretical]), §12.2.3, equations (12.2.18) and
(12.2.19), for the continuous projection; §12.3.1 and Example 12.3.2 for the discontinuous one and
for the operator estimate `‖K (I - P_n)‖ = 𝒪(h²)`, which the book states there without proof.
-/

open Filter MeasureTheory Topology

open IntegralOperator

variable {a b : ℝ}

namespace IntegralOperator

/-! ### Continuous functions and their indicators inside `L²(a, b)` -/

/-- The class in `L²(a, b)` of a continuous function is, almost everywhere, that function. -/
theorem coeFn_iccToLp (g : C(Set.Icc a b, ℝ)) :
    iccToLp a b g =ᵐ[iccMeasure a b] (g : Set.Icc a b → ℝ) :=
  ContinuousMap.coeFn_toLp (𝕜 := ℝ) (iccMeasure a b) g

/-- A continuous function on a compact interval is square-integrable for Lebesgue measure. -/
theorem memLp_iccToLp (g : C(Set.Icc a b, ℝ)) :
    MemLp (g : Set.Icc a b → ℝ) 2 (iccMeasure a b) :=
  (Lp.memLp (iccToLp a b g)).ae_eq (coeFn_iccToLp g)

/-- A continuous kernel on the compact square is square-integrable for the product of Lebesgue
measures, which is the hypothesis of `IntegralOperator.l2KernelCLM`. -/
theorem memLp_prod_iccMeasure (k : C(Set.Icc a b × Set.Icc a b, ℝ)) :
    MemLp k 2 ((iccMeasure a b).prod (iccMeasure a b)) :=
  MemLp.of_bound (map_continuous k).aestronglyMeasurable ‖k‖
    (Filter.Eventually.of_forall fun z => k.norm_coe_le_norm z)

/-- **A continuous function cut down to a measurable set, as an element of `L²(a, b)`.**  A
discontinuous trial space is spanned by such classes: the pieces of a piecewise polynomial are
continuous, and it is the cutting alone that makes the whole discontinuous. -/
noncomputable def iccIndicatorLp (a b : ℝ) {s : Set (Set.Icc a b)} (hs : MeasurableSet s)
    (g : C(Set.Icc a b, ℝ)) : Lp ℝ 2 (iccMeasure a b) :=
  ((memLp_iccToLp g).indicator hs).toLp _

/-- The defining formula of `IntegralOperator.iccIndicatorLp`, almost everywhere. -/
theorem coeFn_iccIndicatorLp {s : Set (Set.Icc a b)} (hs : MeasurableSet s)
    (g : C(Set.Icc a b, ℝ)) :
    iccIndicatorLp a b hs g =ᵐ[iccMeasure a b] s.indicator (g : Set.Icc a b → ℝ) :=
  MemLp.coeFn_toLp _

/-- Only the values on the set matter: two continuous functions agreeing on `s` have the same
indicator class. -/
theorem iccIndicatorLp_congr {s : Set (Set.Icc a b)} (hs : MeasurableSet s)
    {g₁ g₂ : C(Set.Icc a b, ℝ)} (h : ∀ t ∈ s, g₁ t = g₂ t) :
    iccIndicatorLp a b hs g₁ = iccIndicatorLp a b hs g₂ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_iccIndicatorLp hs g₁, coeFn_iccIndicatorLp hs g₂] with t h1 h2
  rw [h1, h2]
  by_cases ht : t ∈ s
  · simp [Set.indicator_of_mem ht, h t ht]
  · simp [Set.indicator_of_notMem ht]

/-- `IntegralOperator.iccIndicatorLp` is additive in the function. -/
theorem iccIndicatorLp_add {s : Set (Set.Icc a b)} (hs : MeasurableSet s)
    (g₁ g₂ : C(Set.Icc a b, ℝ)) :
    iccIndicatorLp a b hs (g₁ + g₂) = iccIndicatorLp a b hs g₁ + iccIndicatorLp a b hs g₂ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_iccIndicatorLp hs (g₁ + g₂), coeFn_iccIndicatorLp hs g₁,
    coeFn_iccIndicatorLp hs g₂, Lp.coeFn_add (iccIndicatorLp a b hs g₁) (iccIndicatorLp a b hs g₂)]
    with t h0 h1 h2 h3
  rw [h3, Pi.add_apply, h0, h1, h2]
  by_cases ht : t ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]

/-- `IntegralOperator.iccIndicatorLp` is homogeneous in the function. -/
theorem iccIndicatorLp_smul {s : Set (Set.Icc a b)} (hs : MeasurableSet s) (c : ℝ)
    (g : C(Set.Icc a b, ℝ)) :
    iccIndicatorLp a b hs (c • g) = c • iccIndicatorLp a b hs g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_iccIndicatorLp hs (c • g), coeFn_iccIndicatorLp hs g,
    Lp.coeFn_smul c (iccIndicatorLp a b hs g)] with t h0 h1 h2
  rw [h2, Pi.smul_apply, h0, h1]
  by_cases ht : t ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]

/-- The coefficient functions of `L²(a, b)` are pointwise sums almost everywhere. -/
private theorem coeFn_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → Lp ℝ 2 (iccMeasure a b)) :
    ⇑(∑ i ∈ s, F i) =ᵐ[iccMeasure a b] fun y => ∑ i ∈ s, F i y := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 (iccMeasure a b)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with y h1 h2
    rw [h1, Finset.sum_insert hi, Pi.add_apply, h2]

end IntegralOperator

/-! ### Best approximation in `L²(a, b)` by a continuous element of the subspace -/

/-- **An orthogonal projection of `L²(a, b)` is at least as good as any continuous function whose
class lies in the subspace**, and a uniform bound is an `L²` bound, so

`‖f - P f‖_{L²} ≤ ‖f - g‖_{L²} ≤ √(b - a) ‖f - g‖_∞`  whenever `[g] ∈ V`.

Every uniform-norm approximation theorem therefore becomes an `L²` bound on the orthogonal
projection onto a subspace containing the approximant, at the cost of one factor `√(b - a)`.  This
is the only approximation-theoretic input either Galerkin projection of this file needs;
[han2009theoretical], §12.2.3, equation (12.2.18). -/
theorem norm_sub_starProjection_le_of_iccToLp_mem (hab : a ≤ b)
    (V : Submodule ℝ (Lp ℝ 2 (IntegralOperator.iccMeasure a b))) [V.HasOrthogonalProjection]
    (f : C(Set.Icc a b, ℝ)) {g : C(Set.Icc a b, ℝ)} (hg : iccToLp a b g ∈ V) :
    ‖iccToLp a b f - V.starProjection (iccToLp a b f)‖ ≤ √(b - a) * ‖f - g‖ := by
  refine ((isBestApprox_starProjection V (iccToLp a b f)).2 _ hg).trans ?_
  rw [← map_sub]
  exact norm_iccToLp_le hab _

/-! ### The continuous piecewise linear functions -/

/-- **The continuous piecewise linear functions of the partition, inside `L²(a, b)`.**  The span of
the images of the constant `1` and of the clamped ramps of the subintervals, which is exactly the
image under `iccToLp` of the range of `piecewiseLinearInterpCLM`. -/
noncomputable def piecewiseLinearLp (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Submodule ℝ (Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :=
  Submodule.span ℝ (iccToLp a b '' insert (1 : C(Set.Icc a b, ℝ))
    ((fun i => piecewiseLinearRamp a b (x i) (x (i + 1))) '' Set.Iic n))

instance (n : ℕ) (x : ℕ → Set.Icc a b) : FiniteDimensional ℝ (piecewiseLinearLp a b n x) :=
  FiniteDimensional.span_of_finite ℝ
    ((((Set.finite_Iic n).image _).insert _).image _)

instance (n : ℕ) (x : ℕ → Set.Icc a b) : (piecewiseLinearLp a b n x).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- **The `L²`-orthogonal projection onto the piecewise linear functions of the partition**: the
Galerkin projection of the partition, the `P_n` of [han2009theoretical], §12.2.3. -/
noncomputable def piecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ] Lp ℝ 2 (IntegralOperator.iccMeasure a b) :=
  (piecewiseLinearLp a b n x).starProjection

/-- The Galerkin projection is a projection. -/
theorem isIdempotentElem_piecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    IsIdempotentElem (piecewiseLinearProjCLM a b n x) :=
  Submodule.isIdempotentElem_starProjection _

/-- **An orthogonal projection has norm at most one**, which is where the Galerkin projection is
cheaper than the interpolation projection `piecewiseLinearInterpCLM`: no Lebesgue constant
enters. -/
theorem norm_piecewiseLinearProjCLM_le_one (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    ‖piecewiseLinearProjCLM a b n x‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- The image of a piecewise linear interpolant lies in the trial space. -/
theorem iccToLp_piecewiseLinearInterpCLM_mem (n : ℕ) (x : ℕ → Set.Icc a b)
    (f : C(Set.Icc a b, ℝ)) :
    iccToLp a b (piecewiseLinearInterpCLM n x f) ∈ piecewiseLinearLp a b n x := by
  have hgen : ∀ z ∈ insert (1 : C(Set.Icc a b, ℝ))
      ((fun i => piecewiseLinearRamp a b (x i) (x (i + 1))) '' Set.Iic n),
      iccToLp a b z ∈ piecewiseLinearLp a b n x := fun z hz =>
    Submodule.subset_span ⟨z, hz, rfl⟩
  have hone : iccToLp a b (1 : C(Set.Icc a b, ℝ)) ∈ piecewiseLinearLp a b n x :=
    hgen _ (Set.mem_insert _ _)
  have hramp : ∀ i ∈ Finset.range (n + 1),
      iccToLp a b (piecewiseLinearRamp a b (x i) (x (i + 1))) ∈ piecewiseLinearLp a b n x := by
    intro i hi
    exact hgen _ (Set.mem_insert_of_mem _ ⟨i, Set.mem_Iic.2 (Nat.lt_succ_iff.1
      (Finset.mem_range.1 hi)), rfl⟩)
  have hval : piecewiseLinearInterpCLM n x f
      = f (x 0) • (1 : C(Set.Icc a b, ℝ)) + ∑ i ∈ Finset.range (n + 1),
        (((x (i + 1) : ℝ) - (x i : ℝ))⁻¹ * (f (x (i + 1)) - f (x i))) •
          piecewiseLinearRamp a b (x i) (x (i + 1)) := by
    simp [piecewiseLinearInterpCLM, mul_smul]
  rw [hval, map_add, map_smul, map_sum]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ hone) (Submodule.sum_mem _ fun i hi => ?_)
  rw [map_smul]
  exact Submodule.smul_mem _ _ (hramp i hi)

/-- **The approximation property of the Galerkin projection**: the orthogonal projection is at
least as good as the interpolant, and a uniform bound is an `L²` bound, so

`‖f - P_n f‖_{L²} ≤ ‖f - I_n f‖_{L²} ≤ √(b - a) ‖f - I_n f‖_∞`.

Every uniform-norm bound on piecewise linear interpolation therefore becomes an `L²` bound on the
Galerkin projection, at the cost of one factor `√(b - a)`; [han2009theoretical], §12.2.3,
equation (12.2.18). -/
theorem norm_sub_piecewiseLinearProjCLM_le (hab : a ≤ b) (n : ℕ) (x : ℕ → Set.Icc a b)
    (f : C(Set.Icc a b, ℝ)) :
    ‖iccToLp a b f - piecewiseLinearProjCLM a b n x (iccToLp a b f)‖
      ≤ √(b - a) * ‖f - piecewiseLinearInterpCLM n x f‖ :=
  norm_sub_starProjection_le_of_iccToLp_mem hab (piecewiseLinearLp a b n x) f
    (iccToLp_piecewiseLinearInterpCLM_mem n x f)

/-! ### The panels of a partition -/

/-- **The `i`-th panel of a partition**, the half-open subinterval `[x i, x (i + 1))` read inside
`Set.Icc a b`.  Half-open rather than closed so that the panels of an increasing partition are
pairwise disjoint on the nose, and so cover `[a, b)` exactly once. -/
def meshPanel (x : ℕ → Set.Icc a b) (i : ℕ) : Set (Set.Icc a b) :=
  Subtype.val ⁻¹' Set.Ico (x i : ℝ) (x (i + 1) : ℝ)

/-- Membership in a panel, unfolded. -/
theorem mem_meshPanel {x : ℕ → Set.Icc a b} {i : ℕ} {t : Set.Icc a b} :
    t ∈ meshPanel x i ↔ (x i : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) < (x (i + 1) : ℝ) := Iff.rfl

/-- A panel is measurable, being the preimage of an interval under the inclusion. -/
theorem measurableSet_meshPanel (x : ℕ → Set.Icc a b) (i : ℕ) :
    MeasurableSet (meshPanel x i) :=
  measurableSet_Ico.preimage measurable_subtype_coe

/-- The nodes of a partition increase along the used range. -/
private theorem node_mono {n : ℕ} {x : ℕ → Set.Icc a b}
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n + 1) :
    (x i : ℝ) ≤ (x j : ℝ) := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ k hk ih => exact fun hk1 => (ih (by omega)).trans (hstep k (by omega)).le

/-- **Every point of `[a, b)` lies in a panel.**  The endpoint `b` lies in none of them, which is
why the statement excludes it; it is a null set, so nothing is lost in `L²`. -/
theorem exists_mem_meshPanel {n : ℕ} {x : ℕ → Set.Icc a b}
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) {t : Set.Icc a b} (ht : (t : ℝ) ≠ b) :
    ∃ j ≤ n, t ∈ meshPanel x j := by
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hfirst hlast t
  rcases lt_or_eq_of_le h2 with h | h
  · exact ⟨j, hj, ⟨h1, h⟩⟩
  · have hjn : j ≠ n := by
      rintro rfl
      exact ht (by rw [h, hlast])
    exact ⟨j + 1, by omega, ⟨h.ge, h ▸ hstep (j + 1) (by omega)⟩⟩

/-- **The panels of an increasing partition are pairwise disjoint.** -/
theorem notMem_meshPanel_of_mem {n : ℕ} {x : ℕ → Set.Icc a b}
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (hij : i ≠ j) {t : Set.Icc a b} (htj : t ∈ meshPanel x j) : t ∉ meshPanel x i := by
  intro hti
  rcases lt_or_gt_of_ne hij with h | h
  · exact absurd (hti.2.trans_le ((node_mono hstep h (by omega)).trans htj.1)) (lt_irrefl _)
  · exact absurd (htj.2.trans_le ((node_mono hstep h (by omega)).trans hti.1)) (lt_irrefl _)

/-- **`L²(a, b)` splits over the panels**: the pieces of a continuous function on the panels of a
partition sum back to the function, because the panels are disjoint and cover `[a, b)`, whose
complement in `[a, b]` is a null set.  This is what makes a panel-by-panel trial space contain the
global objects built from it. -/
theorem sum_iccIndicatorLp_meshPanel {n : ℕ} {x : ℕ → Set.Icc a b}
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) (g : C(Set.Icc a b, ℝ)) :
    ∑ i ∈ Finset.range (n + 1), iccIndicatorLp a b (measurableSet_meshPanel x i) g
      = iccToLp a b g := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  refine Lp.ext ?_
  have hall : ∀ᵐ t ∂(iccMeasure a b), ∀ i ∈ Finset.range (n + 1),
      (iccIndicatorLp a b (measurableSet_meshPanel x i) g) t
        = (meshPanel x i).indicator (g : Set.Icc a b → ℝ) t :=
    (Filter.eventually_all_finset _).2 fun i _ => coeFn_iccIndicatorLp _ g
  filter_upwards [coeFn_finset_sum (Finset.range (n + 1))
      (fun i => iccIndicatorLp a b (measurableSet_meshPanel x i) g), hall, coeFn_iccToLp g,
    ae_ne_iccMeasure (⟨b, ⟨hab, le_rfl⟩⟩ : Set.Icc a b)] with t hsum hind htoLp htb
  rw [hsum, htoLp]
  obtain ⟨j, hj, hmem⟩ := exists_mem_meshPanel hstep hfirst hlast htb
  rw [Finset.sum_congr rfl hind, Finset.sum_eq_single j
    (fun i hi hij => Set.indicator_of_notMem (notMem_meshPanel_of_mem hstep
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hj hij hmem) _)
    (fun hcon => absurd (Finset.mem_range.2 (by omega)) hcon)]
  exact Set.indicator_of_mem hmem _

/-! ### The discontinuous piecewise linear functions -/

/-- The coordinate function of `Set.Icc a b`, whose restrictions to the panels are, together with
the restrictions of the constant `1`, the natural basis of the discontinuous piecewise linear
functions. -/
def iccCoord (a b : ℝ) : C(Set.Icc a b, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem iccCoord_apply (a b : ℝ) (t : Set.Icc a b) : iccCoord a b t = (t : ℝ) := rfl

/-- **The discontinuous piecewise linear functions of the partition, inside `L²(a, b)`.**  The span
of the restrictions to each panel of the constant `1` and of the coordinate function: a function of
this space is affine on every panel, with no continuity imposed across the breakpoints, so the
space is, for a strictly increasing partition, the direct sum of the two-dimensional spaces of the
`n + 1` panels, of dimension `2 (n + 1)`; that count is not proved here, only the membership
statements the approximation theory uses.

This is the trial space of the discontinuous piecewise linear Galerkin method of
[han2009theoretical], §12.3.1, Example 12.3.2, where a mesh of `n` subintervals of `[0, 1]` gives
dimension `2 n`, twice that of the continuous piecewise linear space of §12.2.3. -/
noncomputable def discPiecewiseLinearLp (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Submodule ℝ (Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :=
  Submodule.span ℝ (⋃ i ∈ Set.Iic n,
    ({iccIndicatorLp a b (measurableSet_meshPanel x i) 1,
      iccIndicatorLp a b (measurableSet_meshPanel x i) (iccCoord a b)} :
        Set (Lp ℝ 2 (IntegralOperator.iccMeasure a b))))

instance (n : ℕ) (x : ℕ → Set.Icc a b) :
    FiniteDimensional ℝ (discPiecewiseLinearLp a b n x) :=
  FiniteDimensional.span_of_finite ℝ
    ((Set.finite_Iic n).biUnion fun _ _ => (Set.finite_singleton _).insert _)

instance (n : ℕ) (x : ℕ → Set.Icc a b) :
    (discPiecewiseLinearLp a b n x).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- **A function that is affine on one panel belongs, once cut down to that panel, to the
discontinuous trial space.** -/
theorem iccIndicatorLp_mem_discPiecewiseLinearLp {n : ℕ} {x : ℕ → Set.Icc a b} {i : ℕ}
    (hi : i ≤ n) {c d : ℝ} {g : C(Set.Icc a b, ℝ)}
    (hg : ∀ t ∈ meshPanel x i, g t = c + d * (t : ℝ)) :
    iccIndicatorLp a b (measurableSet_meshPanel x i) g ∈ discPiecewiseLinearLp a b n x := by
  have hgen : ∀ z ∈ ({iccIndicatorLp a b (measurableSet_meshPanel x i) 1,
      iccIndicatorLp a b (measurableSet_meshPanel x i) (iccCoord a b)} :
        Set (Lp ℝ 2 (IntegralOperator.iccMeasure a b))),
      z ∈ discPiecewiseLinearLp a b n x := fun z hz =>
    Submodule.subset_span (Set.mem_biUnion (Set.mem_Iic.2 hi) hz)
  have hrw : iccIndicatorLp a b (measurableSet_meshPanel x i) g
      = c • iccIndicatorLp a b (measurableSet_meshPanel x i) 1
        + d • iccIndicatorLp a b (measurableSet_meshPanel x i) (iccCoord a b) := by
    rw [← iccIndicatorLp_smul, ← iccIndicatorLp_smul, ← iccIndicatorLp_add]
    exact iccIndicatorLp_congr _ fun t ht => by simpa using hg t ht
  rw [hrw]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hgen _ (Set.mem_insert _ _)))
    (Submodule.smul_mem _ _ (hgen _ (Set.mem_insert_of_mem _ rfl)))

/-- **The image of a continuous piecewise linear interpolant lies in the discontinuous trial
space**, which is the inclusion of the continuous piecewise linear functions in the discontinuous
ones: on each panel the interpolant is the affine function through the two node values. -/
theorem iccToLp_piecewiseLinearInterpCLM_mem_disc {n : ℕ} {x : ℕ → Set.Icc a b}
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) (f : C(Set.Icc a b, ℝ)) :
    iccToLp a b (piecewiseLinearInterpCLM n x f) ∈ discPiecewiseLinearLp a b n x := by
  rw [← sum_iccIndicatorLp_meshPanel hstep hfirst hlast]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hd : (x (i + 1) : ℝ) - (x i : ℝ) ≠ 0 := sub_ne_zero.2 (hstep i hin).ne'
  set D : ℝ := (f (x (i + 1)) - f (x i)) / ((x (i + 1) : ℝ) - (x i : ℝ)) with hD
  refine iccIndicatorLp_mem_discPiecewiseLinearLp hin
    (c := f (x i) - D * (x i : ℝ)) (d := D) fun t ht => ?_
  rw [piecewiseLinearInterpCLM_apply_of_mem hstep f hin ht.1 ht.2.le, hD]
  field_simp
  ring

/-- **The `L²`-orthogonal projection onto the discontinuous piecewise linear functions of the
partition**: the Galerkin projection of the discontinuous piecewise linear method of
[han2009theoretical], §12.3.1, Example 12.3.2.  Because the trial space is the orthogonal direct
sum of the panel spaces, this projection acts panel by panel. -/
noncomputable def discPiecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ] Lp ℝ 2 (IntegralOperator.iccMeasure a b) :=
  (discPiecewiseLinearLp a b n x).starProjection

/-- The discontinuous Galerkin projection is a projection. -/
theorem isIdempotentElem_discPiecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    IsIdempotentElem (discPiecewiseLinearProjCLM a b n x) :=
  Submodule.isIdempotentElem_starProjection _

/-- **The discontinuous Galerkin projection is self-adjoint**, being orthogonal.  This is what
turns `‖K (I - P_n)‖` into `‖(I - P_n) K*‖` in a superconvergence argument;
[han2009theoretical], §12.3.1, equation (12.3.13). -/
theorem isSelfAdjoint_discPiecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    IsSelfAdjoint (discPiecewiseLinearProjCLM a b n x) :=
  isSelfAdjoint_starProjection _

/-- **An orthogonal projection has norm at most one**, whatever the mesh: no Lebesgue constant
enters. -/
theorem norm_discPiecewiseLinearProjCLM_le_one (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    ‖discPiecewiseLinearProjCLM a b n x‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- **The approximation property of the discontinuous Galerkin projection**, of the same shape as
`norm_sub_piecewiseLinearProjCLM_le` and with the same constant: the discontinuous trial space
contains the continuous piecewise linear interpolant, so the projection onto it is at least as
good,

`‖f - P_n f‖_{L²} ≤ √(b - a) ‖f - I_n f‖_∞`.

With `norm_sub_piecewiseLinearInterpCLM_le` this is the `𝒪(h²)` order on `C²[a, b]` that
[han2009theoretical], §12.3.1, Example 12.3.2 asserts for the discontinuous piecewise linear
Galerkin method. -/
theorem norm_sub_discPiecewiseLinearProjCLM_le (hab : a ≤ b) {n : ℕ} {x : ℕ → Set.Icc a b}
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) (f : C(Set.Icc a b, ℝ)) :
    ‖iccToLp a b f - discPiecewiseLinearProjCLM a b n x (iccToLp a b f)‖
      ≤ √(b - a) * ‖f - piecewiseLinearInterpCLM n x f‖ :=
  norm_sub_starProjection_le_of_iccToLp_mem hab (discPiecewiseLinearLp a b n x) f
    (iccToLp_piecewiseLinearInterpCLM_mem_disc hstep hfirst hlast f)

/-! ### Pointwise convergence -/

/-- **A sequence of orthogonal projections of `L²(a, b)` whose subspaces contain the piecewise
linear interpolants of a sequence of partitions of vanishing mesh converges pointwise to the
identity on the whole of `L²(a, b)`**: it does so on the continuous functions by
`norm_sub_starProjection_le_of_iccToLp_mem` and the convergence of piecewise linear interpolation,
the projections have norm at most one, and the continuous functions are dense in `L²`.

This is the pointwise convergence that a projection method for an equation of the second kind
needs, and it is stated for an arbitrary family of subspaces because both the continuous and the
discontinuous piecewise linear spaces of this file satisfy the membership hypothesis;
[han2009theoretical], §12.2.3, the paragraph following equation (12.2.18). -/
theorem tendsto_starProjection_of_piecewiseLinearInterpCLM_mem (hab : a ≤ b)
    {V : ℕ → Submodule ℝ (Lp ℝ 2 (IntegralOperator.iccMeasure a b))}
    [∀ m, (V m).HasOrthogonalProjection] {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hmem : ∀ m (f : C(Set.Icc a b, ℝ)),
      iccToLp a b (piecewiseLinearInterpCLM (N m) (y m) f) ∈ V m)
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) (u : Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :
    Tendsto (fun n => (V n).starProjection u) atTop (𝓝 u) := by
  have hs0 : (0 : ℝ) ≤ √(b - a) := Real.sqrt_nonneg _
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  -- a continuous function close to `u` in `L²`
  obtain ⟨v, hv⟩ := Metric.denseRange_iff.1
    (ContinuousMap.toLp_denseRange (p := 2) ℝ (IntegralOperator.iccMeasure a b) ℝ (by simp))
    u (ε / 3) (by linarith)
  -- the interpolation error of that function tends to zero
  have hint : Tendsto (fun n => ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => piecewiseLinearInterpCLM (N n) (y n) v) atTop (𝓝 v) :=
      tendsto_piecewiseLinearInterpCLM hstep hfirst hlast hmesh hh v
    have h2 : Tendsto (fun n => v - piecewiseLinearInterpCLM (N n) (y n) v) atTop (𝓝 (v - v)) :=
      tendsto_const_nhds.sub h1
    rw [sub_self] at h2
    simpa using h2.norm
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.1 hint) (ε / 3 / (√(b - a) + 1)) (by positivity)
  refine ⟨n₀, fun n hn => ?_⟩
  have hmid : √(b - a) * ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖ < ε / 3 := by
    have h1 := hn₀ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
    have hpos : (0 : ℝ) < √(b - a) + 1 := by positivity
    calc √(b - a) * ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖
        ≤ (√(b - a) + 1) * ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖ := by
          nlinarith [norm_nonneg (v - piecewiseLinearInterpCLM (N n) (y n) v)]
      _ < (√(b - a) + 1) * (ε / 3 / (√(b - a) + 1)) := mul_lt_mul_of_pos_left h1 hpos
      _ = ε / 3 := by field_simp
  -- the three-term estimate
  have hproj : ‖(V n).starProjection u
      - (V n).starProjection (iccToLp a b v)‖ ≤ ‖u - iccToLp a b v‖ := by
    rw [← map_sub]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    nlinarith [Submodule.starProjection_norm_le (V n), norm_nonneg (u - iccToLp a b v),
      norm_nonneg ((V n).starProjection)]
  have hd1 : ‖u - iccToLp a b v‖ < ε / 3 := by
    rw [← dist_eq_norm]
    exact hv
  have hd2 := norm_sub_starProjection_le_of_iccToLp_mem hab (V n) v (hmem n v)
  rw [dist_eq_norm]
  have hsplit : (V n).starProjection u - u
      = ((V n).starProjection u
          - (V n).starProjection (iccToLp a b v))
        - (iccToLp a b v - (V n).starProjection (iccToLp a b v))
        - (u - iccToLp a b v) := by abel
  rw [hsplit]
  calc ‖((V n).starProjection u
          - (V n).starProjection (iccToLp a b v))
        - (iccToLp a b v - (V n).starProjection (iccToLp a b v))
        - (u - iccToLp a b v)‖
      ≤ ‖((V n).starProjection u
            - (V n).starProjection (iccToLp a b v))
          - (iccToLp a b v - (V n).starProjection (iccToLp a b v))‖
        + ‖u - iccToLp a b v‖ := norm_sub_le _ _
    _ ≤ (‖(V n).starProjection u
            - (V n).starProjection (iccToLp a b v)‖
          + ‖iccToLp a b v - (V n).starProjection (iccToLp a b v)‖)
        + ‖u - iccToLp a b v‖ := by gcongr; exact norm_sub_le _ _
    _ < ε := by linarith

/-- **The Galerkin projections of a sequence of partitions of vanishing mesh converge pointwise to
the identity on the whole of `L²(a, b)`.**

This is the pointwise convergence that a projection method for an equation of the second kind
needs; [han2009theoretical], §12.2.3, the paragraph following equation (12.2.18). -/
theorem tendsto_piecewiseLinearProjCLM (hab : a ≤ b) {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b}
    {h : ℕ → ℝ} (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) (u : Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :
    Tendsto (fun n => piecewiseLinearProjCLM a b (N n) (y n) u) atTop (𝓝 u) :=
  tendsto_starProjection_of_piecewiseLinearInterpCLM_mem hab
    (fun m f => iccToLp_piecewiseLinearInterpCLM_mem (N m) (y m) f) hstep hfirst hlast hmesh hh u

/-- **The discontinuous Galerkin projections of a sequence of partitions of vanishing mesh converge
pointwise to the identity on the whole of `L²(a, b)`**, by the same argument as
`tendsto_piecewiseLinearProjCLM`: the discontinuous trial space contains the continuous piecewise
linear interpolants; [han2009theoretical], §12.3.1. -/
theorem tendsto_discPiecewiseLinearProjCLM (hab : a ≤ b) {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b}
    {h : ℕ → ℝ} (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) (u : Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :
    Tendsto (fun n => discPiecewiseLinearProjCLM a b (N n) (y n) u) atTop (𝓝 u) :=
  tendsto_starProjection_of_piecewiseLinearInterpCLM_mem hab
    (fun m f => iccToLp_piecewiseLinearInterpCLM_mem_disc (hstep m) (hfirst m) (hlast m) f)
    hstep hfirst hlast hmesh hh u

/-! ### Kernel operators against a projection -/

/-- **The operator norm of a kernel operator composed with a self-adjoint operator is controlled by
what that operator does to the rows of the kernel**:

`‖K Q‖ ≤ √(b - a) · sup_x ‖Q k(x, ·)‖`.

The proof is the identity `K (Q v) (x) = ⟪k(x, ·), Q v⟫ = ⟪Q k(x, ·), v⟫`, which bounds `K (Q v)`
pointwise by `ε ‖v‖`, and a pointwise bound is an `L²` bound with the factor `√(b - a)`.

Applied to `Q = I - P_n` for a projection `P_n`, this is the estimate an iterated projection
method needs: `‖K (I - P_n)‖` is small as soon as `I - P_n` is uniformly small on the rows of the
kernel; [han2009theoretical], §12.3.1, the paragraph containing equation (12.3.17). -/
theorem norm_l2KernelCLM_comp_le (hab : a ≤ b) {k : C(Set.Icc a b × Set.Icc a b, ℝ)}
    (hk : MemLp k 2 ((iccMeasure a b).prod (iccMeasure a b)))
    {Q : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ] Lp ℝ 2 (IntegralOperator.iccMeasure a b)}
    (hQ : IsSelfAdjoint Q) {ε : ℝ} (hε : 0 ≤ ε)
    (hrow : ∀ z, ‖Q (iccToLp a b (k.curry z))‖ ≤ ε) :
    ‖l2KernelCLM hk ∘L Q‖ ≤ √(b - a) * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hbd : ∀ᵐ z ∂(iccMeasure a b), ‖(l2KernelCLM hk (Q v)) z‖ ≤ ε * ‖v‖ := by
    filter_upwards [l2KernelCLM_apply_ae hk (Q v)] with z hz
    have hrowae : ∫ y, (iccToLp a b (k.curry z)) y * (Q v) y ∂(iccMeasure a b)
        = ∫ y, k (z, y) * (Q v) y ∂(iccMeasure a b) := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_iccToLp (k.curry z)] with y hy
      rw [hy]
      rfl
    have hinner : (inner ℝ (Q (iccToLp a b (k.curry z))) v : ℝ)
        = ∫ y, k (z, y) * (Q v) y ∂(iccMeasure a b) := by
      rw [← hrowae, ← real_inner_lp_eq]
      conv_lhs => rw [← hQ.adjoint_eq]
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [hz, ← hinner, Real.norm_eq_abs]
    calc |(inner ℝ (Q (iccToLp a b (k.curry z))) v : ℝ)|
        ≤ ‖Q (iccToLp a b (k.curry z))‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ ε * ‖v‖ := by gcongr; exact hrow z
  refine (Lp.norm_le_of_ae_bound (by positivity : (0 : ℝ) ≤ ε * ‖v‖) hbd).trans_eq ?_
  have hmu : ((measureUnivNNReal (iccMeasure a b) : NNReal) : ℝ) = b - a := by
    rw [show ((measureUnivNNReal (iccMeasure a b) : NNReal) : ℝ)
      = (iccMeasure a b).real Set.univ from rfl]
    exact measureReal_iccMeasure_univ hab
  rw [← mul_assoc]
  norm_num [hmu, Real.sqrt_eq_rpow]

/-- **`‖K (I - P_n)‖ = 𝒪(h²)` for the discontinuous piecewise linear Galerkin projection.**  For a
kernel whose rows `k(z, ·)` are twice continuously differentiable with `|∂²_y k| ≤ M` on `[a, b]`,

`‖K (I - P_n)‖ ≤ (b - a) h² M / 8`,

where `h` bounds the mesh of the partition.  The rows are handled uniformly by
`norm_sub_discPiecewiseLinearProjCLM_le` and `norm_sub_piecewiseLinearInterpCLM_le`, and the two
factors `√(b - a)` — one from the pointwise-to-`L²` step of `norm_l2KernelCLM_comp_le`, one from
the approximation property — combine into `b - a`.

This is the estimate that [han2009theoretical], §12.3.1, Example 12.3.2 states without proof as
"it is straightforward to show `‖(I - P_n) K*‖ = 𝒪(h²)`"; the two forms agree because `P_n` is
self-adjoint (`isSelfAdjoint_discPiecewiseLinearProjCLM`) and an operator and its adjoint have the
same norm, which is equation (12.3.13) there. -/
theorem norm_l2KernelCLM_comp_sub_discPiecewiseLinearProjCLM_le (hab : a ≤ b) {n : ℕ}
    {x : ℕ → Set.Icc a b} (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    (hfirst : (x 0 : ℝ) = a) (hlast : (x (n + 1) : ℝ) = b)
    {k : C(Set.Icc a b × Set.Icc a b, ℝ)}
    (hk : MemLp k 2 ((iccMeasure a b).prod (iccMeasure a b)))
    {G : Set.Icc a b → ℝ → ℝ} (hG : ∀ z, ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (G z))
    (hGk : ∀ z t : Set.Icc a b, k (z, t) = G z (t : ℝ)) {h M : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h)
    (hM : ∀ z : Set.Icc a b, ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 (G z) t| ≤ M) :
    ‖l2KernelCLM hk ∘L (1 - discPiecewiseLinearProjCLM a b n x)‖ ≤ (b - a) * (h ^ 2 / 8 * M) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (x 0) (x 0) (x 0).2)
  have hh0 : 0 ≤ h := le_trans (sub_nonneg.mpr (hstep 0 (Nat.zero_le n)).le)
    (hmesh 0 (Nat.zero_le n))
  have hsa : IsSelfAdjoint (1 - discPiecewiseLinearProjCLM a b n x) :=
    IsSelfAdjoint.sub (IsSelfAdjoint.one _) (isSelfAdjoint_discPiecewiseLinearProjCLM a b n x)
  have key := norm_l2KernelCLM_comp_le hab hk hsa
    (ε := √(b - a) * (h ^ 2 / 8 * M)) (by positivity) fun z => ?_
  · refine key.trans_eq ?_
    rw [← mul_assoc, Real.mul_self_sqrt (sub_nonneg.2 hab)]
  · have hsub : (1 - discPiecewiseLinearProjCLM a b n x) (iccToLp a b (k.curry z))
        = iccToLp a b (k.curry z)
          - discPiecewiseLinearProjCLM a b n x (iccToLp a b (k.curry z)) := by
      simp
    rw [hsub]
    refine (norm_sub_discPiecewiseLinearProjCLM_le hab hstep hfirst hlast _).trans ?_
    gcongr
    exact norm_sub_piecewiseLinearInterpCLM_le hstep hfirst hlast (hG z) (fun t => hGk z t) hmesh
      (hM z)
