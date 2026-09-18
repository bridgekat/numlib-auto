import Numlib.Analysis.Fourier.SineBasis
import Numlib.Analysis.InnerProductSpace.CompactSpectral
import Numlib.MeasureTheory.Function.LpSpace.Convergence
import Numlib.Variational.EllipticInterval.BoundaryConditions

/-!
# The Sturm–Liouville eigenvalue problem on a bounded interval

The spectral decomposition of the Sturm–Liouville operator `A u = −(p u')' + q u` with Dirichlet
boundary conditions on a bounded interval, [brezis2011functional] §8.6: Theorem 8.22 (a sequence
of eigenvalues `λₙ → +∞` and a Hilbert basis `(eₙ)` of `L²(a, b)` of `C²` eigenfunctions), and
its Example (`p = 1`, `q = 0` on `(0, 1)`: the eigenvalues are `n²π²`, each simple, with
eigenfunctions `√2 sin(nπx)`).

## Main definitions

* `EllipticInterval.SturmLiouville.Hypotheses a b p q α`: `a < b`, `p ∈ C¹[a, b]` with
  `p ≥ α > 0`, `q ∈ C[a, b]` with `q ≥ 0` (the book's reduction of a general `q ∈ C[a, b]` to
  `q ≥ 0` by adding a constant is a surface matter); `Hypotheses.form h` is the bilinear form
  `∫ p u' v' + ∫ q u v` on `H¹(a, b)`.
* `EllipticInterval.SturmLiouville.solution h f`, the weak solution `u ∈ H_0^1(a, b)` of
  `−(p u')' + q u = f`; `solutionCLM h : L² →L H¹` and **the solution operator**
  `solutionOperator h : L²(a, b) →L[ℝ] L²(a, b)`, `f ↦ u`.
* `EllipticInterval.SturmLiouville.eigenfunction h : HilbertBasis ℕ ℝ (L²(a, b))` and
  `eigenvalue h : ℕ → ℝ`, the spectral data of Theorem 8.22.

## Main statements

* `EllipticInterval.SturmLiouville.isCompactOperator_solutionOperator`: `T` is compact, through
  the compact embedding `H¹(a, b) ↪ C[a, b]` (Theorem 8.8 (6)) followed by `C[a, b] → L²(a, b)`;
  `isSymmetric_solutionOperator`: `T` is symmetric; `inner_solutionOperator_nonneg`: `T ≥ 0`;
  `ker_solutionOperator`: `T` is injective.
* `EllipticInterval.SturmLiouville.solutionOperator_eigenfunction`, `eigenvalueSeq_pos`,
  `eigenvalue_pos`, `tendsto_eigenvalue_atTop` (**Theorem 8.22**, the spectral data);
  `exists_contDiffMapIcc_eigenfunction` (**Theorem 8.22**, regularity): each `eₙ` is (almost
  everywhere) a `C²` function vanishing at the endpoints and solving `−(p eₙ')' + q eₙ = λₙ eₙ`.
* `EllipticInterval.SturmLiouville.solutionOperator_sinUnitLp`, `eigenvalue_eq_sq_pi_sq`,
  `eq_smul_sin_of_dirichlet` (**the Example**): for `p = 1`, `q = 0` on `(0, 1)`,
  `T sₙ = sₙ/((n+1)²π²)` for the sine basis `sinBasisUnit`, the eigenvalues of Theorem 8.22 are
  exactly the `(n+1)²π²`, each simple, and every `C²` Dirichlet eigenfunction of `−u''` is a
  multiple of a sine.

## Design

The route is the book's: the solution operator is compact (through `H¹ ↪ C[a, b]`), symmetric
(the two weak equations tested against each other) and injective, so the enumerated spectral
theorem (`ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` of
`Numlib/Analysis/InnerProductSpace/CompactSpectral.lean`) applies (it needs `L²(a, b)` infinite
dimensional, `MeasureTheory.Lp.not_finiteDimensional_of_isOpen`). The regularity of the
eigenfunctions is the Sturm–Liouville case of Step C
(`EllipticInterval.exists_contDiffMapIcc_of_continuous`) with the continuous datum `λₙ eₙ`. The
Example is obtained from the sine Hilbert basis of `Numlib/Analysis/Fourier/SineBasis.lean` by
expanding an eigenvector in that basis: `⟪sₙ, T e⟫ = ⟪T sₙ, e⟫ = ⟪sₙ, e⟫/((n+1)²π²)`, so an
eigenvector with eigenvalue `μ` has all coefficients zero except those with `μ = ((n+1)²π²)⁻¹`;
no ODE uniqueness argument is needed.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace EllipticInterval.SturmLiouville

/-! ### The hypotheses of Theorem 8.22 -/

/-- **The coefficient hypotheses of Theorem 8.22** of [brezis2011functional], bundled: a bounded
interval `(a, b)`, `p ∈ C¹[a, b]` with `p ≥ α > 0`, and `q ∈ C[a, b]` with `q ≥ 0`. -/
structure Hypotheses (a b : ℝ) (p q : ℝ → ℝ) (α : ℝ) : Prop where
  /-- The interval is nondegenerate. -/
  lt : a < b
  /-- `p ∈ C¹[a, b]`. -/
  contDiffOn_p : ContDiffOn ℝ 1 p (Icc a b)
  /-- `α > 0`. -/
  pos : 0 < α
  /-- `p ≥ α` on `[a, b]`. -/
  le_p : ∀ x ∈ Icc a b, α ≤ p x
  /-- `q ∈ C[a, b]`. -/
  continuousOn_q : ContinuousOn q (Icc a b)
  /-- `q ≥ 0` on `[a, b]`. -/
  nonneg_q : ∀ x ∈ Icc a b, 0 ≤ q x

variable {a b : ℝ} {p q : ℝ → ℝ} {α : ℝ}

namespace Hypotheses

/-- The coefficient `p` as an element of `L^∞(a, b)`. -/
def pL (h : Hypotheses a b p q α) : Lp ℝ ⊤ (volume.restrict (Ioo a b)) :=
  h.contDiffOn_p.continuousOn.memLp_top_restrict_Ioo.toLp p

/-- The coefficient `q` as an element of `L^∞(a, b)`. -/
def qL (h : Hypotheses a b p q α) : Lp ℝ ⊤ (volume.restrict (Ioo a b)) :=
  h.continuousOn_q.memLp_top_restrict_Ioo.toLp q

/-- The function of `pL` is `p`. -/
theorem coeFn_pL (h : Hypotheses a b p q α) : h.pL =ᵐ[volume.restrict (Ioo a b)] p :=
  MemLp.coeFn_toLp _

/-- The function of `qL` is `q`. -/
theorem coeFn_qL (h : Hypotheses a b p q α) : h.qL =ᵐ[volume.restrict (Ioo a b)] q :=
  MemLp.coeFn_toLp _

/-- `p ≥ α` almost everywhere. -/
theorem ae_le_pL (h : Hypotheses a b p q α) : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α ≤ h.pL x := by
  filter_upwards [h.coeFn_pL, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [hx]; exact h.le_p x (Ioo_subset_Icc_self hxI)

/-- `q ≥ 0` almost everywhere. -/
theorem ae_nonneg_qL (h : Hypotheses a b p q α) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ h.qL x := by
  filter_upwards [h.coeFn_qL, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [hx]; exact h.nonneg_q x (Ioo_subset_Icc_self hxI)

/-- `p` does not vanish on `[a, b]`. -/
theorem p_ne_zero (h : Hypotheses a b p q α) : ∀ x ∈ Icc a b, p x ≠ 0 := fun x hx ↦
  (h.pos.trans_le (h.le_p x hx)).ne'

/-- **The Sturm–Liouville form** `a(u, v) = ∫ p u' v' + ∫ q u v` on `H¹(a, b)`. -/
def form (h : Hypotheses a b p q α) : SesqForm ℝ (SobolevInterval 1 a b) :=
  EllipticInterval.form a b h.pL 0 h.qL

/-- The Sturm–Liouville form is symmetric. -/
theorem form_comm (h : Hypotheses a b p q α) (u v : SobolevInterval 1 a b) :
    h.form u v = h.form v u :=
  EllipticInterval.form_comm h.pL h.qL u v

/-- The Sturm–Liouville form is coercive on `H_0^1(a, b)`, with constant
`α / (1 + (b − a)²/2)` (Poincaré). -/
theorem form_isCoerciveWith_restrict (h : Hypotheses a b p q α) :
    (h.form.restrict (SobolevIntervalZero a b)).IsCoerciveWith (α / (1 + (b - a) ^ 2 / 2)) :=
  EllipticInterval.form_isCoerciveWith_restrict h.lt h.pL h.qL h.ae_le_pL h.ae_nonneg_qL h.pos.le

/-- `a(v, v) ≥ 0` for every `v ∈ H¹(a, b)`. -/
theorem form_self_nonneg (h : Hypotheses a b p q α) (v : SobolevInterval 1 a b) :
    0 ≤ h.form v v :=
  (mul_nonneg h.pos.le (sq_nonneg _)).trans
    (EllipticInterval.form_isCoerciveWith_seminorm h.pL h.qL h.ae_le_pL h.ae_nonneg_qL v)

end Hypotheses

/-! ### The weak solution and the solution operator -/

/-- **The weak solution** `u ∈ H_0^1(a, b)` of `−(p u')' + q u = f`, `u(a) = u(b) = 0`, for
`f ∈ L²(a, b)` (Lax–Milgram, `EllipticInterval.existsUnique_isWeakSolution`). -/
def solution (h : Hypotheses a b p q α) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    SobolevInterval 1 a b :=
  Classical.choose (EllipticInterval.existsUnique_isWeakSolution h.lt h.pL h.qL h.pos h.ae_le_pL
    h.ae_nonneg_qL f).exists

/-- The weak solution solves the weak problem on `H_0^1(a, b)`. -/
theorem isGalerkinSolution_solution (h : Hypotheses a b p q α)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    IsGalerkinSolution h.form (load a b f) (SobolevIntervalZero a b) (solution h f) :=
  Classical.choose_spec (EllipticInterval.existsUnique_isWeakSolution h.lt h.pL h.qL h.pos
    h.ae_le_pL h.ae_nonneg_qL f).exists

/-- The weak solution lies in `H_0^1(a, b)`. -/
theorem solution_mem (h : Hypotheses a b p q α) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    solution h f ∈ SobolevIntervalZero a b :=
  (isGalerkinSolution_solution h f).1

/-- The weak equation of the weak solution. -/
theorem form_solution (h : Hypotheses a b p q α) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {v : SobolevInterval 1 a b} (hv : v ∈ SobolevIntervalZero a b) :
    h.form (solution h f) v = load a b f v :=
  (isGalerkinSolution_solution h f).2 v hv

/-- The weak solution is unique. -/
theorem eq_solution_of_isGalerkinSolution (h : Hypotheses a b p q α)
    {f : Lp ℝ 2 (volume.restrict (Ioo a b))} {u : SobolevInterval 1 a b}
    (hu : IsGalerkinSolution h.form (load a b f) (SobolevIntervalZero a b) u) :
    u = solution h f :=
  (EllipticInterval.existsUnique_isWeakSolution h.lt h.pL h.qL h.pos h.ae_le_pL h.ae_nonneg_qL
    f).unique hu (isGalerkinSolution_solution h f)

/-- The load functional is additive in `f`. -/
theorem _root_.EllipticInterval.load_add (f g : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    load a b (f + g) = load a b f + load a b g := by
  ext v
  rw [add_apply, load_apply_inner, load_apply_inner, load_apply_inner, inner_add_left]

/-- The load functional is homogeneous in `f`. -/
theorem _root_.EllipticInterval.load_smul (c : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    load a b (c • f) = c • load a b f := by
  ext v
  rw [smul_apply, load_apply_inner, load_apply_inner, inner_smul_left]
  simp

/-- The weak solution is additive in the datum. -/
theorem solution_add (h : Hypotheses a b p q α) (f g : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    solution h (f + g) = solution h f + solution h g := by
  refine (eq_solution_of_isGalerkinSolution h ⟨(SobolevIntervalZero a b).add_mem (solution_mem h f)
    (solution_mem h g), fun v hv ↦ ?_⟩).symm
  rw [map_add, add_apply, form_solution h f hv, form_solution h g hv, load_add, add_apply]

/-- The weak solution is homogeneous in the datum. -/
theorem solution_smul (h : Hypotheses a b p q α) (c : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) : solution h (c • f) = c • solution h f := by
  refine (eq_solution_of_isGalerkinSolution h ⟨(SobolevIntervalZero a b).smul_mem c
    (solution_mem h f), fun v hv ↦ ?_⟩).symm
  rw [map_smul, smul_apply, form_solution h f hv, load_smul, smul_apply]

/-- The constant of the a priori estimate `‖u‖_{H¹} ≤ C ‖f‖_{L²}` (the book's (39)). -/
def solutionBound (a b α : ℝ) : ℝ :=
  Real.sqrt (1 + (b - a) ^ 2 / 2) * ((b - a) / Real.sqrt 2 / α)

/-- The constant of the a priori estimate is nonnegative. -/
theorem solutionBound_nonneg (h : Hypotheses a b p q α) : 0 ≤ solutionBound a b α := by
  have := h.lt; have := h.pos
  unfold solutionBound; positivity

open SobolevInterval in
/-- **The a priori estimate (39) of [brezis2011functional]**: `‖u‖_{H¹} ≤ C ‖f‖_{L²}` for the weak
solution, from `α ‖u'‖² ≤ ‖f‖ ‖u‖` and Poincaré's inequality. -/
theorem norm_solution_le (h : Hypotheses a b p q α) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ‖solution h f‖ ≤ solutionBound a b α * ‖f‖ := by
  have h1 := SobolevIntervalZero.norm_le_seminorm h.lt (solution_mem h f)
  have h2 := EllipticInterval.seminorm_le_of_isGalerkinSolution h.lt h.pL h.qL h.pos h.ae_le_pL
    h.ae_nonneg_qL f le_rfl (isGalerkinSolution_solution h f)
  calc ‖solution h f‖ ≤ Real.sqrt (1 + (b - a) ^ 2 / 2) * seminorm 1 a b (solution h f) := h1
    _ ≤ Real.sqrt (1 + (b - a) ^ 2 / 2) * ((b - a) / Real.sqrt 2 / α * ‖f‖) := by
        gcongr
    _ = solutionBound a b α * ‖f‖ := by rw [solutionBound]; ring

/-- The weak solution map `L²(a, b) → H¹(a, b)` as a linear map. -/
def solutionₗ (h : Hypotheses a b p q α) :
    Lp ℝ 2 (volume.restrict (Ioo a b)) →ₗ[ℝ] SobolevInterval 1 a b where
  toFun := solution h
  map_add' := solution_add h
  map_smul' c f := by rw [solution_smul h c f]; rfl

/-- **The weak solution map `L²(a, b) → H¹(a, b)`** as a continuous linear map, of norm at most
`solutionBound a b α`. -/
def solutionCLM (h : Hypotheses a b p q α) :
    Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ] SobolevInterval 1 a b :=
  (solutionₗ h).mkContinuous (solutionBound a b α) (norm_solution_le h)

/-- The continuous solution map is the weak solution. -/
@[simp]
theorem solutionCLM_apply (h : Hypotheses a b p q α) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    solutionCLM h f = solution h f := rfl

/-- **The solution operator `T : L²(a, b) → L²(a, b)`** of [brezis2011functional] Theorem 8.22,
`f ↦ u`, the weak solution of `−(p u')' + q u = f`, `u(a) = u(b) = 0`, read in `L²(a, b)`. -/
def solutionOperator (h : Hypotheses a b p q α) :
    Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  (SobolevInterval.derivL 1 a b 0).comp (solutionCLM h)

/-- The solution operator is the function of the weak solution. -/
theorem solutionOperator_apply (h : Hypotheses a b p q α)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    solutionOperator h f = SobolevInterval.deriv (solution h f) 0 := rfl

/-- The function of `T f` is the function of the weak solution. -/
theorem coeFn_solutionOperator (h : Hypotheses a b p q α)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ⇑(solutionOperator h f) = SobolevInterval.fn (solution h f) := rfl

/-- The load functional through the solution operator: `∫ g (T f) = ⟪g, T f⟫`. -/
theorem load_solution (h : Hypotheses a b p q α) (f g : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    load a b g (solution h f) = ⟪g, solutionOperator h f⟫_ℝ := rfl

/-! ### Compactness -/

/-- A continuous function on `[a, b]`, extended by its endpoint values, as an element of
`L²(a, b)`. -/
def iccToLpFun (hab : a ≤ b) (g : C(Icc a b, ℝ)) : Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  (ContinuousMap.IccExtend hab g).continuous.continuousOn.memLp_two_restrict_Ioo.toLp _

/-- The function of `iccToLpFun`. -/
theorem coeFn_iccToLpFun (hab : a ≤ b) (g : C(Icc a b, ℝ)) :
    ⇑(iccToLpFun hab g) =ᵐ[volume.restrict (Ioo a b)] IccExtend hab g :=
  MemLp.coeFn_toLp (ContinuousMap.IccExtend hab g).continuous.continuousOn.memLp_two_restrict_Ioo

/-- The inclusion `C[a, b] → L²(a, b)`, `g ↦ g` extended by its endpoint values, as a linear
map. -/
def iccToLpₗ (hab : a ≤ b) : C(Icc a b, ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)) where
  toFun := iccToLpFun hab
  map_add' g₁ g₂ := by
    refine Lp.ext ?_
    filter_upwards [coeFn_iccToLpFun hab (g₁ + g₂), Lp.coeFn_add (iccToLpFun hab g₁)
      (iccToLpFun hab g₂), coeFn_iccToLpFun hab g₁, coeFn_iccToLpFun hab g₂] with x h0 h1 h2 h3
    rw [h0, h1, Pi.add_apply, h2, h3]
    rfl
  map_smul' c g := by
    refine Lp.ext ?_
    change ⇑(iccToLpFun hab (c • g)) =ᵐ[volume.restrict (Ioo a b)] ⇑(c • iccToLpFun hab g)
    filter_upwards [coeFn_iccToLpFun hab (c • g), Lp.coeFn_smul c (iccToLpFun hab g),
      coeFn_iccToLpFun hab g] with x h0 h1 h2
    rw [h0, h1, Pi.smul_apply, h2]
    rfl

/-- The function of the inclusion `C[a, b] → L²(a, b)`. -/
theorem coeFn_iccToLpₗ (hab : a ≤ b) (g : C(Icc a b, ℝ)) :
    ⇑(iccToLpₗ hab g) =ᵐ[volume.restrict (Ioo a b)] IccExtend hab g :=
  coeFn_iccToLpFun hab g

/-- The inclusion `C[a, b] → L²(a, b)` has norm at most `√(b − a)`. -/
theorem norm_iccToLpₗ_le (hab : a ≤ b) (g : C(Icc a b, ℝ)) :
    ‖iccToLpₗ hab g‖ ≤ Real.sqrt (b - a) * ‖g‖ := by
  refine Lp.norm_le_sqrt_mul_of_ae_bound hab _ (norm_nonneg _) ?_
  filter_upwards [coeFn_iccToLpₗ hab g] with x hx
  rw [hx, ← Real.norm_eq_abs, IccExtend_apply]
  exact ContinuousMap.norm_coe_le_norm _ _

/-- **The inclusion `C[a, b] → L²(a, b)`** as a continuous linear map. -/
def iccToLp (hab : a ≤ b) : C(Icc a b, ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  (iccToLpₗ hab).mkContinuous _ (norm_iccToLpₗ_le hab)

/-- The function of the inclusion `C[a, b] → L²(a, b)`. -/
theorem coeFn_iccToLp (hab : a ≤ b) (g : C(Icc a b, ℝ)) :
    ⇑(iccToLp hab g) =ᵐ[volume.restrict (Ioo a b)] IccExtend hab g :=
  coeFn_iccToLpₗ hab g

/-- The inclusion `H¹(a, b) → L²(a, b)` factors through the embedding into `C[a, b]`. -/
theorem derivL_zero_eq_iccToLp_comp (hab : a < b) :
    SobolevInterval.derivL 1 a b 0
      = (iccToLp hab.le).comp (SobolevIntervalLp.toContinuousMap (p := 2) hab) := by
  refine ContinuousLinearMap.ext fun u ↦ Lp.ext ?_
  rw [ContinuousLinearMap.comp_apply, SobolevInterval.derivL_apply]
  refine ((SobolevIntervalLp.fn_ae_eq_rep (SobolevIntervalLp.ordConnected_coe_Ioo a b) u).trans
    ?_).trans (coeFn_iccToLp hab.le (SobolevIntervalLp.toContinuousMap hab u)).symm
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
  rw [IccExtend_of_mem hab.le _ (Ioo_subset_Icc_self hx)]
  rfl

/-- **The inclusion `H¹(a, b) → L²(a, b)` is compact** for a bounded interval: it factors through
the compact embedding `H¹(a, b) ↪ C[a, b]` (Theorem 8.8 (6)). -/
theorem isCompactOperator_derivL_zero (hab : a < b) :
    IsCompactOperator (SobolevInterval.derivL 1 a b 0) := by
  rw [derivL_zero_eq_iccToLp_comp hab, ContinuousLinearMap.coe_comp]
  exact (SobolevIntervalLp.isCompactOperator_toContinuousMap hab ENNReal.one_lt_two).clm_comp
    (iccToLp hab.le)

/-- **The solution operator is compact** ([brezis2011functional] Theorem 8.22, proof): `T` is the
bounded map `L² → H_0^1` followed by the compact injection `H¹(a, b) → L²(a, b)`. -/
theorem isCompactOperator_solutionOperator (h : Hypotheses a b p q α) :
    IsCompactOperator (solutionOperator h) := by
  rw [solutionOperator, ContinuousLinearMap.coe_comp]
  exact (isCompactOperator_derivL_zero h.lt).comp_clm (solutionCLM h)

/-! ### Symmetry, positivity and injectivity -/

/-- `⟪T f, g⟫ = a(T f, T g)`: the weak equation of `T g` tested against `T f`. -/
theorem inner_solutionOperator_eq_form (h : Hypotheses a b p q α)
    (f g : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ⟪solutionOperator h f, g⟫_ℝ = h.form (solution h g) (solution h f) := by
  rw [real_inner_comm, ← load_solution, form_solution h g (solution_mem h f)]

/-- **The solution operator is symmetric** ([brezis2011functional] Theorem 8.22, proof):
`⟪T f, g⟫ = a(T g, T f) = a(T f, T g) = ⟪f, T g⟫`. -/
theorem isSymmetric_solutionOperator (h : Hypotheses a b p q α) :
    (solutionOperator h : Lp ℝ 2 (volume.restrict (Ioo a b)) →ₗ[ℝ] _).IsSymmetric := by
  intro f g
  change ⟪solutionOperator h f, g⟫_ℝ = ⟪f, solutionOperator h g⟫_ℝ
  rw [inner_solutionOperator_eq_form, real_inner_comm (solutionOperator h g) f,
    inner_solutionOperator_eq_form, h.form_comm]

/-- **The solution operator is positive**: `⟪T f, f⟫ = a(T f, T f) ≥ 0`. -/
theorem inner_solutionOperator_nonneg (h : Hypotheses a b p q α)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) : 0 ≤ ⟪solutionOperator h f, f⟫_ℝ := by
  rw [inner_solutionOperator_eq_form]
  exact h.form_self_nonneg _

/-- An `L²(a, b)` function orthogonal to every test function vanishes. -/
theorem eq_zero_of_forall_integral_mul_testFunction_eq_zero
    (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hf : ∀ φ : 𝓓(Opens.Ioo a b, ℝ), ∫ x in Ioo a b, f x * φ x = 0) : f = 0 := by
  have hloc : LocallyIntegrableOn (f : ℝ → ℝ) (Ioo a b) :=
    (Lp.memLp f).locallyIntegrableOn (Ω := Opens.Ioo a b) one_le_two
  have key := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgs hgsupp ↦ by
    set φ : 𝓓(Opens.Ioo a b, ℝ) := ⟨g, hg, hgs, hgsupp⟩ with hφ
    have e : ∫ x, g x • f x = ∫ x in Ioo a b, f x * φ x := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo a b) fun x hx ↦ by
        rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hgsupp h)), zero_smul]]
      exact setIntegral_congr_fun measurableSet_Ioo fun x _ ↦ by
        change g x * f x = f x * g x; ring
    rw [e]
    exact hf φ
  refine Lp.ext ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2 key,
    Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo a b))] with x h1 h2
  rw [h1, h2]
  rfl

/-- **The solution operator is injective** ([brezis2011functional] Theorem 8.22, proof):
`T f = 0` forces `u = 0`, hence `∫ f v = 0` for every `v ∈ H_0^1`, hence `f = 0`. -/
theorem ker_solutionOperator (h : Hypotheses a b p q α) :
    LinearMap.ker (solutionOperator h :
      Lp ℝ 2 (volume.restrict (Ioo a b)) →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b))) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun f hf ↦ ?_
  have hf' : SobolevInterval.deriv (solution h f) 0 = 0 := hf
  have hu : solution h f = 0 := by
    refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
    change (SobolevInterval.deriv (solution h f) 0 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      SobolevMultiIndex.fn 0
    rw [hf']
    exact (Lp.coeFn_zero ℝ 2 _).trans SobolevMultiIndex.fn_zero.symm
  refine eq_zero_of_forall_integral_mul_testFunction_eq_zero f fun φ ↦ ?_
  obtain ⟨v, hv, hvφ⟩ := SobolevIntervalZero.exists_mem_fn_ae_eq φ
  have := form_solution h f hv
  rw [hu, map_zero, zero_apply, load_apply] at this
  calc ∫ x in Ioo a b, f x * φ x = ∫ x in Ioo a b, f x * SobolevInterval.deriv v 0 x := by
        refine integral_congr_ae ?_
        filter_upwards [hvφ] with x hx
        rw [SobolevInterval.deriv_zero, hx]
    _ = 0 := this.symm

/-! ### Theorem 8.22: the eigenfunctions and eigenvalues -/

/-- `L²(a, b)` is infinite-dimensional. -/
theorem not_finiteDimensional (h : Hypotheses a b p q α) :
    ¬ FiniteDimensional ℝ (Lp ℝ 2 (volume.restrict (Ioo a b))) :=
  Lp.not_finiteDimensional_of_isOpen volume 2 isOpen_Ioo (nonempty_Ioo.2 h.lt)

/-- **The eigenfunctions of Theorem 8.22** of [brezis2011functional]: the Hilbert basis of
`L²(a, b)` of eigenvectors of the solution operator, from the spectral theorem for compact
self-adjoint operators (`ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis`). -/
def eigenfunction (h : Hypotheses a b p q α) :
    HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ioo a b))) :=
  ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis (isSymmetric_solutionOperator h)
    (isCompactOperator_solutionOperator h) (ker_solutionOperator h) (not_finiteDimensional h)

/-- The eigenvalues `μₙ` of the solution operator. -/
def eigenvalueSeq (h : Hypotheses a b p q α) : ℕ → ℝ :=
  ContinuousLinearMap.IsSymmetric.eigenvalueSeq (isSymmetric_solutionOperator h)
    (isCompactOperator_solutionOperator h)

/-- **The eigenvalues of Theorem 8.22**: `λₙ = 1/μₙ`, where `μₙ` are the eigenvalues of the
solution operator. -/
def eigenvalue (h : Hypotheses a b p q α) (n : ℕ) : ℝ := (eigenvalueSeq h n)⁻¹

/-- `T eₙ = μₙ eₙ`. -/
theorem solutionOperator_eigenfunction (h : Hypotheses a b p q α) (n : ℕ) :
    solutionOperator h (eigenfunction h n) = eigenvalueSeq h n • eigenfunction h n :=
  ContinuousLinearMap.IsSymmetric.apply_eigenvectorHilbertBasis (isSymmetric_solutionOperator h)
    (isCompactOperator_solutionOperator h) (ker_solutionOperator h) (not_finiteDimensional h) n

/-- The eigenvalues of the solution operator tend to `0`. -/
theorem tendsto_eigenvalueSeq_zero (h : Hypotheses a b p q α) :
    Tendsto (eigenvalueSeq h) atTop (𝓝 0) :=
  ContinuousLinearMap.IsSymmetric.tendsto_eigenvalueSeq_zero (isSymmetric_solutionOperator h)
    (isCompactOperator_solutionOperator h)

/-- The eigenfunctions are nonzero. -/
theorem eigenfunction_ne_zero (h : Hypotheses a b p q α) (n : ℕ) : eigenfunction h n ≠ 0 :=
  (eigenfunction h).orthonormal.ne_zero n

/-- **The eigenvalues of the solution operator are positive**: `μₙ ≥ 0` from `⟪T eₙ, eₙ⟫ ≥ 0`
and `μₙ ≠ 0` from the injectivity of `T`. -/
theorem eigenvalueSeq_pos (h : Hypotheses a b p q α) (n : ℕ) : 0 < eigenvalueSeq h n := by
  have h1 := inner_solutionOperator_nonneg h (eigenfunction h n)
  rw [solutionOperator_eigenfunction, inner_smul_left, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq, (eigenfunction h).orthonormal.1 n, one_pow, mul_one] at h1
  refine lt_of_le_of_ne h1 fun h0 ↦ eigenfunction_ne_zero h n ?_
  have h2 := solutionOperator_eigenfunction h n
  rw [← h0, zero_smul] at h2
  have := ker_solutionOperator h
  rw [LinearMap.ker_eq_bot'] at this
  exact this _ h2

/-- **The eigenvalues `λₙ` of Theorem 8.22 are positive.** -/
theorem eigenvalue_pos (h : Hypotheses a b p q α) (n : ℕ) : 0 < eigenvalue h n :=
  inv_pos.2 (eigenvalueSeq_pos h n)

/-- **`λₙ → +∞`** ([brezis2011functional] Theorem 8.22). -/
theorem tendsto_eigenvalue_atTop (h : Hypotheses a b p q α) :
    Tendsto (eigenvalue h) atTop atTop := by
  have h1 : Tendsto (eigenvalueSeq h) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_eigenvalueSeq_zero h,
      Eventually.of_forall fun n ↦ eigenvalueSeq_pos h n⟩
  exact tendsto_inv_nhdsGT_zero.comp h1

/-- `T (λₙ eₙ) = eₙ`: the eigenfunction is the weak solution with datum `λₙ eₙ`. -/
theorem solutionOperator_smul_eigenfunction (h : Hypotheses a b p q α) (n : ℕ) :
    solutionOperator h (eigenvalue h n • eigenfunction h n) = eigenfunction h n := by
  rw [map_smul, solutionOperator_eigenfunction, smul_smul, eigenvalue,
    inv_mul_cancel₀ (eigenvalueSeq_pos h n).ne', one_smul]

open SobolevInterval in
/-- **Theorem 8.22 of [brezis2011functional], regularity of the eigenfunctions**: each
eigenfunction `eₙ` agrees almost everywhere with a function `e ∈ C²[a, b]` with
`e(a) = e(b) = 0` and `−(p e')' + q e = λₙ e` on `(a, b)`: `eₙ` is the weak solution with the
datum `λₙ eₙ`, which is (almost everywhere) continuous on `[a, b]` since `eₙ ∈ H_0^1 ⊆ C[a, b]`,
and Step C (`EllipticInterval.exists_contDiffMapIcc_of_continuous`) applies. -/
theorem exists_contDiffMapIcc_eigenfunction (h : Hypotheses a b p q α) (n : ℕ) :
    ∃ e : ContDiffMapIcc h.lt.le 2,
      ((eigenfunction h n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] e.extend) ∧
      e.extend a = 0 ∧ e.extend b = 0 ∧
      ∀ x ∈ Ioo a b, -_root_.deriv (fun t ↦ p t * e.shift.extend t) x + q x * e.extend x
        = eigenvalue h n * e.extend x := by
  obtain ⟨f, hf⟩ : ∃ f, f = eigenvalue h n • eigenfunction h n := ⟨_, rfl⟩
  have hTf : deriv (solution h f) 0 = eigenfunction h n := by
    rw [hf]; exact solutionOperator_smul_eigenfunction h n
  -- the datum is continuous: `f = λₙ ũ`
  have hfL : (f : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      fun x ↦ eigenvalue h n * rep (solution h f) x := by
    filter_upwards [Lp.coeFn_smul (eigenvalue h n) (eigenfunction h n),
      fn_ae_eq_rep h.lt (solution h f)] with x h1 h2
    have h1' : f x = eigenvalue h n * eigenfunction h n x := by
      rw [hf, h1, Pi.smul_apply, smul_eq_mul]
    rw [h1', ← h2, ← SobolevInterval.deriv_zero, hTf]
  obtain ⟨e, he, hode⟩ := exists_contDiffMapIcc_of_continuous h.lt h.pL 0 h.qL f (α := p)
    (β := fun _ ↦ 0) (γ := q) h.coeFn_pL (Lp.coeFn_zero ℝ ⊤ _) h.coeFn_qL hfL h.contDiffOn_p
    h.p_ne_zero continuousOn_const h.continuousOn_q
    ((continuousOn_rep h.lt.le (solution h f)).const_smul (eigenvalue h n))
    (fun v hv ↦ form_solution h f hv)
  have hrep : EqOn (rep (solution h f)) e.extend (Icc a b) := by
    rw [← he]; exact rep_ofContDiffMapIcc h.lt e
  refine ⟨e, ?_, ?_, ?_, fun x hx ↦ ?_⟩
  · rw [← hTf, SobolevInterval.deriv_zero]
    filter_upwards [fn_ae_eq_rep h.lt (solution h f), ae_restrict_mem measurableSet_Ioo]
      with x h1 h2
    rw [h1, hrep (Ioo_subset_Icc_self h2)]
  · rw [← hrep (left_mem_Icc.2 h.lt.le)]
    exact SobolevIntervalZero.rep_left_eq_zero h.lt (solution_mem h f)
  · rw [← hrep (right_mem_Icc.2 h.lt.le)]
    exact SobolevIntervalZero.rep_right_eq_zero h.lt (solution_mem h f)
  · have := hode x hx
    simp only [zero_mul, add_zero] at this
    rw [this, hrep (Ioo_subset_Icc_self hx)]

/-! ### The Example: `p = 1`, `q = 0` on `(0, 1)` -/

/-- The coefficient hypotheses of the Example of [brezis2011functional] §8.6: `p = 1`, `q = 0`
on `(0, 1)`, with `α = 1`. -/
theorem hypotheses_one_zero : Hypotheses 0 1 (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) 1 where
  lt := zero_lt_one
  contDiffOn_p := contDiffOn_const
  pos := zero_lt_one
  le_p := fun _ _ ↦ le_rfl
  continuousOn_q := continuousOn_const
  nonneg_q := fun _ _ ↦ le_rfl

open Real in
/-- The sine `sₙ = √2 sin((n+1)πx)` is smooth. -/
theorem contDiff_sinUnitFun (n : ℕ) : ContDiff ℝ ∞ (sinUnitFun n) := by
  unfold sinUnitFun; fun_prop

open Real in
/-- The derivative of `sₙ`. -/
theorem hasDerivAt_sinUnitFun (n : ℕ) (x : ℝ) :
    HasDerivAt (sinUnitFun n) (√2 * ((n + 1) * π) * cos ((n + 1) * π * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ ↦ (n + 1) * π * x) ((n + 1) * π) x := by
    simpa using (hasDerivAt_id x).const_mul ((n + 1) * π)
  have h2 := (h1.sin).const_mul (√2)
  refine h2.congr_deriv ?_
  ring

open Real in
/-- The derivative of `sₙ`, as a function. -/
theorem deriv_sinUnitFun (n : ℕ) :
    _root_.deriv (sinUnitFun n) = fun x ↦ √2 * ((n + 1) * π) * cos ((n + 1) * π * x) :=
  funext fun x ↦ (hasDerivAt_sinUnitFun n x).deriv

open Real in
/-- The second derivative of `sₙ`: `−sₙ'' = (n+1)²π² sₙ`. -/
theorem deriv_deriv_sinUnitFun (n : ℕ) :
    _root_.deriv (_root_.deriv (sinUnitFun n)) = fun x ↦ -(((n + 1) * π) ^ 2) * sinUnitFun n x := by
  rw [deriv_sinUnitFun]
  funext x
  have h1 : HasDerivAt (fun x : ℝ ↦ (n + 1) * π * x) ((n + 1) * π) x := by
    simpa using (hasDerivAt_id x).const_mul ((n + 1) * π)
  have h2 := (h1.cos).const_mul (√2 * ((n + 1) * π))
  rw [h2.deriv, sinUnitFun]
  ring

/-- The derivative of `sₙ` is continuous. -/
theorem continuous_deriv_sinUnitFun (n : ℕ) : Continuous (_root_.deriv (sinUnitFun n)) := by
  rw [deriv_sinUnitFun]; fun_prop

/-- **`sₙ` as an element of `H¹(0, 1)`.** -/
def sinElem (n : ℕ) : SobolevInterval 1 0 1 :=
  ContDiffMapIcc.toSobolevInterval zero_le_one zero_lt_one 1
    (ContDiffMapIcc.ofContDiff zero_le_one ((contDiff_sinUnitFun n).of_le (by simp)))

open SobolevInterval in
/-- The function of `sinElem n` is `sₙ`. -/
theorem fn_sinElem_ae_eq (n : ℕ) :
    fn (sinElem n) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] sinUnitFun n := by
  refine (ContDiffMapIcc.fn_toSobolevInterval_ae_eq zero_le_one zero_lt_one _).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
  rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx)]
  exact ContDiffMapIcc.coe_ofContDiff zero_le_one _ ⟨x, Ioo_subset_Icc_self hx⟩

open SobolevInterval in
/-- The weak derivative of `sinElem n` is `sₙ'`. -/
theorem coeFn_deriv_sinElem_one (n : ℕ) :
    ⇑(deriv (sinElem n) 1) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] _root_.deriv (sinUnitFun n) := by
  rw [sinElem, ContDiffMapIcc.deriv_toSobolevInterval]
  refine (ContDiffMapIcc.coeFn_derivLp _ 1).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
  rw [IccExtend_of_mem zero_le_one _ (Ioo_subset_Icc_self hx)]
  change ContDiffMapIcc.deriv _ 1 ⟨x, _⟩ = _
  rw [ContDiffMapIcc.deriv_ofContDiff]
  simp only [Fin.val_one, iteratedDeriv_one]

/-- The function of `sinElem n` is the sine basis element `sinUnitLp n`. -/
theorem deriv_sinElem_zero (n : ℕ) : SobolevInterval.deriv (sinElem n) 0 = sinUnitLp n :=
  Lp.ext ((fn_sinElem_ae_eq n).trans (coeFn_sinUnitLp n).symm)

open SobolevInterval in
/-- The continuous representative of `sinElem n` is `sₙ` on `[0, 1]`. -/
theorem rep_sinElem (n : ℕ) : EqOn (rep (sinElem n)) (sinUnitFun n) (Icc 0 1) :=
  rep_eq_of_continuousOn zero_lt_one _ (continuous_sinUnitFun n).continuousOn (fn_sinElem_ae_eq n)

open Real in
/-- `sₙ(0) = 0`. -/
theorem sinUnitFun_zero (n : ℕ) : sinUnitFun n 0 = 0 := by simp [sinUnitFun]

open Real in
/-- `sₙ(1) = 0`. -/
theorem sinUnitFun_one (n : ℕ) : sinUnitFun n 1 = 0 := by
  rw [sinUnitFun, mul_one, show ((n : ℝ) + 1) * π = ((n + 1 : ℕ) : ℝ) * π by push_cast; ring,
    sin_nat_mul_pi, mul_zero]

/-- `sinElem n ∈ H_0^1(0, 1)`. -/
theorem sinElem_mem (n : ℕ) : sinElem n ∈ SobolevIntervalZero 0 1 :=
  SobolevIntervalZero.mem_of_rep_eq_zero zero_lt_one _
    (by rw [rep_sinElem n (left_mem_Icc.2 zero_le_one), sinUnitFun_zero])
    (by rw [rep_sinElem n (right_mem_Icc.2 zero_le_one), sinUnitFun_one])

open SobolevInterval Real in
/-- **`sₙ` is a weak eigenfunction**: `∫ sₙ' v' = (n+1)²π² ∫ sₙ v` for every `v ∈ H_0^1(0, 1)`,
by one integration by parts. -/
theorem form_sinElem (n : ℕ) {v : SobolevInterval 1 0 1} (hv : v ∈ SobolevIntervalZero 0 1) :
    hypotheses_one_zero.form (sinElem n) v = ((n + 1) * π) ^ 2 * load 0 1 (sinUnitLp n) v := by
  set h := hypotheses_one_zero with hh
  rw [Hypotheses.form, form_apply, load_apply]
  have hψ : ContDiffOn ℝ 1 (_root_.deriv (sinUnitFun n)) (Icc 0 1) :=
    (((contDiff_sinUnitFun n).iterate_deriv 1).of_le (by simp)).contDiffOn
  have ibp := integral_deriv_mul_contDiffOn zero_lt_one v hψ
  rw [SobolevIntervalZero.rep_left_eq_zero zero_lt_one hv,
    SobolevIntervalZero.rep_right_eq_zero zero_lt_one hv, zero_mul, zero_mul, sub_zero,
    zero_sub, deriv_deriv_sinUnitFun] at ibp
  rw [intervalIntegral.integral_eq_setIntegral_Ioo zero_le_one,
    intervalIntegral.integral_eq_setIntegral_Ioo zero_le_one] at ibp
  have e1 : ∫ x in Ioo (0 : ℝ) 1, (h.pL x * deriv (sinElem n) 1 x * deriv v 1 x
      + (0 : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) x * deriv (sinElem n) 1 x * deriv v 0 x
      + h.qL x * deriv (sinElem n) 0 x * deriv v 0 x)
      = ∫ x in Ioo (0 : ℝ) 1, deriv v 1 x * _root_.deriv (sinUnitFun n) x := by
    refine integral_congr_ae ?_
    filter_upwards [h.coeFn_pL, h.coeFn_qL, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)),
      coeFn_deriv_sinElem_one n] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4, Pi.zero_apply]
    ring
  have e2 : ∫ x in Ioo (0 : ℝ) 1, rep v x * (-(((n : ℝ) + 1) * π) ^ 2 * sinUnitFun n x)
      = -(((n : ℝ) + 1) * π) ^ 2 * ∫ x in Ioo (0 : ℝ) 1, sinUnitLp n x * deriv v 0 x := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sinUnitLp n, fn_ae_eq_rep zero_lt_one v] with x h1 h2
    rw [h1, deriv_zero, h2]
    ring
  rw [e1, ibp, e2]
  ring

open Real in
/-- **`T sₙ = sₙ / ((n+1)²π²)`** (the Example of [brezis2011functional] §8.6): the sine `sₙ` is
an eigenvector of the solution operator of `−u''` with eigenvalue `((n+1)²π²)⁻¹`. -/
theorem solutionOperator_sinUnitLp (n : ℕ) :
    solutionOperator hypotheses_one_zero (sinUnitLp n) = (((n + 1) * π) ^ 2)⁻¹ • sinUnitLp n := by
  have hpos : (0 : ℝ) < ((n + 1) * π) ^ 2 := by positivity
  have hsol : solution hypotheses_one_zero (sinUnitLp n) = (((n + 1) * π) ^ 2)⁻¹ • sinElem n := by
    refine (eq_solution_of_isGalerkinSolution hypotheses_one_zero
      ⟨(SobolevIntervalZero 0 1).smul_mem _ (sinElem_mem n), fun v hv ↦ ?_⟩).symm
    rw [map_smul, smul_apply, form_sinElem n hv, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hpos.ne', one_mul]
  rw [solutionOperator_apply, hsol, SobolevInterval.deriv_smul, deriv_sinElem_zero]

/-- The Hilbert basis `sinBasisUnit` consists of eigenvectors of the solution operator. -/
theorem solutionOperator_sinBasisUnit (n : ℕ) :
    solutionOperator hypotheses_one_zero (sinBasisUnit n)
      = (((n + 1) * Real.pi) ^ 2)⁻¹ • sinBasisUnit n := by
  rw [coe_sinBasisUnit]; exact solutionOperator_sinUnitLp n

/-- **The coefficients of an eigenvector of `T` in the sine basis**: if `T e = μ e` then
`(((n+1)²π²)⁻¹ − μ) ⟪sₙ, e⟫ = 0` for every `n`, by symmetry of `T`. -/
theorem inner_sinBasisUnit_eq_zero_of_eigen {e : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))} {μ : ℝ}
    (he : solutionOperator hypotheses_one_zero e = μ • e) (n : ℕ) :
    ((((n + 1) * Real.pi) ^ 2)⁻¹ - μ) * ⟪sinBasisUnit n, e⟫_ℝ = 0 := by
  have h1 : ⟪sinBasisUnit n, solutionOperator hypotheses_one_zero e⟫_ℝ
      = ⟪solutionOperator hypotheses_one_zero (sinBasisUnit n), e⟫_ℝ :=
    (isSymmetric_solutionOperator hypotheses_one_zero (sinBasisUnit n) e).symm
  rw [he, solutionOperator_sinBasisUnit, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    at h1
  linarith

/-- An eigenvector of `T` with eigenvalue `μ` has some nonzero coefficient, which identifies
`μ` as some `((n+1)²π²)⁻¹`. -/
theorem exists_eq_inv_of_eigen {e : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))} (he0 : e ≠ 0) {μ : ℝ}
    (he : solutionOperator hypotheses_one_zero e = μ • e) :
    ∃ n : ℕ, μ = (((n + 1) * Real.pi) ^ 2)⁻¹ ∧ ⟪sinBasisUnit n, e⟫_ℝ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ n, ⟪sinBasisUnit n, e⟫_ℝ = 0 := fun n ↦ by
    have := inner_sinBasisUnit_eq_zero_of_eigen he n
    rcases mul_eq_zero.1 this with h | h
    · exact hcon n (by linarith)
    · exact h
  refine he0 ?_
  have : sinBasisUnit.repr e = 0 := by
    ext n
    rw [HilbertBasis.repr_apply_apply, hzero n]
    rfl
  exact sinBasisUnit.repr.injective (this.trans (map_zero _).symm)

/-- An eigenvector of `T` with eigenvalue `((n+1)²π²)⁻¹` is a multiple of `sₙ`. -/
theorem eq_smul_sinBasisUnit_of_eigen {e : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))} {n : ℕ}
    (he : solutionOperator hypotheses_one_zero e = (((n + 1) * Real.pi) ^ 2)⁻¹ • e) :
    e = ⟪sinBasisUnit n, e⟫_ℝ • sinBasisUnit n := by
  classical
  refine sinBasisUnit.repr.injective ?_
  ext m
  rw [map_smul, HilbertBasis.repr_self, HilbertBasis.repr_apply_apply]
  by_cases hmn : m = n
  · subst hmn
    simp
  · have := inner_sinBasisUnit_eq_zero_of_eigen he m
    have hne : ((((m + 1) * Real.pi) ^ 2)⁻¹ - (((n + 1) * Real.pi) ^ 2)⁻¹) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      apply hmn
      have h' : ((m : ℝ) + 1) * Real.pi = ((n : ℝ) + 1) * Real.pi := by
        have hpos : ∀ k : ℕ, (0 : ℝ) < ((k : ℝ) + 1) * Real.pi := fun k ↦ by positivity
        have h2 := inv_injective h
        exact (pow_left_inj₀ (hpos m).le (hpos n).le two_ne_zero).1 h2
      exact_mod_cast (mul_right_cancel₀ Real.pi_ne_zero h' |> add_right_cancel)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hne
    · rw [h]
      simp [hmn]

/-- Two orthonormal vectors cannot both be multiples of the same vector. -/
theorem orthonormal_ne_of_mem_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : ℕ → E} (hv : Orthonormal ℝ v) {i j : ℕ} (hij : i ≠ j) {s : E} {c d : ℝ}
    (hi : v i = c • s) (hj : v j = d • s) : False := by
  have h1 : ⟪v i, v j⟫_ℝ = 0 := by
    rw [orthonormal_iff_ite.1 hv i j]; simp [hij]
  have hi1 : ‖v i‖ = 1 := hv.1 i
  have hj1 : ‖v j‖ = 1 := hv.1 j
  rw [hi, hj, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq] at h1
  rw [hi, norm_smul, Real.norm_eq_abs] at hi1
  rw [hj, norm_smul, Real.norm_eq_abs] at hj1
  have hc : c ≠ 0 := by rintro rfl; simp at hi1
  have hd : d ≠ 0 := by rintro rfl; simp at hj1
  have hs : ‖s‖ ≠ 0 := by rintro h; rw [h] at hi1; simp at hi1
  exact absurd h1 (by positivity)

/-- **The Example of [brezis2011functional] §8.6, eigenvalues**: for `p = 1`, `q = 0` on
`(0, 1)`, the eigenvalues of Theorem 8.22 are exactly the numbers `(n+1)²π²`, `n ∈ ℕ`, and each
is simple: `eigenvalue h` is injective with range `{(n+1)²π² | n}`. -/
theorem eigenvalue_eq_sq_pi_sq :
    range (eigenvalue hypotheses_one_zero) = range (fun n : ℕ ↦ ((n + 1) * Real.pi) ^ 2) ∧
      Function.Injective (eigenvalue hypotheses_one_zero) := by
  set h := hypotheses_one_zero with hh
  have hpos : ∀ k : ℕ, (0 : ℝ) < ((k : ℝ) + 1) * Real.pi := fun k ↦ by positivity
  -- each eigenvalue of `T` is some `((n+1)²π²)⁻¹`
  have key : ∀ j, ∃ n : ℕ, eigenvalueSeq h j = (((n + 1) * Real.pi) ^ 2)⁻¹ ∧
      eigenfunction h j = ⟪sinBasisUnit n, eigenfunction h j⟫_ℝ • sinBasisUnit n := fun j ↦ by
    obtain ⟨n, hn, -⟩ := exists_eq_inv_of_eigen (eigenfunction_ne_zero h j)
      (solutionOperator_eigenfunction h j)
    refine ⟨n, hn, eq_smul_sinBasisUnit_of_eigen ?_⟩
    rw [← hn]; exact solutionOperator_eigenfunction h j
  refine ⟨Set.ext fun l ↦ ⟨?_, ?_⟩, fun i j hij ↦ ?_⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨n, hn, -⟩ := key j
    exact ⟨n, by rw [eigenvalue, hn, inv_inv]⟩
  · rintro ⟨n, rfl⟩
    -- `sₙ` is orthogonal to every `e_j` with a different eigenvalue; not all, so some `μ_j = cₙ`
    by_contra hcon
    have hall : ∀ j, ⟪eigenfunction h j, sinBasisUnit n⟫_ℝ = 0 := fun j ↦ by
      have h1 : ⟪solutionOperator h (eigenfunction h j), sinBasisUnit n⟫_ℝ
          = ⟪eigenfunction h j, solutionOperator h (sinBasisUnit n)⟫_ℝ :=
        isSymmetric_solutionOperator h (eigenfunction h j) (sinBasisUnit n)
      rw [solutionOperator_eigenfunction, solutionOperator_sinBasisUnit, inner_smul_left,
        inner_smul_right, RCLike.conj_to_real] at h1
      have hne : eigenvalueSeq h j ≠ (((n + 1) * Real.pi) ^ 2)⁻¹ := fun heq ↦
        hcon ⟨j, by rw [eigenvalue, heq, inv_inv]⟩
      have : (eigenvalueSeq h j - (((n + 1) * Real.pi) ^ 2)⁻¹)
          * ⟪eigenfunction h j, sinBasisUnit n⟫_ℝ = 0 := by linarith
      rcases mul_eq_zero.1 this with h2 | h2
      · exact absurd (sub_eq_zero.1 h2) hne
      · exact h2
    have : (eigenfunction h).repr (sinBasisUnit n) = 0 := by
      ext j
      rw [HilbertBasis.repr_apply_apply, hall j]
      rfl
    have h0 : sinBasisUnit n = 0 := (eigenfunction h).repr.injective (this.trans (map_zero _).symm)
    exact sinBasisUnit.orthonormal.ne_zero n h0
  · by_contra hne
    obtain ⟨n, hn, hi⟩ := key i
    obtain ⟨m, hm, hj⟩ := key j
    have hmn : m = n := by
      have : (((m + 1) * Real.pi) ^ 2)⁻¹ = (((n + 1) * Real.pi) ^ 2)⁻¹ := by
        rw [← hm, ← hn]
        exact (inv_injective (hij : (eigenvalueSeq h i)⁻¹ = (eigenvalueSeq h j)⁻¹)).symm
      have h2 := inv_injective this
      have h' := (pow_left_inj₀ (hpos m).le (hpos n).le two_ne_zero).1 h2
      exact_mod_cast (mul_right_cancel₀ Real.pi_ne_zero h' |> add_right_cancel)
    subst hmn
    exact orthonormal_ne_of_mem_span (eigenfunction h).orthonormal hne hi hj

/-- **The Example of [brezis2011functional] §8.6**, assembled: for `p = 1`, `q = 0` on `(0, 1)`,
the sines `sₙ = √2 sin((n+1)πx)` (the Hilbert basis `sinBasisUnit` of `L²(0, 1)`) are
eigenvectors of the solution operator with eigenvalues `((n+1)²π²)⁻¹`, and the eigenvalues of
Theorem 8.22 are exactly the `(n+1)²π²`, each simple. -/
theorem sineHilbertBasis :
    (∀ n : ℕ, solutionOperator hypotheses_one_zero (sinBasisUnit n)
      = (((n + 1) * Real.pi) ^ 2)⁻¹ • sinBasisUnit n) ∧
    range (eigenvalue hypotheses_one_zero) = range (fun n : ℕ ↦ ((n + 1) * Real.pi) ^ 2) ∧
    Function.Injective (eigenvalue hypotheses_one_zero) :=
  ⟨solutionOperator_sinBasisUnit, eigenvalue_eq_sq_pi_sq.1, eigenvalue_eq_sq_pi_sq.2⟩

/-- The second derivative of `e ∈ C²[0, 1]` at an interior point is `deriv` of the derivative. -/
theorem deriv_shift_extend_eq (e : ContDiffMapIcc (zero_le_one' ℝ) 2) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    _root_.deriv e.shift.extend x = e.deriv 2 ⟨x, Ioo_subset_Icc_self hx⟩ :=
  ((e.shift.hasDerivWithinAt_extend ⟨x, Ioo_subset_Icc_self hx⟩).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)).deriv

/-- An element of `C²[0, 1]` whose function vanishes almost everywhere on `(0, 1)` is zero. -/
theorem contDiffMapIcc_eq_zero_of_ae_eq_zero (e : ContDiffMapIcc (zero_le_one' ℝ) 2)
    (h : e.extend =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun _ ↦ (0 : ℝ)) : e = 0 := by
  have heq := eqOn_Icc_of_ae_eq zero_lt_one e.extend.continuous.continuousOn continuousOn_const h
  refine ContDiffMapIcc.coe_injective zero_lt_one ?_
  funext t
  have := heq t.2
  rw [ContDiffMapIcc.extend_val] at this
  exact this

open SobolevInterval Real in
/-- **The Dirichlet eigenfunctions of `−u''` on `(0, 1)` are sines** (Comments on Chapter 8 of
[brezis2011functional], 3 (i), at `p = 1`, `q = 0`): if `e ∈ C²[0, 1]`, `e ≠ 0`, satisfies
`−e'' = λ e` on `[0, 1]` and `e(0) = e(1) = 0`, then `λ = (n+1)²π²` for some `n` and
`e = c sin((n+1)πx)` on `[0, 1]` for some `c ≠ 0`. A corollary of the sine expansion of
eigenvectors of the solution operator — no uniqueness theorem for the ODE is needed. -/
theorem eq_smul_sin_of_dirichlet (e : ContDiffMapIcc (zero_le_one' ℝ) 2) {l : ℝ}
    (hode : ∀ x : Icc (0 : ℝ) 1, -e.deriv 2 x = l * e x)
    (h0 : e ⟨0, left_mem_Icc.2 zero_le_one⟩ = 0) (h1 : e ⟨1, right_mem_Icc.2 zero_le_one⟩ = 0)
    (hne : e ≠ 0) :
    ∃ n : ℕ, l = ((n + 1) * π) ^ 2 ∧
      ∃ c : ℝ, c ≠ 0 ∧ ∀ x ∈ Icc (0 : ℝ) 1, e.extend x = c * sin ((n + 1) * π * x) := by
  set h := hypotheses_one_zero with hh
  set E := ofContDiffMapIcc zero_lt_one e with hEdef
  set eL := deriv E 0 with heLdef
  have heL : (eL : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] e.extend :=
    deriv_ofContDiffMapIcc_zero zero_lt_one e
  -- the datum `λ e` and the weak equation
  have hfL : ((l • eL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x ↦ l * e.extend x := by
    filter_upwards [Lp.coeFn_smul l eL, heL] with x hx1 hx2
    rw [hx1, Pi.smul_apply, smul_eq_mul, hx2]
  have hweak := isWeakSolution_of_classical zero_lt_one (α := fun _ ↦ (1 : ℝ))
    (β := fun _ ↦ (0 : ℝ)) (γ := fun _ ↦ (0 : ℝ)) (f := fun x ↦ l * e.extend x) h.pL 0 h.qL
    (l • eL) h.coeFn_pL (Lp.coeFn_zero ℝ ⊤ _) h.coeFn_qL hfL contDiffOn_const continuousOn_const
    continuousOn_const e
    (fun x hx ↦ by
      have hx' := Ioo_subset_Icc_self hx
      have := hode ⟨x, hx'⟩
      rw [show (fun t ↦ (1 : ℝ) * e.shift.extend t) = e.shift.extend from funext fun t ↦ one_mul _,
        deriv_shift_extend_eq e hx, zero_mul, zero_mul, add_zero, add_zero,
        ContDiffMapIcc.extend_of_mem e hx']
      exact this)
    (by rw [ContDiffMapIcc.extend_of_mem e (left_mem_Icc.2 zero_le_one)]; exact h0)
    (by rw [ContDiffMapIcc.extend_of_mem e (right_mem_Icc.2 zero_le_one)]; exact h1)
  have hsol : E = solution h (l • eL) := eq_solution_of_isGalerkinSolution h hweak
  have hT : solutionOperator h (l • eL) = eL := by
    rw [solutionOperator_apply, ← hsol]
  -- `e ≠ 0` forces `eL ≠ 0` and `λ ≠ 0`
  have heL0 : eL ≠ 0 := fun h0 ↦ hne (contDiffMapIcc_eq_zero_of_ae_eq_zero e (by
    refine heL.symm.trans ?_
    rw [h0]
    exact Lp.coeFn_zero ℝ 2 _))
  have hl : l ≠ 0 := by
    rintro rfl
    rw [zero_smul, map_zero] at hT
    exact heL0 hT.symm
  have heig : solutionOperator h eL = l⁻¹ • eL := by
    rw [map_smul] at hT
    have := congrArg (fun z ↦ l⁻¹ • z) hT
    simp only [smul_smul, inv_mul_cancel₀ hl, one_smul] at this
    exact this
  obtain ⟨n, hn, -⟩ := exists_eq_inv_of_eigen heL0 heig
  have hln : l = ((n + 1) * π) ^ 2 := by
    rw [← inv_inv l, hn, inv_inv]
  have hexp := eq_smul_sinBasisUnit_of_eigen (hn ▸ heig)
  set c := ⟪sinBasisUnit n, eL⟫_ℝ with hcdef
  have hc : c ≠ 0 := fun hc0 ↦ heL0 (by rw [hexp, hc0, zero_smul])
  refine ⟨n, hln, c * √2, mul_ne_zero hc (by positivity), fun x hx ↦ ?_⟩
  have hae : e.extend =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ c * √2 * sin ((n + 1) * π * x) := by
    filter_upwards [heL, Lp.coeFn_smul c (sinBasisUnit n), coeFn_sinBasisUnit n] with x hx1 hx2 hx3
    rw [← hx1, hexp, hx2, Pi.smul_apply, smul_eq_mul, hx3]
    ring
  exact eqOn_Icc_of_ae_eq zero_lt_one e.extend.continuous.continuousOn (by fun_prop) hae hx

end EllipticInterval.SturmLiouville
