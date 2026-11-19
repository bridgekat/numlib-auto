/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter09.Section03
import Numlib.Analysis.Sobolev.Interval
import Numlib.IntegralEquations.L2Kernel
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Generalized inverses of linear differential operators

Section 9.5 of [benIsrael2003generalized] describes differential
expressions on specified domains and Green kernels that solve the resulting
operator equations. The solutions represented by kernels on `L²` agree
almost everywhere, and the input to a generalized kernel is in the actual
range of the differential operator.

## Deviations from the source

* The interval operators use weak Sobolev derivatives and endpoint traces.
* In Exercise 26(b), the first product is the maximal inverse restricted
  to the adjoint domain, which is a proper subspace of the full space.
* In Exercise 34(c)–(d), both Hilbert adjoints of the inverse products
  are the full orthogonal projections.
-/

noncomputable section

namespace BenIsraelGreville.Chapter09

open MeasureTheory Set Filter
open scoped Distributions ENNReal InnerProductSpace Topology

section DifferentialExpression

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Equation (46)** of [benIsrael2003generalized], Chapter 9.
The first-order differential expression with time-dependent coefficients. -/
def differentialExpression (A₁ A₀ : ℝ → V →L[ℝ] W) (u : ℝ → V) (t : ℝ) : W :=
  A₁ t (deriv u t) + A₀ t (u t)

/-- The first-order display for matrix-valued coefficients acting on column vectors. -/
def matrixDifferentialExpression {m n : ℕ} (A₁ A₀ : ℝ → Matrix (Fin m) (Fin n) ℝ)
    (u : ℝ → Fin n → ℝ) (t : ℝ) : Fin m → ℝ :=
  (A₁ t).mulVec (deriv u t) + (A₀ t).mulVec (u t)

/-- **Equation (49)** of [benIsrael2003generalized], Chapter 9.
The scalar differential expression of order `n`. -/
def scalarDifferentialExpression {n : ℕ} (a : Fin (n + 1) → ℝ → ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ j, a j t * iteratedDeriv j.val u t

/-- **Equation (56)** of [benIsrael2003generalized], Chapter 9.
The two endpoint values of a vector function, in boundary-matrix order. -/
def vectorBoundaryValues {n : ℕ} (a b : ℝ) (u : ℝ → Fin n → ℝ) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim (u a) (u b)

/-- **Equation (50)** of [benIsrael2003generalized], Chapter 9.
The derivatives through order `n−1`, taken within the interval at both endpoints. -/
def scalarBoundaryValues (n : ℕ) (a b : ℝ) (u : ℝ → ℝ) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun j : Fin n => iteratedDerivWithin j.val u (Icc a b) a)
    (fun j : Fin n => iteratedDerivWithin j.val u (Icc a b) b)

/-- The scalar jet used to reduce an equation of order `n+1` to first order. -/
def scalarJet (n : ℕ) (u : ℝ → ℝ) (t : ℝ) : Fin (n + 1) → ℝ :=
  fun j => iteratedDeriv j.val u t

/-- The derivative coefficient in the first-order form of a scalar equation.
It retains the leading coefficient in the final row. -/
def scalarCompanionLeading {n : ℕ} (a : Fin (n + 2) → ℝ → ℝ) (t : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (Fin.lastCases (a (Fin.last (n + 1)) t) (fun _ : Fin n => 1))

/-- The remaining coefficient in the first-order form of a scalar equation. -/
def scalarCompanionLower {n : ℕ} (a : Fin (n + 2) → ℝ → ℝ) (t : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.lastCases (a j.castSucc t) (fun k : Fin n => if j = k.succ then -1 else 0) i

/-- **Exercise 31** of [benIsrael2003generalized], Chapter 9.
The vector differential expression applied to the scalar jet has zero
first rows and the original scalar differential expression in its last row. -/
theorem exercise_9_31 {n : ℕ} (a : Fin (n + 2) → ℝ → ℝ) (u : ℝ → ℝ) (t : ℝ)
    (hu : ∀ j : Fin (n + 1), DifferentiableAt ℝ (iteratedDeriv j.val u) t) :
    matrixDifferentialExpression (scalarCompanionLeading a) (scalarCompanionLower a)
      (scalarJet n u) t =
      Pi.single (Fin.last n) (scalarDifferentialExpression a u t) := by
  have hd : deriv (scalarJet n u) t = fun j => iteratedDeriv (j.val + 1) u t := by
    unfold scalarJet
    rw [deriv_pi hu]
    funext j
    exact congrFun iteratedDeriv_succ.symm t
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [matrixDifferentialExpression, hd, Pi.add_apply, scalarCompanionLeading,
      Matrix.mulVec_diagonal]
    simp only [Fin.lastCases_last, Fin.val_last, Pi.single_eq_same]
    rw [Matrix.mulVec, dotProduct, scalarDifferentialExpression,
      Fin.sum_univ_castSucc (fun j : Fin (n + 2) => a j t * iteratedDeriv j.val u t)]
    simp only [scalarCompanionLower, Matrix.of_apply, Fin.lastCases_last, scalarJet,
      Fin.val_castSucc, Fin.val_last]
    rw [add_comm]
  · rw [matrixDifferentialExpression, hd, Pi.add_apply, scalarCompanionLeading,
      Matrix.mulVec_diagonal]
    simp only [Fin.lastCases_castSucc, one_mul, Fin.val_castSucc, Pi.single_eq_of_ne
      (Fin.castSucc_ne_last j)]
    rw [Matrix.mulVec, dotProduct]
    simp [scalarCompanionLower, scalarJet, ite_mul, Finset.sum_ite_eq']

/-- **Equations (54)–(55)** of [benIsrael2003generalized], Chapter 9.
A compatible boundary residual is canceled by applying any inner inverse
of the boundary matrix on the fundamental solutions. -/
theorem boundaryCorrection_of_innerInverse {m n : Type*} [Fintype m] [Fintype n]
    {B : Matrix m n ℝ} {U : Matrix n m ℝ} (hU : B.IsInnerInverse U)
    {r : m → ℝ} (hr : ∃ c : n → ℝ, B.mulVec c = r) :
    r + B.mulVec (-(U.mulVec r)) = 0 := by
  obtain ⟨c, rfl⟩ := hr
  rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.isInnerInverse_iff.mp hU, add_neg_cancel]

end DifferentialExpression

section InnerInverse

variable {𝕜 E F : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- A linear inner inverse specifies a preimage in the operator domain for
 each member of the operator's range. -/
def IsInnerInverseOnRange (L : E →ₗ.[𝕜] F) (G : L.toFun.range →ₗ[𝕜] E) : Prop :=
  ∀ y : L.toFun.range, (G y, (y : F)) ∈ L.graph

/-- The inner inverse identity on the actual domain of a partial operator. -/
theorem isInnerInverseOnRange_iff (L : E →ₗ.[𝕜] F) (G : L.toFun.range →ₗ[𝕜] E) :
    IsInnerInverseOnRange L G ↔
      ∀ x : L.domain, (G ⟨L x, ⟨x, rfl⟩⟩, L x) ∈ L.graph := by
  constructor
  · intro h x
    exact h ⟨L x, ⟨x, rfl⟩⟩
  · rintro h ⟨y, ⟨x, rfl⟩⟩
    exact h x

end InnerInverse

section GreenKernel

variable {𝕜 V W X : Type*} [RCLike 𝕜] [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W]
  [SMulCommClass ℝ 𝕜 W]
  {μ : Measure X}

/-- A Green kernel assigns a linear coefficient to each pair of points. -/
abbrev GreenKernel (𝕜 : Type*) (X : Type*) (V W : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W] :=
  X → X → V →L[𝕜] W

/-- **Equation (48)** of [benIsrael2003generalized], Chapter 9.
The kernel integral is taken over the measure on the original interval or domain. -/
def greenIntegral (G : GreenKernel 𝕜 X V W) (μ : Measure X) (y : X → V) (s : X) : W :=
  ∫ t, G s t (y t) ∂μ

/-- The kernel sends `y` to `x` in `L²`, with integrable rows for this input. -/
structure RepresentsGreenAction (G : GreenKernel 𝕜 X V W) (y : Lp V 2 μ) (x : Lp W 2 μ) : Prop where
  /-- The defining integral exists for almost every output point. -/
  integrable_row : ∀ᵐ s ∂μ, Integrable (fun t => G s t (y t)) μ
  /-- The output represents the almost-everywhere value of the integral. -/
  ae_eq_integral : ⇑x =ᵐ[μ] greenIntegral G μ y

variable {G : GreenKernel 𝕜 X V W}

omit [SMulCommClass ℝ 𝕜 W] in
/-- For a fixed input the kernel has at most one output in `L²`. -/
theorem RepresentsGreenAction.output_unique {y : Lp V 2 μ} {x x' : Lp W 2 μ}
    (h : RepresentsGreenAction G y x) (h' : RepresentsGreenAction G y x') : x = x' :=
  Lp.ext (h.ae_eq_integral.trans h'.ae_eq_integral.symm)

omit [SMulCommClass ℝ 𝕜 W] in
private theorem RepresentsGreenAction.add {y₁ y₂ : Lp V 2 μ} {x₁ x₂ : Lp W 2 μ}
    (h₁ : RepresentsGreenAction G y₁ x₁) (h₂ : RepresentsGreenAction G y₂ x₂) :
    RepresentsGreenAction G (y₁ + y₂) (x₁ + x₂) := by
  have he (s : X) : (fun t => G s t ((y₁ + y₂) t)) =ᵐ[μ] fun t => G s t (y₁ t) + G s t (y₂ t) := by
    filter_upwards [Lp.coeFn_add y₁ y₂] with t ht
    simp only [Pi.add_apply, ht, map_add]
  constructor
  · filter_upwards [h₁.integrable_row, h₂.integrable_row] with s hs₁ hs₂
    exact (hs₁.add hs₂).congr (he s).symm
  · filter_upwards [h₁.ae_eq_integral, h₂.ae_eq_integral, h₁.integrable_row,
      h₂.integrable_row, Lp.coeFn_add x₁ x₂] with s hs₁ hs₂ hi₁ hi₂ hs
    change (x₁ + x₂) s = ∫ t, G s t ((y₁ + y₂) t) ∂μ
    rw [integral_congr_ae (he s), integral_add hi₁ hi₂, hs, Pi.add_apply, hs₁, hs₂]
    rfl

private theorem RepresentsGreenAction.smul (c : 𝕜) {y : Lp V 2 μ} {x : Lp W 2 μ}
    (h : RepresentsGreenAction G y x) : RepresentsGreenAction G (c • y) (c • x) := by
  have he (s : X) : (fun t => G s t ((c • y) t)) =ᵐ[μ] fun t => c • G s t (y t) := by
    filter_upwards [Lp.coeFn_smul c y] with t ht
    simp only [Pi.smul_apply, ht, map_smul]
  constructor
  · filter_upwards [h.integrable_row] with s hs
    exact (hs.smul c).congr (he s).symm
  · filter_upwards [h.ae_eq_integral, Lp.coeFn_smul c x] with s hs ht
    change (c • x) s = ∫ t, G s t ((c • y) t) ∂μ
    rw [integral_congr_ae (he s), integral_smul, ht, Pi.smul_apply, hs]
    rfl

/-- **Equations (47)–(48)** of [benIsrael2003generalized], Chapter 9.
A generalized Green kernel sends each compatible right-hand side to a
solution in the actual operator domain. -/
def IsGeneralizedGreenKernel (L : Lp W 2 μ →ₗ.[𝕜] Lp V 2 μ) (G : GreenKernel 𝕜 X V W) : Prop :=
  ∀ y : L.toFun.range, ∃ x : L.domain, L x = (y : Lp V 2 μ) ∧ RepresentsGreenAction G y.val x.val

/-- **Equations (47)–(48)** of [benIsrael2003generalized], Chapter 9.
For an injective differential operator the Green kernel gives its inverse
on the range. -/
def IsGreenKernel (L : Lp W 2 μ →ₗ.[𝕜] Lp V 2 μ) (G : GreenKernel 𝕜 X V W) : Prop :=
  Function.Injective L ∧ IsGeneralizedGreenKernel L G

variable (L : Lp W 2 μ →ₗ.[𝕜] Lp V 2 μ) (G)

omit [SMulCommClass ℝ 𝕜 W] in
/-- In the ordinary Green case, the represented solution is unique. -/
theorem IsGreenKernel.existsUnique_solution (h : IsGreenKernel L G) (y : L.toFun.range) :
    ∃! x : L.domain, L x = (y : Lp V 2 μ) ∧ RepresentsGreenAction G y.val x.val := by
  obtain ⟨x, hx⟩ := h.2 y
  exact ⟨x, hx, fun z hz => h.1 (hz.1.trans hx.1.symm)⟩

variable {L G}

/-- The integral operator on compatible data associated with a generalized Green kernel. -/
def IsGeneralizedGreenKernel.toLinearMap (h : IsGeneralizedGreenKernel L G) :
    L.toFun.range →ₗ[𝕜] Lp W 2 μ where
  toFun y := (h y).choose.val
  map_add' y z := ((h (y + z)).choose_spec.2).output_unique
    (((h y).choose_spec.2).add ((h z).choose_spec.2))
  map_smul' c y := ((h (c • y)).choose_spec.2).output_unique (((h y).choose_spec.2).smul c)

/-- The chosen integral operator represents the same kernel action. -/
theorem IsGeneralizedGreenKernel.represents_toLinearMap (h : IsGeneralizedGreenKernel L G)
    (y : L.toFun.range) : RepresentsGreenAction G y.val (h.toLinearMap y) :=
  (h y).choose_spec.2

/-- On compatible data the resulting integral operator is an inner inverse. -/
theorem IsGeneralizedGreenKernel.isInnerInverseOnRange (h : IsGeneralizedGreenKernel L G) :
    IsInnerInverseOnRange L h.toLinearMap := by
  intro y
  exact L.mem_graph_iff.mpr ⟨(h y).choose, rfl, (h y).choose_spec.1⟩

/-- **Equations (47)–(48)** of [benIsrael2003generalized], Chapter 9.
A kernel is generalized Green precisely when it represents an inner
inverse of the operator on its range. -/
theorem isGeneralizedGreenKernel_iff_innerInverse (L : Lp W 2 μ →ₗ.[𝕜] Lp V 2 μ)
    (G : GreenKernel 𝕜 X V W) :
    IsGeneralizedGreenKernel L G ↔ ∃ F : L.toFun.range →ₗ[𝕜] Lp W 2 μ,
      IsInnerInverseOnRange L F ∧ ∀ y : L.toFun.range, RepresentsGreenAction G y.val (F y) := by
  constructor
  · intro h
    exact ⟨h.toLinearMap, h.isInnerInverseOnRange, h.represents_toLinearMap⟩
  · rintro ⟨F, hF, hG⟩ y
    obtain ⟨x, hx, hLx⟩ := L.mem_graph_iff.mp (hF y)
    exact ⟨x, hLx, hx.symm ▸ hG y⟩

end GreenKernel

section ContinuousGreenKernel

variable {𝕜 V W X : Type*} [RCLike 𝕜] [TopologicalSpace X] [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W]
  [SMulCommClass ℝ 𝕜 W] {μ : Measure X}

/-- Pointwise kernel action on continuous functions, with an integrable row
at every output point. -/
def RepresentsContinuousGreenAction (G : GreenKernel 𝕜 X V W) (y : C(X, V)) (x : C(X, W)) : Prop :=
  ∀ s, Integrable (fun t => G s t (y t)) μ ∧ x s = greenIntegral G μ y s

variable {G : GreenKernel 𝕜 X V W}

omit [SMulCommClass ℝ 𝕜 W] in
private theorem RepresentsContinuousGreenAction.output_unique {y : C(X, V)} {x x' : C(X, W)}
    (h : RepresentsContinuousGreenAction (μ := μ) G y x)
    (h' : RepresentsContinuousGreenAction (μ := μ) G y x') : x = x' :=
  ContinuousMap.ext fun s => (h s).2.trans (h' s).2.symm

omit [SMulCommClass ℝ 𝕜 W] in
private theorem RepresentsContinuousGreenAction.add {y₁ y₂ : C(X, V)} {x₁ x₂ : C(X, W)}
    (h₁ : RepresentsContinuousGreenAction (μ := μ) G y₁ x₁)
    (h₂ : RepresentsContinuousGreenAction (μ := μ) G y₂ x₂) :
    RepresentsContinuousGreenAction (μ := μ) G (y₁ + y₂) (x₁ + x₂) := by
  intro s
  simp only [ContinuousMap.add_apply, map_add, greenIntegral] at *
  refine ⟨(h₁ s).1.add (h₂ s).1, ?_⟩
  rw [integral_add (h₁ s).1 (h₂ s).1, (h₁ s).2, (h₂ s).2]
  rfl

private theorem RepresentsContinuousGreenAction.smul (c : 𝕜) {y : C(X, V)} {x : C(X, W)}
    (h : RepresentsContinuousGreenAction (μ := μ) G y x) :
    RepresentsContinuousGreenAction (μ := μ) G (c • y) (c • x) := by
  intro s
  simp only [ContinuousMap.smul_apply, map_smul, greenIntegral] at *
  refine ⟨(h s).1.smul c, ?_⟩
  rw [integral_smul, (h s).2]
  rfl

/-- **Equations (47)–(48)** of [benIsrael2003generalized], Chapter 9.
On continuous function spaces a generalized Green kernel gives a
particular solution and its pointwise integral representation for every
compatible right-hand side. -/
def IsContinuousGeneralizedGreenKernel (L : C(X, W) →ₗ.[𝕜] C(X, V))
    (G : GreenKernel 𝕜 X V W) : Prop :=
  ∀ y : L.toFun.range, ∃ x : L.domain, L x = (y : C(X, V)) ∧
    RepresentsContinuousGreenAction (μ := μ) G y.val x.val

/-- The ordinary Green kernel for an injective differential operator on
continuous functions. -/
def IsContinuousGreenKernel (L : C(X, W) →ₗ.[𝕜] C(X, V)) (G : GreenKernel 𝕜 X V W) : Prop :=
  Function.Injective L ∧ IsContinuousGeneralizedGreenKernel (μ := μ) L G

omit [SMulCommClass ℝ 𝕜 W] in
/-- The pointwise kernel gives the unique continuous solution on compatible data. -/
theorem IsContinuousGreenKernel.existsUnique_solution {L : C(X, W) →ₗ.[𝕜] C(X, V)}
    (h : IsContinuousGreenKernel (μ := μ) L G) (y : L.toFun.range) :
    ∃! x : L.domain, L x = (y : C(X, V)) ∧
      RepresentsContinuousGreenAction (μ := μ) G y.val x.val := by
  obtain ⟨x, hx⟩ := h.2 y
  exact ⟨x, hx, fun z hz => h.1 (hz.1.trans hx.1.symm)⟩

/-- The pointwise kernel's action on compatible continuous data is linear. -/
def IsContinuousGeneralizedGreenKernel.toLinearMap {L : C(X, W) →ₗ.[𝕜] C(X, V)}
    (h : IsContinuousGeneralizedGreenKernel (μ := μ) L G) :
    L.toFun.range →ₗ[𝕜] C(X, W) where
  toFun y := (h y).choose.val
  map_add' y z := ((h (y + z)).choose_spec.2).output_unique
    (((h y).choose_spec.2).add ((h z).choose_spec.2))
  map_smul' c y := ((h (c • y)).choose_spec.2).output_unique (((h y).choose_spec.2).smul c)

/-- A pointwise kernel is generalized Green precisely when it represents
an inner inverse on the range of the continuous realization. -/
theorem isContinuousGeneralizedGreenKernel_iff_innerInverse (L : C(X, W) →ₗ.[𝕜] C(X, V))
    (G : GreenKernel 𝕜 X V W) :
    IsContinuousGeneralizedGreenKernel (μ := μ) L G ↔ ∃ F : L.toFun.range →ₗ[𝕜] C(X, W),
      IsInnerInverseOnRange L F ∧
        ∀ y : L.toFun.range, RepresentsContinuousGreenAction (μ := μ) G y.val (F y) := by
  constructor
  · intro h
    refine ⟨h.toLinearMap, ?_, fun y => (h y).choose_spec.2⟩
    intro y
    exact L.mem_graph_iff.mpr ⟨(h y).choose, rfl, (h y).choose_spec.1⟩
  · rintro ⟨F, hF, hG⟩ y
    obtain ⟨x, hx, hLx⟩ := L.mem_graph_iff.mp (hF y)
    exact ⟨x, hLx, hx.symm ▸ hG y⟩

end ContinuousGreenKernel

section LoudProjection

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A normally solvable operator has a maximal inverse defined on the full target space. -/
theorem maximalTsengInverse_domain_eq_top_of_normallySolvable {L : E →ₗ.[𝕜] F}
    (hL : IsNormallySolvable L) : (maximalTsengInverse L).domain = ⊤ := by
  let := hL.2.completeSpace_coe
  have hsplit : L.domain = L.ker ⊔ carrier L :=
    (isDecomposable_of_isClosed L.ker_le_domain hL.1.isClosed_ker).2
  rw [maximalTsengInverse_domain L hsplit,
    Submodule.sup_orthogonal_of_hasOrthogonalProjection]

omit [CompleteSpace F] in
private theorem mem_maximalTsengInverse_graph_of_solution {L : E →ₗ.[𝕜] F} (hL : L.IsClosed)
    {y : F} (x : L.domain) (hy : y - L x ∈ L.toFun.rangeᗮ) :
    (y, L.kerᗮ.starProjection (x : E)) ∈ (maximalTsengInverse L).graph := by
  let := hL.isClosed_ker.completeSpace_coe
  let q := L.kerᗮ.starProjection (x : E)
  have hk : (x : E) - q ∈ L.ker := by
    rw [← Submodule.orthogonal_orthogonal L.ker]
    exact L.kerᗮ.sub_starProjection_mem_orthogonal x
  let k : L.domain := ⟨(x : E) - q, L.ker_le_domain hk⟩
  have hq : (x - k : L.domain).val = q := sub_sub_cancel _ _
  have hz : L k = 0 := L.coe_mem_ker_iff.mp hk
  have hqL : L (x - k) = L x := by rw [L.map_sub, hz, sub_zero]
  rw [maximalTsengInverse, mem_graph_tsengInverseOn_iff]
  refine ⟨x - k, ?_, hq, ?_⟩
  · rw [hq]
    exact L.kerᗮ.starProjection_apply_mem _
  · rwa [hqL]

omit [CompleteSpace F] in
/-- Applied to an image, the maximal inverse removes the kernel component of a preimage. -/
theorem maximalTsengInverse_apply_image {L : E →ₗ.[𝕜] F} (hL : L.IsClosed) (x : L.domain) :
    let h := isTsengInverse_maximalTsengInverse_of_isClosed hL
    maximalTsengInverse L ⟨L x, h.range_le_domain ⟨x, rfl⟩⟩ = L.kerᗮ.starProjection (x : E) := by
  dsimp only
  have h := mem_maximalTsengInverse_graph_of_solution hL x
    (show L x - L x ∈ L.toFun.rangeᗮ by rw [sub_self]; exact Submodule.zero_mem _)
  exact (LinearPMap.image_iff _ |>.mpr h).symm

/-- **Exercise 35**, Equation (63) of [benIsrael2003generalized], Chapter 9.
Project the input onto the range, apply an inner inverse, and remove the
kernel component of the result to obtain the maximal inverse. -/
theorem maximalInverse_eq_project_innerInverse {L : E →ₗ.[𝕜] F} (hL : IsNormallySolvable L)
    (G : L.toFun.range →ₗ[𝕜] E) (hG : IsInnerInverseOnRange L G)
    (y : (maximalTsengInverse L).domain) :
    letI := hL.2.completeSpace_coe
    maximalTsengInverse L y =
      L.kerᗮ.starProjection (G (L.toFun.range.orthogonalProjectionOnto (y : F))) := by
  let := hL.2.completeSpace_coe
  let r := L.toFun.range.orthogonalProjectionOnto (y : F)
  obtain ⟨x, hx, hLx⟩ := L.mem_graph_iff.mp (hG r)
  have hy : (y : F) - L x ∈ L.toFun.rangeᗮ := by
    rw [hLx]
    exact L.toFun.range.sub_starProjection_mem_orthogonal y
  have h := mem_maximalTsengInverse_graph_of_solution hL.1 x hy
  change (x : E) = G r at hx
  change maximalTsengInverse L y = L.kerᗮ.starProjection (G r)
  exact (LinearPMap.image_iff y.2 |>.mpr h).symm.trans (congrArg L.kerᗮ.starProjection hx)

private theorem isClosed_adjoint_range_of_normallySolvable {L : E →ₗ.[𝕜] F}
    (hL : IsNormallySolvable L) (hD : Dense (L.domain : Set E)) :
    IsClosed (L.adjoint.toFun.range : Set E) := by
  rw [range_adjoint_eq_orthogonal_ker_of_isNormallySolvable L hD hL]
  exact L.ker.isClosed_orthogonal

/-- **Exercise 35**, Equation (64) of [benIsrael2003generalized], Chapter 9.
The two range projections are the complements of the corresponding kernel projections. -/
theorem exercise_9_35_projection_complements {L : E →ₗ.[𝕜] F} (hL : IsNormallySolvable L)
    (hD : Dense (L.domain : Set E)) :
    letI := hL.1.isClosed_ker.completeSpace_coe
    letI := hL.2.completeSpace_coe
    letI := (isClosed_adjoint_range_of_normallySolvable hL hD).completeSpace_coe
    letI := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
    (∀ x : E, L.adjoint.toFun.range.starProjection x = x - L.ker.starProjection x) ∧
      ∀ y : F, L.toFun.range.starProjection y = y - L.adjoint.ker.starProjection y := by
  let := hL.1.isClosed_ker.completeSpace_coe
  let := hL.2.completeSpace_coe
  have hR := range_adjoint_eq_orthogonal_ker_of_isNormallySolvable L hD hL
  have hK := ker_adjoint_eq_orthogonal_range L hD
  let := (isClosed_adjoint_range_of_normallySolvable hL hD).completeSpace_coe
  let := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
  constructor
  · intro x
    have hx := L.ker.sub_starProjection_mem_orthogonal x
    apply Submodule.eq_starProjection_of_mem_orthogonal (hR.symm ▸ hx)
    rw [hR, sub_sub_cancel, Submodule.orthogonal_orthogonal]
    exact L.ker.starProjection_apply_mem _
  · intro y
    let z := L.adjoint.ker.starProjection y
    have hy : y - z ∈ L.adjoint.kerᗮ := L.adjoint.ker.sub_starProjection_mem_orthogonal y
    rw [hK, Submodule.orthogonal_orthogonal L.toFun.range] at hy
    apply Submodule.eq_starProjection_of_mem_orthogonal hy
    rw [sub_sub_cancel, ← hK]
    exact L.adjoint.ker.starProjection_apply_mem _

/-- **Exercise 34** of [benIsrael2003generalized], Chapter 9.
The two inverse products are projections and satisfy the two reflexive
Penrose equations on their actual domains. -/
theorem exercise_9_34 {L : E →ₗ.[𝕜] F} (hL : IsNormallySolvable L)
    (hD : Dense (L.domain : Set E)) :
    let S := maximalTsengInverse L
    let h := isTsengInverse_maximalTsengInverse_of_isClosed hL.1
    letI := hL.2.completeSpace_coe
    letI := (isClosed_adjoint_range_of_normallySolvable hL hD).completeSpace_coe
    (∀ x : L.domain,
      L ⟨S ⟨L x, h.range_le_domain ⟨x, rfl⟩⟩, h.inverse_range_le_domain ⟨_, rfl⟩⟩ = L x) ∧
    (∀ y : S.domain,
      S ⟨L ⟨S y, h.inverse_range_le_domain ⟨y, rfl⟩⟩, h.range_le_domain ⟨_, rfl⟩⟩ = S y) ∧
    (∀ y : S.domain,
      L ⟨S y, h.inverse_range_le_domain ⟨y, rfl⟩⟩ = L.toFun.range.starProjection (y : F)) ∧
    (∀ x : L.domain,
      S ⟨L x, h.range_le_domain ⟨x, rfl⟩⟩ = L.adjoint.toFun.range.starProjection (x : E)) := by
  let S := maximalTsengInverse L
  let h := isTsengInverse_maximalTsengInverse_of_isClosed hL.1
  let := hL.2.completeSpace_coe
  have hR := range_adjoint_eq_orthogonal_ker_of_isNormallySolvable L hD hL
  let := (isClosed_adjoint_range_of_normallySolvable hL hD).completeSpace_coe
  refine ⟨fun x => (lemma_2 h).2 ⟨L x, h.range_le_domain ⟨x, rfl⟩⟩ ⟨x, rfl⟩,
    fun y => (lemma_2 h).1 ⟨S y, h.inverse_range_le_domain ⟨y, rfl⟩⟩ ⟨y, rfl⟩, ?_, ?_⟩
  · intro y
    simpa only [hL.2.submodule_topologicalClosure_eq] using h.projections.2 y
  · intro x
    rw [maximalTsengInverse_apply_image hL.1 x]
    symm
    have hq := L.kerᗮ.starProjection_apply_mem (x : E)
    apply Submodule.eq_starProjection_of_mem_orthogonal (hR.symm ▸ hq)
    rw [hR]
    exact L.kerᗮ.sub_starProjection_mem_orthogonal x

/-- **Exercise 34(c)–(d)** of [benIsrael2003generalized], Chapter 9.
The Hilbert adjoints of both inverse products are the full orthogonal
projections. The first identity implies the restriction to the adjoint
differential domain stated in the exercise. -/
theorem exercise_9_34_adjoint_products {L : E →ₗ.[𝕜] F} (hL : IsNormallySolvable L)
    (hD : Dense (L.domain : Set E)) :
    let S := maximalTsengInverse L
    letI := hL.2.completeSpace_coe
    letI := (isClosed_adjoint_range_of_normallySolvable hL hD).completeSpace_coe
    (partialComp L S).adjoint = L.toFun.range.starProjection.toPMap ⊤ ∧
      (partialComp S L).adjoint = L.adjoint.toFun.range.starProjection.toPMap ⊤ := by
  let S := maximalTsengInverse L
  let := hL.2.completeSpace_coe
  let := (isClosed_adjoint_range_of_normallySolvable hL hD).completeSpace_coe
  let P := L.toFun.range.starProjection
  let Q := L.adjoint.toFun.range.starProjection
  let h := isTsengInverse_maximalTsengInverse_of_isClosed hL.1
  have hS : S.domain = ⊤ := maximalTsengInverse_domain_eq_top_of_normallySolvable hL
  obtain ⟨_, _, hP, hQ⟩ := exercise_9_34 hL hD
  have hLP (y : S.domain) : S y ∈ L.domain := h.inverse_range_le_domain ⟨y, rfl⟩
  have hSQ (x : L.domain) : L x ∈ S.domain := h.range_le_domain ⟨x, rfl⟩
  have hEqP : partialComp L S = P.toPMap ⊤ := by
    apply LinearPMap.ext
    · apply eq_top_iff.mpr
      intro y _
      have hy : y ∈ S.domain := hS ▸ Submodule.mem_top
      exact (partialComp_mem_domain L S y).mpr ⟨hy, hLP ⟨y, hy⟩⟩
    · intro y hy _
      have hyS : y ∈ S.domain := hS ▸ Submodule.mem_top
      rw [partialComp_apply L S y hyS (hLP ⟨y, hyS⟩)]
      exact hP ⟨y, hyS⟩
  have hEqQ : partialComp S L = Q.toPMap L.domain := by
    apply LinearPMap.ext
    · ext x
      exact (partialComp_mem_domain S L x).trans
        ⟨fun hx => hx.choose, fun hx => ⟨hx, hSQ ⟨x, hx⟩⟩⟩
    · intro x _ hx
      rw [partialComp_apply S L x hx (hSQ ⟨x, hx⟩)]
      exact hQ ⟨x, hx⟩
  change (partialComp L S).adjoint = P.toPMap ⊤ ∧ (partialComp S L).adjoint = Q.toPMap ⊤
  constructor
  · have htop : Dense ((⊤ : Submodule 𝕜 F) : Set F) := dense_univ
    rw [hEqP, P.toPMap_adjoint_eq_adjoint_toPMap_of_dense htop,
      show P.adjoint = P from isSelfAdjoint_starProjection L.toFun.range]
  · rw [hEqQ, Q.toPMap_adjoint_eq_adjoint_toPMap_of_dense hD,
      show Q.adjoint = Q from isSelfAdjoint_starProjection L.adjoint.toFun.range]

end LoudProjection

section LoudKernel

variable {𝕜 X V W : Type*} [RCLike 𝕜] [MeasurableSpace X]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
  [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] {μ : Measure X}

/-- **Exercise 35**, Equation (63) of [benIsrael2003generalized], Chapter 9.
The inner inverse in Loud's projection formula may be the integral
operator of any generalized Green kernel. -/
theorem maximalInverse_eq_project_greenKernel {L : Lp W 2 μ →ₗ.[𝕜] Lp V 2 μ}
    {G : GreenKernel 𝕜 X V W} (hL : IsNormallySolvable L) (hG : IsGeneralizedGreenKernel L G)
    (y : (maximalTsengInverse L).domain) :
    letI := hL.2.completeSpace_coe
    maximalTsengInverse L y =
      L.kerᗮ.starProjection (hG.toLinearMap (L.toFun.range.orthogonalProjectionOnto y.val)) :=
  maximalInverse_eq_project_innerInverse hL hG.toLinearMap hG.isInnerInverseOnRange y

end LoudKernel

section IntervalDerivative

open TopologicalSpace

/-- The real Hilbert space of square-integrable functions on a finite interval.
Endpoints have measure zero. -/
abbrev IntervalL2 (a b : ℝ) := Lp ℝ 2 (volume.restrict (Ioo a b))

variable {a b : ℝ}

private def intervalDerivativeGraphMap (S : Submodule ℝ (SobolevInterval 1 a b)) :
    S →L[ℝ] (IntervalL2 a b × IntervalL2 a b) :=
  ((SobolevInterval.derivL 1 a b 0).prod (SobolevInterval.derivL 1 a b 1)).comp S.subtypeL

private theorem intervalDerivativeGraphMap_apply (S : Submodule ℝ (SobolevInterval 1 a b)) (u : S) :
    intervalDerivativeGraphMap S u =
      (SobolevInterval.deriv u.val 0, SobolevInterval.deriv u.val 1) := rfl

private theorem intervalDerivativeGraph_singleValued (S : Submodule ℝ (SobolevInterval 1 a b)) :
    ∀ p ∈ (intervalDerivativeGraphMap S).toLinearMap.range, p.1 = 0 → p.2 = 0 := by
  rintro p ⟨u, rfl⟩ hu
  have h₀ : SobolevInterval.deriv u.val 0 = SobolevInterval.deriv (0 : SobolevInterval 1 a b) 0 :=
    hu
  have he : (u : SobolevInterval 1 a b) = 0 := SobolevMultiIndex.fnL_injective h₀
  change SobolevInterval.deriv u.val 1 = 0
  rw [he, SobolevInterval.deriv_zero_elem]

/-- Weak differentiation of real functions, with the domain prescribed by
its Sobolev lifts. -/
def intervalDerivative (S : Submodule ℝ (SobolevInterval 1 a b)) :
    IntervalL2 a b →ₗ.[ℝ] IntervalL2 a b :=
  (intervalDerivativeGraphMap S).toLinearMap.range.toLinearPMap

/-- The graph consists exactly of a permitted function and its weak first derivative. -/
theorem mem_intervalDerivative_graph_iff (S : Submodule ℝ (SobolevInterval 1 a b))
    {x y : IntervalL2 a b} : (x, y) ∈ (intervalDerivative S).graph ↔
      ∃ u : S, SobolevInterval.deriv u.val 0 = x ∧ SobolevInterval.deriv u.val 1 = y := by
  rw [intervalDerivative,
    Submodule.toLinearPMap_graph_eq _ (intervalDerivativeGraph_singleValued S)]
  change (∃ u : S, intervalDerivativeGraphMap S u = (x, y)) ↔ _
  simp only [intervalDerivativeGraphMap_apply, Prod.mk.injEq]

/-- A closed subspace of the first Sobolev space gives a closed differentiation operator. -/
theorem isClosed_intervalDerivative (S : Submodule ℝ (SobolevInterval 1 a b))
    (hS : IsClosed (S : Set (SobolevInterval 1 a b))) : (intervalDerivative S).IsClosed := by
  let := hS.completeSpace_coe
  let A := intervalDerivativeGraphMap S
  have hA : AntilipschitzWith 2 A := A.antilipschitz_of_bound fun u => by
    change ‖u.val‖ ≤ (2 : ℝ) * ‖A u‖
    rw [show A u = _ from intervalDerivativeGraphMap_apply S u, Prod.norm_def]
    exact (SobolevInterval.norm_le_add_norm_deriv u.val).trans
      (by simpa only [two_mul] using add_le_add (le_max_left _ _) (le_max_right _ _))
  change IsClosed ((intervalDerivative S).graph : Set (IntervalL2 a b × IntervalL2 a b))
  rw [intervalDerivative,
    Submodule.toLinearPMap_graph_eq _ (intervalDerivativeGraph_singleValued S)]
  exact hA.isClosed_range A.uniformContinuous

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 9.
The derivative with both endpoint traces fixed to zero. -/
abbrev dirichletDerivative (a b : ℝ) : IntervalL2 a b →ₗ.[ℝ] IntervalL2 a b :=
  intervalDerivative (SobolevIntervalZero a b)

/-- The derivative whose domain is the entire first Sobolev space. -/
abbrev freeDerivative (a b : ℝ) : IntervalL2 a b →ₗ.[ℝ] IntervalL2 a b :=
  intervalDerivative (⊤ : Submodule ℝ (SobolevInterval 1 a b))

private theorem intervalDerivative_domain_of_lift (S : Submodule ℝ (SobolevInterval 1 a b))
    (u : S) : SobolevInterval.deriv u.val 0 ∈ (intervalDerivative S).domain :=
  LinearPMap.mem_domain_of_mem_graph ((mem_intervalDerivative_graph_iff S).mpr ⟨u, rfl, rfl⟩)

/-- **Exercise 25(a)** of [benIsrael2003generalized], Chapter 9.
Test functions in the endpoint-zero domain make the derivative densely defined. -/
theorem dense_dirichletDerivative_domain (hab : a < b) :
    Dense ((dirichletDerivative a b).domain : Set (IntervalL2 a b)) := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨φ, hφ⟩ := exists_testFunction_norm_sub_toLp_le hab x (half_pos hε)
  obtain ⟨u, hu, he⟩ := SobolevIntervalZero.exists_mem_fn_ae_eq φ
  have hEq : SobolevInterval.deriv u 0 = φ.toLp₂ :=
    Lp.ext (he.trans φ.coeFn_toLp₂.symm)
  refine ⟨φ.toLp₂, ?_, hEq ▸ intervalDerivative_domain_of_lift _ ⟨u, hu⟩⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  exact hφ.trans_lt (half_lt_self hε)

/-- **Exercise 25(a)** of [benIsrael2003generalized], Chapter 9.
The endpoint-zero derivative is closed. -/
theorem isClosed_dirichletDerivative (a b : ℝ) : (dirichletDerivative a b).IsClosed :=
  isClosed_intervalDerivative _ (Submodule.isClosed_topologicalClosure _)

/-- **Exercise 25(a)** of [benIsrael2003generalized], Chapter 9.
The endpoint-zero derivative has trivial kernel. -/
theorem ker_dirichletDerivative (hab : a < b) : (dirichletDerivative a b).ker = ⊥ := by
  ext x
  rw [LinearPMap.mem_ker_iff, Submodule.mem_bot]
  constructor
  · rintro ⟨u, hu, hzero⟩
    have h := (mem_intervalDerivative_graph_iff (SobolevIntervalZero a b)).mp
      ((dirichletDerivative a b).mem_graph u)
    obtain ⟨v, hv₀, hv₁⟩ := h
    have hnorm : SobolevInterval.seminorm 1 a b v.val = 0 := by
      change ‖SobolevInterval.deriv v.val 1‖ = 0
      rw [hv₁, hzero, norm_zero]
    have hv : v.val = 0 := (SobolevIntervalZero.seminorm_eq_zero_iff hab v.2).mp hnorm
    rw [hv, SobolevInterval.deriv_zero_elem] at hv₀
    exact hu.trans hv₀.symm
  · rintro rfl
    exact ⟨0, rfl, map_zero _⟩

private theorem intervalL2_integrable (y : IntervalL2 a b) : IntegrableOn y (Ioo a b) := by
  apply (Lp.memLp y).integrable
  norm_num

private theorem intervalL2_intervalIntegrable (hab : a ≤ b) (y : IntervalL2 a b) :
    IntervalIntegrable y volume a b :=
  (intervalL2_integrable y).intervalIntegrable_of_Ioo (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)

/-- A constant function in the interval Hilbert space. -/
def intervalConstant (a b c : ℝ) : IntervalL2 a b :=
  (memLp_const (μ := volume.restrict (Ioo a b)) (p := 2) c).toLp (fun _ => c)

/-- The constant element agrees with its constant representative almost everywhere. -/
theorem intervalConstant_ae (a b c : ℝ) :
    ⇑(intervalConstant a b c) =ᵐ[volume.restrict (Ioo a b)] fun _ => c :=
  MemLp.coeFn_toLp _

/-- The integral of an `L²` vector on the interval. -/
def intervalIntegralCLM (a b : ℝ) : IntervalL2 a b →L[ℝ] ℝ :=
  innerSL ℝ (intervalConstant a b 1)

private theorem integralCLM_apply_eq (hab : a ≤ b) (y : IntervalL2 a b) :
    intervalIntegralCLM a b y = ∫ t in a..b, y t := by
  rw [intervalIntegralCLM, innerSL_apply_apply, L2.inner_eq_integral_mul,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [intervalConstant_ae a b 1] with t ht
  change intervalConstant a b 1 t * y t = y t
  rw [ht, one_mul]

private def sobolevOneOfWeakDerivative (x y : IntervalL2 a b)
    (h : HasWeakDerivOn x y (Opens.Ioo a b)) : SobolevInterval 1 a b :=
  SobolevInterval.mk ![x, y] (by
    intro j
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((intervalL2_integrable x).locallyIntegrableOn)
    · exact h)

private theorem firstDeriv_sobolevOneOfWeakDerivative (x y : IntervalL2 a b)
    (h : HasWeakDerivOn x y (Opens.Ioo a b)) :
    SobolevInterval.deriv (sobolevOneOfWeakDerivative x y h) 1 = y := rfl

/-- An `L²` input has a first Sobolev primitive with any prescribed left endpoint value. -/
theorem exists_intervalSobolev_primitive (hab : a < b) (y : IntervalL2 a b) (c : ℝ) :
    ∃ u : SobolevInterval 1 a b, SobolevInterval.deriv u 1 = y ∧
      EqOn (SobolevInterval.rep u) (fun x => c + ∫ t in a..x, y t) (Icc a b) := by
  let g : ℝ → ℝ := fun x => c + ∫ t in a..x, y t
  have hi := intervalL2_integrable y
  have hg : ContinuousOn g (Icc a b) := intervalIntegral.continuousOn_integral_of_integrableOn_Ioo
    hab.le hi c
  have hm : MemLp g 2 (volume.restrict (Ioo a b)) :=
    hg.memLp_top_restrict_Ioo.mono_exponent le_top
  let x := hm.toLp g
  have hw : HasWeakDerivOn x y (Opens.Ioo a b) :=
    (hasWeakDerivOn_integral hab.le hi c).congr_ae (MemLp.coeFn_toLp hm).symm
      Filter.EventuallyEq.rfl
  refine ⟨sobolevOneOfWeakDerivative x y hw, firstDeriv_sobolevOneOfWeakDerivative x y hw, ?_⟩
  exact SobolevInterval.rep_eq_of_continuousOn hab _ hg (MemLp.coeFn_toLp hm)

/-- **Exercise 25(a)** of [benIsrael2003generalized], Chapter 9.
The range of the endpoint-zero derivative is the space of functions with
zero integral. -/
theorem range_dirichletDerivative_eq_ker_integral (hab : a < b) :
    (dirichletDerivative a b).toFun.range = (intervalIntegralCLM a b).ker := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, _, hu⟩ := (mem_intervalDerivative_graph_iff (SobolevIntervalZero a b)).mp
      ((dirichletDerivative a b).mem_graph x)
    change intervalIntegralCLM a b (dirichletDerivative a b x) = 0
    rw [← hu, integralCLM_apply_eq hab.le,
      ← SobolevInterval.toContinuousMap_sub_eq_integral hab u.val
        ⟨a, left_mem_Icc.2 hab.le⟩ ⟨b, right_mem_Icc.2 hab.le⟩,
      (SobolevIntervalZero.toContinuousMap_eq_zero hab u.2).1,
      (SobolevIntervalZero.toContinuousMap_eq_zero hab u.2).2, sub_zero]
  · intro hy
    have hz : (∫ t in a..b, y t) = 0 := (integralCLM_apply_eq hab.le y).symm.trans hy
    obtain ⟨u, hu, he⟩ := exists_intervalSobolev_primitive hab y 0
    have hu₀ : u ∈ SobolevIntervalZero a b := SobolevIntervalZero.mem_of_rep_eq_zero hab u
      (by simpa using he (left_mem_Icc.2 hab.le))
      (by simpa only [zero_add, hz] using he (right_mem_Icc.2 hab.le))
    have h := (mem_intervalDerivative_graph_iff (SobolevIntervalZero a b)).mpr
      ⟨⟨u, hu₀⟩, rfl, hu⟩
    obtain ⟨x, _, hx⟩ := (dirichletDerivative a b).mem_graph_iff.mp h
    exact ⟨x, hx⟩

/-- **Exercise 25(a)** of [benIsrael2003generalized], Chapter 9.
Endpoint-zero differentiation is normally solvable. -/
theorem isNormallySolvable_dirichletDerivative (hab : a < b) :
    IsNormallySolvable (dirichletDerivative a b) := by
  refine ⟨isClosed_dirichletDerivative a b, ?_⟩
  rw [range_dirichletDerivative_eq_ker_integral hab]
  exact (intervalIntegralCLM a b).isClosed_ker

/-- **Exercise 25(a)** of [benIsrael2003generalized], Chapter 9.
The derivative has no null space to remove from its domain. -/
theorem carrier_dirichletDerivative (hab : a < b) :
    carrier (dirichletDerivative a b) = (dirichletDerivative a b).domain := by
  simp [carrier, ker_dirichletDerivative hab]

private theorem intervalInner_deriv_eq_neg {u v : SobolevInterval 1 a b}
    (hab : a < b) (hv : v ∈ SobolevIntervalZero a b) :
    ⟪SobolevInterval.deriv u 1, SobolevInterval.deriv v 0⟫_ℝ =
      -⟪SobolevInterval.deriv u 0, SobolevInterval.deriv v 1⟫_ℝ := by
  have he := SobolevInterval.integral_deriv_mul_eq_sub_integral_mul_deriv hab u
    (SobolevInterval.absolutelyContinuousOnInterval_rep hab.le v)
  rw [SobolevIntervalZero.rep_left_eq_zero hab hv, SobolevIntervalZero.rep_right_eq_zero hab hv,
    mul_zero, mul_zero, sub_self, zero_sub, intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo] at he
  have hd : deriv (SobolevInterval.rep v) =ᵐ[volume.restrict (Ioo a b)]
      SobolevInterval.deriv v 1 := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    exact (SobolevInterval.ae_deriv_rep_eq v).mono fun t ht hmt => ht (Ioo_subset_Ioc_self hmt)
  have hu : ⇑(SobolevInterval.deriv u 0) =ᵐ[volume.restrict (Ioo a b)] SobolevInterval.rep u :=
    SobolevInterval.fn_ae_eq_rep u
  have hv' : ⇑(SobolevInterval.deriv v 0) =ᵐ[volume.restrict (Ioo a b)] SobolevInterval.rep v :=
    SobolevInterval.fn_ae_eq_rep v
  rw [L2.inner_eq_integral_mul, L2.inner_eq_integral_mul]
  convert he using 1
  · exact integral_congr_ae (EventuallyEq.rfl.mul hv')
  · exact congrArg Neg.neg (integral_congr_ae (hu.mul hd.symm))

/-- **Exercise 25(b)** of [benIsrael2003generalized], Chapter 9.
The adjoint is minus the derivative on the whole first Sobolev space. -/
theorem mem_dirichletDerivative_adjoint_graph_iff (hab : a < b) {x y : IntervalL2 a b} :
    (x, y) ∈ (dirichletDerivative a b).adjoint.graph ↔
      ∃ u : SobolevInterval 1 a b,
        SobolevInterval.deriv u 0 = x ∧ -SobolevInterval.deriv u 1 = y := by
  let L := dirichletDerivative a b
  have hD : Dense (L.domain : Set (IntervalL2 a b)) := dense_dirichletDerivative_domain hab
  constructor
  · intro h
    obtain ⟨z, hz₀, hz₁⟩ := L.adjoint.mem_graph_iff.mp h
    change (z : IntervalL2 a b) = x at hz₀
    change L.adjoint z = y at hz₁
    have hw : HasWeakDerivOn x (-y : IntervalL2 a b) (Opens.Ioo a b) := by
      refine hasWeakDerivOn_iff.mpr ⟨(intervalL2_integrable x).locallyIntegrableOn,
        (intervalL2_integrable (-y)).locallyIntegrableOn, fun φ => ?_⟩
      let u := φ.toSobolevIntervalLp 2
      have hu : u ∈ SobolevIntervalZero a b := φ.toSobolevIntervalLp_mem
      let v : L.domain := ⟨SobolevInterval.deriv u 0, intervalDerivative_domain_of_lift _ ⟨u, hu⟩⟩
      have hv : L v = SobolevInterval.deriv u 1 :=
        (((LinearPMap.image_iff v.2).mpr ((mem_intervalDerivative_graph_iff
          (SobolevIntervalZero a b)).mpr
          ⟨⟨u, hu⟩, rfl, rfl⟩))).symm
      have e := L.adjoint_isFormalAdjoint hD z v
      change inner ℝ (L.adjoint z) (SobolevInterval.deriv u 0) =
        inner ℝ (z : IntervalL2 a b) (L v) at e
      rw [hz₁, hz₀, hv, L2.inner_eq_integral_mul, L2.inner_eq_integral_mul] at e
      have hu₀ : ⇑(SobolevInterval.deriv u 0) =ᵐ[volume.restrict (Ioo a b)] φ :=
        φ.fn_toSobolevIntervalLp_ae_eq
      have hu₁ : ⇑(SobolevInterval.deriv u 1) =ᵐ[volume.restrict (Ioo a b)] deriv φ :=
        φ.coeFn_deriv_toSobolevIntervalLp_one
      calc
        (∫ t in Ioo a b, deriv φ t * x t) = ∫ t in Ioo a b, x t * SobolevInterval.deriv u 1 t := by
          refine integral_congr_ae <| hu₁.mono fun t ht => ?_
          change deriv φ t * x t = x t * SobolevInterval.deriv u 1 t
          rw [ht, mul_comm]
        _ = ∫ t in Ioo a b, y t * SobolevInterval.deriv u 0 t := e.symm
        _ = -∫ t in Ioo a b, φ t * (-y : IntervalL2 a b) t := by
          rw [← integral_neg]
          refine integral_congr_ae ?_
          filter_upwards [hu₀, Lp.coeFn_neg y] with t ht ht'
          rw [ht, ht', Pi.neg_apply, mul_neg, neg_neg, mul_comm]
    refine ⟨sobolevOneOfWeakDerivative x (-y) hw, rfl, ?_⟩
    change -(-y) = y
    exact neg_neg y
  · rintro ⟨u, hu₀, hu₁⟩
    have hform (v : L.domain) : inner ℝ y (v : IntervalL2 a b) = inner ℝ x (L v) := by
      obtain ⟨w, hw₀, hw₁⟩ := (mem_intervalDerivative_graph_iff (SobolevIntervalZero a b)).mp
        (L.mem_graph v)
      rw [← hw₀, ← hw₁, ← hu₀, ← hu₁, inner_neg_left,
        intervalInner_deriv_eq_neg hab w.2, neg_neg]
    let z : L.adjoint.domain := ⟨x, L.mem_adjoint_domain_of_exists x ⟨y, hform⟩⟩
    exact L.adjoint.mem_graph_iff.mpr ⟨z, rfl, L.adjoint_apply_eq hD z hform⟩

/-- The adjoint graph identity as equality of partial operators. -/
theorem dirichletDerivative_adjoint_eq_neg_freeDerivative (hab : a < b) :
    (dirichletDerivative a b).adjoint = -freeDerivative a b := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, y⟩
  rw [mem_dirichletDerivative_adjoint_graph_iff hab]
  constructor
  · rintro ⟨u, hu₀, hu₁⟩
    have he := (mem_intervalDerivative_graph_iff (⊤ : Submodule ℝ (SobolevInterval 1 a b))).mpr
      ⟨⟨u, Submodule.mem_top⟩, hu₀, rfl⟩
    obtain ⟨z, hz₀, hz₁⟩ := (freeDerivative a b).mem_graph_iff.mp he
    refine (-freeDerivative a b).mem_graph_iff.mpr ⟨z, hz₀, ?_⟩
    rw [LinearPMap.neg_apply, hz₁]
    exact hu₁
  · intro h
    obtain ⟨z, hz₀, hz₁⟩ := (-freeDerivative a b).mem_graph_iff.mp h
    obtain ⟨u, hu₀, hu₁⟩ := (mem_intervalDerivative_graph_iff (⊤ : Submodule ℝ
      (SobolevInterval 1 a b))).mp
      ((freeDerivative a b).mem_graph z)
    exact ⟨u.val, hu₀.trans hz₀, by rw [hu₁, ← LinearPMap.neg_apply]; exact hz₁⟩

/-- **Exercise 25(b)** of [benIsrael2003generalized], Chapter 9.
The negative derivative with free endpoints is onto. -/
theorem range_dirichletDerivative_adjoint (hab : a < b) :
    (dirichletDerivative a b).adjoint.toFun.range = ⊤ := by
  apply eq_top_iff.mpr
  intro y _
  obtain ⟨u, hu, _⟩ := exists_intervalSobolev_primitive hab (-y) 0
  obtain ⟨z, _, hz⟩ := (dirichletDerivative a b).adjoint.mem_graph_iff.mp
    ((mem_dirichletDerivative_adjoint_graph_iff hab).mpr ⟨u, rfl, by rw [hu, neg_neg]⟩)
  exact ⟨z, hz⟩

/-- The adjoint carrier consists of its domain elements with zero mean, as
in **Exercise 25(b)** of [benIsrael2003generalized]. -/
theorem carrier_dirichletDerivative_adjoint (hab : a < b) :
    carrier (dirichletDerivative a b).adjoint =
      (dirichletDerivative a b).adjoint.domain ⊓ (dirichletDerivative a b).toFun.range := by
  have hD := dense_dirichletDerivative_domain hab
  have hR := (isNormallySolvable_dirichletDerivative hab).2
  rw [carrier, ker_adjoint_eq_orthogonal_range _ hD,
    Submodule.orthogonal_orthogonal_eq_closure, hR.submodule_topologicalClosure_eq]

/-- **Exercise 26(a,c)** of [benIsrael2003generalized], Chapter 9.
The derivative's maximal inverse commutes with adjoints and the maximal
inverse of the inverse recovers the original partial operator. -/
theorem exercise_9_26_adjoint_involution (hab : a < b) :
    (maximalTsengInverse (dirichletDerivative a b)).adjoint =
      maximalTsengInverse (dirichletDerivative a b).adjoint ∧
    maximalTsengInverse (maximalTsengInverse (dirichletDerivative a b)) =
      dirichletDerivative a b := by
  have h := theorem_2_involution_adjoint (isClosed_dirichletDerivative a b)
    (dense_dirichletDerivative_domain hab)
  exact ⟨h.2.1, h.1⟩

private theorem intervalInner_constant (hab : a ≤ b) (c : ℝ) (y : IntervalL2 a b) :
    ⟪intervalConstant a b c, y⟫_ℝ = c * intervalIntegralCLM a b y := by
  rw [L2.inner_eq_integral_mul, integralCLM_apply_eq hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  exact integral_congr_ae ((intervalConstant_ae a b c).mono fun t ht => by
    change intervalConstant a b c t * y t = c * y t
    rw [ht])

private theorem intervalIntegralCLM_constant (hab : a ≤ b) (c : ℝ) :
    intervalIntegralCLM a b (intervalConstant a b c) = (b - a) * c := by
  rw [integralCLM_apply_eq hab, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  rw [integral_congr_ae (intervalConstant_ae a b c), setIntegral_const,
    Real.volume_real_Ioo_of_le hab, smul_eq_mul]

/-- The orthogonal projection of an interval function onto the range of
the endpoint-zero derivative subtracts its mean. -/
theorem projection_range_dirichletDerivative (hab : a < b) (y : IntervalL2 a b) :
    letI := (isNormallySolvable_dirichletDerivative hab).2.completeSpace_coe
    (dirichletDerivative a b).toFun.range.starProjection y =
      y - intervalConstant a b ((∫ t in a..b, y t) / (b - a)) := by
  let := (isNormallySolvable_dirichletDerivative hab).2.completeSpace_coe
  let c := (∫ t in a..b, y t) / (b - a)
  let R := (dirichletDerivative a b).toFun.range
  change R.starProjection y = y - intervalConstant a b c
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · change _ ∈ (dirichletDerivative a b).toFun.range
    rw [range_dirichletDerivative_eq_ker_integral hab]
    change intervalIntegralCLM a b (y - intervalConstant a b c) = 0
    rw [map_sub, intervalIntegralCLM_constant hab.le, integralCLM_apply_eq hab.le]
    dsimp only [c]
    field_simp [(sub_pos.mpr hab).ne']
    simp
  · rw [sub_sub_cancel]
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro x hx
    have hx0 : intervalIntegralCLM a b x = 0 := by
      change x ∈ (dirichletDerivative a b).toFun.range at hx
      rwa [range_dirichletDerivative_eq_ker_integral hab] at hx
    rw [intervalInner_constant hab.le, hx0, mul_zero]

private theorem intervalIntegral_centered (y : IntervalL2 a b) (c : ℝ)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ∫ t in a..x, (y - intervalConstant a b c) t = (∫ t in a..x, y t) - (x - a) * c := by
  simp only [intervalIntegral.integral_of_le hx.1, integral_Ioc_eq_integral_Ioo]
  have hsub : Ioo a x ⊆ Ioo a b := Ioo_subset_Ioo_right hx.2
  have he' : (fun t => (y - intervalConstant a b c) t) =ᵐ[volume.restrict (Ioo a b)]
    fun t => y t - c := by
    filter_upwards [Lp.coeFn_sub y (intervalConstant a b c), intervalConstant_ae a b c] with t ht hc
    rw [ht, Pi.sub_apply, hc]
  have he : (fun t => (y - intervalConstant a b c) t) =ᵐ[volume.restrict (Ioo a x)]
    fun t => y t - c :=
    he'.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub))
  rw [integral_congr_ae he, integral_sub ((intervalL2_integrable y).mono_set hsub)
    (integrable_const _),
    setIntegral_const, Real.volume_real_Ioo_of_le hx.1, smul_eq_mul]

/-- **Exercise 25(e)** of [benIsrael2003generalized], Chapter 9.
The maximal inverse is the antiderivative after subtracting the input mean.
The displayed formula holds at every point for its continuous representative. -/
theorem exercise_9_25_maximalInverse (hab : a < b) (y : (maximalTsengInverse
  (dirichletDerivative a b)).domain) :
    ∃ u : SobolevInterval 1 a b, u ∈ SobolevIntervalZero a b ∧
      SobolevInterval.deriv u 0 = maximalTsengInverse (dirichletDerivative a b) y ∧
      EqOn (SobolevInterval.rep u) (fun x => (∫ t in a..x, (y.val : IntervalL2 a b) t) -
        ((x - a) / (b - a)) * ∫ t in a..b, (y.val : IntervalL2 a b) t) (Icc a b) := by
  let L := dirichletDerivative a b
  have hL := isNormallySolvable_dirichletDerivative hab
  let := hL.2.completeSpace_coe
  let S := maximalTsengInverse L
  let h := isTsengInverse_maximalTsengInverse_of_isClosed hL.1
  let z : L.domain := ⟨S y, h.inverse_range_le_domain ⟨y, rfl⟩⟩
  have hp := (exercise_9_34 hL (dense_dirichletDerivative_domain hab)).2.2.1 y
  change L z = L.toFun.range.starProjection (y.val : IntervalL2 a b) at hp
  rw [show L.toFun.range.starProjection y.val = _ from projection_range_dirichletDerivative hab
    y.val] at hp
  obtain ⟨u, hu₀, hu₁⟩ := (mem_intervalDerivative_graph_iff (SobolevIntervalZero a b)).mp
    (L.mem_graph z)
  refine ⟨u.val, u.2, hu₀, fun x hx => ?_⟩
  have he := SobolevInterval.toContinuousMap_sub_eq_integral hab u.val
    ⟨a, left_mem_Icc.2 hab.le⟩ ⟨x, hx⟩
  rw [(SobolevIntervalZero.toContinuousMap_eq_zero hab u.2).1, sub_zero, hu₁, hp,
    intervalIntegral_centered _ _ hx] at he
  change SobolevInterval.rep u.val x = _ at he
  rw [he]
  ring

/-- A real scalar kernel viewed as a kernel acting by scalar multiplication. -/
def scalarGreenKernel {X : Type*} (g : X → X → ℝ) : GreenKernel ℝ X ℝ ℝ :=
  fun s t => g s t • ContinuousLinearMap.id ℝ ℝ

/-- The explicit kernel of the derivative's maximal inverse in **Exercise 25(e)**. -/
def dirichletDerivativeMoorePenroseKernel (a b : ℝ) : GreenKernel ℝ ℝ ℝ ℝ :=
  scalarGreenKernel fun s t => (if t ≤ s then 1 else 0) - (s - a) / (b - a)

private theorem dirichletDerivativeMoorePenroseKernel_row (a b s : ℝ) (y : IntervalL2 a b) :
    Integrable (fun t => dirichletDerivativeMoorePenroseKernel a b s t (y t))
      (volume.restrict (Ioo a b)) := by
  have hy : Integrable y (volume.restrict (Ioo a b)) := intervalL2_integrable y
  have h₁ := hy.indicator (s := Iic s) measurableSet_Iic
  have h₂ := hy.const_mul ((s - a) / (b - a))
  convert h₁.sub h₂ using 1
  funext t
  change ((if t ≤ s then (1 : ℝ) else 0) - (s - a) / (b - a)) * y t = _
  by_cases ht : t ≤ s <;> simp [ht, indicator, sub_mul]

/-- The maximal inverse of the endpoint-zero derivative is represented by
its explicit mean-corrected Green kernel on every square-integrable input. -/
theorem exercise_9_25_greenKernel (hab : a < b) (y : (maximalTsengInverse
  (dirichletDerivative a b)).domain) :
    RepresentsGreenAction (dirichletDerivativeMoorePenroseKernel a b) y.val
      (maximalTsengInverse (dirichletDerivative a b) y) := by
  let z : IntervalL2 a b := y.val
  refine ⟨Eventually.of_forall fun s => dirichletDerivativeMoorePenroseKernel_row a b s z, ?_⟩
  obtain ⟨u, hu, hu₀, he⟩ := exercise_9_25_maximalInverse hab y
  rw [← hu₀]
  filter_upwards [SobolevInterval.fn_ae_eq_rep u, ae_restrict_mem measurableSet_Ioo] with s hs hsI
  change SobolevInterval.deriv u 0 s = _ at hs
  have hz : Integrable z (volume.restrict (Ioo a b)) := intervalL2_integrable z
  have h₁ := hz.indicator (s := Iic s) measurableSet_Iic
  have h₂ := hz.const_mul ((s - a) / (b - a))
  have hpt : (fun t => dirichletDerivativeMoorePenroseKernel a b s t (z t)) =
      fun t => (Iic s).indicator z t - ((s - a) / (b - a)) * z t := by
    funext t
    change ((if t ≤ s then (1 : ℝ) else 0) - (s - a) / (b - a)) * z t = _
    by_cases ht : t ≤ s <;> simp [ht, indicator, sub_mul]
  change SobolevInterval.deriv u 0 s = ∫ t, dirichletDerivativeMoorePenroseKernel a b s t
    (z t) ∂volume.restrict (Ioo a b)
  rw [hs, he (Ioo_subset_Icc_self hsI), hpt, integral_sub h₁ h₂,
    integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      integral_const_mul]
  change (∫ t in a..s, z t) - ((s - a) / (b - a)) * ∫ t in a..b, z t = _
  rw [intervalIntegral.integral_of_le hsI.1.le, intervalIntegral.integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo]
  have hi : Iic s ∩ Ioo a b = Ioc a s := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans_lt hsI.2⟩⟩
  rw [hi]
  simp_rw [integral_Ioc_eq_integral_Ioo]

private theorem exists_secondOrder_of_lifts (u v : SobolevInterval 1 a b)
    (h : SobolevInterval.deriv u 1 = SobolevInterval.deriv v 0) :
    ∃ w : SobolevInterval 2 a b,
      SobolevInterval.inclusionCLM 1 a b w = u ∧ SobolevInterval.derivCLM 1 a b w = v := by
  let p : Fin 3 → IntervalL2 a b := ![SobolevInterval.deriv u 0, SobolevInterval.deriv u 1,
    SobolevInterval.deriv v 1]
  have hp (j : Fin 3) : HasWeakIteratedDerivOn j.val (p 0) (p j) (Opens.Ioo a b) := by
    fin_cases j
    · exact SobolevInterval.hasWeakIteratedDerivOn_deriv u 0
    · exact SobolevInterval.hasWeakIteratedDerivOn_deriv u 1
    · have hv := SobolevInterval.hasWeakDerivOn_fn v
      change HasWeakDerivOn (SobolevInterval.deriv v 0) _ _ at hv
      rw [← h] at hv
      exact (SobolevInterval.hasWeakDerivOn_fn u).hasWeakIteratedDerivOn_succ hv
  refine ⟨SobolevInterval.mk p hp, SobolevInterval.ext fun j => ?_, SobolevInterval.ext fun j => ?_⟩
  · fin_cases j <;> rfl
  · fin_cases j
    · exact h
    · rfl

/-- **Exercise 25(c)** of [benIsrael2003generalized], Chapter 9.
The adjoint followed after the endpoint-zero derivative is the negative
second derivative with Dirichlet endpoint conditions. -/
theorem mem_dirichletSecondDerivative_graph_iff (hab : a < b) {x y : IntervalL2 a b} :
    (x, y) ∈ (partialComp (dirichletDerivative a b).adjoint (dirichletDerivative a b)).graph ↔
      ∃ w : SobolevInterval 2 a b, SobolevInterval.inclusionCLM 1 a b w ∈ SobolevIntervalZero a b ∧
        SobolevInterval.deriv w 0 = x ∧ -SobolevInterval.deriv w 2 = y := by
  rw [mem_graph_partialComp_iff]
  constructor
  · rintro ⟨z, hx, hy⟩
    obtain ⟨u, hu₀, hu₁⟩ := (mem_intervalDerivative_graph_iff (SobolevIntervalZero a b)).mp hx
    obtain ⟨v, hv₀, hv₁⟩ := (mem_dirichletDerivative_adjoint_graph_iff hab).mp hy
    obtain ⟨w, hw₀, hw₁⟩ := exists_secondOrder_of_lifts u.val v (hu₁.trans hv₀.symm)
    refine ⟨w, hw₀.symm ▸ u.2, ?_, ?_⟩
    · exact (congrArg (fun q : SobolevInterval 1 a b => SobolevInterval.deriv q 0) hw₀).trans hu₀
    · exact (congrArg (fun q : SobolevInterval 1 a b => -SobolevInterval.deriv q 1) hw₁).trans hv₁
  · rintro ⟨w, hw, hx, hy⟩
    refine ⟨SobolevInterval.deriv w 1, ?_, ?_⟩
    · exact (mem_intervalDerivative_graph_iff (SobolevIntervalZero a b)).mpr
        ⟨⟨SobolevInterval.inclusionCLM 1 a b w, hw⟩, hx, rfl⟩
    · exact (mem_dirichletDerivative_adjoint_graph_iff hab).mpr
        ⟨SobolevInterval.derivCLM 1 a b w, rfl, hy⟩

private theorem sobolevInterval_deriv_neg {m : ℕ} (u : SobolevInterval m a b) (j : Fin (m + 1)) :
    SobolevInterval.deriv (-u) j = -SobolevInterval.deriv u j :=
  map_neg (SobolevInterval.derivL m a b j) u

/-- **Exercise 25(d)** of [benIsrael2003generalized], Chapter 9.
The endpoint-zero derivative applied after its adjoint is the negative
second derivative with Neumann endpoint conditions. -/
theorem mem_neumannSecondDerivative_graph_iff (hab : a < b) {x y : IntervalL2 a b} :
    (x, y) ∈ (partialComp (dirichletDerivative a b) (dirichletDerivative a b).adjoint).graph ↔
      ∃ w : SobolevInterval 2 a b, SobolevInterval.derivCLM 1 a b w ∈ SobolevIntervalZero a b ∧
        SobolevInterval.deriv w 0 = x ∧ -SobolevInterval.deriv w 2 = y := by
  rw [mem_graph_partialComp_iff]
  constructor
  · rintro ⟨z, hx, hy⟩
    obtain ⟨u, hu₀, hu₁⟩ := (mem_dirichletDerivative_adjoint_graph_iff hab).mp hx
    obtain ⟨v, hv₀, hv₁⟩ := (mem_intervalDerivative_graph_iff (SobolevIntervalZero a b)).mp hy
    have he : SobolevInterval.deriv u 1 = SobolevInterval.deriv (-v.val) 0 := by
      rw [sobolevInterval_deriv_neg, hv₀, ← hu₁, neg_neg]
    obtain ⟨w, hw₀, hw₁⟩ := exists_secondOrder_of_lifts u (-v.val) he
    refine ⟨w, hw₁.symm ▸ (SobolevIntervalZero a b).neg_mem v.2, ?_, ?_⟩
    · exact (congrArg (fun q : SobolevInterval 1 a b => SobolevInterval.deriv q 0) hw₀).trans hu₀
    · have hh := congrArg (fun q : SobolevInterval 1 a b => -SobolevInterval.deriv q 1) hw₁
      rw [sobolevInterval_deriv_neg, neg_neg, hv₁] at hh
      exact hh
  · rintro ⟨w, hw, hx, hy⟩
    refine ⟨-SobolevInterval.deriv w 1, ?_, ?_⟩
    · exact (mem_dirichletDerivative_adjoint_graph_iff hab).mpr
        ⟨SobolevInterval.inclusionCLM 1 a b w, hx, rfl⟩
    · refine (mem_intervalDerivative_graph_iff (SobolevIntervalZero a b)).mpr
        ⟨⟨-(SobolevInterval.derivCLM 1 a b w), (SobolevIntervalZero a b).neg_mem hw⟩, ?_, ?_⟩
      · exact sobolevInterval_deriv_neg (SobolevInterval.derivCLM 1 a b w) 0
      · exact (sobolevInterval_deriv_neg (SobolevInterval.derivCLM 1 a b w) 1).trans hy

/-- **Exercise 25(c,d)** of [benIsrael2003generalized], Chapter 9.
The Dirichlet negative second derivative is onto. The Neumann negative
second derivative has exactly the zero-mean range of the first derivative. -/
theorem ranges_intervalSecondDerivatives (hab : a < b) :
    let L := dirichletDerivative a b
    (partialComp L.adjoint L).toFun.range = ⊤ ∧
      (partialComp L L.adjoint).toFun.range = L.toFun.range := by
  let L := dirichletDerivative a b
  let A := partialComp L.adjoint L
  let B := partialComp L L.adjoint
  have hL : IsNormallySolvable L := isNormallySolvable_dirichletDerivative hab
  have hD : Dense (L.domain : Set (IntervalL2 a b)) := dense_dirichletDerivative_domain hab
  have hs := exercise_9_9_gram L hD hL.1
  have hm := gramOperators_nonnegative L hL.1 hD
  obtain ⟨hA, hB, hKA, hKB, _, _, _, _⟩ := theorem_2_gramOperators L hL.1 hD
  have hRA := (isNormallySolvable_iff_orthogonal_ker_adjoint A hA.1.isClosed hm.2.1.dense_domain).mp
    (hs.1.mp hL)
  have hRB := (isNormallySolvable_iff_orthogonal_ker_adjoint B hB.1.isClosed
    hm.2.2.2.dense_domain).mp (hs.2.mp hL)
  rw [LinearPMap.isSelfAdjoint_def.mp hA.1, hKA, ker_dirichletDerivative hab,
    Submodule.bot_orthogonal_eq_top] at hRA
  let := hL.2.completeSpace_coe
  rw [LinearPMap.isSelfAdjoint_def.mp hB.1, hKB, ker_adjoint_eq_orthogonal_range L hD,
    Submodule.orthogonal_orthogonal L.toFun.range] at hRB
  exact ⟨hRA, hRB⟩

private theorem partialComp_domain_of_full {S T : IntervalL2 a b →ₗ.[ℝ] IntervalL2 a b}
    (hS : S.domain = ⊤) : (partialComp S T).domain = T.domain := by
  ext x
  simp [partialComp_mem_domain, hS]

private theorem maximalTsengInverse_eq_of_sub_mem_orthogonal
    {L : IntervalL2 a b →ₗ.[ℝ] IntervalL2 a b}
    {u v : (maximalTsengInverse L).domain} (h : (u : IntervalL2 a b) - (v : IntervalL2 a b) ∈
      L.toFun.rangeᗮ) :
    maximalTsengInverse L u = maximalTsengInverse L v := by
  let S := maximalTsengInverse L
  have hk : (u - v : S.domain).val ∈ S.ker := by
    rw [maximalTsengInverse_ker]
    exact h
  exact sub_eq_zero.mp ((S.map_sub u v).symm.trans (S.coe_mem_ker_iff.mp hk))

/-- **Exercise 26(b)** of [benIsrael2003generalized], Chapter 9.
The first product is the inverse restricted to the adjoint domain.
The second product gives the full maximal inverse. -/
theorem exercise_9_26_products (hab : a < b) :
    let L := dirichletDerivative a b
    let S := maximalTsengInverse L
    partialComp (maximalTsengInverse (partialComp L.adjoint L)) L.adjoint =
      S.domRestrict L.adjoint.domain ∧
      partialComp L.adjoint (maximalTsengInverse (partialComp L L.adjoint)) = S := by
  let L := dirichletDerivative a b
  let S := maximalTsengInverse L
  let V := maximalTsengInverse L.adjoint
  have hL : IsNormallySolvable L := isNormallySolvable_dirichletDerivative hab
  have hD : Dense (L.domain : Set (IntervalL2 a b)) := dense_dirichletDerivative_domain hab
  have hLa : IsNormallySolvable L.adjoint := (exercise_9_9_adjoint L hD hL.1).mp hL
  have hS : S.domain = ⊤ := maximalTsengInverse_domain_eq_top_of_normallySolvable hL
  have hV : V.domain = ⊤ := maximalTsengInverse_domain_eq_top_of_normallySolvable hLa
  have hS_mem (x : IntervalL2 a b) : x ∈ S.domain := hS ▸ Submodule.mem_top
  have hV_mem (x : IntervalL2 a b) : x ∈ V.domain := hV ▸ Submodule.mem_top
  have hVS : (partialComp V S).domain = ⊤ := (partialComp_domain_of_full hV).trans hS
  have hSV : (partialComp S V).domain = ⊤ := (partialComp_domain_of_full hS).trans hV
  obtain ⟨_, _, _, _, hA, hB, _, _⟩ := theorem_2_gramOperators L hL.1 hD
  change partialComp (maximalTsengInverse (partialComp L.adjoint L)) L.adjoint =
    S.domRestrict L.adjoint.domain ∧
    partialComp L.adjoint (maximalTsengInverse (partialComp L L.adjoint)) = S
  rw [hA, hB]
  constructor
  · apply LinearPMap.ext
    · rw [partialComp_domain_of_full hSV, LinearPMap.domRestrict_domain, hS, inf_top_eq]
    · intro x hx _
      have hx' := ((partialComp_mem_domain (partialComp S V) L.adjoint x).mp hx).choose
      let y : L.adjoint.domain := ⟨x, hx'⟩
      let z : V.domain := ⟨L.adjoint y, hV_mem _⟩
      have hstep : (partialComp (partialComp S V) L.adjoint) ⟨x, hx⟩ = S ⟨V z, hS_mem _⟩ := by
        rw [partialComp_apply _ _ x hx' (hSV ▸ Submodule.mem_top),
          partialComp_apply S V _ z.2 (hS_mem _)]
      rw [hstep]
      change S ⟨V z, hS_mem _⟩ = S ⟨x, hS_mem x⟩
      apply maximalTsengInverse_eq_of_sub_mem_orthogonal
      have hproj : V z = L.adjoint.kerᗮ.starProjection x := maximalTsengInverse_apply_image hLa.1 y
      let := hLa.1.isClosed_ker.completeSpace_coe
      have h := L.adjoint.kerᗮ.sub_starProjection_mem_orthogonal x
      rw [Submodule.orthogonal_orthogonal L.adjoint.ker] at h
      change V z - x ∈ L.toFun.rangeᗮ
      rw [hproj, ← neg_sub, ← ker_adjoint_eq_orthogonal_range L hD]
      exact Submodule.neg_mem _ h
  · have hStep (y : S.domain) : V ⟨S y, hV_mem _⟩ ∈ L.adjoint.domain :=
      (isTsengInverse_maximalTsengInverse_of_isClosed hLa.1).inverse_range_le_domain ⟨_, rfl⟩
    have hDom : ∀ x : IntervalL2 a b, x ∈ (partialComp L.adjoint (partialComp V S)).domain := by
      intro x
      refine (partialComp_mem_domain L.adjoint (partialComp V S) x).mpr ⟨hVS ▸ Submodule.mem_top,
        ?_⟩
      rw [partialComp_apply V S x (hS_mem x) (hV_mem _)]
      exact hStep ⟨x, hS_mem x⟩
    apply LinearPMap.ext (by rw [hS]; exact eq_top_iff.mpr fun x _ => hDom x)
    intro x hx hx'
    let w : S.domain := ⟨x, hx'⟩
    have eq : (partialComp V S) ⟨x, hVS ▸ Submodule.mem_top⟩ = V ⟨S w, hV_mem _⟩ :=
      partialComp_apply V S x hx' (hV_mem _)
    rw [partialComp_apply L.adjoint (partialComp V S) x (hVS ▸ Submodule.mem_top)
      (eq.symm ▸ hStep w)]
    have he : (⟨(partialComp V S) ⟨x, hVS ▸ Submodule.mem_top⟩,
      eq.symm ▸ hStep w⟩ : L.adjoint.domain) =
        ⟨V ⟨S w, hV_mem _⟩, hStep w⟩ := Subtype.ext eq
    rw [he]
    have h := (isTsengInverse_maximalTsengInverse_of_isClosed hLa.1).projections.2 ⟨S w, hV_mem _⟩
    have hR : L.adjoint.toFun.range.topologicalClosure = ⊤ :=
      (Submodule.dense_iff_topologicalClosure_eq_top).mp
        (by rw [range_dirichletDerivative_adjoint hab]; exact dense_univ)
    simpa only [hR, Submodule.starProjection_top, ContinuousLinearMap.id_apply] using h

/-- The adjoint domain is proper. A jump at the midpoint has a square-integrable
representative and cannot have a continuous Sobolev representative. -/
theorem dirichletDerivative_adjoint_domain_ne_top (hab : a < b) :
    (dirichletDerivative a b).adjoint.domain ≠ ⊤ := by
  let m := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  let f := (Iio m).indicator (fun _ : ℝ => (1 : ℝ))
  have hf : MemLp f 2 (volume.restrict (Ioo a b)) := by
    refine MemLp.of_bound (measurable_const.indicator measurableSet_Iio).aestronglyMeasurable 1 ?_
    exact Eventually.of_forall fun t => by by_cases ht : t ∈ Iio m <;> simp [f, ht]
  let x : IntervalL2 a b := hf.toLp f
  intro hTop
  have hx : x ∈ (dirichletDerivative a b).adjoint.domain := hTop ▸ Submodule.mem_top
  obtain ⟨u, hu, _⟩ := (mem_dirichletDerivative_adjoint_graph_iff hab).mp
    ((dirichletDerivative a b).adjoint.mem_graph ⟨x, hx⟩)
  have he : SobolevInterval.rep u =ᵐ[volume.restrict (Ioo a b)] f := by
    have hrep := (SobolevInterval.fn_ae_eq_rep u).symm
    change SobolevInterval.rep u =ᵐ[volume.restrict (Ioo a b)] ⇑(SobolevInterval.deriv u 0) at hrep
    rw [hu] at hrep
    exact hrep.trans (MemLp.coeFn_toLp hf)
  have hc := SobolevInterval.continuousOn_rep hab.le u
  have he₁ : SobolevInterval.rep u =ᵐ[volume.restrict (Ioo a m)] fun _ => 1 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hmb.le) he,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [ht]
    exact indicator_of_mem (mem_Iio.mpr htI.2) _
  have he₀ : SobolevInterval.rep u =ᵐ[volume.restrict (Ioo m b)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left ham.le) he,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [ht]
    exact indicator_of_notMem (show t ∉ Iio m from not_lt_of_ge htI.1.le) _
  have h₁ := Measure.eqOn_open_of_ae_eq he₁ isOpen_Ioo
    (hc.mono fun _ ht => ⟨ht.1.le, ht.2.le.trans hmb.le⟩) continuousOn_const
  have h₀ := Measure.eqOn_open_of_ae_eq he₀ isOpen_Ioo
    (hc.mono fun _ ht => ⟨ham.le.trans ht.1.le, ht.2.le⟩) continuousOn_const
  have hleft := h₁.of_subset_closure (t := Icc a m) (hc.mono (Icc_subset_Icc_right hmb.le))
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo ham.ne])
  have hright := h₀.of_subset_closure (t := Icc m b) (hc.mono (Icc_subset_Icc_left ham.le))
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hmb.ne])
  exact one_ne_zero ((hleft (right_mem_Icc.2 ham.le)).symm.trans (hright (left_mem_Icc.2 hmb.le)))

/-- **Exercise 26(b)** of [benIsrael2003generalized], Chapter 9.
The first product has a strictly smaller domain than the maximal inverse. -/
theorem exercise_9_26_leftProduct_ne_maximalInverse (hab : a < b) :
    let L := dirichletDerivative a b
    partialComp (maximalTsengInverse (partialComp L.adjoint L)) L.adjoint ≠
      maximalTsengInverse L := by
  let L := dirichletDerivative a b
  let S := maximalTsengInverse L
  have hS : S.domain = ⊤ :=
    maximalTsengInverse_domain_eq_top_of_normallySolvable
      (isNormallySolvable_dirichletDerivative hab)
  change partialComp (maximalTsengInverse (partialComp L.adjoint L)) L.adjoint ≠ S
  rw [(exercise_9_26_products hab).1]
  intro h
  have he := congrArg LinearPMap.domain h
  rw [LinearPMap.domRestrict_domain, hS, inf_top_eq] at he
  exact dirichletDerivative_adjoint_domain_ne_top hab he

/-- The continuous Green function for the interval negative second derivative
with both endpoint values set to zero. -/
def intervalDirichletGreenFunction (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1 - a) / (b - a) * (b - p.2) - max 0 (p.1 - p.2)

/-- On the unit interval the kernel has the two branches printed in **Exercise 38**. -/
theorem intervalDirichletGreenFunction_unit (s t : ℝ) :
    intervalDirichletGreenFunction 0 1 (s, t) = if s ≤ t then s * (1 - t) else t * (1 - s) := by
  by_cases h : s ≤ t
  · simp [intervalDirichletGreenFunction, h]
  · simp [intervalDirichletGreenFunction, max_eq_right (sub_nonneg.mpr (le_of_not_ge h)), h]
    ring

private theorem memLp_intervalDirichletGreenFunction (a b : ℝ) :
    MemLp (intervalDirichletGreenFunction a b) 2
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo a b))) := by
  have hc : Continuous (intervalDirichletGreenFunction a b) := by
    unfold intervalDirichletGreenFunction
    fun_prop
  let K := Icc a b ×ˢ Icc a b
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact K).exists_bound_of_continuousOn
    hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable C ?_
  have hm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : ∀ᵐ t ∂volume.restrict (Ioo a b), t ∈ Icc a b :=
    (ae_restrict_mem measurableSet_Ioo).mono fun _ h => Ioo_subset_Icc_self h
  have hK : ∀ᵐ p ∂(volume.restrict (Ioo a b)).prod (volume.restrict (Ioo a b)), p ∈ K := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem hm).mpr
    filter_upwards [hae] with x hx
    exact hae.mono fun _ hy => ⟨hx, hy⟩
  exact hK.mono hC

/-- The integral operator of the Dirichlet second-derivative Green function. -/
def intervalDirichletGreenOperator (a b : ℝ) : IntervalL2 a b →L[ℝ] IntervalL2 a b :=
  IntegralOperator.l2KernelCLM (memLp_intervalDirichletGreenFunction a b)

/-- The integral operator is given by the Green function almost everywhere. -/
theorem intervalDirichletGreenOperator_apply_ae (y : IntervalL2 a b) :
    (intervalDirichletGreenOperator a b y : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      fun s => ∫ t in Ioo a b, intervalDirichletGreenFunction a b (s, t) * y t :=
  IntegralOperator.l2KernelCLM_apply_ae _ _

private theorem weightedDerivative_integral (hab : a < b) (v : SobolevInterval 1 a b) {s : ℝ}
    (hs : s ∈ Icc a b) :
    (∫ t in a..s, SobolevInterval.deriv v 1 t * (s - t)) =
      (∫ t in a..s, SobolevInterval.rep v t) - (s - a) * SobolevInterval.rep v a := by
  have hψ : ContDiff ℝ 1 (fun t : ℝ => s - t) := by fun_prop
  have hc : closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) = Icc a b :=
    SobolevIntervalLp.closure_coe_Ioo hab
  have h :=
    SobolevIntervalLp.integral_deriv_mul_eq_sub_integral_mul_deriv_of_absolutelyContinuousOnInterval
      (SobolevIntervalLp.ordConnected_coe_Ioo a b) v (hc.symm ▸ hs)
      (hc.symm ▸ left_mem_Icc.2 hab.le) (ψ := fun t => s - t)
      hψ.contDiffOn.absolutelyContinuousOnInterval
  have hd : deriv (fun t : ℝ => s - t) = fun _ => -1 := by
    funext t
    exact (((hasDerivAt_id t).const_sub s).deriv)
  change (∫ t in a..s, SobolevInterval.deriv v 1 t * (s - t)) = _ at h
  rw [hd] at h
  simp only [sub_self, mul_zero, zero_sub, mul_neg, mul_one, intervalIntegral.integral_neg] at h
  rw [h]
  ring

private theorem ae_intervalIntegral_congr {f g : ℝ → ℝ} {s : ℝ} (hs : s ∈ Icc a b)
    (h : f =ᵐ[volume.restrict (Ioo a b)] g) : ∫ t in a..s, f t = ∫ t in a..s, g t := by
  simp only [intervalIntegral.integral_of_le hs.1, integral_Ioc_eq_integral_Ioo]
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hs.2) h)

private theorem intervalDirichletGreenFunction_integral (hab : a < b) (y : IntervalL2 a b) {s : ℝ}
    (hs : s ∈ Ioo a b) :
    ∫ t in Ioo a b, intervalDirichletGreenFunction a b (s, t) * y t =
      ((s - a) / (b - a)) * (∫ t in a..b, y t * (b - t)) - ∫ t in a..s, y t * (s - t) := by
  have hi (c : ℝ) : Integrable (fun t => y t * (c - t)) (volume.restrict (Ioo a b)) := by
    have hc : Continuous (fun t : ℝ => c - t) := by fun_prop
    have h := ((intervalL2_intervalIntegrable hab.le y).mul_continuousOn hc.continuousOn).1
    exact h.mono_set Ioo_subset_Ioc_self
  have he : (fun t => intervalDirichletGreenFunction a b (s, t) * y t) =
      fun t => ((s - a) / (b - a)) * (y t * (b - t)) -
        (Iic s).indicator (fun t => y t * (s - t)) t := by
    funext t
    by_cases ht : t ≤ s
    · simp only [intervalDirichletGreenFunction, max_eq_right (sub_nonneg.mpr ht),
        indicator_of_mem (mem_Iic.mpr ht)]
      ring
    · simp only [intervalDirichletGreenFunction, max_eq_left (sub_nonpos.mpr (le_of_not_ge ht)),
        indicator_of_notMem (show t ∉ Iic s from ht), sub_zero]
      ring
  rw [he, integral_sub ((hi b).const_mul _) ((hi s).indicator measurableSet_Iic),
    integral_const_mul,
    integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hs.1.le]
  have hset : Iic s ∩ Ioo a b = Ioc a s := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans_lt hs.2⟩⟩
  simp only [hset, integral_Ioc_eq_integral_Ioo]

/-- Solving the Dirichlet second-derivative equation and then applying the
integral kernel returns the original domain element. -/
theorem intervalDirichletGreenOperator_leftInverse (hab : a < b)
    (x : (partialComp (dirichletDerivative a b).adjoint (dirichletDerivative a b)).domain) :
    intervalDirichletGreenOperator a b (partialComp (dirichletDerivative a b).adjoint
      (dirichletDerivative a b) x) =
      (x : IntervalL2 a b) := by
  let L := dirichletDerivative a b
  let A := partialComp L.adjoint L
  let y := A x
  obtain ⟨w, hw, hw₀, hw₁⟩ := (mem_dirichletSecondDerivative_graph_iff hab).mp (A.mem_graph x)
  let u := SobolevInterval.inclusionCLM 1 a b w
  let v := SobolevInterval.derivCLM 1 a b w
  have hzero : SobolevInterval.rep u a = 0 ∧ SobolevInterval.rep u b = 0 :=
    ⟨SobolevIntervalZero.rep_left_eq_zero hab hw, SobolevIntervalZero.rep_right_eq_zero hab hw⟩
  have hy : -SobolevInterval.deriv v 1 = y := hw₁
  have hv : ⇑(SobolevInterval.deriv u 1) =ᵐ[volume.restrict (Ioo a b)] SobolevInterval.rep v :=
    SobolevInterval.fn_ae_eq_rep v
  have hUy (s : ℝ) (hs : s ∈ Icc a b) : SobolevInterval.rep u s =
      (s - a) * SobolevInterval.rep v a - ∫ t in a..s, y t * (s - t) := by
    have h := SobolevInterval.toContinuousMap_sub_eq_integral hab u
      ⟨a, left_mem_Icc.2 hab.le⟩ ⟨s, hs⟩
    change SobolevInterval.rep u s - SobolevInterval.rep u a = _ at h
    rw [hzero.1, sub_zero, ae_intervalIntegral_congr hs hv] at h
    have hneg : (∫ t in a..s, y t * (s - t)) =
        -(∫ t in a..s, SobolevInterval.deriv v 1 t * (s - t)) := by
      rw [← intervalIntegral.integral_neg]
      apply ae_intervalIntegral_congr hs
      rw [← hy]
      filter_upwards [Lp.coeFn_neg (SobolevInterval.deriv v 1)] with t ht
      change (-SobolevInterval.deriv v 1 : IntervalL2 a b) t * (s - t) =
        -(SobolevInterval.deriv v 1 t * (s - t))
      rw [ht, Pi.neg_apply, neg_mul]
    rw [hneg, weightedDerivative_integral hab v hs]
    linarith
  have hca : SobolevInterval.rep v a = (∫ t in a..b, y t * (b - t)) / (b - a) := by
    have h := hUy b (right_mem_Icc.2 hab.le)
    rw [hzero.2] at h
    apply (eq_div_iff (sub_pos.mpr hab).ne').mpr
    linarith [mul_comm (b - a) (SobolevInterval.rep v a)]
  apply Lp.ext
  filter_upwards [intervalDirichletGreenOperator_apply_ae y, SobolevInterval.fn_ae_eq_rep u,
    ae_restrict_mem measurableSet_Ioo] with s hs hx hsI
  change (intervalDirichletGreenOperator a b y : ℝ → ℝ) s = (x.val : IntervalL2 a b) s
  rw [hs, intervalDirichletGreenFunction_integral hab y hsI, ← hw₀]
  change _ = SobolevInterval.deriv u 0 s
  change SobolevInterval.deriv u 0 s = _ at hx
  rw [hx, hUy s (Ioo_subset_Icc_self hsI), hca]
  ring

/-- The Green operator's range is exactly the Dirichlet second derivative's domain. -/
theorem intervalDirichletGreenOperator_range (hab : a < b) :
    (intervalDirichletGreenOperator a b).range =
      (partialComp (dirichletDerivative a b).adjoint (dirichletDerivative a b)).domain := by
  let A := partialComp (dirichletDerivative a b).adjoint (dirichletDerivative a b)
  have hR : A.toFun.range = ⊤ := (ranges_intervalSecondDerivatives hab).1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, hz⟩ : y ∈ A.toFun.range := hR ▸ Submodule.mem_top
    change A z = y at hz
    rw [← hz]
    change intervalDirichletGreenOperator a b
      (partialComp (dirichletDerivative a b).adjoint (dirichletDerivative a b) z) ∈ _
    rw [intervalDirichletGreenOperator_leftInverse hab z]
    exact z.2
  · intro hx
    exact ⟨A ⟨x, hx⟩, intervalDirichletGreenOperator_leftInverse hab ⟨x, hx⟩⟩

/-- The range of the continuous Green integral operator is dense and proper,
so it is nonclosed. -/
theorem intervalDirichletGreenOperator_range_not_closed (hab : a < b) :
    ¬IsClosed ((intervalDirichletGreenOperator a b).range : Set (IntervalL2 a b)) := by
  rw [intervalDirichletGreenOperator_range hab]
  let L := dirichletDerivative a b
  let A := partialComp L.adjoint L
  have hd : Dense (A.domain : Set (IntervalL2 a b)) :=
    (gramOperators_nonnegative L (isClosed_dirichletDerivative a b)
      (dense_dirichletDerivative_domain hab)).2.1.dense_domain
  have hle : A.domain ≤ L.adjoint.domain := by
    intro x hx
    obtain ⟨w, _, hw, _⟩ := (mem_dirichletSecondDerivative_graph_iff hab).mp (A.mem_graph ⟨x, hx⟩)
    exact LinearPMap.mem_domain_of_mem_graph ((mem_dirichletDerivative_adjoint_graph_iff hab).mpr
      ⟨SobolevInterval.inclusionCLM 1 a b w, hw, rfl⟩)
  intro hc
  have he := (Submodule.dense_iff_topologicalClosure_eq_top.mp hd)
  rw [hc.submodule_topologicalClosure_eq] at he
  exact dirichletDerivative_adjoint_domain_ne_top hab (eq_top_iff.mpr (he ▸ hle))

end IntervalDerivative

section GramProjectionKernels

open scoped ComplexOrder

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [Fintype ι] [DecidableEq ι]

/-- The coefficients of orthogonal projection in an arbitrary finite basis,
obtained by solving the Gram system. -/
def gramProjectionCoefficients (v : ι → H) (y : H) : ι → 𝕜 :=
  (Matrix.gram 𝕜 v)⁻¹.mulVec (fun i => inner 𝕜 (v i) y)

/-- **Equations (65)–(66)** of [benIsrael2003generalized], Chapter 9.
A finite-span projection is computed with the inverse of the Gram matrix. -/
theorem starProjection_span_eq_gram_sum (v : ι → H) (hv : LinearIndependent 𝕜 v) (y : H) :
    letI : FiniteDimensional 𝕜 (Submodule.span 𝕜 (range v)) :=
      FiniteDimensional.span_of_finite 𝕜 (finite_range v)
    (Submodule.span 𝕜 (range v)).starProjection y =
      ∑ i, gramProjectionCoefficients (𝕜 := 𝕜) v y i • v i := by
  let : FiniteDimensional 𝕜 (Submodule.span 𝕜 (range v)) :=
    FiniteDimensional.span_of_finite 𝕜 (finite_range v)
  let U := Submodule.span 𝕜 (range v)
  let c := gramProjectionCoefficients (𝕜 := 𝕜) v y
  let q := ∑ i, c i • v i
  have hG := (Matrix.posDef_gram_of_linearIndependent hv).isUnit
  have hz : (Matrix.gram 𝕜 v).mulVec c = fun i => inner 𝕜 (v i) y := by
    unfold c gramProjectionCoefficients
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG),
      Matrix.one_mulVec]
  have hq : q ∈ U := Submodule.sum_mem U fun i _ => U.smul_mem _ (Submodule.subset_span
    (mem_range_self i))
  apply Submodule.eq_starProjection_of_mem_orthogonal hq
  rw [Submodule.mem_orthogonal]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz' =>
    obtain ⟨i, rfl⟩ := hz'
    have hzi := congrFun hz i
    change (∑ j, inner 𝕜 (v i) (v j) * c j) = inner 𝕜 (v i) y at hzi
    change inner 𝕜 (v i) (y - q) = 0
    rw [inner_sub_right, sub_eq_zero]
    exact hzi.symm.trans (by simp [q, inner_sum, inner_smul_right, mul_comm])
  | zero => simp
  | add x₁ x₂ _ _ h₁ h₂ => simp [inner_add_left, h₁, h₂]
  | smul r z _ hz => simp [inner_smul_left, hz]

variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedSpace ℝ V]

/-- The finite-rank kernel $X(s)(X^*X)^{-1} X(t)^*$ for a family of `L²` vectors,
where $X^*X$ denotes the integrated Gram matrix. -/
def gramProjectionGreenKernel (v : ι → Lp V 2 μ) : GreenKernel 𝕜 X V V :=
  fun s t => ∑ i, (∑ j, ((Matrix.gram 𝕜 v)⁻¹ i j) • innerSL 𝕜 (v j t)).smulRight (v i s)

/-- **Equations (65)–(66)** of [benIsrael2003generalized], Chapter 9.
The inverse Gram matrix gives the integral kernel of the projection onto
any finite-dimensional space with the given basis. -/
theorem represents_gramProjectionGreenKernel (v : ι → Lp V 2 μ)
    (hv : LinearIndependent 𝕜 v) (y : Lp V 2 μ) :
    letI : FiniteDimensional 𝕜 (Submodule.span 𝕜 (range v)) :=
      FiniteDimensional.span_of_finite 𝕜 (finite_range v)
    RepresentsGreenAction (gramProjectionGreenKernel (𝕜 := 𝕜) v) y
      ((Submodule.span 𝕜 (range v)).starProjection y) := by
  let : FiniteDimensional 𝕜 (Submodule.span 𝕜 (range v)) :=
    FiniteDimensional.span_of_finite 𝕜 (finite_range v)
  let a := (Matrix.gram 𝕜 v)⁻¹
  let c := gramProjectionCoefficients (𝕜 := 𝕜) v y
  let K := gramProjectionGreenKernel (𝕜 := 𝕜) v
  have hK (s t : X) : K s t (y t) = ∑ i, (∑ j, a i j * inner 𝕜 (v j t) (y t)) • v i s := by
    simp [K, gramProjectionGreenKernel, a, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      smul_eq_mul]
  have hi (i j : ι) : Integrable (fun t => a i j * inner 𝕜 (v j t) (y t)) μ :=
    (L2.integrable_inner (𝕜 := 𝕜) (v j) y).const_mul (a i j)
  have hsum (i : ι) : Integrable (fun t => ∑ j, a i j * inner 𝕜 (v j t) (y t)) μ :=
    integrable_finsetSum _ fun j _ => hi i j
  have hrow (s : X) : Integrable (fun t => K s t (y t)) μ := by
    simp_rw [hK]
    exact integrable_finsetSum _ fun i _ => (hsum i).smul_const (v i s)
  refine ⟨Eventually.of_forall hrow, ?_⟩
  rw [starProjection_span_eq_gram_sum v hv y]
  have hpoint : ∀ᵐ s ∂μ, ∀ i, ((c i • v i : Lp V 2 μ) : X → V) s = c i • v i s :=
    ae_all_iff.mpr fun i => Lp.coeFn_smul (c i) (v i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • v i), hpoint] with s hs hp
  change (∑ i, c i • v i : Lp V 2 μ) s = ∫ t, K s t (y t) ∂μ
  rw [hs]
  simp only [hK]
  rw [integral_finsetSum _ (fun i _ => (hsum i).smul_const (v i s))]
  apply Finset.sum_congr rfl
  intro i _
  rw [hp i, integral_smul_const, integral_finsetSum _ (fun j _ => hi i j)]
  congr 1
  simp only [integral_const_mul, ← L2.inner_def]
  rfl

end GramProjectionKernels

section GreenKernelProducts

variable {𝕜 X U V W : Type*} [RCLike 𝕜] [MeasurableSpace X]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W]
  [SMulCommClass ℝ 𝕜 W] {μ : Measure X}

/-- The Green kernel of a composite is obtained by integrating the composed coefficients
over the intermediate variable. -/
def greenKernelProduct (μ : Measure X) (P : GreenKernel 𝕜 X V W)
    (G : GreenKernel 𝕜 X U V) : GreenKernel 𝕜 X U W :=
  fun s t => ∫ u, (P s u).comp (G u t) ∂μ

/-- For a specified input, the composition has integrable coefficient rows and an
integrable Fubini integrand for almost every output point. -/
structure GreenKernelProductIntegrable (μ : Measure X) (P : GreenKernel 𝕜 X V W)
    (G : GreenKernel 𝕜 X U V) (y : Lp U 2 μ) : Prop where
  coefficient : ∀ᵐ s ∂μ, ∀ᵐ t ∂μ, Integrable (fun u => (P s u).comp (G u t)) μ
  integrand : ∀ᵐ s ∂μ, Integrable (fun p : X × X => P s p.1 (G p.1 p.2 (y p.2))) (μ.prod μ)

variable [CompleteSpace V] [CompleteSpace W] [SFinite μ]

omit [SMulCommClass ℝ 𝕜 W] in
/-- Under the coefficient and Fubini integrability conditions, the convolution represents
the composition of the two Green operators on the given input. -/
theorem represents_greenKernelProduct {P : GreenKernel 𝕜 X V W}
    {G : GreenKernel 𝕜 X U V} {y : Lp U 2 μ} {v : Lp V 2 μ} {w : Lp W 2 μ}
    (hP : RepresentsGreenAction P v w) (hG : RepresentsGreenAction G y v)
    (hPG : GreenKernelProductIntegrable μ P G y) :
    RepresentsGreenAction (greenKernelProduct μ P G) y w := by
  have hAt : ∀ᵐ s ∂μ, ∀ᵐ t ∂μ,
      greenKernelProduct μ P G s t (y t) = ∫ u, P s u (G u t (y t)) ∂μ := by
    filter_upwards [hPG.coefficient] with s hs
    filter_upwards [hs] with t ht
    exact ContinuousLinearMap.integral_apply ht _
  constructor
  · filter_upwards [hAt, hPG.integrand] with s hs hi
    exact hi.integral_prod_right.congr (Filter.EventuallyEq.symm hs)
  · filter_upwards [hP.ae_eq_integral, hAt, hPG.integrand] with s hw hrow hs
    rw [hw]
    change (∫ u, P s u (v u) ∂μ) = ∫ t, greenKernelProduct μ P G s t (y t) ∂μ
    calc
      ∫ u, P s u (v u) ∂μ = ∫ u, ∫ t, P s u (G u t (y t)) ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hG.ae_eq_integral, hG.integrable_row] with u hu hI
        rw [hu]
        exact ((P s u).integral_comp_comm hI).symm
      _ = ∫ t, ∫ u, P s u (G u t (y t)) ∂μ ∂μ := integral_integral_swap hs
      _ = ∫ t, greenKernelProduct μ P G s t (y t) ∂μ :=
        integral_congr_ae (Filter.EventuallyEq.symm hrow)

end GreenKernelProducts

section GreenKernelCombination

variable {𝕜 X V W : Type*} [RCLike 𝕜] [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W] {μ : Measure X}

private theorem RepresentsGreenAction.addKernel {F G : GreenKernel 𝕜 X V W} {y : Lp V 2 μ}
    {x z : Lp W 2 μ} (hF : RepresentsGreenAction F y x) (hG : RepresentsGreenAction G y z) :
    RepresentsGreenAction (fun s t => F s t + G s t) y (x + z) := by
  constructor
  · filter_upwards [hF.integrable_row, hG.integrable_row] with s hFs hGs
    exact hFs.add hGs
  · filter_upwards [hF.ae_eq_integral, hG.ae_eq_integral, hF.integrable_row,
      hG.integrable_row, Lp.coeFn_add x z] with s hx hz hiF hiG hs
    change _ = ∫ t, F s t (y t) + G s t (y t) ∂μ
    rw [hs, Pi.add_apply, hx, hz, integral_add hiF hiG]
    rfl

private theorem RepresentsGreenAction.subKernel {F G : GreenKernel 𝕜 X V W} {y : Lp V 2 μ}
    {x z : Lp W 2 μ} (hF : RepresentsGreenAction F y x) (hG : RepresentsGreenAction G y z) :
    RepresentsGreenAction (fun s t => F s t - G s t) y (x - z) := by
  constructor
  · filter_upwards [hF.integrable_row, hG.integrable_row] with s hFs hGs
    exact hFs.sub hGs
  · filter_upwards [hF.ae_eq_integral, hG.ae_eq_integral, hF.integrable_row,
      hG.integrable_row, Lp.coeFn_sub x z] with s hx hz hiF hiG hs
    change _ = ∫ t, F s t (y t) - G s t (y t) ∂μ
    rw [hs, Pi.sub_apply, hx, hz, integral_sub hiF hiG]
    rfl

end GreenKernelCombination

section LoudExpandedGreen

variable {𝕜 X V W : Type*} [RCLike 𝕜] [MeasurableSpace X]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] {μ : Measure X} [SFinite μ]

/-- The double integral in the expansion of Loud's projected Green kernel. -/
def greenKernelTripleProduct (μ : Measure X) (P : GreenKernel 𝕜 X W W)
    (G : GreenKernel 𝕜 X V W) (Q : GreenKernel 𝕜 X V V) : GreenKernel 𝕜 X V W :=
  fun s t => ∫ v, ∫ u, (P s u).comp ((G u v).comp (Q v t)) ∂μ ∂μ

omit [CompleteSpace V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [SMulCommClass ℝ 𝕜 W] [SFinite μ] in
private theorem greenKernelProduct_product_ae (P : GreenKernel 𝕜 X W W)
    (G : GreenKernel 𝕜 X V W) (Q : GreenKernel 𝕜 X V V)
    (h : ∀ᵐ s ∂μ, ∀ᵐ v ∂μ, Integrable (fun u => (P s u).comp (G u v)) μ) :
    ∀ᵐ s ∂μ, ∀ t, greenKernelProduct μ (greenKernelProduct μ P G) Q s t =
      greenKernelTripleProduct μ P G Q s t := by
  filter_upwards [h] with s hs
  intro t
  apply integral_congr_ae
  filter_upwards [hs] with v hv
  let J : (V →L[𝕜] W) →L[𝕜] V →L[𝕜] W :=
    (ContinuousLinearMap.compL 𝕜 V V W).flip (Q v t)
  change J (∫ u, (P s u).comp (G u v) ∂μ) = ∫ u, J ((P s u).comp (G u v)) ∂μ
  exact (J.integral_comp_comm hv).symm

omit [SMulCommClass ℝ 𝕜 V] in
/-- **Exercise 35**, Equation (67), of [benIsrael2003generalized].
The four kernels in the expanded formula represent the maximal inverse on its domain.
The two projection kernels may be taken to be the Gram kernels of (65)–(66). -/
theorem exercise_9_35_kernel_expansion {L : Lp W 2 μ →ₗ.[𝕜] Lp V 2 μ}
    (hL : IsNormallySolvable L) (hD : Dense (L.domain : Set (Lp W 2 μ)))
    (G : GreenKernel 𝕜 X V W) (hG : IsGeneralizedGreenKernel L G)
    (Gop : Lp V 2 μ →ₗ[𝕜] Lp W 2 μ) (hGop : ∀ x, RepresentsGreenAction G x (Gop x))
    (P : GreenKernel 𝕜 X W W) (Q : GreenKernel 𝕜 X V V) :
    letI := hL.1.isClosed_ker.completeSpace_coe
    letI := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
    (∀ x, RepresentsGreenAction P x (L.ker.starProjection x)) →
    (∀ x, RepresentsGreenAction Q x (L.adjoint.ker.starProjection x)) →
    ∀ y : (maximalTsengInverse L).domain,
      GreenKernelProductIntegrable μ P G y.val →
      GreenKernelProductIntegrable μ G Q y.val →
      GreenKernelProductIntegrable μ P G (L.adjoint.ker.starProjection y.val) →
      GreenKernelProductIntegrable μ (greenKernelProduct μ P G) Q y.val →
      RepresentsGreenAction (fun s t =>
        G s t - greenKernelProduct μ P G s t - greenKernelProduct μ G Q s t +
          greenKernelTripleProduct μ P G Q s t) y.val (maximalTsengInverse L y) := by
  let := hL.1.isClosed_ker.completeSpace_coe
  let := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
  let := hL.2.completeSpace_coe
  intro hP hQ y hPG hGQ hPGQ hAll
  let p := L.ker.starProjection
  let q := L.adjoint.ker.starProjection
  have h1 := hGop y.val
  have h2 := represents_greenKernelProduct (hP (Gop y.val)) h1 hPG
  have h3 := represents_greenKernelProduct (hGop (q y.val)) (hQ y.val) hGQ
  have h4 := represents_greenKernelProduct (hP (Gop (q y.val))) (hGop (q y.val)) hPGQ
  have h5 := represents_greenKernelProduct h4 (hQ y.val) hAll
  have h6 := ((h1.subKernel h2).subKernel h3).addKernel h5
  have hprod := greenKernelProduct_product_ae P G Q hPG.coefficient
  let r := L.toFun.range.orthogonalProjectionOnto y.val
  have hr : r.val = y.val - q y.val := (exercise_9_35_projection_complements hL hD).2 y.val
  have hGproj : hG.toLinearMap r = Gop r.val :=
    (hG.represents_toLinearMap r).output_unique (hGop r.val)
  have hp (x : Lp W 2 μ) : L.kerᗮ.starProjection x = x - p x := by
    apply Submodule.eq_starProjection_of_mem_orthogonal (L.ker.sub_starProjection_mem_orthogonal x)
    rw [sub_sub_cancel, Submodule.orthogonal_orthogonal]
    exact L.ker.starProjection_apply_mem x
  have he : maximalTsengInverse L y =
      Gop y.val - p (Gop y.val) - Gop (q y.val) + p (Gop (q y.val)) := by
    rw [maximalInverse_eq_project_greenKernel hL hG, hGproj, hp, hr, map_sub, map_sub]
    abel
  have hrow : ∀ᵐ s ∂μ, (fun t =>
      (G s t - greenKernelProduct μ P G s t - greenKernelProduct μ G Q s t +
        greenKernelProduct μ (greenKernelProduct μ P G) Q s t) (y.val t)) =ᵐ[μ] fun t =>
      (G s t - greenKernelProduct μ P G s t - greenKernelProduct μ G Q s t +
        greenKernelTripleProduct μ P G Q s t) (y.val t) := by
    filter_upwards [hprod] with s hs
    exact Eventually.of_forall fun t => congrArg
      (fun K : V →L[𝕜] W => (G s t - greenKernelProduct μ P G s t -
        greenKernelProduct μ G Q s t + K) (y.val t)) (hs t)
  rw [he]
  constructor
  · filter_upwards [h6.integrable_row, hrow] with s hs ht
    exact hs.congr ht
  · filter_upwards [h6.ae_eq_integral, hrow] with s hs ht
    exact hs.trans (integral_congr_ae ht)

end LoudExpandedGreen

end BenIsraelGreville.Chapter09
