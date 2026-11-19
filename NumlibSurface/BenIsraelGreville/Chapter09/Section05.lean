/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Numlib.Analysis.Sobolev.Interval.Vector
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Numlib.Analysis.Fourier.SineBasis
import Numlib.Analysis.InnerProductSpace.OrthonormalSeries
import Numlib.Analysis.ODE.Cauchy
import Numlib.Analysis.PDE.DirichletLaplacian
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
* Exercise 27 uses the maximal weak negative divergence as the adjoint.
  The differentiated Green series is integrated through its finite sums
  and converges in the square-integrable norm.
* The sign Green kernels in Exercise 30 use the inverse leading coefficient
  on the forcing side and evaluate the correction in endpoint order (a, b).
* Exercise 32 uses a common essentially bounded kernel class. The normalized
  kernel in Exercise 33 is unique almost everywhere, and its operator range
  is the intersection of the differential domain with the orthogonal
  complement of the test columns.
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

section GreenOperatorStructure

open Set InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]

/-- The bounded operator giving a normalized Green solution by obliquely projecting
the data and then the solution. -/
def normalizedGreenOperator (L : E →ₗ.[𝕜] F) (G : F →L[𝕜] E)
    [L.adjoint.ker.HasOrthogonalProjection]
    (Θ : E →L[𝕜] L.ker) (Ψ : L.adjoint.ker →L[𝕜] F) : F →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 E - L.ker.subtypeL.comp Θ).comp
    (G.comp (ContinuousLinearMap.id 𝕜 F - Ψ.comp L.adjoint.ker.orthogonalProjectionOnto))

omit [CompleteSpace E] [CompleteSpace F] in
private theorem green_mem_graph_ker {L : E →ₗ.[𝕜] F} {u : E}
    (hu : (u, 0) ∈ L.graph) : u ∈ L.ker := by
  obtain ⟨x, rfl, hx⟩ := L.mem_graph_iff.mp hu
  exact LinearPMap.mem_ker_iff.mpr ⟨x, rfl, hx⟩

omit [CompleteSpace E] [CompleteSpace F] in
private theorem green_ker_mem_graph {L : E →ₗ.[𝕜] F} {u : E}
    (hu : u ∈ L.ker) : (u, 0) ∈ L.graph := by
  obtain ⟨x, rfl, hx⟩ := LinearPMap.mem_ker_iff.mp hu
  exact L.mem_graph_iff.mpr ⟨x, rfl, hx⟩

/-- **Exercise 33** of [benIsrael2003generalized], Chapter 9, at the operator level.
Biorthogonality makes the two oblique projections well defined. They specify a
unique Green operator whose kernel is the prescribed complementary space and whose
range is the intersection of the differential domain with the normalized subspace. -/
theorem normalizedGreenOperator_spec (L : E →ₗ.[𝕜] F)
    (hL : IsNormallySolvable L) (hD : Dense (L.domain : Set E))
    (G : F →L[𝕜] E) (hG : ∀ y ∈ L.toFun.range, (G y, y) ∈ L.graph) :
    letI := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
    ∀ (Θ : E →L[𝕜] L.ker) (Ψ : L.adjoint.ker →L[𝕜] F),
      (∀ x : L.ker, Θ (x : E) = x) →
      (∀ u : L.adjoint.ker, L.adjoint.ker.orthogonalProjectionOnto (Ψ u) = u) →
      let C := normalizedGreenOperator L G Θ Ψ
      (∀ y ∈ L.toFun.range, (C y, y) ∈ L.graph) ∧
      C.ker = Ψ.range ∧ C.range = L.domain ⊓ Θ.ker ∧
      ∀ D : F →L[𝕜] E, (∀ y ∈ L.toFun.range, (D y, y) ∈ L.graph) →
        (∀ y, Θ (D y) = 0) → (∀ u, D (Ψ u) = 0) → D = C := by
  let := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
  let := hL.2.completeSpace_coe
  intro Θ Ψ hΘ hΨ C
  let P := L.adjoint.ker.orthogonalProjectionOnto
  let y₀ (y : F) := y - Ψ (P y)
  have hR : P.ker = L.toFun.range := by
    change L.adjoint.ker.orthogonalProjectionOnto.ker = _
    rw [Submodule.ker_orthogonalProjectionOnto, ker_adjoint_eq_orthogonal_range L hD,
      Submodule.orthogonal_orthogonal]
  have hy₀ (y : F) : y₀ y ∈ L.toFun.range := by
    rw [← hR, LinearMap.mem_ker]
    change P (y - Ψ (P y)) = 0
    rw [map_sub, hΨ, sub_self]
  have hfix (y : F) (hy : y ∈ L.toFun.range) : y₀ y = y := by
    have hp : P y = 0 := (LinearMap.mem_ker.mp (hR.symm ▸ hy))
    simp [y₀, hp]
  have hC (y : F) : C y = G (y₀ y) - (Θ (G (y₀ y)) : E) := rfl
  have hC_graph (y : F) : (C y, y₀ y) ∈ L.graph := by
    rw [hC]
    convert L.graph.sub_mem (hG _ (hy₀ y)) (green_ker_mem_graph (Θ (G (y₀ y))).property)
      using 1
    simp
  have hC_θ (y : F) : Θ (C y) = 0 := by
    rw [hC, map_sub, hΘ, sub_self]
  have hC_inverse (y : F) (hy : y ∈ L.toFun.range) : (C y, y) ∈ L.graph := by
    have h := hC_graph y
    rwa [hfix y hy] at h
  have hC_ψ (u : L.adjoint.ker) : C (Ψ u) = 0 := by
    have h : y₀ (Ψ u) = 0 := by simp [y₀, hΨ, P]
    rw [hC, h, map_zero, map_zero, Submodule.coe_zero, sub_zero]
  refine ⟨hC_inverse, ?_, ?_, ?_⟩
  · ext y
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    change C y = 0 ↔ ∃ u : L.adjoint.ker, Ψ u = y
    constructor
    · intro he
      have h := L.graph_fst_eq_zero_snd (hC_graph y) he
      change y - Ψ (P y) = 0 at h
      exact ⟨P y, (sub_eq_zero.mp h).symm⟩
    · rintro ⟨u, rfl⟩
      exact hC_ψ u
  · ext x
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range]
    change (∃ y, C y = x) ↔ x ∈ L.domain ∧ Θ x = 0
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨L.mem_domain_of_mem_graph (hC_graph y), hC_θ y⟩
    · rintro ⟨hx, hΘx⟩
      let u : L.domain := ⟨x, hx⟩
      let y := L u
      have hy : y ∈ L.toFun.range := ⟨u, rfl⟩
      refine ⟨y, ?_⟩
      have hk : C y - x ∈ L.ker := by
        apply green_mem_graph_ker
        have he := L.graph.sub_mem (hC_inverse y hy) (L.mem_graph u)
        change (C y, y) - (x, y) ∈ L.graph at he
        simpa only [Prod.mk_sub_mk, sub_self] using he
      let v : L.ker := ⟨C y - x, hk⟩
      have hv : Θ (v : E) = 0 := by
        change Θ (C y - x) = 0
        rw [map_sub, hC_θ, hΘx, sub_zero]
      have : v = 0 := (hΘ v).symm.trans hv
      exact sub_eq_zero.mp (congrArg (fun k : L.ker => (k : E)) this)
  · intro D hDinv hDθ hDψ
    apply ContinuousLinearMap.ext
    intro y
    have hDy : D (y₀ y) = D y := by simp [y₀, map_sub, hDψ]
    have he : (D y, y₀ y) ∈ L.graph := hDy ▸ hDinv (y₀ y) (hy₀ y)
    have hk : D y - C y ∈ L.ker := by
      apply green_mem_graph_ker
      simpa only [Prod.mk_sub_mk, sub_self] using L.graph.sub_mem he (hC_graph y)
    let v : L.ker := ⟨D y - C y, hk⟩
    have hv : Θ (v : E) = 0 := by
      change Θ (D y - C y) = 0
      rw [map_sub, hDθ, hC_θ, sub_zero]
    have : v = 0 := (hΘ v).symm.trans hv
    exact sub_eq_zero.mp (congrArg (fun k : L.ker => (k : E)) this)

/-- The difference of two bounded Green operators is a sum of two finite-rank
maps. The first has outputs in the primal null space. The second vanishes on
the orthogonal complement of the adjoint null space. -/
theorem greenOperator_difference_iff (L : E →ₗ.[𝕜] F)
    (hL : IsNormallySolvable L) (hD : Dense (L.domain : Set E))
    (G T : F →L[𝕜] E) (hG : ∀ y ∈ L.toFun.range, (G y, y) ∈ L.graph)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι 𝕜 L.ker) (c : OrthonormalBasis κ 𝕜 L.adjoint.ker) :
    (∀ y ∈ L.toFun.range, (T y, y) ∈ L.graph) ↔
      ∃ (a : ι → F) (w : κ → E), T = G +
        (∑ i, rankOne 𝕜 (b i : E) (a i)) + ∑ j, rankOne 𝕜 (w j) (c j : F) := by
  let := hL.1.isClosed_ker.completeSpace_coe
  let := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
  let := hL.2.completeSpace_coe
  have hR : L.adjoint.kerᗮ = L.toFun.range := by
    rw [ker_adjoint_eq_orthogonal_range L hD, Submodule.orthogonal_orthogonal]
  constructor
  · intro hT
    let D := T - G
    let P := L.ker.starProjection
    let Q := L.adjoint.ker.starProjection
    let V := D - P.comp D
    have hV (y : F) : V (y - Q y) = 0 := by
      have hy : y - Q y ∈ L.toFun.range := hR ▸ L.adjoint.ker.sub_starProjection_mem_orthogonal y
      have hDker : D (y - Q y) ∈ L.ker := by
        apply green_mem_graph_ker
        have he := L.graph.sub_mem (hT _ hy) (hG _ hy)
        simpa only [D, sub_apply, Prod.mk_sub_mk, sub_self] using he
      change D (y - Q y) - P (D (y - Q y)) = 0
      rw [show P (D (y - Q y)) = D (y - Q y) from L.ker.starProjection_eq_self_iff.mpr hDker,
        sub_self]
    have hP : P.comp D = ∑ i, rankOne 𝕜 (b i : E) (D.adjoint (b i : E)) := by
      apply ContinuousLinearMap.ext
      intro y
      change L.ker.starProjection (D y) = _
      rw [b.starProjection_eq_sum_rankOne]
      simp only [sum_apply, rankOne_apply, D.adjoint_inner_left]
    have hQ : V = ∑ j, rankOne 𝕜 (V (c j : F)) (c j : F) := by
      apply ContinuousLinearMap.ext
      intro y
      have he := hV y
      rw [map_sub, sub_eq_zero] at he
      rw [he]
      change V (L.adjoint.ker.starProjection y) = _
      rw [c.starProjection_eq_sum_rankOne]
      simp only [sum_apply, rankOne_apply, map_sum, map_smul]
    refine ⟨fun i => D.adjoint (b i : E), fun j => V (c j : F), ?_⟩
    rw [← hP, ← hQ]
    dsimp only [V, D]
    abel
  · rintro ⟨a, w, rfl⟩ y hy
    have hU : (∑ i, rankOne 𝕜 (b i : E) (a i)) y ∈ L.ker := by
      simp only [sum_apply, rankOne_apply]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).property
    have hW : (∑ j, rankOne 𝕜 (w j) (c j : F)) y = 0 := by
      simp only [sum_apply, rankOne_apply]
      exact Finset.sum_eq_zero fun j _ => by
        rw [(Submodule.mem_orthogonal _ _).mp (hR.symm ▸ hy) _ (c j).property, zero_smul]
    rw [add_apply, hW, add_zero, add_apply]
    have he := L.graph.add_mem (hG y hy) (green_ker_mem_graph hU)
    simpa only [Prod.mk_add_mk, add_zero] using he


end GreenOperatorStructure

section GreenKernelFiniteRank

open Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal

section RealGreenKernels

variable {X V W : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ] [IsSeparable μ]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- A square-integrable vector-valued Green kernel with zero action on every input
vanishes almost everywhere. -/
theorem greenKernel_ae_zero_of_action_zero
    (D : GreenKernel ℝ X V W) (hD : MemLp (fun p : X × X => D p.1 p.2) 2 (μ.prod μ))
    (h0 : ∀ y : Lp V 2 μ, RepresentsGreenAction D y (0 : Lp W 2 μ)) :
    (fun p : X × X => D p.1 p.2) =ᵐ[μ.prod μ] 0 := by
  let b := stdOrthonormalBasis ℝ V
  let c := stdOrthonormalBasis ℝ W
  have hmatrix (i : Fin (Module.finrank ℝ V)) (j : Fin (Module.finrank ℝ W)) :
      (fun p : X × X => inner ℝ (c j) (D p.1 p.2 (b i))) =ᵐ[μ.prod μ] 0 := by
    let B : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight (b i)
    let v : W →L[ℝ] ℝ := innerSL ℝ (c j)
    let A : (V →L[ℝ] W) →L[ℝ] ℝ := v.comp (ContinuousLinearMap.apply ℝ W (b i))
    let k (p : X × X) := A (D p.1 p.2)
    have hk : MemLp k 2 (μ.prod μ) := A.comp_memLp' hD
    have hK : IntegralOperator.l2KernelCLM hk = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      change IntegralOperator.l2KernelCLM hk x = 0
      apply Lp.ext
      have hAct := h0 (B.compLp x)
      filter_upwards [Lp.coeFn_zero W 2 μ, Lp.coeFn_zero ℝ 2 μ,
        IntegralOperator.l2KernelCLM_apply_ae hk x, hAct.ae_eq_integral, hAct.integrable_row]
        with s hzW hzR hA hDx hI
      change (IntegralOperator.l2KernelCLM hk x) s = (0 : Lp ℝ 2 μ) s
      have hcoeff : (∫ t, k (s, t) * x t ∂μ) =
          ∫ t, v (D s t ((B.compLp x) t)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [B.coeFn_compLp x] with t ht
        rw [ht]
        change inner ℝ (c j) (D s t (b i)) * x t = inner ℝ (c j) (D s t (x t • b i))
        rw [map_smul, inner_smul_right, mul_comm]
      have hInt : (∫ t, D s t ((B.compLp x) t) ∂μ) = 0 := by
        have h := hDx.symm.trans hzW
        exact h
      calc
        _ = ∫ t, k (s, t) * x t ∂μ := hA
        _ = ∫ t, v (D s t ((B.compLp x) t)) ∂μ := hcoeff
        _ = (0 : Lp ℝ 2 μ) s := by
          rw [v.integral_comp_comm hI, hInt, map_zero]
          exact hzR.symm
    exact IntegralOperator.ae_eq_zero_of_l2KernelCLM_eq_zero hk hK
  filter_upwards [eventually_all.mpr fun i => eventually_all.mpr fun j => hmatrix i j] with p hp
  change D p.1 p.2 = 0
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro i
  change D p.1 p.2 (b i) = 0
  apply c.repr.injective
  ext j
  rw [map_zero]
  change c.repr (D p.1 p.2 (b i)) j = 0
  rw [c.repr_apply_apply]
  exact hp i j

/-- A separated Green kernel giving the outer product of two (L^2) vectors. -/
def rankOneGreenKernel (u : Lp W 2 μ) (v : Lp V 2 μ) : GreenKernel ℝ X V W :=
  fun s t => rankOne ℝ (u s) (v t)

omit [SFinite μ] [IsSeparable μ] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- The separated kernel is square-integrable on the product space. -/
theorem memLp_rankOneGreenKernel (u : Lp W 2 μ) (v : Lp V 2 μ) :
    MemLp (fun p : X × X => rankOneGreenKernel u v p.1 p.2) 2 (μ.prod μ) := by
  have h : AEStronglyMeasurable (fun p : X × X => rankOne ℝ (u p.1) (v p.2)) (μ.prod μ) :=
    (rankOne ℝ : W →L[ℝ] V →L[ℝ] V →L[ℝ] W).aestronglyMeasurable_comp₂
      (Lp.aestronglyMeasurable u).comp_fst (Lp.aestronglyMeasurable v).comp_snd
  apply (memLp_two_iff_integrable_sq_norm h).mpr
  simp only [norm_rankOne, mul_pow]
  exact (Lp.memLp u).norm.integrable_sq.mul_prod (Lp.memLp v).norm.integrable_sq

omit [SFinite μ] [IsSeparable μ] [FiniteDimensional ℝ V] in
/-- A rank-one Green kernel represents the corresponding Hilbert-space rank-one map. -/
theorem represents_rankOneGreenKernel (u : Lp W 2 μ) (v x : Lp V 2 μ) :
    RepresentsGreenAction (rankOneGreenKernel u v) x (rankOne ℝ u v x) := by
  have h : Integrable (fun t => inner ℝ (v t) (x t)) μ := L2.integrable_inner v x
  constructor
  · exact Eventually.of_forall fun s => h.smul_const (u s)
  · rw [rankOne_apply]
    filter_upwards [Lp.coeFn_smul (inner ℝ v x) u] with s hs
    change (inner ℝ v x • u : Lp W 2 μ) s = ∫ t, inner ℝ (v t) (x t) • u s ∂μ
    rw [hs]
    change inner ℝ v x • u s = _
    rw [integral_smul_const, L2.inner_def]

omit [SFinite μ] [IsSeparable μ] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
private theorem represents_sumGreenKernel {ι : Type*} [Fintype ι]
    (K : ι → GreenKernel ℝ X V W) (x : Lp V 2 μ) (z : ι → Lp W 2 μ)
    (h : ∀ i, RepresentsGreenAction (K i) x (z i)) :
    RepresentsGreenAction (fun s t => ∑ i, K i s t) x (∑ i, z i) := by
  have hI : ∀ᵐ s ∂μ, ∀ i, Integrable (fun t => K i s t (x t)) μ :=
    eventually_all.mpr fun i => (h i).integrable_row
  have hE : ∀ᵐ s ∂μ, ∀ i, z i s = greenIntegral (K i) μ x s :=
    eventually_all.mpr fun i => (h i).ae_eq_integral
  constructor
  · filter_upwards [hI] with s hs
    simp only [sum_apply]
    exact integrable_finsetSum _ fun i _ => hs i
  · filter_upwards [hI, hE, Lp.coeFn_fun_finsetSum Finset.univ z] with s hi hs hsum
    change (∑ i, z i : Lp W 2 μ) s = ∫ t, (∑ i, K i s t) (x t) ∂μ
    rw [hsum]
    simp only [sum_apply]
    rw [integral_finsetSum _ (fun i _ => hi i)]
    exact Finset.sum_congr rfl fun i _ => hs i

omit [SFinite μ] [IsSeparable μ] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
private theorem isGeneralizedGreenKernel_iff_represented_graph
    (L : Lp W 2 μ →ₗ.[ℝ] Lp V 2 μ) (G : GreenKernel ℝ X V W)
    (T : Lp V 2 μ →L[ℝ] Lp W 2 μ) (hT : ∀ y, RepresentsGreenAction G y (T y)) :
    IsGeneralizedGreenKernel L G ↔ ∀ y ∈ L.toFun.range, (T y, y) ∈ L.graph := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, hRep⟩ := h ⟨y, hy⟩
    refine L.mem_graph_iff.mpr ⟨x, ?_, hx⟩
    exact hRep.output_unique (hT y)
  · intro h y
    obtain ⟨x, hx, hy⟩ := L.mem_graph_iff.mp (h y.val y.property)
    exact ⟨x, hy, hx ▸ hT y.val⟩

omit [IsSeparable μ] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
private theorem greenAction_congr_ae_kernel {G K : GreenKernel ℝ X V W}
    {x : Lp V 2 μ} {y : Lp W 2 μ}
    (hGK : (fun p : X × X => G p.1 p.2) =ᵐ[μ.prod μ] fun p => K p.1 p.2)
    (hG : RepresentsGreenAction G x y) : RepresentsGreenAction K x y := by
  have hrows := Measure.ae_ae_of_ae_prod hGK
  have hh : ∀ᵐ s ∂μ, (fun t => G s t (x t)) =ᵐ[μ] fun t => K s t (x t) := by
    filter_upwards [hrows] with s hs
    filter_upwards [hs] with t ht
    rw [ht]
  constructor
  · filter_upwards [hh, hG.integrable_row] with s hs hI
    exact hI.congr hs
  · filter_upwards [hh, hG.ae_eq_integral] with s hs hE
    exact hE.trans (integral_congr_ae hs)

set_option maxHeartbeats 2000000 in
-- The operator decomposition is transferred to the kernel via two finite sums.
/-- **Exercise 32**, Equation (61), of [benIsrael2003generalized].
For two square-integrable kernels with bounded actions, the generalized Green
condition is equivalent to the two separated corrections almost everywhere. -/
theorem exercise_9_32_l2 (L : Lp W 2 μ →ₗ.[ℝ] Lp V 2 μ)
    (hL : IsNormallySolvable L) (hD : Dense (L.domain : Set (Lp W 2 μ)))
    (G K : GreenKernel ℝ X V W)
    (hG₂ : MemLp (fun p : X × X => G p.1 p.2) 2 (μ.prod μ))
    (hK₂ : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) (hG : IsGeneralizedGreenKernel L G)
    (T U : Lp V 2 μ →L[ℝ] Lp W 2 μ) (hT : ∀ y, RepresentsGreenAction G y (T y))
    (hU : ∀ y, RepresentsGreenAction K y (U y))
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ L.ker) (c : OrthonormalBasis κ ℝ L.adjoint.ker) :
    IsGeneralizedGreenKernel L K ↔
      ∃ (a : ι → Lp V 2 μ) (w : κ → Lp W 2 μ),
        (fun p : X × X => K p.1 p.2) =ᵐ[μ.prod μ] fun p =>
          G p.1 p.2 + (∑ i, rankOneGreenKernel (b i : Lp W 2 μ) (a i) p.1 p.2) +
            ∑ j, rankOneGreenKernel (w j) (c j : Lp V 2 μ) p.1 p.2 := by
  let U₁ (a : ι → Lp V 2 μ) : Lp V 2 μ →L[ℝ] Lp W 2 μ :=
    ∑ i, rankOne ℝ (b i : Lp W 2 μ) (a i)
  let U₂ (w : κ → Lp W 2 μ) : Lp V 2 μ →L[ℝ] Lp W 2 μ :=
    ∑ j, rankOne ℝ (w j) (c j : Lp V 2 μ)
  let G' (a : ι → Lp V 2 μ) (w : κ → Lp W 2 μ) : GreenKernel ℝ X V W :=
    fun s t => G s t + (∑ i, rankOneGreenKernel (b i : Lp W 2 μ) (a i) s t) +
      ∑ j, rankOneGreenKernel (w j) (c j : Lp V 2 μ) s t
  have hrep (a : ι → Lp V 2 μ) (w : κ → Lp W 2 μ) (y : Lp V 2 μ) :
      RepresentsGreenAction (G' a w) y ((T + U₁ a + U₂ w) y) := by
    have h₁ := represents_sumGreenKernel
      (fun i => rankOneGreenKernel (b i : Lp W 2 μ) (a i)) y
      (fun i => rankOne ℝ (b i : Lp W 2 μ) (a i) y)
      (fun i => represents_rankOneGreenKernel (b i : Lp W 2 μ) (a i) y)
    have h₂ := represents_sumGreenKernel
      (fun j => rankOneGreenKernel (w j) (c j : Lp V 2 μ)) y
      (fun j => rankOne ℝ (w j) (c j : Lp V 2 μ) y)
      (fun j => represents_rankOneGreenKernel (w j) (c j : Lp V 2 μ) y)
    simpa only [G', U₁, U₂, add_apply, sum_apply] using ((hT y).addKernel h₁).addKernel h₂
  have h₂ (a : ι → Lp V 2 μ) (w : κ → Lp W 2 μ) :
      MemLp (fun p : X × X => G' a w p.1 p.2) 2 (μ.prod μ) := by
    let left (i : ι) (p : X × X) := rankOneGreenKernel (b i : Lp W 2 μ) (a i) p.1 p.2
    let right (j : κ) (p : X × X) := rankOneGreenKernel (w j) (c j : Lp V 2 μ) p.1 p.2
    have hleft : MemLp (fun p : X × X => ∑ i, left i p) 2 (μ.prod μ) :=
      memLp_finsetSum (f := left) Finset.univ (fun i _ => memLp_rankOneGreenKernel (b i : Lp W 2 μ) (a i))
    have hright : MemLp (fun p : X × X => ∑ j, right j p) 2 (μ.prod μ) :=
      memLp_finsetSum (f := right) Finset.univ (fun j _ => memLp_rankOneGreenKernel (w j) (c j : Lp V 2 μ))
    change MemLp (fun p : X × X => G p.1 p.2 + (∑ i, left i p) + ∑ j, right j p) 2 (μ.prod μ)
    exact MemLp.add (MemLp.add hG₂ hleft) hright
  have hKgraph := isGeneralizedGreenKernel_iff_represented_graph L K U hU
  have hTgraph := (isGeneralizedGreenKernel_iff_represented_graph L G T hT).mp hG
  have hDecomp := greenOperator_difference_iff L hL hD T U hTgraph b c
  constructor
  · intro hK
    obtain ⟨a, w, hv⟩ := hDecomp.mp (hKgraph.mp hK)
    refine ⟨a, w, ?_⟩
    change (fun p : X × X => K p.1 p.2) =ᵐ[μ.prod μ] fun p => G' a w p.1 p.2
    let D : GreenKernel ℝ X V W := fun s t => K s t - G' a w s t
    have hD₂ : MemLp (fun p : X × X => D p.1 p.2) 2 (μ.prod μ) := hK₂.sub (h₂ a w)
    have hZ (y : Lp V 2 μ) : RepresentsGreenAction D y 0 := by
      have he := (hU y).subKernel (hrep a w y)
      have hy : (T + U₁ a + U₂ w) y = U y := DFunLike.congr_fun hv.symm y
      rw [hy, sub_self] at he
      exact he
    filter_upwards [greenKernel_ae_zero_of_action_zero D hD₂ hZ] with p hp
    exact sub_eq_zero.mp hp
  · rintro ⟨a, w, hkw⟩
    apply hKgraph.mpr
    apply hDecomp.mpr
    refine ⟨a, w, ?_⟩
    apply ContinuousLinearMap.ext
    intro y
    exact (hU y).output_unique (greenAction_congr_ae_kernel
      (Filter.EventuallyEq.symm hkw) (hrep a w y))

end RealGreenKernels


end GreenKernelFiniteRank

section EssentiallyBoundedGreenKernels

variable {X V W : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace V] [CompleteSpace W] in
/-- On a finite measure space, a measurable essentially bounded Green kernel
sends every square-integrable input to an essentially bounded output. -/
theorem exists_bounded_greenAction (G : GreenKernel ℝ X V W)
    (hG : AEStronglyMeasurable (fun p : X × X => G p.1 p.2) (μ.prod μ))
    {C : ℝ} (_hC : 0 ≤ C) (hB : ∀ᵐ p : X × X ∂(μ.prod μ), ‖G p.1 p.2‖ ≤ C)
    (y : Lp V 2 μ) : ∃ x : Lp W 2 μ, RepresentsGreenAction G y x ∧
      MemLp (fun s => x s) ∞ μ := by
  have hy : Integrable (fun t => ‖y t‖) μ :=
    (Lp.memLp y).norm.integrable (by norm_num)
  have hmeas : AEStronglyMeasurable (fun p : X × X => G p.1 p.2 (y p.2)) (μ.prod μ) :=
    (ContinuousLinearMap.apply ℝ W).aestronglyMeasurable_comp₂
      (Lp.aestronglyMeasurable y).comp_snd hG
  have hdom : ∀ᵐ s ∂μ, ∀ᵐ t ∂μ, ‖G s t (y t)‖ ≤ C * ‖y t‖ := by
    filter_upwards [Measure.ae_ae_of_ae_prod hB] with s hs
    filter_upwards [hs] with t ht
    calc
      ‖G s t (y t)‖ ≤ ‖G s t‖ * ‖y t‖ := (G s t).le_opNorm _
      _ ≤ C * ‖y t‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  have hI : ∀ᵐ s ∂μ, Integrable (fun t => G s t (y t)) μ := by
    filter_upwards [hmeas.prodMk_left, hdom] with s hs hd
    exact Integrable.mono' (hy.const_mul C) hs hd
  have hlim : ∀ᵐ s ∂μ, ‖greenIntegral G μ y s‖ ≤ C * ∫ t, ‖y t‖ ∂μ := by
    filter_upwards [hI, hdom] with s hs hd
    calc
      ‖greenIntegral G μ y s‖ ≤ ∫ t, ‖G s t (y t)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, C * ‖y t‖ ∂μ := integral_mono_ae hs.norm (hy.const_mul C) hd
      _ = _ := integral_const_mul _ _
  have hI₂ : MemLp (greenIntegral G μ y) 2 μ :=
    MemLp.of_bound hmeas.integral_prod_right' _ hlim
  have hI_top : MemLp (greenIntegral G μ y) ∞ μ :=
    MemLp.of_bound hmeas.integral_prod_right' _ hlim
  let x := hI₂.toLp _
  have hx : (fun s => x s) =ᵐ[μ] greenIntegral G μ y := MemLp.coeFn_toLp hI₂
  exact ⟨x, ⟨hI, hx⟩, (memLp_congr_ae (Filter.EventuallyEq.symm hx)).mp hI_top⟩

omit [CompleteSpace V] [CompleteSpace W] in
private theorem norm_bound_of_bounded_greenAction (G : GreenKernel ℝ X V W)
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ᵐ p : X × X ∂(μ.prod μ), ‖G p.1 p.2‖ ≤ C)
    {y : Lp V 2 μ} {x : Lp W 2 μ} (h : RepresentsGreenAction G y x) :
    ‖x‖ ≤ ((μ Set.univ).toReal * C) * ‖y‖ := by
  let m := (μ Set.univ).toReal
  have hy : Integrable (fun t => ‖y t‖) μ := (Lp.memLp y).norm.integrable (by norm_num)
  have hCInt : 0 ≤ C * ∫ t, ‖y t‖ ∂μ := mul_nonneg hC (integral_nonneg fun _ => norm_nonneg _)
  have hxb : ∀ᵐ s ∂μ, ‖x s‖ ≤ C * ∫ t, ‖y t‖ ∂μ := by
    filter_upwards [h.ae_eq_integral, h.integrable_row, Measure.ae_ae_of_ae_prod hB] with s he hi hb
    rw [he]
    calc
      ‖greenIntegral G μ y s‖ ≤ ∫ t, ‖G s t (y t)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, C * ‖y t‖ ∂μ := by
        apply integral_mono_ae hi.norm (hy.const_mul C)
        filter_upwards [hb] with t ht
        exact ((G s t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
      _ = _ := integral_const_mul _ _
  have hnorm : ‖x‖ ≤ m ^ (1 / 2 : ℝ) * (C * ∫ t, ‖y t‖ ∂μ) := by
    have h := Lp.norm_le_of_ae_bound hCInt hxb
    norm_num [m, measureUnivNNReal, one_div] at h ⊢
    exact h
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1 : ℝ≥0∞) ≤ 2 by norm_num) (Lp.aestronglyMeasurable y)
  have hn : ∫ t, ‖y t‖ ∂μ ≤ ‖y‖ * m ^ (1 / 2 : ℝ) := by
    rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable y),
      ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable y), Lp.norm_def]
    have he : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
    rw [he] at hcompare
    have hfin : eLpNorm y 2 μ * μ Set.univ ^ (1 / 2 : ℝ) ≠ ∞ :=
      ENNReal.mul_ne_top (Lp.eLpNorm_ne_top y) (ENNReal.rpow_ne_top_of_nonneg (by positivity)
        (measure_ne_top _ _))
    simpa only [m, ENNReal.toReal_mul, ENNReal.toReal_rpow] using ENNReal.toReal_mono hfin hcompare
  calc
    ‖x‖ ≤ m ^ (1 / 2 : ℝ) * (C * ∫ t, ‖y t‖ ∂μ) := hnorm
    _ ≤ m ^ (1 / 2 : ℝ) * (C * (‖y‖ * m ^ (1 / 2 : ℝ))) := by gcongr
    _ = m * C * ‖y‖ := by
      have hm : m ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ) = m := by
        rw [← Real.rpow_add_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num [m]
      linear_combination C * ‖y‖ * hm

omit [CompleteSpace V] [CompleteSpace W] in
/-- A measurable essentially bounded Green kernel on a finite measure space
has a bounded integral action on the entire square-integrable space. -/
theorem exists_bounded_greenOperator (G : GreenKernel ℝ X V W)
    (hG : AEStronglyMeasurable (fun p : X × X => G p.1 p.2) (μ.prod μ))
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ᵐ p : X × X ∂(μ.prod μ), ‖G p.1 p.2‖ ≤ C) :
    ∃ T : Lp V 2 μ →L[ℝ] Lp W 2 μ, ∀ y, RepresentsGreenAction G y (T y) := by
  choose f hf _ using exists_bounded_greenAction G hG hC hB
  let S : Lp V 2 μ →ₗ[ℝ] Lp W 2 μ :=
    { toFun := f
      map_add' := fun x y => (hf (x + y)).output_unique ((hf x).add (hf y))
      map_smul' := fun c y => (hf (c • y)).output_unique ((hf y).smul c) }
  exact ⟨S.mkContinuous ((μ Set.univ).toReal * C) fun y =>
    norm_bound_of_bounded_greenAction G hC hB (hf y), hf⟩

/-- The real adjoint Green kernel interchanges the arguments and takes the
adjoint of the coefficient map. -/
def adjointGreenKernel (G : GreenKernel ℝ X V W) : GreenKernel ℝ X W V :=
  fun s t => (G t s).adjoint

private theorem adjointGreenKernel_measurable (G : GreenKernel ℝ X V W)
    (hG : AEStronglyMeasurable (fun p : X × X => G p.1 p.2) (μ.prod μ)) :
    AEStronglyMeasurable (fun p : X × X => adjointGreenKernel G p.1 p.2) (μ.prod μ) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_aestronglyMeasurable
    (hG.comp_measurePreserving Measure.measurePreserving_swap)

private theorem adjointGreenKernel_norm_bound (G : GreenKernel ℝ X V W) {C : ℝ}
    (hG : ∀ᵐ p : X × X ∂(μ.prod μ), ‖G p.1 p.2‖ ≤ C) :
    ∀ᵐ p : X × X ∂(μ.prod μ), ‖adjointGreenKernel G p.1 p.2‖ ≤ C := by
  have he := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hG
  filter_upwards [he] with p hp
  change ‖(G p.2 p.1).adjoint‖ ≤ C
  rwa [ContinuousLinearMap.adjoint.norm_map]

set_option maxHeartbeats 550000 in
-- Fubini interchanges two represented Hilbert-space pairings using the bounded kernel.
private theorem boundedGreenAction_inner_adjoint (G : GreenKernel ℝ X V W)
    (hG : AEStronglyMeasurable (fun p : X × X => G p.1 p.2) (μ.prod μ))
    {C : ℝ} (hB : ∀ᵐ p : X × X ∂(μ.prod μ), ‖G p.1 p.2‖ ≤ C)
    {v v' : Lp V 2 μ} {w w' : Lp W 2 μ}
    (h : RepresentsGreenAction G v w') (h' : RepresentsGreenAction (adjointGreenKernel G) w v') :
    inner ℝ v' v = inner ℝ w w' := by
  let f (p : X × X) := inner ℝ (w p.1) (G p.1 p.2 (v p.2))
  have hv : Integrable (fun t => ‖v t‖) μ := (Lp.memLp v).norm.integrable (by norm_num)
  have hw : Integrable (fun s => ‖w s‖) μ := (Lp.memLp w).norm.integrable (by norm_num)
  have hmeas : AEStronglyMeasurable f (μ.prod μ) :=
    (Lp.aestronglyMeasurable w).comp_fst.inner
      ((ContinuousLinearMap.apply ℝ W).aestronglyMeasurable_comp₂
        (Lp.aestronglyMeasurable v).comp_snd hG)
  have hf : Integrable f (μ.prod μ) := by
    refine Integrable.mono' ((hw.mul_prod hv).const_mul C) hmeas ?_
    filter_upwards [hB] with p hp
    calc
      ‖f p‖ ≤ ‖w p.1‖ * ‖G p.1 p.2 (v p.2)‖ := norm_inner_le_norm _ _
      _ ≤ ‖w p.1‖ * (‖G p.1 p.2‖ * ‖v p.2‖) := by gcongr; exact (G p.1 p.2).le_opNorm _
      _ ≤ ‖w p.1‖ * (C * ‖v p.2‖) := by gcongr
      _ = _ := by ring
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ t, inner ℝ (v' t) (v t) ∂μ) = ∫ t, ∫ s, f (s, t) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [h'.ae_eq_integral, h'.integrable_row] with t ht hI
      rw [real_inner_comm, ht]
      change (innerSL ℝ (v t)) (∫ s, adjointGreenKernel G t s (w s) ∂μ) = _
      rw [← (innerSL ℝ (v t)).integral_comp_comm hI]
      apply integral_congr_ae
      filter_upwards with s
      change inner ℝ (v t) ((G s t).adjoint (w s)) = f (s, t)
      rw [(G s t).adjoint_inner_right, real_inner_comm]
    _ = ∫ s, ∫ t, f (s, t) ∂μ ∂μ := (integral_integral_swap hf).symm
    _ = ∫ s, inner ℝ (w s) (w' s) ∂μ := by
      apply integral_congr_ae
      filter_upwards [h.ae_eq_integral, h.integrable_row] with s hs hI
      rw [hs]
      exact (innerSL ℝ (w s)).integral_comp_comm hI

private theorem represents_adjointGreenKernel
    (G : GreenKernel ℝ X V W)
    (hG : AEStronglyMeasurable (fun p : X × X => G p.1 p.2) (μ.prod μ))
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ᵐ p : X × X ∂(μ.prod μ), ‖G p.1 p.2‖ ≤ C)
    (T : Lp V 2 μ →L[ℝ] Lp W 2 μ) (hT : ∀ v, RepresentsGreenAction G v (T v))
    (w : Lp W 2 μ) : RepresentsGreenAction (adjointGreenKernel G) w (T.adjoint w) := by
  obtain ⟨u, hu, _⟩ := exists_bounded_greenAction (adjointGreenKernel G)
    (adjointGreenKernel_measurable G hG) hC (adjointGreenKernel_norm_bound G hB) w
  have he : T.adjoint w = u := by
    apply ext_inner_right ℝ
    intro v
    rw [T.adjoint_inner_left]
    exact (boundedGreenAction_inner_adjoint G hG hB (hT v) hu).symm
  exact he.symm ▸ hu

/-- The adjoint of an operator represented by an essentially bounded Green
kernel also has essentially bounded output. -/
theorem memLp_top_adjoint_of_boundedGreenAction (G : GreenKernel ℝ X V W)
    (hG : AEStronglyMeasurable (fun p : X × X => G p.1 p.2) (μ.prod μ))
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ᵐ p : X × X ∂(μ.prod μ), ‖G p.1 p.2‖ ≤ C)
    (T : Lp V 2 μ →L[ℝ] Lp W 2 μ) (hT : ∀ v, RepresentsGreenAction G v (T v))
    (w : Lp W 2 μ) : MemLp (fun t => (T.adjoint w) t) ∞ μ := by
  obtain ⟨u, hu, hu_top⟩ := exists_bounded_greenAction (adjointGreenKernel G)
    (adjointGreenKernel_measurable G hG) hC (adjointGreenKernel_norm_bound G hB) w
  exact hu.output_unique (represents_adjointGreenKernel G hG hC hB T hT w) ▸ hu_top

end EssentiallyBoundedGreenKernels

section BoundedGreenDifference

open InnerProductSpace

variable {X V W : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] [IsSeparable μ]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

private theorem rankOne_sum_values {A B ι : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [Fintype ι] {S : Submodule ℝ A}
    (b : OrthonormalBasis ι ℝ S) (v : ι → B) (i : ι) :
    (∑ j, rankOne ℝ (v j) (b j : A)) (b i : A) = v i := by
  classical
  have h (j : ι) : inner ℝ (b j : A) (b i : A) = if j = i then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal j i
  simp only [sum_apply, rankOne_apply, h]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hne
    simp [hne]
  · simp

omit [IsFiniteMeasure μ] [IsSeparable μ] in
private theorem memLp_top_sum_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (x : ι → Lp E 2 μ) (c : ι → ℝ)
    (hx : ∀ i, MemLp (fun t => x i t) ∞ μ) :
    MemLp (fun t => (∑ i, c i • x i : Lp E 2 μ) t) ∞ μ := by
  have h₁ : MemLp (fun t => ∑ i, c i • x i t) ∞ μ :=
    memLp_finsetSum _ fun i _ => (hx i).const_smul (c i)
  apply (memLp_congr_ae ?_).mp h₁
  symm
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • x i)).trans ?_
  filter_upwards [eventually_all.mpr fun i => Lp.coeFn_smul (c i) (x i)] with t ht
  exact Finset.sum_congr rfl fun i _ => ht i

omit [IsFiniteMeasure μ] [IsSeparable μ] in
private theorem green_memLp_top_sub {E : Type*} [NormedAddCommGroup E] {u v : Lp E 2 μ}
    (hu : MemLp (fun t => u t) ∞ μ) (hv : MemLp (fun t => v t) ∞ μ) :
    MemLp (fun t => (u - v) t) ∞ μ :=
  (memLp_congr_ae (Lp.coeFn_sub u v).symm).mp (hu.sub hv)

omit [IsFiniteMeasure μ] [IsSeparable μ] in
private theorem greenDifferenceCoefficients_memLp_top
    {L : Lp W 2 μ →ₗ.[ℝ] Lp V 2 μ}
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ L.ker) (c : OrthonormalBasis κ ℝ L.adjoint.ker)
    (hb : ∀ i, MemLp (fun t => (b i : Lp W 2 μ) t) ∞ μ)
    (hc : ∀ j, MemLp (fun t => (c j : Lp V 2 μ) t) ∞ μ)
    (R : Lp V 2 μ →L[ℝ] Lp W 2 μ) (a : ι → Lp V 2 μ) (w : κ → Lp W 2 μ)
    (hR_eq : R = (∑ i, rankOne ℝ (b i : Lp W 2 μ) (a i)) +
      ∑ j, rankOne ℝ (w j) (c j : Lp V 2 μ))
    (hR : ∀ y, MemLp (fun t => (R y) t) ∞ μ)
    (hR' : ∀ x, MemLp (fun t => (R.adjoint x) t) ∞ μ) :
    (∀ i, MemLp (fun t => a i t) ∞ μ) ∧ (∀ j, MemLp (fun t => w j t) ∞ μ) := by
  have ha (i : ι) : MemLp (fun t => a i t) ∞ μ := by
    have hEq : R.adjoint (b i : Lp W 2 μ) =
        a i + ∑ j, inner ℝ (w j) (b i : Lp W 2 μ) • (c j : Lp V 2 μ) := by
      rw [hR_eq, map_add, map_sum, map_sum]
      simp only [adjoint_rankOne, add_apply, rankOne_sum_values b, sum_apply, rankOne_apply]
    have hEq' : a i = R.adjoint (b i : Lp W 2 μ) -
        ∑ j, inner ℝ (w j) (b i : Lp W 2 μ) • (c j : Lp V 2 μ) := by
      rw [hEq, add_sub_cancel_right]
    rw [hEq']
    exact green_memLp_top_sub (hR' (b i : Lp W 2 μ)) (memLp_top_sum_smul
      (fun j => (c j : Lp V 2 μ)) (fun j => inner ℝ (w j) (b i : Lp W 2 μ)) hc)
  have hw (j : κ) : MemLp (fun t => w j t) ∞ μ := by
    have hEq : R (c j : Lp V 2 μ) =
        (∑ i, inner ℝ (a i) (c j : Lp V 2 μ) • (b i : Lp W 2 μ)) + w j := by
      rw [hR_eq, add_apply, rankOne_sum_values c]
      simp only [sum_apply, rankOne_apply]
    have hEq' : w j = R (c j : Lp V 2 μ) -
        ∑ i, inner ℝ (a i) (c j : Lp V 2 μ) • (b i : Lp W 2 μ) := by
      rw [hEq, add_sub_cancel_left]
    rw [hEq']
    exact green_memLp_top_sub (hR (c j : Lp V 2 μ)) (memLp_top_sum_smul
      (fun i => (b i : Lp W 2 μ)) (fun i => inner ℝ (a i) (c j : Lp V 2 μ)) hb)
  exact ⟨ha, hw⟩

set_option maxHeartbeats 1000000 in
-- The two coefficients are recovered from the action and adjoint action of the difference.
/-- **Exercise 32**, Equation (61), of [benIsrael2003generalized].
In a common essentially bounded kernel class on a finite interval, the two
families of separated correction coefficients can both be taken essentially
bounded. Null-space basis vectors are assumed essentially bounded, as in
the smooth differential realization. -/
theorem exercise_9_32_of_representation (L : Lp W 2 μ →ₗ.[ℝ] Lp V 2 μ)
    (hL : IsNormallySolvable L) (hD : Dense (L.domain : Set (Lp W 2 μ)))
    (G K : GreenKernel ℝ X V W)
    (hGm : AEStronglyMeasurable (fun p : X × X => G p.1 p.2) (μ.prod μ))
    (hKm : AEStronglyMeasurable (fun p : X × X => K p.1 p.2) (μ.prod μ))
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hGb : ∀ᵐ p : X × X ∂(μ.prod μ), ‖G p.1 p.2‖ ≤ C₁)
    (hKb : ∀ᵐ p : X × X ∂(μ.prod μ), ‖K p.1 p.2‖ ≤ C₂) (hG : IsGeneralizedGreenKernel L G)
    (T U : Lp V 2 μ →L[ℝ] Lp W 2 μ) (hT : ∀ y, RepresentsGreenAction G y (T y))
    (hU : ∀ y, RepresentsGreenAction K y (U y))
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ L.ker) (c : OrthonormalBasis κ ℝ L.adjoint.ker)
    (hb : ∀ i, MemLp (fun t => (b i : Lp W 2 μ) t) ∞ μ)
    (hc : ∀ j, MemLp (fun t => (c j : Lp V 2 μ) t) ∞ μ) :
    IsGeneralizedGreenKernel L K ↔
      ∃ (a : ι → Lp V 2 μ) (w : κ → Lp W 2 μ),
        (∀ i, MemLp (fun t => a i t) ∞ μ) ∧ (∀ j, MemLp (fun t => w j t) ∞ μ) ∧
        (fun p : X × X => K p.1 p.2) =ᵐ[μ.prod μ] fun p =>
          G p.1 p.2 + (∑ i, rankOneGreenKernel (b i : Lp W 2 μ) (a i) p.1 p.2) +
            ∑ j, rankOneGreenKernel (w j) (c j : Lp V 2 μ) p.1 p.2 := by
  have hG₂ : MemLp (fun p : X × X => G p.1 p.2) 2 (μ.prod μ) := MemLp.of_bound hGm _ hGb
  have hK₂ : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ) := MemLp.of_bound hKm _ hKb
  have hL₂ := exercise_9_32_l2 L hL hD G K hG₂ hK₂ hG T U hT hU b c
  constructor
  · intro hK
    obtain ⟨a, w, hEq⟩ := hL₂.mp hK
    have hOp : U = T + (∑ i, rankOne ℝ (b i : Lp W 2 μ) (a i)) +
        ∑ j, rankOne ℝ (w j) (c j : Lp V 2 μ) := by
      apply ContinuousLinearMap.ext
      intro y
      have h₁ := represents_sumGreenKernel
        (fun i => rankOneGreenKernel (b i : Lp W 2 μ) (a i)) y
        (fun i => rankOne ℝ (b i : Lp W 2 μ) (a i) y)
        (fun i => represents_rankOneGreenKernel (b i : Lp W 2 μ) (a i) y)
      have h₂ := represents_sumGreenKernel
        (fun j => rankOneGreenKernel (w j) (c j : Lp V 2 μ)) y
        (fun j => rankOne ℝ (w j) (c j : Lp V 2 μ) y)
        (fun j => represents_rankOneGreenKernel (w j) (c j : Lp V 2 μ) y)
      exact (hU y).output_unique (greenAction_congr_ae_kernel
        (Filter.EventuallyEq.symm hEq) (by
          simpa only [add_apply, sum_apply] using ((hT y).addKernel h₁).addKernel h₂))
    let D : GreenKernel ℝ X V W := fun s t => K s t - G s t
    let R := U - T
    have hm : AEStronglyMeasurable (fun p : X × X => D p.1 p.2) (μ.prod μ) := hKm.sub hGm
    have hn : ∀ᵐ p : X × X ∂(μ.prod μ), ‖D p.1 p.2‖ ≤ C₂ + C₁ := by
      filter_upwards [hKb, hGb] with p hk hg
      exact (norm_sub_le _ _).trans (add_le_add hk hg)
    have hR (y : Lp V 2 μ) : RepresentsGreenAction D y (R y) := (hU y).subKernel (hT y)
    have hR_eq : R = (∑ i, rankOne ℝ (b i : Lp W 2 μ) (a i)) +
        ∑ j, rankOne ℝ (w j) (c j : Lp V 2 μ) := by
      dsimp only [R]
      rw [hOp]
      abel
    have hR_top (y : Lp V 2 μ) : MemLp (fun t => (R y) t) ∞ μ := by
      obtain ⟨x, hx, hx_top⟩ := exists_bounded_greenAction D hm (add_nonneg hC₂ hC₁) hn y
      exact hx.output_unique (hR y) ▸ hx_top
    have hR'_top (x : Lp W 2 μ) : MemLp (fun t => (R.adjoint x) t) ∞ μ :=
      memLp_top_adjoint_of_boundedGreenAction D hm (add_nonneg hC₂ hC₁) hn R hR x
    obtain ⟨ha, hw⟩ := greenDifferenceCoefficients_memLp_top b c hb hc R a w hR_eq hR_top hR'_top
    exact ⟨a, w, ha, hw, hEq⟩
  · rintro ⟨a, w, _, _, he⟩
    exact hL₂.mpr ⟨a, w, he⟩

/-- **Exercise 32**, Equation (61), of [benIsrael2003generalized].
For bounded measurable kernels the integral operators exist on all of $L^2$.
The generalized Green kernels are exactly the two separated corrections to
any fixed generalized Green kernel. -/
theorem exercise_9_32 (L : Lp W 2 μ →ₗ.[ℝ] Lp V 2 μ)
    (hL : IsNormallySolvable L) (hD : Dense (L.domain : Set (Lp W 2 μ)))
    (G K : GreenKernel ℝ X V W)
    (hGm : AEStronglyMeasurable (fun p : X × X => G p.1 p.2) (μ.prod μ))
    (hKm : AEStronglyMeasurable (fun p : X × X => K p.1 p.2) (μ.prod μ))
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hGb : ∀ᵐ p : X × X ∂(μ.prod μ), ‖G p.1 p.2‖ ≤ C₁)
    (hKb : ∀ᵐ p : X × X ∂(μ.prod μ), ‖K p.1 p.2‖ ≤ C₂)
    (hG : IsGeneralizedGreenKernel L G)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ L.ker) (c : OrthonormalBasis κ ℝ L.adjoint.ker)
    (hb : ∀ i, MemLp (fun t => (b i : Lp W 2 μ) t) ∞ μ)
    (hc : ∀ j, MemLp (fun t => (c j : Lp V 2 μ) t) ∞ μ) :
    IsGeneralizedGreenKernel L K ↔ ∃ (a : ι → Lp V 2 μ) (w : κ → Lp W 2 μ),
      (∀ i, MemLp (fun t => a i t) ∞ μ) ∧ (∀ j, MemLp (fun t => w j t) ∞ μ) ∧
      (fun p : X × X => K p.1 p.2) =ᵐ[μ.prod μ] fun p =>
        G p.1 p.2 + (∑ i, rankOneGreenKernel (b i : Lp W 2 μ) (a i) p.1 p.2) +
          ∑ j, rankOneGreenKernel (w j) (c j : Lp V 2 μ) p.1 p.2 := by
  obtain ⟨T, hT⟩ := exists_bounded_greenOperator G hGm hC₁ hGb
  obtain ⟨U, hU⟩ := exists_bounded_greenOperator K hKm hC₂ hKb
  exact exercise_9_32_of_representation L hL hD G K hGm hKm hC₁ hC₂ hGb hKb hG T U hT hU b c hb hc

end BoundedGreenDifference

section BiorthogonalGreenKernels

open InnerProductSpace

variable {X V W : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] [IsSeparable μ]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [FiniteDimensional ℝ W]

private theorem exists_nonnegative_bound_of_memLp_top {Y E : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup E] {ν : Measure Y} {f : Y → E} (hf : MemLp f ∞ ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ t ∂ν, ‖f t‖ ≤ C := by
  have htop : eLpNormEssSup f ν < ∞ := by
    simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp htop
  refine ⟨C, C.coe_nonneg, ?_⟩
  filter_upwards [hC] with t ht using NNReal.coe_le_coe.mpr ht

omit [IsFiniteMeasure μ] [IsSeparable μ] [CompleteSpace V] [FiniteDimensional ℝ V]
  [CompleteSpace W] [FiniteDimensional ℝ W] in
private theorem memLp_top_rankOneGreenKernel (u : Lp W 2 μ) (v : Lp V 2 μ)
    (hu : MemLp (fun t => u t) ∞ μ) (hv : MemLp (fun t => v t) ∞ μ) :
    MemLp (fun p : X × X => rankOneGreenKernel u v p.1 p.2) ∞ (μ.prod μ) := by
  obtain ⟨B, hB, hBu⟩ := exists_nonnegative_bound_of_memLp_top hu
  obtain ⟨C, hC, hCv⟩ := exists_nonnegative_bound_of_memLp_top hv
  apply memLp_top_of_bound (memLp_rankOneGreenKernel u v).aestronglyMeasurable (B * C)
  have h₁ := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hBu
  have h₂ := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hCv
  filter_upwards [h₁, h₂] with p hp hq
  change ‖rankOne ℝ (u p.1) (v p.2)‖ ≤ B * C
  rw [norm_rankOne]
  exact mul_le_mul hp hq (norm_nonneg _) hB

omit [IsFiniteMeasure μ] [IsSeparable μ] in
private theorem green_memLp_top_submodule {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {S : Submodule ℝ (Lp E 2 μ)}
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ S)
    (hb : ∀ i, MemLp (fun t => (b i : Lp E 2 μ) t) ∞ μ)
    (u : S) : MemLp (fun t => (u : Lp E 2 μ) t) ∞ μ := by
  have he : (∑ i, b.repr u i • (b i : Lp E 2 μ)) = (u : Lp E 2 μ) := by
    exact_mod_cast b.sum_repr u
  rw [← he]
  exact memLp_top_sum_smul (fun i => (b i : Lp E 2 μ)) (fun i => b.repr u i) hb

set_option maxHeartbeats 1000000 in
-- Finite-rank corrections transfer from represented operators to almost-everywhere kernels.
omit [IsFiniteMeasure μ] [IsSeparable μ] in
private theorem exists_memLp_top_greenKernel_of_difference
    (L : Lp W 2 μ →ₗ.[ℝ] Lp V 2 μ) (hL : IsNormallySolvable L)
    (hD : Dense (L.domain : Set (Lp W 2 μ)))
    (G : GreenKernel ℝ X V W) (hG : MemLp (fun p : X × X => G p.1 p.2) ∞ (μ.prod μ))
    (T U : Lp V 2 μ →L[ℝ] Lp W 2 μ) (hT : ∀ y, RepresentsGreenAction G y (T y))
    (hTg : ∀ y ∈ L.toFun.range, (T y, y) ∈ L.graph)
    (hUg : ∀ y ∈ L.toFun.range, (U y, y) ∈ L.graph)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ L.ker) (c : OrthonormalBasis κ ℝ L.adjoint.ker)
    (hb : ∀ i, MemLp (fun t => (b i : Lp W 2 μ) t) ∞ μ)
    (hc : ∀ j, MemLp (fun t => (c j : Lp V 2 μ) t) ∞ μ)
    (hR : ∀ y, MemLp (fun t => ((U - T) y) t) ∞ μ)
    (hR' : ∀ x, MemLp (fun t => ((U - T).adjoint x) t) ∞ μ) :
    ∃ K : GreenKernel ℝ X V W, MemLp (fun p : X × X => K p.1 p.2) ∞ (μ.prod μ) ∧
      ∀ y, RepresentsGreenAction K y (U y) := by
  obtain ⟨a, w, he⟩ := (greenOperator_difference_iff L hL hD T U hTg b c).mp hUg
  let R := U - T
  have hR_eq : R = (∑ i, rankOne ℝ (b i : Lp W 2 μ) (a i)) +
      ∑ j, rankOne ℝ (w j) (c j : Lp V 2 μ) := by
    dsimp only [R]
    rw [he]
    abel
  obtain ⟨ha, hw⟩ := greenDifferenceCoefficients_memLp_top b c hb hc R a w hR_eq hR hR'
  let P (i : ι) := rankOneGreenKernel (b i : Lp W 2 μ) (a i)
  let Q (j : κ) := rankOneGreenKernel (w j) (c j : Lp V 2 μ)
  refine ⟨fun s t => G s t + (∑ i, P i s t) + ∑ j, Q j s t, ?_, ?_⟩
  · have hP : MemLp (fun p : X × X => ∑ i, P i p.1 p.2) ∞ (μ.prod μ) :=
      memLp_finsetSum (f := fun i (p : X × X) => P i p.1 p.2) Finset.univ fun i _ =>
        memLp_top_rankOneGreenKernel (b i : Lp W 2 μ) (a i) (hb i) (ha i)
    have hQ : MemLp (fun p : X × X => ∑ j, Q j p.1 p.2) ∞ (μ.prod μ) :=
      memLp_finsetSum (f := fun j (p : X × X) => Q j p.1 p.2) Finset.univ fun j _ =>
        memLp_top_rankOneGreenKernel (w j) (c j : Lp V 2 μ) (hw j) (hc j)
    exact MemLp.add (MemLp.add hG hP) hQ
  · intro y
    have hP := represents_sumGreenKernel P y _ fun i =>
      represents_rankOneGreenKernel (b i : Lp W 2 μ) (a i) y
    have hQ := represents_sumGreenKernel Q y _ fun j =>
      represents_rankOneGreenKernel (w j) (c j : Lp V 2 μ) y
    rw [he]
    simpa only [add_apply, sum_apply] using ((hT y).addKernel hP).addKernel hQ

set_option maxHeartbeats 1000000 in
-- The biorthogonal inverse is first constructed on the Hilbert spaces.
omit [IsSeparable μ] in
private theorem normalizedGreenOperator_has_bounded_kernel
    (L : Lp W 2 μ →ₗ.[ℝ] Lp V 2 μ) (hL : IsNormallySolvable L)
    (hD : Dense (L.domain : Set (Lp W 2 μ))) (G : GreenKernel ℝ X V W)
    (hG : MemLp (fun p : X × X => G p.1 p.2) ∞ (μ.prod μ))
    (T : Lp V 2 μ →L[ℝ] Lp W 2 μ) (hT : ∀ y, RepresentsGreenAction G y (T y))
    (hTg : ∀ y ∈ L.toFun.range, (T y, y) ∈ L.graph)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ L.ker) (c : OrthonormalBasis κ ℝ L.adjoint.ker)
    (hb : ∀ i, MemLp (fun t => (b i : Lp W 2 μ) t) ∞ μ)
    (hc : ∀ j, MemLp (fun t => (c j : Lp V 2 μ) t) ∞ μ) :
    letI := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
    ∀ (Θ : Lp W 2 μ →L[ℝ] L.ker) (Ψ : L.adjoint.ker →L[ℝ] Lp V 2 μ),
      (∀ x : L.ker, Θ (x : Lp W 2 μ) = x) →
      (∀ u : L.adjoint.ker, L.adjoint.ker.orthogonalProjectionOnto (Ψ u) = u) →
      ∃ K : GreenKernel ℝ X V W, MemLp (fun p : X × X => K p.1 p.2) ∞ (μ.prod μ) ∧
        ∀ y, RepresentsGreenAction K y (normalizedGreenOperator L T Θ Ψ y) := by
  let := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
  let := hL.1.isClosed_ker.completeSpace_coe
  intro Θ Ψ hΘ hΨ
  let P := L.ker.subtypeL.comp Θ
  let Q := Ψ.comp L.adjoint.ker.orthogonalProjectionOnto
  let C := normalizedGreenOperator L T Θ Ψ
  obtain ⟨M, hM, hBG⟩ := exists_nonnegative_bound_of_memLp_top hG
  have hT_top (y : Lp V 2 μ) : MemLp (fun t => (T y) t) ∞ μ := by
    obtain ⟨z, hz, hz_top⟩ := exists_bounded_greenAction G hG.aestronglyMeasurable hM hBG y
    exact hz.output_unique (hT y) ▸ hz_top
  have hT'_top (x : Lp W 2 μ) : MemLp (fun t => (T.adjoint x) t) ∞ μ :=
    memLp_top_adjoint_of_boundedGreenAction G hG.aestronglyMeasurable hM hBG T hT x
  have hC_top (y : Lp V 2 μ) : MemLp (fun t => (C y) t) ∞ μ := by
    change MemLp (fun t => (T (y - Q y) - (Θ (T (y - Q y)) : Lp W 2 μ)) t) ∞ μ
    exact green_memLp_top_sub (hT_top _) (green_memLp_top_submodule b hb _)
  have hC'_top (x : Lp W 2 μ) : MemLp (fun t => (C.adjoint x) t) ∞ μ := by
    let z := T.adjoint (x - P.adjoint x)
    have hC' : C.adjoint x = z - (Ψ.adjoint z : Lp V 2 μ) := by
      simp only [C, normalizedGreenOperator, z, P, ContinuousLinearMap.adjoint_comp, map_sub,
        ContinuousLinearMap.adjoint_id, Submodule.adjoint_orthogonalProjectionOnto,
        ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
        Submodule.subtypeL_apply, Submodule.coe_sub]
      abel
    rw [hC']
    exact green_memLp_top_sub (hT'_top _) (green_memLp_top_submodule c hc _)
  obtain ⟨hCg, _, _, _⟩ := normalizedGreenOperator_spec L hL hD T hTg Θ Ψ hΘ hΨ
  apply exists_memLp_top_greenKernel_of_difference L hL hD G hG T C hT hTg hCg b c hb hc
  · intro y
    exact green_memLp_top_sub (hC_top y) (hT_top y)
  · intro x
    rw [map_sub, sub_apply]
    exact green_memLp_top_sub (hC'_top x) (hT'_top x)

/-- The two integral equations in (62). The left equation is written with
the adjoint coefficient to let the column vectors of the test maps serve as
inputs to the two integral operators. -/
def HasGreenNormalization {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K : GreenKernel ℝ X V W)
    (Θ₀ : E →L[ℝ] Lp W 2 μ) (Ψ₀ : F →L[ℝ] Lp V 2 μ) : Prop :=
  (∀ u : E, greenIntegral (adjointGreenKernel K) μ (Θ₀ u) =ᵐ[μ] (0 : X → V)) ∧
    (∀ v : F, greenIntegral K μ (Ψ₀ v) =ᵐ[μ] (0 : X → W))

omit [IsFiniteMeasure μ] [IsSeparable μ] in
private theorem greenIntegral_ae_zero_iff {U Z : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {K : GreenKernel ℝ X U Z} {u : Lp U 2 μ} {z : Lp Z 2 μ}
    (hz : RepresentsGreenAction K u z) :
    greenIntegral K μ u =ᵐ[μ] (0 : X → Z) ↔ z = 0 := by
  constructor
  · intro h
    apply Lp.ext
    exact (hz.ae_eq_integral.trans h).trans (Lp.coeFn_zero Z 2 μ).symm
  · rintro rfl
    exact hz.ae_eq_integral.symm.trans (Lp.coeFn_zero Z 2 μ)

omit [CompleteSpace V] [CompleteSpace W] in
private theorem greenKernels_ae_eq_of_represents_same
    (G K : GreenKernel ℝ X V W)
    (hG : MemLp (fun p : X × X => G p.1 p.2) ∞ (μ.prod μ))
    (hK : MemLp (fun p : X × X => K p.1 p.2) ∞ (μ.prod μ))
    (C : Lp V 2 μ →L[ℝ] Lp W 2 μ)
    (hRepG : ∀ y, RepresentsGreenAction G y (C y))
    (hRepK : ∀ y, RepresentsGreenAction K y (C y)) :
    (fun p : X × X => G p.1 p.2) =ᵐ[μ.prod μ] fun p => K p.1 p.2 := by
  let D : GreenKernel ℝ X V W := fun s t => G s t - K s t
  have hD : MemLp (fun p : X × X => D p.1 p.2) 2 (μ.prod μ) :=
    (hG.sub hK).mono_exponent le_top
  have hR (y : Lp V 2 μ) : RepresentsGreenAction D y 0 := by
    simpa only [sub_self] using (hRepG y).subKernel (hRepK y)
  filter_upwards [greenKernel_ae_zero_of_action_zero D hD hR] with p hp
  exact sub_eq_zero.mp hp

set_option maxHeartbeats 1500000 in
-- Both integral normalizations are transferred through the represented action and adjoint.
/-- **Exercise 33** of [benIsrael2003generalized], Chapter 9.
Invertible pairings of the test columns with the primal and adjoint null
spaces give a unique bounded generalized Green kernel up to almost-everywhere
equality. The represented operator has kernel equal to the range of the
forcing test map and range equal to the normalized part of the differential
domain. -/
theorem exercise_9_33
    (L : Lp W 2 μ →ₗ.[ℝ] Lp V 2 μ) (hL : IsNormallySolvable L)
    (hD : Dense (L.domain : Set (Lp W 2 μ))) (G : GreenKernel ℝ X V W)
    (hG : IsGeneralizedGreenKernel L G)
    (hGb : MemLp (fun p : X × X => G p.1 p.2) ∞ (μ.prod μ))
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ L.ker) (c : OrthonormalBasis κ ℝ L.adjoint.ker)
    (hb : ∀ i, MemLp (fun t => (b i : Lp W 2 μ) t) ∞ μ)
    (hc : ∀ j, MemLp (fun t => (c j : Lp V 2 μ) t) ∞ μ)
    (Θ₀ : L.ker →L[ℝ] Lp W 2 μ) (Ψ₀ : L.adjoint.ker →L[ℝ] Lp V 2 μ) :
    letI := hL.1.isClosed_ker.completeSpace_coe
    letI := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
    Function.Bijective (Θ₀.adjoint.comp L.ker.subtypeL) →
    Function.Bijective (L.adjoint.ker.orthogonalProjectionOnto.comp Ψ₀) →
    ∃ K : GreenKernel ℝ X V W, ∃ C : Lp V 2 μ →L[ℝ] Lp W 2 μ,
      MemLp (fun p : X × X => K p.1 p.2) ∞ (μ.prod μ) ∧
      IsGeneralizedGreenKernel L K ∧ (∀ y, RepresentsGreenAction K y (C y)) ∧
      HasGreenNormalization K Θ₀ Ψ₀ ∧ C.ker = Ψ₀.range ∧
      C.range = L.domain ⊓ Θ₀.rangeᗮ ∧
      ∀ K' : GreenKernel ℝ X V W, MemLp (fun p : X × X => K' p.1 p.2) ∞ (μ.prod μ) →
        IsGeneralizedGreenKernel L K' → HasGreenNormalization K' Θ₀ Ψ₀ →
        (fun p : X × X => K' p.1 p.2) =ᵐ[μ.prod μ] fun p => K p.1 p.2 := by
  let := hL.1.isClosed_ker.completeSpace_coe
  let := (L.adjoint_isClosed hD).isClosed_ker.completeSpace_coe
  intro hA hB
  let A := Θ₀.adjoint.comp L.ker.subtypeL
  let B := L.adjoint.ker.orthogonalProjectionOnto.comp Ψ₀
  let Ae := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hA.1)
    (LinearMap.range_eq_top.mpr hA.2)
  let Be := ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hB.1)
    (LinearMap.range_eq_top.mpr hB.2)
  let Θ := (Ae.symm : L.ker →L[ℝ] L.ker).comp Θ₀.adjoint
  let Ψ := Ψ₀.comp (Be.symm : L.adjoint.ker →L[ℝ] L.adjoint.ker)
  have hΘ (x : L.ker) : Θ (x : Lp W 2 μ) = x := Ae.symm_apply_apply x
  have hΨ (v : L.adjoint.ker) : L.adjoint.ker.orthogonalProjectionOnto (Ψ v) = v :=
    Be.apply_symm_apply v
  have hΘker (x : Lp W 2 μ) : Θ x = 0 ↔ Θ₀.adjoint x = 0 := by
    change Ae.symm (Θ₀.adjoint x) = 0 ↔ _
    exact map_eq_zero_iff Ae.symm Ae.symm.injective
  have hΘeq : Θ.ker = Θ₀.rangeᗮ := by
    rw [ContinuousLinearMap.orthogonal_range]
    ext x
    exact hΘker x
  have hΨeq : Ψ.range = Ψ₀.range := by
    ext v
    rw [LinearMap.mem_range, LinearMap.mem_range]
    exact ⟨fun ⟨x, hx⟩ => ⟨Be.symm x, hx⟩, fun ⟨x, hx⟩ => ⟨Be x, by
      change Ψ₀ (Be.symm (Be x)) = v
      rwa [Be.symm_apply_apply]⟩⟩
  obtain ⟨MG, hMG, hGe⟩ := exists_nonnegative_bound_of_memLp_top hGb
  obtain ⟨T, hT⟩ := exists_bounded_greenOperator G hGb.aestronglyMeasurable hMG hGe
  have hTg := (isGeneralizedGreenKernel_iff_represented_graph L G T hT).mp hG
  obtain ⟨K, hKb, hK⟩ := normalizedGreenOperator_has_bounded_kernel L hL hD G hGb T hT hTg
    b c hb hc Θ Ψ hΘ hΨ
  let C := normalizedGreenOperator L T Θ Ψ
  change (∀ y, RepresentsGreenAction K y (C y)) at hK
  obtain ⟨hCg, hCker, hCrange, hUnique⟩ := normalizedGreenOperator_spec L hL hD T hTg Θ Ψ hΘ hΨ
  change C.ker = Ψ.range at hCker
  change C.range = L.domain ⊓ Θ.ker at hCrange
  obtain ⟨MK, hMK, hKe⟩ := exists_nonnegative_bound_of_memLp_top hKb
  have hKadj := represents_adjointGreenKernel K hKb.aestronglyMeasurable hMK hKe C hK
  refine ⟨K, C, hKb, (isGeneralizedGreenKernel_iff_represented_graph L K C hK).mpr hCg,
    hK, ?_, hCker.trans hΨeq, ?_, ?_⟩
  · constructor
    · intro u
      apply (greenIntegral_ae_zero_iff (hKadj (Θ₀ u))).mpr
      apply ext_inner_right ℝ
      intro y
      have hy : C y ∈ C.range := ⟨y, rfl⟩
      rw [hCrange] at hy
      have h0 := (hΘker _).mp (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hy).2)
      rw [C.adjoint_inner_left, ← Θ₀.adjoint_inner_right, h0, inner_zero_right, inner_zero_left]
    · intro v
      apply (greenIntegral_ae_zero_iff (hK (Ψ₀ v))).mpr
      apply LinearMap.mem_ker.mp
      rw [hCker, hΨeq]
      exact ⟨v, rfl⟩
  · rw [hCrange, hΘeq]
  · intro K' hK'b hK'g hK'n
    obtain ⟨M', hM', hK'e⟩ := exists_nonnegative_bound_of_memLp_top hK'b
    obtain ⟨D, hK'⟩ := exists_bounded_greenOperator K' hK'b.aestronglyMeasurable hM' hK'e
    have hDg := (isGeneralizedGreenKernel_iff_represented_graph L K' D hK').mp hK'g
    have hK'adj := represents_adjointGreenKernel K' hK'b.aestronglyMeasurable hM' hK'e D hK'
    have hDθ (y : Lp V 2 μ) : Θ (D y) = 0 := by
      apply (hΘker _).mpr
      apply ext_inner_left ℝ
      intro u
      have he := (greenIntegral_ae_zero_iff (hK'adj (Θ₀ u))).mp (hK'n.1 u)
      rw [Θ₀.adjoint_inner_right, ← D.adjoint_inner_left, he, inner_zero_left, inner_zero_right]
    have hDψ (u : L.adjoint.ker) : D (Ψ u) = 0 :=
      (greenIntegral_ae_zero_iff (hK' (Ψ₀ (Be.symm u)))).mp (hK'n.2 (Be.symm u))
    have he : D = C := hUnique D hDg hDθ hDψ
    exact greenKernels_ae_eq_of_represents_same K' K hK'b hKb C (he ▸ hK') hK

end BiorthogonalGreenKernels

section SignGreen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private def halfSign (s t : ℝ) : ℝ := (1 / 2 : ℝ) * (SignType.sign (s - t) : ℝ)

private theorem halfSign_eq_of_lt {s t : ℝ} (h : t < s) : halfSign s t = 1 / 2 := by
  simp [halfSign, sign_pos (sub_pos.mpr h)]

private theorem halfSign_eq_of_gt {s t : ℝ} (h : s < t) : halfSign s t = -(1 / 2) := by
  simp [halfSign, sign_neg (sub_neg.mpr h)]

omit [CompleteSpace E] in
private theorem halfSign_integrable {a b s : ℝ} (has : a ≤ s) (hsb : s ≤ b)
    {h : ℝ → E} (hh : Continuous h) :
    Integrable (fun t => halfSign s t • h t) (volume.restrict (Icc a b)) ∧
      (∫ t, halfSign s t • h t ∂(volume.restrict (Icc a b))) =
        (∫ t in a..s, h t) - (1 / 2 : ℝ) • (∫ t in a..b, h t) := by
  let F (t : ℝ) := halfSign s t • h t
  have hLo : F =ᵐ[volume.restrict (Ioc a s)] fun t => (1 / 2 : ℝ) • h t := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne s)] with t ht hne
    change halfSign s t • h t = _
    rw [halfSign_eq_of_lt (lt_of_le_of_ne ht.2 hne)]
  have hHi : F =ᵐ[volume.restrict (Ioc s b)] fun t => -(1 / 2 : ℝ) • h t := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    change halfSign s t • h t = _
    rw [halfSign_eq_of_gt ht.1]
  have hLa := (intervalIntegrable_iff_integrableOn_Ioc_of_le has).mp (hh.intervalIntegrable (μ := volume) a s)
  have hHa := (intervalIntegrable_iff_integrableOn_Ioc_of_le hsb).mp (hh.intervalIntegrable (μ := volume) s b)
  have hL : IntegrableOn F (Ioc a s) volume := (hLa.smul (1 / 2 : ℝ)).congr (Filter.EventuallyEq.symm hLo)
  have hH : IntegrableOn F (Ioc s b) volume := (hHa.smul (-(1 / 2) : ℝ)).congr (Filter.EventuallyEq.symm hHi)
  have hUnion : Ioc a s ∪ Ioc s b = Ioc a b := Ioc_union_Ioc_eq_Ioc has hsb
  have hDisj : Disjoint (Ioc a s) (Ioc s b) := by
    apply Set.disjoint_left.mpr
    exact fun _ hx hy => (not_lt_of_ge hx.2) hy.1
  constructor
  · apply (integrableOn_Icc_iff_integrableOn_Ioc (by simp)).mpr
    rw [← hUnion]
    exact hL.union hH
  · change (∫ t in Icc a b, F t) = _
    rw [integral_Icc_eq_integral_Ioc, ← hUnion, setIntegral_union hDisj measurableSet_Ioc hL hH]
    rw [integral_congr_ae hLo, integral_congr_ae hHi, integral_smul, integral_smul,
      ← intervalIntegral.integral_of_le has, ← intervalIntegral.integral_of_le hsb,
      ← intervalIntegral.integral_add_adjacent_intervals (hh.intervalIntegrable (μ := volume) a s)
        (hh.intervalIntegrable (μ := volume) s b)]
    module

/-- The sign Green kernel for a first-order system includes the inverse of the
leading coefficient on the forcing side. -/
def fundamentalSignGreenKernel (X A₁ : ℝ → E ≃L[ℝ] E) : GreenKernel ℝ ℝ E E :=
  fun s t => halfSign s t • ((X s : E →L[ℝ] E).comp
    (((X t).symm : E →L[ℝ] E).comp ((A₁ t).symm : E →L[ℝ] E)))

/-- Variation of constants in fundamental coordinates, with the constant
chosen by the sign kernel. -/
def fundamentalSignGreenSolution (X A₁ : ℝ → E ≃L[ℝ] E) (a b : ℝ) (y : ℝ → E) (s : ℝ) : E :=
  X s ((∫ t in a..s, (X t).symm ((A₁ t).symm (y t))) -
    (1 / 2 : ℝ) • (∫ t in a..b, (X t).symm ((A₁ t).symm (y t))))

/-- **Exercise 30(f)** of [benIsrael2003generalized], Chapter 9.
The sign kernel represents variation of constants for a continuous
forcing in fundamental coordinates. The inverse of the leading coefficient
gives the original differential expression its prescribed right-hand side. -/
theorem exercise_9_30_signGreen_classical (X A₁ : ℝ → E ≃L[ℝ] E)
    (A₀ X' : ℝ → E →L[ℝ] E) (a b : ℝ) (y : ℝ → E)
    (hh : Continuous (fun t => (X t).symm ((A₁ t).symm (y t))))
    (hX : ∀ s ∈ Icc a b, HasDerivAt (fun t => (X t : E →L[ℝ] E)) (X' s) s)
    (hHom : ∀ s ∈ Icc a b,
      (A₁ s : E →L[ℝ] E).comp (X' s) + (A₀ s).comp (X s : E →L[ℝ] E) = 0)
    (s : ℝ) (hs : s ∈ Icc a b) :
    Integrable (fun t => fundamentalSignGreenKernel X A₁ s t (y t)) (volume.restrict (Icc a b)) ∧
    greenIntegral (fundamentalSignGreenKernel X A₁) (volume.restrict (Icc a b)) y s =
      fundamentalSignGreenSolution X A₁ a b y s ∧
    differentialExpression (fun t => (A₁ t : E →L[ℝ] E)) A₀
      (fundamentalSignGreenSolution X A₁ a b y) s = y s := by
  let h (t : ℝ) := (X t).symm ((A₁ t).symm (y t))
  let u (s : ℝ) := (∫ t in a..s, h t) - (1 / 2 : ℝ) • (∫ t in a..b, h t)
  obtain ⟨hi, he⟩ := halfSign_integrable hs.1 hs.2 hh
  have hu : HasDerivAt u (h s) s := by
    exact (intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable (μ := volume) a s)
      hh.stronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt).sub_const _
  have hd := (hX s hs).clm_apply hu
  have hK (t : ℝ) :
      fundamentalSignGreenKernel X A₁ s t (y t) = X s (halfSign s t • h t) := by
    simp only [fundamentalSignGreenKernel, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, map_smul, h]
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hK]
    exact (X s : E →L[ℝ] E).integrable_comp hi
  · rw [greenIntegral]
    simp_rw [hK]
    change (∫ t in Icc a b, (X s : E →L[ℝ] E) (halfSign s t • h t)) =
      (X s : E →L[ℝ] E) (u s)
    rw [(X s : E →L[ℝ] E).integral_comp_comm hi]
    exact congrArg (X s : E →L[ℝ] E) he
  · rw [differentialExpression]
    change A₁ s (deriv (fun t => X t (u t)) s) + A₀ s (X s (u s)) = y s
    have hd' : deriv (fun t => X t (u t)) s = X' s (u s) + X s (h s) := hd.deriv
    rw [hd', map_add]
    have hz : A₁ s (X' s (u s)) + A₀ s (X s (u s)) = 0 :=
      DFunLike.congr_fun (hHom s hs) (u s)
    have hF : A₁ s (X s (h s)) = y s := by simp [h]
    rw [hF]
    rw [add_right_comm, hz, zero_add]

end SignGreen

section SignBoundaryCorrection

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The boundary residual of a homogeneous solution, as a map of the
fundamental coefficient. -/
def fundamentalBoundaryMap (X : ℝ → E ≃L[ℝ] E) (a b : ℝ) (M : E × E →L[ℝ] F) :
    E →L[ℝ] F :=
  M.comp ((X a : E →L[ℝ] E).prod (X b : E →L[ℝ] E))

/-- The coefficient in the sign-kernel correction when the boundary values are
ordered as the left endpoint followed by the right endpoint. -/
def fundamentalSignBoundaryCorrection (X : ℝ → E ≃L[ℝ] E) (a b : ℝ)
    (M : E × E →L[ℝ] F) (J : F →L[ℝ] E) : E →L[ℝ] E :=
  J.comp (M.comp ((X a : E →L[ℝ] E).prod (-(X b : E →L[ℝ] E))))

/-- The corrected sign kernel for a system with a compatible boundary
residual. The row added to the sign kernel is homogeneous in its output
variable. -/
def fundamentalBoundaryGreenKernel (X A₁ : ℝ → E ≃L[ℝ] E) (a b : ℝ)
    (M : E × E →L[ℝ] F) (J : F →L[ℝ] E) : GreenKernel ℝ ℝ E E :=
  fun s t =>
    fundamentalSignGreenKernel X A₁ s t +
      (1 / 2 : ℝ) • (X s : E →L[ℝ] E).comp
        ((fundamentalSignBoundaryCorrection X a b M J).comp
          (((X t).symm : E →L[ℝ] E).comp ((A₁ t).symm : E →L[ℝ] E)))

/-- Variation of constants with the boundary residual removed by a homogeneous
solution. -/
def fundamentalBoundaryGreenSolution (X A₁ : ℝ → E ≃L[ℝ] E) (a b : ℝ)
    (M : E × E →L[ℝ] F) (J : F →L[ℝ] E) (y : ℝ → E) (s : ℝ) : E :=
  let u := fundamentalSignGreenSolution X A₁ a b y
  u s - X s (J (M (u a, u b)))

/-- **Exercise 30(g)** of [benIsrael2003generalized], Chapter 9, for continuous
fundamental forcing. The corrected integral solves the differential system
and the homogeneous endpoint condition when the boundary residual is in the
range of the homogeneous boundary map. -/
theorem exercise_9_30_boundaryGreen_classical (X A₁ : ℝ → E ≃L[ℝ] E)
    (A₀ X' : ℝ → E →L[ℝ] E) (a b : ℝ) (y : ℝ → E)
    (hh : Continuous (fun t => (X t).symm ((A₁ t).symm (y t))))
    (hX : ∀ s ∈ Icc a b, HasDerivAt (fun t => (X t : E →L[ℝ] E)) (X' s) s)
    (hHom : ∀ s ∈ Icc a b,
      (A₁ s : E →L[ℝ] E).comp (X' s) + (A₀ s).comp (X s : E →L[ℝ] E) = 0)
    (M : E × E →L[ℝ] F) (J : F →L[ℝ] E)
    (hJ : (fundamentalBoundaryMap X a b M).comp (J.comp (fundamentalBoundaryMap X a b M)) =
      fundamentalBoundaryMap X a b M)
    (hr : ∃ c : E, fundamentalBoundaryMap X a b M c =
      M (fundamentalSignGreenSolution X A₁ a b y a, fundamentalSignGreenSolution X A₁ a b y b))
    (s : ℝ) (hs : s ∈ Icc a b) :
    Integrable (fun t => fundamentalBoundaryGreenKernel X A₁ a b M J s t (y t))
      (volume.restrict (Icc a b)) ∧
    greenIntegral (fundamentalBoundaryGreenKernel X A₁ a b M J)
      (volume.restrict (Icc a b)) y s = fundamentalBoundaryGreenSolution X A₁ a b M J y s ∧
    differentialExpression (fun t => (A₁ t : E →L[ℝ] E)) A₀
      (fundamentalBoundaryGreenSolution X A₁ a b M J y) s = y s ∧
    M (fundamentalBoundaryGreenSolution X A₁ a b M J y a,
      fundamentalBoundaryGreenSolution X A₁ a b M J y b) = 0 := by
  let h (t : ℝ) := (X t).symm ((A₁ t).symm (y t))
  let u := fundamentalSignGreenSolution X A₁ a b y
  let H := ∫ t in a..b, h t
  let z := J (M (u a, u b))
  let N := fundamentalSignBoundaryCorrection X a b M J
  let P := (1 / 2 : ℝ) • ((X s : E →L[ℝ] E).comp N)
  have hI : Integrable h (volume.restrict (Icc a b)) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (by simp)).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (hs.1.trans hs.2)).mp
        (hh.intervalIntegrable (μ := volume) a b))
  have hInt : (∫ t in Icc a b, h t) = H := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hs.1.trans hs.2)]
  have ha : u a = -(1 / 2 : ℝ) • X a H := by
    simp [u, H, h, fundamentalSignGreenSolution, neg_smul]
  have hb : u b = (1 / 2 : ℝ) • X b H := by
    change X b (H - (1 / 2 : ℝ) • H) = _
    rw [← map_smul]
    congr 1
    module
  have hz : -X s z = P H := by
    change -X s (J (M (u a, u b))) = (1 / 2 : ℝ) • X s (N H)
    rw [ha, hb]
    have he : (-(1 / 2 : ℝ) • X a H, (1 / 2 : ℝ) • X b H) =
        -(1 / 2 : ℝ) • (X a H, -X b H) := by
      ext <;> simp [neg_smul]
    rw [he, map_smul, map_smul, map_smul, neg_smul, neg_neg]
    rfl
  obtain ⟨hK, hrep, hdu⟩ := exercise_9_30_signGreen_classical X A₁ A₀ X' a b y hh hX hHom s hs
  have hSum (t : ℝ) : fundamentalBoundaryGreenKernel X A₁ a b M J s t (y t) =
      fundamentalSignGreenKernel X A₁ s t (y t) + P (h t) := rfl
  have hP := P.integrable_comp hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [hSum]
    exact hK.add hP
  · unfold greenIntegral
    simp_rw [hSum]
    rw [integral_add hK hP, P.integral_comp_comm hI, hInt, ← hz]
    change greenIntegral (fundamentalSignGreenKernel X A₁) (volume.restrict (Icc a b)) y s +
      -X s z = u s - X s z
    rw [hrep, sub_eq_add_neg]
  · let aux (t : ℝ) := (∫ r in a..t, h r) - (1 / 2 : ℝ) • H
    have haux : HasDerivAt aux (h s) s :=
      (intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable (μ := volume) a s)
        hh.stronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt).sub_const _
    have hderiv : HasDerivAt u (X' s (aux s) + X s (h s)) s :=
      (hX s hs).clm_apply haux
    have hcorr : HasDerivAt (fun t => X t z) (X' s z) s :=
      (hX s hs).clm_apply (hasDerivAt_const s z) |>.congr_deriv (by simp)
    have hd : deriv (fun t => u t - X t z) s = deriv u s - X' s z := by
      have hd' : deriv (fun t => u t - X t z) s =
          (X' s (aux s) + X s (h s)) - X' s z := (hderiv.sub hcorr).deriv
      rw [hd', hderiv.deriv]
    have hdz : A₁ s (X' s z) + A₀ s (X s z) = 0 := DFunLike.congr_fun (hHom s hs) z
    change A₁ s (deriv (fun t => u t - X t z) s) + A₀ s (u s - X s z) = y s
    rw [hd, map_sub, map_sub, sub_add_sub_comm, hdz, sub_zero]
    exact hdu
  · let B := fundamentalBoundaryMap X a b M
    let r := M (u a, u b)
    have hB : B z = r := by
      obtain ⟨c, hc⟩ := hr
      have he : B (J (B c)) = B c := DFunLike.congr_fun hJ c
      change B c = r at hc
      rwa [hc] at he
    change M ((u a, u b) - (X a z, X b z)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hB.symm

end SignBoundaryCorrection

section GradientResults

open MeasureTheory Set SobolevMultiIndex TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

section DirichletGradients

set_option maxHeartbeats 1200000
set_option autoImplicit false

private abbrev DirichletScalarSpace {n : ℕ} (region : Opens (EuclideanSpace ℝ (Fin n))) :=
  Lp ℝ 2 (volume.restrict (region : Set (EuclideanSpace ℝ (Fin n))))

private abbrev DirichletVectorSpace {n : ℕ} (region : Opens (EuclideanSpace ℝ (Fin n))) :=
  PiLp 2 fun _ : Fin n => DirichletScalarSpace region

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

private def weakGradientCLM : SobolevEuclidean N 1 2 Ω →L[ℝ] DirichletVectorSpace Ω := by
  let A : SobolevEuclidean N 1 2 Ω →ₗ[ℝ] DirichletVectorSpace Ω :=
    { toFun := fun u => grad u
      map_add' := grad_add
      map_smul' := grad_smul }
  refine A.mkContinuous 1 fun u => ?_
  change gradNorm u ≤ 1 * ‖u‖
  rw [one_mul]
  exact gradNorm_le_norm u

private def weakDirichletGradientGraphMap : SobolevEuclideanZero N 1 2 Ω →L[ℝ] DirichletScalarSpace Ω × DirichletVectorSpace Ω :=
  (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume).prod
    ((weakGradientCLM Ω).comp (SobolevEuclideanZero N 1 2 Ω).subtypeL)

private theorem weakDirichletGradientGraph_singleValued :
    ∀ p : DirichletScalarSpace Ω × DirichletVectorSpace Ω, p ∈ (weakDirichletGradientGraphMap Ω).range → p.1 = 0 → p.2 = 0 := by
  rintro p ⟨u, rfl⟩ hu
  have he : u = 0 := (SobolevMultiIndexZero.fnL_injective (F := ℝ)) (by
    change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u =
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume 0
    rw [map_zero]
    exact hu)
  rw [he, map_zero, Prod.snd_zero]

/-- **Exercise 27(a)** of [benIsrael2003generalized], Chapter 9.
The weak gradient with homogeneous Dirichlet trace, on the scalar and
vector-valued square-integrable spaces of an open Euclidean domain. -/
def weakDirichletGradient : DirichletScalarSpace Ω →ₗ.[ℝ] DirichletVectorSpace Ω :=
  (weakDirichletGradientGraphMap Ω).range.toLinearPMap

/-- The Dirichlet gradient graph consists of a zero-trace Sobolev function
and its vector of weak first derivatives. -/
theorem mem_weakDirichletGradient_graph_iff {u : DirichletScalarSpace Ω} {y : DirichletVectorSpace Ω} :
    (u, y) ∈ (weakDirichletGradient Ω).graph ↔
      ∃ x : SobolevEuclideanZero N 1 2 Ω, SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume x = u ∧ grad (x : SobolevEuclidean N 1 2 Ω) = y := by
  rw [weakDirichletGradient, Submodule.toLinearPMap_graph_eq _
    (weakDirichletGradientGraph_singleValued Ω)]
  change (∃ x : SobolevEuclideanZero N 1 2 Ω, (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume x, grad (x : SobolevEuclidean N 1 2 Ω)) = (u, y)) ↔ _
  simp only [Prod.mk.injEq]

/-- The Dirichlet gradient has dense domain in the underlying $L^2$ space. -/
theorem dense_weakDirichletGradient_domain : Dense ((weakDirichletGradient Ω).domain : Set (DirichletScalarSpace Ω)) := by
  apply (SobolevEuclideanZero.denseRange_fnL (Ω := Ω)).mono
  rintro u ⟨x, rfl⟩
  exact (weakDirichletGradient Ω).mem_domain_of_mem_graph
    ((mem_weakDirichletGradient_graph_iff Ω).mpr ⟨x, rfl, rfl⟩)

/-- Closedness of the first-order Sobolev graph gives a closed Dirichlet
gradient on the ambient $L^2$ space. -/
theorem isClosed_weakDirichletGradient : (weakDirichletGradient Ω).IsClosed := by
  let A := weakDirichletGradientGraphMap Ω
  have hbound (x : SobolevEuclideanZero N 1 2 Ω) : ‖x‖ ≤ (2 : ℝ) * ‖A x‖ := by
    change ‖(x : SobolevEuclidean N 1 2 Ω)‖ ≤ _
    let f := ‖weakDeriv (x : SobolevEuclidean N 1 2 Ω) 0‖
    let g := gradNorm (x : SobolevEuclidean N 1 2 Ω)
    have he : ‖(x : SobolevEuclidean N 1 2 Ω)‖ = Real.sqrt (f ^ 2 + g ^ 2) := by
      rw [norm_eq_gradNorm (by norm_num : (2 : ℝ≥0∞) ≠ ∞), Real.sqrt_eq_rpow]
      norm_num [f, g]
    have hA : ‖A x‖ = max f g := Prod.norm_def _
    rw [he, hA]
    have hf : 0 ≤ f := norm_nonneg _
    have hg : 0 ≤ g := norm_nonneg _
    have hfg : Real.sqrt (f ^ 2 + g ^ 2) ≤ f + g := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity, by nlinarith⟩
    exact hfg.trans (by linarith [le_max_left f g, le_max_right f g])
  have ht : AntilipschitzWith 2 A := A.antilipschitz_of_bound hbound
  change IsClosed ((weakDirichletGradient Ω).graph : Set (DirichletScalarSpace Ω × DirichletVectorSpace Ω))
  rw [weakDirichletGradient, Submodule.toLinearPMap_graph_eq _
    (weakDirichletGradientGraph_singleValued Ω)]
  exact ht.isClosed_range A.uniformContinuous

/-- Square-integrable weak negative divergence, tested against the Sobolev
lifts of compactly supported smooth functions. -/
def IsWeakNegativeDivergence (y : DirichletVectorSpace Ω) (g : DirichletScalarSpace Ω) : Prop :=
    ∀ φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      ⟪grad φ, y⟫_ℝ = ⟪fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume φ, g⟫_ℝ

private theorem weakNegativeDivergence_iff_forall (y : DirichletVectorSpace Ω) (g : DirichletScalarSpace Ω) :
    IsWeakNegativeDivergence Ω y g ↔
      ∀ x : SobolevEuclideanZero N 1 2 Ω, ⟪grad (x : SobolevEuclidean N 1 2 Ω), y⟫_ℝ = ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume x, g⟫_ℝ := by
  constructor
  · intro hy x
    let F := (innerSL ℝ y).comp (weakGradientCLM Ω)
    let G := (innerSL ℝ g).comp (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)
    have hmatch : ∀ φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume, F φ = G φ := by
      intro φ hφ
      change ⟪y, grad φ⟫_ℝ = ⟪g, fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ
      rw [← real_inner_comm y (grad φ), ← real_inner_comm g (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume φ)]
      exact hy φ hφ
    have he := SobolevEuclideanZero.ext_on_testFunctions hmatch x.property
    change ⟪y, grad (x : SobolevEuclidean N 1 2 Ω)⟫_ℝ = ⟪g, fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (x : SobolevEuclidean N 1 2 Ω)⟫_ℝ at he
    exact (real_inner_comm _ _).trans (he.trans (real_inner_comm _ _))
  · intro h φ hφ
    have hmem : φ ∈ SobolevEuclideanZero N 1 2 Ω := subset_closure hφ
    exact h ⟨φ, hmem⟩

/-- **Exercise 27(b)** of [benIsrael2003generalized], Chapter 9.
The adjoint graph is the maximal square-integrable weak negative divergence. -/
theorem mem_weakDirichletGradient_adjoint_graph_iff {y : DirichletVectorSpace Ω} {g : DirichletScalarSpace Ω} :
    (y, g) ∈ (weakDirichletGradient Ω).adjoint.graph ↔ IsWeakNegativeDivergence Ω y g := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_weakDirichletGradient_domain Ω),
    Submodule.mem_adjoint_iff, weakNegativeDivergence_iff_forall]
  constructor
  · intro h x
    apply sub_eq_zero.mp
    apply h
    exact (mem_weakDirichletGradient_graph_iff Ω).mpr ⟨x, rfl, rfl⟩
  · intro h u v huv
    obtain ⟨x, rfl, rfl⟩ := (mem_weakDirichletGradient_graph_iff Ω).mp huv
    exact sub_eq_zero.mpr (h x)

private theorem mem_partialComp_graph_iff {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (A : E →ₗ.[ℝ] F) (B : F →ₗ.[ℝ] G) {x : E} {z : G} :
    (x, z) ∈ (partialComp B A).graph ↔ ∃ y, (x, y) ∈ A.graph ∧ (y, z) ∈ B.graph := by
  constructor
  · intro h
    obtain ⟨u, rfl, hu⟩ := (partialComp B A).mem_graph_iff.mp h
    obtain ⟨hx, hy⟩ := (partialComp_mem_domain B A (u : E)).mp u.property
    exact ⟨A ⟨u, hx⟩, A.mem_graph ⟨u, hx⟩, B.mem_graph_iff.mpr ⟨⟨_, hy⟩, rfl, hu⟩⟩
  · rintro ⟨y, ha, hb⟩
    obtain ⟨u, rfl, rfl⟩ := A.mem_graph_iff.mp ha
    obtain ⟨v, hv, hvz⟩ := B.mem_graph_iff.mp hb
    change (v : F) = A u at hv
    let hy : A u ∈ B.domain := hv ▸ v.property
    exact (partialComp B A).mem_graph_iff.mpr
      ⟨⟨u, (partialComp_mem_domain B A _).mpr ⟨u.property, hy⟩⟩, rfl,
        (partialComp_apply B A _ u.property hy).trans (by
          have he : (⟨A u, hy⟩ : B.domain) = v := Subtype.ext hv.symm
          rwa [he])⟩

private theorem weakNegativeDivergence_grad_iff (x : SobolevEuclideanZero N 1 2 Ω) (g : DirichletScalarSpace Ω) :
    IsWeakNegativeDivergence Ω (grad (x : SobolevEuclidean N 1 2 Ω)) g ↔
      ∀ φ ∈ (SobolevEuclideanZero N 1 2 Ω), Elliptic.dirichletForm Ω (x : SobolevEuclidean N 1 2 Ω) φ = Elliptic.load Ω g φ := by
  have hForm (φ : SobolevEuclidean N 1 2 Ω) : Elliptic.dirichletForm Ω (x : SobolevEuclidean N 1 2 Ω) φ =
      ⟪grad φ, grad (x : SobolevEuclidean N 1 2 Ω)⟫_ℝ := by
    rw [Elliptic.dirichletForm_apply_inner, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => real_inner_comm
      (weakDeriv φ (MultiIndexLE.single i)) (weakDeriv (x : SobolevEuclidean N 1 2 Ω) (MultiIndexLE.single i))
  rw [weakNegativeDivergence_iff_forall]
  constructor
  · intro h φ hφ
    rw [hForm, Elliptic.load_apply_inner, real_inner_comm (weakDeriv _ 0) g]
    exact h ⟨φ, hφ⟩
  · intro h φ
    have hf := h φ φ.property
    rw [hForm, Elliptic.load_apply_inner, real_inner_comm (weakDeriv _ 0) g] at hf
    exact hf

/-- **Exercise 27(c)** of [benIsrael2003generalized], Chapter 9.
The Gram operator of the closed gradient is exactly the negative Dirichlet
Laplacian, including equality of the differential operator domains. -/
theorem weakDirichletGradient_gram :
    partialComp (weakDirichletGradient Ω).adjoint (weakDirichletGradient Ω) =
      dirichletLaplacian Ω := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  obtain ⟨u, g⟩ := p
  rw [mem_partialComp_graph_iff]
  constructor
  · rintro ⟨y, hy, hg⟩
    obtain ⟨x, hx, rfl⟩ := (mem_weakDirichletGradient_graph_iff Ω).mp hy
    have hr := (weakNegativeDivergence_grad_iff Ω x g).mp
      ((mem_weakDirichletGradient_adjoint_graph_iff Ω).mp hg)
    have hd : u ∈ (dirichletLaplacian Ω).domain :=
      ⟨x, x.property, hx, g, hr⟩
    exact (dirichletLaplacian Ω).mem_graph_iff.mpr
      ⟨⟨u, hd⟩, rfl, dirichletLaplacian_apply_unique ⟨u, hd⟩ x.property hx hr⟩
  · intro h
    obtain ⟨v, rfl, rfl⟩ := (dirichletLaplacian Ω).mem_graph_iff.mp h
    obtain ⟨x, hx, he⟩ := dirichletLaplacian_exists_lift v
    refine ⟨grad x, (mem_weakDirichletGradient_graph_iff Ω).mpr ⟨⟨x, hx⟩, he, rfl⟩, ?_⟩
    apply (mem_weakDirichletGradient_adjoint_graph_iff Ω).mpr
    apply (weakNegativeDivergence_grad_iff Ω ⟨x, hx⟩ _).mpr
    intro φ hφ
    rw [Elliptic.load_apply_inner]
    exact (dirichletLaplacian_inner_eq_dirichletForm v hx he hφ).symm

end DirichletGradients

end GradientResults

section SineKernelResults

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

section ProductSine

private theorem memLp_prod_real {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {u v : X → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    MemLp (fun p : X × X => u p.1 * v p.2) 2 (μ.prod μ) := by
  apply (memLp_two_iff_integrable_sq
    (hu.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd)).mpr
  simpa only [Pi.mul_apply, mul_pow] using hu.integrable_sq.mul_prod hv.integrable_sq

private def realLpTensor {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (u v : Lp ℝ 2 μ) : Lp ℝ 2 (μ.prod μ) :=
  (memLp_prod_real (Lp.memLp u) (Lp.memLp v)).toLp _

private theorem realLpTensor_coeFn {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (u v : Lp ℝ 2 μ) :
    (fun p => realLpTensor u v p) =ᵐ[μ.prod μ] fun p => u p.1 * v p.2 :=
  MemLp.coeFn_toLp (memLp_prod_real (Lp.memLp u) (Lp.memLp v))

private theorem realLpTensor_inner {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (u v w z : Lp ℝ 2 μ) :
    ⟪realLpTensor u v, realLpTensor w z⟫_ℝ = ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ := by
  simp only [L2.inner_eq_integral_mul]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [realLpTensor_coeFn u v, realLpTensor_coeFn w z] with p hp hq
  change realLpTensor u v p * realLpTensor w z p = (u p.1 * w p.1) * (v p.2 * z p.2)
  rw [hp, hq]
  ring

private theorem realLpTensor_orthonormal {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    [SFinite μ] {e : ι → Lp ℝ 2 μ} (he : Orthonormal ℝ e) :
    Orthonormal ℝ (fun p : ι × ι => realLpTensor (e p.1) (e p.2)) := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  rw [realLpTensor_inner, orthonormal_iff_ite.mp he, orthonormal_iff_ite.mp he]
  by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2 <;> simp [Prod.ext_iff, h₁, h₂]

private theorem row_integral_tensor_inner {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (f : Lp ℝ 2 (μ.prod μ)) (u v : Lp ℝ 2 μ) :
    ⟪u, IntegralOperator.l2KernelCLM (Lp.memLp f) v⟫_ℝ =
      ⟪realLpTensor u v, f⟫_ℝ := by
  have hInt := IntegralOperator.integrable_kernel_mul_prod (Lp.memLp f) (Lp.memLp v) (Lp.memLp u)
  simp only [L2.inner_eq_integral_mul]
  calc
    (∫ s, u s * IntegralOperator.l2KernelCLM (Lp.memLp f) v s ∂μ) =
        ∫ s, ∫ t, f (s, t) * (v t * u s) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [IntegralOperator.l2KernelCLM_apply_ae (Lp.memLp f) v] with s hs
      rw [hs, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = ∫ p : X × X, f p * (v p.2 * u p.1) ∂(μ.prod μ) := (integral_prod _ hInt).symm
    _ = ∫ p, realLpTensor u v p * f p ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [realLpTensor_coeFn u v] with p hp
      rw [hp]
      ring

private theorem realLpTensor_complete {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    [SFinite μ] [Countable ι] (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    (Submodule.span ℝ (Set.range fun p : ι × ι => realLpTensor (b p.1) (b p.2)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hfs (i j : ι) : ⟪realLpTensor (b i) (b j), f⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hcol (j : ι) : IntegralOperator.l2KernelCLM (Lp.memLp f) (b j) = 0 := by
    apply b.repr.injective
    ext i
    rw [map_zero, lp.coeFn_zero, Pi.zero_apply, b.repr_apply_apply, row_integral_tensor_inner]
    exact hfs i j
  have hrow (j : ι) : ∀ᵐ s ∂μ, (∫ t, f (s, t) * b j t ∂μ) = 0 := by
    have hh := IntegralOperator.l2KernelCLM_apply_ae (Lp.memLp f) (b j)
    rw [hcol] at hh
    filter_upwards [hh, Lp.coeFn_zero ℝ 2 μ] with s hs hz
    exact hs.symm.trans hz
  have hae : ∀ᵐ s ∂μ, ∀ᵐ t ∂μ, f (s, t) = 0 := by
    filter_upwards [IntegralOperator.ae_memLp_row (Lp.memLp f), ae_all_iff.mpr hrow] with s hs ht
    let g := hs.toLp _
    have hg : (fun t => g t) =ᵐ[μ] fun t => f (s, t) := MemLp.coeFn_toLp hs
    have h0 : g = 0 := by
      apply b.repr.injective
      ext j
      rw [map_zero, lp.coeFn_zero, Pi.zero_apply, b.repr_apply_apply, real_inner_comm g,
        L2.inner_eq_integral_mul]
      refine (integral_congr_ae (show (fun t => g t * b j t) =ᵐ[μ]
        fun t => f (s, t) * b j t from ?_)).trans (ht j)
      filter_upwards [hg] with t h
      rw [h]
    rw [h0] at hg
    filter_upwards [hg, Lp.coeFn_zero ℝ 2 μ] with t h hz
    exact h.symm.trans hz
  let fm := (Lp.aestronglyMeasurable f).mk f
  have hfM : Measurable fm := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.measurable
  have haf : (fun p => f p) =ᵐ[μ.prod μ] fm := (Lp.aestronglyMeasurable f).ae_eq_mk
  have hf0 : fm =ᵐ[μ.prod μ] (0 : X × X → ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hfM measurable_const)).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod haf, hae] with s hs hs0
    filter_upwards [hs, hs0] with t ht h0
    exact ht.symm.trans h0
  exact Lp.ext ((haf.trans hf0).trans (Lp.coeFn_zero ℝ 2 (μ.prod μ)).symm)

/-- The product of the two normalized sine systems is a Hilbert basis of the
square-integrable functions on $[0,\pi]^2$. Its frequencies start at one. -/
def squareSineBasis : HilbertBasis (ℕ × ℕ) ℝ (Lp ℝ 2 (halfRangeMeasure.prod halfRangeMeasure)) :=
  HilbertBasis.mkOfOrthogonalEqBot (realLpTensor_orthonormal sinBasis.orthonormal)
    (realLpTensor_complete sinBasis)

/-- The sine basis functions on the square have the product normalization
$2/\pi$. -/
theorem squareSineBasis_apply_ae (j : ℕ × ℕ) :
    (fun p => squareSineBasis j p) =ᵐ[halfRangeMeasure.prod halfRangeMeasure]
      fun p => (2 / Real.pi) * Real.sin ((j.1 + 1) * p.1.val) *
        Real.sin ((j.2 + 1) * p.2.val) := by
  unfold squareSineBasis
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot]
  have he₁ := (Measure.quasiMeasurePreserving_fst (ν := halfRangeMeasure)).ae (coeFn_sinLp j.1)
  have he₂ := (Measure.quasiMeasurePreserving_snd (μ := halfRangeMeasure)).ae (coeFn_sinLp j.2)
  filter_upwards [realLpTensor_coeFn (sinBasis j.1) (sinBasis j.2), he₁, he₂] with p hp h₁ h₂
  rw [hp, coe_sinBasis]
  change sinLp j.1 p.1 = sinFun j.1 p.1 at h₁
  change sinLp j.2 p.2 = sinFun j.2 p.2 at h₂
  rw [h₁, h₂]
  change (Real.sqrt (2 / Real.pi) * Real.sin ((j.1 + 1) * p.1.val)) *
    (Real.sqrt (2 / Real.pi) * Real.sin ((j.2 + 1) * p.2.val)) = _
  calc
    _ = (Real.sqrt (2 / Real.pi) * Real.sqrt (2 / Real.pi)) *
        Real.sin ((j.1 + 1) * p.1.val) * Real.sin ((j.2 + 1) * p.2.val) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (by positivity)]

local notation "μ□" => Measure.prod halfRangeMeasure halfRangeMeasure

/-- The positive Dirichlet frequency of the double sine mode. -/
def squareSineEigenvalue (j : ℕ × ℕ) : ℝ := (j.1 + 1 : ℝ) ^ 2 + (j.2 + 1 : ℝ) ^ 2

private theorem squareSineEigenvalue_pos (j : ℕ × ℕ) : 0 < squareSineEigenvalue j := by
  unfold squareSineEigenvalue
  positivity

private theorem summable_sq_inv_squareSineEigenvalue :
    Summable (fun j : ℕ × ℕ => (squareSineEigenvalue j)⁻¹ ^ 2) := by
  let a (n : ℕ) : ℝ := ((n + 1 : ℝ) ^ 2)⁻¹
  have hsum : Summable a := by
    simpa only [a, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹) 1).mpr
        (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ)))
  have ha (n : ℕ) : 0 ≤ a n := by positivity
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hsum.mul_of_nonneg hsum ha ha)
  intro j
  let u : ℝ := (j.1 + 1 : ℝ) ^ 2
  let v : ℝ := (j.2 + 1 : ℝ) ^ 2
  have hu : 0 < u := by positivity
  have hv : 0 < v := by positivity
  have huv : 0 < u + v := add_pos hu hv
  change (u + v)⁻¹ ^ 2 ≤ u⁻¹ * v⁻¹
  rw [← mul_inv, inv_pow]
  apply inv_anti₀ (mul_pos hu hv)
  nlinarith [sq_nonneg (u - v)]

private theorem squareSineGreenModes_orthonormal :
    Orthonormal ℝ (fun j : ℕ × ℕ => realLpTensor (squareSineBasis j) (squareSineBasis j)) := by
  classical
  rw [orthonormal_iff_ite]
  intro j k
  rw [realLpTensor_inner, orthonormal_iff_ite.mp squareSineBasis.orthonormal]
  split_ifs <;> norm_num

/-- **Exercise 27(d)** of [benIsrael2003generalized], Chapter 9.
The Green series on the square converges in $L^2$ of the product of the
two squares. Each term is the product of two normalized sine modes
divided by the positive eigenvalue. -/
def squareSineGreenKernel : Lp ℝ 2 (μ□.prod μ□) :=
  ∑' j : ℕ × ℕ, (squareSineEigenvalue j)⁻¹ • realLpTensor (squareSineBasis j) (squareSineBasis j)

/-- The double sine kernel series converges unconditionally in the product
$L^2$ norm. -/
theorem hasSum_squareSineGreenKernel :
    HasSum (fun j : ℕ × ℕ => (squareSineEigenvalue j)⁻¹ •
      realLpTensor (squareSineBasis j) (squareSineBasis j)) squareSineGreenKernel := by
  exact ((Orthonormal.summable_smul_iff squareSineGreenModes_orthonormal
    (fun j => (squareSineEigenvalue j)⁻¹)).mpr summable_sq_inv_squareSineEigenvalue).hasSum

/-- The integral operator of the sine Green series divides the coefficient
at each frequency by the corresponding positive eigenvalue. -/
theorem squareSineGreenKernel_action_repr (f : Lp ℝ 2 μ□) (i : ℕ × ℕ) :
    squareSineBasis.repr (IntegralOperator.l2KernelCLM (Lp.memLp squareSineGreenKernel) f) i =
      (squareSineEigenvalue i)⁻¹ * squareSineBasis.repr f i := by
  classical
  rw [squareSineBasis.repr_apply_apply, row_integral_tensor_inner,
    squareSineBasis.repr_apply_apply]
  have h := hasSum_squareSineGreenKernel.mapL (innerSL ℝ (realLpTensor (squareSineBasis i) f))
  have h' : HasSum (fun j : ℕ × ℕ => if j = i then
      (squareSineEigenvalue i)⁻¹ * ⟪squareSineBasis i, f⟫_ℝ else 0)
      ⟪realLpTensor (squareSineBasis i) f, squareSineGreenKernel⟫_ℝ := by
    apply h.congr_fun
    intro j
    simp only [innerSL_apply_apply, real_inner_smul_right, realLpTensor_inner]
    by_cases hji : j = i
    · subst j
      rw [ite_eq_left rfl, orthonormal_iff_ite.mp squareSineBasis.orthonormal, ite_eq_left rfl,
        one_mul, real_inner_comm (squareSineBasis i) f]
    · rw [ite_eq_right hji, orthonormal_iff_ite.mp squareSineBasis.orthonormal,
        ite_eq_right (Ne.symm hji), zero_mul, mul_zero]
  exact h'.unique (hasSum_ite_eq _ _)

end ProductSine

end SineKernelResults

section ScalarSobolevOperator

open Matrix

variable {n m : ℕ} {l r : ℝ}

local notation "H" => SobolevInterval (n + 1) l r
local notation "S" => IntervalL2 l r
local notation "μ" => volume.restrict (Ioo l r)

private def scalarCoefficientMultiplier (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r)) :
    S →L[ℝ] S :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 ⊤ 2).flip (hc.memLp_top_restrict_Ioo.toLp c)

private theorem scalarCoefficientMultiplier_apply_ae
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r)) (u : S) :
    scalarCoefficientMultiplier c hc u =ᵐ[μ] fun t => c t * u t := by
  have h := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) u (hc.memLp_top_restrict_Ioo.toLp c)
  filter_upwards [h, hc.memLp_top_restrict_Ioo.coeFn_toLp] with t ht htc
  simpa [scalarCoefficientMultiplier, htc, mul_comm] using ht

/-- The differential expression (49) on the order-\(n+1\) Sobolev space,
with coefficients represented as bounded multipliers on the interval. -/
def scalarSobolevExpression (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (c j) (Icc l r)) : H →L[ℝ] S :=
  ∑ j, (scalarCoefficientMultiplier (c j) (hc j)).comp (SobolevInterval.derivL (n + 1) l r j)

/-- The Sobolev expression acts almost everywhere as the coefficient-weighted sum of weak derivatives. -/
theorem scalarSobolevExpression_apply_ae (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (c j) (Icc l r)) (u : H) :
    scalarSobolevExpression c hc u =ᵐ[μ] fun t =>
      ∑ j, c j t * SobolevInterval.deriv u j t := by
  let f : Fin (n + 2) → S := fun j =>
    scalarCoefficientMultiplier (c j) (hc j) (SobolevInterval.deriv u j)
  have hsum (T : Finset (Fin (n + 2))) :
      (⇑(∑ j ∈ T, f j) : ℝ → ℝ) =ᵐ[μ] fun t => ∑ j ∈ T, c j t * SobolevInterval.deriv u j t := by
    classical
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero ..
    | @insert j T hj hT =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (f j) (∑ i ∈ T, f i), hT,
        scalarCoefficientMultiplier_apply_ae (c j) (hc j) (SobolevInterval.deriv u j)]
        with t ht hs hj'
      simp only [Pi.add_apply] at ht
      rw [ht, hs, hj']
  simpa only [scalarSobolevExpression, sum_apply,
    ContinuousLinearMap.comp_apply, SobolevInterval.derivL_apply, f] using hsum Finset.univ

private def scalarSobolevEval (hlr : l < r) (x : Icc l r) (j : Fin (n + 1)) :
    H →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp ((ContDiffMapIcc.derivCLM hlr.le n j).comp
    (SobolevIntervalLp.toContDiffMapIcc (p := 2) hlr))

/-- Endpoint values of the derivatives through order \(n\), in the order
of the two blocks in (50). -/
def scalarSobolevBoundaryTrace (hlr : l < r) : H →L[ℝ] (Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi
    (Sum.elim (scalarSobolevEval hlr ⟨l, left_mem_Icc.mpr hlr.le⟩)
      (scalarSobolevEval hlr ⟨r, right_mem_Icc.mpr hlr.le⟩))

/-- The boundary trace picks the appropriate endpoint of each derivative. -/
theorem scalarSobolevBoundaryTrace_apply (hlr : l < r) (u : H)
    (j : Fin (n + 1) ⊕ Fin (n + 1)) :
    scalarSobolevBoundaryTrace hlr u j =
      Sum.elim (fun k => SobolevIntervalLp.rep (SobolevIntervalLp.derivOne u k) l)
        (fun k => SobolevIntervalLp.rep (SobolevIntervalLp.derivOne u k) r) j := by
  cases j <;> simp only [scalarSobolevBoundaryTrace, ContinuousLinearMap.pi_apply,
    scalarSobolevEval, ContinuousLinearMap.comp_apply, Sum.elim_inl, Sum.elim_inr,
    ContinuousMap.evalCLM_apply, ContDiffMapIcc.derivCLM_apply,
    SobolevIntervalLp.deriv_toContDiffMapIcc]

/-- The Sobolev domain satisfying the homogeneous boundary matrix condition
(50). -/
def scalarSobolevBoundarySpace (hlr : l < r)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) : Submodule ℝ H :=
  ((LinearMap.toContinuousLinearMap M.mulVecLin).comp (scalarSobolevBoundaryTrace hlr)).ker

/-- A Sobolev function satisfies the homogeneous trace constraint exactly when its boundary residual is zero. -/
theorem mem_scalarSobolevBoundarySpace_iff (hlr : l < r)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) (u : H) :
    u ∈ scalarSobolevBoundarySpace hlr M ↔ M.mulVec (scalarSobolevBoundaryTrace hlr u) = 0 :=
  Iff.rfl

/-- The homogeneous boundary equations define a closed Sobolev subspace. -/
theorem isClosed_scalarSobolevBoundarySpace (hlr : l < r)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    IsClosed (scalarSobolevBoundarySpace hlr M : Set H) :=
  ((LinearMap.toContinuousLinearMap M.mulVecLin).comp (scalarSobolevBoundaryTrace hlr)).isClosed_ker

private def scalarSobolevGraphMap (A : H →L[ℝ] S) (W : Submodule ℝ H) : W →L[ℝ] S × S :=
  ((SobolevInterval.derivL (n + 1) l r 0).prod A).comp W.subtypeL

private theorem scalarSobolevGraph_singleValued (A : H →L[ℝ] S) (W : Submodule ℝ H) :
    ∀ p ∈ (scalarSobolevGraphMap A W).toLinearMap.range, p.1 = 0 → p.2 = 0 := by
  rintro p ⟨u, rfl⟩ hu
  have h₀ : SobolevInterval.deriv u.val 0 = SobolevInterval.deriv (0 : H) 0 := hu
  have he : u.val = 0 := SobolevMultiIndex.fnL_injective h₀
  change A u.val = 0
  rw [he, map_zero]

/-- The realization of the scalar differential expression on a designated
subspace of its Sobolev domain. -/
def scalarIntervalOperator (A : H →L[ℝ] S) (W : Submodule ℝ H) : S →ₗ.[ℝ] S :=
  (scalarSobolevGraphMap A W).toLinearMap.range.toLinearPMap

/-- The scalar operator graph records the function and image of a permitted Sobolev lift. -/
theorem mem_scalarIntervalOperator_graph_iff (A : H →L[ℝ] S) (W : Submodule ℝ H) {x y : S} :
    (x, y) ∈ (scalarIntervalOperator A W).graph ↔
      ∃ u : W, SobolevInterval.deriv u.val 0 = x ∧ A u.val = y := by
  rw [scalarIntervalOperator, Submodule.toLinearPMap_graph_eq _ (scalarSobolevGraph_singleValued A W)]
  change (∃ u : W, (SobolevInterval.deriv u.val 0, A u.val) = (x, y)) ↔ _
  simp only [Prod.mk.injEq]

/-- The unrestricted Sobolev realization of the scalar expression (49). -/
abbrev freeScalarIntervalOperator (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (c j) (Icc l r)) : S →ₗ.[ℝ] S :=
  scalarIntervalOperator (scalarSobolevExpression c hc) ⊤

/-- The scalar differential operator with the homogeneous endpoint
conditions of **Exercise 28** of [benIsrael2003generalized], Chapter 9. -/
abbrev constrainedScalarIntervalOperator (hlr : l < r) (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) : S →ₗ.[ℝ] S :=
  scalarIntervalOperator (scalarSobolevExpression c hc) (scalarSobolevBoundarySpace hlr M)

private theorem scalarSobolevGraph_domain_of_lift (A : H →L[ℝ] S) (W : Submodule ℝ H) (u : W) :
    SobolevInterval.deriv u.val 0 ∈ (scalarIntervalOperator A W).domain :=
  LinearPMap.mem_domain_of_mem_graph ((mem_scalarIntervalOperator_graph_iff A W).mpr ⟨u, rfl, rfl⟩)

/-- **Exercise 28(a)** of [benIsrael2003generalized], Chapter 9.
The homogeneous endpoint conditions contain all test functions in the
operator domain, which is dense in the Hilbert space. -/
theorem dense_constrainedScalarIntervalOperator (hlr : l < r) (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    Dense ((constrainedScalarIntervalOperator hlr c hc M).domain : Set S) := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨φ, hφ⟩ := exists_testFunction_norm_sub_toLp_le hlr x (half_pos hε)
  have hd : ContDiff ℝ (n + 1 : ℕ) (φ : ℝ → ℝ) := φ.contDiff.of_le (by simp)
  let v := ContDiffMapIcc.ofContDiff hlr.le hd
  let u := ContDiffMapIcc.toSobolevIntervalLp 2 hlr.le hlr (n + 1) v
  have hfn : SobolevInterval.deriv u 0 = φ.toLp₂ := by
    apply Lp.ext
    have h := ContDiffMapIcc.fn_toSobolevIntervalLp_ae_eq (p := 2) hlr.le hlr v
    filter_upwards [h, φ.coeFn_toLp₂, ae_restrict_mem measurableSet_Ioo] with t ht hφt htI
    rw [hφt]
    change u.fn t = φ t
    exact ht.trans ((v.extend_of_mem (Ioo_subset_Icc_self htI)).trans rfl)
  have hder (j : Fin (n + 1)) (t : Icc l r) (ht : (t : ℝ) ∉ Ioo l r) :
      SobolevIntervalLp.rep (SobolevIntervalLp.derivOne u j) t = 0 := by
    rw [← SobolevIntervalLp.deriv_toContDiffMapIcc (p := 2) hlr u j t,
      ContDiffMapIcc.deriv_toContDiffMapIcc_toSobolevIntervalLp, ContDiffMapIcc.deriv_ofContDiff]
    exact (φ.iteratedFDerivApply j fun _ ↦ 1).eq_zero_of_notMem ht
  have hu : u ∈ scalarSobolevBoundarySpace hlr M := by
    rw [mem_scalarSobolevBoundarySpace_iff]
    have hzero : scalarSobolevBoundaryTrace hlr u = 0 := by
      funext j
      rw [scalarSobolevBoundaryTrace_apply]
      cases j with
      | inl j => exact hder j ⟨l, left_mem_Icc.mpr hlr.le⟩ (fun h => lt_irrefl _ h.1)
      | inr j => exact hder j ⟨r, right_mem_Icc.mpr hlr.le⟩ (fun h => lt_irrefl _ h.2)
    rw [hzero, Matrix.mulVec_zero]
  refine ⟨φ.toLp₂, ?_, hfn ▸ scalarSobolevGraph_domain_of_lift _ _ ⟨u, hu⟩⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  exact hφ.trans_lt (half_lt_self hε)

end ScalarSobolevOperator

section ScalarSobolevOperatorClosed

variable {n m : ℕ} {l r : ℝ}

local notation "H" => SobolevInterval (n + 1) l r
local notation "S" => IntervalL2 l r
local notation "μ" => volume.restrict (Ioo l r)
local notation "last" => Fin.last (n + 1)

private theorem inverse_leading_mul_scalarSobolevExpression
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) (u : H) :
    let invLead := scalarCoefficientMultiplier (fun t => (c last t)⁻¹) ((hc last).inv₀ hnz)
    let M := fun j : Fin (n + 1) => scalarCoefficientMultiplier
      (fun t => (c last t)⁻¹ * c j.castSucc t) (((hc last).inv₀ hnz).mul (hc j.castSucc))
    invLead (scalarSobolevExpression c hc u) =
      SobolevInterval.deriv u last + ∑ j, M j (SobolevInterval.deriv u j.castSucc) := by
  dsimp only
  let f := fun t => (c last t)⁻¹
  let hf := (hc last).inv₀ hnz
  let lower : Fin (n + 2) → ℝ → ℝ := fun j t => f t * c j t
  let hlower : ∀ j, ContinuousOn (lower j) (Icc l r) := fun j => hf.mul (hc j)
  have hfull :
      scalarCoefficientMultiplier f hf (scalarSobolevExpression c hc u) =
        scalarSobolevExpression lower hlower u := by
    apply Lp.ext
    filter_upwards [scalarCoefficientMultiplier_apply_ae f hf (scalarSobolevExpression c hc u),
      scalarSobolevExpression_apply_ae c hc u, scalarSobolevExpression_apply_ae lower hlower u]
      with t h₁ h₂ h₃
    rw [h₁, h₂, h₃, Finset.mul_sum]
    simp only [lower, mul_assoc]
  rw [hfull, scalarSobolevExpression, Fin.sum_univ_castSucc, add_apply,
    sum_apply, ContinuousLinearMap.comp_apply, SobolevInterval.derivL_apply,
    add_comm]
  congr 1
  apply Lp.ext
  filter_upwards [scalarCoefficientMultiplier_apply_ae (lower last) (hlower last)
    (SobolevInterval.deriv u last), ae_restrict_mem measurableSet_Ioo] with t ht htI
  rw [ht]
  change (c last t)⁻¹ * c last t * SobolevInterval.deriv u last t = _
  rw [inv_mul_cancel₀ (hnz t (Ioo_subset_Icc_self htI)), one_mul]

private theorem scalarSobolev_graph_estimate
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H,
      ‖u‖ ≤ C * max ‖SobolevInterval.deriv u 0‖ ‖scalarSobolevExpression c hc u‖ := by
  let A := scalarSobolevExpression c hc
  let B := scalarCoefficientMultiplier (fun t => (c last t)⁻¹) ((hc last).inv₀ hnz)
  let M := fun j : Fin (n + 1) => scalarCoefficientMultiplier
    (fun t => (c last t)⁻¹ * c j.castSucc t) (((hc last).inv₀ hnz).mul (hc j.castSucc))
  let K : ℝ := 1 + ∑ j, ‖M j‖
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let ε : ℝ := (2 * K)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hI : (Ioo l r).OrdConnected := ordConnected_Ioo
  have hcomponent (j : Fin (n + 1)) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H,
        ‖SobolevInterval.deriv u j.castSucc‖ ≤
          ε * ‖SobolevInterval.deriv u last‖ + C * ‖SobolevInterval.deriv u 0‖ := by
    by_cases hj : j.castSucc = (0 : Fin (n + 2))
    · refine ⟨1, zero_le_one, ?_⟩
      intro u
      rw [hj, one_mul]
      exact le_add_of_nonneg_left (mul_nonneg hε.le (norm_nonneg _))
    · exact SobolevIntervalLp.eLpNorm_deriv_le_mul_add hI j.castSucc hj (Fin.castSucc_ne_last j) hε
  choose C hC hcomponent using hcomponent
  let D : ℝ := ∑ j, ‖M j‖ * C j
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hC j)
  have hhalf : ε * ∑ j, ‖M j‖ ≤ 1 / 2 := by
    calc
      ε * ∑ j, ‖M j‖ ≤ ε * K :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hε.le
      _ = 1 / 2 := by dsimp [ε]; field_simp [hK.ne']
  obtain ⟨E, hE, hnorm⟩ := SobolevIntervalLp.exists_norm_le_mul_norm_deriv_add (p := 2) (I := TopologicalSpace.Opens.Ioo l r) hI (n + 1)
  refine ⟨E * (1 + 2 * ‖B‖ + 2 * D), by positivity, fun u => ?_⟩
  let x := SobolevInterval.deriv u 0
  let y := A u
  let z := SobolevInterval.deriv u last
  have hlow : ‖∑ j, M j (SobolevInterval.deriv u j.castSucc)‖ ≤ ‖z‖ / 2 + D * ‖x‖ := by
    calc
      ‖∑ j, M j (SobolevInterval.deriv u j.castSucc)‖ ≤ ∑ j, ‖M j (SobolevInterval.deriv u j.castSucc)‖ :=
        norm_sum_le ..
      _ ≤ ∑ j, ‖M j‖ * (ε * ‖z‖ + C j * ‖x‖) :=
        Finset.sum_le_sum fun j _ => (ContinuousLinearMap.le_opNorm (M j) _).trans
          (mul_le_mul_of_nonneg_left (hcomponent j u) (norm_nonneg _))
      _ = ∑ j, ((ε * ‖M j‖) * ‖z‖ + (‖M j‖ * C j) * ‖x‖) := by
        exact Finset.sum_congr rfl fun j _ => by ring
      _ = (ε * ∑ j, ‖M j‖) * ‖z‖ + D * ‖x‖ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ ‖z‖ / 2 + D * ‖x‖ := by
        apply add_le_add_left
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_right (by simpa only [one_div] using hhalf) (norm_nonneg _)
  have hzy : B y = z + ∑ j, M j (SobolevInterval.deriv u j.castSucc) :=
    inverse_leading_mul_scalarSobolevExpression c hc hnz u
  have hz : ‖z‖ ≤ ‖B‖ * ‖y‖ + (‖z‖ / 2 + D * ‖x‖) := by
    have he : z = B y - ∑ j, M j (SobolevInterval.deriv u j.castSucc) := eq_sub_of_add_eq hzy.symm
    calc
      ‖z‖ ≤ ‖B y‖ + ‖∑ j, M j (SobolevInterval.deriv u j.castSucc)‖ := by
        conv_lhs => rw [he]
        exact norm_sub_le _ _
      _ ≤ _ := add_le_add (ContinuousLinearMap.le_opNorm _ _) hlow
  have hz' : ‖z‖ ≤ 2 * ‖B‖ * ‖y‖ + 2 * D * ‖x‖ := by linarith
  change ‖u‖ ≤ E * (1 + 2 * ‖B‖ + 2 * D) * max ‖x‖ ‖y‖
  rw [mul_assoc]
  refine (hnorm u).trans (mul_le_mul_of_nonneg_left ?_ hE)
  change ‖x‖ + ‖z‖ ≤ _
  calc
    ‖x‖ + ‖z‖ ≤ ‖x‖ + (2 * ‖B‖ * ‖y‖ + 2 * D * ‖x‖) := add_le_add_right hz' _
    _ ≤ max ‖x‖ ‖y‖ + (2 * ‖B‖ * max ‖x‖ ‖y‖ + 2 * D * max ‖x‖ ‖y‖) :=
      add_le_add (le_max_left _ _) (add_le_add
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)))
    _ = _ := by ring

/-- A closed subspace of the Sobolev space, equipped with a scalar
differential expression of nonvanishing leading coefficient, defines a
closed partial operator on the ambient interval Hilbert space. -/
theorem isClosed_scalarIntervalOperator
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (W : Submodule ℝ H) (hW : IsClosed (W : Set H)) :
    (scalarIntervalOperator (scalarSobolevExpression c hc) W).IsClosed := by
  let := hW.completeSpace_coe
  obtain ⟨C, hC, hbound⟩ := scalarSobolev_graph_estimate c hc hnz
  let A := scalarSobolevGraphMap (scalarSobolevExpression c hc) W
  have hA : AntilipschitzWith ⟨C, hC⟩ A := A.antilipschitz_of_bound fun u => by
    change ‖u.val‖ ≤ C * ‖A u‖
    rw [Prod.norm_def]
    exact hbound u.val
  change IsClosed ((scalarIntervalOperator (scalarSobolevExpression c hc) W).graph : Set (S × S))
  rw [scalarIntervalOperator, Submodule.toLinearPMap_graph_eq _ (scalarSobolevGraph_singleValued _ _)]
  exact hA.isClosed_range A.uniformContinuous

/-- The closed operator assertion in **Exercise 28(a)** of
[benIsrael2003generalized], Chapter 9. -/
theorem isClosed_constrainedScalarIntervalOperator (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    (constrainedScalarIntervalOperator hlr c hc M).IsClosed :=
  isClosed_scalarIntervalOperator c hc hnz _ (isClosed_scalarSobolevBoundarySpace hlr M)

end ScalarSobolevOperatorClosed

section LinearIntegralIVP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {l r : ℝ}

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem intervalIntegrable_of_continuousOn_Icc {h : ℝ → E}
    (hh : ContinuousOn h (Icc l r)) {t : ℝ} (ht : t ∈ Icc l r) :
    IntervalIntegrable h volume l t :=
  ContinuousOn.intervalIntegrable_of_Icc ht.1 (hh.mono (Icc_subset_Icc_right ht.2))

/-- A continuous linear first-order system with integrable forcing has
a unique continuous solution of its integral initial-value equation. -/
theorem exists_linear_integral_ivp (hlr : l ≤ r)
    (B : ℝ → E →L[ℝ] E) (hB : ContinuousOn B (Icc l r))
    (g : ℝ → E) (hg : IntegrableOn g (Ioo l r)) (v₀ : E) :
    ∃ q : ℝ → E, ContinuousOn q (Icc l r) ∧
      (∀ x ∈ Icc l r, q x = v₀ + ∫ t in l..x, B t (q t) + g t) ∧
      ∀ q' : ℝ → E, ContinuousOn q' (Icc l r) →
        (∀ x ∈ Icc l r, q' x = v₀ + ∫ t in l..x, B t (q' t) + g t) → EqOn q' q (Icc l r) := by
  have hgI : IntegrableOn g (Icc l r) := by
    rwa [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  let p : ℝ → E := fun x => ∫ t in l..x, g t
  have hp : ContinuousOn p (Icc l r) := by
    simpa only [uIcc_of_le hlr] using
      intervalIntegral.continuousOn_primitive_interval (f := g) (a := l) (b := r)
        (by simpa only [uIcc_of_le hlr] using hgI)
  let f : ℝ → E → E := fun t z => B t (z + p t)
  have hfst : MapsTo (Prod.fst : ℝ × E → ℝ) (Icc l r ×ˢ univ) (Icc l r) := fun _ h => h.1
  have hf : ContinuousOn (Function.uncurry f) (Icc l r ×ˢ univ) :=
    (hB.comp continuous_fst.continuousOn hfst).clm_apply
      (continuous_snd.continuousOn.add (hp.comp continuous_fst.continuousOn hfst))
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  let K' : NNReal := ⟨max 0 K, le_max_left _ _⟩
  have hlip (t : ℝ) (ht : t ∈ Icc l r) : LipschitzWith K' (f t) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [show f t x = B t (x + p t) from rfl, show f t y = B t (y + p t) from rfl,
      dist_eq_norm, ← map_sub, add_sub_add_right_eq_sub, dist_eq_norm]
    exact (ContinuousLinearMap.le_opNorm (B t) (x - y)).trans
      (mul_le_mul_of_nonneg_right ((hK t ht).trans (le_max_right _ _)) (norm_nonneg _))
  have hl : l ∈ Icc l r := left_mem_Icc.mpr hlr
  obtain ⟨w, hw⟩ := ODE.exists_isSolutionOn_of_lipschitz hl hf hlip v₀
  have hwint := (ODE.isSolutionOn_iff_integral hl hf hw.continuousOn).mp hw
  let q := fun x => w x + p x
  have hq : ContinuousOn q (Icc l r) := hw.continuousOn.add hp
  have hg' (x : ℝ) (hx : x ∈ Icc l r) : IntervalIntegrable g volume l x :=
    (hgI.mono_set (uIcc_subset_Icc hl hx)).intervalIntegrable
  refine ⟨q, hq, ?_, ?_⟩
  · intro x hx
    have hA : IntervalIntegrable (fun t => B t (q t)) volume l x :=
      intervalIntegrable_of_continuousOn_Icc (hB.clm_apply hq) hx
    rw [intervalIntegral.integral_add hA (hg' x hx)]
    change w x + p x = v₀ + ((∫ t in l..x, f t (w t)) + p x)
    rw [hwint x hx, add_assoc]
  · intro q' hq' heq x hx
    let w' : ℝ → E := fun t => q' t - p t
    have hwc : ContinuousOn w' (Icc l r) := hq'.sub hp
    have hwi (t : ℝ) (ht : t ∈ Icc l r) :
        w' t = v₀ + ∫ z in l..t, f z (w' z) := by
      have hA : IntervalIntegrable (fun z => B z (q' z)) volume l t :=
        intervalIntegrable_of_continuousOn_Icc (hB.clm_apply hq') ht
      change q' t - p t = _
      rw [heq t ht, intervalIntegral.integral_add hA (hg' t ht)]
      have hId : (fun z => f z (w' z)) = (fun z => B z (q' z)) := by
        funext z
        simp [f, w']
      rw [hId]
      change v₀ + ((∫ z in l..t, B z (q' z)) + p t) - p t = _
      abel
    have hw' := (ODE.isSolutionOn_iff_integral hl hf hwc).mpr hwi
    have he : w' x = w x := by
      have hr : l + (r - l) = r := by ring
      exact ODE.isSolutionOn_unique_of_lipschitz
        (t₀ := l) (T := r - l) (f := f) (K := K') (y₀ := v₀)
        (by simpa only [hr] using hlip)
        (by simpa only [hr] using hw') (by simpa only [hr] using hw)
        (by simpa only [hr] using hx)
    change q' x - p x = w x at he
    exact eq_add_of_sub_eq he

end LinearIntegralIVP

section FundamentalFamilyResults

open Set
open scoped ContDiff NNReal

private theorem continuousMulODE_exists_pair
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {C : ℝ → A} (hC : ContinuousOn C (Icc a b)) :
    ∃ X Y : ℝ → A,
      ODE.IsSolutionOn (fun t U => C t * U) t₀ 1 (Icc a b) X ∧
      ODE.IsSolutionOn (fun t U => -(U * C t)) t₀ 1 (Icc a b) Y ∧
      ∀ t ∈ Icc a b, Y t * X t = 1 := by
  obtain ⟨tmax, _, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨t₀, ht₀⟩ hC.norm
  let K : ℝ≥0 := ‖C tmax‖₊
  have hK (t : ℝ) (ht : t ∈ Icc a b) : ‖C t‖ ≤ (K : ℝ) := hmax ht
  have h₁ : ContinuousOn (fun p : ℝ × A => C p.1) (Icc a b ×ˢ univ) :=
    hC.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hLeft (t : ℝ) (ht : t ∈ Icc a b) : LipschitzWith K (fun U => C t * U) := by
    refine LipschitzWith.of_dist_le_mul fun U V => ?_
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _))
  have hRight (t : ℝ) (ht : t ∈ Icc a b) : LipschitzWith K (fun U => -(U * C t)) := by
    refine LipschitzWith.of_dist_le_mul fun U V => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : -(U * C t) - -(V * C t) = -((U - V) * C t) := by
      rw [sub_mul]
      abel
    rw [hsub, norm_neg]
    exact (norm_mul_le _ _).trans (by
      rw [mul_comm (K : ℝ)]
      exact mul_le_mul_of_nonneg_left (hK t ht) (norm_nonneg _))
  obtain ⟨X, hX⟩ := ODE.exists_isSolutionOn_of_lipschitz ht₀
    (h₁.mul continuous_snd.continuousOn) hLeft (1 : A)
  obtain ⟨Y, hY⟩ := ODE.exists_isSolutionOn_of_lipschitz ht₀
    (continuous_snd.continuousOn.mul h₁).neg hRight (1 : A)
  refine ⟨X, Y, hX, hY, fun t ht => ?_⟩
  rcases (ht₀.1.trans ht₀.2).lt_or_eq with hab | rfl
  · have hprod (s : ℝ) (hs : s ∈ Icc a b) :
        HasDerivWithinAt (fun u => Y u * X u) 0 (Icc a b) s := by
      have h := (hY.hasDerivWithinAt hs).fun_mul (hX.hasDerivWithinAt hs)
      simpa only [neg_mul, mul_assoc, neg_add_cancel] using h
    have hderiv (s : ℝ) (hs : s ∈ Icc a b) :
        fderivWithin ℝ (fun u => Y u * X u) (Icc a b) s = 0 := by
      simpa using (hprod s hs).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc hab s hs)
    calc
      Y t * X t = Y t₀ * X t₀ :=
        (convex_Icc a b).is_const_of_fderivWithin_eq_zero
          (fun s hs => (hprod s hs).differentiableWithinAt) hderiv ht ht₀
      _ = 1 := by rw [hY.apply_eq, hX.apply_eq, one_mul]
  · have heq : t = t₀ := (le_antisymm ht.2 ht.1).trans (le_antisymm ht₀.2 ht₀.1).symm
    rw [heq, hY.apply_eq, hX.apply_eq, one_mul]

private theorem contDiffOn_one_of_Icc_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {u v : ℝ → E}
    (hab : a ≤ b) (h : ∀ t ∈ Icc a b, HasDerivWithinAt u (v t) (Icc a b) t)
    (hv : ContinuousOn v (Icc a b)) : ContDiffOn ℝ 1 u (Icc a b) := by
  rcases hab.lt_or_eq with hab | rfl
  · rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)]
    exact ⟨fun t ht => (h t ht).differentiableWithinAt,
      hv.congr fun t ht => (h t ht).derivWithin (uniqueDiffOn_Icc hab t ht)⟩
  · apply (contDiffOn_const (c := u a)).congr
    intro t ht
    rw [show t = a from le_antisymm ht.2 ht.1]

/-- **Exercises 30 and 36** of [benIsrael2003generalized], Chapter 9.
A continuous first-order coefficient has a normalized, continuously differentiable
fundamental family. Its inverse solves the corresponding right-multiplication
equation with the opposite sign. Both equations use the interval derivative. -/
theorem exists_firstOrderFundamentalFamily {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {C : ℝ → E →L[ℝ] E} (hC : ContinuousOn C (Icc a b)) :
    ∃ X : ℝ → E ≃L[ℝ] E,
      X t₀ = ContinuousLinearEquiv.refl ℝ E ∧
      ContDiffOn ℝ 1 (fun t => (X t : E →L[ℝ] E)) (Icc a b) ∧
      ContDiffOn ℝ 1 (fun t => ((X t).symm : E →L[ℝ] E)) (Icc a b) ∧
      (∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s => (X s : E →L[ℝ] E))
          ((C t).comp (X t : E →L[ℝ] E)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s => ((X s).symm : E →L[ℝ] E))
          (-((X t).symm : E →L[ℝ] E).comp (C t)) (Icc a b) t) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨U, V, hU, hV, hVU⟩ := continuousMulODE_exists_pair ht₀ hC
  classical
  have hleft (t : ℝ) (ht : t ∈ Icc a b) : Function.LeftInverse (V t) (U t) :=
    fun x => DFunLike.congr_fun (hVU t ht) x
  have hright (t : ℝ) (ht : t ∈ Icc a b) : Function.RightInverse (V t) (U t) := by
    have hsurj : Function.Surjective (U t) := LinearMap.injective_iff_surjective.mp
      (hleft t ht).injective
    rintro y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [hleft t ht x]
  let X : ℝ → E ≃L[ℝ] E := fun t =>
    if ht : t ∈ Icc a b then
      { toLinearEquiv :=
          { toLinearMap := (U t).toLinearMap
            invFun := V t
            left_inv := hleft t ht
            right_inv := hright t ht }
        continuous_toFun := (U t).continuous
        continuous_invFun := (V t).continuous }
    else ContinuousLinearEquiv.refl ℝ E
  have hX (t : ℝ) (ht : t ∈ Icc a b) : (X t : E →L[ℝ] E) = U t := by
    simp only [X, dite_eq_left ht]
    rfl
  have hXinv (t : ℝ) (ht : t ∈ Icc a b) : ((X t).symm : E →L[ℝ] E) = V t := by
    simp only [X, dite_eq_left ht]
    ext x
    rfl
  have hXd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => (X s : E →L[ℝ] E))
        ((C t).comp (X t : E →L[ℝ] E)) (Icc a b) t := by
    rw [hX t ht]
    exact (hU.hasDerivWithinAt ht).congr hX (hX t ht)
  have hXid (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => ((X s).symm : E →L[ℝ] E))
        (-((X t).symm : E →L[ℝ] E).comp (C t)) (Icc a b) t := by
    rw [hXinv t ht]
    exact (hV.hasDerivWithinAt ht).congr hXinv (hXinv t ht)
  refine ⟨X, ?_, ?_, ?_, hXd, hXid⟩
  · ext x
    exact DFunLike.congr_fun ((hX t₀ ht₀).trans hU.apply_eq) x
  · exact (contDiffOn_one_of_Icc_derivative (ht₀.1.trans ht₀.2)
      (fun t ht => hU.hasDerivWithinAt ht) (hC.mul hU.continuousOn)).congr hX
  · exact (contDiffOn_one_of_Icc_derivative (ht₀.1.trans ht₀.2)
      (fun t ht => hV.hasDerivWithinAt ht) (hV.continuousOn.mul hC).neg).congr hXinv

/-- A fundamental family can be chosen with globally continuous forward and
inverse maps, and with ordinary derivatives at every point of the interval.
The coefficient is extended continuously before solving on a larger interval. -/
theorem exists_firstOrderFundamentalFamily_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {C : ℝ → E →L[ℝ] E} (hC : ContinuousOn C (Icc a b)) :
    ∃ X : ℝ → E ≃L[ℝ] E,
      X t₀ = ContinuousLinearEquiv.refl ℝ E ∧
      Continuous (fun t => (X t : E →L[ℝ] E)) ∧
      Continuous (fun t => ((X t).symm : E →L[ℝ] E)) ∧
      (∀ t ∈ Icc a b,
        HasDerivAt (fun s => (X s : E →L[ℝ] E))
          ((C t).comp (X t : E →L[ℝ] E)) t) ∧
      (∀ t ∈ Icc a b,
        HasDerivAt (fun s => ((X s).symm : E →L[ℝ] E))
          (-((X t).symm : E →L[ℝ] E).comp (C t)) t) := by
  let a' := a - 1
  let b' := b + 1
  have hab : a ≤ b := ht₀.1.trans ht₀.2
  have hab' : a' ≤ b' := by dsimp [a', b']; linarith
  have hin (t : ℝ) (ht : t ∈ Icc a b) : t ∈ Ioo a' b' := by
    exact ⟨by dsimp [a']; linarith [ht.1], by dsimp [b']; linarith [ht.2]⟩
  let C' : ℝ → E →L[ℝ] E := IccExtend hab (fun t : Icc a b => C t)
  have hC' : Continuous C' :=
    continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_domRestrict.mp hC)
  have hCeq (t : ℝ) (ht : t ∈ Icc a b) : C' t = C t := IccExtend_of_mem hab _ ht
  obtain ⟨U, hU₀, hUc, hUi, hUd, hUid⟩ :=
    exists_firstOrderFundamentalFamily (Ioo_subset_Icc_self (hin t₀ ht₀)) hC'.continuousOn
  let X : ℝ → E ≃L[ℝ] E := IccExtend hab' (fun t : Icc a' b' => U t)
  have hX (t : ℝ) (ht : t ∈ Icc a' b') : X t = U t := IccExtend_of_mem hab' _ ht
  refine ⟨X, (hX t₀ (Ioo_subset_Icc_self (hin t₀ ht₀))).trans hU₀, ?_, ?_, ?_, ?_⟩
  · exact continuous_IccExtend_iff.mpr
      (continuousOn_iff_continuous_domRestrict.mp hUc.continuousOn)
  · exact continuous_IccExtend_iff.mpr
      (continuousOn_iff_continuous_domRestrict.mp hUi.continuousOn)
  · intro t ht
    have hm : t ∈ Icc a' b' := Ioo_subset_Icc_self (hin t ht)
    rw [← hCeq t ht, hX t hm]
    exact ((hUd t hm).congr
      (fun s hs => congrArg ContinuousLinearEquiv.toContinuousLinearMap (hX s hs))
      (congrArg ContinuousLinearEquiv.toContinuousLinearMap (hX t hm))).hasDerivAt
      (Filter.mem_of_superset (Ioo_mem_nhds (hin t ht).1 (hin t ht).2) Ioo_subset_Icc_self)
  · intro t ht
    have hm : t ∈ Icc a' b' := Ioo_subset_Icc_self (hin t ht)
    rw [← hCeq t ht, hX t hm]
    exact ((hUid t hm).congr
      (fun s hs => congrArg (fun W : E ≃L[ℝ] E => (W.symm : E →L[ℝ] E)) (hX s hs))
      (congrArg (fun W : E ≃L[ℝ] E => (W.symm : E →L[ℝ] E)) (hX t hm))).hasDerivAt
      (Filter.mem_of_superset (Ioo_mem_nhds (hin t ht).1 (hin t ht).2) Ioo_subset_Icc_self)

/-- **Exercise 30(c), (f)** of [benIsrael2003generalized], Chapter 9.
For continuous coefficients in a first-order system, the family solving the
homogeneous equation uses the inverse of the leading coefficient. -/
theorem exists_differentialExpression_fundamentalFamily {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (A₁ : ℝ → E ≃L[ℝ] E) {A₀ : ℝ → E →L[ℝ] E}
    (hA₁ : ContinuousOn (fun t => (A₁ t : E →L[ℝ] E)) (Icc a b))
    (hA₀ : ContinuousOn A₀ (Icc a b)) :
    ∃ (X : ℝ → E ≃L[ℝ] E) (X' : ℝ → E →L[ℝ] E),
      X t₀ = ContinuousLinearEquiv.refl ℝ E ∧
      Continuous (fun t => (X t : E →L[ℝ] E)) ∧
      Continuous (fun t => ((X t).symm : E →L[ℝ] E)) ∧
      (∀ t ∈ Icc a b, HasDerivAt (fun s => (X s : E →L[ℝ] E)) (X' t) t) ∧
      (∀ t ∈ Icc a b,
        (A₁ t : E →L[ℝ] E).comp (X' t) + (A₀ t).comp (X t : E →L[ℝ] E) = 0) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hA₁inv : ContinuousOn (fun t => ((A₁ t).symm : E →L[ℝ] E)) (Icc a b) := by
    have heq (t : ℝ) : Ring.inverse (A₁ t : E →L[ℝ] E) = (A₁ t).symm := by
      change Ring.inverse ((A₁ t).toUnit : E →L[ℝ] E) = (A₁ t).symm
      exact Ring.inverse_unit _
    intro t ht
    have hi := (NormedRing.inverse_continuousAt (A₁ t).toUnit).comp_continuousWithinAt_of_eq
      (hA₁ t ht) rfl
    exact hi.congr (fun s _ => (heq s).symm) (heq t).symm
  let C (t : ℝ) : E →L[ℝ] E := -((A₁ t).symm : E →L[ℝ] E).comp (A₀ t)
  have hC : ContinuousOn C (Icc a b) := (hA₁inv.mul hA₀).neg
  obtain ⟨X, hX₀, hXc, hXic, hXd, _⟩ := exists_firstOrderFundamentalFamily_hasDerivAt ht₀ hC
  refine ⟨X, fun t => (C t).comp (X t : E →L[ℝ] E), hX₀, hXc, hXic, hXd, ?_⟩
  intro t _
  ext x
  simp [C]

/-- The normalized fundamental family evaluates to the homogeneous solution
with a prescribed initial vector. Every interval solution equals this one. -/
theorem eqOn_firstOrderSolution_iff_eval_fundamentalFamily {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {C : ℝ → E →L[ℝ] E} (X : ℝ → E ≃L[ℝ] E)
    (hX₀ : X t₀ = ContinuousLinearEquiv.refl ℝ E)
    (hX : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => (X s : E →L[ℝ] E))
        ((C t).comp (X t : E →L[ℝ] E)) (Icc a b) t)
    (hXi : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => ((X s).symm : E →L[ℝ] E))
        (-((X t).symm : E →L[ℝ] E).comp (C t)) (Icc a b) t)
    (x₀ : E) (u : ℝ → E) :
    ODE.IsSolutionOn (fun t x => C t x) t₀ x₀ (Icc a b) u ↔
      EqOn u (fun t => X t x₀) (Icc a b) := by
  have hsol : ODE.IsSolutionOn (fun t x => C t x) t₀ x₀ (Icc a b) (fun t => X t x₀) := by
    refine ⟨by simp [hX₀], fun t ht => ?_⟩
    simpa using (hX t ht).clm_apply (hasDerivWithinAt_const t (Icc a b) x₀)
  refine ⟨fun hu t ht => ?_, fun hu => hsol.congr hu ((hu ht₀).trans hsol.apply_eq)⟩
  rcases (ht₀.1.trans ht₀.2).lt_or_eq with hab | rfl
  · let v (s : ℝ) := (X s).symm (u s)
    have hV (s : ℝ) (hs : s ∈ Icc a b) : HasDerivWithinAt v 0 (Icc a b) s := by
      simpa only [neg_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, neg_add_cancel] using
        (hXi s hs).clm_apply (hu.hasDerivWithinAt hs)
    have hderiv (s : ℝ) (hs : s ∈ Icc a b) : fderivWithin ℝ v (Icc a b) s = 0 := by
      simpa using (hV s hs).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc hab s hs)
    have hev : v t = v t₀ := (convex_Icc a b).is_const_of_fderivWithin_eq_zero
      (fun s hs => (hV s hs).differentiableWithinAt) hderiv ht ht₀
    have hval : (X t).symm (u t) = x₀ := by simpa [v, hX₀, hu.apply_eq] using hev
    simpa using congrArg (X t) hval
  · have heq : t = t₀ := (le_antisymm ht.2 ht.1).trans (le_antisymm ht₀.2 ht₀.1).symm
    simp [heq, hX₀, hu.apply_eq]

section AdjointFundamental

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The inverse adjoint of the fundamental family, bundled with its pointwise inverse. -/
def firstOrderAdjointFundamentalFamily (X : ℝ → E ≃L[ℝ] E) (t : ℝ) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit
    { val := (((X t).symm : E →L[ℝ] E)).adjoint
      inv := ((X t : E →L[ℝ] E)).adjoint
      val_inv := by
        change (((X t).symm : E →L[ℝ] E)).adjoint.comp ((X t : E →L[ℝ] E)).adjoint = 1
        rw [← ContinuousLinearMap.adjoint_comp]
        simp [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.one_def]
      inv_val := by
        change ((X t : E →L[ℝ] E)).adjoint.comp (((X t).symm : E →L[ℝ] E)).adjoint = 1
        rw [← ContinuousLinearMap.adjoint_comp]
        simp [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.one_def] }

/-- The forward map of the adjoint fundamental family is the inverse adjoint. -/
theorem firstOrderAdjointFundamentalFamily_toContinuousLinearMap
    (X : ℝ → E ≃L[ℝ] E) (t : ℝ) :
    (firstOrderAdjointFundamentalFamily X t : E →L[ℝ] E) =
      ((X t).symm : E →L[ℝ] E).adjoint := rfl

/-- The inverse map of the adjoint fundamental family is the adjoint of the original family. -/
theorem firstOrderAdjointFundamentalFamily_symm_toContinuousLinearMap
    (X : ℝ → E ≃L[ℝ] E) (t : ℝ) :
    ((firstOrderAdjointFundamentalFamily X t).symm : E →L[ℝ] E) =
      (X t : E →L[ℝ] E).adjoint := rfl

/-- **Exercise 36** of [benIsrael2003generalized], Chapter 9.
The inverse adjoint solves the adjoint homogeneous system, and every
adjoint solution is obtained by applying it to an initial vector. -/
theorem eqOn_adjointFirstOrderSolution_iff_eval_fundamentalFamily
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {C : ℝ → E →L[ℝ] E} (X : ℝ → E ≃L[ℝ] E)
    (hX₀ : X t₀ = ContinuousLinearEquiv.refl ℝ E)
    (hX : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => (X s : E →L[ℝ] E))
        ((C t).comp (X t : E →L[ℝ] E)) (Icc a b) t)
    (hXi : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => ((X s).symm : E →L[ℝ] E))
        (-((X t).symm : E →L[ℝ] E).comp (C t)) (Icc a b) t)
    (y₀ : E) (v : ℝ → E) :
    ODE.IsSolutionOn (fun t y => -(C t).adjoint y) t₀ y₀ (Icc a b) v ↔
      EqOn v (fun t => firstOrderAdjointFundamentalFamily X t y₀) (Icc a b) := by
  let A : (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  have hA (T : E →L[ℝ] E) : A T = T.adjoint := rfl
  let Y := firstOrderAdjointFundamentalFamily X
  have hY₀ : Y t₀ = ContinuousLinearEquiv.refl ℝ E := by
    apply ContinuousLinearEquiv.coe_injective
    rw [firstOrderAdjointFundamentalFamily_toContinuousLinearMap, hX₀]
    simp [ContinuousLinearMap.adjoint_id]
  have hY (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => (Y s : E →L[ℝ] E))
        ((-(C t).adjoint).comp (Y t : E →L[ℝ] E)) (Icc a b) t := by
    have h := A.hasFDerivAt.comp_hasDerivWithinAt t (hXi t ht)
    simpa [Y, hA, Function.comp_def, firstOrderAdjointFundamentalFamily_toContinuousLinearMap]
      using h
  have hYi (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => ((Y s).symm : E →L[ℝ] E))
        (-((Y t).symm : E →L[ℝ] E).comp (-(C t).adjoint)) (Icc a b) t := by
    have h := A.hasFDerivAt.comp_hasDerivWithinAt t (hX t ht)
    simpa [Y, hA, Function.comp_def, firstOrderAdjointFundamentalFamily_symm_toContinuousLinearMap]
      using h
  exact eqOn_firstOrderSolution_iff_eval_fundamentalFamily ht₀ Y hY₀ hY hYi y₀ v

end AdjointFundamental

end FundamentalFamilyResults

section BoundaryResults

open Set Module

section BoundaryRange

variable {S Y M : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- The boundary data attained by homogeneous solutions of the free
differential equation. -/
def homogeneousBoundaryRange (A : S →L[ℝ] Y) (B : S →L[ℝ] M) : Submodule ℝ M :=
  A.ker.map B.toLinearMap

/-- The obstruction to a boundary solution is the boundary residual of one
free solution, taken modulo the homogeneous boundary data. -/
def boundaryObstruction (A : S →L[ℝ] Y) (B : S →L[ℝ] M) (J : Y →L[ℝ] S) :
    Y →L[ℝ] M ⧸ homogeneousBoundaryRange A B :=
  (homogeneousBoundaryRange A B).mkQL.comp (B.comp J)

private theorem mem_boundaryObstruction_ker_iff (A : S →L[ℝ] Y) (B : S →L[ℝ] M)
    (J : Y →L[ℝ] S) (y : Y) :
    y ∈ (boundaryObstruction A B J).ker ↔ B (J y) ∈ homogeneousBoundaryRange A B := by
  change (homogeneousBoundaryRange A B).mkQ (B (J y)) = 0 ↔ _
  simp

/-- A forcing is compatible with the homogeneous boundary conditions
exactly when its free boundary residual can be canceled by a homogeneous
solution. -/
theorem range_restrictedBoundary_eq_ker_obstruction (A : S →L[ℝ] Y) (B : S →L[ℝ] M)
    (J : Y →L[ℝ] S) (hJ : Function.RightInverse J A) :
    (A.toLinearMap.domRestrict B.ker).range = (boundaryObstruction A B J).ker := by
  ext y
  rw [mem_boundaryObstruction_ker_iff]
  change (∃ x : B.ker, A (x : S) = y) ↔ ∃ x ∈ A.ker, B x = B (J y)
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨J (A (x : S)) - (x : S), ?_, ?_⟩
    · change A (J (A (x : S)) - (x : S)) = 0
      rw [map_sub, hJ, sub_self]
    · have hx : B (x : S) = 0 := x.property
      rw [map_sub, hx, sub_zero]
  · rintro ⟨x, hx, he⟩
    have hB : J y - x ∈ B.ker := by
      change B (J y - x) = 0
      rw [map_sub, he, sub_self]
    refine ⟨⟨J y - x, hB⟩, ?_⟩
    change A (J y - x) = y
    rw [map_sub, hJ, show A x = 0 from hx, sub_zero]

/-- Independent boundary equations make the finite-dimensional obstruction
map surjective. -/
theorem boundaryObstruction_surjective (A : S →L[ℝ] Y) (B : S →L[ℝ] M)
    (J : Y →L[ℝ] S) (hJ : Function.RightInverse J A) (hB : Function.Surjective B) :
    Function.Surjective (boundaryObstruction A B J) := by
  let W := homogeneousBoundaryRange A B
  intro z
  obtain ⟨m, rfl⟩ := W.mkQ_surjective z
  obtain ⟨x, rfl⟩ := hB m
  refine ⟨A x, ?_⟩
  change W.mkQ (B (J (A x))) = W.mkQ (B x)
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub]
  have hx : J (A x) - x ∈ A.ker := by
    change A (J (A x) - x) = 0
    rw [map_sub, hJ, sub_self]
  have hW : B (J (A x) - x) ∈ W := ⟨_, hx, rfl⟩
  simpa only [← LinearMap.mem_ker, Submodule.ker_mkQ] using hW

/-- On a finite-dimensional space of boundary data, the constrained
differential expression has closed range. -/
theorem isClosed_range_restrictedBoundary [FiniteDimensional ℝ M]
    (A : S →L[ℝ] Y) (B : S →L[ℝ] M) (J : Y →L[ℝ] S) (hJ : Function.RightInverse J A) :
    IsClosed ((A.toLinearMap.domRestrict B.ker).range : Set Y) := by
  let W := homogeneousBoundaryRange A B
  have hset : ((boundaryObstruction A B J).ker : Set Y) = (B.comp J) ⁻¹' (W : Set M) := by
    ext y
    exact mem_boundaryObstruction_ker_iff A B J y
  rw [range_restrictedBoundary_eq_ker_obstruction A B J hJ, hset]
  exact W.closed_of_finiteDimensional.preimage (B.comp J).continuous

private def restrictedBoundaryKernelEquiv (A : S →L[ℝ] Y) (B : S →L[ℝ] M) :
    (A.toLinearMap.domRestrict B.ker).ker ≃ₗ[ℝ] (B.toLinearMap.domRestrict A.ker).ker where
  toFun u := ⟨⟨u.val.val, show A u.val.val = 0 from u.property⟩, u.val.property⟩
  invFun v := ⟨⟨v.val.val, show B v.val.val = 0 from v.property⟩, v.val.property⟩
  left_inv _ :=  Subtype.ext (Subtype.ext rfl)
  right_inv _ :=  Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

/-- **Exercise 30(d)** of [benIsrael2003generalized], Chapter 9, at the
boundary-constraint level. The nullity of the free operator and the number
of independent boundary conditions determine the index of the constrained
realization. -/
theorem finrank_restrictedBoundary_index [FiniteDimensional ℝ M]
    (A : S →L[ℝ] Y) (B : S →L[ℝ] M) [FiniteDimensional ℝ A.ker]
    (J : Y →L[ℝ] S) (hJ : Function.RightInverse J A) (hB : Function.Surjective B) :
    finrank ℝ (A.toLinearMap.domRestrict B.ker).ker + finrank ℝ M =
      finrank ℝ (Y ⧸ (A.toLinearMap.domRestrict B.ker).range) + finrank ℝ A.ker := by
  let W := homogeneousBoundaryRange A B
  let Ob := boundaryObstruction A B J
  have hRank := (B.toLinearMap.domRestrict A.ker).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict] at hRank
  have hk := (restrictedBoundaryKernelEquiv A B).finrank_eq
  have hquot := W.finrank_quotient_add_finrank
  have hEq : finrank ℝ (Y ⧸ Ob.ker) = finrank ℝ (M ⧸ W) :=
    (Ob.toLinearMap.quotKerEquivOfSurjective (boundaryObstruction_surjective A B J hJ hB)).finrank_eq
  rw [range_restrictedBoundary_eq_ker_obstruction A B J hJ]
  change _ + _ = finrank ℝ (Y ⧸ Ob.ker) + _
  change finrank ℝ W + _ = _ at hRank
  omega

end BoundaryRange

end BoundaryResults

section ScalarCompanionIVP

open Matrix

variable {n : ℕ} {l r : ℝ}

local notation "H" => SobolevInterval (n + 1) l r
local notation "S" => IntervalL2 l r
local notation "J" => (Fin (n + 1) → ℝ)
local notation "μ" => volume.restrict (Ioo l r)
local notation "last" => Fin.last (n + 1)

/-- The normalized companion matrix acts on successive derivatives of a scalar solution. -/
def scalarNormalizedCompanion (c : Fin (n + 2) → ℝ → ℝ) (t : ℝ) : J →L[ℝ] J :=
  ContinuousLinearMap.pi (Fin.lastCases 0 (fun j : Fin n => ContinuousLinearMap.proj (R := ℝ) j.succ))
    - ∑ j : Fin (n + 1), (c j.castSucc t / c last t) •
      (ContinuousLinearMap.proj (R := ℝ) j).smulRight (Pi.single (Fin.last n) 1)

private theorem scalarNormalizedCompanion_apply_castSucc (c : Fin (n + 2) → ℝ → ℝ) (t : ℝ)
    (v : J) (j : Fin n) : scalarNormalizedCompanion c t v j.castSucc = v j.succ := by
  simp [scalarNormalizedCompanion, Fin.castSucc_ne_last, Pi.single_eq_of_ne]

private theorem scalarNormalizedCompanion_apply_last (c : Fin (n + 2) → ℝ → ℝ) (t : ℝ) (v : J) :
    scalarNormalizedCompanion c t v (Fin.last n) =
      -∑ j : Fin (n + 1), (c j.castSucc t / c last t) * v j := by
  simp [scalarNormalizedCompanion]

private theorem continuousOn_scalarNormalizedCompanion (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (c j) (Icc l r)) (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) :
    ContinuousOn (scalarNormalizedCompanion c) (Icc l r) := by
  unfold scalarNormalizedCompanion
  exact continuousOn_const.sub (continuousOn_finsetSum _ fun j _ =>
    ((hc j.castSucc).div (hc last) hnz).smul continuousOn_const)

private def scalarSobolevJet (u : H) (t : ℝ) : J := fun j =>
  SobolevIntervalLp.rep (SobolevIntervalLp.derivOne u j) t

private theorem continuousOn_scalarSobolevJet (hlr : l < r) (u : H) :
    ContinuousOn (scalarSobolevJet u) (Icc l r) := by
  apply continuousOn_pi.mpr
  intro j
  have h := SobolevIntervalLp.continuousOn_rep (SobolevIntervalLp.ordConnected_coe_Ioo l r)
    (SobolevIntervalLp.derivOne u j)
  simpa only [SobolevIntervalLp.closure_coe_Ioo hlr, scalarSobolevJet] using h

private theorem scalarSobolevJet_apply_ae (u : H) (j : Fin (n + 1)) :
    (fun t => scalarSobolevJet u t j) =ᵐ[μ] SobolevInterval.deriv u j.castSucc := by
  symm
  have h := SobolevInterval.fn_ae_eq_rep (SobolevIntervalLp.derivOne u j)
  rwa [← SobolevIntervalLp.deriv_zero, SobolevIntervalLp.deriv_derivOne_zero] at h

private theorem intervalIntegral_congr_ae_Ioo {f g : ℝ → ℝ} (h : f =ᵐ[μ] g)
    {t : ℝ} (ht : t ∈ Icc l r) :
    (∫ x in l..t, f x) = ∫ x in l..t, g x := by
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
    ← restrict_Ioo_eq_restrict_Ioc]
  exact integral_congr_ae (Filter.EventuallyEq.filter_mono h
    (ae_mono (Measure.restrict_mono_set volume (Ioo_subset_Ioo_right ht.2))))

private def scalarJetForcing (y : S) (t : ℝ) : J :=
  Pi.single (Fin.last n) (y t)

private theorem integrableOn_scalarJetForcing (y : S) : IntegrableOn (scalarJetForcing y : ℝ → J)
    (Ioo l r) := by
  apply integrable_pi_iff.mpr
  intro j
  by_cases hj : j = Fin.last n
  · subst j
    simp only [scalarJetForcing, Pi.single_eq_same]
    exact (Lp.memLp y).integrable one_le_two
  · simp [scalarJetForcing, Pi.single_eq_of_ne hj]

private theorem scalarSobolevJet_sub_eq_integral (hlr : l < r) (u : H)
    (j : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc l r) :
    scalarSobolevJet u t j - scalarSobolevJet u l j =
      ∫ x in l..t, SobolevInterval.deriv u j.succ x := by
  have he := SobolevInterval.toContinuousMap_sub_eq_integral hlr (SobolevIntervalLp.derivOne u j)
    ⟨l, left_mem_Icc.mpr hlr.le⟩ ⟨t, ht⟩
  change scalarSobolevJet u t j - scalarSobolevJet u l j =
    ∫ x in l..t, SobolevInterval.deriv (SobolevIntervalLp.derivOne u j) 1 x at he
  rwa [show SobolevInterval.deriv (SobolevIntervalLp.derivOne u j) 1 =
    SobolevInterval.deriv u j.succ from SobolevIntervalLp.deriv_derivOne_one u j] at he

private theorem scalarSobolevJet_solves (hlr : l < r) (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (c j) (Icc l r)) (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (u : H) :
    let q := scalarSobolevJet u
    let y := scalarCoefficientMultiplier (fun t => (c last t)⁻¹) ((hc last).inv₀ hnz)
      (scalarSobolevExpression c hc u)
    ∀ t ∈ Icc l r, q t = q l + ∫ x in l..t, scalarNormalizedCompanion c x (q x) + scalarJetForcing y x := by
  dsimp only
  let q := scalarSobolevJet u
  let y := scalarCoefficientMultiplier (fun t => (c last t)⁻¹) ((hc last).inv₀ hnz)
    (scalarSobolevExpression c hc u)
  intro t ht
  have hB := (continuousOn_scalarNormalizedCompanion c hc hnz).clm_apply (continuousOn_scalarSobolevJet hlr u)
  have hgI : IntegrableOn (scalarJetForcing y : ℝ → J) (Icc l r) := by
    rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
    exact integrableOn_scalarJetForcing y
  let F : ℝ → J := fun x => scalarNormalizedCompanion c x (q x) + scalarJetForcing y x
  have hi : IntervalIntegrable F volume l t :=
    (intervalIntegrable_of_continuousOn_Icc hB ht).add
      ((hgI.mono_set (uIcc_subset_Icc (left_mem_Icc.mpr hlr.le) ht)).intervalIntegrable)
  funext j
  let P : J →L[ℝ] ℝ := ContinuousLinearMap.proj j
  change q t j = (q l + ∫ x in l..t, F x) j
  have he : ((∫ x in l..t, F x) : J) j = ∫ x in l..t, F x j :=
    (P.intervalIntegral_comp_comm hi).symm
  rw [Pi.add_apply, he]
  rw [add_comm (q l j)]
  apply sub_eq_iff_eq_add.mp
  change scalarSobolevJet u t j - scalarSobolevJet u l j = _
  rw [scalarSobolevJet_sub_eq_integral hlr u j ht]
  refine intervalIntegral_congr_ae_Ioo (r := r) ?_ ht
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hRep : ∀ᵐ x ∂μ, ∀ k, q x k = SobolevInterval.deriv u k.castSucc x :=
      ae_all_iff.mpr (scalarSobolevJet_apply_ae u)
    filter_upwards [scalarCoefficientMultiplier_apply_ae (fun t => (c last t)⁻¹)
        ((hc last).inv₀ hnz) (scalarSobolevExpression c hc u),
      scalarSobolevExpression_apply_ae c hc u, hRep, ae_restrict_mem measurableSet_Ioo]
      with x hy hA hRep hx
    simp only [F, Pi.add_apply, scalarNormalizedCompanion_apply_last, scalarJetForcing, Pi.single_eq_same,
      Fin.succ_last]
    have hA' : (scalarSobolevExpression c hc u) x =
        (∑ j : Fin (n + 1), c j.castSucc x * SobolevInterval.deriv u j.castSucc x) +
          c last x * SobolevInterval.deriv u last x :=
      hA.trans (Fin.sum_univ_castSucc (fun j : Fin (n + 2) => c j x * SobolevInterval.deriv u j x))
    rw [show y x = _ from hy, hA']
    have hsum : (∑ j : Fin (n + 1), (c j.castSucc x / c last x) * q x j) =
        (c last x)⁻¹ * ∑ j : Fin (n + 1), c j.castSucc x * SobolevInterval.deriv u j.castSucc x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hRep]; ring
    rw [hsum, mul_add, ← mul_assoc, inv_mul_cancel₀ (hnz x (Ioo_subset_Icc_self hx)), one_mul]
    ring
  · have h := (scalarSobolevJet_apply_ae u k.succ).symm
    filter_upwards [h] with x hx
    simp only [F]
    rw [Pi.add_apply, scalarNormalizedCompanion_apply_castSucc,
      scalarJetForcing, Pi.single_eq_of_ne (Fin.castSucc_ne_last k), add_zero]
    simpa only [Fin.succ_castSucc] using hx

end ScalarCompanionIVP

section ScalarInitialValue

variable {n : ℕ} {l r : ℝ}

local notation "H" => SobolevInterval (n + 1) l r
local notation "S" => IntervalL2 l r
local notation "J" => (Fin (n + 1) → ℝ)
local notation "μ" => volume.restrict (Ioo l r)
local notation "last" => Fin.last (n + 1)

private theorem scalarHasWeakIteratedDerivOn_of_chain {k : ℕ} (v : Fin (k + 1) → S)
    (h : ∀ j : Fin k, HasWeakDerivOn (v j.castSucc) (v j.succ) (TopologicalSpace.Opens.Ioo l r)) :
    ∀ j : Fin (k + 1), HasWeakIteratedDerivOn j (v 0) (v j) (TopologicalSpace.Opens.Ioo l r) := by
  intro j
  induction j using Fin.induction with
  | zero =>
    exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
      ((intervalL2_integrable (v 0)).locallyIntegrableOn)
  | succ j ih =>
    exact HasWeakIteratedDerivOn.succ_of_hasWeakDerivOn ih (h j)

private theorem scalarSobolev_of_integral_jet (hlr : l < r)
    (q f : ℝ → J) (hq : ContinuousOn q (Icc l r))
    (hf : ∀ j, MemLp (fun x => f x j) 2 μ)
    (hshift : ∀ x (j : Fin n), f x j.castSucc = q x j.succ)
    (heq : ∀ x ∈ Icc l r, q x = q l + ∫ t in l..x, f t) :
    ∃ u : H, EqOn (scalarSobolevJet u) q (Icc l r) ∧
      SobolevInterval.deriv u last =ᵐ[μ] fun x => f x (Fin.last n) := by
  have hqc (j : Fin (n + 1)) : ContinuousOn (fun x => q x j) (Icc l r) := continuousOn_pi.mp hq j
  have hqLp (j : Fin (n + 1)) : MemLp (fun x => q x j) 2 μ :=
    (hqc j).memLp_top_restrict_Ioo.mono_exponent le_top
  let v : Fin (n + 2) → S :=
    Fin.lastCases ((hf (Fin.last n)).toLp _) (fun j => (hqLp j).toLp _)
  have hd (j : Fin (n + 1)) : HasWeakDerivOn (fun x => q x j) (fun x => f x j)
      (TopologicalSpace.Opens.Ioo l r) := by
    have hfi : IntegrableOn f (Ioo l r) :=
      integrable_pi_iff.mpr fun k => (hf k).integrable one_le_two
    have hj : IntegrableOn (fun x => f x j) (Ioo l r) := (hf j).integrable one_le_two
    refine (hasWeakDerivOn_integral hlr.le hj (q l j)).congr_ae ?_ EventuallyEq.rfl
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' := Ioo_subset_Icc_self hx
    have hi : IntervalIntegrable f volume l x := by
      have hI : IntegrableOn f (Icc l r) := by
        rwa [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
      exact (hI.mono_set (uIcc_subset_Icc (left_mem_Icc.mpr hlr.le) hx')).intervalIntegrable
    have Hx : q x j = q l j + ((∫ t in l..x, f t) : J) j := congrFun (heq x hx') j
    let P : J →L[ℝ] ℝ := ContinuousLinearMap.proj j
    exact ((congrArg (fun z : ℝ => q l j + z) (P.intervalIntegral_comp_comm hi)).trans Hx.symm)
  have hchain (j : Fin (n + 1)) : HasWeakDerivOn (v j.castSucc) (v j.succ)
      (TopologicalSpace.Opens.Ioo l r) := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [v, Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last]
      exact (hd (Fin.last n)).congr_ae (hqLp _).coeFn_toLp.symm (hf _).coeFn_toLp.symm
    · simp only [v, Fin.lastCases_castSucc, Fin.succ_castSucc]
      refine (hd j.castSucc).congr_ae (hqLp _).coeFn_toLp.symm ?_
      have hs : (fun x => f x j.castSucc) =ᵐ[μ] (fun x => q x j.succ) :=
        Eventually.of_forall fun x => hshift x j
      exact hs.trans (hqLp _).coeFn_toLp.symm
  let u : H := SobolevInterval.mk v (scalarHasWeakIteratedDerivOn_of_chain v hchain)
  refine ⟨u, ?_, ?_⟩
  · intro x hx
    funext j
    apply SobolevIntervalLp.rep_eq_of_continuousOn (SobolevIntervalLp.ordConnected_coe_Ioo l r)
      (SobolevIntervalLp.derivOne u j)
    · simpa only [SobolevIntervalLp.closure_coe_Ioo hlr] using hqc j
    · rw [← SobolevIntervalLp.deriv_zero, SobolevIntervalLp.deriv_derivOne_zero]
      change (⇑(v j.castSucc) : ℝ → ℝ) =ᵐ[μ] _
      simp only [v, Fin.lastCases_castSucc]
      exact (hqLp j).coeFn_toLp
    · simpa only [SobolevIntervalLp.closure_coe_Ioo hlr] using hx
  · change v last =ᵐ[μ] _
    simp only [v, Fin.lastCases_last]
    exact (hf (Fin.last n)).coeFn_toLp

/-- The unrestricted scalar problem has a Sobolev solution for every
square-integrable forcing and prescribed initial jet. -/
theorem exists_scalarSobolev_initialValue (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) (y : S) (v₀ : J) :
    ∃ u : H, scalarSobolevExpression c hc u = y ∧
      scalarSobolevBoundaryTrace hlr u ∘ Sum.inl = v₀ := by
  let B := scalarNormalizedCompanion c
  let normedY := scalarCoefficientMultiplier (fun t => (c last t)⁻¹) ((hc last).inv₀ hnz) y
  let g : ℝ → J := scalarJetForcing normedY
  obtain ⟨q, hq, heq, _⟩ := exists_linear_integral_ivp hlr.le B
    (continuousOn_scalarNormalizedCompanion c hc hnz) g (integrableOn_scalarJetForcing normedY) v₀
  let f : ℝ → J := fun t => B t (q t) + g t
  have hL : ContinuousOn (fun t => B t (q t)) (Icc l r) :=
    (continuousOn_scalarNormalizedCompanion c hc hnz).clm_apply hq
  have hf (j : Fin (n + 1)) : MemLp (fun t => f t j) 2 μ := by
    have h₁ : MemLp (fun t => B t (q t) j) 2 μ :=
      (continuousOn_pi.mp hL j).memLp_top_restrict_Ioo.mono_exponent le_top
    apply h₁.add
    by_cases hj : j = Fin.last n
    · subst j
      simpa [g, scalarJetForcing] using Lp.memLp normedY
    · simp [g, scalarJetForcing, Pi.single_eq_of_ne hj]
  have hshift (t : ℝ) (j : Fin n) : f t j.castSucc = q t j.succ := by
    simp [f, g, B, scalarJetForcing, scalarNormalizedCompanion_apply_castSucc]
  have hinit : q l = v₀ := by
    simpa using heq l (left_mem_Icc.mpr hlr.le)
  obtain ⟨u, hu, htop⟩ := scalarSobolev_of_integral_jet hlr q f hq hf hshift (by simpa only [hinit] using heq)
  refine ⟨u, ?_, ?_⟩
  · apply Lp.ext
    have hRep : ∀ᵐ t ∂μ, ∀ j, SobolevInterval.deriv u j.castSucc t = q t j := by
      apply ae_all_iff.mpr
      intro j
      exact (scalarSobolevJet_apply_ae u j).symm.trans (ae_restrict_of_forall_mem measurableSet_Ioo
        (fun t ht => congrFun (hu (Ioo_subset_Icc_self ht)) j))
    filter_upwards [scalarSobolevExpression_apply_ae c hc u, htop, hRep,
      scalarCoefficientMultiplier_apply_ae (fun t => (c last t)⁻¹) ((hc last).inv₀ hnz) y,
      ae_restrict_mem measurableSet_Ioo] with t hA hT hRep hy ht
    rw [hA, Fin.sum_univ_castSucc, hT]
    simp only [f, B, g, Pi.add_apply, scalarJetForcing, Pi.single_eq_same,
      scalarNormalizedCompanion_apply_last, hRep]
    rw [show normedY t = _ from hy, mul_add, ← mul_assoc,
      mul_inv_cancel₀ (hnz t (Ioo_subset_Icc_self ht)), one_mul]
    have hz := hnz t (Ioo_subset_Icc_self ht)
    have hsum : c last t * (∑ j : Fin (n + 1), (c j.castSucc t / c last t) * q t j) =
        ∑ j : Fin (n + 1), c j.castSucc t * q t j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by field_simp [hz]
    rw [mul_neg, hsum]
    ring
  · funext j
    change scalarSobolevBoundaryTrace hlr u (Sum.inl j) = _
    rw [scalarSobolevBoundaryTrace_apply]
    exact (congrFun (hu (left_mem_Icc.mpr hlr.le)) j).trans (congrFun hinit j)

private theorem scalarSobolevJet_injective_on {u v : H}
    (h : EqOn (scalarSobolevJet u) (scalarSobolevJet v) (Icc l r)) : u = v := by
  apply SobolevMultiIndex.fnL_injective
  apply Lp.ext
  have h₁ := (scalarSobolevJet_apply_ae u 0).symm
  have h₂ := scalarSobolevJet_apply_ae v 0
  have hmid : (fun t => scalarSobolevJet u t 0) =ᵐ[μ] (fun t => scalarSobolevJet v t 0) :=
    ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => congrFun (h (Ioo_subset_Icc_self ht)) 0)
  exact h₁.trans (hmid.trans h₂)

/-- For fixed square-integrable forcing, the left endpoint jet determines
a unique Sobolev solution of the unrestricted scalar equation. -/
theorem scalarSobolev_initialValue_injective (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) {u v : H}
    (hF : scalarSobolevExpression c hc u = scalarSobolevExpression c hc v)
    (hI : scalarSobolevBoundaryTrace hlr u ∘ Sum.inl = scalarSobolevBoundaryTrace hlr v ∘ Sum.inl) :
    u = v := by
  have hinit : scalarSobolevJet u l = scalarSobolevJet v l := by
    funext j
    simpa only [Function.comp_apply, scalarSobolevBoundaryTrace_apply, Sum.elim_inl, scalarSobolevJet] using congrFun hI j
  let B := scalarNormalizedCompanion c
  let N := scalarCoefficientMultiplier (fun t => (c last t)⁻¹) ((hc last).inv₀ hnz)
  let g : ℝ → J := scalarJetForcing (N (scalarSobolevExpression c hc u))
  obtain ⟨_, _, _, hu⟩ := exists_linear_integral_ivp hlr.le B
    (continuousOn_scalarNormalizedCompanion c hc hnz) g
    (integrableOn_scalarJetForcing (N (scalarSobolevExpression c hc u))) (scalarSobolevJet u l)
  have h₁ := hu _ (continuousOn_scalarSobolevJet hlr u) (scalarSobolevJet_solves hlr c hc hnz u)
  have h₂ := hu _ (continuousOn_scalarSobolevJet hlr v)
    (by simpa only [B, g, N, hinit, hF] using scalarSobolevJet_solves hlr c hc hnz v)
  exact scalarSobolevJet_injective_on (h₁.trans h₂.symm)

end ScalarInitialValue

section ScalarSobolevRange

open Matrix

variable {n m : ℕ} {l r : ℝ}

local notation "H" => SobolevInterval (n + 1) l r
local notation "S" => IntervalL2 l r
local notation "J" => (Fin (n + 1) → ℝ)
local notation "last" => Fin.last (n + 1)

private def scalarTraceSide (hlr : l < r) (side : Fin (n + 1) → Fin (n + 1) ⊕ Fin (n + 1)) :
    H →L[ℝ] J :=
  ContinuousLinearMap.pi (fun j => (ContinuousLinearMap.proj (side j)).comp (scalarSobolevBoundaryTrace hlr))

/-- The scalar equation and its left initial jet give continuous linear
coordinates on the entire order-\(n+1\) Sobolev space. -/
def scalarSobolevInitialEquiv (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) : H ≃L[ℝ] S × J :=
  ContinuousLinearEquiv.ofBijective ((scalarSobolevExpression c hc).prod (scalarTraceSide hlr Sum.inl))
    (LinearMap.ker_eq_bot.mpr fun u v hv =>
      scalarSobolev_initialValue_injective hlr c hc hnz
        (congrArg Prod.fst hv) (congrArg Prod.snd hv))
    (LinearMap.range_eq_top.mpr fun yz => by
      obtain ⟨u, he, ht⟩ := exists_scalarSobolev_initialValue hlr c hc hnz yz.1 yz.2
      exact ⟨u, Prod.ext he ht⟩)

/-- The initial-value coordinates record the forcing and the left endpoint jet. -/
theorem scalarSobolevInitialEquiv_apply (hlr : l < r) (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (c j) (Icc l r)) (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) (u : H) :
    scalarSobolevInitialEquiv hlr c hc hnz u =
      (scalarSobolevExpression c hc u, scalarSobolevBoundaryTrace hlr u ∘ Sum.inl) :=
  rfl

/-- The boundary matrix applied to the Sobolev trace in (50). -/
def scalarSobolevBoundaryResidual (hlr : l < r)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) : H →L[ℝ] (Fin m → ℝ) :=
  (LinearMap.toContinuousLinearMap M.mulVecLin).comp (scalarSobolevBoundaryTrace hlr)

private theorem mem_scalarIntervalOperator_range_iff (A : H →L[ℝ] S) (W : Submodule ℝ H) {y : S} :
    y ∈ (scalarIntervalOperator A W).toFun.range ↔ ∃ u : W, A u.val = y := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, _, he⟩ := (mem_scalarIntervalOperator_graph_iff A W).mp
      ((scalarIntervalOperator A W).mem_graph x)
    exact ⟨u, he⟩
  · rintro ⟨u, rfl⟩
    have hr := (mem_scalarIntervalOperator_graph_iff A W).mpr ⟨u, rfl, rfl⟩
    obtain ⟨x, _, hx⟩ := (scalarIntervalOperator A W).mem_graph_iff.mp hr
    exact ⟨x, hx⟩

/-- **Exercise 28(d)** of [benIsrael2003generalized], Chapter 9.
A forcing is solvable precisely when the boundary residual of its
zero-initial-jet solution belongs to the image of the homogeneous boundary map. -/
theorem mem_constrainedScalarIntervalOperator_range_iff (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) (y : S) :
    let F := scalarSobolevInitialEquiv hlr c hc hnz
    let B := scalarSobolevBoundaryResidual hlr M
    y ∈ (constrainedScalarIntervalOperator hlr c hc M).toFun.range ↔
      ∃ z : J, B (F.symm (0, z)) = B (F.symm (y, 0)) := by
  dsimp only
  let F := scalarSobolevInitialEquiv hlr c hc hnz
  let A := scalarSobolevExpression c hc
  let W := scalarSobolevBoundarySpace hlr M
  let B := scalarSobolevBoundaryResidual hlr M
  change y ∈ (scalarIntervalOperator A W).toFun.range ↔ ∃ z : J, B (F.symm (0, z)) = B (F.symm (y, 0))
  rw [mem_scalarIntervalOperator_range_iff]
  have hsplit (y : S) (z : J) : F.symm (y, z) = F.symm (y, 0) + F.symm (0, z) := by
    rw [← map_add]
    simp
  constructor
  · rintro ⟨u, hu⟩
    let z := scalarTraceSide hlr Sum.inl u.val
    have hF : F u.val = (y, z) := Prod.ext hu rfl
    have he : F.symm (y, z) = u.val := by rw [← hF, F.symm_apply_apply]
    have hB : B u.val = 0 := u.2
    refine ⟨-z, ?_⟩
    have he₀ : (0, -z) = -((0, z) : S × J) := by simp
    rw [he₀, map_neg, map_neg]
    rw [← he, hsplit, map_add] at hB
    have he' : B (F.symm (0, z)) + B (F.symm (y, 0)) = 0 := by
      rw [add_comm]
      exact hB
    exact neg_eq_of_add_eq_zero_right he'
  · rintro ⟨z, hz⟩
    let u := F.symm (y, -z)
    have he₀ : (0, -z) = -((0, z) : S × J) := by simp
    have hu : B u = 0 := by
      change B (F.symm (y, -z)) = 0
      rw [hsplit, he₀, map_neg, map_add, map_neg, hz, add_neg_cancel]
    refine ⟨⟨u, hu⟩, ?_⟩
    exact congrArg Prod.fst (F.apply_symm_apply (y, -z))

/-- **Exercise 28(d)** of [benIsrael2003generalized], Chapter 9.
The constrained scalar differential operator has closed range. -/
theorem isClosed_range_constrainedScalarIntervalOperator (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    IsClosed ((constrainedScalarIntervalOperator hlr c hc M).toFun.range : Set S) := by
  let F := scalarSobolevInitialEquiv hlr c hc hnz
  let B := scalarSobolevBoundaryResidual hlr M
  let φ := B.comp (F.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ S J))
  let ψ := B.comp (F.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ S J))
  have h : ((constrainedScalarIntervalOperator hlr c hc M).toFun.range : Set S) =
      φ ⁻¹' (ψ.range : Set (Fin m → ℝ)) := by
    ext y
    exact mem_constrainedScalarIntervalOperator_range_iff hlr c hc hnz M y
  rw [h]
  exact (Submodule.closed_of_finiteDimensional ψ.range).preimage φ.continuous

/-- **Exercise 28(e)–(g)** of [benIsrael2003generalized], Chapter 9.
The carrier restriction is closed, injective, and has the entire operator
range. Its inverse is bounded, and the maximal inverse is bounded on the
full Hilbert space with null space the orthogonal complement of the range. -/
theorem constrainedScalarIntervalOperator_carrier_inverse (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    let L := constrainedScalarIntervalOperator hlr c hc M
    (restrictCarrier L).IsClosed ∧ (restrictCarrier L).ker = ⊥ ∧
      (restrictCarrier L).toFun.range = L.toFun.range ∧ IsBoundedOperator (restrictCarrier L).inverse ∧
      (maximalTsengInverse L).domain = ⊤ ∧ IsBoundedOperator (maximalTsengInverse L) ∧
      (maximalTsengInverse L).ker = L.toFun.rangeᗮ := by
  dsimp only
  let L := constrainedScalarIntervalOperator hlr c hc M
  have hL : L.IsClosed := isClosed_constrainedScalarIntervalOperator hlr c hc hnz M
  have hR : IsClosed (L.toFun.range : Set S) := isClosed_range_constrainedScalarIntervalOperator hlr c hc hnz M
  have hN : IsNormallySolvable L := ⟨hL, hR⟩
  exact ⟨restrictCarrier_isClosed L hL, restrictCarrier_ker L,
    restrictCarrier_range L (isDecomposable_of_isClosed L.ker_le_domain hL.isClosed_ker),
    (isNormallySolvable_iff L hL).1.mp hN,
    maximalTsengInverse_domain_eq_top_of_normallySolvable hN,
    (exercise_9_13 hL).mp hR, maximalTsengInverse_ker L⟩

end ScalarSobolevRange

section ScalarNullities

open Matrix

variable {n m : ℕ} {l r : ℝ}

local notation "H" => SobolevInterval (n + 1) l r
local notation "S" => IntervalL2 l r
local notation "J" => (Fin (n + 1) → ℝ)
local notation "last" => Fin.last (n + 1)

private theorem mem_scalarIntervalOperator_ker_iff (A : H →L[ℝ] S) (W : Submodule ℝ H) (x : S) :
    x ∈ (scalarIntervalOperator A W).ker ↔ ∃ u : W, SobolevInterval.deriv u.val 0 = x ∧ A u.val = 0 := by
  rw [LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨z, rfl, hz⟩
    have h := (scalarIntervalOperator A W).mem_graph z
    rw [hz] at h
    exact (mem_scalarIntervalOperator_graph_iff A W).mp h
  · rintro ⟨u, hx, hu⟩
    obtain ⟨z, hz, hz'⟩ := (scalarIntervalOperator A W).mem_graph_iff.mp
      ((mem_scalarIntervalOperator_graph_iff A W).mpr ⟨u, hx, hu⟩)
    exact ⟨z, hz.symm, hz'⟩

/-- **Exercise 28(b)** of [benIsrael2003generalized], Chapter 9.
The unrestricted null space is linearly equivalent to the space of all
left initial jets. -/
def freeScalarIntervalOperator_ker_equiv (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) : J ≃ₗ[ℝ] (freeScalarIntervalOperator c hc).ker := by
  let F := scalarSobolevInitialEquiv hlr c hc hnz
  let A := scalarSobolevExpression c hc
  let L := freeScalarIntervalOperator c hc
  let G : J →L[ℝ] H := F.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ S J)
  have hG (z : J) : A (G z) = 0 := congrArg Prod.fst (F.apply_symm_apply (0, z))
  let B := ((SobolevInterval.derivL (n + 1) l r 0).comp G).toLinearMap
  let P : J →ₗ[ℝ] L.ker := B.codRestrict L.ker fun z =>
    (mem_scalarIntervalOperator_ker_iff A ⊤ _).mpr ⟨⟨G z, Submodule.mem_top⟩, rfl, hG z⟩
  refine LinearEquiv.ofBijective P ⟨?_, ?_⟩
  · intro z w hz
    have h := congrArg (fun x : L.ker => (x : S)) hz
    have h' : G z = G w := SobolevMultiIndex.fnL_injective h
    exact congrArg Prod.snd (F.symm.injective h')
  · intro x
    obtain ⟨u, hu₀, huA⟩ := (mem_scalarIntervalOperator_ker_iff A ⊤ x.val).mp x.2
    let z := (F u.val).2
    have hz : F u.val = (0, z) := Prod.ext huA rfl
    have h' : G z = u.val := by
      change F.symm (0, z) = u.val
      rw [← hz, F.symm_apply_apply]
    refine ⟨z, Subtype.ext ?_⟩
    change SobolevInterval.deriv (G z) 0 = x.val
    rw [h', hu₀]

/-- The nullity in Exercise 28(b) is the order of the expression. -/
theorem finrank_ker_freeScalarIntervalOperator (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) :
    Module.finrank ℝ (freeScalarIntervalOperator c hc).ker = n + 1 := by
  rw [← (freeScalarIntervalOperator_ker_equiv hlr c hc hnz).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The unrestricted scalar expression is onto the entire interval Hilbert space. -/
theorem range_freeScalarIntervalOperator (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) :
    (freeScalarIntervalOperator c hc).toFun.range = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro y
  obtain ⟨u, h, _⟩ := exists_scalarSobolev_initialValue hlr c hc hnz y 0
  exact (mem_scalarIntervalOperator_range_iff (scalarSobolevExpression c hc) ⊤).mpr
    ⟨⟨u, Submodule.mem_top⟩, h⟩

/-- **Exercise 28(c)** of [benIsrael2003generalized], Chapter 9.
Requiring the boundary conditions can only reduce the null space. -/
theorem ker_constrainedScalarIntervalOperator_le (hlr : l < r) (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    (constrainedScalarIntervalOperator hlr c hc M).ker ≤ (freeScalarIntervalOperator c hc).ker := by
  intro x hx
  obtain ⟨u, hu₀, huA⟩ := (mem_scalarIntervalOperator_ker_iff _ _ x).mp hx
  exact (mem_scalarIntervalOperator_ker_iff _ _ x).mpr ⟨⟨u.val, Submodule.mem_top⟩, hu₀, huA⟩

/-- Both constrained nullities in Exercise 28(c) are bounded by the order.
For the Hilbert adjoint, the right boundary jet of the zero-left-jet
particular solution separates the orthogonal complement of the range. -/
theorem finrank_ker_constrainedScalarIntervalOperator (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    let L := constrainedScalarIntervalOperator hlr c hc M
    Module.finrank ℝ L.ker ≤ n + 1 ∧ Module.finrank ℝ L.adjoint.ker ≤ n + 1 := by
  dsimp only
  let L := constrainedScalarIntervalOperator hlr c hc M
  let F := scalarSobolevInitialEquiv hlr c hc hnz
  let R := scalarTraceSide (n := n) hlr Sum.inr
  let G : S →L[ℝ] H := F.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ S J)
  have hG (y : S) : F (G y) = (y, 0) := F.apply_symm_apply (y, 0)
  let K := freeScalarIntervalOperator_ker_equiv hlr c hc hnz
  let : Module.Finite ℝ (freeScalarIntervalOperator c hc).ker :=
    Module.Finite.of_surjective K.toLinearMap K.surjective
  refine ⟨(Submodule.finrank_mono (ker_constrainedScalarIntervalOperator_le hlr c hc M)).trans
    (finrank_ker_freeScalarIntervalOperator hlr c hc hnz).le, ?_⟩
  have hD : Dense (L.domain : Set S) := dense_constrainedScalarIntervalOperator hlr c hc M
  rw [show L.adjoint.ker = L.toFun.rangeᗮ from ker_adjoint_eq_orthogonal_range L hD]
  let P := ((R.comp G).toLinearMap).comp L.toFun.rangeᗮ.subtype
  have hinj : Function.Injective P := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hyP : P y = 0 := LinearMap.mem_ker.mp hy
    have hleft : scalarTraceSide (n := n) hlr Sum.inl (G y.val) = 0 := congrArg Prod.snd (hG y.val)
    have hright : R (G y.val) = 0 := hyP
    have hzero : scalarSobolevBoundaryTrace hlr (G y.val) = 0 := by
      funext j
      cases j with
      | inl j => exact congrFun hleft j
      | inr j => exact congrFun hright j
    have hGm : G y.val ∈ scalarSobolevBoundarySpace hlr M := by
      simp [mem_scalarSobolevBoundarySpace_iff, hzero]
    have hyR : y.val ∈ L.toFun.range := (mem_scalarIntervalOperator_range_iff _ _).mpr
      ⟨⟨G y.val, hGm⟩, congrArg Prod.fst (hG y.val)⟩
    apply Subtype.ext
    exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp y.2 y.val hyR)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using P.finrank_le_finrank_of_injective hinj

/-- The two orthogonal projection identities in **Exercise 28(g)**. -/
theorem constrainedScalarIntervalOperator_inverse_projections (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    let L := constrainedScalarIntervalOperator hlr c hc M
    let P := maximalTsengInverse L
    let hL := isClosed_constrainedScalarIntervalOperator hlr c hc hnz M
    letI := (isClosed_range_constrainedScalarIntervalOperator hlr c hc hnz M).completeSpace_coe
    let h := isTsengInverse_maximalTsengInverse_of_isClosed hL
    (∀ x : L.domain, P ⟨L x, h.range_le_domain ⟨x, rfl⟩⟩ = L.kerᗮ.starProjection x) ∧
      (∀ y : P.domain, L ⟨P y, h.inverse_range_le_domain ⟨y, rfl⟩⟩ = L.toFun.range.starProjection y) := by
  dsimp only
  let L := constrainedScalarIntervalOperator hlr c hc M
  have hL : L.IsClosed := isClosed_constrainedScalarIntervalOperator hlr c hc hnz M
  have hR : IsClosed (L.toFun.range : Set S) := isClosed_range_constrainedScalarIntervalOperator hlr c hc hnz M
  refine ⟨fun x => maximalTsengInverse_apply_image hL x, ?_⟩
  have hs := (theorem_2_projections L (isDecomposable_of_isClosed L.ker_le_domain hL.isClosed_ker).2).2
  have hclosed : L.toFun.range.topologicalClosure = L.toFun.range := by
    apply SetLike.coe_injective
    exact hR.closure_eq
  simpa only [hclosed] using hs

end ScalarNullities

section ScalarFormalAdjoint

variable {n : ℕ} {l r : ℝ}

local notation "S" => IntervalL2 l r
local notation "last" => Fin.last (n + 1)

/-- The coefficients of the formal adjoint in **Exercise 28(b)**, obtained
by expanding each term `(-D)^k (cₖ ·)` by the Leibniz formula. -/
def scalarFormalAdjointCoefficients (l r : ℝ) (c : Fin (n + 2) → ℝ → ℝ)
    (j : Fin (n + 2)) (t : ℝ) : ℝ :=
  ∑ k : Fin (n + 2), if j ≤ k then
    (-1) ^ k.val * (k.val.choose j.val : ℝ) *
      iteratedDerivWithin (k.val - j.val) (c k) (Icc l r) t else 0

/-- The differentiability assumptions on the original coefficients give continuous formal adjoint coefficients. -/
theorem continuousOn_scalarFormalAdjointCoefficients (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContDiffOn ℝ j.val (c j) (Icc l r)) (j : Fin (n + 2)) :
    ContinuousOn (scalarFormalAdjointCoefficients l r c j) (Icc l r) := by
  unfold scalarFormalAdjointCoefficients
  apply continuousOn_finsetSum
  intro k _
  by_cases hj : j ≤ k
  · simp only [ite_eq_left hj]
    have hh : (↑(k.val - j.val) : WithTop ℕ∞) ≤ k.val := by exact_mod_cast Nat.sub_le _ _
    exact continuousOn_const.mul ((hc k).continuousOn_iteratedDerivWithin hh (uniqueDiffOn_Icc hlr))
  · simp [hj, continuousOn_const]

/-- The leading formal adjoint coefficient differs by the sign of the differential order. -/
theorem scalarFormalAdjointCoefficients_leading (c : Fin (n + 2) → ℝ → ℝ) (t : ℝ) :
    scalarFormalAdjointCoefficients l r c last t = (-1) ^ (n + 1) * c last t := by
  classical
  unfold scalarFormalAdjointCoefficients
  rw [Finset.sum_eq_single last]
  · simp [iteratedDerivWithin_zero]
  · intro k _ hk
    exact ite_eq_right (fun h => hk (le_antisymm (Fin.le_last k) h))
  · simp

/-- The maximal realization of the formal differential adjoint has the
same Sobolev order as the original expression. -/
abbrev freeScalarFormalAdjointOperator (hlr : l < r) (c : Fin (n + 2) → ℝ → ℝ)
    (hc : ∀ j, ContDiffOn ℝ j.val (c j) (Icc l r)) : S →ₗ.[ℝ] S :=
  freeScalarIntervalOperator (scalarFormalAdjointCoefficients l r c)
    (continuousOn_scalarFormalAdjointCoefficients hlr c hc)

/-- The unrestricted realization of the formal adjoint has nullity equal
to the order in Exercise 28(b). -/
theorem finrank_ker_freeScalarFormalAdjointOperator (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContDiffOn ℝ j.val (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) :
    Module.finrank ℝ (freeScalarFormalAdjointOperator hlr c hc).ker = n + 1 := by
  apply finrank_ker_freeScalarIntervalOperator hlr
  intro t ht
  rw [scalarFormalAdjointCoefficients_leading]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (hnz t ht)

/-- The Hilbert adjoint of the unrestricted operator has trivial null
space. The maximal realization of the formal adjoint is the different
operator meant by the second dimension assertion in Exercise 28(b). -/
theorem ker_adjoint_freeScalarIntervalOperator (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0) :
    (freeScalarIntervalOperator c hc).adjoint.ker = ⊥ := by
  let L := freeScalarIntervalOperator c hc
  have hD : Dense (L.domain : Set S) := by
    let M : Matrix (Fin 0) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ := 0
    apply (dense_constrainedScalarIntervalOperator hlr c hc M).mono
    intro x hx
    let lOp := constrainedScalarIntervalOperator hlr c hc M
    have hg : (x, lOp ⟨x, hx⟩) ∈ lOp.graph := lOp.mem_graph ⟨x, hx⟩
    obtain ⟨u, hu, _⟩ := (mem_scalarIntervalOperator_graph_iff _ _).mp hg
    exact hu ▸ scalarSobolevGraph_domain_of_lift _ _ ⟨u.val, Submodule.mem_top⟩
  rw [ker_adjoint_eq_orthogonal_range L hD, range_freeScalarIntervalOperator hlr c hc hnz,
    Submodule.top_orthogonal_eq_bot]

end ScalarFormalAdjoint

section ScalarGreenAlgebra

open Matrix

variable {n m : ℕ} {l r : ℝ}

local notation "H" => SobolevInterval (n + 1) l r
local notation "S" => IntervalL2 l r
local notation "J" => (Fin (n + 1) → ℝ)
local notation "last" => Fin.last (n + 1)

/-- The Wronskian matrix of the fundamental scalar solutions in (51).
Column `j` is the jet of the `j`th solution at the stated time. -/
def scalarWronskian (l r : ℝ) (basis : Fin (n + 1) → ℝ → ℝ) (t : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => iteratedDerivWithin i.val (basis j) (Icc l r) t

/-- The causal Wronskian kernel in **Exercise 29**, Equation (51). The
diagonal value is chosen from the causal branch. -/
def scalarWronskianGreenKernel (l r : ℝ) (c : Fin (n + 2) → ℝ → ℝ)
    (basis : Fin (n + 1) → ℝ → ℝ) (s t : ℝ) : ℝ :=
  if t ≤ s then
    ∑ j : Fin (n + 1), basis j s *
      ((scalarWronskian l r basis t).updateCol j (Pi.single (Fin.last n) 1)).det /
        (c last t * (scalarWronskian l r basis t).det)
  else 0

/-- Cramer's rule identifies (51) with the scalar component of the causal
fundamental propagation kernel. -/
theorem scalarWronskianGreenKernel_eq_propagator
    (c : Fin (n + 2) → ℝ → ℝ) (basis : Fin (n + 1) → ℝ → ℝ) (s t : ℝ)
    (hW : IsUnit (scalarWronskian l r basis t).det) :
    scalarWronskianGreenKernel l r c basis s t =
      if t ≤ s then
        (∑ j : Fin (n + 1), basis j s *
          ((scalarWronskian l r basis t)⁻¹ *ᵥ Pi.single (Fin.last n) 1) j) / c last t
      else 0 := by
  unfold scalarWronskianGreenKernel
  split <;> rename_i h
  · rw [div_eq_inv_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    let X := scalarWronskian l r basis t
    let e : J := Pi.single (Fin.last n) 1
    have hcoe : (X.updateCol j e).det = X.det * (X⁻¹ *ᵥ e) j := by
      rw [← Matrix.cramer_apply]
      exact (congrFun (Matrix.det_smul_inv_mulVec_eq_cramer X e hW) j).symm
    change basis j s * (X.updateCol j e).det / (c last t * X.det) =
      (c last t)⁻¹ * (basis j s * (X⁻¹ *ᵥ e) j)
    rw [hcoe, div_eq_mul_inv, mul_inv]
    calc
      _ = (c last t)⁻¹ * (basis j s * (X⁻¹ *ᵥ e) j) * (X.det * X.det⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hW.ne_zero, mul_one]
  · rfl

/-- The homogeneous boundary matrix (Mwidehat X) from (54) in left
initial-jet coordinates. -/
def scalarInitialBoundaryMatrix (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    Matrix (Fin m) (Fin (n + 1)) ℝ :=
  let F := scalarSobolevInitialEquiv hlr c hc hnz
  LinearMap.toMatrix' ((scalarSobolevBoundaryResidual hlr M).comp
    (F.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ S J))).toLinearMap

/-- Applying the boundary matrix to the homogeneous initial-value solution gives its boundary residual. -/
theorem scalarInitialBoundaryMatrix_mulVec (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) (z : J) :
    scalarInitialBoundaryMatrix hlr c hc hnz M *ᵥ z =
      scalarSobolevBoundaryResidual hlr M ((scalarSobolevInitialEquiv hlr c hc hnz).symm (0, z)) := by
  unfold scalarInitialBoundaryMatrix
  rw [LinearMap.toMatrix'_mulVec]
  rfl

/-- The particular scalar solution corrected by the boundary coefficient
formula (55). Its first Sobolev component is the underlying element of
the interval Hilbert space. -/
def scalarBoundaryCorrectedSolution (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (U : Matrix (Fin (n + 1)) (Fin m) ℝ) : S →L[ℝ] H :=
  let F := scalarSobolevInitialEquiv hlr c hc hnz
  let B := scalarSobolevBoundaryResidual hlr M
  let G := F.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ S J)
  let X := F.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ S J)
  G - X.comp ((LinearMap.toContinuousLinearMap U.mulVecLin).comp (B.comp G))

/-- **Exercise 29**, Equations (52)–(55). A compatible forcing has a
solution obtained by correcting the zero initial-jet solution with
a homogeneous solution. Any inner inverse of the homogeneous boundary
matrix produces the correct boundary residual. -/
theorem scalarBoundaryCorrectedSolution_spec (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (U : Matrix (Fin (n + 1)) (Fin m) ℝ)
    (hU : (scalarInitialBoundaryMatrix hlr c hc hnz M).IsInnerInverse U)
    (y : S) (hy : y ∈ (constrainedScalarIntervalOperator hlr c hc M).toFun.range) :
    let u := scalarBoundaryCorrectedSolution hlr c hc hnz M U y
    u ∈ scalarSobolevBoundarySpace hlr M ∧ scalarSobolevExpression c hc u = y := by
  dsimp only
  let F := scalarSobolevInitialEquiv hlr c hc hnz
  let B := scalarSobolevBoundaryResidual hlr M
  let G := F.symm (y, 0)
  let a := U.mulVec (B G)
  have hsplit : scalarBoundaryCorrectedSolution hlr c hc hnz M U y = F.symm (y, -a) := by
    change G - F.symm (0, a) = F.symm (y, -a)
    rw [← map_sub]
    simp
  rw [hsplit]
  refine ⟨?_, congrArg Prod.fst (F.apply_symm_apply (y, -a))⟩
  obtain ⟨z, hz⟩ := (mem_constrainedScalarIntervalOperator_range_iff hlr c hc hnz M y).mp hy
  have hRange : ∃ v : J, (scalarInitialBoundaryMatrix hlr c hc hnz M).mulVec v = B G := by
    exact ⟨z, (scalarInitialBoundaryMatrix_mulVec hlr c hc hnz M z).trans hz⟩
  have he := boundaryCorrection_of_innerInverse hU hRange
  rw [scalarInitialBoundaryMatrix_mulVec hlr c hc hnz M] at he
  change B (F.symm (y, -a)) = 0
  rw [show (y, -a) = (y, 0) + (0, -a) by simp, map_add, map_add]
  exact he

/-- After projecting the forcing onto the constrained range, the boundary
correction (55) followed by removal of the constrained null component is
the Moore–Penrose inverse of the scalar differential operator. -/
theorem scalarBoundaryCorrectedSolution_maximalInverse (hlr : l < r)
    (c : Fin (n + 2) → ℝ → ℝ) (hc : ∀ j, ContinuousOn (c j) (Icc l r))
    (hnz : ∀ t ∈ Icc l r, c last t ≠ 0)
    (M : Matrix (Fin m) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (U : Matrix (Fin (n + 1)) (Fin m) ℝ)
    (hU : (scalarInitialBoundaryMatrix hlr c hc hnz M).IsInnerInverse U)
    (y : (maximalTsengInverse (constrainedScalarIntervalOperator hlr c hc M)).domain) :
    let L := constrainedScalarIntervalOperator hlr c hc M
    letI := (isClosed_range_constrainedScalarIntervalOperator hlr c hc hnz M).completeSpace_coe
    maximalTsengInverse L y = L.kerᗮ.starProjection
      (SobolevInterval.deriv (scalarBoundaryCorrectedSolution hlr c hc hnz M U
        (L.toFun.range.starProjection y.val)) 0) := by
  dsimp only
  let L := constrainedScalarIntervalOperator hlr c hc M
  have hL : IsNormallySolvable L := ⟨isClosed_constrainedScalarIntervalOperator hlr c hc hnz M,
    isClosed_range_constrainedScalarIntervalOperator hlr c hc hnz M⟩
  let G := ((SobolevInterval.derivL (n + 1) l r 0).comp
    (scalarBoundaryCorrectedSolution hlr c hc hnz M U)).toLinearMap.comp L.toFun.range.subtype
  have hG : IsInnerInverseOnRange L G := by
    intro f
    obtain ⟨hm, hy⟩ := scalarBoundaryCorrectedSolution_spec hlr c hc hnz M U hU f.val f.2
    exact (mem_scalarIntervalOperator_graph_iff _ _).mpr
      ⟨⟨scalarBoundaryCorrectedSolution hlr c hc hnz M U f.val, hm⟩, rfl, hy⟩
  exact maximalInverse_eq_project_innerInverse hL G hG y

end ScalarGreenAlgebra

section SquareGradient

local notation "μ□" => Measure.prod halfRangeMeasure halfRangeMeasure

section SquareSpectralProblem

open EuclideanSpace TopologicalSpace
open scoped Laplacian

local notation "V₂" => EuclideanSpace ℝ (Fin 2)
local notation "Iπ" => Set.Icc (0 : ℝ) Real.pi
local notation "Jπ" => Set.Ioo (0 : ℝ) Real.pi

private def squareCoordinateEquiv : V₂ ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.finTwoArrow (α := ℝ))

private theorem squareCoordinateEquiv_apply (x : V₂) :
    squareCoordinateEquiv x = (x 0, x 1) := rfl

private theorem squareCoordinateEquiv_preserving :
    MeasurePreserving squareCoordinateEquiv volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp
    ((PiLp.volume_preserving_toLp (Fin 2)).symm (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))

/-- The open square $(0,\pi)^2$ for the Dirichlet boundary condition. -/
def dirichletSquare : Opens V₂ :=
  ⟨squareCoordinateEquiv ⁻¹' (Jπ ×ˢ Jπ), by
    apply (isOpen_Ioo.prod isOpen_Ioo).preimage
    rw [show (squareCoordinateEquiv : V₂ → ℝ × ℝ) = fun x => (x 0, x 1) from rfl]
    fun_prop⟩

private theorem measurableEmbedding_squareInclusion :
    MeasurableEmbedding (fun p : Iπ × Iπ =>
      squareCoordinateEquiv.symm (p.1.val, p.2.val)) :=
  squareCoordinateEquiv.symm.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe measurableSet_Icc).prodMap
      (MeasurableEmbedding.subtype_coe measurableSet_Icc))

private theorem squareInclusion_preserving :
    MeasurePreserving (fun p : Iπ × Iπ => squareCoordinateEquiv.symm (p.1.val, p.2.val))
      μ□ (volume.restrict (dirichletSquare : Set V₂)) := by
  have hsub : MeasurePreserving (Subtype.val : Iπ → ℝ)
      halfRangeMeasure (volume.restrict Jπ) :=
    ⟨measurable_subtype_coe, by
      rw [halfRangeMeasure, map_comap_subtype_coe measurableSet_Icc, restrict_Ioo_eq_restrict_Icc]⟩
  have hsub₂ : MeasurePreserving (fun p : Iπ × Iπ => (p.1.val, p.2.val)) μ□
      ((volume.restrict Jπ).prod (volume.restrict Jπ)) := hsub.prod hsub
  rw [Measure.prod_restrict] at hsub₂
  have he := squareCoordinateEquiv_preserving.restrict_preimage
    (s := Jπ ×ˢ Jπ) (measurableSet_Ioo.prod measurableSet_Ioo)
  exact (he.symm squareCoordinateEquiv).comp hsub₂

/-- The measure-preserving product coordinates give a linear isometry on square-integrable functions. -/
def squareL2Equiv : Lp ℝ 2 (volume.restrict (dirichletSquare : Set V₂)) ≃ₗᵢ[ℝ]
    Lp ℝ 2 μ□ := by
  let f (p : Iπ × Iπ) := squareCoordinateEquiv.symm (p.1.val, p.2.val)
  let T := Lp.compMeasurePreservingₗᵢ ℝ (E := ℝ) (p := 2) f squareInclusion_preserving
  refine LinearIsometryEquiv.ofSurjective T ?_
  intro u
  let g := (Lp.aestronglyMeasurable u).mk u
  have hm : Measurable g := (Lp.aestronglyMeasurable u).stronglyMeasurable_mk.measurable
  have hg : (fun p => u p) =ᵐ[μ□] g := (Lp.aestronglyMeasurable u).ae_eq_mk
  obtain ⟨v, hv, he⟩ := measurableEmbedding_squareInclusion.exists_measurable_extend hm
    (fun _ => ⟨(0 : ℝ)⟩)
  have hV : MemLp v 2 (volume.restrict (dirichletSquare : Set V₂)) := by
    rw [← squareInclusion_preserving.map_eq, measurableEmbedding_squareInclusion.memLp_map_measure_iff,
      he]
    exact (memLp_congr_ae hg).mp (Lp.memLp u)
  refine ⟨hV.toLp _, ?_⟩
  change Lp.compMeasurePreserving f squareInclusion_preserving (hV.toLp v) = u
  rw [Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  exact (MemLp.coeFn_toLp (hV.comp_measurePreserving squareInclusion_preserving)).trans
    (he ▸ hg.symm)

private theorem squareL2Equiv_apply_ae
    (u : Lp ℝ 2 (volume.restrict (dirichletSquare : Set V₂))) :
    (fun p => squareL2Equiv u p) =ᵐ[μ□]
      fun p : Iπ × Iπ => u (squareCoordinateEquiv.symm (p.1.val, p.2.val)) :=
  Lp.coeFn_compMeasurePreserving u squareInclusion_preserving

/-- The smooth normalized product sine mode on the Euclidean square. -/
def squareSineMode (j : ℕ × ℕ) (x : V₂) : ℝ :=
  (2 / Real.pi) * Real.sin ((j.1 + 1 : ℝ) * x 0) * Real.sin ((j.2 + 1 : ℝ) * x 1)

private theorem squareSineMode_contDiff (j : ℕ × ℕ) :
    ContDiff ℝ ⊤ (squareSineMode j) := by unfold squareSineMode; fun_prop

private theorem squareSineMode_zero_frontier (j : ℕ × ℕ) :
    EqOn (squareSineMode j) 0 (frontier (dirichletSquare : Set V₂)) := by
  intro x hx
  have hsub : closure (dirichletSquare : Set V₂) ⊆ squareCoordinateEquiv ⁻¹' (Iπ ×ˢ Iπ) := by
    apply closure_minimal
    · intro z hz
      exact ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩
    · apply (isClosed_Icc.prod isClosed_Icc).preimage
      rw [show (squareCoordinateEquiv : V₂ → ℝ × ℝ) = fun x => (x 0, x 1) from rfl]
      fun_prop
  have hmem : x 0 ∈ Iπ ∧ x 1 ∈ Iπ := hsub hx.1
  have hnot : ¬ (x 0 ∈ Jπ ∧ x 1 ∈ Jπ) := by
    change x ∉ (dirichletSquare : Set V₂)
    have hO : IsOpen (dirichletSquare : Set V₂) := dirichletSquare.isOpen
    exact fun he => hx.2 (hO.interior_eq.symm ▸ he)
  have he : x 0 = 0 ∨ x 0 = Real.pi ∨ x 1 = 0 ∨ x 1 = Real.pi := by
    by_contra! hn
    exact hnot ⟨⟨lt_of_le_of_ne hmem.1.1 hn.1.symm, lt_of_le_of_ne hmem.1.2 hn.2.1⟩,
      ⟨lt_of_le_of_ne hmem.2.1 hn.2.2.1.symm, lt_of_le_of_ne hmem.2.2 hn.2.2.2⟩⟩
  change squareSineMode j x = 0
  have hs (n : ℕ) : Real.sin ((n + 1 : ℝ) * Real.pi) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.sin_nat_mul_pi (n + 1)
  rcases he with h0 | h0 | h0 | h0 <;> simp [squareSineMode, h0, hs]

private theorem squareSineMode_laplacian (j : ℕ × ℕ) (x : V₂) :
    -Δ (squareSineMode j) x = squareSineEigenvalue j * squareSineMode j x := by
  let P (i : Fin 2) : V₂ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i
  let a : ℝ := j.1 + 1
  let b : ℝ := j.2 + 1
  let c : ℝ := 2 / Real.pi
  let s (i : Fin 2) (k : ℝ) (y : V₂) := Real.sin (k * y i)
  let r (i : Fin 2) (k : ℝ) (y : V₂) := Real.cos (k * y i)
  have hs (i : Fin 2) (k : ℝ) (y : V₂) :
      HasFDerivAt (s i k) ((k * r i k y) • P i) y := by
    have hf : HasFDerivAt (fun z : V₂ => k * z i) (k • P i) y :=
      ((P i).hasFDerivAt (x := y)).const_mul k
    simpa only [s, r, smul_smul, mul_comm] using hf.sin
  have hr (i : Fin 2) (k : ℝ) (y : V₂) :
      HasFDerivAt (r i k) ((-k * s i k y) • P i) y := by
    have hf : HasFDerivAt (fun z : V₂ => k * z i) (k • P i) y :=
      ((P i).hasFDerivAt (x := y)).const_mul k
    have he : -Real.sin (k * y i) * k = -k * s i k y := by dsimp [s]; ring
    simpa only [r, smul_smul, he] using hf.cos
  have h1 (y : V₂) : fderiv ℝ (squareSineMode j) y (EuclideanSpace.single 0 1) =
      c * a * r 0 a y * s 1 b y := by
    have hh := (((hs 0 a y).mul (hs 1 b y)).const_smul c).fderiv
    have he : c • (s 0 a * s 1 b) = squareSineMode j := by
      funext z
      change c * (s 0 a z * s 1 b z) = squareSineMode j z
      rw [← mul_assoc, squareSineMode]
    rw [he] at hh
    rw [hh]
    simp [P, PiLp.proj_apply, smul_eq_mul]
    ring
  have h2 (y : V₂) : fderiv ℝ (squareSineMode j) y (EuclideanSpace.single 1 1) =
      c * b * s 0 a y * r 1 b y := by
    have hh := (((hs 0 a y).mul (hs 1 b y)).const_smul c).fderiv
    have he : c • (s 0 a * s 1 b) = squareSineMode j := by
      funext z
      change c * (s 0 a z * s 1 b z) = squareSineMode j z
      rw [← mul_assoc, squareSineMode]
    rw [he] at hh
    rw [hh]
    simp [P, PiLp.proj_apply, smul_eq_mul]
    ring
  have hd₁ : fderiv ℝ (fun y => c * a * r 0 a y * s 1 b y) x (EuclideanSpace.single 0 1) =
      -(a ^ 2) * squareSineMode j x := by
    have hh := (((hr 0 a x).const_smul (c * a)).mul (hs 1 b x)).fderiv
    change fderiv ℝ ((c * a) • r 0 a * s 1 b) x _ = _
    rw [hh]
    simp [P, PiLp.proj_apply, smul_eq_mul, a, b, c, s, r, squareSineMode]
    ring
  have hd₂ : fderiv ℝ (fun y => c * b * s 0 a y * r 1 b y) x (EuclideanSpace.single 1 1) =
      -(b ^ 2) * squareSineMode j x := by
    have hh := (((hs 0 a x).const_smul (c * b)).mul (hr 1 b x)).fderiv
    change fderiv ℝ ((c * b) • s 0 a * r 1 b) x _ = _
    rw [hh]
    simp [P, PiLp.proj_apply, smul_eq_mul, a, b, c, s, r, squareSineMode]
    ring
  rw [Elliptic.laplacian_eq_sum_fderiv_fderiv (Ω := (⊤ : Opens V₂))
    (squareSineMode_contDiff j |>.of_le (by norm_num) |>.contDiffOn) (by simp),
    Fin.sum_univ_two, funext h1, funext h2, hd₁, hd₂]
  change -(-(a ^ 2) * _ + -(b ^ 2) * _) = (a ^ 2 + b ^ 2) * _
  ring

private theorem isBounded_dirichletSquare : Bornology.IsBounded (dirichletSquare : Set V₂) := by
  apply Metric.isBounded_closedBall (x := (0 : V₂)) (r := 2 * Real.pi) |>.subset
  intro x hx
  have hx' : x 0 ∈ Jπ ∧ x 1 ∈ Jπ := hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have h0 : ‖x 0‖ ≤ Real.pi := by
    rw [Real.norm_of_nonneg hx'.1.1.le]
    exact hx'.1.2.le
  have h1 : ‖x 1‖ ≤ Real.pi := by
    rw [Real.norm_of_nonneg hx'.2.1.le]
    exact hx'.2.2.le
  have hn : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  nlinarith [norm_nonneg x, norm_nonneg (x 0), norm_nonneg (x 1), Real.pi_pos,
    mul_nonneg (sub_nonneg.mpr h0) (add_nonneg (norm_nonneg (x 0)) Real.pi_pos.le),
    mul_nonneg (sub_nonneg.mpr h1) (add_nonneg (norm_nonneg (x 1)) Real.pi_pos.le)]

local notation "ν□" => Measure.restrict (volume : Measure V₂) (dirichletSquare : Set V₂)

private theorem squareSineMode_memLp (j : ℕ × ℕ) : MemLp (squareSineMode j) 2 ν□ := by
  let : IsFiniteMeasure ν□ := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact isBounded_dirichletSquare.measure_lt_top
  apply MemLp.of_bound (squareSineMode_contDiff j).continuous.aestronglyMeasurable
    (2 / Real.pi)
  filter_upwards with x
  change ‖(2 / Real.pi) * Real.sin ((j.1 + 1) * x 0) *
    Real.sin ((j.2 + 1) * x 1)‖ ≤ 2 / Real.pi
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ 2 / Real.pi by positivity)]
  calc
    _ ≤ (2 / Real.pi) * 1 * 1 := by
      gcongr <;> exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    _ = _ := by rw [mul_one, mul_one]

/-- The normalized double sine mode in the ambient Hilbert space of the
Dirichlet square. -/
def squareDirichletMode (j : ℕ × ℕ) : Lp ℝ 2 ν□ :=
  (squareSineMode_memLp j).toLp _

/-- The square Dirichlet modes become the product sine basis under the
measure-preserving identification with the product of the two intervals. -/
theorem squareL2Equiv_dirichletMode (j : ℕ × ℕ) :
    squareL2Equiv (squareDirichletMode j) = squareSineBasis j := by
  apply Lp.ext
  refine (squareL2Equiv_apply_ae (squareDirichletMode j)).trans ?_
  have he := squareInclusion_preserving.quasiMeasurePreserving.ae
    (MemLp.coeFn_toLp (squareSineMode_memLp j))
  filter_upwards [he, squareSineBasis_apply_ae j] with p hp hq
  rw [squareDirichletMode, hp, hq]
  have h := squareCoordinateEquiv.apply_symm_apply (p.1.val, p.2.val)
  rw [squareCoordinateEquiv_apply] at h
  have h₁ := Prod.mk.inj h
  rw [squareSineMode, h₁.1, h₁.2]

/-- **Exercise 27(d)** of [benIsrael2003generalized], Chapter 9.
Each double sine mode is in the domain of the weak Dirichlet Laplacian
and has its stated eigenvalue. -/
theorem squareDirichletMode_eigen (j : ℕ × ℕ) :
    (squareDirichletMode j, squareSineEigenvalue j • squareDirichletMode j) ∈
      (dirichletLaplacian dirichletSquare).graph := by
  let u := squareSineMode j
  let lam := squareSineEigenvalue j
  let g := squareDirichletMode j
  let F := (lam + 1) • u
  have hMem := (squareSineMode_memLp j).const_smul (lam + 1)
  have hEq (x : V₂) (_ : x ∈ dirichletSquare) : -Δ u x + u x = F x := by
    change -Δ (squareSineMode j) x + squareSineMode j x = _
    rw [squareSineMode_laplacian]
    change lam * u x + u x = (lam + 1) * u x
    ring
  have hc : ContDiff ℝ 2 u := (squareSineMode_contDiff j).of_le (by norm_num)
  obtain ⟨U, hU, heU, hGal⟩ := Elliptic.isGalerkinSolution_laplace_of_classical dirichletSquare
    isBounded_dirichletSquare (hc.contDiffOn.contDiffOnClosure dirichletSquare.isOpen)
    hc.continuous.continuousOn
    (squareSineMode_zero_frontier j) hMem hEq
  have h₀ : SobolevMultiIndex.weakDeriv U 0 = g :=
    Lp.ext (heU.trans (MemLp.coeFn_toLp (squareSineMode_memLp j)).symm)
  have hF : hMem.toLp F = (lam + 1) • g :=
    MemLp.toLp_const_smul (lam + 1) (squareSineMode_memLp j)
  have hForm (v : SobolevEuclidean 2 1 2 dirichletSquare)
      (hv : v ∈ SobolevEuclideanZero 2 1 2 dirichletSquare) :
      Elliptic.dirichletForm dirichletSquare U v = Elliptic.load dirichletSquare (lam • g) v := by
    have h := hGal.2 v hv
    rw [Elliptic.laplaceForm_apply_eq_dirichletForm_add_weakDeriv, h₀, hF,
      Elliptic.load_apply_inner, real_inner_smul_left] at h
    rw [Elliptic.load_apply_inner, real_inner_smul_left]
    linarith
  have hd : g ∈ (dirichletLaplacian dirichletSquare).domain := ⟨U, hU, h₀, lam • g, hForm⟩
  exact (dirichletLaplacian dirichletSquare).mem_graph_iff.mpr
    ⟨⟨g, hd⟩, rfl, dirichletLaplacian_apply_unique ⟨g, hd⟩ hU h₀ hForm⟩

/-- The integral inverse transported to the ambient square Hilbert space. -/
def squareDirichletGreenOperator : Lp ℝ 2 ν□ →L[ℝ] Lp ℝ 2 ν□ :=
  squareL2Equiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((IntegralOperator.l2KernelCLM (Lp.memLp squareSineGreenKernel)).comp
      squareL2Equiv.toLinearIsometry.toContinuousLinearMap)

private theorem squareDirichletGreenOperator_repr (f : Lp ℝ 2 ν□) (j : ℕ × ℕ) :
    squareSineBasis.repr (squareL2Equiv (squareDirichletGreenOperator f)) j =
      (squareSineEigenvalue j)⁻¹ * squareSineBasis.repr (squareL2Equiv f) j := by
  simp only [squareDirichletGreenOperator, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply]
  exact squareSineGreenKernel_action_repr _ j

private theorem squareDirichletGreenOperator_mode (j : ℕ × ℕ) :
    squareDirichletGreenOperator (squareDirichletMode j) =
      (squareSineEigenvalue j)⁻¹ • squareDirichletMode j := by
  apply squareL2Equiv.injective
  apply squareSineBasis.repr.injective
  ext i
  rw [squareDirichletGreenOperator_repr, map_smul, map_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, squareL2Equiv_dirichletMode, squareSineBasis.repr_apply_apply]
  classical
  rw [orthonormal_iff_ite.mp squareSineBasis.orthonormal]
  by_cases he : i = j
  · rw [he]
  · simp [he]

private theorem hasSum_squareDirichletMode_repr (f : Lp ℝ 2 ν□) :
    HasSum (fun j : ℕ × ℕ => squareSineBasis.repr (squareL2Equiv f) j • squareDirichletMode j) f := by
  have h := (squareSineBasis.hasSum_repr (squareL2Equiv f)).mapL
    squareL2Equiv.symm.toLinearIsometry.toContinuousLinearMap
  have h₁ (j : ℕ × ℕ) : squareL2Equiv.symm (squareSineBasis j) = squareDirichletMode j := by
    rw [← squareL2Equiv_dirichletMode, LinearIsometryEquiv.symm_apply_apply]
  simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, map_smul, h₁,
    LinearIsometryEquiv.symm_apply_apply] using h

/-- **Exercise 27(d)** of [benIsrael2003generalized], Chapter 9.
The operator integrating the double sine Green series is an inverse of the
weak Dirichlet Laplacian on the entire square-integrable forcing space. -/
theorem squareDirichletGreenOperator_rightInverse (f : Lp ℝ 2 ν□) :
    (squareDirichletGreenOperator f, f) ∈ (dirichletLaplacian dirichletSquare).graph := by
  let L := dirichletLaplacian dirichletSquare
  let C := squareDirichletGreenOperator
  let ξ (j : ℕ × ℕ) := squareSineBasis.repr (squareL2Equiv f) j
  have ht := hasSum_squareDirichletMode_repr f
  have hu := ht.mapL C
  have hSum := Filter.Tendsto.prodMk_nhds hu ht
  apply (dirichletLaplacian_isClosed (Ω := dirichletSquare)).mem_of_tendsto hSum
  apply Filter.Eventually.of_forall
  intro s
  have hs : ((∑ j ∈ s, C (ξ j • squareDirichletMode j)), ∑ j ∈ s, ξ j • squareDirichletMode j) =
      ∑ j ∈ s, (C (ξ j • squareDirichletMode j), ξ j • squareDirichletMode j) := by
    apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  change ((∑ j ∈ s, C (ξ j • squareDirichletMode j)), ∑ j ∈ s, ξ j • squareDirichletMode j) ∈ L.graph
  rw [hs]
  apply L.graph.sum_mem
  intro j _
  have hmem := L.graph.smul_mem (ξ j * (squareSineEigenvalue j)⁻¹) (squareDirichletMode_eigen j)
  change (C (ξ j • squareDirichletMode j), ξ j • squareDirichletMode j) ∈ L.graph
  rw [map_smul, squareDirichletGreenOperator_mode, smul_smul]
  change ((ξ j * (squareSineEigenvalue j)⁻¹) • squareDirichletMode j, _) ∈ L.graph at hmem
  have hz : (ξ j * (squareSineEigenvalue j)⁻¹) •
      (squareSineEigenvalue j • squareDirichletMode j) = ξ j • squareDirichletMode j := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ (squareSineEigenvalue_pos j).ne', mul_one]
  simpa only [Prod.smul_mk, hz] using hmem

/-- **Exercise 27(d)** of [benIsrael2003generalized], Chapter 9.
The Green integral recovers every solution in the Dirichlet Laplacian
domain from its forcing. -/
theorem squareDirichletGreenOperator_leftInverse
    (u : (dirichletLaplacian dirichletSquare).domain) :
    squareDirichletGreenOperator (dirichletLaplacian dirichletSquare u) = u := by
  let L := dirichletLaplacian dirichletSquare
  apply squareL2Equiv.injective
  apply squareSineBasis.repr.injective
  ext j
  rw [squareDirichletGreenOperator_repr, squareSineBasis.repr_apply_apply,
    squareSineBasis.repr_apply_apply, ← squareL2Equiv_dirichletMode,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
  have he := squareDirichletMode_eigen j
  obtain ⟨v, hv, hAv⟩ := L.mem_graph_iff.mp he
  have hs := (dirichletLaplacian_isFormalAdjoint (Ω := dirichletSquare)) v u
  change ⟪L v, (u : Lp ℝ 2 ν□)⟫_ℝ = ⟪(v : Lp ℝ 2 ν□), L u⟫_ℝ at hs
  change (v : Lp ℝ 2 ν□) = squareDirichletMode j at hv
  rw [← hv, ← hs, hAv, real_inner_smul_left, hv, ← mul_assoc,
    inv_mul_cancel₀ (squareSineEigenvalue_pos j).ne', one_mul]

private theorem squareGradient_normallySolvable :
    IsNormallySolvable (weakDirichletGradient dirichletSquare) := by
  let L := weakDirichletGradient dirichletSquare
  let S := SobolevEuclideanZero 2 1 2 dirichletSquare
  let A := (SobolevEuclideanZero.gradₗ 2 2 dirichletSquare).mkContinuous 1
    (fun x : S => by
      change SobolevMultiIndex.gradNorm (x : SobolevEuclidean 2 1 2 dirichletSquare) ≤
        1 * ‖(x : SobolevEuclidean 2 1 2 dirichletSquare)‖
      rw [one_mul]
      exact SobolevMultiIndex.gradNorm_le_norm _)
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : V₂)).mp isBounded_dirichletSquare
  let R := max r 1
  have hR : 0 ≤ R := zero_le_one.trans (le_max_right _ _)
  have hSub : (dirichletSquare : Set V₂) ⊆ Metric.ball 0 R :=
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let c : NNReal := ⟨(1 + (2 * R) ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal),
    Real.rpow_nonneg (by positivity) _⟩
  have hA : AntilipschitzWith c A := A.antilipschitz_of_bound fun x =>
    SobolevEuclideanZero.norm_le_mul_norm_gradₗ (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hR hSub x
  refine ⟨isClosed_weakDirichletGradient _, ?_⟩
  have he : L.toFun.range = A.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨u, _, hu⟩ := (mem_weakDirichletGradient_graph_iff _).mp (L.mem_graph x)
      exact ⟨u, hu⟩
    · rintro ⟨u, rfl⟩
      have hgraph := (mem_weakDirichletGradient_graph_iff dirichletSquare).mpr ⟨u, rfl, rfl⟩
      obtain ⟨x, _, hx⟩ := L.mem_graph_iff.mp hgraph
      exact ⟨x, hx⟩
  rw [he]
  exact hA.isClosed_range A.uniformContinuous

private theorem exists_squareModeGradient (j : ℕ × ℕ) :
    ∃ y, (squareDirichletMode j, y) ∈ (weakDirichletGradient dirichletSquare).graph ∧
      (y, squareSineEigenvalue j • squareDirichletMode j) ∈
        (weakDirichletGradient dirichletSquare).adjoint.graph := by
  let L := weakDirichletGradient dirichletSquare
  have he : (squareDirichletMode j, squareSineEigenvalue j • squareDirichletMode j) ∈
      (partialComp L.adjoint L).graph := by
    rw [weakDirichletGradient_gram]
    exact squareDirichletMode_eigen j
  obtain ⟨u, hu, hform⟩ := (partialComp L.adjoint L).mem_graph_iff.mp he
  obtain ⟨hx, hy⟩ := (partialComp_mem_domain L.adjoint L (u : Lp ℝ 2 ν□)).mp u.property
  exact ⟨L ⟨u, hx⟩, L.mem_graph_iff.mpr ⟨⟨u, hx⟩, hu, rfl⟩,
    L.adjoint.mem_graph_iff.mpr ⟨⟨_, hy⟩, rfl, hform⟩⟩

/-- The weak gradient of each normalized sine mode of the square. -/
def squareDirichletModeGradient (j : ℕ × ℕ) : PiLp 2 (fun _ : Fin 2 => Lp ℝ 2 ν□) :=
  (exists_squareModeGradient j).choose

private theorem squareDirichletModeGradient_spec (j : ℕ × ℕ) :
    (squareDirichletMode j, squareDirichletModeGradient j) ∈
      (weakDirichletGradient dirichletSquare).graph ∧
    (squareDirichletModeGradient j, squareSineEigenvalue j • squareDirichletMode j) ∈
      (weakDirichletGradient dirichletSquare).adjoint.graph :=
  (exists_squareModeGradient j).choose_spec

/-- The mode gradient uses the ordinary partial derivatives of the smooth
sine eigenfunction in each coordinate. -/
theorem squareDirichletModeGradient_apply_ae (j : ℕ × ℕ) (i : Fin 2) :
    (fun s => squareDirichletModeGradient j i s) =ᵐ[ν□]
      fun s => fderiv ℝ (squareSineMode j) s (EuclideanSpace.single i 1) := by
  obtain ⟨u, hu, hv⟩ := (mem_weakDirichletGradient_graph_iff dirichletSquare).mp
    (squareDirichletModeGradient_spec j).1
  have hFunction : SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 dirichletSquare) =ᵐ[ν□]
      squareSineMode j := by
    change (fun s => (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      1 2 dirichletSquare volume u) s) =ᵐ[ν□] _
    rw [hu]
    exact MemLp.coeFn_toLp (squareSineMode_memLp j)
  rw [← hv]
  exact Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn dirichletSquare
    ((squareSineMode_contDiff j).of_le (by norm_num)).contDiffOn hFunction i

/-- **Exercise 27(e)** of [benIsrael2003generalized], Chapter 9.
Integrating the input against the input-coordinate derivatives of the
finite double sine Green series converges in $L^2$ to the maximal inverse of
the Dirichlet gradient. -/
theorem exercise_9_27_gradientSeries (y : PiLp 2 (fun _ : Fin 2 => Lp ℝ 2 ν□)) :
    let L := weakDirichletGradient dirichletSquare
    let y₀ : (maximalTsengInverse L).domain := ⟨y,
      maximalTsengInverse_domain_eq_top_of_normallySolvable squareGradient_normallySolvable ▸
        Submodule.mem_top⟩
    HasSum
      (fun j : ℕ × ℕ => ((squareSineEigenvalue j)⁻¹ *
        ∑ i : Fin 2, ∫ s, fderiv ℝ (squareSineMode j) s (EuclideanSpace.single i 1) *
          y i s ∂ν□) • squareDirichletMode j) (maximalTsengInverse L y₀) := by
  let L := weakDirichletGradient dirichletSquare
  let S := maximalTsengInverse L
  let hN := squareGradient_normallySolvable
  let h := isTsengInverse_maximalTsengInverse_of_isClosed hN.1
  let := hN.2.completeSpace_coe
  let y₀ : S.domain := ⟨y, maximalTsengInverse_domain_eq_top_of_normallySolvable hN ▸
    Submodule.mem_top⟩
  let x : L.domain := ⟨S y₀, h.inverse_range_le_domain ⟨y₀, rfl⟩⟩
  have hP : L x = L.toFun.range.starProjection y :=
    (exercise_9_34 hN (dense_weakDirichletGradient_domain dirichletSquare)).2.2.1 y₀
  change HasSum _ (x : Lp ℝ 2 ν□)
  apply (hasSum_squareDirichletMode_repr (x : Lp ℝ 2 ν□)).congr_fun
  intro j
  congr 1
  let v := squareDirichletModeGradient j
  have hv : v ∈ L.toFun.range := by
    obtain ⟨u, _, hu⟩ := L.mem_graph_iff.mp (squareDirichletModeGradient_spec j).1
    exact ⟨u, hu⟩
  have hz : inner ℝ v (y - L x) = 0 := by
    rw [hP]
    exact (Submodule.mem_orthogonal _ _).mp
      (L.toFun.range.sub_starProjection_mem_orthogonal y) v hv
  have h₁ : inner ℝ v y = inner ℝ v (L x) := by
    rwa [inner_sub_right, sub_eq_zero] at hz
  have hG := (squareDirichletModeGradient_spec j).2
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_weakDirichletGradient_domain _)] at hG
  have h₂ : inner ℝ (L x) v = inner ℝ (x : Lp ℝ 2 ν□)
      (squareSineEigenvalue j • squareDirichletMode j) :=
    sub_eq_zero.mp ((Submodule.mem_adjoint_iff _ _).mp hG _ _ (L.mem_graph x))
  have hI : inner ℝ v y = ∑ i : Fin 2,
      ∫ s, fderiv ℝ (squareSineMode j) s (EuclideanSpace.single i 1) * y i s ∂ν□ := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [L2.inner_eq_integral_mul]
      exact integral_congr_ae ((squareDirichletModeGradient_apply_ae j i).mul
        (Filter.EventuallyEq.rfl : (fun s => y i s) =ᵐ[ν□] fun s => y i s))
  rw [squareSineBasis.repr_apply_apply, ← squareL2Equiv_dirichletMode,
    LinearIsometryEquiv.inner_map_map, ← hI, h₁, ← real_inner_comm v (L x), h₂,
    real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ (squareSineEigenvalue_pos j).ne',
    one_mul, real_inner_comm]

end SquareSpectralProblem

open MeasureTheory Set SobolevMultiIndex TopologicalSpace
open scoped ENNReal InnerProductSpace

/-- Smooth fields with square-integrable components and diagonal derivatives
belong to the maximal adjoint domain. The adjoint acts by negative divergence. -/
theorem weakDirichletGradient_adjoint_of_contDiffOn
    {n : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin n)))
    (v : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hv : ∀ i, ContDiffOn ℝ 1 (v i) Ω)
    (hvLp : ∀ i, MemLp (v i) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))))
    (hdLp : ∀ i, MemLp (fun s => fderiv ℝ (v i) s (EuclideanSpace.single i 1))
      2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n))))) :
    ((WithLp.toLp 2 (fun i => (hvLp i).toLp (v i))),
      -(∑ i, (hdLp i).toLp (fun s => fderiv ℝ (v i) s (EuclideanSpace.single i 1)))) ∈
        (weakDirichletGradient Ω).adjoint.graph := by
  apply (mem_weakDirichletGradient_adjoint_graph_iff Ω).mpr
  intro φ hφ
  obtain ⟨ψ, hψ⟩ := hφ
  let μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))
  let d (i : Fin n) (s : EuclideanSpace ℝ (Fin n)) := fderiv ℝ (v i) s (EuclideanSpace.single i 1)
  have he (i : Fin n) :
      ⟪SobolevMultiIndex.weakDeriv φ (MultiIndexLE.single i), (hvLp i).toLp (v i)⟫_ℝ =
        -⟪SobolevMultiIndex.weakDeriv φ 0, (hdLp i).toLp (d i)⟫_ℝ := by
    have h1 := SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hψ i
    rw [EuclideanSpace.basisFun_toBasis_apply] at h1
    have hi := ((hv i).hasWeakIteratedLineDerivOn_single Ω i).integral_smul_eq ψ
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, smul_eq_mul, pow_one,
      neg_one_mul] at hi
    rw [L2.inner_eq_integral_mul, L2.inner_eq_integral_mul]
    calc
      _ = ∫ s, fderiv ℝ ψ s (EuclideanSpace.single i 1) * v i s ∂μ :=
        integral_congr_ae (h1.mul (hvLp i).coeFn_toLp)
      _ = -∫ s, ψ s * d i s ∂μ := hi
      _ = -∫ s, SobolevMultiIndex.weakDeriv φ 0 s * (hdLp i).toLp (d i) s ∂μ :=
        congrArg Neg.neg (integral_congr_ae (hψ.mul (hdLp i).coeFn_toLp)).symm
  rw [PiLp.inner_apply, inner_neg_right, inner_sum]
  exact (Finset.sum_congr rfl fun i _ => he i).trans (Finset.sum_neg_distrib _)

end SquareGradient

end BenIsraelGreville.Chapter09
