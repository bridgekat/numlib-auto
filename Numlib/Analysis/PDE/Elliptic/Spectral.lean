import Numlib.Analysis.InnerProductSpace.CompactSpectral
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.PDE.Elliptic.Dirichlet
import Numlib.Analysis.PDE.Elliptic.Regularity
import Numlib.MeasureTheory.Function.LpSpace.Convergence

/-!
# Eigenfunctions and spectral decomposition of the Dirichlet problem

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.8: the
Dirichlet eigenfunctions of `-Δ` on a bounded open set `Ω ⊆ ℝ^N`. Theorem 9.31 reads: there are
a Hilbert basis `(e_n)` of `L²(Ω)` and reals `λ_n > 0` with `λ_n → +∞` such that
`e_n ∈ H^1_0(Ω) ∩ C^∞(Ω)` and `-Δ e_n = λ_n e_n` in `Ω`.

## Design: a general symmetric coercive form, and the basis as data

The proof uses nothing about the Laplacian beyond three properties of its Dirichlet form
`a(u, v) = ∫ ∇u·∇v` on `H^1_0(Ω)`: bounded, symmetric, coercive (Poincaré). So the construction
is carried out for an arbitrary `a : SesqForm ℝ (H^1(Ω))` that is Hermitian and coercive on
`H^1_0(Ω)`: the solution operator `T = solutionOperator Ω a _ : L²(Ω) → L²(Ω)` of
`Numlib/Analysis/PDE/Elliptic/Dirichlet.lean` is compact when `Ω` has finite measure
(Rellich–Kondrachov, `Elliptic.solutionOperator_isCompactOperator`), symmetric
(`Elliptic.solutionOperator_isSymmetric`: `⟪T f, g⟫ = a(T g, T f) = a(T f, T g) = ⟪f, T g⟫`),
positive (`Elliptic.inner_solutionOperator_nonneg`) and injective
(`Elliptic.solutionOperator_ker_eq_bot`: `T f = 0` forces `∫ f φ = 0` for every `φ ∈ H^1_0(Ω)`,
so `f = 0`), and `L²(Ω)` is infinite-dimensional when `Ω ≠ ∅` and `N ≥ 1`
(`MeasureTheory.Lp.not_finiteDimensional_of_isOpen`). The enumerated spectral theorem
`ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` of
`Numlib/Analysis/InnerProductSpace/CompactSpectral.lean` — which needs exactly injectivity and
infinite dimension — produces the basis, with eigenvalues `μ_n → 0`, `μ_n > 0`, listed in
decreasing order; `λ_n = 1/μ_n` is then increasing to `+∞`.

The basis and the eigenvalues are **data**, not an existential: `Elliptic.eigenbasis` and
`Elliptic.eigenvalue`, together with the elements `Elliptic.eigenfunction … n ∈ H^1_0(Ω)` whose
functions the basis vectors are, and the weak eigenvalue equation
`a(u_n, φ) = λ_n ⟪e_n, φ⟫` (`Elliptic.form_eigenfunction`). The Laplacian instance is
`Elliptic.dirichletEigenbasis`, `Elliptic.dirichletEigenvalue`, `Elliptic.dirichletEigenfunction`
(Theorem 9.31, the Hilbert-space part), consumed by the heat and wave equations of
`Numlib/Analysis/PDE/Heat.lean` and `Wave.lean`; Remark 30, a general elliptic operator with
symmetric `L^∞` coefficients, is `Elliptic.exists_hilbertBasis_eigen_general`, the instance
`a = generalForm Ω A 0 a₀ + λ₀ ⟨·,·⟩_{L²}` with `λ₀` from Gårding's inequality, its eigenvalues
shifted back by `λ₀`.

The spaces are on `ℝ^N` with `N = d + 1`: for `N = 0` the open set `Ω` is at most a point and
`L²(Ω)` is finite-dimensional, so there is no `ℕ`-indexed basis. The symmetry and injectivity of
the solution operator hold for every `N`.

## The bases of `H^1_0(Ω)`

Remark 28 states that `(e_n / √λ_n)` is a Hilbert basis of `H^1_0(Ω)` for the inner product
`∫ ∇u·∇v` and `(e_n / √(λ_n + 1))` for the `H^1` inner product. The second is
`Elliptic.sobolevZeroEigenbasis`, a `HilbertBasis ℕ ℝ (SobolevEuclideanZero N 1 2 Ω)` on the
nose, since `laplaceForm = innerSL` (`Elliptic.hilbertBasis_sobolevZero`); the first is
`Elliptic.energyEigenbasis`, on the energy space `WithEnergy` of
`Numlib/Analysis/InnerProductSpace/Energy.lean` for the operator `Elliptic.dirichletOperator` of
the Dirichlet form restricted to `H^1_0(Ω)`, symmetric and coercive there
(`Elliptic.hilbertBasis_energy`); the energy basis is built for every Hermitian form coercive on
`H^1_0(Ω)`.

## Smoothness

`e_n ∈ C^∞(Ω)` is interior regularity alone (Remark 25, `Elliptic.regularity_interior_higher` of
`Numlib/Analysis/PDE/Elliptic/Regularity.lean`): the weak equation bootstraps
`e_n ∈ H^1_loc ⇒ H^3_loc ⇒ …`, and `MemSobolevMultiIndexLoc.exists_contDiffOn` gives a `C^∞`
representative on `Ω`. The classical equation `-Δ ũ_n = λ_n ũ_n` pointwise on `Ω` for a `C²`
representative, with Mathlib's `Δ`, is `Elliptic.laplacian_eq_of_eigenfunction`, from the weak
one against test functions by the variational lemma (Step D of §9.5, Example 1). The smoothness
clauses of Theorem 9.31 are `Elliptic.dirichletEigenbasis_exists_contDiffOn`; on a `C^∞` domain the
eigenfunctions lie in every `H^m(Ω)` and are `C^∞(Ω̄)` (Remark 29,
`Elliptic.exists_contDiffOn_closure_eigenfunction`, through Theorem 9.25 of
`Numlib/Analysis/PDE/Elliptic/Regularity.lean`).

## References

[brezis2011functional], §9.8: Theorem 9.31, Remarks 28–30.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace Elliptic

/-! ### Symmetry, positivity and injectivity of the solution operator -/

section Symmetric

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N))) (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
  (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)

/-- `⟪T f, g⟫_{L²} = a(T g, T f)`: the weak equation of `T g` tested against the solution
`T f ∈ H^1_0(Ω)`. -/
theorem inner_solutionOperator_eq_form
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ⟪solutionOperator Ω a ha f, g⟫_ℝ = a (solutionMap Ω a ha g) (solutionMap Ω a ha f) := by
  rw [real_inner_comm, ← SesqForm.restrict_apply a (SobolevEuclideanZero N 1 2 Ω),
    restrict_apply_solutionMap]
  rfl

/-- **The solution operator is symmetric** for a Hermitian form: `⟪T f, g⟫ = a(T g, T f) =
a(T f, T g) = ⟪f, T g⟫` — "repeat the proof of Theorem 8.21" in the proof of
[brezis2011functional] Theorem 9.31 (the one-dimensional Sturm–Liouville theorem is its
Theorem 8.22). -/
theorem solutionOperator_isSymmetric (hsymm : a.IsHermitian) :
    (solutionOperator Ω a ha : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).IsSymmetric := by
  intro f g
  change ⟪solutionOperator Ω a ha f, g⟫_ℝ = ⟪f, solutionOperator Ω a ha g⟫_ℝ
  rw [inner_solutionOperator_eq_form, real_inner_comm (solutionOperator Ω a ha g) f,
    inner_solutionOperator_eq_form, SesqForm.isHermitian_real_iff] at *
  exact hsymm _ _

/-- **`⟪T f, f⟫ = a(T f, T f)`**, read on `H^1_0(Ω)`. -/
theorem inner_solutionOperator_self_eq
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ⟪solutionOperator Ω a ha f, f⟫_ℝ = a (solutionMap Ω a ha f) (solutionMap Ω a ha f) :=
  inner_solutionOperator_eq_form Ω a ha f f

/-- **The solution operator is positive**: `⟪T f, f⟫ = a(T f, T f) ≥ c ‖T f‖² ≥ 0` by the
coercivity of the form on `H^1_0(Ω)`. -/
theorem inner_solutionOperator_nonneg
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    0 ≤ ⟪solutionOperator Ω a ha f, f⟫_ℝ := by
  rw [inner_solutionOperator_self_eq]
  obtain ⟨c, hc, hcoer⟩ := id ha
  have h := hcoer (solutionMap Ω a ha f)
  rw [SesqForm.restrict_apply] at h
  exact le_trans (by positivity) h

/-- **The solution operator is injective** (`N(T) = {0}` in the proof of [brezis2011functional]
Theorem 9.31): `T f = 0` forces the solution `u ∈ H^1_0(Ω)` to vanish, so `∫_Ω f φ = a(0, φ) = 0`
for every `φ ∈ H^1_0(Ω)`, and a function of `L²(Ω)` orthogonal to `H^1_0(Ω)` is zero
(`SobolevEuclideanZero.toDualL2_injective`, the variational lemma). -/
theorem solutionOperator_ker_eq_bot :
    LinearMap.ker (solutionOperator Ω a ha :
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun f hf ↦ ?_
  have hu : solutionMap Ω a ha f = 0 :=
    SobolevMultiIndexZero.fnL_injective (hf.trans (map_zero _).symm)
  have h1 : loadL Ω (SobolevEuclideanZero N 1 2 Ω) f = 0 := by
    calc loadL Ω (SobolevEuclideanZero N 1 2 Ω) f
        = a.restrict (SobolevEuclideanZero N 1 2 Ω) (solutionMap Ω a ha f) :=
          (ContinuousLinearMap.ext (restrict_apply_solutionMap Ω a ha f)).symm
      _ = a.restrict (SobolevEuclideanZero N 1 2 Ω) 0 := congrArg _ hu
      _ = 0 := (a.restrict (SobolevEuclideanZero N 1 2 Ω)).map_zero
  have h2 : SobolevEuclideanZero.toDualL2 N Ω f = 0 := h1
  exact SobolevEuclideanZero.toDualL2_injective (h2.trans (map_zero _).symm)

end Symmetric

/-- A real bounded form is linear in its first slot: `a (c • u) v = c * a u v`, for `u` in a
subspace `K` (the coercion of `c • u` being `c • ↑u`). Belongs beside `SesqForm.restrict` in
`Numlib/Variational/Forms.lean`. -/
theorem _root_.SesqForm.apply_coe_smul_left {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (a : SesqForm ℝ V) (K : Submodule ℝ V) (c : ℝ) (u : K) (v : V) :
    a (c • u : K) v = c * a u v := by
  rw [Submodule.coe_smul, map_smulₛₗ, conj_trivial, smul_apply, smul_eq_mul]

/-! ### The eigenbasis of a symmetric coercive form -/

section Eigenbasis

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
  (a : SesqForm ℝ (SobolevEuclidean (d + 1) 1 2 Ω)) (hsymm : a.IsHermitian)
  (ha : (a.restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoercive)

include hne in
/-- `L²(Ω)` is infinite-dimensional for a nonempty open `Ω ⊆ ℝ^N`, `N ≥ 1`
(`MeasureTheory.Lp.not_finiteDimensional_of_isOpen`); the hypothesis `hfin` of the enumerated
spectral theorem. -/
theorem not_finiteDimensional_L2 :
    ¬ FiniteDimensional ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :=
  Lp.not_finiteDimensional_of_isOpen volume 2 Ω.isOpen hne

/-- **The eigenbasis of a symmetric coercive form** — the abstract core of
[brezis2011functional] Theorem 9.31, for a general Hermitian form `a` on `H^1(Ω)` coercive on
`H^1_0(Ω)`, on an open set `Ω ⊆ ℝ^N` (`N = d + 1`) of finite measure, nonempty: the Hilbert
basis of `L²(Ω)` of eigenfunctions of the solution operator `T = solutionOperator Ω a ha`,
produced by `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` from the symmetry,
compactness and injectivity of `T` and the infinite dimension of `L²(Ω)`. Its `n`-th vector
`e_n` is the function of `Elliptic.eigenfunction … n ∈ H^1_0(Ω)`, which solves
`a(e_n, φ) = λ_n ⟪e_n, φ⟫` for the eigenvalue `λ_n = Elliptic.eigenvalue … n`
(`Elliptic.form_eigenfunction`). -/
def eigenbasis :
    HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :=
  ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis
    (solutionOperator_isSymmetric Ω a ha hsymm) (solutionOperator_isCompactOperator Ω hΩ a ha)
    (solutionOperator_ker_eq_bot Ω a ha) (not_finiteDimensional_L2 Ω hne)

/-- The eigenvalues `μ_n` of the solution operator `T`, listed with multiplicity in decreasing
order (`ContinuousLinearMap.IsSymmetric.eigenvalueSeq`): `T e_n = μ_n e_n`. -/
def eigenvalueSeq : ℕ → ℝ :=
  ContinuousLinearMap.IsSymmetric.eigenvalueSeq (solutionOperator_isSymmetric Ω a ha hsymm)
    (solutionOperator_isCompactOperator Ω hΩ a ha)

/-- **The eigenvalues `λ_n = 1/μ_n`** of the weak eigenvalue problem `a(u, φ) = λ ⟪u, φ⟫` on
`H^1_0(Ω)`, the reciprocals of the eigenvalues of the solution operator: positive
(`Elliptic.eigenvalue_pos`), increasing (`Elliptic.monotone_eigenvalue`) and tending to `+∞`
(`Elliptic.tendsto_eigenvalue_atTop`). -/
def eigenvalue (n : ℕ) : ℝ := (eigenvalueSeq Ω hΩ a hsymm ha n)⁻¹

/-- `T e_n = μ_n e_n`. -/
theorem solutionOperator_eigenbasis (n : ℕ) :
    solutionOperator Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)
      = eigenvalueSeq Ω hΩ a hsymm ha n • eigenbasis Ω hΩ hne a hsymm ha n :=
  ContinuousLinearMap.IsSymmetric.apply_eigenvectorHilbertBasis _ _ _ _ n

/-- The eigenvalues of the solution operator tend to `0`. -/
theorem tendsto_eigenvalueSeq_zero : Tendsto (eigenvalueSeq Ω hΩ a hsymm ha) atTop (𝓝 0) :=
  ContinuousLinearMap.IsSymmetric.tendsto_eigenvalueSeq_zero _ _

/-- The eigenfunctions are nonzero. -/
theorem eigenbasis_ne_zero (n : ℕ) : eigenbasis Ω hΩ hne a hsymm ha n ≠ 0 :=
  (eigenbasis Ω hΩ hne a hsymm ha).orthonormal.ne_zero n

include hne in
/-- **The eigenvalues of the solution operator are positive**: `μ_n = ⟪T e_n, e_n⟫ ≥ 0` by the
positivity of `T` and `μ_n ≠ 0` by its injectivity. -/
theorem eigenvalueSeq_pos (n : ℕ) : 0 < eigenvalueSeq Ω hΩ a hsymm ha n := by
  have h1 := inner_solutionOperator_nonneg Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)
  rw [solutionOperator_eigenbasis, inner_smul_left, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq, (eigenbasis Ω hΩ hne a hsymm ha).orthonormal.1 n, one_pow,
    mul_one] at h1
  refine lt_of_le_of_ne h1 fun h0 ↦ eigenbasis_ne_zero Ω hΩ hne a hsymm ha n ?_
  have h2 := solutionOperator_eigenbasis Ω hΩ hne a hsymm ha n
  rw [← h0, zero_smul] at h2
  exact LinearMap.ker_eq_bot'.1 (solutionOperator_ker_eq_bot Ω a ha) _ h2

include hne in
/-- The eigenvalues of the solution operator decrease. -/
theorem eigenvalueSeq_antitone : Antitone (eigenvalueSeq Ω hΩ a hsymm ha) := fun m n hmn ↦ by
  have h : |eigenvalueSeq Ω hΩ a hsymm ha n| ≤ |eigenvalueSeq Ω hΩ a hsymm ha m| :=
    ContinuousLinearMap.IsSymmetric.eigenvalueSeq_antitone _ _ hmn
  rwa [abs_of_pos (eigenvalueSeq_pos Ω hΩ hne a hsymm ha n),
    abs_of_pos (eigenvalueSeq_pos Ω hΩ hne a hsymm ha m)] at h

include hne in
/-- **The eigenvalues `λ_n` are positive** ([brezis2011functional] Theorem 9.31). -/
theorem eigenvalue_pos (n : ℕ) : 0 < eigenvalue Ω hΩ a hsymm ha n :=
  inv_pos.2 (eigenvalueSeq_pos Ω hΩ hne a hsymm ha n)

include hne in
/-- **The eigenvalues `λ_n` increase.** -/
theorem monotone_eigenvalue : Monotone (eigenvalue Ω hΩ a hsymm ha) := fun _ n hmn ↦
  inv_anti₀ (eigenvalueSeq_pos Ω hΩ hne a hsymm ha n)
    (eigenvalueSeq_antitone Ω hΩ hne a hsymm ha hmn)

include hne in
/-- **`λ_n → +∞`** ([brezis2011functional] Theorem 9.31). -/
theorem tendsto_eigenvalue_atTop : Tendsto (eigenvalue Ω hΩ a hsymm ha) atTop atTop := by
  have h1 : Tendsto (eigenvalueSeq Ω hΩ a hsymm ha) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_eigenvalueSeq_zero Ω hΩ a hsymm ha,
      Eventually.of_forall fun n ↦ eigenvalueSeq_pos Ω hΩ hne a hsymm ha n⟩
  exact tendsto_inv_nhdsGT_zero.comp h1

/-- **The eigenfunctions as elements of `H^1_0(Ω)`**: `u_n = λ_n • (the weak solution with datum
`e_n`)`, whose function is `e_n` (`Elliptic.fnL_eigenfunction`) and which solves
`a(u_n, φ) = λ_n ⟪e_n, φ⟫` for every `φ ∈ H^1_0(Ω)` (`Elliptic.form_eigenfunction`). -/
def eigenfunction (n : ℕ) : SobolevEuclideanZero (d + 1) 1 2 Ω :=
  eigenvalue Ω hΩ a hsymm ha n • solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)

/-- **The function of `u_n` is `e_n`**: `T (λ_n e_n) = e_n`. -/
theorem fnL_eigenfunction (n : ℕ) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (eigenfunction Ω hΩ hne a hsymm ha n) = eigenbasis Ω hΩ hne a hsymm ha n := by
  have h1 : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume (solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n))
      = eigenvalueSeq Ω hΩ a hsymm ha n • eigenbasis Ω hΩ hne a hsymm ha n :=
    solutionOperator_eigenbasis Ω hΩ hne a hsymm ha n
  calc SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (eigenfunction Ω hΩ hne a hsymm ha n)
      = eigenvalue Ω hΩ a hsymm ha n • SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
          (solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)) :=
        (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume).map_smul _ _
    _ = eigenvalue Ω hΩ a hsymm ha n
        • (eigenvalueSeq Ω hΩ a hsymm ha n • eigenbasis Ω hΩ hne a hsymm ha n) :=
        congrArg (fun x ↦ eigenvalue Ω hΩ a hsymm ha n • x) h1
    _ = eigenbasis Ω hΩ hne a hsymm ha n := by
        rw [smul_smul, eigenvalue, inv_mul_cancel₀ (eigenvalueSeq_pos Ω hΩ hne a hsymm ha n).ne',
          one_smul]

/-- **The function of `u_n` is `e_n`**, almost everywhere on `Ω`. -/
theorem fn_eigenfunction (n : ℕ) :
    SobolevMultiIndex.fn (eigenfunction Ω hΩ hne a hsymm ha n : SobolevEuclidean (d + 1) 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        eigenbasis Ω hΩ hne a hsymm ha n := by
  rw [← fnL_eigenfunction Ω hΩ hne a hsymm ha n]
  exact Filter.EventuallyEq.refl _ _

/-- **The weak eigenvalue equation (83)** of [brezis2011functional] Theorem 9.31 for the form
`a`: `a(u_n, φ) = λ_n ⟪e_n, φ⟫_{L²}` for every `φ ∈ H^1_0(Ω)`. -/
theorem form_eigenfunction (n : ℕ) (φ : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    a (eigenfunction Ω hΩ hne a hsymm ha n) φ
      = eigenvalue Ω hΩ a hsymm ha n * ⟪eigenbasis Ω hΩ hne a hsymm ha n,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume φ⟫_ℝ :=
  calc a (eigenfunction Ω hΩ hne a hsymm ha n) φ
      = eigenvalue Ω hΩ a hsymm ha n
        * a (solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)) φ :=
        SesqForm.apply_coe_smul_left a _ _ _ _
    _ = eigenvalue Ω hΩ a hsymm ha n
        * loadL Ω (SobolevEuclideanZero (d + 1) 1 2 Ω) (eigenbasis Ω hΩ hne a hsymm ha n) φ :=
        congrArg (fun x ↦ eigenvalue Ω hΩ a hsymm ha n * x)
          (restrict_apply_solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n) φ)
    _ = _ := rfl

/-- **Each basis function is in `H^1_0(Ω)` and solves the weak eigenvalue problem**: for every
`n`, `e_n` is the function of some `u ∈ H^1_0(Ω)` with `a(u, φ) = λ_n ⟪e_n, φ⟫` for every
`φ ∈ H^1_0(Ω)` — the book's (83) for the form `a`; the element is `Elliptic.eigenfunction`. -/
theorem eigenbasis_mem_sobolevZero (n : ℕ) :
    ∃ u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u
        = eigenbasis Ω hΩ hne a hsymm ha n ∧
      ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, a u φ
        = eigenvalue Ω hΩ a hsymm ha n * ⟪eigenbasis Ω hΩ hne a hsymm ha n,
          SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume φ⟫_ℝ :=
  ⟨eigenfunction Ω hΩ hne a hsymm ha n, (eigenfunction Ω hΩ hne a hsymm ha n).2,
    fnL_eigenfunction Ω hΩ hne a hsymm ha n,
    fun φ hφ ↦ form_eigenfunction Ω hΩ hne a hsymm ha n ⟨φ, hφ⟩⟩

end Eigenbasis

/-! ### Theorem 9.31: the Dirichlet eigenfunctions of `-Δ` -/

section Dirichlet

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- **Poincaré's inequality as coercivity of the Dirichlet form on `H^1_0(Ω)`** for
`Ω ⊆ B(0, R)`: `∫_Ω |∇v|² ≥ (1 + (2R)²)⁻¹ ‖v‖²_{H^1}`, from `SobolevEuclideanZero.norm_le_gradNorm`
([brezis2011functional] Corollary 9.19) in the form `Elliptic.norm_sq_le_dirichletForm_self`. -/
theorem dirichletForm_restrict_isCoerciveWith {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) :
    ((dirichletForm Ω).restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoerciveWith
      (1 + (2 * R) ^ 2)⁻¹ := by
  intro v
  rw [RCLike.re_to_real, SesqForm.restrict_apply, ← Submodule.norm_coe]
  have hpos : (0 : ℝ) < 1 + (2 * R) ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hpos]
  exact norm_sq_le_dirichletForm_self hR hΩ v.2

/-- **The Dirichlet form is coercive on `H^1_0(Ω)` for a bounded `Ω`** (Poincaré's inequality):
the hypothesis `ha` of the solution operator and of the eigenbasis for `a = dirichletForm Ω`. -/
theorem dirichletForm_restrict_isCoercive
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ((dirichletForm Ω).restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoercive := by
  obtain ⟨R, hR0, hR⟩ := hΩ.subset_ball_lt 0 0
  exact ⟨_, by positivity, dirichletForm_restrict_isCoerciveWith Ω hR0.le hR⟩

variable (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- **[brezis2011functional] Theorem 9.31, the basis of Dirichlet eigenfunctions of `-Δ`**: for
a bounded nonempty open `Ω ⊆ ℝ^N` (`N = d + 1`), the Hilbert basis `(e_n)` of `L²(Ω)` of
eigenfunctions of the Dirichlet problem for `-Δ`, the instance of `Elliptic.eigenbasis` for the
Dirichlet form `∫ ∇u·∇v`, Hermitian and coercive on `H^1_0(Ω)` by Poincaré's inequality. Each
`e_n` is the function of `Elliptic.dirichletEigenfunction Ω hΩ hne n ∈ H^1_0(Ω)`, which solves
`∫ ∇e_n·∇φ = λ_n ∫ e_n φ` for all `φ ∈ H^1_0(Ω)` (the book's (83),
`Elliptic.dirichletForm_dirichletEigenfunction`) with the eigenvalue
`λ_n = Elliptic.dirichletEigenvalue Ω hΩ n > 0`, `λ_n → +∞`. -/
def dirichletEigenbasis :
    HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :=
  eigenbasis Ω hΩ.measure_lt_top.ne hne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- **The Dirichlet eigenvalues `λ_n` of `-Δ`** ([brezis2011functional] Theorem 9.31): positive
(`Elliptic.dirichletEigenvalue_pos`), increasing (`Elliptic.monotone_dirichletEigenvalue`), tending
to `+∞` (`Elliptic.tendsto_dirichletEigenvalue_atTop`). -/
def dirichletEigenvalue : ℕ → ℝ :=
  eigenvalue Ω hΩ.measure_lt_top.ne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- **The Dirichlet eigenfunctions as elements of `H^1_0(Ω)`**: `u_n ∈ H^1_0(Ω)` with function
`e_n = dirichletEigenbasis Ω hΩ hne n`. -/
def dirichletEigenfunction (n : ℕ) : SobolevEuclideanZero (d + 1) 1 2 Ω :=
  eigenfunction Ω hΩ.measure_lt_top.ne hne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ) n

include hne in
/-- **`λ_n > 0`** ([brezis2011functional] Theorem 9.31). -/
theorem dirichletEigenvalue_pos (n : ℕ) : 0 < dirichletEigenvalue Ω hΩ n :=
  eigenvalue_pos Ω hΩ.measure_lt_top.ne hne _ _ _ n

include hne in
/-- **The Dirichlet eigenvalues increase.** -/
theorem monotone_dirichletEigenvalue : Monotone (dirichletEigenvalue Ω hΩ) :=
  monotone_eigenvalue Ω hΩ.measure_lt_top.ne hne _ _ _

include hne in
/-- **`λ_n → +∞`** ([brezis2011functional] Theorem 9.31). -/
theorem tendsto_dirichletEigenvalue_atTop : Tendsto (dirichletEigenvalue Ω hΩ) atTop atTop :=
  tendsto_eigenvalue_atTop Ω hΩ.measure_lt_top.ne hne _ _ _

/-- **`e_n ∈ H^1_0(Ω)`**: the basis function `e_n` is the function of
`dirichletEigenfunction Ω hΩ hne n`. -/
theorem fnL_dirichletEigenfunction (n : ℕ) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (dirichletEigenfunction Ω hΩ hne n) = dirichletEigenbasis Ω hΩ hne n :=
  fnL_eigenfunction Ω hΩ.measure_lt_top.ne hne _ _ _ n

/-- **`e_n ∈ H^1_0(Ω)`**, almost everywhere on `Ω`. -/
theorem fn_dirichletEigenfunction (n : ℕ) :
    SobolevMultiIndex.fn (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        dirichletEigenbasis Ω hΩ hne n :=
  fn_eigenfunction Ω hΩ.measure_lt_top.ne hne _ _ _ n

/-- **The weak eigenvalue equation (83)** of [brezis2011functional] Theorem 9.31:
`∫_Ω ∇e_n·∇φ = λ_n ∫_Ω e_n φ` for every `φ ∈ H^1_0(Ω)`. -/
theorem dirichletForm_dirichletEigenfunction (n : ℕ) (φ : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n) φ
      = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume φ⟫_ℝ :=
  form_eigenfunction Ω hΩ.measure_lt_top.ne hne _ _ _ n φ

/-- **Each Dirichlet eigenfunction is in `H^1_0(Ω)` and solves (83)**, in the existential form:
`e_n` is the function of some `u ∈ H^1_0(Ω)` with `∫ ∇u·∇φ = λ_n ∫ e_n φ` for all
`φ ∈ H^1_0(Ω)`. -/
theorem dirichletEigenbasis_mem_sobolevZero (n : ℕ) :
    ∃ u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u
        = dirichletEigenbasis Ω hΩ hne n ∧
      ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω u φ
        = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
          SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume φ⟫_ℝ :=
  eigenbasis_mem_sobolevZero Ω hΩ.measure_lt_top.ne hne _ _ _ n

end Dirichlet

/-! ### The classical eigenvalue equation for a `C²` eigenfunction -/

section Classical

open Laplacian

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-- **The classical eigenvalue equation**: if `U ∈ H^1(Ω)` satisfies the weak equation
`∫_Ω ∇U·∇φ = λ ∫_Ω U φ` for every test function `φ` and its function is a `C²` function `u` on
`Ω`, then `-Δ u = λ u` at every point of `Ω`, with Mathlib's Laplacian `Δ`. The weak equation
says that `U` solves `-ΔU + U = (λ + 1) U` weakly, so Step D of [brezis2011functional] §9.5,
Example 1 (`Elliptic.laplacian_ae_eq_of_forall_testFunction`) gives `-Δu + u = (λ + 1) u` almost
everywhere on `Ω`, and both sides are continuous on the open `Ω`
(`MeasureTheory.Measure.eqOn_open_of_ae_eq`). This is the reading of "`-Δ e_n = λ_n e_n` in
`Ω`" of Theorem 9.31 for the `C^∞` representative of `e_n`. -/
theorem laplacian_eq_of_eigenfunction {U : SobolevEuclidean N 1 2 Ω} {lam : ℝ}
    (hUw : ∀ V ∈ SobolevMultiIndex.testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume, dirichletForm Ω U V
        = lam * ⟪SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          U, SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
            V⟫_ℝ)
    {u : EuclideanSpace ℝ (Fin N) → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) :
    ∀ x ∈ Ω, -Δ u x = lam * u x := by
  have hΩo := Ω.isOpen
  obtain ⟨f, hf⟩ : ∃ f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      f = (lam + 1) • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
        volume U := ⟨_, rfl⟩
  have hUw' : ∀ V ∈ SobolevMultiIndex.testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume, laplaceForm Ω U V = load Ω f V := fun V hV ↦ by
    rw [laplaceForm_apply_eq_dirichletForm_add, hUw V hV, load_apply_inner, hf, inner_smul_left,
      RCLike.conj_to_real, SobolevMultiIndex.fnL_eq_weakDeriv_zero,
      SobolevMultiIndex.fnL_eq_weakDeriv_zero]
    ring
  have h1 := laplacian_ae_eq_of_forall_testFunction Ω hUw' hu hU
  have h2 : (f : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ (lam + 1) * u x := by
    rw [hf]
    filter_upwards [Lp.coeFn_smul (lam + 1) (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U), hU] with x hx hx'
    rw [hx, Pi.smul_apply, smul_eq_mul, SobolevMultiIndex.fnL_apply, hx']
  have h3 : EqOn (fun x ↦ -Δ u x + u x) (fun x ↦ (lam + 1) * u x) Ω :=
    Measure.eqOn_open_of_ae_eq (h1.trans h2) hΩo
      ((continuousOn_laplacian Ω hu).neg.add
        (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn)
      ((hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn.const_smul (lam + 1))
  intro x hx
  have := h3 hx
  simp only at this
  linarith

end Classical

/-! ### Transporting a Hilbert basis along the eigenvalue equation -/

section Transport

variable {ι E L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup L]
  [InnerProductSpace ℝ L]

/-- A vector orthogonal to every vector of a Hilbert basis is zero. Belongs beside
`HilbertBasis.repr_apply_apply` in `Mathlib/Analysis/InnerProductSpace/l2Space.lean`. -/
theorem _root_.HilbertBasis.eq_zero_of_forall_inner_eq_zero (b : HilbertBasis ι ℝ L) {x : L}
    (h : ∀ i, ⟪b i, x⟫_ℝ = 0) : x = 0 := by
  have hr : b.repr x = 0 := by
    ext i
    rw [b.repr_apply_apply, h i, lp.coeFn_zero, Pi.zero_apply]
  simpa using congrArg b.repr.symm hr

/-- The orthogonal complement of the span of a family is trivial when only `0` is orthogonal to
every member of the family. Belongs beside `Submodule.mem_orthogonal` in
`Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`. -/
theorem _root_.Submodule.orthogonal_span_range_eq_bot_of_forall {v : ι → E}
    (h : ∀ x, (∀ i, ⟪v i, x⟫_ℝ = 0) → x = 0) : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  exact h x fun i ↦ (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨i, rfl⟩)

/-- A family `u` with `⟪u i, u i⟫ = c i > 0` and `⟪u i, u j⟫ = 0` for `i ≠ j`, normalized by
`1/√(c i)`, is orthonormal. -/
theorem _root_.orthonormal_inv_sqrt_smul {u : ι → E} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (hd : ∀ i, ⟪u i, u i⟫_ℝ = c i) (ho : ∀ i j, i ≠ j → ⟪u i, u j⟫_ℝ = 0) :
    Orthonormal ℝ fun i ↦ (√(c i))⁻¹ • u i := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  split_ifs with hij
  · subst hij
    rw [hd, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt (hc i).le, inv_mul_cancel₀ (hc i).ne']
  · rw [ho i j hij, mul_zero, mul_zero]

variable [CompleteSpace E]

/-- **Transport of a Hilbert basis along a weak eigenvalue equation.** Let `b` be a Hilbert
basis of `L`, `T : E →ₗ L` injective, and `u : ι → E` a family with `T (u i) = b i` and
`⟪u i, x⟫_E = c i ⟪b i, T x⟫_L` for every `x ∈ E`, with `c i > 0`. Then `i ↦ u i / √(c i)` is a
Hilbert basis of `E`: it is orthonormal because `⟪u i, u j⟫ = c i ⟪b i, b j⟫ = c i δ_ij`, and
complete because `x ⊥ u i` for all `i` gives `T x ⊥ b i` for all `i`, so `T x = 0` and `x = 0`.
This is the argument of [brezis2011functional] Chapter 9, Remark 28, with `E = H^1_0(Ω)`,
`L = L²(Ω)`, `T` the inclusion, `b` the Dirichlet eigenbasis and `c i = λ_i` or `λ_i + 1`. -/
def _root_.HilbertBasis.ofInnerEqMul (b : HilbertBasis ι ℝ L) (T : E →ₗ[ℝ] L)
    (hT : Function.Injective T) (u : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hTu : ∀ i, T (u i) = b i) (h : ∀ i x, ⟪u i, x⟫_ℝ = c i * ⟪b i, T x⟫_ℝ) :
    HilbertBasis ι ℝ E :=
  HilbertBasis.mkOfOrthogonalEqBot
    (orthonormal_inv_sqrt_smul hc
      (fun i ↦ by rw [h, hTu, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow, mul_one])
      fun i j hij ↦ by rw [h, hTu, b.orthonormal.2 hij, mul_zero])
    (Submodule.orthogonal_span_range_eq_bot_of_forall fun x hx ↦ by
      refine hT ((b.eq_zero_of_forall_inner_eq_zero fun i ↦ ?_).trans (map_zero T).symm)
      have hi := hx i
      rw [inner_smul_left, RCLike.conj_to_real, h, mul_eq_zero, mul_eq_zero] at hi
      rcases hi with hi | hi | hi
      · exact absurd hi (inv_ne_zero (Real.sqrt_pos.2 (hc i)).ne')
      · exact absurd hi (hc i).ne'
      · exact hi)

/-- The basis vectors of `HilbertBasis.ofInnerEqMul` are the normalized `u i / √(c i)`. -/
@[simp]
theorem _root_.HilbertBasis.coe_ofInnerEqMul (b : HilbertBasis ι ℝ L) (T : E →ₗ[ℝ] L)
    (hT : Function.Injective T) (u : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hTu : ∀ i, T (u i) = b i) (h : ∀ i x, ⟪u i, x⟫_ℝ = c i * ⟪b i, T x⟫_ℝ) :
    ⇑(HilbertBasis.ofInnerEqMul b T hT u c hc hTu h) = fun i ↦ (√(c i))⁻¹ • u i :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- **Transport of a Hilbert basis to an energy space.** For a bounded symmetric coercive
operator `A` on `E`, a Hilbert basis `b` of `L`, `T : E →ₗ L` injective and a family `u` with
`T (u i) = b i` and `⟪A (u i), x⟫ = c i ⟪b i, T x⟫` for every `x`, `c i > 0`, the family
`i ↦ u i / √(c i)` is a Hilbert basis of the energy space `WithEnergy A _` of `A`
(`HilbertBasis.ofInnerEqMul` for the energy inner product `⟪A u, x⟫`). This is
[brezis2011functional] Chapter 9, Remark 28, first clause, in the abstract: `E = H^1_0(Ω)`, `A`
the operator of the form `a`, `⟪A u_i, x⟫ = a(u_i, x) = λ_i ⟪e_i, x⟫_{L²}`. -/
def _root_.HilbertBasis.ofInnerEqMulEnergy (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetricCoercive)
    (b : HilbertBasis ι ℝ L) (T : E →ₗ[ℝ] L) (hT : Function.Injective T) (u : ι → E) (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) (hTu : ∀ i, T (u i) = b i)
    (h : ∀ i x, ⟪A (u i), x⟫_ℝ = c i * ⟪b i, T x⟫_ℝ) :
    HilbertBasis ι ℝ (WithEnergy A.toLinearMap hA) :=
  haveI := WithEnergy.instCompleteSpace_of_continuousLinearMap hA
  HilbertBasis.ofInnerEqMul b (T ∘ₗ (WithEnergy.equiv _ _).symm.toLinearMap)
    (hT.comp (WithEnergy.equiv _ _).symm.injective) (fun i ↦ WithEnergy.equiv _ _ (u i)) c hc
    (fun i ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hTu])
    (fun i x ↦ h i _)

/-- The basis vectors of `HilbertBasis.ofInnerEqMulEnergy` are the normalized `u i / √(c i)`,
read in the energy space. -/
@[simp]
theorem _root_.HilbertBasis.coe_ofInnerEqMulEnergy (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetricCoercive) (b : HilbertBasis ι ℝ L) (T : E →ₗ[ℝ] L)
    (hT : Function.Injective T) (u : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hTu : ∀ i, T (u i) = b i) (h : ∀ i x, ⟪A (u i), x⟫_ℝ = c i * ⟪b i, T x⟫_ℝ) :
    ⇑(HilbertBasis.ofInnerEqMulEnergy A hA b T hT u c hc hTu h)
      = fun i ↦ (√(c i))⁻¹ • WithEnergy.equiv _ _ (u i) :=
  haveI := WithEnergy.instCompleteSpace_of_continuousLinearMap hA
  HilbertBasis.coe_ofInnerEqMul _ _ _ _ _ _ _ _

end Transport

/-! ### The operator of a form restricted to `H^1_0(Ω)` -/

section RestrictOperator

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))
  (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω)) (hsymm : a.IsHermitian)
  (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)

/-- **The operator of a form restricted to `H^1_0(Ω)`**: the bounded operator `A` on `H^1_0(Ω)`
with `⟪A u, v⟫_{H^1} = a(u, v)` (`SesqForm.toOperator`); its energy space `WithEnergy` is
`H^1_0(Ω)` with the inner product `a(u, v)`. -/
def restrictOperator :
    SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclideanZero N 1 2 Ω :=
  SesqForm.toOperator (a.restrict (SobolevEuclideanZero N 1 2 Ω))

/-- `⟪A u, v⟫_{H^1} = a(u, v)`. -/
theorem inner_restrictOperator (u v : SobolevEuclideanZero N 1 2 Ω) :
    ⟪restrictOperator Ω a u, v⟫_ℝ = a u v :=
  SesqForm.inner_toOperator _ u v

include hsymm ha in
/-- The operator of a Hermitian form coercive on `H^1_0(Ω)` is symmetric and coercive, so that
`H^1_0(Ω)` with the inner product `a(u, v)` is the energy space
`WithEnergy (restrictOperator Ω a) _`. -/
theorem restrictOperator_isSymmetricCoercive :
    (restrictOperator Ω a).toLinearMap.IsSymmetricCoercive :=
  (hsymm.restrict _).isSymmetricCoercive_toOperator ha

/-- The energy space of a form coercive on `H^1_0(Ω)` is complete
(`WithEnergy.instCompleteSpace_of_continuousLinearMap`). -/
theorem completeSpace_withEnergy_restrictOperator :
    CompleteSpace (WithEnergy (restrictOperator Ω a).toLinearMap
      (restrictOperator_isSymmetricCoercive Ω a hsymm ha)) :=
  WithEnergy.instCompleteSpace_of_continuousLinearMap _

/-- **The operator of the Dirichlet form on `H^1_0(Ω)`**: the bounded operator `A` on `H^1_0(Ω)`
with `⟪A u, v⟫_{H^1} = ∫_Ω ∇u·∇v` (`Elliptic.inner_dirichletOperator`); symmetric and coercive
for a bounded `Ω` (`Elliptic.dirichletOperator_isSymmetricCoercive`), so that its energy space
`WithEnergy (dirichletOperator Ω) _` is `H^1_0(Ω)` with the scalar product `∫ ∇u·∇v` of
[brezis2011functional] Chapter 9, Remark 28 — the first factor of the phase space of the wave
equation, whose energy `∫_Ω |∇u|²` is `⟪A u, u⟫` ([brezis2011functional] §10.3, (32)). -/
def dirichletOperator :
    SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclideanZero N 1 2 Ω :=
  restrictOperator Ω (dirichletForm Ω)

/-- `⟪A u, v⟫_{H^1} = ∫_Ω ∇u·∇v`. -/
theorem inner_dirichletOperator (u v : SobolevEuclideanZero N 1 2 Ω) :
    ⟪dirichletOperator Ω u, v⟫_ℝ = dirichletForm Ω u v :=
  inner_restrictOperator Ω _ u v

/-- `⟪A u, v⟫_{H¹} = ⟪A v, u⟫_{H¹}`: the operator of the Dirichlet form is symmetric. -/
theorem inner_dirichletOperator_comm (u v : SobolevEuclideanZero N 1 2 Ω) :
    ⟪dirichletOperator Ω u, v⟫_ℝ = ⟪dirichletOperator Ω v, u⟫_ℝ := by
  rw [inner_dirichletOperator, inner_dirichletOperator, dirichletForm_isHermitian Ω _ _,
    conj_trivial]

end RestrictOperator

/-! ### The energy basis of a symmetric coercive form (Remark 28, first clause) -/

section EnergyBasis

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
  (a : SesqForm ℝ (SobolevEuclidean (d + 1) 1 2 Ω)) (hsymm : a.IsHermitian)
  (ha : (a.restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoercive)

/-- **The eigenfunctions normalized in the energy norm form a Hilbert basis of `H^1_0(Ω)` for
the inner product `a(u, v)`** ([brezis2011functional] Chapter 9, Remark 28, first clause, for a
general Hermitian form coercive on `H^1_0(Ω)`): `n ↦ u_n / √λ_n` on the energy space
`WithEnergy (restrictOperator Ω a) _`, by `HilbertBasis.ofInnerEqMul` with the weak equation
`a(u_n, x) = λ_n ⟪e_n, x⟫_{L²}` (`Elliptic.form_eigenfunction`). -/
def energyEigenbasis :
    HilbertBasis ℕ ℝ (WithEnergy (restrictOperator Ω a).toLinearMap
      (restrictOperator_isSymmetricCoercive Ω a hsymm ha)) :=
  HilbertBasis.ofInnerEqMulEnergy (restrictOperator Ω a)
    (restrictOperator_isSymmetricCoercive Ω a hsymm ha) (eigenbasis Ω hΩ hne a hsymm ha)
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume).toLinearMap
    SobolevMultiIndexZero.fnL_injective (eigenfunction Ω hΩ hne a hsymm ha)
    (eigenvalue Ω hΩ a hsymm ha) (eigenvalue_pos Ω hΩ hne a hsymm ha)
    (fnL_eigenfunction Ω hΩ hne a hsymm ha)
    (fun n x ↦ (inner_restrictOperator Ω a _ x).trans (form_eigenfunction Ω hΩ hne a hsymm ha n x))

/-- The vectors of the energy basis are `u_n / √λ_n`. -/
theorem coe_energyEigenbasis :
    ⇑(energyEigenbasis Ω hΩ hne a hsymm ha) = fun n ↦ (√(eigenvalue Ω hΩ a hsymm ha n))⁻¹
      • WithEnergy.equiv _ _ (eigenfunction Ω hΩ hne a hsymm ha n) :=
  HilbertBasis.coe_ofInnerEqMulEnergy _ _ _ _ _ _ _ _ _ _

end EnergyBasis

/-! ### Remark 28: the two bases of `H^1_0(Ω)` for the Dirichlet form -/

section SobolevZeroBasis

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- **The `H^1` inner product against a Dirichlet eigenfunction**:
`⟪u_n, x⟫_{H^1} = (λ_n + 1) ⟪e_n, x⟫_{L²}` for every `x ∈ H^1_0(Ω)`, from the weak equation (83)
and `laplaceForm = innerSL`. -/
theorem inner_dirichletEigenfunction_left (n : ℕ) (x : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ⟪dirichletEigenfunction Ω hΩ hne n, x⟫_ℝ
      = (dirichletEigenvalue Ω hΩ n + 1) * ⟪dirichletEigenbasis Ω hΩ hne n,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume x⟫_ℝ :=
  calc ⟪dirichletEigenfunction Ω hΩ hne n, x⟫_ℝ
      = laplaceForm Ω (dirichletEigenfunction Ω hΩ hne n) x :=
        (laplaceForm_apply_eq_inner Ω _ _).symm
    _ = dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n) x
        + ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume (dirichletEigenfunction Ω hΩ hne n),
          SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume x⟫_ℝ :=
        laplaceForm_apply_eq_dirichletForm_add Ω _ _
    _ = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
          SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume x⟫_ℝ
        + ⟪dirichletEigenbasis Ω hΩ hne n,
          SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume x⟫_ℝ :=
        congrArg₂ (· + ·) (dirichletForm_dirichletEigenfunction Ω hΩ hne n x)
          (congrArg (fun y ↦ ⟪y, SobolevMultiIndexZero.fnL ℝ
            (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume x⟫_ℝ)
            (fnL_dirichletEigenfunction Ω hΩ hne n))
    _ = _ := by ring

/-- **The Dirichlet eigenfunctions normalized in `H^1` form a Hilbert basis of `H^1_0(Ω)`**
([brezis2011functional] Chapter 9, Remark 28, second clause): `n ↦ u_n / √(λ_n + 1)`, for the
inner product `∫ (∇u·∇v + uv)` the type carries, by `HilbertBasis.ofInnerEqMul` with
`⟪u_n, x⟫_{H^1} = (λ_n + 1) ⟪e_n, x⟫_{L²}`. -/
def sobolevZeroEigenbasis : HilbertBasis ℕ ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  HilbertBasis.ofInnerEqMul (dirichletEigenbasis Ω hΩ hne)
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume).toLinearMap
    SobolevMultiIndexZero.fnL_injective (dirichletEigenfunction Ω hΩ hne)
    (fun n ↦ dirichletEigenvalue Ω hΩ n + 1)
    (fun n ↦ by linarith [dirichletEigenvalue_pos Ω hΩ hne n])
    (fnL_dirichletEigenfunction Ω hΩ hne) (inner_dirichletEigenfunction_left Ω hΩ hne)

/-- The vectors of the `H^1` basis are `u_n / √(λ_n + 1)`. -/
theorem coe_sobolevZeroEigenbasis :
    ⇑(sobolevZeroEigenbasis Ω hΩ hne)
      = fun n ↦ (√(dirichletEigenvalue Ω hΩ n + 1))⁻¹ • dirichletEigenfunction Ω hΩ hne n :=
  HilbertBasis.coe_ofInnerEqMul _ _ _ _ _ _ _ _

/-- **[brezis2011functional] Chapter 9, Remark 28, second clause**: `(e_n / √(λ_n + 1))` is a
Hilbert basis of `H^1_0(Ω)` for the scalar product `∫ (∇u·∇v + uv)` — there is a
`HilbertBasis ℕ ℝ (H^1_0(Ω))` whose `n`-th vector is `u_n / √(λ_n + 1)`, `u_n ∈ H^1_0(Ω)` the
`n`-th Dirichlet eigenfunction (`Elliptic.sobolevZeroEigenbasis`). -/
theorem hilbertBasis_sobolevZero :
    ∃ b : HilbertBasis ℕ ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω),
      ∀ n, b n = (√(dirichletEigenvalue Ω hΩ n + 1))⁻¹ • dirichletEigenfunction Ω hΩ hne n :=
  ⟨sobolevZeroEigenbasis Ω hΩ hne, fun n ↦ congrFun (coe_sobolevZeroEigenbasis Ω hΩ hne) n⟩

include hΩ in
/-- The operator of the Dirichlet form is symmetric and coercive on `H^1_0(Ω)` of a bounded
`Ω` (Poincaré's inequality). -/
theorem dirichletOperator_isSymmetricCoercive :
    (dirichletOperator Ω).toLinearMap.IsSymmetricCoercive :=
  restrictOperator_isSymmetricCoercive Ω _ (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- **The Dirichlet eigenfunctions normalized in the Dirichlet energy form a Hilbert basis of
`H^1_0(Ω)` for the scalar product `∫ ∇u·∇v`** ([brezis2011functional] Chapter 9, Remark 28,
first clause): `n ↦ u_n / √λ_n` on the energy space `WithEnergy (dirichletOperator Ω) _`. -/
def dirichletEnergyEigenbasis :
    HilbertBasis ℕ ℝ (WithEnergy (dirichletOperator Ω).toLinearMap
      (dirichletOperator_isSymmetricCoercive Ω hΩ)) :=
  energyEigenbasis Ω hΩ.measure_lt_top.ne hne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- The vectors of the energy basis are `u_n / √λ_n`. -/
theorem coe_dirichletEnergyEigenbasis :
    ⇑(dirichletEnergyEigenbasis Ω hΩ hne) = fun n ↦ (√(dirichletEigenvalue Ω hΩ n))⁻¹
      • WithEnergy.equiv _ _ (dirichletEigenfunction Ω hΩ hne n) :=
  coe_energyEigenbasis Ω hΩ.measure_lt_top.ne hne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- **[brezis2011functional] Chapter 9, Remark 28, first clause**: `(e_n / √λ_n)` is a Hilbert
basis of `H^1_0(Ω)` for the scalar product `∫ ∇u·∇v` — there is a Hilbert basis of the energy
space `WithEnergy (dirichletOperator Ω) _` whose `n`-th vector is `u_n / √λ_n`
(`Elliptic.dirichletEnergyEigenbasis`). -/
theorem hilbertBasis_energy :
    ∃ b : HilbertBasis ℕ ℝ (WithEnergy (dirichletOperator Ω).toLinearMap
      (dirichletOperator_isSymmetricCoercive Ω hΩ)),
      ∀ n, b n = (√(dirichletEigenvalue Ω hΩ n))⁻¹
        • WithEnergy.equiv _ _ (dirichletEigenfunction Ω hΩ hne n) :=
  ⟨dirichletEnergyEigenbasis Ω hΩ hne, fun n ↦ congrFun (coe_dirichletEnergyEigenbasis Ω hΩ hne) n⟩

end SobolevZeroBasis

/-! ### Remark 30: a general symmetric elliptic operator -/

section General

/-- The sum of two Hermitian forms is Hermitian. Belongs beside `SesqForm.IsHermitian` in
`Numlib/Variational/Forms.lean`. -/
theorem _root_.SesqForm.IsHermitian.add {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] {a b : SesqForm 𝕜 V} (ha : a.IsHermitian) (hb : b.IsHermitian) :
    (a + b).IsHermitian := fun u v ↦ by
  rw [add_apply, add_apply, add_apply, add_apply, map_add, ha u v, hb u v]

/-- A real multiple of a Hermitian real form is Hermitian. Belongs beside `SesqForm.IsHermitian`
in `Numlib/Variational/Forms.lean`. -/
theorem _root_.SesqForm.IsHermitian.smul_real {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} (c : ℝ) (ha : a.IsHermitian) :
    (c • a).IsHermitian := fun u v ↦ by
  rw [smul_apply, smul_apply, smul_apply, smul_apply, conj_trivial, smul_eq_mul, smul_eq_mul,
    ha u v, conj_trivial]

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-- A pairing through the identity of a multi-index with itself is a Hermitian form. -/
theorem pairing_id_isHermitian (α : MultiIndexLE (Fin N) 1) :
    (pairing Ω (ContinuousLinearMap.id ℝ _) α α).IsHermitian := fun u v ↦ by
  rw [conj_trivial]
  exact pairing_id_comm Ω α α u v

end General

section Remark30

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  {A : Fin (d + 1) → Fin (d + 1) →
    Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))} {α : ℝ}

/-- **Remark 30, for a shifted form**: if `a` is a Hermitian form coercive on `H^1_0(Ω)` with
`a(u, v) = ∫ ∑ a_ij ∂ᵢu ∂ⱼv + ∫ a₀ u v + μ ∫ u v`, then the eigenbasis of `a` with the
eigenvalues shifted back by `μ` is the spectral decomposition (84) of the operator with
coefficients `a_ij`, `a₀`. -/
theorem exists_hilbertBasis_eigen_of_shift
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    (a : SesqForm ℝ (SobolevEuclidean (d + 1) 1 2 Ω)) (hherm : a.IsHermitian)
    (hcoer : (a.restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoercive) (μ : ℝ)
    (hkey : ∀ u v : SobolevEuclidean (d + 1) 1 2 Ω, a u v = generalForm Ω A 0 a₀ u v
      + μ * ⟪SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume u,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume v⟫_ℝ) :
    ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))))
      (lam : ℕ → ℝ), Tendsto lam atTop atTop ∧
      ∀ n, ∃ u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u
          = e n ∧
        ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, generalForm Ω A 0 a₀ u φ
          = lam n * ⟪e n, SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
            1 2 Ω volume φ⟫_ℝ := by
  refine ⟨eigenbasis Ω hΩ hne a hherm hcoer, fun n ↦ eigenvalue Ω hΩ a hherm hcoer n - μ,
    (tendsto_atTop_add_const_right _ (-μ) (tendsto_eigenvalue_atTop Ω hΩ hne a hherm hcoer)).congr
      fun n ↦ (sub_eq_add_neg _ _).symm, fun n ↦ ?_⟩
  refine ⟨eigenfunction Ω hΩ hne a hherm hcoer n, (eigenfunction Ω hΩ hne a hherm hcoer n).2,
    fnL_eigenfunction Ω hΩ hne a hherm hcoer n, fun φ hφ ↦ ?_⟩
  have h1 : a (eigenfunction Ω hΩ hne a hherm hcoer n) φ = eigenvalue Ω hΩ a hherm hcoer n
      * ⟪eigenbasis Ω hΩ hne a hherm hcoer n,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume φ⟫_ℝ :=
    form_eigenfunction Ω hΩ hne a hherm hcoer n ⟨φ, hφ⟩
  have h2 := hkey (eigenfunction Ω hΩ hne a hherm hcoer n) φ
  have h3 : ⟪SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
        volume (eigenfunction Ω hΩ hne a hherm hcoer n),
      SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ
      = ⟪eigenbasis Ω hΩ hne a hherm hcoer n,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume φ⟫_ℝ :=
    congrArg (fun y ↦ ⟪y, SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      1 2 Ω volume φ⟫_ℝ) (fnL_eigenfunction Ω hΩ hne a hherm hcoer n)
  rw [h3] at h2
  change _ = (eigenvalue Ω hΩ a hherm hcoer n - μ) * _
  linear_combination h1 - h2

/-- **[brezis2011functional] Chapter 9, Remark 30**: for an open `Ω ⊆ ℝ^N` (`N = d + 1`) of
finite measure, nonempty, `L^∞` coefficients `a_ij` satisfying the ellipticity condition (36)
and *symmetric* (`a_ij = a_ji`, a hypothesis the book omits and without which the solution
operator is not self-adjoint), and `a₀ ∈ L^∞(Ω)`, there are a Hilbert basis `(e_n)` of `L²(Ω)`
and reals `λ_n → +∞` such that each `e_n` is the function of some `u_n ∈ H^1_0(Ω)` with
`∫_Ω ∑ a_ij ∂ᵢu_n ∂ⱼφ + ∫_Ω a₀ u_n φ = λ_n ∫_Ω e_n φ` for all `φ ∈ H^1_0(Ω)` (84). Proof:
`Elliptic.eigenbasis` for the shifted form `a = generalForm Ω A 0 a₀ + λ₀ ⟪·,·⟫_{L²}`, Hermitian
(`Elliptic.generalForm_isHermitian_of_symm`) and coercive on `H^1_0(Ω)` for the `λ₀` of Gårding's
inequality (`Elliptic.generalForm_garding_restrict_isCoercive`); its eigenvalues `λ'_n → +∞`
give `λ_n = λ'_n - λ₀`, which need not be positive. -/
theorem exists_hilbertBasis_eigen_general
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    (hA : IsUniformlyElliptic Ω A α) (hsymm : ∀ i j, A i j = A j i) :
    ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))))
      (lam : ℕ → ℝ), Tendsto lam atTop atTop ∧
      ∀ n, ∃ u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u
          = e n ∧
        ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, generalForm Ω A 0 a₀ u φ
          = lam n * ⟪e n, SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
            1 2 Ω volume φ⟫_ℝ :=
  exists_hilbertBasis_eigen_of_shift Ω hΩ hne
    (generalForm Ω A 0 a₀ + ((∑ i : Fin (d + 1),
      ‖(0 : Fin (d + 1) → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) i‖)
        ^ 2 / (2 * α) + ‖a₀‖ + α / 2) • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0)
    ((generalForm_isHermitian_of_symm Ω A a₀ hsymm).add ((pairing_id_isHermitian Ω 0).smul_real _))
    (generalForm_garding_restrict_isCoercive Ω hA) _ (add_smul_pairing_apply Ω _ _)

end Remark30

/-! ### Theorem 9.31: the classical equation for a smooth representative of `e_n` -/

section DirichletClassical

open Laplacian

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- **`-Δ e_n = λ_n e_n` in `Ω`** ([brezis2011functional] Theorem 9.31): a representative `ũ` of
the Dirichlet eigenfunction `e_n` that is `C²` on `Ω` satisfies `-Δ ũ x = λ_n ũ x` at every point
of `Ω`, by `Elliptic.laplacian_eq_of_eigenfunction` and the weak equation (83). The `C^∞`
representative itself comes from interior regularity (Remark 25). -/
theorem laplacian_eq_dirichletEigenfunction (n : ℕ) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω)
    (hU : (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u) :
    ∀ x ∈ Ω, -Δ u x = dirichletEigenvalue Ω hΩ n * u x :=
  laplacian_eq_of_eigenfunction Ω (U := dirichletEigenfunction Ω hΩ hne n)
    (lam := dirichletEigenvalue Ω hΩ n)
    (fun V hV ↦ (dirichletForm_dirichletEigenfunction Ω hΩ hne n
      ⟨V, SobolevMultiIndexZero.testFunctions_le hV⟩).trans
      (congrArg (fun y ↦ dirichletEigenvalue Ω hΩ n * ⟪y, SobolevMultiIndex.fnL ℝ
        (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
        (fnL_dirichletEigenfunction Ω hΩ hne n).symm))
    hu ((fn_dirichletEigenfunction Ω hΩ hne n).trans hU)

end DirichletClassical


/-! ### Smoothness of the eigenfunctions: interior regularity and regularity up to the boundary -/

section Smoothness

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

open SobolevMultiIndex

/-- **The weak eigenvalue equation against a test function, in terms of functions**: if
`U ∈ H^1(Ω)` satisfies `∫_Ω ∇U·∇V = λ ⟪U, V⟫` for every test-function element `V`, then for every
test function `φ`, `∫_Ω ∑ᵢ ∂ᵢU ∂ᵢφ = ∫_Ω (λ U) φ` — the hypothesis shape of the interior
regularity theorem `Elliptic.regularity_interior_higher`. -/
theorem integral_sum_weakDeriv_mul_fderiv_eq_of_eigenfunction {U : SobolevEuclidean N 1 2 Ω}
    {lam : ℝ}
    (hUw : ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω U V
        = lam * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
          fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, weakDeriv U (MultiIndexLE.single i) x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (lam • fn U) x * φ x := by
  obtain ⟨V, hV, hVφ⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
  have h1 := hUw V hV
  rw [dirichletForm_apply, L2.inner_eq_integral_mul, ← integral_const_mul] at h1
  have hVi : ∀ i, (weakDeriv V (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) := fun i ↦
    weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω (φ.contDiff.contDiffOn.of_le (by simp)) hVφ i
  have hL : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, weakDeriv U (MultiIndexLE.single i) x * weakDeriv V (MultiIndexLE.single i) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ∑ i, weakDeriv U (MultiIndexLE.single i) x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hVi] with x hx
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hx i]
  have hR : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      lam * (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U x
        * fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (lam • fn U) x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hVφ] with x hx
    rw [fnL_apply, fnL_apply, hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← hL, h1, hR]

/-- **The `H¹_loc`-to-`H^{m+2}_loc` bootstrap for a weak eigenfunction**: if `U ∈ H^1(Ω)`
satisfies the weak eigenvalue equation against the test functions and its function lies in
`H^m_loc(Ω)`, then it lies in `H^{m+2}_loc(Ω)`: the datum `λ U` of the equation `−ΔU = λ U` is in
`H^m_loc(Ω)`, and `Elliptic.regularity_interior_higher` applies. -/
theorem memSobolevMultiIndexLoc_add_two_of_eigenfunction {U : SobolevEuclidean N 1 2 Ω}
    {lam : ℝ}
    (hUw : ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω U V
        = lam * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
          fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
    {m : ℕ}
    (hm : MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) m 2 Ω
      volume) :
    MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) (m + 2) 2 Ω
      volume :=
  regularity_interior_higher m (memSobolevMultiIndex U).memSobolevMultiIndexLoc
    (fun i ↦ weakDeriv_hasWeakIteratedLineDerivOn_single U i)
    (fun V hVc hVΩ ↦ (hm V hVc hVΩ).const_smul lam)
    (integral_sum_weakDeriv_mul_fderiv_eq_of_eigenfunction Ω hUw)

/-- **A weak Dirichlet eigenfunction of `−Δ` lies in `H^m_loc(Ω)` for every `m`**
([brezis2011functional] §9.8, proof of Theorem 9.31, "`e_n ∈ ⋂_m H^m(ω)` for all `ω ⊂⊂ Ω`"):
if `U ∈ H^1(Ω)` satisfies `∫_Ω ∇U·∇V = λ ⟪U, V⟫` for every test-function element `V`, then the
function of `U` lies in `H^m_loc(Ω)` for every `m`. Induction on `m` two steps at a time: `U`
lies in `H^1_loc(Ω)`, and `U ∈ H^m_loc(Ω)` gives `U ∈ H^{m+2}_loc(Ω)` by interior regularity
(Remark 25, `Elliptic.regularity_interior_higher`) applied to the equation `−ΔU = λ U`, whose datum
`λ U` is then in `H^m_loc(Ω)`. -/
theorem eigenfunction_memSobolevMultiIndexLoc {U : SobolevEuclidean N 1 2 Ω} {lam : ℝ}
    (hUw : ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω U V
        = lam * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
          fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
    (m : ℕ) :
    MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) m 2 Ω volume := by
  have h1 : MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) 1 2 Ω
      volume := (memSobolevMultiIndex U).memSobolevMultiIndexLoc
  have key : ∀ m : ℕ,
      MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) m 2 Ω volume ∧
      MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) (m + 1) 2 Ω
        volume := by
    intro m
    induction m with
    | zero => exact ⟨h1.mono_order zero_le_one, h1⟩
    | succ m ih => exact ⟨ih.2, memSobolevMultiIndexLoc_add_two_of_eigenfunction Ω hUw ih.1⟩
  exact (key m).1

/-- **A weak Dirichlet eigenfunction of `−Δ` has a `C^∞` representative on `Ω`**: with the
hypotheses of `Elliptic.eigenfunction_memSobolevMultiIndexLoc`, the function of `U` agrees almost
everywhere on `Ω` with a function of class `C^∞` on `Ω`
(`MemSobolevMultiIndexLoc.exists_contDiffOn`). -/
theorem eigenfunction_exists_contDiffOn {U : SobolevEuclidean N 1 2 Ω} {lam : ℝ}
    (hUw : ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω U V
        = lam * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
          fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ ∞ ũ Ω ∧
      fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ :=
  MemSobolevMultiIndexLoc.exists_contDiffOn (eigenfunction_memSobolevMultiIndexLoc Ω hUw)

end Smoothness

section DirichletSmooth

open Laplacian SobolevMultiIndex

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- The weak eigenvalue equation (83) of the `n`-th Dirichlet eigenfunction against the
test-function elements, in the shape of `Elliptic.eigenfunction_memSobolevMultiIndexLoc`. -/
theorem dirichletForm_dirichletEigenfunction_testFunctions (n : ℕ) :
    ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n) V
        = dirichletEigenvalue Ω hΩ n
          * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
              (dirichletEigenfunction Ω hΩ hne n),
            fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume V⟫_ℝ :=
  fun V hV ↦ (dirichletForm_dirichletEigenfunction Ω hΩ hne n
    ⟨V, SobolevMultiIndexZero.testFunctions_le hV⟩).trans
    (congrArg (fun y ↦ dirichletEigenvalue Ω hΩ n * ⟪y, fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
      (fnL_dirichletEigenfunction Ω hΩ hne n).symm)

/-- **[brezis2011functional] Theorem 9.31, the smoothness clauses**: for every `n` there is
`ũ : ℝ^N → ℝ` of class `C^∞` on `Ω` (`e_n ∈ C^∞(Ω)`), agreeing almost everywhere on `Ω` with the
`n`-th Dirichlet eigenfunction `e_n = dirichletEigenbasis Ω hΩ hne n`, with
`−Δ ũ x = λ_n ũ x` at every point `x ∈ Ω` (`−Δ e_n = λ_n e_n` in `Ω`). The representative comes
from interior regularity (`Elliptic.eigenfunction_exists_contDiffOn`, Remark 25) and the pointwise
equation from `Elliptic.laplacian_eq_dirichletEigenfunction`. With `dirichletEigenbasis`,
`dirichletEigenvalue_pos`, `tendsto_dirichletEigenvalue_atTop` and `dirichletEigenfunction`, this
is the whole of Theorem 9.31. -/
theorem dirichletEigenbasis_exists_contDiffOn (n : ℕ) :
    ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, ContDiffOn ℝ ∞ ũ Ω ∧
      (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ ∧
      ∀ x ∈ Ω, -Δ ũ x = dirichletEigenvalue Ω hΩ n * ũ x := by
  obtain ⟨ũ, hũ, hae⟩ := eigenfunction_exists_contDiffOn Ω
    (dirichletForm_dirichletEigenfunction_testFunctions Ω hΩ hne n)
  have hae' : (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ :=
    (fn_dirichletEigenfunction Ω hΩ hne n).symm.trans hae
  exact ⟨ũ, hũ, hae', laplacian_eq_dirichletEigenfunction Ω hΩ hne n
    (hũ.of_le (by simp)) hae'⟩

/-- **The Dirichlet eigenfunction `u_n ∈ H^1_0(Ω)` solves `−Δu + u = (λ_n + 1) e_n` weakly**: it
is the Galerkin solution of the form of `−Δ + 1` with the datum `(λ_n + 1) e_n` on `H^1_0(Ω)`,
by `laplaceForm_apply_eq_dirichletForm_add` and the weak eigenvalue equation (83). -/
theorem dirichletEigenfunction_isGalerkinSolution_laplace (n : ℕ) :
    IsGalerkinSolution (laplaceForm Ω)
      (load Ω ((dirichletEigenvalue Ω hΩ n + 1) • dirichletEigenbasis Ω hΩ hne n))
      (SobolevEuclideanZero (d + 1) 1 2 Ω)
      (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω) := by
  refine ⟨(dirichletEigenfunction Ω hΩ hne n).2, fun φ hφ ↦ ?_⟩
  have h1 := laplaceForm_apply_eq_dirichletForm_add Ω
    (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω) φ
  have h2 : dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      φ = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ :=
    dirichletForm_dirichletEigenfunction Ω hΩ hne n ⟨φ, hφ⟩
  have h3 : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      = dirichletEigenbasis Ω hΩ hne n := fnL_dirichletEigenfunction Ω hΩ hne n
  have h4 : load Ω ((dirichletEigenvalue Ω hΩ n + 1) • dirichletEigenbasis Ω hΩ hne n) φ
      = (dirichletEigenvalue Ω hΩ n + 1) * ⟪dirichletEigenbasis Ω hΩ hne n,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ := by
    rw [load_apply_inner, real_inner_smul_left]
    rfl
  have h5 : dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      φ + ⟪fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω),
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ
      = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ
        + ⟪dirichletEigenbasis Ω hΩ hne n,
          fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ :=
    congrArg₂ (· + ·) h2 (congrArg (fun y ↦ ⟪y,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ) h3)
  refine h1.trans (h5.trans (Eq.trans ?_ h4.symm))
  ring

/-- **The Dirichlet eigenfunctions lie in `H^m(Ω)` for every `m`** on a `C^∞` domain (bounded, so
that the eigenbasis exists): `u_n` solves `−Δu + u = (λ_n + 1) e_n` weakly, so `u_n ∈ H^m` gives
`(λ_n + 1) e_n ∈ H^m`, hence `u_n ∈ H^{m+2}` by Theorem 9.25
(`Elliptic.regularity_dirichlet_higher_mem_laplace`); induction on `m`. -/
theorem dirichletEigenfunction_memSobolevMultiIndex
    (hΩ' : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (n : ℕ) (m : ℕ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑(dirichletEigenbasis Ω hΩ hne n)) m 2 Ω volume := by
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hΩ.closure.subset frontier_subset_closure
  have hfn : (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fn (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω) :=
    (fn_dirichletEigenfunction Ω hΩ hne n).symm
  -- the datum is in `H^m` whenever the eigenfunction is
  have hdat : ∀ j : ℕ, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑(dirichletEigenbasis Ω hΩ hne n)) j 2 Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (⇑((dirichletEigenvalue Ω hΩ n + 1) • dirichletEigenbasis Ω hΩ hne n)) j 2 Ω volume :=
    fun j hj ↦ (hj.const_smul (dirichletEigenvalue Ω hΩ n + 1)).congr_ae
      (Lp.coeFn_smul _ _).symm
  have key : ∀ m : ℕ,
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (⇑(dirichletEigenbasis Ω hΩ hne n)) m 2 Ω volume ∧
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (⇑(dirichletEigenbasis Ω hΩ hne n)) (m + 1) 2 Ω volume := by
    intro m
    induction m with
    | zero =>
      have h1 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
          (⇑(dirichletEigenbasis Ω hΩ hne n)) 1 2 Ω volume :=
        (memSobolevMultiIndex (dirichletEigenfunction Ω hΩ hne n :
          SobolevEuclidean (d + 1) 1 2 Ω)).congr_ae hfn.symm
      exact ⟨h1.mono_order zero_le_one, h1⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have := regularity_dirichlet_higher_mem_laplace m (hΩ'.of_le (by simp)) hΓ (hdat m ih.1)
        (dirichletEigenfunction_isGalerkinSolution_laplace Ω hΩ hne n)
      exact this.congr_ae hfn.symm
  exact (key m).1

/-- **[brezis2011functional] Chapter 9, Remark 29, second clause**: on a bounded nonempty open
set of class `C^∞`, every Dirichlet eigenfunction `e_n` agrees almost everywhere on `Ω` with a
function `ũ` continuous on `ℝ^N`, of class `C^∞` on `Ω`, all of whose derivatives extend
continuously from `Ω` to `ℝ^N` — `e_n ∈ C^∞(Ω̄)` in the sense of Chapter 9, footnote 16. The
eigenfunction solves `−Δu + u = (λ_n + 1) e_n` weakly with a datum in every `H^m(Ω)`
(`Elliptic.dirichletEigenfunction_memSobolevMultiIndex`), and Theorem 9.25's `C^∞(Ω̄)` clause
(`Elliptic.regularity_dirichlet_smooth`) applies. -/
theorem exists_contDiffOn_closure_eigenfunction
    (hΩ' : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (n : ℕ) :
    ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous ũ ∧ ContDiffOn ℝ ∞ ũ Ω ∧
      (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ ∧
      ∀ j : ℕ, ∃ G : EuclideanSpace ℝ (Fin (d + 1)) →
        (EuclideanSpace ℝ (Fin (d + 1)) [×j]→L[ℝ] ℝ), Continuous G ∧
        EqOn (iteratedFDeriv ℝ j ũ) G Ω := by
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hΩ.closure.subset frontier_subset_closure
  have hf : ∀ m : ℕ, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑((dirichletEigenvalue Ω hΩ n + 1) • dirichletEigenbasis Ω hΩ hne n)) m 2 Ω volume :=
    fun m ↦ ((dirichletEigenfunction_memSobolevMultiIndex Ω hΩ hne hΩ' n m).const_smul
      (dirichletEigenvalue Ω hΩ n + 1)).congr_ae (Lp.coeFn_smul _ _).symm
  obtain ⟨ũ, hc, hk, hae, hG⟩ := regularity_dirichlet_smooth hΩ' hΓ hf
    (dirichletEigenfunction_isGalerkinSolution_laplace Ω hΩ hne n)
  exact ⟨ũ, hc, hk, (fn_dirichletEigenfunction Ω hΩ hne n).symm.trans hae, hG⟩

end DirichletSmooth

end Elliptic
