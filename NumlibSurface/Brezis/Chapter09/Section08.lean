import Numlib.Analysis.PDE.Elliptic.Spectral
import NumlibSurface.Brezis.Chapter09.Section07

/-!
# Brezis §9.8: Eigenfunctions and spectral decomposition

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §9.8, on a bounded open subset `Ω` of
`ℝ^N = EuclideanSpace ℝ (Fin N)` with Lebesgue measure: Theorem 9.31 (the Dirichlet
eigenfunctions of `-Δ` form a Hilbert basis of `L²(Ω)`, lie in `H^1_0(Ω)`, with eigenvalues
`λ_n > 0` tending to `+∞`), Remark 28 (the bases of `H^1_0(Ω)` for its two scalar products) and
Remark 30 (general symmetric elliptic operators). Everything delegates to
`Numlib/Analysis/PDE/Elliptic/Spectral`, which proves the theorem for an arbitrary symmetric
coercive form on `H^1_0(Ω)` and names the Dirichlet data `Elliptic.dirichletEigenbasis`,
`Elliptic.dirichletEigenvalue`, `Elliptic.dirichletEigenfunction`.

## Conventions

* The book's standing assumption "`Ω` is a bounded open set" is `Bornology.IsBounded Ω`, together
  with `Ω ≠ ∅` and `N ≥ 1` (`N = d + 1`), which the book leaves implicit: for an empty `Ω` or
  `N = 0` the space `L²(Ω)` is finite-dimensional and has no Hilbert basis indexed by `ℕ`.
* `H^1(Ω) = hSpace N Ω`, `H^1_0(Ω) = hZeroSpace N Ω` (§9.1, §9.4); "`e_n ∈ H^1_0(Ω)`" is the
  existence of `u_n ∈ H^1_0(Ω)` with function `e_n`, and the weak eigenvalue equation (83) is
  written with the book's integrals, `∫_Ω ∇u_n · ∇φ = λ_n ∫_Ω e_n φ` for all `φ ∈ H^1_0(Ω)`.
* Theorem 9.31 is stated as the book's existential (`theorem_9_31`), its witnesses being the
  backbone's named data; the clause "`e_n ∈ C^∞(Ω)` and `-Δe_n = λ_n e_n` in `Ω`" (pointwise,
  with Mathlib's Laplacian `Δ`, for the `C^∞` representative) is the separate node
  `theorem_9_31_smooth`, which waits for the backbone's smooth representative; the classical
  equation for any `C²` representative is `theorem_9_31_laplacian`.
* Remark 28 is stated for the data of Theorem 9.31: the scalar product `∫_Ω ∇u · ∇v` is that of
  the energy space `WithEnergy` of the operator of the Dirichlet form on `H^1_0(Ω)`, and
  `∫_Ω (∇u · ∇v + uv)` is the scalar product `H^1_0(Ω)` carries; both identifications are part of
  the statements.
* Remark 30 carries the symmetry `a_ij = a_ji`, which the book omits and without which there is
  no orthonormal basis of eigenfunctions; its `λ_n` need not be positive. The ellipticity
  condition (36) on the `L^∞` classes is the almost-everywhere `Elliptic.IsUniformlyElliptic`, as
  in §9.5. Remark 29 (`e_n ∈ L^∞(Ω)`, and `e_n ∈ C^∞(Ω̄)` on a `C^∞` domain) is stated by the
  book without proof and is not restated here.
* The book's proof "repeat the proof of Theorem 8.21" refers to the one-dimensional
  Sturm–Liouville theorem, which is its Theorem 8.22.

## Main results

* `theorem_9_31`, `theorem_9_31_laplacian`; `theorem_9_31_smooth` waits for the backbone.
* `remark_9_28`, `remark_9_28_h1`.
* `remark_9_30`.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal InnerProductSpace

namespace Brezis.Chapter09

section Spectral

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-! ### Theorem 9.31 -/

/-- **Theorem 9.31, the Hilbert-space clauses.** Let `Ω ⊆ ℝ^N` be a bounded open set (nonempty,
`N ≥ 1`). There exist a Hilbert basis `(e_n)_{n ≥ 1}` of `L²(Ω)` and a sequence `(λ_n)_{n ≥ 1}` of
reals with `λ_n > 0` for all `n` and `λ_n → +∞` (moreover increasing) such that
`e_n ∈ H^1_0(Ω)` and `-Δe_n = λ_n e_n` in `Ω` in the weak sense (83): `e_n` is the function of an
element `u_n ∈ H^1_0(Ω)` with `∫_Ω ∇u_n · ∇φ = λ_n ∫_Ω e_n φ` for all `φ ∈ H^1_0(Ω)`. The
witnesses are the backbone's `Elliptic.dirichletEigenbasis`, `Elliptic.dirichletEigenvalue` and
`Elliptic.dirichletEigenfunction`: the solution operator `T` of `∫_Ω ∇u · ∇φ = ∫_Ω f φ` on
`H^1_0(Ω)` is self-adjoint, compact (`H^1_0(Ω) ⊂ L²(Ω)` with compact injection, Remark 20),
positive and injective, and the spectral theorem for compact self-adjoint operators (Theorem 6.11)
gives the basis, with `λ_n = 1/μ_n`. The clause "`e_n ∈ C^∞(Ω)`, and `-Δe_n = λ_n e_n` pointwise
in `Ω`" (Remark 25 iterated) is `theorem_9_31_smooth`. -/
theorem theorem_9_31 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty) :
    ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))) (lam : ℕ → ℝ),
      (∀ n, 0 < lam n) ∧ Monotone lam ∧ Tendsto lam atTop atTop ∧
      ∀ n, ∃ u : hSpace (d + 1) Ω, u ∈ hZeroSpace (d + 1) Ω ∧
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] e n ∧
        ∀ φ ∈ hZeroSpace (d + 1) Ω,
          ∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x
            = lam n * ∫ x in (Ω : Set 𝔼), e n x * SobolevMultiIndex.fn φ x := by
  refine ⟨Elliptic.dirichletEigenbasis Ω hb hne, Elliptic.dirichletEigenvalue Ω hb,
    Elliptic.dirichletEigenvalue_pos Ω hb hne, Elliptic.monotone_dirichletEigenvalue Ω hb hne,
    Elliptic.tendsto_dirichletEigenvalue_atTop Ω hb hne, fun n ↦
    ⟨Elliptic.dirichletEigenfunction Ω hb hne n, (Elliptic.dirichletEigenfunction Ω hb hne n).2,
      Elliptic.fn_dirichletEigenfunction Ω hb hne n, fun φ hφ ↦ ?_⟩⟩
  have h := Elliptic.dirichletForm_dirichletEigenfunction Ω hb hne n ⟨φ, hφ⟩
  refine (Elliptic.dirichletForm_apply Ω _ _).symm.trans (h.trans ?_)
  exact congrArg (fun y ↦ Elliptic.dirichletEigenvalue Ω hb n * y)
    (Elliptic.inner_eq_integral Ω _ _)

/-- **Theorem 9.31, "`-Δe_n = λ_n e_n` in `Ω`" for a `C²` representative**: if `e ∈ L²(Ω)` is
the function of some `u ∈ H^1(Ω)` satisfying the weak equation (83) with the eigenvalue `λ`,
`∫_Ω ∇u · ∇φ = λ ∫_Ω e φ` for all `φ ∈ H^1_0(Ω)`, and `e` agrees almost everywhere on `Ω` with a
function `ẽ` of class `C²` on `Ω`, then `-Δ ẽ x = λ ẽ x` at every point `x ∈ Ω`, with Mathlib's
Laplacian `Δ`. The backbone's `Elliptic.laplacian_eq_of_eigenfunction` (Step D of §9.5, Example 1,
for the equation `-Δu + u = (λ + 1) u`, and the continuity of both sides on the open `Ω`). -/
theorem theorem_9_31_laplacian {e : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {lam : ℝ}
    {u : hSpace (d + 1) Ω} (hue : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] e)
    (heq : ∀ φ ∈ hZeroSpace (d + 1) Ω,
      ∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x
        = lam * ∫ x in (Ω : Set 𝔼), e x * SobolevMultiIndex.fn φ x)
    {e₀ : 𝔼 → ℝ} (hc : ContDiffOn ℝ 2 e₀ Ω)
    (he₀ : (e : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] e₀) :
    ∀ x ∈ Ω, -Δ e₀ x = lam * e₀ x := by
  refine Elliptic.laplacian_eq_of_eigenfunction Ω (U := u) (lam := lam) (fun V hV ↦ ?_) hc
    (hue.trans he₀)
  have h := heq V (SobolevMultiIndexZero.testFunctions_le hV)
  refine (Elliptic.dirichletForm_apply Ω _ _).trans (h.trans ?_)
  rw [Elliptic.inner_eq_integral]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hue] with x hx
  rw [SobolevMultiIndex.fnL_apply, hx]
  rfl

/-! ### Remark 28: the bases of `H^1_0(Ω)` -/

/-- **Remark 28, first clause.** Under the assumptions of Theorem 9.31, the sequence
`(e_n / √λ_n)` is a Hilbert basis of `H^1_0(Ω)` equipped with the scalar product `∫_Ω ∇u · ∇v`:
on the energy space `WithEnergy` of the operator `A` of the Dirichlet form on `H^1_0(Ω)`
(`Elliptic.dirichletOperator`, `⟪A u, v⟫_{H^1} = ∫_Ω ∇u · ∇v`), whose scalar product is
`∫_Ω ∇u · ∇v` (the first clause of the statement), there is a Hilbert basis whose `n`-th vector
is `u_n / √λ_n`, `u_n ∈ H^1_0(Ω)` the `n`-th eigenfunction of Theorem 9.31
(`Elliptic.dirichletEigenfunction`, whose function is `e_n`). The backbone's
`Elliptic.hilbertBasis_energy`: the orthonormality is (83), and the completeness the basis
property in `L²(Ω)` ("`f ⊥ e_n` in `H^1_0` for all `n` gives `λ_n ∫ e_n f = 0`, hence
`f = 0`"). -/
theorem remark_9_28 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty) :
    (∀ u v : hZeroSpace (d + 1) Ω,
      ⟪WithEnergy.equiv _ (Elliptic.dirichletOperator_isSymmetricCoercive Ω hb) u,
        WithEnergy.equiv _ (Elliptic.dirichletOperator_isSymmetricCoercive Ω hb) v⟫_ℝ
        = ∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv (u : hSpace (d + 1) Ω) i x
          * partialDeriv (v : hSpace (d + 1) Ω) i x) ∧
    ∃ b : HilbertBasis ℕ ℝ (WithEnergy (Elliptic.dirichletOperator Ω).toLinearMap
      (Elliptic.dirichletOperator_isSymmetricCoercive Ω hb)),
      ∀ n, b n = (√(Elliptic.dirichletEigenvalue Ω hb n))⁻¹
        • WithEnergy.equiv _ _ (Elliptic.dirichletEigenfunction Ω hb hne n) := by
  refine ⟨fun u v ↦ ?_, Elliptic.hilbertBasis_energy Ω hb hne⟩
  rw [WithEnergy.inner_equiv]
  exact (Elliptic.inner_dirichletOperator Ω u v).trans (Elliptic.dirichletForm_apply Ω _ _)

/-- **Remark 28, second clause.** Under the assumptions of Theorem 9.31, the sequence
`(e_n / √(λ_n + 1))` is a Hilbert basis of `H^1_0(Ω)` equipped with the scalar product
`∫_Ω (∇u · ∇v + uv)` — the scalar product of `H^1(Ω)` restricted to `H^1_0(Ω)`, which is the
one the type carries (the first clause of the statement): there is a
`HilbertBasis ℕ ℝ (H^1_0(Ω))` whose `n`-th vector is `u_n / √(λ_n + 1)`, `u_n ∈ H^1_0(Ω)` the
`n`-th eigenfunction of Theorem 9.31 (`Elliptic.dirichletEigenfunction`). The backbone's
`Elliptic.hilbertBasis_sobolevZero`: `⟪u_n, x⟫_{H^1} = (λ_n + 1) ⟪e_n, x⟫_{L²}` by (83), and the
completeness follows from the basis property in `L²(Ω)`. -/
theorem remark_9_28_h1 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty) :
    (∀ u v : hZeroSpace (d + 1) Ω, ⟪u, v⟫_ℝ
        = ∫ x in (Ω : Set 𝔼), ((∑ i, partialDeriv (u : hSpace (d + 1) Ω) i x
          * partialDeriv (v : hSpace (d + 1) Ω) i x)
          + SobolevMultiIndex.fn (u : hSpace (d + 1) Ω) x
            * SobolevMultiIndex.fn (v : hSpace (d + 1) Ω) x)) ∧
    ∃ b : HilbertBasis ℕ ℝ (hZeroSpace (d + 1) Ω),
      ∀ n, b n = (√(Elliptic.dirichletEigenvalue Ω hb n + 1))⁻¹
        • Elliptic.dirichletEigenfunction Ω hb hne n := by
  refine ⟨fun u v ↦ ?_, Elliptic.hilbertBasis_sobolevZero Ω hb hne⟩
  rw [Submodule.coe_inner, ← Elliptic.laplaceForm_apply_eq_inner, Elliptic.laplaceForm_apply]
  rfl

/-! ### Remark 30: general symmetric elliptic operators -/

/-- **Remark 30.** Let `a_ij ∈ L^∞(Ω)` be functions satisfying the ellipticity condition (36),
symmetric (`a_ij = a_ji`, a hypothesis the book omits and without which the solution operator is
not self-adjoint), and let `a₀ ∈ L^∞(Ω)`, on a bounded nonempty `Ω`. Then there exist a Hilbert
basis `(e_n)` of `L²(Ω)` and a sequence `(λ_n)` of reals with `λ_n → +∞` such that
`e_n ∈ H^1_0(Ω)` and `∫_Ω ∑_{i,j} a_ij ∂_i e_n ∂_j φ + ∫_Ω a₀ e_n φ = λ_n ∫_Ω e_n φ` for all
`φ ∈ H^1_0(Ω)` (84): each `e_n` is the function of some `u_n ∈ H^1_0(Ω)` satisfying (84). The
backbone's `Elliptic.exists_hilbertBasis_eigen_general`: the construction of Theorem 9.31 for
the form shifted by Gårding's constant `λ₀` (Hermitian by the symmetry, coercive on `H^1_0(Ω)`
by Gårding's inequality), whose eigenvalues `λ'_n → +∞` give `λ_n = λ'_n − λ₀`, not necessarily
positive. -/
theorem remark_9_30 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty)
    {A : Fin (d + 1) → Fin (d + 1) → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))}
    {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))} {α : ℝ}
    (hA : Elliptic.IsUniformlyElliptic Ω A α) (hsymm : ∀ i j, A i j = A j i) :
    ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))) (lam : ℕ → ℝ),
      Tendsto lam atTop atTop ∧
      ∀ n, ∃ u : hSpace (d + 1) Ω, u ∈ hZeroSpace (d + 1) Ω ∧
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] e n ∧
        ∀ φ ∈ hZeroSpace (d + 1) Ω,
          (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
            + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
            = lam n * ∫ x in (Ω : Set 𝔼), e n x * SobolevMultiIndex.fn φ x := by
  obtain ⟨e, lam, hlam, h⟩ :=
    Elliptic.exists_hilbertBasis_eigen_general Ω hb.measure_lt_top.ne hne hA hsymm
  refine ⟨e, lam, hlam, fun n ↦ ?_⟩
  obtain ⟨u, hu0, hue, heq⟩ := h n
  refine ⟨u, hu0, EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) ↦
    (z : 𝔼 → ℝ)) hue), fun φ hφ ↦ ?_⟩
  rw [← generalForm_zero_drift_apply, heq φ hφ, Elliptic.inner_eq_integral]
  rfl

end Spectral

end Brezis.Chapter09
