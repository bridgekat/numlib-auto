/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural homes: `Mathlib.LinearAlgebra.Eigenspace.Minpoly` (the spectral mapping theorem for
eigenvalues), `Mathlib.Analysis.InnerProductSpace.Spectrum` (numerical range, isometries).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Numlib.Eigen.NumericalRange

/-!
# Spectral theory of bounded operators beyond Mathlib

The operator-theoretic part of [brezis2011functional] §11.4 (Propositions 11.29, 11.32, 11.33,
11.37 and Remark 1), in three groups.

* **Eigenvalues under polynomials.** `Module.End.hasEigenvalue_aeval_iff`: over an algebraically
  closed field, for a polynomial `p` of positive degree, `μ` is an eigenvalue of `p(f)` iff
  `μ = p(ν)` for some eigenvalue `ν` of `f` — the `EV` half of [brezis2011functional]
  Proposition 11.32, display (20). Mathlib has the inclusion `p(EV f) ⊆ EV(p(f))`
  (`Module.End.aeval_apply_of_hasEigenvector`) and the spectrum half
  (`spectrum.map_polynomial_aeval`), but not this. The converse is by induction on the degree,
  splitting off one root factor `X - C ν` at a time: if `p(f)` kills `x ≠ 0` then either
  `q(f) x ≠ 0` is an eigenvector of `f` for the root `ν` or `q(f)` kills `x`, with `p = (X - ν) q`.
  The degree hypothesis is needed: for `p = C c` and `f` without eigenvalues (the right shift) the
  left side is `c = μ` while the right side is empty.
* **The numerical range** `W(T) = {⟪u, T u⟫ / ⟪u, u⟫ : u ≠ 0}` (the backbone's
  `LinearMap.numericalRange`, convex by `LinearMap.convex_numericalRange`) on a complex Hilbert
  space: the estimate `dist (λ, W(T)) ‖u‖ ≤ ‖T u - λ u‖`
  (`ContinuousLinearMap.infDist_numericalRange_mul_norm_le_norm_sub_smul`), so that
  `λ ∉ closure W(T)` puts `λ` in the resolvent set
  (`ContinuousLinearMap.mem_resolventSet_of_notMem_closure_numericalRange`, by Mathlib's
  Lax–Milgram criterion `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`, which is
  [brezis2011functional] Proposition 11.29) with the resolvent bound
  `‖(T - λ)⁻¹‖ ≤ 1 / dist (λ, W(T))`
  (`ContinuousLinearMap.norm_resolvent_le_inv_infDist_numericalRange`); hence
  `σ(T) ⊆ closure W(T)` (`ContinuousLinearMap.spectrum_subset_closure_numericalRange`,
  [brezis2011functional] Proposition 11.33). Remark 1 of that section,
  `ContinuousLinearMap.exists_re_inner_smul_ge_of_norm_inner_ge`: the hypothesis
  `|⟪u, T u⟫| ≥ α ‖u‖²` of the "more general" Lax–Milgram is the coercivity `re ⟪u, ξ T u⟫ ≥ α ‖u‖²`
  after a rotation by a unit complex number `ξ`, obtained by projecting `0` onto the closed convex
  set `closure W(T)`.
* **Isometries** ([brezis2011functional] Proposition 11.37): the eigenvalues of an isometry lie on
  the unit circle (`ContinuousLinearMap.norm_eq_one_of_hasEigenvalue_of_isometry`, over any normed
  field); a surjective isometry of a Hilbert space is unitary
  (`ContinuousLinearMap.mem_unitary_of_isometry_of_surjective`, so that Mathlib's
  `spectrum.subset_circle_of_unitary` gives `σ(T) ⊆ S¹`); and a non-surjective isometry of a
  complex Hilbert space has the whole closed unit disc as its spectrum
  (`ContinuousLinearMap.spectrum_eq_closedBall_of_isometry_of_not_surjective`): for `|λ| < 1`,
  `T - λ = (1 - λ T†) T` with `1 - λ T†` invertible, so `T - λ` invertible would make `T` onto.

Conventions: Mathlib's inner product is conjugate-linear in the first slot, so the book's
`(T u, u)` is `⟪u, T u⟫` here. The compact normal spectral theorem (Proposition 11.36) is
`Numlib.Analysis.InnerProductSpace.CompactSpectral.Normal`, on the assembly lemma of
`CompactSpectral.Basis`; the spectral radius material (Proposition 11.31) is
`Numlib.Analysis.Normed.Algebra.SpectralRadius` and Mathlib.
-/

open scoped InnerProductSpace

/-! ### Eigenvalues under polynomials -/

namespace Module.End

open Polynomial

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]

/-- If `0` is an eigenvalue of `p(f)` for a nonzero polynomial `p` over an algebraically closed
field, some root of `p` is an eigenvalue of `f`: split off a root factor `p = (X - ν) q`; either
`q(f) x` is a `ν`-eigenvector or `q(f)` already kills the eigenvector `x`, and induct on the
degree. -/
theorem exists_hasEigenvalue_isRoot_of_hasEigenvalue_aeval_zero (f : Module.End K V) (p : K[X])
    (hp : p ≠ 0) (h : (aeval f p).HasEigenvalue 0) : ∃ ν, f.HasEigenvalue ν ∧ p.IsRoot ν := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  have hpx : aeval f p x = 0 := by simpa using hx.apply_eq_smul
  rcases eq_or_ne p.degree 0 with hdeg | hdeg
  · -- a nonzero constant polynomial has no eigenvalue `0`
    exfalso
    rw [eq_C_of_degree_eq_zero hdeg, aeval_C, Module.algebraMap_end_apply] at hpx
    rcases smul_eq_zero.1 hpx with hc | hx0
    · exact hp (by rw [eq_C_of_degree_eq_zero hdeg, hc, C_0])
    · exact hx.2 hx0
  · obtain ⟨ν, hν⟩ := IsAlgClosed.exists_root p hdeg
    have hfac : (X - C ν) * (p / (X - C ν)) = p := mul_div_eq_iff_isRoot.2 hν
    set q := p / (X - C ν) with hq
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hfac
      exact hp hfac.symm
    have hqdeg : q.natDegree < p.natDegree :=
      natDegree_lt_natDegree hq0 (degree_div_lt hp (by rw [degree_X_sub_C]; exact zero_lt_one))
    by_cases hy : aeval f q x = 0
    · -- `q(f)` kills `x`: induct
      have hev : (aeval f q).HasEigenvalue 0 :=
        hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 (by rw [hy, zero_smul]), hx.2⟩
      obtain ⟨ν', hν', hroot⟩ := ih q.natDegree (hn ▸ hqdeg) q hq0 hev rfl
      refine ⟨ν', hν', ?_⟩
      rw [← hfac, IsRoot.def, eval_mul, IsRoot.def.1 hroot, mul_zero]
    · -- `q(f) x ≠ 0` is an eigenvector of `f` for the root `ν`
      refine ⟨ν, hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 ?_, hy⟩, hν⟩
      have h1 : aeval f (X - C ν) (aeval f q x) = 0 := by
        rw [← Module.End.mul_apply, ← map_mul, hfac, hpx]
      rwa [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply,
        sub_eq_zero] at h1

/-- **The spectral mapping theorem for eigenvalues** ([brezis2011functional] Proposition 11.32,
display (20)): over an algebraically closed field, for a polynomial `p` of positive degree, `μ` is
an eigenvalue of `p(f)` iff `μ = p(ν)` for some eigenvalue `ν` of `f`. The degree hypothesis is
needed: for `p = C c` and `f` without eigenvalues the left side is `c = μ` and the right side
is empty. -/
theorem hasEigenvalue_aeval_iff (f : Module.End K V) {p : K[X]} (hp : 0 < p.degree) (μ : K) :
    (aeval f p).HasEigenvalue μ ↔ ∃ ν, f.HasEigenvalue ν ∧ p.eval ν = μ := by
  constructor
  · intro h
    have hp0 : p - C μ ≠ 0 := by
      intro h0
      have h1 : (p - C μ).degree = p.degree := degree_sub_C hp
      rw [h0, degree_zero] at h1
      rw [← h1] at hp
      exact not_lt_bot hp
    have h0 : (aeval f (p - C μ)).HasEigenvalue 0 := by
      obtain ⟨x, hx⟩ := h.exists_hasEigenvector
      refine hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 ?_, hx.2⟩
      rw [map_sub, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, hx.apply_eq_smul,
        sub_self, zero_smul]
    obtain ⟨ν, hν, hroot⟩ := exists_hasEigenvalue_isRoot_of_hasEigenvalue_aeval_zero f _ hp0 h0
    refine ⟨ν, hν, ?_⟩
    rw [IsRoot.def, eval_sub, eval_C, sub_eq_zero] at hroot
    exact hroot
  · rintro ⟨ν, hν, rfl⟩
    obtain ⟨x, hx⟩ := hν.exists_hasEigenvector
    exact hasEigenvalue_of_hasEigenvector
      ⟨mem_eigenspace_iff.2 (aeval_apply_of_hasEigenvector hx), hx.2⟩

end Module.End

/-! ### The numerical range and the resolvent -/

namespace ContinuousLinearMap

section NumericalRange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `⟪x, T x - λ x⟫ = (⟪x, T x⟫ / ⟪x, x⟫ - λ) ⟪x, x⟫` for `x ≠ 0`. -/
private theorem inner_sub_smul_eq (T : H →L[ℂ] H) (lam : ℂ) {x : H} (hx : x ≠ 0) :
    ⟪x, T x - lam • x⟫_ℂ = (⟪x, T x⟫_ℂ / ⟪x, x⟫_ℂ - lam) * ⟪x, x⟫_ℂ := by
  have hxx : ⟪x, x⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx
  rw [inner_sub_right, inner_smul_right, sub_mul, div_mul_cancel₀ _ hxx]

/-- `‖⟪x, T x - λ x⟫‖ = ‖⟪x, T x⟫ / ⟪x, x⟫ - λ‖ ‖x‖ ^ 2` for `x ≠ 0`. -/
private theorem norm_inner_sub_smul (T : H →L[ℂ] H) (lam : ℂ) {x : H} (hx : x ≠ 0) :
    ‖⟪x, T x - lam • x⟫_ℂ‖ = ‖⟪x, T x⟫_ℂ / ⟪x, x⟫_ℂ - lam‖ * ‖x‖ ^ 2 := by
  have h : ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
  rw [inner_sub_smul_eq T lam hx, norm_mul, h]

/-- The Rayleigh quotient of a nonzero vector lies in the numerical range. -/
private theorem div_inner_mem_numericalRange (T : H →L[ℂ] H) {x : H} (hx : x ≠ 0) :
    ⟪x, T x⟫_ℂ / ⟪x, x⟫_ℂ ∈ (T : H →ₗ[ℂ] H).numericalRange :=
  ⟨x, hx, rfl⟩

/-- The estimate inside [brezis2011functional] Proposition 11.33:
`dist (λ, W(T)) ‖u‖ ≤ ‖T u - λ u‖` for every `u`, where `W(T)` is the numerical range. For
`u ≠ 0` the Rayleigh quotient `z = ⟪u, T u⟫ / ⟪u, u⟫` lies in `W(T)` and
`‖z - λ‖ ‖u‖ ^ 2 = ‖⟪u, T u - λ u⟫‖ ≤ ‖u‖ ‖T u - λ u‖`. No completeness is needed. -/
theorem infDist_numericalRange_mul_norm_le_norm_sub_smul (T : H →L[ℂ] H) (lam : ℂ) (u : H) :
    Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange * ‖u‖ ≤ ‖T u - lam • u‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 hu
  have h1 : Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange ≤ ‖⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ - lam‖ :=
    calc Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange
        ≤ dist lam (⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ) :=
          Metric.infDist_le_dist_of_mem (div_inner_mem_numericalRange T hu)
      _ = ‖⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ - lam‖ := by rw [dist_eq_norm, norm_sub_rev]
  have h2 : ‖⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ - lam‖ * ‖u‖ ^ 2 ≤ ‖u‖ * ‖T u - lam • u‖ := by
    rw [← norm_inner_sub_smul T lam hu]
    exact norm_inner_le_norm _ _
  calc Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange * ‖u‖
      ≤ ‖⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ - lam‖ * ‖u‖ := by gcongr
    _ ≤ ‖T u - lam • u‖ := by
        refine le_of_mul_le_mul_left ?_ hu0
        calc ‖u‖ * (‖⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ - lam‖ * ‖u‖)
            = ‖⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ - lam‖ * ‖u‖ ^ 2 := by ring
          _ ≤ ‖u‖ * ‖T u - lam • u‖ := h2

variable [CompleteSpace H]

/-- **[brezis2011functional] Proposition 11.33, first clause**: a point outside the closure of
the numerical range is in the resolvent set. With `α = dist (λ, W(T)) > 0`,
`‖⟪u, (T - λ) u⟫‖ ≥ α ‖u‖ ^ 2` for all `u`, so `T - λ` is invertible by the Lax–Milgram criterion
`ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map` ([brezis2011functional] Proposition
11.29). -/
theorem mem_resolventSet_of_notMem_closure_numericalRange (T : H →L[ℂ] H) {lam : ℂ}
    (h : lam ∉ closure (T : H →ₗ[ℂ] H).numericalRange) : lam ∈ resolventSet ℂ T := by
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]
  suffices hunit : IsUnit (T - lam • (1 : H →L[ℂ] H)) by
    have := hunit.neg
    rwa [neg_sub] at this
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact isUnit_of_forall_le_norm_inner_map _ (c := 1) one_pos fun x => by
      simp [Subsingleton.elim x 0]
  have hne : (T : H →ₗ[ℂ] H).numericalRange.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    exact ⟨_, div_inner_mem_numericalRange T hx⟩
  have hα : 0 < Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange :=
    (Metric.infDist_pos_iff_notMem_closure hne).1 h
  refine isUnit_of_forall_le_norm_inner_map _ (c := ⟨_, hα.le⟩) (by exact_mod_cast hα) fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1 : Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange
      ≤ ‖⟪x, T x⟫_ℂ / ⟪x, x⟫_ℂ - lam‖ :=
    calc Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange
        ≤ dist lam (⟪x, T x⟫_ℂ / ⟪x, x⟫_ℂ) :=
          Metric.infDist_le_dist_of_mem (div_inner_mem_numericalRange T hx)
      _ = ‖⟪x, T x⟫_ℂ / ⟪x, x⟫_ℂ - lam‖ := by rw [dist_eq_norm, norm_sub_rev]
  calc ‖x‖ ^ 2 * ((⟨_, hα.le⟩ : NNReal) : ℝ)
      = Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange * ‖x‖ ^ 2 := by
        change ‖x‖ ^ 2 * Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange = _
        ring
    _ ≤ ‖⟪x, T x⟫_ℂ / ⟪x, x⟫_ℂ - lam‖ * ‖x‖ ^ 2 := by gcongr
    _ = ‖⟪x, T x - lam • x⟫_ℂ‖ := (norm_inner_sub_smul T lam hx).symm
    _ = ‖⟪(T - lam • (1 : H →L[ℂ] H)) x, x⟫_ℂ‖ := by
        rw [norm_inner_symm, sub_apply, smul_apply, one_apply_eq_self]

/-- **[brezis2011functional] Proposition 11.33, display (23)**: the spectrum lies in the closure
of the numerical range, `σ(T) ⊆ closure W(T)`. The convexity clause of that proposition is
`LinearMap.convex_numericalRange`. -/
theorem spectrum_subset_closure_numericalRange (T : H →L[ℂ] H) :
    spectrum ℂ T ⊆ closure (T : H →ₗ[ℂ] H).numericalRange := by
  intro lam hlam
  by_contra h
  exact spectrum.mem_iff.1 hlam
    (spectrum.mem_resolventSet_iff.1 (mem_resolventSet_of_notMem_closure_numericalRange T h))

omit [CompleteSpace H] in
/-- The resolvent bound of [brezis2011functional] Proposition 11.33 in pointwise form: for `λ` in
the resolvent set, `dist (λ, W(T)) ‖(λ - T)⁻¹ v‖ ≤ ‖v‖` for every `v`, where `(λ - T)⁻¹` is
Mathlib's `resolvent T λ`. This is `infDist_numericalRange_mul_norm_le_norm_sub_smul` at
`u = (λ - T)⁻¹ v`. -/
theorem infDist_numericalRange_mul_norm_resolvent_apply_le (T : H →L[ℂ] H) {lam : ℂ}
    (hlam : lam ∈ resolventSet ℂ T) (v : H) :
    Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange * ‖resolvent T lam v‖ ≤ ‖v‖ := by
  have h := infDist_numericalRange_mul_norm_le_norm_sub_smul T lam (resolvent T lam v)
  have h1 : (algebraMap ℂ (H →L[ℂ] H) lam - T) * resolvent T lam = 1 := by
    rw [spectrum.resolvent_eq hlam]
    have := hlam.unit.mul_inv
    rwa [hlam.unit_spec] at this
  have h2 : T (resolvent T lam v) - lam • resolvent T lam v = -v := by
    have h3 : (algebraMap ℂ (H →L[ℂ] H) lam - T) (resolvent T lam v) = v := by
      rw [← mul_apply_eq_comp, h1, one_apply_eq_self]
    rw [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self] at h3
    rw [← neg_sub, h3]
  rwa [h2, norm_neg] at h

/-- **[brezis2011functional] Proposition 11.33, second clause**: for `λ ∉ closure W(T)`,
`‖(λ - T)⁻¹‖ ≤ 1 / dist (λ, W(T))`. -/
theorem norm_resolvent_le_inv_infDist_numericalRange (T : H →L[ℂ] H) {lam : ℂ}
    (h : lam ∉ closure (T : H →ₗ[ℂ] H).numericalRange) :
    ‖resolvent T lam‖ ≤ (Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange)⁻¹ := by
  have hlam := mem_resolventSet_of_notMem_closure_numericalRange T h
  refine opNorm_le_bound _ (inv_nonneg.2 Metric.infDist_nonneg) fun v => ?_
  have hv := infDist_numericalRange_mul_norm_resolvent_apply_le T hlam v
  have hα0 : 0 ≤ Metric.infDist lam (T : H →ₗ[ℂ] H).numericalRange := Metric.infDist_nonneg
  rcases hα0.eq_or_lt with hα | hα
  · -- the numerical range is empty, so the space is trivial
    rw [← hα, inv_zero, zero_mul, norm_le_zero_iff]
    rcases subsingleton_or_nontrivial H with hH | hH
    · exact Subsingleton.elim _ _
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : H)
      have hne : (T : H →ₗ[ℂ] H).numericalRange.Nonempty := ⟨_, div_inner_mem_numericalRange T hx⟩
      exact ((Metric.infDist_pos_iff_notMem_closure hne).1 h).ne hα
  · rw [inv_mul_eq_div, le_div_iff₀ hα, mul_comm]
    exact hv

omit [CompleteSpace H] in
/-- **[brezis2011functional] §11.4, Remark 1**: if `|⟪u, T u⟫| ≥ α ‖u‖ ^ 2` for all `u` with
`α > 0`, then after a rotation by a unit complex number `ξ` the operator `ξ T` is coercive,
`re ⟪u, ξ T u⟫ ≥ α ‖u‖ ^ 2`. The numerical range is convex (Toeplitz–Hausdorff,
`LinearMap.convex_numericalRange`) and at distance at least `α` from `0`; if `p` is the
projection of `0` onto its closure, `ξ = conj p / ‖p‖` and the variational inequality of the
projection gives `re (ξ w) ≥ ‖p‖ ≥ α` for every `w` in the numerical range. -/
theorem exists_re_inner_smul_ge_of_norm_inner_ge (T : H →L[ℂ] H) {α : ℝ} (hα : 0 < α)
    (h : ∀ u, α * ‖u‖ ^ 2 ≤ ‖⟪u, T u⟫_ℂ‖) :
    ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ ∀ u, α * ‖u‖ ^ 2 ≤ RCLike.re ⟪u, (ξ • T) u⟫_ℂ := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact ⟨1, by simp, fun u => by simp [Subsingleton.elim u 0]⟩
  set W := (T : H →ₗ[ℂ] H).numericalRange with hW
  have hne : W.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    exact ⟨_, div_inner_mem_numericalRange T hx⟩
  have hconv : Convex ℝ (closure W) := (LinearMap.convex_numericalRange _).closure
  -- every point of the numerical range has modulus at least `α`
  have hWα : ∀ z ∈ W, α ≤ ‖z‖ := by
    rintro _ ⟨u, hu, rfl⟩
    have hu2 : 0 < ‖u‖ ^ 2 := by positivity
    have hxx : ‖⟪u, u⟫_ℂ‖ = ‖u‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
    rw [norm_div, hxx, le_div_iff₀ hu2]
    exact h u
  -- the projection `p` of `0` onto the closed convex set `closure W`
  obtain ⟨p, hpW, hp⟩ := exists_norm_eq_iInf_of_complete_convex hne.closure
    isClosed_closure.isComplete hconv (0 : ℂ)
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hconv hpW).1 hp
  have hpα : α ≤ ‖p‖ := by
    have h1 : ‖(0 : ℂ) - p‖ = Metric.infDist 0 W := by
      rw [hp, ← Metric.infDist_closure, Metric.infDist_eq_iInf]
      simp_rw [dist_eq_norm]
    rw [zero_sub, norm_neg] at h1
    rw [h1, Metric.le_infDist hne]
    intro z hz
    rw [dist_eq_norm, zero_sub, norm_neg]
    exact hWα z hz
  have hp0 : 0 < ‖p‖ := hα.trans_le hpα
  refine ⟨((‖p‖⁻¹ : ℝ) : ℂ) * starRingEnd ℂ p, ?_, fun u => ?_⟩
  · rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hp0.ne']
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  -- the variational inequality at the Rayleigh quotient `w` of `u`
  set w := ⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ with hw
  have hwW : w ∈ closure W := subset_closure (div_inner_mem_numericalRange T hu)
  have h1 := hvar w hwW
  rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq, Complex.inner] at h1
  -- `re (conj p * w) ≥ ‖p‖ ^ 2`
  have h2 : ‖p‖ ^ 2 ≤ (w * starRingEnd ℂ p).re := by linarith
  have huu : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hTu : ⟪u, T u⟫_ℂ = w * ⟪u, u⟫_ℂ := by
    rw [hw, div_mul_cancel₀ _ (inner_self_ne_zero.2 hu)]
  rw [smul_apply, inner_smul_right, hTu, huu]
  -- pull the real factors out of the real part
  have h3 : RCLike.re (((‖p‖⁻¹ : ℝ) : ℂ) * starRingEnd ℂ p * (w * ((‖u‖ ^ 2 : ℝ) : ℂ)))
      = ‖p‖⁻¹ * (w * starRingEnd ℂ p).re * ‖u‖ ^ 2 := by
    rw [show ((‖p‖⁻¹ : ℝ) : ℂ) * starRingEnd ℂ p * (w * ((‖u‖ ^ 2 : ℝ) : ℂ))
        = ((‖p‖⁻¹ : ℝ) : ℂ) * ((w * starRingEnd ℂ p) * ((‖u‖ ^ 2 : ℝ) : ℂ)) by ring,
      RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [h3]
  have h4 : ‖p‖ ≤ ‖p‖⁻¹ * (w * starRingEnd ℂ p).re := by
    rw [← div_eq_inv_mul, le_div_iff₀ hp0]
    nlinarith [h2]
  have hu2 : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  calc α * ‖u‖ ^ 2 ≤ ‖p‖ * ‖u‖ ^ 2 := by gcongr
    _ ≤ ‖p‖⁻¹ * (w * starRingEnd ℂ p).re * ‖u‖ ^ 2 := by gcongr

end NumericalRange

/-! ### Isometries -/

section Isometry

/-- **[brezis2011functional] Proposition 11.37, first clause**: the eigenvalues of an isometry lie
on the unit circle, `EV(T) ⊆ S¹`, over any normed field: from an eigenvector `u ≠ 0`,
`‖u‖ = ‖T u‖ = ‖μ‖ ‖u‖`. -/
theorem norm_eq_one_of_hasEigenvalue_of_isometry {𝕜 X : Type*} [NormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] {T : X →L[𝕜] X} (hT : Isometry T) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (T : Module.End 𝕜 X) μ) : ‖μ‖ = 1 := by
  obtain ⟨u, hu⟩ := hμ.exists_hasEigenvector
  have h1 : ‖T u‖ = ‖u‖ := (AddMonoidHomClass.isometry_iff_norm T).1 hT u
  have h2 : T u = μ • u := hu.apply_eq_smul
  rw [h2, norm_smul] at h1
  have hu0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu.2
  exact mul_right_cancel₀ hu0 (h1.trans (one_mul _).symm)

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A surjective isometry of a Hilbert space is unitary: `T† T = 1` is
`ContinuousLinearMap.isometry_iff_adjoint_comp_self`, and `T T† = 1` follows on the range of `T`,
which is everything. With Mathlib's `spectrum.subset_circle_of_unitary` this is
[brezis2011functional] Proposition 11.37, second clause: `σ(T) ⊆ S¹` for unitary `T`. -/
theorem mem_unitary_of_isometry_of_surjective {T : H →L[𝕜] H} (hT : Isometry T)
    (hs : Function.Surjective T) : T ∈ unitary (H →L[𝕜] H) := by
  have h1 : adjoint T ∘L T = 1 := (isometry_iff_adjoint_comp_self T).1 hT
  refine Unitary.mem_iff.2 ⟨by rw [star_eq_adjoint, mul_def, h1], ?_⟩
  rw [star_eq_adjoint, mul_def]
  ext y
  obtain ⟨x, rfl⟩ := hs y
  have h2 : adjoint T (T x) = x := by
    have := congrArg (fun S : H →L[𝕜] H => S x) h1
    simpa using this
  simp [h2]

end Isometry

section IsometryComplex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **[brezis2011functional] Proposition 11.37, third clause**: a non-surjective isometry of a
complex Hilbert space has the whole closed unit disc as its spectrum. `‖T‖ ≤ 1` gives
`σ(T) ⊆ closedBall 0 1`; for `‖λ‖ < 1`, `T - λ = (1 - λ T†) T` with `1 - λ T†` invertible
(`Units.oneSub`), so `T - λ` invertible would make `T` invertible, hence onto; the spectrum is
closed, so it contains the closure of the open disc. -/
theorem spectrum_eq_closedBall_of_isometry_of_not_surjective {T : H →L[ℂ] H} (hT : Isometry T)
    (hs : ¬ Function.Surjective T) : spectrum ℂ T = Metric.closedBall 0 1 := by
  have hnorm : ∀ x, ‖T x‖ = ‖x‖ := (AddMonoidHomClass.isometry_iff_norm T).1 hT
  have hH : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with hH | hH
    · exact absurd (fun y => ⟨y, Subsingleton.elim _ _⟩) hs
    · exact hH
  have hT1 : ‖T‖ ≤ 1 := opNorm_le_bound T zero_le_one fun x => by rw [hnorm, one_mul]
  have hadj : adjoint T ∘L T = 1 := (isometry_iff_adjoint_comp_self T).1 hT
  apply le_antisymm
  · exact (spectrum.subset_closedBall_norm T).trans (Metric.closedBall_subset_closedBall hT1)
  · rw [← closure_ball (0 : ℂ) one_ne_zero]
    refine closure_minimal (fun lam hlam => ?_) (spectrum.isClosed T)
    rw [Metric.mem_ball, dist_zero_right] at hlam
    by_contra hres
    rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hres
    -- `T - λ = (1 - λ T†) T`, with `1 - λ T†` a unit
    have hsmall : ‖lam • adjoint T‖ < 1 := by
      calc ‖lam • adjoint T‖ = ‖lam‖ * ‖adjoint T‖ := norm_smul _ _
        _ ≤ ‖lam‖ * 1 := by gcongr; rw [adjoint.norm_map]; exact hT1
        _ < 1 := by rwa [mul_one]
    have hU : IsUnit (1 - lam • adjoint T) := (Units.oneSub _ hsmall).isUnit
    have hfac : (1 - lam • adjoint T) * T = T - lam • (1 : H →L[ℂ] H) := by
      rw [sub_mul, one_mul, smul_mul_assoc, mul_def, hadj]
    have hTunit : IsUnit T := by
      have h1 : IsUnit (T - lam • (1 : H →L[ℂ] H)) := by
        have := hres.neg
        rwa [neg_sub] at this
      have h2 := hU.unit⁻¹.isUnit.mul h1
      have h3 : (↑hU.unit⁻¹ : H →L[ℂ] H) * (T - lam • (1 : H →L[ℂ] H)) = T := by
        calc (↑hU.unit⁻¹ : H →L[ℂ] H) * (T - lam • (1 : H →L[ℂ] H))
            = ↑hU.unit⁻¹ * (↑hU.unit * T) := by rw [hU.unit_spec, hfac]
          _ = T := Units.inv_mul_cancel_left _ _
      rwa [h3] at h2
    exact hs (isUnit_iff_bijective.1 hTunit).2

end IsometryComplex

end ContinuousLinearMap
