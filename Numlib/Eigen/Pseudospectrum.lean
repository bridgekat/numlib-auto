import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Eigen.Normal
import Numlib.Topology.Algebra.Polynomial

/-!
# Pseudospectra

The `ε`-pseudospectrum of a bounded operator `A`, in its open and its closed form
([saad2011numerical] Def 3.3; [golub2013matrix] §7.9; L. N. Trefethen and M. Embree, *Spectra and
Pseudospectra*, 2005):

* `ContinuousLinearMap.pseudospectrum ε A = {z | ∃ w, ‖w‖ = 1 ∧ ‖A w - z w‖ < ε}`, Saad's and
  Trefethen–Embree's strict form;
* `ContinuousLinearMap.closedPseudospectrum ε A = {z | ∃ w, ‖w‖ = 1 ∧ ‖A w - z w‖ ≤ ε}`, the form of
  [golub2013matrix] (7.9.5), whose theorems are about it ("the distinction has no impact in the
  matrix case": in finite dimension the closed set is the intersection of the open ones of larger
  radius, `ContinuousLinearMap.closedPseudospectrum_eq_iInter_pseudospectrum`).

Both are defined by approximate eigenvectors rather than by the resolvent norm, so that no
convention about the resolvent on the spectrum is needed; the equivalences with the other
definitions are theorems. In finite dimension, for the closed set:

* the least value `⨅_{‖w‖ = 1} ‖A w - z w‖` (the book's `σ_min(z I - A)`) is at most `ε`
  (`ContinuousLinearMap.mem_closedPseudospectrum_iff_iInf`, (7.9.5));
* `z` is an eigenvalue or `‖(z I - A)⁻¹‖ ≥ 1/ε`, for `ε > 0`
  (`ContinuousLinearMap.mem_closedPseudospectrum_iff_resolvent`, (7.9.6));
* `z` is an eigenvalue of some `A + B` with `‖B‖ ≤ ε`, on an inner product space
  (`ContinuousLinearMap.mem_closedPseudospectrum_iff_exists_mem_spectrum_add`, (7.9.7)); the open
  set has the strict form `ContinuousLinearMap.mem_pseudospectrum_iff` ([saad2011numerical]
  Prop 3.7).

Around them: the closed pseudospectrum of radius `0` is the spectrum, the closed pseudospectrum is
compact, it transforms affinely under `α + β A` ([golub2013matrix] Theorem 7.9.1), it is the
conjugate of the one of the adjoint, and every point outside it is at distance at least
`σ_min(z₀ I - A) - ε` from it (Theorem 7.9.8). Isometric intertwiners carry pseudospectra into
pseudospectra (`ContinuousLinearMap.closedPseudospectrum_subset_of_intertwine`), and a similarity
enlarges the radius by at most the condition number
(`ContinuousLinearMap.closedPseudospectrum_units_conj_subset`, Theorem 7.9.2).

The pseudospectral abscissa and radius (`ContinuousLinearMap.pseudospectralAbscissa`,
`ContinuousLinearMap.pseudospectralRadius`, (7.9.8)–(7.9.9)) are defined for complex operators and
are maxima in finite dimension; bounded powers force `(ρ_ε(A) - 1)/ε ≤ sup_k ‖A^k‖`
(`ContinuousLinearMap.pseudospectralRadius_sub_one_div_le_norm_pow`, (7.9.11)), by the Neumann
series of the resolvent.

Every connected component of `Λ_ε(A)` contains an eigenvalue
(`ContinuousLinearMap.exists_mem_spectrum_mem_connectedComponentIn`, [golub2013matrix] §7.9.3).
The proof is by continuity of roots rather than by the maximum modulus principle for the resolvent:
a component missing the spectrum would split `Λ_ε(A)` into two disjoint compact parts, and along
`t ↦ A + t B` (with `‖B‖ ≤ ε` and `z ∈ σ(A + B)`, the normed-space rank-one construction
`ContinuousLinearMap.exists_hasEigenvalue_add_of_norm_sub_smul_le`) the number of eigenvalues in
the part containing `z` would have to jump (`Polynomial.countRootsIn_eq_of_preconnected`).

## Matrices

A square matrix `A` over `RCLike 𝕜` is read through its Euclidean operator
`Matrix.toEuclideanCLM A`, whose norm is the spectral norm. The gallery of [golub2013matrix]
§7.9.4: unitary invariance (`Matrix.closedPseudospectrum_unitary_conj`, Corollary 7.9.3), the
similarity bound with `κ₂(X)` (`Matrix.closedPseudospectrum_conj_subset`, Theorem 7.9.2), diagonal
and normal matrices (discs about the eigenvalues, `Matrix.closedPseudospectrum_diagonal`,
`Matrix.closedPseudospectrum_of_isStarNormal`, Theorem 7.9.4 and Corollary 7.9.5), and block
triangular and block diagonal matrices (`Matrix.closedPseudospectrum_fromBlocks_zero₂₁_supset`,
`Matrix.closedPseudospectrum_fromBlocks_diagonal`, Theorem 7.9.6 and Corollary 7.9.7). The matrix
pseudospectral abscissa and radius are abbreviations for the operator ones.
-/

open Metric Set

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]

section Normed

variable [NormedSpace 𝕜 E] {ε ε₁ ε₂ : ℝ} {A : E →L[𝕜] E} {z : 𝕜}

/-- The **`ε`-pseudospectrum** of `A` ([saad2011numerical], Def 3.3, in the form of his (3.55)): the
scalars `z` for which some unit vector is an eigenvector to within `ε`,
`{z | ∃ w, ‖w‖ = 1 ∧ ‖A w - z w‖ < ε}`. Saad defines it by the resolvent, `‖(A - z)⁻¹‖ > ε⁻¹`, with
the convention that the resolvent norm is infinite on the spectrum; this form needs no such
convention — an exact eigenvector has residual `0` — and is what the perturbation statements
consume. `ContinuousLinearMap.mem_pseudospectrum_iff` identifies it with the backward-error form,
and `ContinuousLinearMap.closedPseudospectrum` is its closed counterpart. -/
def pseudospectrum (ε : ℝ) (A : E →L[𝕜] E) : Set 𝕜 :=
  {z | ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ < ε}

/-- The **closed `ε`-pseudospectrum** of `A` ([golub2013matrix] (7.9.5)): the scalars `z` for which
some unit vector has residual `‖A w - z w‖ ≤ ε`. -/
def closedPseudospectrum (ε : ℝ) (A : E →L[𝕜] E) : Set 𝕜 :=
  {z | ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ ≤ ε}

/-- Membership in the pseudospectrum, unfolded. -/
theorem mem_pseudospectrum :
    z ∈ pseudospectrum ε A ↔ ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ < ε := Iff.rfl

/-- Membership in the closed pseudospectrum, unfolded. -/
theorem mem_closedPseudospectrum :
    z ∈ closedPseudospectrum ε A ↔ ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ ≤ ε := Iff.rfl

/-- The open pseudospectrum is contained in the closed one of the same radius. -/
theorem pseudospectrum_subset_closedPseudospectrum :
    pseudospectrum ε A ⊆ closedPseudospectrum ε A :=
  fun _ ⟨w, hw, h⟩ => ⟨w, hw, h.le⟩

/-- The closed pseudospectrum is contained in every open one of larger radius. -/
theorem closedPseudospectrum_subset_pseudospectrum (h : ε₁ < ε₂) :
    closedPseudospectrum ε₁ A ⊆ pseudospectrum ε₂ A :=
  fun _ ⟨w, hw, h'⟩ => ⟨w, hw, h'.trans_lt h⟩

/-- The pseudospectra increase with the radius. -/
theorem pseudospectrum_mono (h : ε₁ ≤ ε₂) : pseudospectrum ε₁ A ⊆ pseudospectrum ε₂ A :=
  fun _ ⟨w, hw, h'⟩ => ⟨w, hw, h'.trans_le h⟩

/-- The closed pseudospectra increase with the radius ([golub2013matrix] §7.9.3). -/
theorem closedPseudospectrum_mono (h : ε₁ ≤ ε₂) :
    closedPseudospectrum ε₁ A ⊆ closedPseudospectrum ε₂ A :=
  fun _ ⟨w, hw, h'⟩ => ⟨w, hw, h'.trans h⟩

/-- On the zero space there is no unit vector, so the closed pseudospectrum is empty. -/
theorem closedPseudospectrum_eq_empty [Subsingleton E] : closedPseudospectrum ε A = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨w, hw, _⟩ => by
    rw [Subsingleton.elim w 0, norm_zero] at hw
    exact zero_ne_one hw

/-- An eigenvalue has a unit eigenvector. -/
private theorem exists_norm_eq_one_apply_eq_smul
    (hz : Module.End.HasEigenvalue (A : E →ₗ[𝕜] E) z) : ∃ w : E, ‖w‖ = 1 ∧ A w = z • w := by
  obtain ⟨w, hw, hw0⟩ := hz.exists_hasEigenvector
  have hval : A w = z • w := by simpa using Module.End.mem_eigenspace_iff.1 hw
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
  refine ⟨(‖w‖ : 𝕜)⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w),
      inv_mul_cancel₀ hn]
  · rw [map_smul, smul_comm z, hval]

/-- Every eigenvalue lies in every pseudospectrum of positive radius: an exact eigenvector has
residual `0`. This is the inclusion `σ(A) ⊆ Λ_ε(A)`, and the reason the residual form of the
definition needs no convention about the resolvent norm on the spectrum. -/
theorem mem_pseudospectrum_of_hasEigenvalue (hε : 0 < ε)
    (hz : Module.End.HasEigenvalue (A : E →ₗ[𝕜] E) z) : z ∈ pseudospectrum ε A := by
  obtain ⟨w, hw, hAw⟩ := exists_norm_eq_one_apply_eq_smul hz
  exact ⟨w, hw, by rwa [hAw, sub_self, norm_zero]⟩

/-- Every eigenvalue lies in every closed pseudospectrum of nonnegative radius. -/
theorem mem_closedPseudospectrum_of_hasEigenvalue (hε : 0 ≤ ε)
    (hz : Module.End.HasEigenvalue (A : E →ₗ[𝕜] E) z) : z ∈ closedPseudospectrum ε A := by
  obtain ⟨w, hw, hAw⟩ := exists_norm_eq_one_apply_eq_smul hz
  exact ⟨w, hw, by rwa [hAw, sub_self, norm_zero]⟩

private theorem bddBelow_range_norm_sub_smul (A : E →L[𝕜] E) (z : 𝕜) :
    BddBelow (range fun w : {w : E // ‖w‖ = 1} => ‖A w - z • (w : E)‖) :=
  ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩

/-- The least residual `⨅_{‖w‖ = 1} ‖A w - z w‖` (the book's `σ_min(z I - A)`) is a lower bound
by homogeneity: `(⨅_{‖w‖ = 1} ‖A w - z w‖) ‖x‖ ≤ ‖A x - z x‖` for every `x`. -/
theorem iInf_norm_sub_smul_mul_norm_le (A : E →L[𝕜] E) (z : 𝕜) (x : E) :
    (⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖) * ‖x‖ ≤ ‖A x - z • x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have h := ciInf_le (bddBelow_range_norm_sub_smul A z) ⟨_, hu⟩
  simp only [map_smul, smul_comm z, ← smul_sub, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hn)] at h
  calc (⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖) * ‖x‖
      ≤ ‖x‖⁻¹ * ‖A x - z • x‖ * ‖x‖ := by gcongr
    _ = ‖A x - z • x‖ := by field_simp

/-- The least residual `⨅_{‖w‖ = 1} ‖A w - z w‖` is `1`-Lipschitz in `z`. -/
theorem iInf_norm_sub_smul_le_add (A : E →L[𝕜] E) (z z' : 𝕜) :
    ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ ≤
      (⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z' • (w : E)‖) + ‖z - z'‖ := by
  rcases isEmpty_or_nonempty {w : E // ‖w‖ = 1} with h | h
  · rw [Real.iInf_of_isEmpty, Real.iInf_of_isEmpty, zero_add]; exact norm_nonneg _
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun w => ?_
  rw [sub_le_iff_le_add]
  calc ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ ≤ ‖A w - z • (w : E)‖ :=
        ciInf_le (bddBelow_range_norm_sub_smul A z) w
    _ = ‖(A w - z' • (w : E)) - (z - z') • (w : E)‖ := by rw [sub_smul]; congr 1; abel
    _ ≤ ‖A w - z' • (w : E)‖ + ‖(z - z') • (w : E)‖ := norm_sub_le _ _
    _ = ‖A w - z' • (w : E)‖ + ‖z - z'‖ := by rw [norm_smul, w.2, mul_one]

/-- [golub2013matrix] Theorem 7.9.8: every point `z₀` is at distance at least
`σ_min(z₀ I - A) - ε` from a nonempty closed pseudospectrum, where
`σ_min(z₀ I - A) = ⨅_{‖w‖ = 1} ‖A w - z₀ w‖` (for `z₀ ∉ σ(A)` it is at least
`1 / ‖(z₀ I - A)⁻¹‖`, `ContinuousLinearMap.inv_norm_inverse_le_norm_sub_smul`, the book's form).
For `z ∈ Λ_ε(A)` with a unit `w`, `‖A w - z₀ w‖ ≤ ‖A w - z w‖ + |z - z₀| ≤ ε + |z - z₀|`. -/
theorem le_infDist_closedPseudospectrum (hne : (closedPseudospectrum ε A).Nonempty) (z₀ : 𝕜) :
    (⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z₀ • (w : E)‖) - ε ≤
      infDist z₀ (closedPseudospectrum ε A) := by
  rw [le_infDist hne]
  rintro z ⟨w, hw, hz⟩
  have h1 := ciInf_le (bddBelow_range_norm_sub_smul A z₀) ⟨w, hw⟩
  have h2 : ‖A w - z₀ • w‖ ≤ ‖A w - z • w‖ + ‖z - z₀‖ := by
    calc ‖A w - z₀ • w‖ = ‖(A w - z • w) + (z - z₀) • w‖ := by rw [sub_smul]; congr 1; abel
      _ ≤ ‖A w - z • w‖ + ‖(z - z₀) • w‖ := norm_add_le _ _
      _ = ‖A w - z • w‖ + ‖z - z₀‖ := by rw [norm_smul, hw, mul_one]
  rw [dist_comm, dist_eq_norm]
  simp only at h1
  linarith

/-- The affine image of an approximate eigenpair: `(α + β A) w - (α + β z) w = β (A w - z w)`. -/
private theorem smul_add_apply_sub (α β : 𝕜) (w : E) :
    (α • (1 : E →L[𝕜] E) + β • A) w - (α + β * z) • w = β • (A w - z • w) := by
  simp only [add_apply, smul_apply, one_apply_eq_self, add_smul, mul_smul, smul_sub]
  abel

/-- [golub2013matrix] Theorem 7.9.1: for `β ≠ 0`,
`Λ_{ε |β|}(α I + β A) = α + β Λ_ε(A)`. -/
theorem closedPseudospectrum_smul_add (α : 𝕜) {β : 𝕜} (hβ : β ≠ 0) :
    closedPseudospectrum (ε * ‖β‖) (α • 1 + β • A) =
      (fun z => α + β * z) '' closedPseudospectrum ε A := by
  have hβn : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  ext z'
  constructor
  · rintro ⟨w, hw, h⟩
    refine ⟨β⁻¹ * (z' - α), ⟨w, hw, ?_⟩, by field_simp; ring⟩
    have e : z' = α + β * (β⁻¹ * (z' - α)) := by field_simp; ring
    rw [e, smul_add_apply_sub, norm_smul] at h
    exact le_of_mul_le_mul_left (by linarith) hβn
  · rintro ⟨z, ⟨w, hw, h⟩, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [smul_add_apply_sub, norm_smul, mul_comm ε]
    exact mul_le_mul_of_nonneg_left h hβn.le

/-- The open counterpart of `ContinuousLinearMap.closedPseudospectrum_smul_add`: for `β ≠ 0`,
`Λ^{open}_{ε |β|}(α I + β A) = α + β Λ^{open}_ε(A)`. -/
theorem pseudospectrum_smul_add (α : 𝕜) {β : 𝕜} (hβ : β ≠ 0) :
    pseudospectrum (ε * ‖β‖) (α • 1 + β • A) =
      (fun z => α + β * z) '' pseudospectrum ε A := by
  have hβn : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  ext z'
  constructor
  · rintro ⟨w, hw, h⟩
    refine ⟨β⁻¹ * (z' - α), ⟨w, hw, ?_⟩, by field_simp; ring⟩
    have e : z' = α + β * (β⁻¹ * (z' - α)) := by field_simp; ring
    rw [e, smul_add_apply_sub, norm_smul] at h
    exact lt_of_mul_lt_mul_left (by linarith) hβn.le
  · rintro ⟨z, ⟨w, hw, h⟩, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [smul_add_apply_sub, norm_smul, mul_comm ε]
    exact mul_lt_mul_of_pos_left h hβn

/-- Outside the spectrum, `z I - A` is invertible. -/
private theorem isUnit_smul_one_sub (hz : z ∉ spectrum 𝕜 A) : IsUnit (z • 1 - A) := by
  rwa [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, not_not] at hz

/-- **The resolvent bounds the residual from below**: for `z ∉ σ(A)` and every `x`,
`‖x‖ ≤ ‖(z I - A)⁻¹‖ ‖A x - z x‖`. -/
theorem norm_le_norm_inverse_mul_norm_sub_smul (hz : z ∉ spectrum 𝕜 A) (x : E) :
    ‖x‖ ≤ ‖Ring.inverse (z • 1 - A)‖ * ‖A x - z • x‖ := by
  have h1 : Ring.inverse (z • 1 - A) * (z • 1 - A) = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_smul_one_sub hz)
  calc ‖x‖ = ‖Ring.inverse (z • 1 - A) ((z • 1 - A) x)‖ := by
        rw [← mul_apply_eq_comp, h1, one_apply_eq_self]
    _ ≤ ‖Ring.inverse (z • 1 - A)‖ * ‖(z • 1 - A) x‖ := le_opNorm _ _
    _ = ‖Ring.inverse (z • 1 - A)‖ * ‖A x - z • x‖ := by
        rw [sub_apply, smul_apply, one_apply_eq_self, norm_sub_rev]

/-- For `z ∉ σ(A)`, every unit vector has residual at least `1 / ‖(z I - A)⁻¹‖`; so
`1 / ‖(z I - A)⁻¹‖ ≤ σ_min(z I - A)`, the book's form of the distance bound of Theorem 7.9.8. -/
theorem inv_norm_inverse_le_norm_sub_smul (hz : z ∉ spectrum 𝕜 A) {w : E} (hw : ‖w‖ = 1) :
    ‖Ring.inverse (z • 1 - A)‖⁻¹ ≤ ‖A w - z • w‖ := by
  have h := norm_le_norm_inverse_mul_norm_sub_smul hz w
  rw [hw] at h
  have hpos : 0 < ‖Ring.inverse (z • 1 - A)‖ := by
    by_contra h0
    push Not at h0
    nlinarith [norm_nonneg (Ring.inverse (z • 1 - A)), norm_nonneg (A w - z • w)]
  rw [inv_le_iff_one_le_mul₀' hpos]
  exact h

end Normed

section FiniteDimensional

variable [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {ε : ℝ} {A : E →L[𝕜] E} {z : 𝕜}

/-- In finite dimension the least residual is attained on the unit sphere. -/
theorem exists_norm_sub_smul_eq_iInf [Nontrivial E] (A : E →L[𝕜] E) (z : 𝕜) :
    ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ = ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ := by
  have := FiniteDimensional.proper_rclike 𝕜 E
  have hc : Continuous fun w : E => ‖A w - z • w‖ :=
    (A.continuous.sub (continuous_const.smul continuous_id)).norm
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hw₀ : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    ⟨_, mem_sphere_zero_iff_norm.mpr hw₀⟩ hc.continuousOn
  rw [mem_sphere_zero_iff_norm] at hw
  have : Nonempty {w : E // ‖w‖ = 1} := ⟨⟨w, hw⟩⟩
  refine ⟨w, hw, le_antisymm (le_ciInf fun v => hmin (mem_sphere_zero_iff_norm.mpr v.2))
    (ciInf_le (bddBelow_range_norm_sub_smul A z) ⟨w, hw⟩)⟩

/-- [golub2013matrix] (7.9.5): in finite dimension, `z ∈ Λ_ε(A)` exactly when the least residual
`σ_min(z I - A) = ⨅_{‖w‖ = 1} ‖A w - z w‖` is at most `ε`. -/
theorem mem_closedPseudospectrum_iff_iInf [Nontrivial E] :
    z ∈ closedPseudospectrum ε A ↔ ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ ≤ ε := by
  constructor
  · rintro ⟨w, hw, h⟩
    exact (ciInf_le (bddBelow_range_norm_sub_smul A z) ⟨w, hw⟩).trans h
  · intro h
    obtain ⟨w, hw, heq⟩ := exists_norm_sub_smul_eq_iInf A z
    exact ⟨w, hw, heq ▸ h⟩

/-- In finite dimension, an eigenvalue of the operator is an eigenvalue of the linear map. -/
private theorem hasEigenvalue_iff_mem_spectrum' :
    Module.End.HasEigenvalue (A : E →ₗ[𝕜] E) z ↔ z ∈ spectrum 𝕜 A := by
  have := FiniteDimensional.complete 𝕜 E
  rw [spectrum_eq, Module.End.hasEigenvalue_iff_mem_spectrum]

/-- The spectrum lies in every closed pseudospectrum of nonnegative radius. -/
theorem spectrum_subset_closedPseudospectrum (hε : 0 ≤ ε) :
    spectrum 𝕜 A ⊆ closedPseudospectrum ε A := fun _ hz =>
  mem_closedPseudospectrum_of_hasEigenvalue hε (hasEigenvalue_iff_mem_spectrum'.mpr hz)

/-- The spectrum lies in every pseudospectrum of positive radius. -/
theorem spectrum_subset_pseudospectrum (hε : 0 < ε) : spectrum 𝕜 A ⊆ pseudospectrum ε A :=
  fun _ hz => mem_pseudospectrum_of_hasEigenvalue hε (hasEigenvalue_iff_mem_spectrum'.mpr hz)

/-- `Λ₀(A) = σ(A)` ([golub2013matrix] §7.9.1): in finite dimension the closed pseudospectrum of
radius `0` is the spectrum. -/
theorem closedPseudospectrum_zero : closedPseudospectrum 0 A = spectrum 𝕜 A := by
  refine Subset.antisymm ?_ (spectrum_subset_closedPseudospectrum le_rfl)
  rintro z ⟨w, hw, h⟩
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hAw : A w = z • w := sub_eq_zero.mp (norm_le_zero_iff.mp h)
  exact hasEigenvalue_iff_mem_spectrum'.mp (Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hAw, hw0⟩)

/-- In finite dimension the closed pseudospectrum is the intersection of the open ones of larger
radius, `Λ_ε(A) = ⋂_{δ > ε} Λ^{open}_δ(A)`: the book's remark that the strict and the non-strict
definitions agree for matrices ([golub2013matrix] §7.9.1). -/
theorem closedPseudospectrum_eq_iInter_pseudospectrum :
    closedPseudospectrum ε A = ⋂ δ > ε, pseudospectrum δ A := by
  cases subsingleton_or_nontrivial E
  · rw [closedPseudospectrum_eq_empty]
    refine (eq_empty_of_forall_notMem fun z hz => ?_).symm
    obtain ⟨w, hw, -⟩ := mem_iInter₂.mp hz (ε + 1) (by linarith)
    rw [Subsingleton.elim w 0, norm_zero] at hw
    exact zero_ne_one hw
  refine Subset.antisymm (fun z hz => mem_iInter₂.mpr fun δ hδ =>
    closedPseudospectrum_subset_pseudospectrum hδ hz) fun z hz => ?_
  rw [mem_closedPseudospectrum_iff_iInf]
  by_contra h
  push Not at h
  obtain ⟨w, hw, hlt⟩ := mem_iInter₂.mp hz _ h
  exact (ciInf_le (bddBelow_range_norm_sub_smul A z) ⟨w, hw⟩).not_gt hlt

/-- [golub2013matrix] (7.9.6): in finite dimension, for `ε > 0`, `z ∈ Λ_ε(A)` exactly when `z` is
an eigenvalue or the resolvent is large, `‖(z I - A)⁻¹‖ ≥ 1/ε`. (At `ε = 0` the resolvent form
degenerates, `1/0 = 0` in Lean; `ContinuousLinearMap.closedPseudospectrum_zero` is the right
statement there.) -/
theorem mem_closedPseudospectrum_iff_resolvent (hε : 0 < ε) :
    z ∈ closedPseudospectrum ε A ↔
      z ∈ spectrum 𝕜 A ∨ 1 / ε ≤ ‖Ring.inverse (z • 1 - A)‖ := by
  constructor
  · rintro ⟨w, hw, h⟩
    by_cases hz : z ∈ spectrum 𝕜 A
    · exact Or.inl hz
    · right
      have := norm_le_norm_inverse_mul_norm_sub_smul hz w
      rw [hw] at this
      rw [div_le_iff₀ hε]
      exact this.trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))
  · rintro (hz | h)
    · exact spectrum_subset_closedPseudospectrum hε.le hz
    by_cases hz : z ∈ spectrum 𝕜 A
    · exact spectrum_subset_closedPseudospectrum hε.le hz
    cases subsingleton_or_nontrivial E
    · have h0 : Ring.inverse (z • 1 - A) = 0 := Subsingleton.elim _ _
      rw [h0, norm_zero] at h
      exact absurd h (not_le.mpr (by positivity))
    rw [mem_closedPseudospectrum_iff_iInf]
    set m := ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ with hm
    by_contra hlt
    push Not at hlt
    have hm0 : 0 < m := hε.trans hlt
    -- `‖(z I - A)⁻¹ v‖ ≤ ‖v‖ / m`, so `‖(z I - A)⁻¹‖ ≤ 1/m < 1/ε`
    have hR : ‖Ring.inverse (z • 1 - A)‖ ≤ 1 / m := by
      refine opNorm_le_bound _ (by positivity) fun v => ?_
      have h1 : (z • 1 - A) * Ring.inverse (z • 1 - A) = 1 :=
        Ring.mul_inverse_cancel _ (isUnit_smul_one_sub hz)
      have h2 := iInf_norm_sub_smul_mul_norm_le A z (Ring.inverse (z • 1 - A) v)
      have h3 : A (Ring.inverse (z • 1 - A) v) - z • Ring.inverse (z • 1 - A) v = -v := by
        have := congrArg (fun T : E →L[𝕜] E => T v) h1
        simp only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] at this
        rw [← neg_sub, this]
      rw [← hm, h3, norm_neg] at h2
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm0, mul_comm]
      exact h2
    have : 1 / m < 1 / ε := one_div_lt_one_div_of_lt hε hlt
    linarith

/-- In finite dimension the closed pseudospectrum is compact: it is bounded by `‖A‖ + ε`
(`|z| = ‖z w‖ ≤ ‖A w‖ + ε`) and closed (the least residual is continuous in `z`). -/
theorem isCompact_closedPseudospectrum (ε : ℝ) (A : E →L[𝕜] E) :
    IsCompact (closedPseudospectrum ε A) := by
  cases subsingleton_or_nontrivial E
  · rw [closedPseudospectrum_eq_empty]; exact isCompact_empty
  have hbdd : closedPseudospectrum ε A ⊆ closedBall 0 (‖A‖ + ε) := by
    rintro z ⟨w, hw, h⟩
    rw [mem_closedBall_zero_iff]
    calc ‖z‖ = ‖z • w‖ := by rw [norm_smul, hw, mul_one]
      _ = ‖A w - (A w - z • w)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖A w‖ + ‖A w - z • w‖ := norm_sub_le _ _
      _ ≤ ‖A‖ + ε := by
          gcongr
          simpa [hw] using A.le_opNorm w
  have hcont : Continuous fun z : 𝕜 => ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ := by
    refine (LipschitzWith.of_dist_le_mul fun z z' => ?_).continuous (K := 1)
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, abs_sub_le_iff]
    exact ⟨sub_le_iff_le_add'.mpr (iInf_norm_sub_smul_le_add A z z'),
      sub_le_iff_le_add'.mpr ((iInf_norm_sub_smul_le_add A z' z).trans_eq
        (by rw [norm_sub_rev]))⟩
  have hclosed : IsClosed (closedPseudospectrum ε A) := by
    have : closedPseudospectrum ε A =
        {z | ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ ≤ ε} := by
      ext z; exact mem_closedPseudospectrum_iff_iInf
    rw [this]
    exact isClosed_le hcont continuous_const
  exact isCompact_of_isClosed_isBounded hclosed (isBounded_closedBall.subset hbdd)

end FiniteDimensional

section InnerProduct

variable [InnerProductSpace 𝕜 E] {ε : ℝ}

/-- **The backward-error characterization of the pseudospectrum** ([saad2011numerical], Prop 3.7,
(iv) ↔ (v)): `z` is in the `ε`-pseudospectrum exactly when it is an eigenvalue of some `A - B` with
`‖B‖ < ε`.

Forwards, the perturbation is the rank-one `(A w - z w) wᴴ`, built from the residual of the
approximate eigenvector; backwards, an eigenvector of `A - B` has residual `B w` for `A`. The book
states (v) with `‖B‖ ≤ ε`, but its own proof of (v) ⇒ (iv) needs the strict inequality, and with
`≤` the equivalence is false: for `A = 0` every `z` of modulus `ε` satisfies the right-hand side,
with the perturbation `B = -z • 1` of norm exactly `ε`, and none satisfies the left, `‖0 - z • w‖`
being `ε` at every unit `w`. The closed pseudospectrum has the non-strict form,
`ContinuousLinearMap.mem_closedPseudospectrum_iff_exists_mem_spectrum_add`. -/
theorem mem_pseudospectrum_iff (A : E →L[𝕜] E) (z : 𝕜) :
    z ∈ pseudospectrum ε A ↔
      ∃ B : E →L[𝕜] E, ‖B‖ < ε ∧ Module.End.HasEigenvalue ((A - B : E →L[𝕜] E) :
        E →ₗ[𝕜] E) z := by
  constructor
  · rintro ⟨w, hw, hlt⟩
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    refine ⟨InnerProductSpace.rankOne 𝕜 (A w - z • w) w, ?_, ?_⟩
    · rwa [InnerProductSpace.norm_rankOne, hw, mul_one]
    · have huu : (inner 𝕜 w w : 𝕜) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hw]; norm_num
      refine Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 ?_, hw0⟩
      simp only [ContinuousLinearMap.coe_coe, sub_apply, InnerProductSpace.rankOne_apply, huu,
        one_smul, sub_sub_cancel]
  · rintro ⟨B, hB, hz⟩
    obtain ⟨w, hw, hAw⟩ := exists_norm_eq_one_apply_eq_smul hz
    refine ⟨w, hw, ?_⟩
    have hres : A w - z • w = B w := by
      rw [← hAw, sub_apply]; abel
    rw [hres]
    calc ‖B w‖ ≤ ‖B‖ * ‖w‖ := B.le_opNorm w
      _ = ‖B‖ := by rw [hw, mul_one]
      _ < ε := hB

/-- [golub2013matrix] (7.9.7): on a finite-dimensional inner product space, `z ∈ Λ_ε(A)` exactly
when `z` is an eigenvalue of some `A + B` with `‖B‖ ≤ ε`. Forwards, `B = -(A w - z w) wᴴ` for a
unit `w` with small residual; backwards, a unit eigenvector `w` of `A + B` has
`‖A w - z w‖ = ‖B w‖ ≤ ε`. -/
theorem mem_closedPseudospectrum_iff_exists_mem_spectrum_add [FiniteDimensional 𝕜 E]
    (A : E →L[𝕜] E) (z : 𝕜) :
    z ∈ closedPseudospectrum ε A ↔ ∃ B : E →L[𝕜] E, ‖B‖ ≤ ε ∧ z ∈ spectrum 𝕜 (A + B) := by
  constructor
  · rintro ⟨w, hw, hle⟩
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    refine ⟨-InnerProductSpace.rankOne 𝕜 (A w - z • w) w, ?_, ?_⟩
    · rwa [norm_neg, InnerProductSpace.norm_rankOne, hw, mul_one]
    · have huu : (inner 𝕜 w w : 𝕜) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hw]; norm_num
      refine hasEigenvalue_iff_mem_spectrum'.mp (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 ?_, hw0⟩)
      simp only [ContinuousLinearMap.coe_coe, add_apply, neg_apply,
        InnerProductSpace.rankOne_apply, huu, one_smul]
      abel
  · rintro ⟨B, hB, hz⟩
    obtain ⟨w, hw, hAw⟩ := exists_norm_eq_one_apply_eq_smul
      (hasEigenvalue_iff_mem_spectrum'.mpr hz)
    refine ⟨w, hw, ?_⟩
    have hres : A w - z • w = -B w := by
      rw [← hAw, add_apply]; abel
    rw [hres, norm_neg]
    calc ‖B w‖ ≤ ‖B‖ * ‖w‖ := B.le_opNorm w
      _ = ‖B‖ := by rw [hw, mul_one]
      _ ≤ ε := hB

/-- **A lower bound passes to the adjoint** in finite dimension: if `c ‖x‖ ≤ ‖T x‖` for every `x`,
then `c ‖y‖ ≤ ‖T† y‖` for every `y`. For `c > 0`, `T` is injective, hence onto; writing
`y = T x`, `‖y‖² = re ⟪T† y, x⟫ ≤ ‖T† y‖ ‖x‖ ≤ ‖T† y‖ ‖y‖ / c`. -/
theorem le_norm_adjoint_apply_of_le [FiniteDimensional 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    {c : ℝ} (h : ∀ x, c * ‖x‖ ≤ ‖T x‖) (y : E) : c * ‖y‖ ≤ ‖adjoint T y‖ := by
  rcases le_or_gt c 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg _)).trans (norm_nonneg _)
  have hinj : Function.Injective (T : E →ₗ[𝕜] E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := h x
    rw [coe_coe] at hx
    rw [hx, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right this hc) (norm_nonneg _))
  obtain ⟨x, rfl⟩ := LinearMap.injective_iff_surjective.mp hinj y
  rw [coe_coe]
  have hcs : ‖T x‖ ^ 2 ≤ ‖adjoint T (T x)‖ * ‖x‖ := by
    rw [← @inner_self_eq_norm_sq 𝕜, ← adjoint_inner_left]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hx := h x
  rcases (norm_nonneg (T x)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  have : c * ‖T x‖ ^ 2 ≤ ‖adjoint T (T x)‖ * ‖T x‖ := by
    calc c * ‖T x‖ ^ 2 ≤ c * (‖adjoint T (T x)‖ * ‖x‖) := by gcongr
      _ = ‖adjoint T (T x)‖ * (c * ‖x‖) := by ring
      _ ≤ ‖adjoint T (T x)‖ * ‖T x‖ := by gcongr
  nlinarith

/-- On a finite-dimensional inner product space, `z ∈ Λ_ε(A†)` exactly when `z̄ ∈ Λ_ε(A)`: an
operator and its adjoint have the same least value of `‖T w‖` on the unit sphere
(`ContinuousLinearMap.le_norm_adjoint_apply_of_le` both ways). -/
theorem mem_closedPseudospectrum_adjoint_iff [FiniteDimensional 𝕜 E] [CompleteSpace E]
    {A : E →L[𝕜] E} {z : 𝕜} :
    z ∈ closedPseudospectrum ε (adjoint A) ↔ star z ∈ closedPseudospectrum ε A := by
  cases subsingleton_or_nontrivial E
  · simp [closedPseudospectrum_eq_empty]
  -- the least residual of `T` bounds that of `T†`
  have key : ∀ (T : E →L[𝕜] E) (c : 𝕜),
      ⨅ w : {w : E // ‖w‖ = 1}, ‖T w - c • (w : E)‖ ≤
        ⨅ w : {w : E // ‖w‖ = 1}, ‖adjoint T w - star c • (w : E)‖ := by
    intro T c
    obtain ⟨w, hw, heq⟩ := exists_norm_sub_smul_eq_iInf (adjoint T) (star c)
    rw [← heq]
    have h := le_norm_adjoint_apply_of_le (T := T - c • 1)
      (c := ⨅ w : {w : E // ‖w‖ = 1}, ‖T w - c • (w : E)‖)
      (fun x => by
        have := iInf_norm_sub_smul_mul_norm_le T c x
        rwa [sub_apply, smul_apply, one_apply_eq_self]) w
    have h1 : adjoint (1 : E →L[𝕜] E) = 1 := by rw [← star_eq_adjoint, star_one]
    have hadj : adjoint (T - c • 1) w = adjoint T w - star c • w := by
      rw [map_sub, map_smulₛₗ, h1, sub_apply, smul_apply, one_apply_eq_self]
      rfl
    rw [hadj, hw, mul_one] at h
    exact h
  rw [mem_closedPseudospectrum_iff_iInf, mem_closedPseudospectrum_iff_iInf]
  constructor
  · intro h
    exact (key A (star z)).trans (by simpa using h)
  · intro h
    have := key (adjoint A) z
    rw [adjoint_adjoint] at this
    exact this.trans h

end InnerProduct

section Intertwine

variable [NormedSpace 𝕜 E] {ε : ℝ} {A : E →L[𝕜] E} {z : 𝕜}

/-- Outside the closed pseudospectrum every nonzero vector has a large residual:
`z ∉ Λ_ε(A)` gives `ε ‖x‖ < ‖A x - z x‖` for `x ≠ 0`. -/
theorem mul_norm_lt_norm_sub_smul_of_notMem (hz : z ∉ closedPseudospectrum ε A) {x : E}
    (hx : x ≠ 0) : ε * ‖x‖ < ‖A x - z • x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have h : ε < ‖A (((‖x‖⁻¹ : ℝ) : 𝕜) • x) - z • ((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ :=
    not_le.mp fun h => hz ⟨_, hu, h⟩
  rw [map_smul, smul_comm z, ← smul_sub, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hn)] at h
  rwa [← lt_div_iff₀ hn, div_eq_inv_mul]

/-- **Pseudospectra pass along isometric intertwiners**: if `J : F → E` is linear and isometric and
`A J = J P`, then `Λ_ε(P) ⊆ Λ_ε(A)` — a unit `w` with small residual for `P` gives the unit `J w`
with the same residual for `A`. This covers restriction to an invariant subspace and unitary
similarity. -/
theorem closedPseudospectrum_subset_of_intertwine {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {P : F →L[𝕜] F} {J : F →ₗ[𝕜] E} (hJ : ∀ w, ‖J w‖ = ‖w‖)
    (h : ∀ w, A (J w) = J (P w)) : closedPseudospectrum ε P ⊆ closedPseudospectrum ε A := by
  rintro z ⟨w, hw, hle⟩
  refine ⟨J w, by rw [hJ, hw], ?_⟩
  rwa [h, ← map_smul, ← map_sub, hJ]

/-- [golub2013matrix] Theorem 7.9.2, operator form: for an invertible `X`,
`Λ_ε(X⁻¹ A X) ⊆ Λ_{ε ‖X‖ ‖X⁻¹‖}(A)`. From a unit `w` with `‖(X⁻¹ A X - z) w‖ ≤ ε`, the unit vector
`X w / ‖X w‖` has residual `‖X (X⁻¹ A X - z) w‖ / ‖X w‖ ≤ ‖X‖ ε ‖X⁻¹‖`, since
`1 = ‖X⁻¹ X w‖ ≤ ‖X⁻¹‖ ‖X w‖`. -/
theorem closedPseudospectrum_units_conj_subset (u : (E →L[𝕜] E)ˣ) (A : E →L[𝕜] E) (ε : ℝ) :
    closedPseudospectrum ε ((↑u⁻¹ : E →L[𝕜] E) * A * (u : E →L[𝕜] E)) ⊆
      closedPseudospectrum (ε * (‖(u : E →L[𝕜] E)‖ * ‖(↑u⁻¹ : E →L[𝕜] E)‖)) A := by
  rintro z ⟨w, hw, hle⟩
  set X : E →L[𝕜] E := (u : E →L[𝕜] E)
  set Y : E →L[𝕜] E := ↑u⁻¹
  have hXY : ∀ v, X (Y v) = v := fun v => by
    rw [← mul_apply_eq_comp, u.mul_inv, one_apply_eq_self]
  have hYX : ∀ v, Y (X v) = v := fun v => by
    rw [← mul_apply_eq_comp, u.inv_mul, one_apply_eq_self]
  have hε : 0 ≤ ε := (norm_nonneg _).trans hle
  have hXw : 1 ≤ ‖Y‖ * ‖X w‖ := by
    calc (1 : ℝ) = ‖Y (X w)‖ := by rw [hYX, hw]
      _ ≤ ‖Y‖ * ‖X w‖ := le_opNorm _ _
  have hXw0 : 0 < ‖X w‖ := by
    by_contra h0
    push Not at h0
    nlinarith [norm_nonneg Y, norm_nonneg (X w)]
  have hres : A (X w) - z • X w = X ((Y * A * X) w - z • w) := by
    simp only [mul_apply_eq_comp, map_sub, map_smul, hXY]
  refine ⟨((‖X w‖⁻¹ : ℝ) : 𝕜) • X w, ?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hXw0), inv_mul_cancel₀ hXw0.ne']
  rw [map_smul, smul_comm z, ← smul_sub, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hXw0), hres]
  have hinv : ‖X w‖⁻¹ ≤ ‖Y‖ := by
    rw [inv_le_iff_one_le_mul₀ hXw0]; linarith
  calc ‖X w‖⁻¹ * ‖X ((Y * A * X) w - z • w)‖ ≤ ‖Y‖ * (‖X‖ * ε) := by
        gcongr
        exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hle (norm_nonneg _))
    _ = ε * (‖X‖ * ‖Y‖) := by ring

end Intertwine

/-! ### The pseudospectral abscissa and radius -/

section Complex

variable [NormedSpace ℂ E]

/-- The **pseudospectral abscissa** ([golub2013matrix] (7.9.8); Trefethen–Embree §14):
`α_ε(A) = sup {re z | z ∈ Λ_ε(A)}`, the `ε`-analogue of the spectral abscissa. The value is `0`
when the closed pseudospectrum is empty or unbounded above; in finite dimension it is a maximum
(`ContinuousLinearMap.exists_eq_pseudospectralAbscissa_radius`). -/
noncomputable def pseudospectralAbscissa (ε : ℝ) (A : E →L[ℂ] E) : ℝ :=
  sSup ((fun z : ℂ => z.re) '' closedPseudospectrum ε A)

/-- The **pseudospectral radius** ([golub2013matrix] (7.9.9)): `ρ_ε(A) = sup {|z| | z ∈ Λ_ε(A)}`,
the `ε`-analogue of the spectral radius (real-valued: `Λ_ε(A)` is bounded by `‖A‖ + ε`). -/
noncomputable def pseudospectralRadius (ε : ℝ) (A : E →L[ℂ] E) : ℝ :=
  sSup (norm '' closedPseudospectrum ε A)

variable [FiniteDimensional ℂ E] [Nontrivial E] {ε : ℝ}

/-- On a nontrivial finite-dimensional complex space the closed pseudospectrum of nonnegative
radius is nonempty: it contains the eigenvalues. -/
theorem closedPseudospectrum_nonempty (hε : 0 ≤ ε) (A : E →L[ℂ] E) :
    (closedPseudospectrum ε A).Nonempty :=
  let ⟨_, hc⟩ := Module.End.exists_eigenvalue (A : E →ₗ[ℂ] E)
  ⟨_, mem_closedPseudospectrum_of_hasEigenvalue hε hc⟩

/-- The maxima in (7.9.8) and (7.9.9) of [golub2013matrix] are attained: on a nontrivial
finite-dimensional complex space and for `0 ≤ ε`, some `z₁ ∈ Λ_ε(A)` has
`re z₁ = α_ε(A)` and some `z₂ ∈ Λ_ε(A)` has `|z₂| = ρ_ε(A)` (compactness). -/
theorem exists_eq_pseudospectralAbscissa_radius (hε : 0 ≤ ε) (A : E →L[ℂ] E) :
    (∃ z ∈ closedPseudospectrum ε A, z.re = pseudospectralAbscissa ε A) ∧
      ∃ z ∈ closedPseudospectrum ε A, ‖z‖ = pseudospectralRadius ε A := by
  have hK := isCompact_closedPseudospectrum ε A
  have hne := closedPseudospectrum_nonempty hε A
  constructor
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
    refine ⟨z, hz, (IsGreatest.csSup_eq ⟨mem_image_of_mem _ hz, ?_⟩).symm⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hmax hv
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨z, hz, (IsGreatest.csSup_eq ⟨mem_image_of_mem _ hz, ?_⟩).symm⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hmax hv

/-- **Transient growth** ([golub2013matrix] (7.9.11); Trefethen–Embree pp. 160–161): on a
nontrivial finite-dimensional complex space, if `‖A ^ k‖ ≤ M` for every `k` then
`(ρ_ε(A) - 1) / ε ≤ M` for every `ε > 0`, i.e. `sup_k ‖A^k‖ ≥ (ρ_ε(A) - 1)/ε`. Take `z ∈ Λ_ε(A)`
with `|z| = ρ_ε(A) > 1`; the Neumann series `∑ A^k / z^{k+1}` converges (its terms are at most
`M / |z|^{k+1}`) to `(z I - A)⁻¹`, so `1/ε ≤ ‖(z I - A)⁻¹‖ ≤ M / (|z| - 1)`. -/
theorem pseudospectralRadius_sub_one_div_le_norm_pow (hε : 0 < ε) (A : E →L[ℂ] E) {M : ℝ}
    (hM : ∀ k : ℕ, ‖A ^ k‖ ≤ M) : (pseudospectralRadius ε A - 1) / ε ≤ M := by
  have := FiniteDimensional.complete ℂ E
  obtain ⟨-, z, hz, hzr⟩ := exists_eq_pseudospectralAbscissa_radius hε.le A
  have hM1 : 1 ≤ M := by simpa using hM 0
  rw [← hzr]
  rcases le_or_gt ‖z‖ 1 with h1 | h1
  · have : (‖z‖ - 1) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    linarith
  have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at h1; linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set r := ‖z‖⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ h1
  set x : E →L[ℂ] E := z⁻¹ • A with hx
  have hxk : ∀ k : ℕ, ‖x ^ k‖ ≤ M * r ^ k := fun k => by
    rw [hx, smul_pow, norm_smul, norm_pow, norm_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM k) (by positivity)
  have hgeom : HasSum (fun k : ℕ => M * r ^ k) (M * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left M
  have hsum : Summable (x ^ ·) := Summable.of_norm_bounded hgeom.summable hxk
  set S := ∑' k : ℕ, x ^ k with hS
  have hS1 : S * (1 - x) = 1 := hsum.tsum_pow_mul_one_sub
  have hS2 : (1 - x) * S = 1 := hsum.one_sub_mul_tsum_pow
  have hzx : z • (1 : E →L[ℂ] E) - A = z • (1 - x) := by
    rw [hx, smul_sub, smul_smul, mul_inv_cancel₀ hz0, one_smul]
  let u : (E →L[ℂ] E)ˣ :=
    { val := z • 1 - A
      inv := z⁻¹ • S
      val_inv := by rw [hzx, smul_mul_smul_comm, mul_inv_cancel₀ hz0, one_smul, hS2]
      inv_val := by rw [hzx, smul_mul_smul_comm, inv_mul_cancel₀ hz0, one_smul, hS1] }
  have hnot : z ∉ spectrum ℂ A := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, not_not]
    exact u.isUnit
  have hres : 1 / ε ≤ ‖Ring.inverse (z • 1 - A)‖ :=
    ((mem_closedPseudospectrum_iff_resolvent hε).mp hz).resolve_left hnot
  have hinv : Ring.inverse (z • (1 : E →L[ℂ] E) - A) = z⁻¹ • S := Ring.inverse_unit u
  have hSn : ‖S‖ ≤ M * (1 - r)⁻¹ := tsum_of_norm_bounded hgeom hxk
  have hbound : ‖Ring.inverse (z • (1 : E →L[ℂ] E) - A)‖ ≤ M / (‖z‖ - 1) := by
    rw [hinv, norm_smul, norm_inv]
    calc ‖z‖⁻¹ * ‖S‖ ≤ ‖z‖⁻¹ * (M * (1 - r)⁻¹) := by gcongr
      _ = M / (‖z‖ - 1) := by
          rw [hr]
          field_simp
  have h2 : 1 / ε ≤ M / (‖z‖ - 1) := hres.trans hbound
  have hz1 : 0 < ‖z‖ - 1 := by linarith
  rw [div_le_div_iff₀ hε hz1] at h2
  rw [div_le_iff₀ hε]
  linarith

end Complex

end ContinuousLinearMap


namespace ContinuousLinearMap

/-! ### Connected components -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : ℝ}

/-- A unit approximate eigenvector gives a perturbation: if `‖A w - z w‖ ≤ δ` with `‖w‖ = 1`, then
`z` is an eigenvalue of `A + B` for the rank-one `B = -(A w - z w) g(·)`, `g` a norming functional
of `w` (Hahn–Banach), with `‖B‖ ≤ δ`. This is the normed-space form of the forward direction of
[golub2013matrix] (7.9.7). -/
theorem exists_hasEigenvalue_add_of_norm_sub_smul_le {A : E →L[ℂ] E} {z : ℂ} {w : E}
    (hw : ‖w‖ = 1) {δ : ℝ} (h : ‖A w - z • w‖ ≤ δ) :
    ∃ B : E →L[ℂ] E, ‖B‖ ≤ δ ∧ Module.End.HasEigenvalue ((A + B : E →L[ℂ] E) : E →ₗ[ℂ] E) z := by
  obtain ⟨g, hg1, hgw⟩ := exists_dual_vector ℂ w (by rw [hw]; exact one_ne_zero)
  refine ⟨-g.smulRight (A w - z • w), ?_, ?_⟩
  · rw [norm_neg, norm_smulRight_apply, hg1, one_mul]; exact h
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 ?_, hw0⟩
  simp only [coe_coe, add_apply, neg_apply, smulRight_apply, hgw, hw, map_one, one_smul]
  abel

/-- The eigenvalues of `A + t B` lie in `Λ_{|t| ‖B‖}(A)`. -/
theorem mem_closedPseudospectrum_of_hasEigenvalue_add {A B : E →L[ℂ] E} {z : ℂ}
    (hz : Module.End.HasEigenvalue ((A + B : E →L[ℂ] E) : E →ₗ[ℂ] E) z) :
    z ∈ closedPseudospectrum ‖B‖ A := by
  obtain ⟨w, hw, hw0⟩ := hz.exists_hasEigenvector
  have hval : A w + B w = z • w := by simpa using Module.End.mem_eigenspace_iff.1 hw
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
  refine ⟨((‖w‖⁻¹ : ℝ) : ℂ) • w, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2
      (norm_nonneg w)), inv_mul_cancel₀ hn]
  · have : A (((‖w‖⁻¹ : ℝ) : ℂ) • w) - z • ((‖w‖⁻¹ : ℝ) : ℂ) • w =
        ((‖w‖⁻¹ : ℝ) : ℂ) • -B w := by
      rw [map_smul, smul_comm z, ← smul_sub, ← hval]; congr 1; abel
    rw [this, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 (norm_nonneg w))]
    calc ‖w‖⁻¹ * ‖B w‖ ≤ ‖w‖⁻¹ * (‖B‖ * ‖w‖) := by gcongr; exact B.le_opNorm w
      _ = ‖B‖ := by field_simp

variable [FiniteDimensional ℂ E]

/-- In finite dimension, the spectrum of a complex operator is finite. -/
private theorem finite_spectrum (A : E →L[ℂ] E) : (spectrum ℂ A).Finite := by
  have := FiniteDimensional.complete ℂ E
  rw [spectrum_eq]
  exact Module.End.finite_spectrum _

/-- A connected component of a compact set `Λ` that misses a finite set `F ⊆ Λ` is contained in a
relatively clopen part `C` of `Λ` that misses `F`: `Λ = C ∪ D` with `C`, `D` compact and disjoint,
`z ∈ C`, `F ⊆ D`. -/
private theorem exists_compact_split {Λ F : Set ℂ} (hΛ : IsCompact Λ) (hF : F.Finite)
    (hFΛ : F ⊆ Λ) {z : ℂ} (hz : z ∈ Λ) (hK : ∀ μ ∈ F, μ ∉ connectedComponentIn Λ z) :
    ∃ C D : Set ℂ, IsCompact C ∧ IsCompact D ∧ Disjoint C D ∧ C ∪ D = Λ ∧ z ∈ C ∧ F ⊆ D := by
  have : CompactSpace Λ := isCompact_iff_compactSpace.mp hΛ
  -- for each point of `F`, a clopen subset of `Λ` containing `z` and not that point
  have hsep : ∀ μ : F, ∃ U : Set Λ, IsClopen U ∧ (⟨z, hz⟩ : Λ) ∈ U ∧
      (⟨μ.1, hFΛ μ.2⟩ : Λ) ∉ U := by
    intro μ
    have hnot : (⟨μ.1, hFΛ μ.2⟩ : Λ) ∉ connectedComponent (⟨z, hz⟩ : Λ) := by
      intro hmem
      apply hK μ.1 μ.2
      rw [connectedComponentIn_eq_image hz]
      exact ⟨_, hmem, rfl⟩
    rw [connectedComponent_eq_iInter_isClopen, mem_iInter] at hnot
    push Not at hnot
    obtain ⟨⟨U, hU, hzU⟩, hμU⟩ := hnot
    exact ⟨U, hU, hzU, hμU⟩
  choose U hU hzU hμU using hsep
  have : Fintype F := hF.fintype
  set V : Set Λ := ⋂ μ ∈ (Finset.univ : Finset F), U μ with hV
  have hVc : IsClopen V := isClopen_biInter_finset fun μ _ => hU μ
  refine ⟨(↑) '' V, (↑) '' Vᶜ, hVc.isClosed.isCompact.image continuous_subtype_val,
    hVc.compl.isClosed.isCompact.image continuous_subtype_val, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact hb (Subtype.ext hab ▸ ha)
  · rw [← image_union, union_compl_self, image_univ, Subtype.range_coe]
  · exact ⟨⟨z, hz⟩, mem_iInter₂.mpr fun μ _ => hzU μ, rfl⟩
  · intro μ hμ
    refine ⟨⟨μ, hFΛ hμ⟩, fun hmem => ?_, rfl⟩
    exact hμU ⟨μ, hμ⟩ (mem_iInter₂.mp hmem ⟨μ, hμ⟩ (Finset.mem_univ _))

/-- [golub2013matrix] §7.9.3, "each connected component of `Λ_ε(A)` contains at least one eigenvalue
of `A`": on a finite-dimensional complex normed space, for `ε ≥ 0` and `z ∈ Λ_ε(A)` there is an
eigenvalue `μ ∈ σ(A)` in the connected component of `z` in `Λ_ε(A)`.

Proof by continuity of roots, not by the maximum modulus principle. If the component missed the
(finite) spectrum, `Λ_ε(A)` would split into disjoint compact parts `C ∋ z` and `D ⊇ σ(A)`. Take `B`
with `‖B‖ ≤ ε` and `z ∈ σ(A + B)`; along `t ↦ A + t B`, `t ∈ [0, 1]`, all eigenvalues stay in
`Λ_ε(A) = C ∪ D`, so the number of them in `C` is constant
(`Polynomial.countRootsIn_eq_of_preconnected`): `0` at `t = 0`, at least `1` at `t = 1`. -/
theorem exists_mem_spectrum_mem_connectedComponentIn [Nontrivial E] (A : E →L[ℂ] E) {z : ℂ}
    (hz : z ∈ closedPseudospectrum ε A) :
    ∃ μ ∈ spectrum ℂ A, μ ∈ connectedComponentIn (closedPseudospectrum ε A) z := by
  have := FiniteDimensional.complete ℂ E
  classical
  have hε : 0 ≤ ε := let ⟨_, _, h⟩ := hz; (norm_nonneg _).trans h
  by_contra hK
  push Not at hK
  obtain ⟨C, D, hC, hD, hCD, hΛ, hzC, hσD⟩ := exists_compact_split
    (isCompact_closedPseudospectrum ε A) (finite_spectrum A)
    (spectrum_subset_closedPseudospectrum hε) hz hK
  obtain ⟨w, hw, hle⟩ := hz
  obtain ⟨B, hB, hzB⟩ := exists_hasEigenvalue_add_of_norm_sub_smul_le hw hle
  -- the path of matrices
  set b := Module.finBasis ℂ E
  set N := Module.finrank ℂ E
  set M : ℝ → Matrix (Fin N) (Fin N) ℂ := fun t =>
    LinearMap.toMatrix b b (A : E →ₗ[ℂ] E) + (t : ℂ) • LinearMap.toMatrix b b (B : E →ₗ[ℂ] E)
    with hM
  have hMeq : ∀ t : ℝ, M t = LinearMap.toMatrix b b ((A + (t : ℂ) • B : E →L[ℂ] E) : E →ₗ[ℂ] E) :=
    fun t => by
      simp only [hM, toLinearMap_add, toLinearMap_smul, map_add, LinearEquiv.map_smul]
  have hMcont : Continuous M :=
    continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  -- roots of the characteristic polynomial are eigenvalues of `A + t B`
  have hroot : ∀ t : ℝ, ∀ μ, μ ∈ (M t).charpoly.roots ↔
      Module.End.HasEigenvalue ((A + (t : ℂ) • B : E →L[ℂ] E) : E →ₗ[ℂ] E) μ := by
    intro t μ
    rw [Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero, hMeq, LinearMap.charpoly_toMatrix,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  have hsub : ∀ t : Icc (0 : ℝ) 1, ∀ μ ∈ (M t.1).charpoly.roots, μ ∈ C ∪ D := by
    rintro ⟨t, ht0, ht1⟩ μ hμ
    rw [hΛ]
    refine closedPseudospectrum_mono ?_ (mem_closedPseudospectrum_of_hasEigenvalue_add
      ((hroot t μ).mp hμ))
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖B‖ ≤ 1 * ε := mul_le_mul ht1 hB (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  have hcard : ∀ t : ℝ, Multiset.card (M t).charpoly.roots = N := fun t =>
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (M t).charpoly)).trans
      ((Matrix.charpoly_natDegree_eq_dim _).trans (Fintype.card_fin N))
  have : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have key := Polynomial.countRootsIn_eq_of_preconnected (T := Icc (0 : ℝ) 1)
    (p := fun t => (M t.1).charpoly) (n := N) hC hD hCD
    (fun _ => Matrix.charpoly_monic _)
    (fun _ => (Matrix.charpoly_natDegree_eq_dim _).trans (Fintype.card_fin N))
    (fun t => hcard t.1) hsub
    (fun j => (Matrix.continuous_coeff_charpoly hMcont j).comp continuous_subtype_val)
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  simp only at key
  -- at `t = 0` no root lies in `C`; at `t = 1`, `z` does
  have h0 : (M 0).charpoly.countRootsIn C = 0 := by
    rw [Polynomial.countRootsIn, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro μ hμ hμC
    have hμA : μ ∈ spectrum ℂ A := by
      have h := (hroot 0 μ).mp hμ
      rw [Complex.ofReal_zero, zero_smul, add_zero, Module.End.hasEigenvalue_iff_mem_spectrum,
        ← spectrum_eq] at h
      exact h
    exact Set.disjoint_left.mp hCD hμC (hσD hμA)
  have h1 : 0 < (M 1).charpoly.countRootsIn C := by
    rw [Polynomial.countRootsIn, Multiset.card_pos_iff_exists_mem]
    refine ⟨z, Multiset.mem_filter.mpr ⟨(hroot 1 z).mpr ?_, hzC⟩⟩
    rwa [Complex.ofReal_one, one_smul]
  omega

end ContinuousLinearMap

/-! ### Matrices -/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

open ContinuousLinearMap

/-- The closed pseudospectrum of `Aᴴ` is the conjugate of that of `A`. -/
theorem mem_closedPseudospectrum_conjTranspose_iff {A : Matrix n n 𝕜} {ε : ℝ} {z : 𝕜} :
    z ∈ (toEuclideanCLM (n := n) (𝕜 := 𝕜) Aᴴ).closedPseudospectrum ε ↔
      star z ∈ (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).closedPseudospectrum ε := by
  rw [← star_eq_conjTranspose, map_star, star_eq_adjoint]
  exact mem_closedPseudospectrum_adjoint_iff

/-- A unitary matrix acts isometrically on `EuclideanSpace`. -/
theorem norm_toEuclideanCLM_of_mem_unitaryGroup {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜)
    (w : EuclideanSpace 𝕜 n) : ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) U w‖ = ‖w‖ := by
  refine norm_map_of_mem_unitary ?_ w
  rw [Unitary.mem_iff, ← map_star, ← map_mul, ← map_mul, Unitary.star_mul_self_of_mem hU,
    Unitary.mul_star_self_of_mem hU, map_one]
  exact ⟨rfl, rfl⟩

section L2

open scoped Matrix.Norms.L2Operator

/-- [golub2013matrix] Theorem 7.9.2: for an invertible `X`,
`Λ_ε(X⁻¹ A X) ⊆ Λ_{ε κ₂(X)}(A)` with `κ₂(X) = ‖X‖₂ ‖X⁻¹‖₂`
(`ContinuousLinearMap.closedPseudospectrum_units_conj_subset` for the Euclidean operators). -/
theorem closedPseudospectrum_conj_subset {X : Matrix n n 𝕜} (hX : IsUnit X) (A : Matrix n n 𝕜)
    (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (X⁻¹ * A * X)).closedPseudospectrum ε ⊆
      (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).closedPseudospectrum (ε * NormedRing.condNumber X) := by
  obtain ⟨u, hu⟩ := hX.map (toEuclideanCLM (n := n) (𝕜 := 𝕜))
  have hinv : (↑u⁻¹ : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) X⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hu, ← map_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det X).mp hX), map_one]
  have hcond : NormedRing.condNumber X =
      ‖(u : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)‖ *
        ‖(↑u⁻¹ : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)‖ := by
    rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse, hinv, hu]
    rfl
  rw [map_mul, map_mul, ← hu, ← hinv, hcond]
  exact closedPseudospectrum_units_conj_subset u _ ε

end L2

private theorem toEuclideanCLM_mul_apply (X Y : Matrix n n 𝕜)
    (w : EuclideanSpace 𝕜 n) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (X * Y) w =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) X (toEuclideanCLM (n := n) (𝕜 := 𝕜) Y w) := by
  rw [map_mul]
  rfl

private theorem closedPseudospectrum_unitary_conj_subset {V : Matrix n n 𝕜}
    (hV : V ∈ unitaryGroup n 𝕜) (B : Matrix n n 𝕜) (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (star V * B * V)).closedPseudospectrum ε ⊆
      (toEuclideanCLM (n := n) (𝕜 := 𝕜) B).closedPseudospectrum ε := by
  rintro z ⟨w, hw, h⟩
  refine ⟨toEuclideanCLM (n := n) (𝕜 := 𝕜) V w, by
    rw [norm_toEuclideanCLM_of_mem_unitaryGroup hV, hw], ?_⟩
  have hres : toEuclideanCLM (n := n) (𝕜 := 𝕜) B (toEuclideanCLM (n := n) (𝕜 := 𝕜) V w) -
      z • toEuclideanCLM (n := n) (𝕜 := 𝕜) V w =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) V
        (toEuclideanCLM (n := n) (𝕜 := 𝕜) (star V * B * V) w - z • w) := by
    rw [map_sub, map_smul, ← toEuclideanCLM_mul_apply, ← toEuclideanCLM_mul_apply,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Unitary.mul_star_self_of_mem hV, Matrix.one_mul]
  rw [hres, norm_toEuclideanCLM_of_mem_unitaryGroup hV]
  exact h

/-- [golub2013matrix] Corollary 7.9.3: unitary similarity preserves the closed pseudospectrum,
`Λ_ε(Uᴴ A U) = Λ_ε(A)`: a unitary matrix maps unit vectors with small residual for `Uᴴ A U` to
unit vectors with the same residual for `A`, and conversely. -/
theorem closedPseudospectrum_unitary_conj {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜)
    (A : Matrix n n 𝕜) (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (star U * A * U)).closedPseudospectrum ε =
      (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).closedPseudospectrum ε := by
  refine Subset.antisymm (closedPseudospectrum_unitary_conj_subset hU A ε) ?_
  have hA : star (star U) * (star U * A * U) * star U = A := by
    have h1 : U * star U = 1 := Unitary.mul_star_self_of_mem hU
    rw [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      h1, Matrix.mul_one]
  conv_lhs => rw [← hA]
  exact closedPseudospectrum_unitary_conj_subset (Unitary.star_mem hU) _ ε

/-- The residual of a diagonal matrix, entrywise. -/
private theorem toEuclideanCLM_diagonal_sub_smul_apply (d : n → 𝕜) (z : 𝕜)
    (w : EuclideanSpace 𝕜 n) (i : n) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal d) w - z • w) i = (d i - z) * w i := by
  simp [mulVec_diagonal, sub_mul]

/-- [golub2013matrix] Theorem 7.9.4: the closed pseudospectrum of a diagonal matrix is the union of
the closed discs of radius `ε` about its diagonal entries. For a unit `w`,
`‖(D - z) w‖² = ∑ |d_i - z|² |w_i|² ≥ min_i |d_i - z|²`, with equality at a coordinate vector. -/
theorem closedPseudospectrum_diagonal (d : n → 𝕜) (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal d)).closedPseudospectrum ε =
      ⋃ i, closedBall (d i) ε := by
  ext z
  simp only [mem_iUnion, mem_closedBall]
  constructor
  · rintro ⟨w, hw, h⟩
    by_contra hz
    push Not at hz
    rcases isEmpty_or_nonempty n with hn | hn
    · have : w = 0 := PiLp.ext fun i => (IsEmpty.false i).elim
      rw [this, norm_zero] at hw
      exact zero_ne_one hw
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ‖d i - z‖)
      Finset.univ_nonempty
    have hδ : ε < ‖d i₀ - z‖ := by rw [← dist_eq_norm, dist_comm]; exact hz i₀
    have hε : 0 ≤ ε := (norm_nonneg _).trans h
    have hsq : ‖d i₀ - z‖ ^ 2 ≤
        ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal d) w - z • w‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ‖d i₀ - z‖ ^ 2 = ‖d i₀ - z‖ ^ 2 * ‖w‖ ^ 2 := by rw [hw, one_pow, mul_one]
        _ = ∑ i, ‖d i₀ - z‖ ^ 2 * ‖w i‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
        _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [toEuclideanCLM_diagonal_sub_smul_apply, norm_mul, mul_pow]
          gcongr
          exact hi₀ i (Finset.mem_univ i)
    have := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith
  · rintro ⟨i, hi⟩
    refine ⟨EuclideanSpace.single i 1, by simp, ?_⟩
    have : toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal d) (EuclideanSpace.single i 1) -
        z • EuclideanSpace.single i 1 = EuclideanSpace.single i (d i - z) := by
      ext j
      rw [toEuclideanCLM_diagonal_sub_smul_apply]
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [this, PiLp.norm_single, ← dist_eq_norm, dist_comm]
    exact hi

/-- [golub2013matrix] Corollary 7.9.5: a normal matrix over an algebraically closed `RCLike` field
has `Λ_ε(A) = ⋃_{λ ∈ σ(A)} {z | |z - λ| ≤ ε}` (unitary diagonalization,
`Matrix.closedPseudospectrum_unitary_conj`, `Matrix.closedPseudospectrum_diagonal`). -/
theorem closedPseudospectrum_of_isStarNormal [IsAlgClosed 𝕜] {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).closedPseudospectrum ε =
      ⋃ μ ∈ spectrum 𝕜 A, closedBall μ ε := by
  obtain ⟨U, hU, d, hd⟩ := IsStarNormal.spectral_theorem.mp hA
  rw [← star_eq_conjTranspose] at hd
  have hspec : spectrum 𝕜 A = range d := by
    let u : (Matrix n n 𝕜)ˣ :=
      ⟨star U, U, Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩
    have := spectrum.units_conjugate (R := 𝕜) (a := A) (u := u)
    rw [← spectrum_diagonal (R := 𝕜) d, ← hd, ← this]
    rfl
  rw [hspec, biUnion_range, ← closedPseudospectrum_diagonal, ← hd,
    closedPseudospectrum_unitary_conj hU]

/-- `x ↦ (x, 0)`, isometric. -/
private def inlL : EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 (m ⊕ n) where
  toFun x := WithLp.toLp 2 (Sum.elim (WithLp.ofLp x) 0)
  map_add' x y := by ext (i | i) <;> simp
  map_smul' c x := by ext (i | i) <;> simp

/-- `y ↦ (0, y)`, isometric. -/
private def inrL : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 (m ⊕ n) where
  toFun y := WithLp.toLp 2 (Sum.elim 0 (WithLp.ofLp y))
  map_add' x y := by ext (i | i) <;> simp
  map_smul' c x := by ext (i | i) <;> simp

omit [DecidableEq m] [DecidableEq n] in
/-- The Euclidean norm on `m ⊕ n` splits into the two halves. -/
private theorem norm_sq_eq_add (v : EuclideanSpace 𝕜 (m ⊕ n)) :
    ‖v‖ ^ 2 = ‖(WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inl) : EuclideanSpace 𝕜 m)‖ ^ 2 +
      ‖(WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inr) : EuclideanSpace 𝕜 n)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  rfl

omit [DecidableEq m] [DecidableEq n] in
private theorem norm_inlL (x : EuclideanSpace 𝕜 m) : ‖(inlL (n := n) x)‖ = ‖x‖ := by
  have h := norm_sq_eq_add (inlL (n := n) x)
  have h0 : (WithLp.toLp 2 (WithLp.ofLp (inlL (n := n) x) ∘ Sum.inr) : EuclideanSpace 𝕜 n) =
      0 := by
    ext j; simp [inlL]
  have h1 : (WithLp.toLp 2 (WithLp.ofLp (inlL (n := n) x) ∘ Sum.inl) : EuclideanSpace 𝕜 m) =
      x := by
    ext j; simp [inlL]
  rw [h0, h1, norm_zero] at h
  simpa [sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] using h

omit [DecidableEq m] [DecidableEq n] in
private theorem norm_inrL (y : EuclideanSpace 𝕜 n) : ‖(inrL (m := m) y)‖ = ‖y‖ := by
  have h := norm_sq_eq_add (inrL (m := m) y)
  have h0 : (WithLp.toLp 2 (WithLp.ofLp (inrL (m := m) y) ∘ Sum.inl) : EuclideanSpace 𝕜 m) =
      0 := by
    ext j; simp [inrL]
  have h1 : (WithLp.toLp 2 (WithLp.ofLp (inrL (m := m) y) ∘ Sum.inr) : EuclideanSpace 𝕜 n) =
      y := by
    ext j; simp [inrL]
  rw [h0, h1, norm_zero] at h
  simpa [sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] using h

/-- [golub2013matrix] Theorem 7.9.6: for a block upper triangular `T = [T₁₁ T₁₂; 0 T₂₂]`,
`Λ_ε(T₁₁) ∪ Λ_ε(T₂₂) ⊆ Λ_ε(T)`. `T₁₁` acts on the invariant subspace of vectors `(x, 0)`; for
`T₂₂` pass to the conjugate transposes (`Matrix.mem_closedPseudospectrum_conjTranspose_iff`), where
`T₂₂ᴴ` acts on the invariant subspace of vectors `(0, y)` of `Tᴴ`. -/
theorem closedPseudospectrum_fromBlocks_zero₂₁_supset (T₁₁ : Matrix m m 𝕜)
    (T₁₂ : Matrix m n 𝕜) (T₂₂ : Matrix n n 𝕜) (ε : ℝ) :
    (toEuclideanCLM (n := m) (𝕜 := 𝕜) T₁₁).closedPseudospectrum ε ∪
        (toEuclideanCLM (n := n) (𝕜 := 𝕜) T₂₂).closedPseudospectrum ε ⊆
      (toEuclideanCLM (n := m ⊕ n) (𝕜 := 𝕜)
        (fromBlocks T₁₁ T₁₂ 0 T₂₂)).closedPseudospectrum ε := by
  refine union_subset ?_ fun z hz => ?_
  · refine closedPseudospectrum_subset_of_intertwine (J := inlL) norm_inlL fun w => ?_
    ext (i | i) <;> simp [inlL, fromBlocks_mulVec]
  · rw [← star_star z, ← mem_closedPseudospectrum_conjTranspose_iff] at hz ⊢
    rw [fromBlocks_conjTranspose, conjTranspose_zero]
    refine closedPseudospectrum_subset_of_intertwine (J := inrL) norm_inrL (fun w => ?_) hz
    ext (i | i) <;> simp [inrL, fromBlocks_mulVec]

/-- Outside `Λ_ε(P)`, the squared residual of any `x` is at least `ε² ‖x‖²`, strictly when
`x ≠ 0`. -/
private theorem sq_mul_norm_sq_le {p : Type*} [Fintype p] [DecidableEq p] {P : Matrix p p 𝕜}
    {ε : ℝ} {z : 𝕜} (hz : z ∉ (toEuclideanCLM (n := p) (𝕜 := 𝕜) P).closedPseudospectrum ε)
    (hε : 0 ≤ ε) (x : EuclideanSpace 𝕜 p) :
    ε ^ 2 * ‖x‖ ^ 2 ≤ ‖toEuclideanCLM (n := p) (𝕜 := 𝕜) P x - z • x‖ ^ 2 ∧
      (x ≠ 0 → ε ^ 2 * ‖x‖ ^ 2 < ‖toEuclideanCLM (n := p) (𝕜 := 𝕜) P x - z • x‖ ^ 2) := by
  have hlt : x ≠ 0 → ε ^ 2 * ‖x‖ ^ 2 < ‖toEuclideanCLM (n := p) (𝕜 := 𝕜) P x - z • x‖ ^ 2 :=
    fun hx => by
      have := mul_norm_lt_norm_sub_smul_of_notMem hz hx
      rw [← mul_pow]
      exact pow_lt_pow_left₀ this (by positivity) two_ne_zero
  refine ⟨?_, hlt⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (hlt hx).le

/-- [golub2013matrix] Corollary 7.9.7: `Λ_ε(diag(T₁₁, T₂₂)) = Λ_ε(T₁₁) ∪ Λ_ε(T₂₂)`. For `⊆`: a
unit `(u, w)` has `‖(T - z)(u, w)‖² = ‖(T₁₁ - z) u‖² + ‖(T₂₂ - z) w‖²`; if `z` lay in neither, the
two terms would exceed `ε² ‖u‖²` and `ε² ‖w‖²` (strictly for a nonzero half), so the sum would
exceed `ε²`. -/
theorem closedPseudospectrum_fromBlocks_diagonal (T₁₁ : Matrix m m 𝕜) (T₂₂ : Matrix n n 𝕜)
    (ε : ℝ) :
    (toEuclideanCLM (n := m ⊕ n) (𝕜 := 𝕜) (fromBlocks T₁₁ 0 0 T₂₂)).closedPseudospectrum ε =
      (toEuclideanCLM (n := m) (𝕜 := 𝕜) T₁₁).closedPseudospectrum ε ∪
        (toEuclideanCLM (n := n) (𝕜 := 𝕜) T₂₂).closedPseudospectrum ε := by
  refine Subset.antisymm ?_ (closedPseudospectrum_fromBlocks_zero₂₁_supset T₁₁ 0 T₂₂ ε)
  rintro z ⟨v, hv, h⟩
  by_contra hz
  rw [mem_union, not_or] at hz
  have hε : 0 ≤ ε := (norm_nonneg _).trans h
  set u : EuclideanSpace 𝕜 m := WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inl) with hu
  set w : EuclideanSpace 𝕜 n := WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inr) with hw
  set r := toEuclideanCLM (n := m ⊕ n) (𝕜 := 𝕜) (fromBlocks T₁₁ 0 0 T₂₂) v - z • v with hr
  have hr2 : ‖r‖ ^ 2 = ‖toEuclideanCLM (n := m) (𝕜 := 𝕜) T₁₁ u - z • u‖ ^ 2 +
      ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) T₂₂ w - z • w‖ ^ 2 := by
    rw [norm_sq_eq_add]
    congr 3 <;> ext i <;> simp [r, u, w, fromBlocks_mulVec]
  have hv2 : ‖u‖ ^ 2 + ‖w‖ ^ 2 = 1 := by rw [← norm_sq_eq_add, hv, one_pow]
  obtain ⟨hu1, hu2⟩ := sq_mul_norm_sq_le hz.1 hε u
  obtain ⟨hw1, hw2⟩ := sq_mul_norm_sq_le hz.2 hε w
  have hle : ‖r‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rcases eq_or_ne u 0 with hu0 | hu0
  · have hw0 : w ≠ 0 := by
      rintro hw0
      rw [hu0, hw0, norm_zero] at hv2
      norm_num at hv2
    have := hw2 hw0
    nlinarith
  · have := hu2 hu0
    nlinarith

section L2

open scoped Matrix.Norms.L2Operator

/-- The pseudospectral abscissa of a matrix ([golub2013matrix] (7.9.8)): that of its Euclidean
operator. -/
noncomputable abbrev pseudospectralAbscissa (ε : ℝ) (A : Matrix n n ℂ) : ℝ :=
  (toEuclideanCLM (n := n) (𝕜 := ℂ) A).pseudospectralAbscissa ε

/-- The pseudospectral radius of a matrix ([golub2013matrix] (7.9.9)): that of its Euclidean
operator. -/
noncomputable abbrev pseudospectralRadius (ε : ℝ) (A : Matrix n n ℂ) : ℝ :=
  (toEuclideanCLM (n := n) (𝕜 := ℂ) A).pseudospectralRadius ε

/-- The maxima in (7.9.8) and (7.9.9) of [golub2013matrix] are attained for a matrix. -/
theorem exists_eq_pseudospectralAbscissa_radius [Nonempty n] {ε : ℝ} (hε : 0 ≤ ε)
    (A : Matrix n n ℂ) :
    (∃ z ∈ (toEuclideanCLM (n := n) (𝕜 := ℂ) A).closedPseudospectrum ε,
        z.re = pseudospectralAbscissa ε A) ∧
      ∃ z ∈ (toEuclideanCLM (n := n) (𝕜 := ℂ) A).closedPseudospectrum ε,
        ‖z‖ = pseudospectralRadius ε A :=
  ContinuousLinearMap.exists_eq_pseudospectralAbscissa_radius hε _

/-- [golub2013matrix] (7.9.11) for a matrix: if `‖A ^ k‖₂ ≤ M` for every `k`, then
`(ρ_ε(A) - 1) / ε ≤ M` for every `ε > 0`. -/
theorem pseudospectralRadius_sub_one_div_le_norm_pow [Nonempty n] {ε : ℝ} (hε : 0 < ε)
    (A : Matrix n n ℂ) {M : ℝ} (hM : ∀ k : ℕ, ‖A ^ k‖ ≤ M) :
    (pseudospectralRadius ε A - 1) / ε ≤ M :=
  ContinuousLinearMap.pseudospectralRadius_sub_one_div_le_norm_pow hε _ fun k => by
    rw [← map_pow, ← cstar_norm_def]
    exact hM k

end L2

end Matrix
