import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Wielandt deflation of a computed eigenpair

Once an eigenpair `(l, u)` of `A` has been computed, a *deflation* modifies `A` by a rank-one
operator so that `l` is displaced to `l - σ` while every other eigenvalue is left where it was;
running the same eigenvalue algorithm on the modified operator then produces the next eigenpair.
Wielandt's choice is

`wielandtDeflate A u v σ = A - σ • (x ↦ ⟪v, x⟫ u)`,

for any `v` normalized by `⟪v, u⟫ = 1` ([saad2011numerical], §4.2.1).

## Main definitions

* `LinearMap.wielandtDeflate A u v σ` is the deflation itself, the rank-one modification `A - σ u
  vᴴ`.

## Main results

### The spectrum of the deflated operator

`LinearMap.charpoly_wielandtDeflate` is the theorem of Wielandt ([saad2011numerical], Thm 4.2) in
the form that records multiplicities:

`(wielandtDeflate A u v σ).charpoly * (X - C l) = A.charpoly * (X - C (l - σ))`.

Dividing out the common factor, the multiset of eigenvalues of the deflated operator is that of `A`
with one copy of `l` replaced by `l - σ`. `LinearMap.hasEigenvalue_wielandtDeflate_iff` is the
set-level reading, and `LinearMap.hasEigenvalue_wielandtDeflate` says that `l - σ` is always an
eigenvalue of the deflated operator, `u` still being an eigenvector for it.

The proof is not the book's. Deflation changes `A` by an operator whose range is the line `𝕜 ∙ u`,
so the two operators induce the *same* map on the quotient `E ⧸ (𝕜 ∙ u)`, while the line itself is
invariant for both, with `A` acting on it as `l` and the deflated operator as `l - σ`. Hence both
determinants `det (t - A)` and `det (t - A₁)` factor through the same quotient determinant
(`LinearMap.det_eq_det_mul_det`), with cofactors `t - l` and `t - l + σ`; the polynomial identity
follows because a field of characteristic zero is infinite (`Polynomial.funext`). No basis adapted
to `u` and no block matrix is ever constructed.

The book's own argument is `LinearMap.wielandtDeflate_adjoint_apply_of_ne` ([saad2011numerical],
Prop 4.1): a left eigenvector of `A` for an eigenvalue `μ ≠ l` is orthogonal to `u` and therefore
survives the deflation untouched. That statement is proved here as well, since it is what says the
deflation leaves the *left* eigenvectors alone; it is not strong enough on its own to give the
multiplicities.

### The Schur–Wielandt choice

Taking `v = u` for a unit eigenvector `u` — [saad2011numerical] Prop 4.1, and the reason Algorithm
4.4 is called Schur–Wielandt deflation — preserves the Schur vectors of `A`. A Schur factorization
is a complete flag of invariant subspaces, each containing `u`, and what preserving it amounts to is
`LinearMap.schurWielandtDeflate_invtSubmodule`: an `A`-invariant subspace containing `u` is
invariant for the deflated operator. Mathlib has no Schur form, and none is needed to state or to
use this; the flag is exactly the data the statement quantifies over.

Nothing in that theorem uses `v = u` or the normalization: only `u ∈ S`. The block deflation `A - Q
Σ Qᴴ` of [saad2011numerical] Prop 4.2 is `LinearMap.wielandtDeflate` iterated over the columns of
`Q` (`LinearMap.wielandtDeflate_wielandtDeflate` composes two steps into one rank-two modification),
and the same theorem applies at each step.

### Householder deflation

The matrix form used by [quarteroni2000numerical] (Remark 5.3, §5.12.2) is different: instead of
displacing the eigenvalue it *removes* it. The reflector `H` that sends the computed eigenvector `x`
to a multiple of `e₀` conjugates `A` into a matrix whose first column is `l e₀`
(`Matrix.householder_conj_eigenvector_col`), and Laplace expansion along that column shows that
the trailing `N × N` block carries the remaining eigenvalues with their multiplicities,
`A.charpoly = (X - C l) * A₂.charpoly` (`Matrix.charpoly_householder_conj_eigenvector`). The next
eigenpair is then computed on a matrix one size smaller.
-/

open Polynomial

open scoped ComplexConjugate

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Wielandt's deflation** of `A` at the vector `u` with the shift `σ`, the rank-one modification
`A - σ u vᴴ` of [saad2011numerical], (4.6).

The vector `v` is arbitrary; it is normalized by `⟪v, u⟫ = 1` in every statement about the spectrum,
and the choice `v = u` for a unit eigenvector `u` is the Schur–Wielandt one. -/
noncomputable def wielandtDeflate (A : E →ₗ[𝕜] E) (u v : E) (σ : 𝕜) : E →ₗ[𝕜] E :=
  A - σ • (toSpanSingleton 𝕜 E u ∘ₗ innerₛₗ 𝕜 v)

/-- The deflated operator, applied to a vector. -/
@[simp]
theorem wielandtDeflate_apply (A : E →ₗ[𝕜] E) (u v : E) (σ : 𝕜) (x : E) :
    wielandtDeflate A u v σ x = A x - (σ * inner 𝕜 v x) • u := by
  simp [wielandtDeflate, mul_smul]

/-- The deflated operator differs from `A` only along the line through `u`. -/
theorem sub_wielandtDeflate_mem_span (A : E →ₗ[𝕜] E) (u v : E) (σ : 𝕜) (x : E) :
    A x - wielandtDeflate A u v σ x ∈ 𝕜 ∙ u := by
  simp only [wielandtDeflate_apply, sub_sub_cancel]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)

/-- The deflation acts as `A` on the vectors annihilated by `v`. -/
theorem wielandtDeflate_apply_of_inner_eq_zero {A : E →ₗ[𝕜] E} {u v x : E} {σ : 𝕜}
    (hx : (inner 𝕜 v x : 𝕜) = 0) : wielandtDeflate A u v σ x = A x := by
  simp [hx]

/-- **The computed eigenvalue is displaced by the shift.** With the normalization `⟪v, u⟫ = 1`, the
deflated operator has `u` as an eigenvector for `l - σ`. -/
theorem wielandtDeflate_apply_self {A : E →ₗ[𝕜] E} {u v : E} {l : 𝕜}
    (hv : (inner 𝕜 v u : 𝕜) = 1) (hu : A u = l • u) (σ : 𝕜) :
    wielandtDeflate A u v σ u = (l - σ) • u := by
  simp [hu, hv, sub_smul]

/-- Two deflations compose into a rank-two modification: this is how the several-vector deflation `A
- Q Σ Qᴴ` of [saad2011numerical], Prop 4.2 arises. -/
theorem wielandtDeflate_wielandtDeflate (A : E →ₗ[𝕜] E) (u v u' v' : E) (σ σ' : 𝕜) (x : E) :
    wielandtDeflate (wielandtDeflate A u v σ) u' v' σ' x
      = A x - (σ * inner 𝕜 v x) • u - (σ' * inner 𝕜 v' x) • u' := by
  simp

section Spectrum

variable [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
/-- The scalar shift `t - B` maps the line through an eigenvector of `B` into itself. -/
private theorem span_le_comap_of_apply_eq_smul {B : E →ₗ[𝕜] E} {u : E} {m : 𝕜}
    (hu : B u = m • u) (t : 𝕜) :
    (𝕜 ∙ u) ≤ (𝕜 ∙ u).comap (algebraMap 𝕜 (E →ₗ[𝕜] E) t - B) := by
  rintro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  refine Submodule.mem_span_singleton.2 ⟨c * t - c * m, ?_⟩
  simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, map_smul, hu, sub_smul]
  module

omit [FiniteDimensional 𝕜 E] in
/-- On the line through an eigenvector, `t - B` is multiplication by `t - m`, so its determinant
there is `t - m`. -/
private theorem det_restrict_span {B : E →ₗ[𝕜] E} {u : E} {m : 𝕜} (hu : B u = m • u)
    (hu0 : u ≠ 0) (t : 𝕜)
    (h : ∀ x ∈ (𝕜 ∙ u), (algebraMap 𝕜 (E →ₗ[𝕜] E) t - B) x ∈ (𝕜 ∙ u)) :
    ((algebraMap 𝕜 (E →ₗ[𝕜] E) t - B).restrict h).det = t - m := by
  have hrestrict : (algebraMap 𝕜 (E →ₗ[𝕜] E) t - B).restrict h = (t - m) • LinearMap.id := by
    ext x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
    have hx : (x : E) = c • u := hc.symm
    simp only [coe_restrict_apply, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, hx,
      map_smul, hu, id_coe, _root_.id, Submodule.coe_smul]
    module
  rw [hrestrict, LinearMap.det_smul, LinearMap.det_id, mul_one,
    finrank_span_singleton hu0, pow_one]

/-- Two operators differing by an operator with range in the line `𝕜 ∙ u`, and having `u` as an
eigenvector with respective eigenvalues `l` and `m`, have characteristic polynomials related by
`charpoly A * (X - C m) = charpoly B * (X - C l)`. This is the whole of Wielandt's theorem. -/
private theorem eval_charpoly_mul_of_sub_mem_span {A B : E →ₗ[𝕜] E} {u : E} {l m : 𝕜}
    (hA : A u = l • u) (hB : B u = m • u) (hu0 : u ≠ 0)
    (hAB : ∀ x, A x - B x ∈ 𝕜 ∙ u) (t : 𝕜) :
    A.charpoly.eval t * (t - m) = B.charpoly.eval t * (t - l) := by
  have hqA := span_le_comap_of_apply_eq_smul hA t
  have hqB := span_le_comap_of_apply_eq_smul hB t
  have hquot : (𝕜 ∙ u).mapQ (𝕜 ∙ u) (algebraMap 𝕜 (E →ₗ[𝕜] E) t - A) hqA
      = (𝕜 ∙ u).mapQ (𝕜 ∙ u) (algebraMap 𝕜 (E →ₗ[𝕜] E) t - B) hqB := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp only [comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simpa using Submodule.neg_mem _ (hAB x)
  rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly,
    LinearMap.det_eq_det_mul_det _ _ hqA, LinearMap.det_eq_det_mul_det _ _ hqB,
    det_restrict_span hA hu0, det_restrict_span hB hu0, hquot]
  ring

/-- **Wielandt's theorem** ([saad2011numerical], Thm 4.2), with multiplicities: deflating the
eigenpair `(l, u)` with the shift `σ` replaces one copy of `l` in the characteristic polynomial by
`l - σ` and changes nothing else.

The normalization `⟪v, u⟫ = 1` is the hypothesis of the book; it already forces `u ≠ 0`, so no such
hypothesis is stated. -/
theorem charpoly_wielandtDeflate {A : E →ₗ[𝕜] E} {u v : E} {l : 𝕜}
    (hv : (inner 𝕜 v u : 𝕜) = 1) (hu : A u = l • u) (σ : 𝕜) :
    (wielandtDeflate A u v σ).charpoly * (X - C l) = A.charpoly * (X - C (l - σ)) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hv
  refine Polynomial.funext fun t => ?_
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  exact eval_charpoly_mul_of_sub_mem_span (wielandtDeflate_apply_self hv hu σ) hu hu0
    (fun x => by
      simpa using Submodule.neg_mem _ (sub_wielandtDeflate_mem_span A u v σ x)) t

omit [FiniteDimensional 𝕜 E] in
/-- The shifted eigenvalue really is an eigenvalue of the deflated operator: `u` is an eigenvector
for it. -/
theorem hasEigenvalue_wielandtDeflate {A : E →ₗ[𝕜] E} {u v : E} {l : 𝕜}
    (hv : (inner 𝕜 v u : 𝕜) = 1) (hu : A u = l • u) (σ : 𝕜) :
    Module.End.HasEigenvalue (wielandtDeflate A u v σ) (l - σ) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hv
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 (wielandtDeflate_apply_self hv hu σ), hu0⟩

/-- **The spectrum away from the two moved points is unchanged.** Every scalar other than the
computed eigenvalue `l` and its image `l - σ` is an eigenvalue of the deflated operator exactly when
it is one of `A` ([saad2011numerical], Thm 4.2). -/
theorem hasEigenvalue_wielandtDeflate_iff {A : E →ₗ[𝕜] E} {u v : E} {l μ : 𝕜}
    (hv : (inner 𝕜 v u : 𝕜) = 1) (hu : A u = l • u) (σ : 𝕜) (hμ : μ ≠ l) (hμ' : μ ≠ l - σ) :
    Module.End.HasEigenvalue (wielandtDeflate A u v σ) μ ↔ Module.End.HasEigenvalue A μ := by
  have key := congrArg (Polynomial.eval μ) (charpoly_wielandtDeflate hv hu σ)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at key
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    IsRoot.def, IsRoot.def]
  constructor
  · intro h
    rw [h, zero_mul] at key
    exact (mul_eq_zero.1 key.symm).resolve_right (sub_ne_zero.2 hμ')
  · intro h
    rw [h, zero_mul] at key
    exact (mul_eq_zero.1 key).resolve_right (sub_ne_zero.2 hμ)

/-- **Left eigenvectors survive the deflation** ([saad2011numerical], Prop 4.1, and the mechanism of
his proof of Thm 4.2): a left eigenvector `w` of `A`, that is an eigenvector of the adjoint for the
conjugate eigenvalue, belonging to an eigenvalue `μ ≠ l`, is orthogonal to `u` and is a left
eigenvector of the deflated operator for the same eigenvalue.

Orthogonality is the classical argument: `⟪w, A u⟫` equals `l ⟪w, u⟫` on one side and `μ ⟪w, u⟫` on
the other, and `μ ≠ l`. -/
theorem wielandtDeflate_adjoint_apply_of_ne {A : E →ₗ[𝕜] E} {u v w : E} {l μ : 𝕜}
    (hu : A u = l • u) (hw : A.adjoint w = conj μ • w) (hne : μ ≠ l) (σ : 𝕜) :
    (inner 𝕜 w u : 𝕜) = 0 ∧
      (wielandtDeflate A u v σ).adjoint w = conj μ • w := by
  have horth : (inner 𝕜 w u : 𝕜) = 0 := by
    have h1 : (inner 𝕜 w (A u) : 𝕜) = l * inner 𝕜 w u := by
      rw [hu, inner_smul_right]
    have h2 : (inner 𝕜 w (A u) : 𝕜) = μ * inner 𝕜 w u := by
      rw [← LinearMap.adjoint_inner_left, hw, inner_smul_left]
      simp
    have : (l - μ) * inner 𝕜 w u = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  refine ⟨horth, ?_⟩
  refine ext_inner_right 𝕜 fun x => ?_
  rw [LinearMap.adjoint_inner_left, wielandtDeflate_apply, inner_sub_right, inner_smul_right,
    horth, mul_zero, sub_zero, ← LinearMap.adjoint_inner_left, hw]

end Spectrum

/-- **Schur–Wielandt deflation preserves the invariant flag** ([saad2011numerical], Prop 4.1): an
`A`-invariant subspace containing the deflation vector `u` is invariant for the deflated operator.

The Schur vectors of `A` are, up to phase, determined by the complete flag of invariant subspaces
they span, and every member of the flag of a Schur factorization whose first vector is `u` contains
`u`; so this is the coordinate-free content of "the Schur vectors are unchanged", and it needs
neither a Schur factorization — which Mathlib does not have — nor the choice `v = u` nor a
normalization. [saad2011numerical] several-vector deflation `A - Q Σ Qᴴ` (his Prop 4.2) is this
theorem applied once per column of `Q`, through `LinearMap.wielandtDeflate_wielandtDeflate`. -/
theorem schurWielandtDeflate_invtSubmodule {A : E →ₗ[𝕜] E} {u : E} {S : Submodule 𝕜 E}
    (hS : S ∈ Module.End.invtSubmodule A) (hu : u ∈ S) (v : E) (σ : 𝕜) :
    S ∈ Module.End.invtSubmodule (wielandtDeflate A u v σ) := by
  refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun x hx => ?_
  rw [wielandtDeflate_apply]
  exact Submodule.sub_mem _
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hS x hx)
    (Submodule.smul_mem _ _ hu)

end LinearMap

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Householder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Householder deflation** ([quarteroni2000numerical] Remark 5.3): for an eigenpair
`A x = l x`, `x ≠ 0`, and the reflector `H = householder (householderVec x i₀)` that sends `x` to a
multiple of `e_{i₀}` (`Matrix.householder_mulVec_eq_smul_single`), the similar matrix `H A H` has
`i₀`-th column `l e_{i₀}`: `e_{i₀}` is an eigenvector of `H A H` for `l`, because `H A H (H x) = H A
x = l H x` and `H x` is a nonzero multiple of `e_{i₀}`. -/
theorem householder_conj_eigenvector_col (A : Matrix n n 𝕜) {x : n → 𝕜} {l : 𝕜}
    (hx : A *ᵥ x = l • x) (hx0 : x ≠ 0) (i₀ : n) :
    (householder (householderVec x i₀) * A * householder (householderVec x i₀)).col i₀
      = Pi.single i₀ l := by
  set H := householder (householderVec x i₀) with hH
  have hHH : H * H = 1 := householder_mul_self (star_dotProduct_householderVec_self hx0 i₀)
  have hHx := householder_mulVec_eq_smul_single hx0 i₀
  rw [← hH] at hHx
  set α : 𝕜 := -(phase (x i₀) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜))) with hα
  have hα0 : α ≠ 0 := by
    rw [hα, neg_ne_zero]
    refine mul_ne_zero (norm_ne_zero_iff.mp (by rw [norm_phase]; exact one_ne_zero)) ?_
    have : (WithLp.toLp 2 x : EuclideanSpace 𝕜 n) ≠ 0 := by simpa using hx0
    simpa using norm_ne_zero_iff.mpr this
  have key : (H * A * H) *ᵥ (H *ᵥ x) = l • (H *ᵥ x) := by
    rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hHH, Matrix.mul_one, ← mulVec_mulVec,
      hx, mulVec_smul]
  rw [hHx, mulVec_smul, smul_smul, mul_comm, ← smul_smul] at key
  have key' := smul_right_injective (n → 𝕜) hα0 key
  rw [mulVec_single_one] at key'
  rw [key', ← Pi.single_smul, smul_eq_mul, mul_one]

/-- **Householder deflation**, entrywise ([quarteroni2000numerical] Remark 5.3): the `i₀`-th column
of `H A H` is `l e_{i₀}`, that is, `(H A H) i₀ i₀ = l` and `(H A H) i i₀ = 0` for `i ≠ i₀`. -/
theorem householder_conj_eigenvector_apply (A : Matrix n n 𝕜) {x : n → 𝕜} {l : 𝕜}
    (hx : A *ᵥ x = l • x) (hx0 : x ≠ 0) (i₀ i : n) :
    (householder (householderVec x i₀) * A * householder (householderVec x i₀)) i i₀
      = if i = i₀ then l else 0 := by
  have h := congrFun (householder_conj_eigenvector_col A hx hx0 i₀) i
  rw [col_apply] at h
  rw [h, Pi.single_apply]

end Householder

section Charpoly

variable {N : ℕ}

/-- The characteristic matrix of a principal submatrix along `Fin.succ` is the principal submatrix
of the characteristic matrix. -/
private theorem charmatrix_submatrix_succ (M : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    (charmatrix M).submatrix Fin.succ Fin.succ = charmatrix (M.submatrix Fin.succ Fin.succ) := by
  ext i j
  simp [charmatrix_apply, diagonal_apply, Fin.succ_inj]

/-- The characteristic polynomial of a matrix whose first column is `l e₀` factors as `(X - l)`
times that of the trailing principal submatrix: Laplace expansion along the first column. -/
theorem charpoly_eq_mul_charpoly_submatrix_succ_of_col_zero
    {M : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜} {l : 𝕜} (hM : M.col 0 = Pi.single 0 l) :
    M.charpoly = (X - C l) * (M.submatrix Fin.succ Fin.succ).charpoly := by
  have hcol : ∀ i, M i 0 = (Pi.single (0 : Fin (N + 1)) l : Fin (N + 1) → 𝕜) i := fun i =>
    congrFun hM i
  rw [charpoly, det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · rw [charmatrix_apply_eq, hcol, Pi.single_eq_same, Fin.succAbove_zero, charmatrix_submatrix_succ]
    simp [charpoly]
  · intro i _
    rw [charmatrix_apply, hcol, Pi.single_eq_of_ne (Fin.succ_ne_zero i), map_zero, sub_zero,
      diagonal_apply_ne _ (Fin.succ_ne_zero i)]
    simp

/-- **Householder deflation removes one copy of the eigenvalue** ([quarteroni2000numerical] Remark
5.3; §5.12.2): for an eigenpair `A x = l x` of an `(N + 1) × (N + 1)` matrix and
`A₁ = H A H` with `H` the reflector sending `x` to a multiple of `e₀`, the trailing `N × N` block
`A₂ = A₁.submatrix Fin.succ Fin.succ` satisfies `A.charpoly = (X - C l) * A₂.charpoly`: the
eigenvalues of `A₂` are those of `A` with one copy of `l` removed, with multiplicities. Wielandt
deflation (`LinearMap.charpoly_wielandtDeflate`) instead moves `l` to `l - σ` and keeps the size. -/
theorem charpoly_householder_conj_eigenvector (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜)
    {x : Fin (N + 1) → 𝕜} {l : 𝕜} (hx : A *ᵥ x = l • x) (hx0 : x ≠ 0) :
    A.charpoly = (X - C l) *
      ((householder (householderVec x 0) * A * householder (householderVec x 0)).submatrix
        Fin.succ Fin.succ).charpoly := by
  set H := householder (householderVec x 0) with hH
  have hHH : H * H = 1 := householder_mul_self (star_dotProduct_householderVec_self hx0 0)
  have hsim : A.charpoly = (H * A * H).charpoly := by
    rw [charpoly_mul_comm, ← Matrix.mul_assoc, hHH, Matrix.one_mul]
  rw [hsim]
  exact charpoly_eq_mul_charpoly_submatrix_succ_of_col_zero
    (householder_conj_eigenvector_col A hx hx0 0)

end Charpoly

end Matrix
