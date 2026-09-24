import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.PowerMethod
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.KrylovDecomposition
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Orthogonal iteration and the QR algorithm

**Orthogonal (simultaneous) iteration** runs the power method on a whole flag of subspaces at once:
starting from an orthonormal family `q`, the family `Krylov.orthogonalIterate A q k` is the
Gram–Schmidt orthonormalization of `A^k q`, so that the span of its first `m` members is the `k`-th
iterate `Krylov.subspaceIterate A (span {q_0, …, q_m}) k` of the corresponding starting subspace.
Orthonormalizing is what keeps the family from collapsing onto the dominant eigendirection, which is
what the unnormalized iteration does.

The **QR algorithm** is the same iteration written without any subspaces: factor `A_k = Q_k R_k` and
set `A_{k+1} = R_k Q_k`.  The identity `Matrix.qrIterate_eq_conj_orthogonalIterate` is the reason it
computes eigenvalues at all: `A_k` is `A` conjugated by the matrix whose columns are the orthogonal
iterates of the canonical flag, so convergence of the flag is convergence of `A_k` to triangular
form.

## Main definitions

* `Krylov.orthogonalIterate`: the orthonormal family obtained by Gram–Schmidt from `A^k q`.
* `Matrix.qrQ`, `Matrix.qrR`: the QR decomposition built from Gram–Schmidt on the columns.  Mathlib
  has no QR decomposition; this one is normalized so that `R` has a positive diagonal, which is what
  makes it unique and lets it be recognized inside a product.
* `Matrix.qrIterate`, `Matrix.qrAccum`, `Matrix.qrTriangle`: the QR iterates `A_k`, the accumulated
  unitary factor `Q̃_k = Q_0 ⋯ Q_{k-1}` and the accumulated triangular factor `R_{k-1} ⋯ R_0`.
* `Matrix.IsShiftedQrStep μ H H'`: one QR step with shift `μ` for *some* QR factorization, the
  specification of the textbook algorithms (Givens or Householder, any signs);
  `Matrix.IsShiftedQrChain H V R μ p`: a chain of such steps with its factors ([golub2013matrix]
  (10.5.4)).
* `Matrix.IsFrancisStep s t H H'`: the specification of the implicit double-shift (Francis) step,
  `H' = Zᵀ H Z` Hessenberg with `Zᵀ (H² − s H + t I)` upper triangular.

## Main results

* `Krylov.span_orthogonalIterate`: the orthogonal iterates span the iterated subspaces.
* `Matrix.qrQ_mul_qrR`: `A = Q R`, with `Matrix.qrQ_mem_unitaryGroup` and
  `Matrix.isUpperTriangular_qrR`.
* `Matrix.euclideanCol_eq_gramSchmidtNormed_of_eq_mul`: **uniqueness of the QR decomposition** in
  the only form needed here — if `M = U T` with `U` unitary and `T` upper triangular with positive
  diagonal, then the columns of `U` are the Gram–Schmidt orthonormalization of the columns of `M`.
* `Matrix.pow_eq_qrAccum_mul_qrTriangle`: `A^k = Q̃_k R̃_k`, so the accumulated unitary factor of
  the QR algorithm orthonormalizes the columns of `A^k`.
* `Matrix.qrAccum_eq_orthogonalIterate` and `Matrix.qrIterate_eq_conj_orthogonalIterate`: the QR
  algorithm *is* orthogonal iteration on the canonical flag.
* `Krylov.tendsto_orthogonalIterate` and `Matrix.tendsto_qrIterate`: **the convergence theorems**.
  For a diagonalizable operator whose eigenvalues have pairwise distinct moduli and a starting flag
  in general position, the compressions `Q_νᴴ A Q_ν` — the QR iterates, in the matrix reading — tend
  to upper triangular form with the eigenvalues in order down the diagonal.
* `Matrix.exists_abs_qrIterate_apply_le`: the rate, `O((r/|λ_k|)^ν)` for the entries below the
  diagonal in column `k`; `Matrix.disjoint_span_euclideanCol_iff_isUnit_leadingPrincipal`: the
  general-position hypothesis is the nonvanishing of the leading principal minors of the inverse
  eigenvector matrix, the hypothesis [quarteroni2000numerical] Property 5.9 omits.
* `Matrix.isHermitian_qrIterate`, `Matrix.isUpperHessenberg_qrIterate`: the iteration preserves
  Hermitian and upper Hessenberg form ([quarteroni2000numerical] §5.6.4).
* `Matrix.shiftedQrStep`, `Matrix.shiftedQrIterate`, `Matrix.rayleighShiftQrIterate`,
  `Matrix.doubleShiftQrStep`: the shifted iterations of [quarteroni2000numerical] §5.7, each a
  unitary similarity; `Matrix.shiftedQrIterate_eq_qrIterate_sub_add` reduces a fixed shift to the
  basic iteration on `A - μ I`.
* Shifted steps for arbitrary factorizations: each is a unitary similarity
  (`Matrix.IsShiftedQrStep.eq_conj`), two of them are diagonally similar when `H − μ I` is
  nonsingular (`Matrix.IsShiftedQrStep.unique_of_isUnit`), Hessenberg form survives a nonsingular
  step (`Matrix.IsShiftedQrStep.isUpperHessenberg`, of which `Matrix.isUpperHessenberg_qrQ` and
  `Matrix.isUpperHessenberg_qrIterate` are the canonical instances), and an exact shift deflates
  an unreduced Hessenberg matrix in one step
  (`Matrix.IsUnreducedUpperHessenberg.isShiftedQrStep_apply_last`, [golub2013matrix] Theorem 7.5.1).
* `Matrix.prod_mul_prod_reverse_eq_prod_sub_smul_one`: a chain multiplies out to the shift
  polynomial, `(V_0 ⋯ V_{p-1})(R_{p-1} ⋯ R_0) = ∏ (H_0 − μ_i I)` ([golub2013matrix] (7.5.7),
  Theorem 10.5.1); `Matrix.pow_eq_qrAccum_mul_qrTriangle` is its unshifted canonical instance.
  `Matrix.exists_isShiftedQrChain`: Givens chains exist for arbitrary shifts.
* The Francis step: the double-shift step of a real matrix is real
  (`Matrix.doubleShiftQrStep_map_ofReal`), the explicit route gives a Francis step
  (`Matrix.isFrancisStep_qrQ`), and every Francis step of an unreduced Hessenberg matrix is that
  one up to a `±1` diagonal similarity (`Matrix.IsFrancisStep.eq_diagonal_conj`, through the
  implicit Q theorem `Matrix.implicitQ_real` of `Numlib/LinearAlgebra/Matrix/KrylovDecomposition`).

## Implementation notes

The index type of a matrix carries a `LinearOrder` and a `LocallyFiniteOrderBot` here, because
Gram–Schmidt orthonormalizes from left to right and so has to know what "earlier" means.  Both hold
for `Fin n`.

`Numlib.LinearAlgebra.Matrix.QR` already has the QR factorization, as the *existence* statement
`Matrix.exists_qr` together with its uniqueness `Matrix.qr_unique`; an existence statement cannot be
iterated, so the algorithm needs the factorization as a function of the matrix, which is what
`Matrix.qrQ` and `Matrix.qrR` are.  They are the same factorization: both take `Q` to be the
Gram–Schmidt orthonormalization of the columns, and `Matrix.qr_unique` identifies them with any
other factorization of positive diagonal, a product of Householder reflectors included.  What is not
there and is proved here is the reverse reading,
`Matrix.euclideanCol_eq_gramSchmidtNormed_of_eq_mul`: it is about the *columns* rather than the
factors, and it is the columns that orthogonal iteration speaks of.

The nonsingularity hypothesis `IsUnit A.det` is what makes the QR decomposition unique, through the
positivity of the diagonal of `R`: at a singular matrix a column can lie in the span of its
predecessors, the corresponding Gram–Schmidt vector is `0`, and
`InnerProductSpace.gramSchmidtOrthonormalBasis` completes the family by an arbitrary choice.  Every
statement below that identifies a factor assumes it; the decomposition `A = Q R` itself does not.

## References

Orthogonal iteration and the QR algorithm are [kress1998numerical], §7.4: the definitions here are
his, and `Matrix.qrIterate_eq_conj_orthogonalIterate` is his (7.25)–(7.26).  His Theorem 7.19
(orthogonal iteration converges to triangular form) is `Krylov.tendsto_orthogonalIterate` and his
Theorem 7.20 (so does the QR algorithm) is `Matrix.tendsto_qrIterate`; both rest on his Lemma 7.18,
the gap form of subspace iteration, which is `Krylov.exists_gap_subspaceIterate_span_image_le` of
`Numlib/Eigen/PowerMethod`.
-/

open Filter Topology InnerProductSpace Submodule

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- **Orthogonal (simultaneous) iteration**: the Gram–Schmidt orthonormalization of the iterated
family `A^k q`.

Orthonormalizing after every step and orthonormalizing once at the end give the same family, since
Gram–Schmidt depends only on the flag its input spans; the definition takes the second reading,
which is the one with a closed form.  The iteration is run on a whole family at once so that each
initial segment iterates its own subspace, which is `Krylov.span_orthogonalIterate`. -/
noncomputable def orthogonalIterate (A : E →ₗ[𝕜] E) (q : ι → E) (k : ℕ) : ι → E :=
  gramSchmidtNormed 𝕜 fun i => (A ^ k) (q i)

/-- **The orthogonal iterates span the iterated subspaces**: the span of the members of
`orthogonalIterate A q k` up to the index `m` is the `k`-th subspace iterate of the span of the
members of `q` up to `m`. -/
theorem span_orthogonalIterate (A : E →ₗ[𝕜] E) (q : ι → E) (k : ℕ) (m : ι) :
    span 𝕜 (orthogonalIterate A q k '' Set.Iic m) =
      subspaceIterate A (span 𝕜 (q '' Set.Iic m)) k := by
  simp only [orthogonalIterate, subspaceIterate]
  rw [span_gramSchmidtNormed, span_gramSchmidt_Iic, ← Submodule.span_image, Set.image_image]

/-- **The orthogonal iterates span the iterated subspaces of every lower set of indices**, which is
what makes the whole flag, and not only one member of it, iterate at once. -/
theorem span_orthogonalIterate_of_isLowerSet (A : E →ₗ[𝕜] E) (q : ι → E) (k : ℕ) {J : Set ι}
    (hJ : IsLowerSet J) :
    span 𝕜 (orthogonalIterate A q k '' J) = subspaceIterate A (span 𝕜 (q '' J)) k := by
  simp only [orthogonalIterate, subspaceIterate]
  rw [span_gramSchmidtNormed, span_gramSchmidt_of_isLowerSet _ hJ, ← Submodule.span_image,
    Set.image_image]

/-- The orthogonal iterates are an orthonormal family as soon as the iterated family is
independent. -/
theorem orthonormal_orthogonalIterate {A : E →ₗ[𝕜] E} {q : ι → E} {k : ℕ}
    (h : LinearIndependent 𝕜 fun i => (A ^ k) (q i)) : Orthonormal 𝕜 (orthogonalIterate A q k) :=
  gramSchmidtNormed_orthonormal h

/-- At the zeroth step orthogonal iteration returns an orthonormal starting family unchanged. -/
theorem orthogonalIterate_zero {A : E →ₗ[𝕜] E} {q : ι → E} (hq : Orthonormal 𝕜 q) :
    orthogonalIterate A q 0 = q := by
  have h0 : (fun i => (A ^ 0) (q i)) = q := by funext j; simp
  funext i
  simp only [orthogonalIterate, h0, gramSchmidtNormed,
    congrFun (gramSchmidt_of_orthogonal 𝕜 fun _ _ hab => hq.2 hab) i, hq.1 i]
  simp

/-! ### Convergence of orthogonal iteration

[kress1998numerical], Theorem 7.19.  The gap bound `Krylov.exists_gap_subspaceIterate_span_image_le`
applied to every initial segment of the flag says that the iterated subspaces converge to the
invariant subspaces of the dominant eigenvalues; what is added here is that the *compressions*
`Q_νᴴ A Q_ν` then converge to the triangular matrix of the eigenvalues.

The two halves of that are `Krylov.norm_inner_le_of_gap` for the entries below the diagonal and
`Krylov.norm_inner_self_sub_le` for the diagonal itself, and neither mentions the iteration: they
are statements about an orthonormal family whose initial segments are close to an invariant flag.
The second is where the eigenvalue appears, through the Schur property `A b - λ_j b ∈ T_{<j}` of the
part of `q_j` in `T_{≤ j} ∩ T_{<j}ᴾ`. -/

section Triangular

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The off-diagonal entries: a vector orthogonal to `S` tests to nothing against `A` applied to a
vector of `S`, up to the gap between `S` and an `A`-invariant subspace `T`. -/
theorem norm_inner_le_of_gap {A : Module.End 𝕜 E} {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ y, ‖A y‖ ≤ M * ‖y‖) {T S : Submodule 𝕜 E} [T.HasOrthogonalProjection]
    [S.HasOrthogonalProjection] (hinv : ∀ y ∈ T, A y ∈ T) {v w : E} (hv : v ∈ S) (hnv : ‖v‖ ≤ 1)
    (hw : w ∈ Sᗮ) (hnw : ‖w‖ ≤ 1) :
    ‖(inner 𝕜 w (A v) : 𝕜)‖ ≤ 2 * M * T.gap S := by
  have hgap0 : 0 ≤ T.gap S := T.gap_nonneg S
  have hPv : ‖v - T.starProjection v‖ ≤ T.gap S := by
    have h := T.norm_starProjection_sub_le_gap_mul S v
    rw [starProjection_eq_self_iff.2 hv, norm_sub_rev] at h
    calc ‖v - T.starProjection v‖ ≤ T.gap S * ‖v‖ := h
      _ ≤ T.gap S * 1 := by gcongr
      _ = T.gap S := mul_one _
  have hPw : ‖T.starProjection w‖ ≤ T.gap S := by
    have h := T.norm_starProjection_sub_le_gap_mul S w
    rw [(Submodule.starProjection_apply_eq_zero_iff S).2 hw, sub_zero] at h
    calc ‖T.starProjection w‖ ≤ T.gap S * ‖w‖ := h
      _ ≤ T.gap S * 1 := by gcongr
      _ = T.gap S := mul_one _
  have hnPv : ‖T.starProjection v‖ ≤ 1 := (T.norm_starProjection_apply_le v).trans hnv
  have hsplit : (inner 𝕜 w (A v) : 𝕜) =
      inner 𝕜 (T.starProjection w) (A (T.starProjection v))
        + inner 𝕜 w (A (v - T.starProjection v)) := by
    have h1 : (inner 𝕜 (T.starProjection w) (A (T.starProjection v)) : 𝕜)
        = inner 𝕜 w (A (T.starProjection v)) :=
      Submodule.inner_starProjection_left_eq_of_mem T w (hinv _ (T.starProjection_apply_mem v))
    rw [h1, ← inner_add_right, ← map_add]
    congr 2
    abel
  calc ‖(inner 𝕜 w (A v) : 𝕜)‖
      ≤ ‖(inner 𝕜 (T.starProjection w) (A (T.starProjection v)) : 𝕜)‖
        + ‖(inner 𝕜 w (A (v - T.starProjection v)) : 𝕜)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖T.starProjection w‖ * ‖A (T.starProjection v)‖ + ‖w‖ * ‖A (v - T.starProjection v)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ T.gap S * (M * 1) + 1 * (M * T.gap S) := by
        gcongr
        · exact (hA _).trans (by gcongr)
        · exact (hA _).trans (by gcongr)
    _ = 2 * M * T.gap S := by ring

/-- The diagonal entries: a unit vector of `S` orthogonal to `Slt` has Rayleigh quotient close to
`lam`, once `S` is close to `Tle` and `Slt` to `Tlt`. -/
theorem norm_inner_self_sub_le {A : Module.End 𝕜 E} {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ y, ‖A y‖ ≤ M * ‖y‖) {Tle Tlt S Slt : Submodule 𝕜 E}
    [Tle.HasOrthogonalProjection] [Tlt.HasOrthogonalProjection]
    [S.HasOrthogonalProjection] [Slt.HasOrthogonalProjection]
    (hTle : Tlt ≤ Tle) {lam : 𝕜}
    (hschur : ∀ b ∈ Tle, A b - lam • b ∈ Tlt)
    {v : E} (hv1 : ‖v‖ = 1) (hvS : v ∈ S) (hvSlt : v ∈ Sltᗮ) :
    ‖(inner 𝕜 v (A v) : 𝕜) - lam‖
      ≤ (M + ‖lam‖) * (Tlt.gap Slt + Tle.gap S) * (2 + (Tlt.gap Slt + Tle.gap S)) := by
  set b := Tle.starProjection v - Tlt.starProjection v with hb
  set e := Tlt.gap Slt + Tle.gap S with he
  have he0 : 0 ≤ e := add_nonneg (Tlt.gap_nonneg Slt) (Tle.gap_nonneg S)
  have hvb : v - b = Tlt.starProjection v + (v - Tle.starProjection v) := by rw [hb]; abel
  have hna : ‖Tlt.starProjection v‖ ≤ Tlt.gap Slt := by
    have h := Tlt.norm_starProjection_sub_le_gap_mul Slt v
    rw [(Submodule.starProjection_apply_eq_zero_iff Slt).2 hvSlt, sub_zero, hv1, mul_one] at h
    exact h
  have hnc : ‖v - Tle.starProjection v‖ ≤ Tle.gap S := by
    have h := Tle.norm_starProjection_sub_le_gap_mul S v
    rw [starProjection_eq_self_iff.2 hvS, norm_sub_rev, hv1, mul_one] at h
    exact h
  have hne : ‖v - b‖ ≤ e := by
    rw [hvb]
    exact (norm_add_le _ _).trans (add_le_add hna hnc)
  have hnb : ‖b‖ ≤ 1 + ‖v - b‖ := by
    have : ‖b‖ ≤ ‖v‖ + ‖v - b‖ := by
      calc ‖b‖ = ‖v - (v - b)‖ := by congr 1; abel
        _ ≤ ‖v‖ + ‖v - b‖ := norm_sub_le _ _
    rwa [hv1] at this
  have hbTle : b ∈ Tle :=
    Submodule.sub_mem _ (Tle.starProjection_apply_mem v) (hTle (Tlt.starProjection_apply_mem v))
  have hbperp : ∀ z ∈ Tlt, (inner 𝕜 b z : 𝕜) = 0 := by
    intro z hz
    rw [hb, inner_sub_left, Submodule.inner_starProjection_left_eq_of_mem Tle v (hTle hz),
      Submodule.inner_starProjection_left_eq_of_mem Tlt v hz, sub_self]
  have hbAb : (inner 𝕜 b (A b) : 𝕜) = lam * inner 𝕜 b b := by
    have hz := hbperp _ (hschur b hbTle)
    rw [inner_sub_right, inner_smul_right, sub_eq_zero] at hz
    rw [hz]
  have hkey : (inner 𝕜 v (A v) : 𝕜) - lam =
      (inner 𝕜 v (A (v - b)) + inner 𝕜 (v - b) (A b)) + lam * (inner 𝕜 b b - 1) := by
    rw [map_sub, inner_sub_right, inner_sub_left, mul_sub, ← hbAb]
    ring
  have hb2 : ‖(inner 𝕜 b b : 𝕜) - 1‖ ≤ ‖v - b‖ * (2 + ‖v - b‖) := by
    have hcast : (inner 𝕜 b b : 𝕜) - 1 = ((‖b‖ ^ 2 - 1 : ℝ) : 𝕜) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      ring
    rw [hcast, RCLike.norm_ofReal]
    have hva : ‖v‖ - ‖b‖ ≤ ‖v - b‖ := norm_sub_norm_le v b
    rw [hv1] at hva
    have h1 : |‖b‖ - 1| ≤ ‖v - b‖ := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have h2 : |‖b‖ ^ 2 - 1| = |‖b‖ - 1| * (‖b‖ + 1) := by
      rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖b‖ + 1), ← abs_mul]
      congr 1
      ring
    rw [h2]
    have h3 : ‖b‖ + 1 ≤ 2 + ‖v - b‖ := by linarith [hnb]
    exact mul_le_mul h1 h3 (by positivity) (norm_nonneg _)
  have hbound : ‖(inner 𝕜 v (A v) : 𝕜) - lam‖
      ≤ (M + ‖lam‖) * ‖v - b‖ * (2 + ‖v - b‖) := by
    rw [hkey]
    have hA1 : ‖(inner 𝕜 v (A (v - b)) : 𝕜)‖ ≤ M * ‖v - b‖ := by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [hv1, one_mul]
      exact hA _
    have hA2 : ‖(inner 𝕜 (v - b) (A b) : 𝕜)‖ ≤ ‖v - b‖ * (M * ‖b‖) :=
      (norm_inner_le_norm _ _).trans (by gcongr; exact hA _)
    have hA3 : ‖lam * ((inner 𝕜 b b : 𝕜) - 1)‖ ≤ ‖lam‖ * (‖v - b‖ * (2 + ‖v - b‖)) := by
      rw [norm_mul]
      gcongr
    calc ‖(inner 𝕜 v (A (v - b)) + inner 𝕜 (v - b) (A b) : 𝕜) + lam * (inner 𝕜 b b - 1)‖
        ≤ (‖(inner 𝕜 v (A (v - b)) : 𝕜)‖ + ‖(inner 𝕜 (v - b) (A b) : 𝕜)‖)
          + ‖lam * ((inner 𝕜 b b : 𝕜) - 1)‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ (M * ‖v - b‖ + ‖v - b‖ * (M * (1 + ‖v - b‖)))
          + ‖lam‖ * (‖v - b‖ * (2 + ‖v - b‖)) :=
          add_le_add (add_le_add hA1 (hA2.trans (by gcongr))) hA3
      _ = (M + ‖lam‖) * ‖v - b‖ * (2 + ‖v - b‖) := by ring
  refine hbound.trans ?_
  have h0 : (0 : ℝ) ≤ ‖v - b‖ := norm_nonneg _
  have hMl : 0 ≤ M + ‖lam‖ := by positivity
  gcongr

/-- The span of a subfamily of an eigenbasis is invariant under the operator. -/
theorem mapsTo_span_image_of_eigen {ι : Type*} {A : Module.End 𝕜 E} {x : ι → E} {l : ι → 𝕜}
    (heig : ∀ j, A (x j) = l j • x j) (J : Set ι) :
    ∀ y ∈ span 𝕜 (x '' J), A y ∈ span 𝕜 (x '' J) := by
  intro y hy
  have hle : span 𝕜 (x '' J) ≤ Submodule.comap A (span 𝕜 (x '' J)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, heig i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  exact hle hy

/-- A member of an orthonormal family is orthogonal to the span of any subfamily not containing
it. -/
theorem mem_orthogonal_span_image_of_orthonormal {ι : Type*} {q : ι → E} (hq : Orthonormal 𝕜 q)
    {J : Set ι} {j : ι} (hj : j ∉ J) : q j ∈ (span 𝕜 (q '' J))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  have hle : span 𝕜 (q '' J) ≤
      LinearMap.ker ((innerSL 𝕜 (q j) : E →L[𝕜] 𝕜) : E →ₗ[𝕜] 𝕜) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hq.2 fun h => hj (h ▸ hi)
  exact hle hu

/-- Two linearly independent families span subspaces of the same dimension over every index
set. -/
theorem finrank_span_image_eq_of_linearIndependent {ι : Type*} [Finite ι] {q x : ι → E}
    (hq : LinearIndependent 𝕜 q) (hx : LinearIndependent 𝕜 x) (J : Set ι) :
    Module.finrank 𝕜 ↥(span 𝕜 (q '' J)) = Module.finrank 𝕜 ↥(span 𝕜 (x '' J)) := by
  classical
  cases nonempty_fintype ι
  have h1 : Set.range (fun j : ↥J => q ↑j) = q '' J := by rw [← Set.image_eq_range]
  have h2 : Set.range (fun j : ↥J => x ↑j) = x '' J := by rw [← Set.image_eq_range]
  have hqli : LinearIndependent 𝕜 fun j : ↥J => q ↑j := hq.comp _ Subtype.val_injective
  have hxli : LinearIndependent 𝕜 fun j : ↥J => x ↑j := hx.comp _ Subtype.val_injective
  rw [← h1, ← h2, finrank_span_eq_card hqli, finrank_span_eq_card hxli]

open scoped NNReal in
/-- The flag of iterated subspaces converges to the flag of dominant invariant subspaces. -/
theorem tendsto_gap_span_image [FiniteDimensional 𝕜 E] {ι : Type*} [Finite ι] [LinearOrder ι]
    {A : Module.End 𝕜 E} {x : ι → E} {l : ι → 𝕜} {q : ℕ → ι → E}
    (hx : LinearIndependent 𝕜 x) (hxtop : span 𝕜 (Set.range x) = ⊤)
    (heig : ∀ j, A (x j) = l j • x j) (hl0 : ∀ j, l j ≠ 0)
    (hsep : ∀ j k : ι, j < k → ‖l k‖ < ‖l j‖) (hq : ∀ ν, Orthonormal 𝕜 (q ν))
    (hspan : ∀ (ν : ℕ) (J : Set ι), IsLowerSet J →
      span 𝕜 (q ν '' J) = subspaceIterate A (span 𝕜 (q 0 '' J)) ν)
    (hgen : ∀ J : Set ι, IsLowerSet J → Disjoint (span 𝕜 (q 0 '' J)) (span 𝕜 (x '' Jᶜ)))
    (J : Set ι) (hJ : IsLowerSet J) :
    Tendsto (fun ν => (span 𝕜 (x '' J)).gap (span 𝕜 (q ν '' J))) atTop (𝓝 0) := by
  classical
  cases nonempty_fintype ι
  rcases Set.eq_empty_or_nonempty J with rfl | hJne
  · simp only [Set.image_empty, Submodule.span_empty, Submodule.gap_self]
    exact tendsto_const_nhds
  have hJfin : J.toFinset.Nonempty := by
    obtain ⟨j, hj⟩ := hJne
    exact ⟨j, Set.mem_toFinset.2 hj⟩
  set rho : ℝ≥0 := J.toFinset.inf' hJfin (fun j => ‖l j‖₊) with hrho
  set rr : ℝ≥0 := Jᶜ.toFinset.sup (fun k => ‖l k‖₊) with hrr
  have hrho0 : 0 < rho := by
    rw [hrho, Finset.lt_inf'_iff]
    intro j _
    simpa using hl0 j
  have hrrho : rr < rho := by
    rw [hrr, Finset.sup_lt_iff hrho0]
    intro k hk
    have hkJ : k ∉ J := by simpa using Set.mem_toFinset.1 hk
    rw [Finset.lt_inf'_iff]
    intro j hj
    have hjJ : j ∈ J := Set.mem_toFinset.1 hj
    have hjk : j < k := lt_of_not_ge fun hle => hkJ (hJ hle hjJ)
    exact_mod_cast hsep j k hjk
  have hrank := finrank_span_image_eq_of_linearIndependent (hq 0).linearIndependent hx J
  obtain ⟨D, hD⟩ := exists_gap_subspaceIterate_span_image_le (J := J) hx hxtop heig
    (by exact_mod_cast hrho0) (fun j hj => by
      exact_mod_cast Finset.inf'_le (fun j => ‖l j‖₊) (Set.mem_toFinset.2 hj))
    (NNReal.coe_nonneg rr) (by exact_mod_cast hrrho)
    (fun k hk => by
      exact_mod_cast Finset.le_sup (f := fun k => ‖l k‖₊) (Set.mem_toFinset.2 hk))
    (hgen J hJ) hrank
  have hq1 : ((rr : ℝ) / (rho : ℝ)) < 1 := (div_lt_one (by exact_mod_cast hrho0)).2
    (by exact_mod_cast hrrho)
  have hq0 : (0 : ℝ) ≤ (rr : ℝ) / (rho : ℝ) := by positivity
  have hlim : Tendsto (fun ν : ℕ => D * ((rr : ℝ) / (rho : ℝ)) ^ ν) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul D
  refine squeeze_zero (fun ν => Submodule.gap_nonneg _ _) (fun ν => ?_) hlim
  rw [Submodule.gap_congr _ _ (hspan ν J hJ)]
  exact hD ν

/-- **Kress's Theorem 7.19**: orthogonal iteration converges to triangular form. -/
theorem tendsto_orthogonalIterate [FiniteDimensional 𝕜 E] {ι : Type*} [Finite ι] [LinearOrder ι]
    {A : Module.End 𝕜 E} {x : ι → E} {l : ι → 𝕜} {q : ℕ → ι → E}
    (hx : LinearIndependent 𝕜 x) (hxtop : span 𝕜 (Set.range x) = ⊤)
    (heig : ∀ j, A (x j) = l j • x j) (hl0 : ∀ j, l j ≠ 0)
    (hsep : ∀ j k : ι, j < k → ‖l k‖ < ‖l j‖) (hq : ∀ ν, Orthonormal 𝕜 (q ν))
    (hspan : ∀ (ν : ℕ) (J : Set ι), IsLowerSet J →
      span 𝕜 (q ν '' J) = subspaceIterate A (span 𝕜 (q 0 '' J)) ν)
    (hgen : ∀ J : Set ι, IsLowerSet J → Disjoint (span 𝕜 (q 0 '' J)) (span 𝕜 (x '' Jᶜ))) :
    (∀ j k : ι, k < j → Tendsto (fun ν => (inner 𝕜 (q ν j) (A (q ν k)) : 𝕜)) atTop (𝓝 0)) ∧
      ∀ j : ι, Tendsto (fun ν => (inner 𝕜 (q ν j) (A (q ν j)) : 𝕜)) atTop (𝓝 (l j)) := by
  set M := ‖LinearMap.toContinuousLinearMap A‖ with hMdef
  have hM : 0 ≤ M := norm_nonneg _
  have hA : ∀ y, ‖A y‖ ≤ M * ‖y‖ := fun y =>
    (LinearMap.toContinuousLinearMap A).le_opNorm y
  have hgapJ := tendsto_gap_span_image hx hxtop heig hl0 hsep hq hspan hgen
  have hinv : ∀ (J : Set ι), ∀ y ∈ span 𝕜 (x '' J), A y ∈ span 𝕜 (x '' J) :=
    fun J => mapsTo_span_image_of_eigen heig J
  have hmemS : ∀ (ν : ℕ) (J : Set ι) (i : ι), i ∈ J → q ν i ∈ span 𝕜 (q ν '' J) :=
    fun ν J i hi => Submodule.subset_span ⟨i, hi, rfl⟩
  have hperp : ∀ (ν : ℕ) (J : Set ι) (j : ι), j ∉ J → q ν j ∈ (span 𝕜 (q ν '' J))ᗮ :=
    fun ν J j hj => mem_orthogonal_span_image_of_orthonormal (hq ν) hj
  have hnq : ∀ (ν : ℕ) (j : ι), ‖q ν j‖ = 1 := fun ν j => (hq ν).1 j
  constructor
  · intro j k hkj
    have hbound : ∀ ν, ‖(inner 𝕜 (q ν j) (A (q ν k)) : 𝕜)‖
        ≤ 2 * M * (span 𝕜 (x '' Set.Iic k)).gap (span 𝕜 (q ν '' Set.Iic k)) := fun ν =>
      norm_inner_le_of_gap hM hA (hinv (Set.Iic k)) (hmemS ν _ k le_rfl)
        ((hnq ν k).le) (hperp ν _ j (by simpa using hkj)) ((hnq ν j).le)
    refine squeeze_zero_norm hbound ?_
    simpa using (hgapJ (Set.Iic k) (isLowerSet_Iic k)).const_mul (2 * M)
  · intro j
    have hTle : span 𝕜 (x '' Set.Iio j) ≤ span 𝕜 (x '' Set.Iic j) :=
      Submodule.span_mono (Set.image_mono Set.Iio_subset_Iic_self)
    have hschur : ∀ b ∈ span 𝕜 (x '' Set.Iic j), A b - l j • b ∈ span 𝕜 (x '' Set.Iio j) := by
      have hle : span 𝕜 (x '' Set.Iic j) ≤
          Submodule.comap (A - l j • (1 : Module.End 𝕜 E)) (span 𝕜 (x '' Set.Iio j)) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply,
          LinearMap.smul_apply, Module.End.one_apply, heig i, ← sub_smul]
        rcases lt_or_eq_of_le (Set.mem_Iic.1 hi) with hlt | rfl
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hlt, rfl⟩)
        · simp
      intro b hb
      simpa using hle hb
    have hbound : ∀ ν, ‖(inner 𝕜 (q ν j) (A (q ν j)) : 𝕜) - l j‖
        ≤ (M + ‖l j‖) * ((span 𝕜 (x '' Set.Iio j)).gap (span 𝕜 (q ν '' Set.Iio j))
            + (span 𝕜 (x '' Set.Iic j)).gap (span 𝕜 (q ν '' Set.Iic j)))
          * (2 + ((span 𝕜 (x '' Set.Iio j)).gap (span 𝕜 (q ν '' Set.Iio j))
            + (span 𝕜 (x '' Set.Iic j)).gap (span 𝕜 (q ν '' Set.Iic j)))) := fun ν =>
      norm_inner_self_sub_le hM hA hTle hschur (hnq ν j) (hmemS ν _ j le_rfl)
        (hperp ν _ j (by simp))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun ν => norm_nonneg _) hbound ?_
    have hlim : Tendsto (fun ν => (span 𝕜 (x '' Set.Iio j)).gap (span 𝕜 (q ν '' Set.Iio j))
        + (span 𝕜 (x '' Set.Iic j)).gap (span 𝕜 (q ν '' Set.Iic j))) atTop (𝓝 0) := by
      simpa using (hgapJ (Set.Iio j) (isLowerSet_Iio j)).add (hgapJ (Set.Iic j) (isLowerSet_Iic j))
    have := ((hlim.const_mul (M + ‖l j‖)).mul ((tendsto_const_nhds (x := (2 : ℝ))).add hlim))
    simpa using this

end Triangular


end Krylov

namespace Matrix

open scoped ComplexOrder

section Column

variable {𝕜 : Type*} {n : Type*}

/-! ### Columns as Euclidean vectors -/

/-- The `j`-th column of a matrix, read as a vector of `EuclideanSpace 𝕜 n`. -/
noncomputable def euclideanCol (A : Matrix n n 𝕜) (j : n) : EuclideanSpace 𝕜 n :=
  WithLp.toLp 2 (Aᵀ j)

@[simp]
theorem euclideanCol_apply (A : Matrix n n 𝕜) (i j : n) :
    (euclideanCol A j).ofLp i = A i j := rfl

theorem euclideanCol_injective :
    Function.Injective (euclideanCol : Matrix n n 𝕜 → n → EuclideanSpace 𝕜 n) := by
  intro A B h
  ext i j
  exact congrFun (congrArg WithLp.ofLp (congrFun h j)) i

end Column

section Ring

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix acts on the canonical flag by taking columns: `M e_j` is the `j`-th column of `M`. -/
theorem toEuclideanLin_euclideanCol_one (M : Matrix n n 𝕜) (j : n) :
    toEuclideanLin M (euclideanCol 1 j) = euclideanCol M j := by
  ext i
  simp [euclideanCol, toLpLin_apply, mulVec, dotProduct, Matrix.one_apply]

set_option linter.unusedDecidableInType false in
/-- The columns of a product: `(U T)_{·j} = ∑_p T_{pj} U_{·p}`. -/
theorem euclideanCol_mul (U T : Matrix n n 𝕜) (j : n) :
    euclideanCol (U * T) j = ∑ p, T p j • euclideanCol U p := by
  have h : euclideanCol (U * T) j = toEuclideanLin U (euclideanCol T j) := by
    ext i
    simp [euclideanCol, toLpLin_apply, mulVec, dotProduct, Matrix.mul_apply, mul_comm]
  rw [h, euclideanCol, toEuclideanLin_apply_eq_sum]
  rfl

/-- The columns of a unitary matrix are an orthonormal family. -/
theorem orthonormal_euclideanCol {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) :
    Orthonormal 𝕜 (euclideanCol U) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hinner : (inner 𝕜 (euclideanCol U i) (euclideanCol U j) : 𝕜) = (Uᴴ * U) i j := by
    simp [PiLp.inner_apply, RCLike.inner_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      mul_comm]
  rw [hinner, hU, Matrix.one_apply]

/-- The columns of a nonsingular matrix are linearly independent. -/
theorem linearIndependent_euclideanCol {A : Matrix n n 𝕜} (hA : IsUnit A.det) :
    LinearIndependent 𝕜 (euclideanCol A) := by
  have h : LinearIndependent 𝕜 A.col :=
    Matrix.linearIndependent_cols_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 hA)
  exact LinearIndependent.of_comp (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).toLinearMap h

/-- The columns of a nonsingular `n × n` matrix span `EuclideanSpace 𝕜 n`. -/
theorem span_range_euclideanCol_eq_top {A : Matrix n n 𝕜} (hA : IsUnit A.det) :
    Submodule.span 𝕜 (Set.range (euclideanCol A)) = ⊤ :=
  (linearIndependent_euclideanCol hA).span_eq_top_of_card_eq_finrank'
    (by rw [finrank_euclideanSpace])

/-- The columns of the eigenvector matrix are eigenvectors: if `X⁻¹ A X = diag(λ)` with `X`
nonsingular then `A` sends the `j`-th column of `X` to `λ_j` times itself. -/
theorem toEuclideanLin_euclideanCol_of_conj_eq_diagonal {A X : Matrix n n 𝕜} (hX : IsUnit X)
    {lam : n → 𝕜} (hD : X⁻¹ * A * X = diagonal lam) (j : n) :
    toEuclideanLin A (euclideanCol X j) = lam j • euclideanCol X j := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hAX : A * X = X * diagonal lam := by
    rw [← hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.one_mul]
  have hcol : euclideanCol (diagonal lam) j = lam j • euclideanCol (1 : Matrix n n 𝕜) j := by
    ext i
    simp [euclideanCol, diagonal_apply, one_apply]
  rw [← toEuclideanLin_euclideanCol_one, ← toEuclideanLin_mul_apply, hAX, toEuclideanLin_mul_apply,
    toEuclideanLin_euclideanCol_one, hcol, map_smul, toEuclideanLin_euclideanCol_one]

/-- A matrix similar to a diagonal matrix with nonzero entries is nonsingular. -/
theorem isUnit_det_of_conj_eq_diagonal {A X : Matrix n n 𝕜} (hX : IsUnit X) {lam : n → 𝕜}
    (hD : X⁻¹ * A * X = diagonal lam) (hne : ∀ i, lam i ≠ 0) : IsUnit A.det := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hA : A = X * diagonal lam * X⁻¹ := by
    rw [← hD, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.mul_one,
      ← Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.one_mul]
  rw [hA, det_mul, det_mul, det_diagonal, det_nonsing_inv]
  exact (hdet.mul (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.2 fun i _ => hne i))).mul
    (Ring.inverse_unit hdet.unit ▸ hdet.unit⁻¹.isUnit)

omit [Fintype n] in
/-- The columns of the identity are the standard basis vectors. -/
theorem euclideanCol_one (i : n) :
    euclideanCol (1 : Matrix n n 𝕜) i = EuclideanSpace.single i 1 := by
  ext j
  simp [euclideanCol, one_apply, PiLp.single_apply, eq_comm]

omit [Fintype n] in
/-- A vector lies in the span of the standard basis vectors indexed by `S` exactly when it
vanishes off `S`. -/
theorem mem_span_euclideanCol_one_iff [Finite n] (S : Set n) (v : EuclideanSpace 𝕜 n) :
    v ∈ span 𝕜 (euclideanCol (1 : Matrix n n 𝕜) '' S) ↔ ∀ i, i ∉ S → v i = 0 := by
  classical
  cases nonempty_fintype n
  constructor
  · intro hv i hi
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      rw [euclideanCol_one, PiLp.single_apply]
      exact ite_eq_right fun h : i = j => hi (h.symm ▸ hj)
    | zero => rfl
    | add y z _ _ hy hz => rw [PiLp.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [PiLp.smul_apply, hy, smul_zero]
  · intro hv
    have hsum : v = ∑ i ∈ Finset.univ.filter (· ∈ S), v i • euclideanCol (1 : Matrix n n 𝕜) i := by
      calc v = ∑ i, v i • euclideanCol (1 : Matrix n n 𝕜) i := by
            conv_lhs => rw [← (EuclideanSpace.basisFun n 𝕜).sum_repr v]
            simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
              euclideanCol_one]
        _ = _ := (Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => by
            rw [hv i (by simpa using hi), zero_smul]).symm
    rw [hsum]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩)

/-- The span of the columns of `A` indexed by `S` is the image under `A` of the coordinate
subspace indexed by `S`. -/
theorem span_euclideanCol_eq_map (A : Matrix n n 𝕜) (S : Set n) :
    span 𝕜 (euclideanCol A '' S) =
      (span 𝕜 (euclideanCol (1 : Matrix n n 𝕜) '' S)).map (toEuclideanLin A) := by
  rw [Submodule.map_span, Set.image_image]
  simp only [toEuclideanLin_euclideanCol_one]


end Ring

section Order

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-! ### Upper triangular matrices -/

omit [DecidableEq n] in
/-- The diagonal of a product of upper triangular matrices is the product of the diagonals. -/
theorem IsUpperTriangular.diag_mul {M N : Matrix n n 𝕜} (hM : M.IsUpperTriangular)
    (hN : N.IsUpperTriangular) (i : n) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun p _ hp => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · rw [hM hlt, zero_mul]
  · rw [hN hgt, mul_zero]

end Order

/-! ### Shifted QR steps for arbitrary factorizations

The canonical steps below (`Matrix.shiftedQrStep`, `Matrix.qrIterate`) fix one QR factorization,
the Gram–Schmidt one with a positive diagonal. The textbook algorithms compute *some* QR
factorization — by Givens rotations or Householder reflectors, with their own signs — so their
specifications are stated for any factorization: `Matrix.IsShiftedQrStep μ H H'` says that `H'` is
one QR step with shift `μ` for some factorization, and `Matrix.IsShiftedQrChain` records a chain of
steps together with its factors ([golub2013matrix] (10.5.4)). -/

section ShiftedStep

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- `H'` is obtained from `H` by **one QR step with shift `μ`, for some QR factorization**
([golub2013matrix] (7.3.1) with `μ = 0`, (7.4.1), (7.5.3)): `H - μ I = Q R` with `Q` unitary and
`R` upper triangular, and `H' = R Q + μ I`. -/
def IsShiftedQrStep (μ : 𝕜) (H H' : Matrix n n 𝕜) : Prop :=
  ∃ Q ∈ unitaryGroup n 𝕜, ∃ R : Matrix n n 𝕜, R.IsUpperTriangular ∧ H - μ • 1 = Q * R ∧
    H' = R * Q + μ • 1

/-- Every shifted QR step is a unitary similarity: `R Q + μ I = Qᴴ (Q R + μ I) Q` (the display
after [golub2013matrix] (7.5.3)). -/
theorem IsShiftedQrStep.eq_conj {μ : 𝕜} {H H' : Matrix n n 𝕜} (h : IsShiftedQrStep μ H H') :
    ∃ Q ∈ unitaryGroup n 𝕜, H' = star Q * H * Q := by
  obtain ⟨Q, hQ, R, -, hQR, rfl⟩ := h
  refine ⟨Q, hQ, ?_⟩
  have h1 : star Q * Q = 1 := (mem_unitaryGroup_iff').1 hQ
  have hR : R = star Q * (H - μ • 1) := by rw [hQR, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1,
    sub_add_cancel]

/-- A unitary upper triangular matrix is diagonal: its inverse `Uᴴ` is both upper and lower
triangular. -/
theorem IsUpperTriangular.eq_diagonal_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U.IsUpperTriangular) (hUu : U ∈ unitaryGroup n 𝕜) : U = diagonal fun i => U i i := by
  have hinv : U⁻¹ = star U := inv_eq_left_inv ((mem_unitaryGroup_iff').1 hUu)
  have hst : (star U).IsUpperTriangular := by rw [← hinv]; exact hU.inv
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [diagonal_apply_ne _ hij.ne]
    have := hst hij
    rwa [star_apply, star_eq_zero] at this
  · rw [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hij.ne', hU hij]

/-- For nonsingular `H - μ I` any two shifted QR steps are unitarily *diagonally* similar: the two
QR factorizations of `H - μ I` differ by a unimodular diagonal (`Q₁ᴴ Q₂ = R₁ R₂⁻¹` is unitary and
upper triangular, hence diagonal). -/
theorem IsShiftedQrStep.unique_of_isUnit {μ : 𝕜} {H H₁ H₂ : Matrix n n 𝕜}
    (h₁ : IsShiftedQrStep μ H H₁) (h₂ : IsShiftedQrStep μ H H₂) (hH : IsUnit (H - μ • 1).det) :
    ∃ d : n → 𝕜, (∀ i, ‖d i‖ = 1) ∧ H₂ = star (diagonal d) * H₁ * diagonal d := by
  obtain ⟨Q₁, hQ₁, R₁, hR₁, hM₁, rfl⟩ := h₁
  obtain ⟨Q₂, hQ₂, R₂, hR₂, hM₂, rfl⟩ := h₂
  have hdet₂ : IsUnit R₂.det := by
    rw [hM₂, det_mul] at hH
    exact isUnit_of_mul_isUnit_right hH
  set U := star Q₁ * Q₂ with hUdef
  have hU : U ∈ unitaryGroup n 𝕜 := mul_mem (Unitary.star_mem hQ₁) hQ₂
  have hUR₂ : U * R₂ = R₁ := by
    rw [hUdef, Matrix.mul_assoc, ← hM₂, hM₁, ← Matrix.mul_assoc, (mem_unitaryGroup_iff').1 hQ₁,
      Matrix.one_mul]
  have hUt : U.IsUpperTriangular := by
    rw [← mul_nonsing_inv_cancel_right R₂ U hdet₂, hUR₂]
    exact hR₁.mul hR₂.inv
  have hUd := hUt.eq_diagonal_of_mem_unitaryGroup hU
  have hUU : star U * U = 1 := (mem_unitaryGroup_iff').1 hU
  have hQ₂' : Q₂ = Q₁ * U := by
    rw [hUdef, ← Matrix.mul_assoc, (mem_unitaryGroup_iff).1 hQ₁, Matrix.one_mul]
  have hR₂' : R₂ = star U * R₁ := by rw [← hUR₂, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  refine ⟨fun i => U i i, fun i => ?_, ?_⟩
  · refine RCLike.norm_eq_one_of_star_mul_self_eq_one ?_
    have := congrFun (congrFun hUU i) i
    rw [hUd, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      diagonal_apply_eq, one_apply_eq] at this
    simpa using this
  · rw [← hUd, hR₂', hQ₂']
    calc star U * R₁ * (Q₁ * U) + μ • 1 = star U * R₁ * (Q₁ * U) + μ • (star U * U) := by
          rw [hUU]
      _ = star U * (R₁ * Q₁ + μ • 1) * U := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one, Matrix.mul_assoc]

/-- If `M = Q R` is nonsingular and upper Hessenberg with `R` upper triangular, then `Q` is upper
Hessenberg: `Q = M R⁻¹`, Hessenberg times triangular ([golub2013matrix] §7.4.2,
[quarteroni2000numerical] §5.6.3). -/
theorem IsUpperHessenberg.isUpperHessenberg_of_eq_mul {R : Type*} [CommRing R]
    {M Q T : Matrix n n R} (hM : M.IsUpperHessenberg) (hdet : IsUnit M.det)
    (hT : T.IsUpperTriangular) (hMQT : M = Q * T) : Q.IsUpperHessenberg := by
  have hTu : IsUnit T.det := by
    rw [hMQT, det_mul] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  rw [← mul_nonsing_inv_cancel_right T Q hTu, ← hMQT]
  exact hM.mul_isUpperTriangular hT.inv

/-- Hessenberg form survives a nonsingular shifted QR step, for any factorization
([golub2013matrix] §7.4.2): `Q = (H − μ I) R⁻¹` is Hessenberg, and so is `R Q + μ I`. -/
theorem IsShiftedQrStep.isUpperHessenberg {μ : 𝕜} {H H' : Matrix n n 𝕜}
    (h : IsShiftedQrStep μ H H') (hH : H.IsUpperHessenberg) (hdet : IsUnit (H - μ • 1).det) :
    H'.IsUpperHessenberg := by
  obtain ⟨Q, -, R, hR, hQR, rfl⟩ := h
  exact (hR.mul_isUpperHessenberg ((hH.sub_smul_one μ).isUpperHessenberg_of_eq_mul hdet hR
    hQR)).add_smul_one μ

/-- [golub2013matrix] **Theorem 7.5.1** (an exact shift deflates in one step): if `H` is unreduced
upper Hessenberg, `μ` an eigenvalue of `H` and `H'` a QR step of `H` with shift `μ`, then the last
row of `H'` is `μ e_Nᵀ`. In `H − μ I = Q R` the leading `N × N` block of `R` is nonsingular
(deleting the first row of `H − μ I` and the last column leaves the unreduced subdiagonal, and that
block is `Q(2:, :N) R(:N, :N)`); `det (H − μ I) = 0` then forces `r_{NN} = 0`, so the last row of
`R`, and hence of `R Q`, is zero. -/
theorem IsUnreducedUpperHessenberg.isShiftedQrStep_apply_last {N : ℕ}
    {H H' : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜} (hH : H.IsUnreducedUpperHessenberg) {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 H) (h : IsShiftedQrStep μ H H') (j : Fin (N + 1)) :
    H' (Fin.last N) j = if j = Fin.last N then μ else 0 := by
  obtain ⟨Q, hQ, R, hR, hM, rfl⟩ := h
  have hMu := hH.sub_smul_one μ
  have hdetM : (H - μ • 1).det = 0 := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not] at hμ
    rw [show H - μ • 1 = -(μ • 1 - H) by abel, det_neg, hμ, mul_zero]
  -- the leading block of `R` is nonsingular
  have hS : (H - μ • 1).submatrix Fin.succ Fin.castSucc =
      Q.submatrix Fin.succ Fin.castSucc * R.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    rw [hM, submatrix_apply, mul_apply, Fin.sum_univ_castSucc,
      show R (Fin.last N) b.castSucc = 0 from hR (Fin.castSucc_lt_last b), mul_zero, add_zero]
    rfl
  have hRdet : (R.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
    intro h0
    apply hMu.det_submatrix_succ_castSucc_ne_zero
    rw [hS, det_mul, h0, mul_zero]
  have hRt : (R.submatrix Fin.castSucc Fin.castSucc).IsUpperTriangular := fun a b hab =>
    hR (Fin.castSucc_lt_castSucc_iff.2 hab)
  rw [det_of_isUpperTriangular hRt, Finset.prod_ne_zero_iff] at hRdet
  -- hence `r_NN = 0`
  have hRNN : R (Fin.last N) (Fin.last N) = 0 := by
    have hQd : Q.det ≠ 0 := (isUnit_iff_ne_zero).1 ((isUnit_iff_isUnit_det Q).1
      (isUnit_of_mem_unitaryGroup hQ))
    rw [hM, det_mul, det_of_isUpperTriangular hR, Fin.prod_univ_castSucc] at hdetM
    rcases mul_eq_zero.1 hdetM with h0 | h0
    · exact absurd h0 hQd
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 (Finset.prod_ne_zero_iff.2 fun i hi => hRdet i hi)
    · exact h1
  have hrow : ∀ l, R (Fin.last N) l = 0 := by
    intro l
    rcases eq_or_ne l (Fin.last N) with rfl | hl
    · exact hRNN
    · exact hR (Fin.lt_last_iff_ne_last.2 hl)
  rw [add_apply, mul_apply, Finset.sum_eq_zero fun l _ => by rw [hrow l, zero_mul], zero_add,
    smul_apply, smul_eq_mul]
  by_cases hj : j = Fin.last N
  · subst hj
    simp
  · rw [one_apply_ne (Ne.symm hj), mul_zero]
    exact (ite_eq_right_iff.2 fun h => absurd h hj).symm

end ShiftedStep

section Chain

variable {𝕜 : Type*} [CommRing 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **A chain of shifted QR steps with explicit factors** ([golub2013matrix] (10.5.4), whose loop
`for i = 0:p` should read `i = 1:p`): `H i − μ_i I = V_i R_i` and `H (i + 1) = R_i V_i + μ_i I`
for `i < p`. Neither unitarity nor triangularity is part of the definition; the theorems add what
they use. -/
structure IsShiftedQrChain (H V R : ℕ → Matrix n n 𝕜) (μ : ℕ → 𝕜) (p : ℕ) : Prop where
  /-- The factorization of each shifted matrix. -/
  sub_eq : ∀ i < p, H i - μ i • 1 = V i * R i
  /-- The next matrix of the chain. -/
  succ_eq : ∀ i < p, H (i + 1) = R i * V i + μ i • 1

namespace IsShiftedQrChain

variable {H V R : ℕ → Matrix n n 𝕜} {μ : ℕ → 𝕜} {p : ℕ}

/-- A chain of length `p` restricts to every shorter length. -/
theorem mono (h : IsShiftedQrChain H V R μ p) {q : ℕ} (hq : q ≤ p) :
    IsShiftedQrChain H V R μ q :=
  ⟨fun i hi => h.sub_eq i (by omega), fun i hi => h.succ_eq i (by omega)⟩

/-- One link of the chain: `H i V i = V i H (i + 1)`. -/
theorem mul_eq_mul_succ (h : IsShiftedQrChain H V R μ p) {i : ℕ} (hi : i < p) :
    H i * V i = V i * H (i + 1) := by
  rw [h.succ_eq i hi, Matrix.mul_add, ← Matrix.mul_assoc, ← h.sub_eq i hi, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_add_cancel]

/-- `H₀ V_{<p} = V_{<p} H_p` with `V_{<p} = V_0 V_1 ⋯ V_{p-1}`. -/
theorem mul_prod (h : IsShiftedQrChain H V R μ p) :
    H 0 * ((List.range p).map V).prod = ((List.range p).map V).prod * H p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, ← Matrix.mul_assoc, ih (h.mono p.le_succ), Matrix.mul_assoc,
      h.mul_eq_mul_succ (lt_add_one p), ← Matrix.mul_assoc]

end IsShiftedQrChain

/-- **The product identity of a chain of shifted QR steps** ([golub2013matrix] (7.5.7), P7.5.5,
and Theorem 10.5.1): `(V_0 ⋯ V_{p-1}) (R_{p-1} ⋯ R_0) = ∏_{i<p} (H_0 − μ_i I)`. No unitarity or
triangularity is used: `V_{<p} (H_p − μ_p) = (H_0 − μ_p) V_{<p}` by `IsShiftedQrChain.mul_prod`, and
the factors `H_0 − μ_i I` commute. -/
theorem prod_mul_prod_reverse_eq_prod_sub_smul_one {H V R : ℕ → Matrix n n 𝕜} {μ : ℕ → 𝕜}
    {p : ℕ} (h : IsShiftedQrChain H V R μ p) :
    ((List.range p).map V).prod * ((List.range p).reverse.map R).prod =
      ((List.range p).map fun i => H 0 - μ i • 1).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hc := h.mono p.le_succ
    have hcomm : ∀ a b : 𝕜, Commute (H 0 - a • 1) (H 0 - b • 1) := fun a b =>
      ((Commute.refl _).sub_right ((Commute.one_right _).smul_right b)).sub_left
        ((Commute.one_left _).smul_left a)
    have hV : ((List.range p).map V).prod * (H p - μ p • 1) =
        (H 0 - μ p • 1) * ((List.range p).map V).prod := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hc.mul_prod, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul]
    simp only [List.range_succ, List.reverse_append, List.map_append, List.prod_append,
      List.reverse_singleton, List.singleton_append, List.map_cons, List.prod_cons, List.map_nil,
      List.prod_nil, mul_one]
    calc ((List.range p).map V).prod * V p * (R p * ((List.range p).reverse.map R).prod)
        = ((List.range p).map V).prod * (H p - μ p • 1) *
            ((List.range p).reverse.map R).prod := by
          rw [h.sub_eq p (lt_add_one p)]
          simp only [Matrix.mul_assoc]
      _ = (H 0 - μ p • 1) * ((List.range p).map fun i => H 0 - μ i • 1).prod := by
          rw [hV, Matrix.mul_assoc, ih hc]
      _ = ((List.range p).map fun i => H 0 - μ i • 1).prod * (H 0 - μ p • 1) :=
          (Commute.list_prod_right _ _ fun y hy => by
            obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
            exact hcomm _ _).eq

namespace IsShiftedQrChain

variable {H V R : ℕ → Matrix n n 𝕜} {μ : ℕ → 𝕜} {p : ℕ}

/-- [golub2013matrix] (10.5.6): with unitary `V_i`, the accumulated `V_{<p}` is unitary and
`H_p = V_{<p}ᴴ H_0 V_{<p}`. -/
theorem conjTranspose_mul_mul [StarRing 𝕜] (h : IsShiftedQrChain H V R μ p)
    (hV : ∀ i < p, V i ∈ unitaryGroup n 𝕜) :
    ((List.range p).map V).prod ∈ unitaryGroup n 𝕜 ∧
      H p = star ((List.range p).map V).prod * H 0 * ((List.range p).map V).prod := by
  have hmem : ((List.range p).map V).prod ∈ unitaryGroup n 𝕜 := by
    refine Submonoid.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hV i (List.mem_range.1 hi)
  refine ⟨hmem, ?_⟩
  rw [Matrix.mul_assoc, h.mul_prod, ← Matrix.mul_assoc, (mem_unitaryGroup_iff').1 hmem,
    Matrix.one_mul]

/-- Hessenberg form along a chain ([golub2013matrix] §10.5.3, "each `H^{(i)}` is upper
Hessenberg"): if `H_0` is upper Hessenberg and every `R_i` upper triangular and `V_i` upper
Hessenberg, then so is every `H_i`, `i ≤ p`. -/
theorem isUpperHessenberg [LinearOrder n] (h : IsShiftedQrChain H V R μ p)
    (h0 : (H 0).IsUpperHessenberg) (hR : ∀ i < p, (R i).IsUpperTriangular)
    (hV : ∀ i < p, (V i).IsUpperHessenberg) : ∀ i ≤ p, (H i).IsUpperHessenberg := by
  intro i hi
  induction i with
  | zero => exact h0
  | succ i ih =>
    rw [h.succ_eq i (by omega)]
    exact ((hR i (by omega)).mul_isUpperHessenberg (hV i (by omega))).add_smul_one _

/-- With upper Hessenberg `V_i`, the accumulated `V_{<p}` has lower bandwidth `p`
([golub2013matrix] §10.5.3, "`V(m, 1:m−p−1) = 0`"). -/
theorem hasLowerBandwidth_prod [LinearOrder n] (hV : ∀ i < p, (V i).IsUpperHessenberg) :
    (((List.range p).map V).prod).HasLowerBandwidth p := by
  induction p with
  | zero => exact hasLowerBandwidth_zero_iff.2 (by simpa using blockTriangular_one)
  | succ p ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
    exact (ih fun i hi => hV i (by omega)).mul
      (isUpperHessenberg_iff_hasLowerBandwidth_one.1 (hV p (lt_add_one p)))

/-- The first column of the accumulated factor ([golub2013matrix] §10.5.3, "`V(:,1) = p(H_c) e₁`
with `c = 1/R(1,1)`"), without dividing: with upper triangular `R_i`,
`(∏_{i<p} (H_0 − μ_i I)) e₀ = (R_{<p})₀₀ • V_{<p} e₀` where `R_{<p} = R_{p-1} ⋯ R_0`. -/
theorem mulVec_first [LinearOrder n] [OrderBot n] (h : IsShiftedQrChain H V R μ p)
    (hR : ∀ i < p, (R i).IsUpperTriangular) :
    ((List.range p).map fun i => H 0 - μ i • 1).prod *ᵥ Pi.single ⊥ 1 =
      ((List.range p).reverse.map R).prod ⊥ ⊥ •
        (((List.range p).map V).prod *ᵥ Pi.single ⊥ 1) := by
  have hlist : ∀ l : List ℕ, (∀ i ∈ l, i < p) → ((l.map R).prod).IsUpperTriangular := by
    intro l hl
    induction l with
    | nil => simpa using blockTriangular_one
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons]
      exact (hR a (hl a List.mem_cons_self)).mul (ih fun i hi => hl i (List.mem_cons_of_mem a hi))
  have htri := hlist (List.range p).reverse fun i hi => List.mem_range.1 (List.mem_reverse.1 hi)
  rw [← prod_mul_prod_reverse_eq_prod_sub_smul_one h, ← mulVec_mulVec, ← mulVec_smul]
  congr 1
  ext i
  rw [mulVec_single_one, Pi.smul_apply, col_apply, Pi.single_apply, smul_eq_mul]
  split_ifs with hi
  · rw [hi, mul_one]
  · rw [mul_zero, htri (bot_lt_iff_ne_bot.2 hi)]

end IsShiftedQrChain

/-- **Existence of Givens chains for arbitrary shifts** ([golub2013matrix] (10.5.4) with "Givens
QR"): for upper Hessenberg real `H` and any shifts `μ`, there is a chain from `H` whose factors
come from the Givens QR factorization of `Matrix.hessenbergGivensQR`: every `V_i` orthogonal and
upper Hessenberg, every `R_i` upper triangular. No nonsingularity is needed — exact shifts are
allowed. -/
theorem exists_isShiftedQrChain {m : ℕ} {H : Matrix (Fin m) (Fin m) ℝ} (hH : H.IsUpperHessenberg)
    (μ : ℕ → ℝ) :
    ∃ Hs V R : ℕ → Matrix (Fin m) (Fin m) ℝ, Hs 0 = H ∧
      (∀ p, IsShiftedQrChain Hs V R μ p) ∧
      ∀ i, V i ∈ orthogonalGroup (Fin m) ℝ ∧ (V i).IsUpperHessenberg ∧
        (R i).IsUpperTriangular ∧ (Hs i).IsUpperHessenberg := by
  let Hs : ℕ → Matrix (Fin m) (Fin m) ℝ := fun i => Nat.rec (motive := fun _ =>
    Matrix (Fin m) (Fin m) ℝ) H (fun i M =>
    (hessenbergGivensQR (M - μ i • 1)).2 * (hessenbergGivensQR (M - μ i • 1)).1 + μ i • 1) i
  have hHs : ∀ i, (Hs i).IsUpperHessenberg := by
    intro i
    induction i with
    | zero => exact hH
    | succ i ih =>
      obtain ⟨-, hR, -, hQ⟩ := hessenbergGivensQR_spec (ih.sub_smul_one (μ i))
      exact (hR.mul_isUpperHessenberg hQ).add_smul_one _
  refine ⟨Hs, fun i => (hessenbergGivensQR (Hs i - μ i • 1)).1,
    fun i => (hessenbergGivensQR (Hs i - μ i • 1)).2, rfl, fun p => ⟨fun i _ => ?_, fun i _ => rfl⟩,
    fun i => ?_⟩
  · exact (hessenbergGivensQR_spec ((hHs i).sub_smul_one (μ i))).2.2.1
  · obtain ⟨hQ, hR, -, hQH⟩ := hessenbergGivensQR_spec ((hHs i).sub_smul_one (μ i))
    exact ⟨hQ, hQH, hR, hHs i⟩

end Chain

/-- Each link of a chain with unitary `V_i` and upper triangular `R_i` is a shifted QR step. -/
theorem IsShiftedQrChain.isShiftedQrStep {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] [LinearOrder n] {H V R : ℕ → Matrix n n 𝕜} {μ : ℕ → 𝕜} {p : ℕ}
    (h : IsShiftedQrChain H V R μ p) (hV : ∀ i < p, V i ∈ unitaryGroup n 𝕜)
    (hR : ∀ i < p, (R i).IsUpperTriangular) {i : ℕ} (hi : i < p) :
    IsShiftedQrStep (μ i) (H i) (H (i + 1)) :=
  ⟨V i, hV i hi, R i, hR i hi, h.sub_eq i hi, h.succ_eq i hi⟩

section GramSchmidt

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
  [LocallyFiniteOrderBot n]

/-! ### The QR decomposition from Gram–Schmidt -/

/-- The orthonormal basis of `EuclideanSpace 𝕜 n` produced by Gram–Schmidt from the columns of `A`:
the columns of the unitary factor of the QR decomposition. -/
noncomputable def qrBasis (A : Matrix n n 𝕜) : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  gramSchmidtOrthonormalBasis finrank_euclideanSpace (euclideanCol A)

/-- The **unitary factor** of the QR decomposition of `A`: the matrix whose columns are the
Gram–Schmidt orthonormalization of the columns of `A`. -/
noncomputable def qrQ (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (qrBasis A).toBasis

/-- The **upper triangular factor** of the QR decomposition of `A`: the matrix of the columns of `A`
in the orthonormal basis `Matrix.qrBasis A`. -/
noncomputable def qrR (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (qrBasis A).toBasis.toMatrix (euclideanCol A)

omit [DecidableEq n] in
/-- **The QR decomposition**: `A = Q R`. -/
theorem qrQ_mul_qrR (A : Matrix n n 𝕜) : qrQ A * qrR A = A := by
  rw [qrQ, qrR, Module.Basis.toMatrix_mul_toMatrix]
  ext i j
  simp [Module.Basis.toMatrix]

/-- The unitary factor of the QR decomposition is unitary. -/
theorem qrQ_mem_unitaryGroup (A : Matrix n n 𝕜) : qrQ A ∈ Matrix.unitaryGroup n 𝕜 :=
  (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary (qrBasis A)

omit [DecidableEq n] in
/-- The triangular factor of the QR decomposition is upper triangular. -/
theorem isUpperTriangular_qrR (A : Matrix n n 𝕜) : (qrR A).IsUpperTriangular :=
  gramSchmidtOrthonormalBasis_inv_isUpperTriangular _ _

omit [DecidableEq n] in
/-- The columns of the unitary factor are the Gram–Schmidt basis. -/
theorem euclideanCol_qrQ (A : Matrix n n 𝕜) (j : n) : euclideanCol (qrQ A) j = qrBasis A j := by
  ext i
  simp [euclideanCol, qrQ, Module.Basis.toMatrix]

omit [DecidableEq n] in
/-- The entries of the triangular factor are the coordinates of the columns of `A` in the
Gram–Schmidt basis. -/
theorem qrR_apply (A : Matrix n n 𝕜) (i j : n) :
    qrR A i j = inner 𝕜 (qrBasis A i) (euclideanCol A j) := by
  simp [qrR, Module.Basis.toMatrix, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]

/-- **The diagonal of the triangular factor is positive** at a nonsingular matrix: it is the norm of
the corresponding unnormalized Gram–Schmidt vector.  This is the normalization that makes the QR
decomposition unique. -/
theorem qrR_diag_pos {A : Matrix n n 𝕜} (hA : IsUnit A.det) (j : n) : 0 < qrR A j j := by
  have hli : LinearIndependent 𝕜 (euclideanCol A) := linearIndependent_euclideanCol hA
  have hg : gramSchmidt 𝕜 (euclideanCol A) j ≠ 0 := gramSchmidt_ne_zero j hli
  have hne : gramSchmidtNormed 𝕜 (euclideanCol A) j ≠ 0 := by
    rw [← norm_ne_zero_iff, gramSchmidtNormed_unit_length j hli]
    norm_num
  have hbasis : qrBasis A j = gramSchmidtNormed 𝕜 (euclideanCol A) j :=
    gramSchmidtOrthonormalBasis_apply _ hne
  rw [qrR_apply, hbasis, inner_gramSchmidtNormed_self]
  exact RCLike.pos_iff.2 ⟨by simpa using norm_pos_iff.2 hg, by simp⟩

/-! ### Uniqueness of the QR decomposition -/

/-- **Uniqueness of the QR decomposition**, in the form the QR algorithm needs: if `M = U T` with
`U` unitary and `T` upper triangular with a positive diagonal, then the columns of `U` are the
Gram–Schmidt orthonormalization of the columns of `M`.

This is what identifies the accumulated unitary factor of the QR algorithm with the orthogonal
iteration of the canonical flag, and it is where the normalization of `Matrix.qrR` earns its
keep. -/
theorem euclideanCol_eq_gramSchmidtNormed_of_eq_mul {M U T : Matrix n n 𝕜} (hU : Uᴴ * U = 1)
    (hT : T.IsUpperTriangular) (hTpos : ∀ j, 0 < T j j) (hM : M = U * T) (j : n) :
    euclideanCol U j = gramSchmidtNormed 𝕜 (euclideanCol M) j := by
  have hUon : Orthonormal 𝕜 (euclideanCol U) := orthonormal_euclideanCol hU
  have hite := orthonormal_iff_ite.1 hUon
  have hcol : ∀ p, euclideanCol M p = ∑ q, T q p • euclideanCol U q := by
    intro p; rw [hM, euclideanCol_mul]
  have hMle : ∀ p : n, euclideanCol M p ∈ span 𝕜 (euclideanCol U '' Set.Iic p) := by
    intro p
    rw [hcol p]
    refine Submodule.sum_mem _ fun q _ => ?_
    rcases le_or_gt q p with hqp | hqp
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hqp, rfl⟩)
    · rw [hT hqp, zero_smul]
      exact Submodule.zero_mem _
  have hUle : ∀ p : n, euclideanCol U p ∈ span 𝕜 (euclideanCol M '' Set.Iic p) := by
    intro p
    induction p using WellFoundedLT.induction with
    | _ p ih =>
      have hprev : ∀ q < p, euclideanCol U q ∈ span 𝕜 (euclideanCol M '' Set.Iic p) := fun q hq =>
        span_mono (Set.image_mono fun x hx => le_trans hx hq.le) (ih q hq)
      have hsplit : T p p • euclideanCol U p
          = euclideanCol M p - ∑ q ∈ Finset.univ.erase p, T q p • euclideanCol U q := by
        rw [hcol p, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        abel
      have hmem : T p p • euclideanCol U p ∈ span 𝕜 (euclideanCol M '' Set.Iic p) := by
        rw [hsplit]
        refine Submodule.sub_mem _ (Submodule.subset_span ⟨p, le_rfl, rfl⟩)
          (Submodule.sum_mem _ fun q hq => ?_)
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hq) with hqp | hqp
        · exact Submodule.smul_mem _ _ (hprev q hqp)
        · rw [hT hqp, zero_smul]
          exact Submodule.zero_mem _
      have hscaled := Submodule.smul_mem _ (T p p)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (hTpos p).ne', one_smul] at hscaled
  refine eq_gramSchmidtNormed_of_re_inner_pos hUon (fun p => ?_) j ?_
  · refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
    · rintro _ ⟨q, hq, rfl⟩
      exact span_mono (Set.image_mono fun x hx => le_trans hx hq) (hUle q)
    · rintro _ ⟨q, hq, rfl⟩
      exact span_mono (Set.image_mono fun x hx => le_trans hx hq) (hMle q)
  · rw [hcol j, inner_sum]
    have hsum : (∑ q, (inner 𝕜 (euclideanCol U j) (T q j • euclideanCol U q) : 𝕜)) = T j j := by
      rw [Finset.sum_eq_single j]
      · rw [inner_smul_right, hite j j]
        simp
      · intro q _ hq
        rw [inner_smul_right, hite j q]
        simp [Ne.symm hq]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [hsum]
    exact hTpos j

/-! ### The QR algorithm -/

/-- **The QR algorithm**: `A_0 = A`, and `A_{k+1} = R_k Q_k` for the QR decomposition
`A_k = Q_k R_k`. -/
noncomputable def qrIterate (A : Matrix n n 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => A
  | k + 1 => qrR (qrIterate A k) * qrQ (qrIterate A k)

/-- The **accumulated unitary factor** `Q̃_k = Q_0 Q_1 ⋯ Q_{k-1}` of the QR algorithm. -/
noncomputable def qrAccum (A : Matrix n n 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => 1
  | k + 1 => qrAccum A k * qrQ (qrIterate A k)

/-- The **accumulated triangular factor** `R̃_k = R_{k-1} ⋯ R_1 R_0` of the QR algorithm. -/
noncomputable def qrTriangle (A : Matrix n n 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => 1
  | k + 1 => qrR (qrIterate A k) * qrTriangle A k

omit [DecidableEq n] in
@[simp]
theorem qrIterate_zero (A : Matrix n n 𝕜) : qrIterate A 0 = A := rfl

omit [DecidableEq n] in
/-- One QR step: `A_{k+1} = R_k Q_k`, by definition. -/
theorem qrIterate_succ (A : Matrix n n 𝕜) (k : ℕ) :
    qrIterate A (k + 1) = qrR (qrIterate A k) * qrQ (qrIterate A k) := rfl

@[simp]
theorem qrAccum_zero (A : Matrix n n 𝕜) : qrAccum A 0 = 1 := rfl

theorem qrAccum_succ (A : Matrix n n 𝕜) (k : ℕ) :
    qrAccum A (k + 1) = qrAccum A k * qrQ (qrIterate A k) := rfl

@[simp]
theorem qrTriangle_zero (A : Matrix n n 𝕜) : qrTriangle A 0 = 1 := rfl

theorem qrTriangle_succ (A : Matrix n n 𝕜) (k : ℕ) :
    qrTriangle A (k + 1) = qrR (qrIterate A k) * qrTriangle A k := rfl

/-- Each QR iterate is an unshifted QR step (`Matrix.IsShiftedQrStep` with `μ = 0`) of the
previous one. -/
theorem isShiftedQrStep_qrIterate (A : Matrix n n 𝕜) (k : ℕ) :
    IsShiftedQrStep 0 (qrIterate A k) (qrIterate A (k + 1)) :=
  ⟨qrQ _, qrQ_mem_unitaryGroup _, qrR _, isUpperTriangular_qrR _,
    by rw [zero_smul, sub_zero, qrQ_mul_qrR], by rw [zero_smul, add_zero, qrIterate_succ]⟩

/-- The QR iterates with their factors form a chain of unshifted QR steps. -/
theorem isShiftedQrChain_qrIterate (A : Matrix n n 𝕜) (p : ℕ) :
    IsShiftedQrChain (qrIterate A) (fun k => qrQ (qrIterate A k)) (fun k => qrR (qrIterate A k))
      (fun _ => 0) p :=
  ⟨fun _ _ => by rw [zero_smul, sub_zero, qrQ_mul_qrR], fun _ _ => by rw [zero_smul, add_zero]; rfl⟩

/-- The accumulated unitary factor is the product `Q_0 Q_1 ⋯ Q_{k-1}` of the chain. -/
theorem qrAccum_eq_prod (A : Matrix n n 𝕜) (k : ℕ) :
    qrAccum A k = ((List.range k).map fun i => qrQ (qrIterate A i)).prod := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qrAccum_succ, ih, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]

/-- The accumulated triangular factor is the product `R_{k-1} ⋯ R_0` of the chain. -/
theorem qrTriangle_eq_prod (A : Matrix n n 𝕜) (k : ℕ) :
    qrTriangle A k = ((List.range k).reverse.map fun i => qrR (qrIterate A i)).prod := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qrTriangle_succ, ih, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.prod_cons]

/-- The accumulated factor of the QR algorithm is unitary. -/
theorem qrAccum_mem_unitaryGroup (A : Matrix n n 𝕜) (k : ℕ) :
    qrAccum A k ∈ Matrix.unitaryGroup n 𝕜 := by
  induction k with
  | zero => rw [qrAccum_zero]; exact one_mem _
  | succ k ih => exact mul_mem ih (qrQ_mem_unitaryGroup _)

theorem conjTranspose_mul_qrAccum (A : Matrix n n 𝕜) (k : ℕ) :
    (qrAccum A k)ᴴ * qrAccum A k = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff'.1 (qrAccum_mem_unitaryGroup A k)

theorem qrAccum_mul_conjTranspose (A : Matrix n n 𝕜) (k : ℕ) :
    qrAccum A k * (qrAccum A k)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff.1 (qrAccum_mem_unitaryGroup A k)

theorem conjTranspose_qrQ_mul_self (A : Matrix n n 𝕜) : (qrQ A)ᴴ * qrQ A = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff'.1 (qrQ_mem_unitaryGroup A)

/-- An upper triangular matrix with a positive diagonal is its own triangular factor, with the
identity as unitary factor: `qrQ A = 1` and `qrR A = A`, by the uniqueness of the QR
factorization (`Matrix.qr_unique`). -/
theorem qrQ_eq_one_of_isUpperTriangular {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsUpperTriangular) (hd : ∀ j, 0 < A j j) : qrQ A = 1 ∧ qrR A = A := by
  have hdet : IsUnit A.det := by
    rw [det_of_isUpperTriangular hA]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.2 fun j _ => (hd j).ne')
  exact qr_unique (qrQ_mul_qrR A).symm (Matrix.one_mul A).symm (conjTranspose_qrQ_mul_self A)
    (by simp) (isUpperTriangular_qrR A) hA (qrR_diag_pos hdet) hd

set_option linter.unusedDecidableInType false in
/-- The triangular factor read off the QR decomposition: `R = Qᴴ A`. -/
theorem qrR_eq (A : Matrix n n 𝕜) : qrR A = (qrQ A)ᴴ * A := by
  have h : (qrQ A)ᴴ * A = (qrQ A)ᴴ * (qrQ A * qrR A) := by rw [qrQ_mul_qrR]
  rw [h, ← Matrix.mul_assoc, conjTranspose_qrQ_mul_self, Matrix.one_mul]

/-- **[kress1998numerical], (7.26)**: the `k`-th QR iterate is `A` conjugated by the accumulated
unitary factor.  This is why the QR algorithm computes eigenvalues: every iterate is similar to
`A`. -/
theorem qrIterate_eq_conj_qrAccum (A : Matrix n n 𝕜) (k : ℕ) :
    qrIterate A k = (qrAccum A k)ᴴ * A * qrAccum A k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [qrIterate_succ, qrR_eq, qrAccum_succ, Matrix.conjTranspose_mul]
    generalize qrQ (qrIterate A k) = Q
    rw [ih]
    simp only [Matrix.mul_assoc]

/-- **[kress1998numerical], (7.25)**: `A^k = Q̃_k R̃_k`.  The accumulated unitary factor of the QR
algorithm therefore orthonormalizes the columns of `A^k`, which is what identifies it with
orthogonal iteration. -/
theorem pow_eq_qrAccum_mul_qrTriangle (A : Matrix n n 𝕜) (k : ℕ) :
    A ^ k = qrAccum A k * qrTriangle A k := by
  rw [qrAccum_eq_prod, qrTriangle_eq_prod,
    prod_mul_prod_reverse_eq_prod_sub_smul_one (isShiftedQrChain_qrIterate A k)]
  simp [List.map_const', List.prod_replicate]

/-- The accumulated triangular factor is upper triangular. -/
theorem isUpperTriangular_qrTriangle (A : Matrix n n 𝕜) (k : ℕ) :
    (qrTriangle A k).IsUpperTriangular := by
  induction k with
  | zero =>
    intro i j hij
    rw [qrTriangle_zero]
    exact Matrix.one_apply_ne hij.ne'
  | succ k ih => exact (isUpperTriangular_qrR _).mul ih

/-- Every QR iterate of a nonsingular matrix is nonsingular: it is a unitary conjugate of `A`. -/
theorem isUnit_det_qrIterate {A : Matrix n n 𝕜} (hA : IsUnit A.det) (k : ℕ) :
    IsUnit (qrIterate A k).det := by
  have hunit : IsUnit ((qrAccum A k)ᴴ.det * (qrAccum A k).det) := by
    rw [← Matrix.det_mul, conjTranspose_mul_qrAccum, Matrix.det_one]
    exact isUnit_one
  rw [qrIterate_eq_conj_qrAccum, Matrix.det_mul, Matrix.det_mul, mul_right_comm]
  exact (isUnit_of_mul_isUnit_left hunit |>.mul (isUnit_of_mul_isUnit_right hunit)).mul hA

private theorem mul_pos_of_pos {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [RCLike.pos_iff] at ha hb ⊢
  refine ⟨?_, ?_⟩
  · rw [RCLike.mul_re, ha.2, hb.2]
    have := mul_pos ha.1 hb.1
    nlinarith
  · rw [RCLike.mul_im, ha.2, hb.2]
    ring

/-- **The accumulated triangular factor has a positive diagonal** at a nonsingular matrix: it is a
product of the triangular factors `R_j`, each of which has one by `Matrix.qrR_diag_pos`. -/
theorem qrTriangle_diag_pos {A : Matrix n n 𝕜} (hA : IsUnit A.det) (k : ℕ) (j : n) :
    0 < qrTriangle A k j j := by
  induction k with
  | zero =>
    rw [qrTriangle_zero, Matrix.one_apply_eq]
    exact zero_lt_one
  | succ k ih =>
    rw [qrTriangle_succ,
      IsUpperTriangular.diag_mul (isUpperTriangular_qrR _) (isUpperTriangular_qrTriangle A k)]
    exact mul_pos_of_pos (qrR_diag_pos (isUnit_det_qrIterate hA k) j) ih

/-- **The accumulated unitary factor of the QR algorithm is the orthogonal iteration of the
canonical flag** ([kress1998numerical], §7.4): the columns of `Q̃_k` are the Gram–Schmidt
orthonormalization of the columns of `A^k`, which is `Krylov.orthogonalIterate` started at the
canonical basis.

The QR algorithm was defined without reference to any subspace; this is what makes
`Krylov.span_orthogonalIterate` apply to it, so that convergence of the iterated flag becomes
convergence of the QR iterates. -/
theorem qrAccum_eq_orthogonalIterate {A : Matrix n n 𝕜} (hA : IsUnit A.det) (k : ℕ) :
    euclideanCol (qrAccum A k) =
      Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) k := by
  have hcolpow : (fun i => ((toEuclideanLin A) ^ k) (euclideanCol 1 i)) = euclideanCol (A ^ k) := by
    funext i
    rw [← toEuclideanLin_pow, toEuclideanLin_euclideanCol_one]
  funext j
  rw [Krylov.orthogonalIterate, hcolpow]
  exact euclideanCol_eq_gramSchmidtNormed_of_eq_mul (conjTranspose_mul_qrAccum A k)
    (isUpperTriangular_qrTriangle A k) (qrTriangle_diag_pos hA k)
    (pow_eq_qrAccum_mul_qrTriangle A k) j

/-- **[kress1998numerical], (7.25)–(7.26): the QR algorithm is orthogonal iteration on the canonical
flag.**  For a nonsingular `A`, the `k`-th QR iterate is `A` conjugated by the matrix whose columns
are the orthogonal iterates of the canonical basis.

The matrix `Q` is passed as data with its columns prescribed, rather than constructed: it is
determined, `Matrix.euclideanCol_injective` being injective, and this form lets a consumer supply
whatever spelling of the orthogonal iteration it has. -/
theorem qrIterate_eq_conj_orthogonalIterate {A Q : Matrix n n 𝕜} (hA : IsUnit A.det) (k : ℕ)
    (hQ : euclideanCol Q = Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) k) :
    qrIterate A k = Qᴴ * A * Q := by
  have hQeq : Q = qrAccum A k :=
    euclideanCol_injective (hQ.trans (qrAccum_eq_orthogonalIterate hA k).symm)
  rw [hQeq, qrIterate_eq_conj_qrAccum]

/-! ### Convergence of the QR algorithm -/

omit [LinearOrder n] [LocallyFiniteOrderBot n] in
set_option linter.unusedDecidableInType false in
/-- The entries of a conjugate `Uᴴ M U` are the inner products of the columns of `U` against `M`
applied to the columns of `U`.  This is what turns the QR iterates into the compressions of `A` on
the orthogonal iterates. -/
theorem conjTranspose_mul_mul_apply (U M : Matrix n n 𝕜) (j k : n) :
    (Uᴴ * M * U) j k = inner 𝕜 (euclideanCol U j) (toEuclideanLin M (euclideanCol U k)) := by
  have hcol : ∀ i, (toEuclideanLin M (euclideanCol U k)).ofLp i = ∑ r, M i r * U r k := by
    intro i
    simp [euclideanCol, toLpLin_apply, mulVec, dotProduct]
  simp only [PiLp.inner_apply, RCLike.inner_apply, euclideanCol_apply, hcol, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => by
    rw [RCLike.star_def]; ring

/-- **The QR iterates are the compressions of `A` on the orthogonal iterates of the canonical
flag**: entrywise, `(A_ν)_{jk} = ⟪q_{jν}, A q_{kν}⟫`. -/
theorem qrIterate_apply {A : Matrix n n 𝕜} (hA : IsUnit A.det) (ν : ℕ) (j k : n) :
    qrIterate A ν j k =
      inner 𝕜 (Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν j)
        (toEuclideanLin A (Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν k)) := by
  rw [qrIterate_eq_conj_qrAccum, conjTranspose_mul_mul_apply, qrAccum_eq_orthogonalIterate hA]

/-- The orthogonal iterates of the canonical flag start at the canonical basis. -/
theorem orthogonalIterate_euclideanCol_one_zero (A : Matrix n n 𝕜) :
    Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol (1 : Matrix n n 𝕜)) 0 =
      euclideanCol 1 :=
  Krylov.orthogonalIterate_zero (orthonormal_euclideanCol (by simp))

/-- The orthogonal iterates of the canonical flag are orthonormal: they are the columns of
`Matrix.qrAccum`. -/
theorem orthonormal_orthogonalIterate_euclideanCol_one {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    (ν : ℕ) : Orthonormal 𝕜 (Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν) := by
  rw [← qrAccum_eq_orthogonalIterate hA ν]
  exact orthonormal_euclideanCol (conjTranspose_mul_qrAccum A ν)

/-- **[kress1998numerical], Theorem 7.20: the QR algorithm converges to triangular form.**  For a
diagonalizable `A` whose eigenvalues have pairwise distinct moduli, ordered strictly decreasingly
along the index type, and whose canonical flag is in general position with respect to the invariant
complements (his (7.24)), the QR iterates satisfy `(A_ν)_{jk} → 0` below the diagonal and
`(A_ν)_{jj} → λ_j` on it.

It is [kress1998numerical]'s Theorem 7.19 read through `Matrix.qrIterate_apply`: the QR algorithm is
orthogonal iteration on the canonical flag, so its iterates are the compressions `Q_νᴴ A Q_ν` that
theorem is about.  The nonsingularity of `A` is implied by the hypotheses — the eigenvalues are all
nonzero and there are `n` independent eigenvectors — but it is assumed rather than derived, because
it is what `Matrix.qrAccum_eq_orthogonalIterate` needs and deriving it would take the determinant
through the eigenbasis. -/
theorem tendsto_qrIterate {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    {x : n → EuclideanSpace 𝕜 n} {l : n → 𝕜} (hx : LinearIndependent 𝕜 x)
    (hxtop : Submodule.span 𝕜 (Set.range x) = ⊤)
    (heig : ∀ j, toEuclideanLin A (x j) = l j • x j) (hl0 : ∀ j, l j ≠ 0)
    (hsep : ∀ j k : n, j < k → ‖l k‖ < ‖l j‖)
    (hgen : ∀ J : Set n, IsLowerSet J →
      Disjoint (Submodule.span 𝕜 (euclideanCol (1 : Matrix n n 𝕜) '' J))
        (Submodule.span 𝕜 (x '' Jᶜ))) :
    (∀ j k : n, k < j → Filter.Tendsto (fun ν => qrIterate A ν j k) Filter.atTop (nhds 0)) ∧
      ∀ j : n, Filter.Tendsto (fun ν => qrIterate A ν j j) Filter.atTop (nhds (l j)) := by
  set q : ℕ → n → EuclideanSpace 𝕜 n :=
    fun ν => Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν with hqdef
  have hq0 : q 0 = euclideanCol (1 : Matrix n n 𝕜) := orthogonalIterate_euclideanCol_one_zero A
  have hqon : ∀ ν, Orthonormal 𝕜 (q ν) := orthonormal_orthogonalIterate_euclideanCol_one hA
  have hspan : ∀ (ν : ℕ) (J : Set n), IsLowerSet J →
      Submodule.span 𝕜 (q ν '' J) =
        Krylov.subspaceIterate (toEuclideanLin A) (Submodule.span 𝕜 (q 0 '' J)) ν := by
    intro ν J hJ
    rw [hq0]
    exact Krylov.span_orthogonalIterate_of_isLowerSet _ _ _ hJ
  obtain ⟨h1, h2⟩ := Krylov.tendsto_orthogonalIterate hx hxtop heig hl0 hsep hqon hspan
    (by rw [hq0]; exact hgen)
  exact ⟨fun j k hkj => by simpa only [qrIterate_apply hA] using h1 j k hkj,
    fun j => by simpa only [qrIterate_apply hA] using h2 j⟩

/-! ### The rate of convergence, and structure preserved by the iteration -/

/-- **The rate of convergence of the QR iteration**, [quarteroni2000numerical] (5.37) with the
usual loss of this library's subspace-iteration estimates: under the hypotheses of
`Matrix.tendsto_qrIterate`, a strictly subdiagonal entry `(j, k)`, `k < j`, of the `ν`-th iterate is
`O((r / |λ_k|)^ν)` for every `r` above the moduli of the eigenvalues after the `k`-th. For
`j = k + 1` and `r` close to `|λ_{k+1}|` this is the book's
`|t_{i,i-1}^{(k)}| = O(|λ_i/λ_{i-1}|^k)`.

The entry is `⟪q_j^ν, A q_k^ν⟫` (`Matrix.qrIterate_apply`) with `q_k^ν` in the `ν`-th iterate of
the span of the first `k + 1` canonical vectors and `q_j^ν` orthogonal to it, so
`Krylov.norm_inner_le_of_gap` bounds it by the gap between that iterate and the invariant subspace
of the first `k + 1` eigenvectors, and `Krylov.exists_gap_subspaceIterate_span_image_le` bounds the
gap. -/
theorem exists_abs_qrIterate_apply_le {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    {x : n → EuclideanSpace 𝕜 n} {l : n → 𝕜} (hx : LinearIndependent 𝕜 x)
    (hxtop : Submodule.span 𝕜 (Set.range x) = ⊤)
    (heig : ∀ j, toEuclideanLin A (x j) = l j • x j)
    (hsep : ∀ j k : n, j < k → ‖l k‖ < ‖l j‖)
    (hgen : ∀ J : Set n, IsLowerSet J →
      Disjoint (Submodule.span 𝕜 (euclideanCol (1 : Matrix n n 𝕜) '' J))
        (Submodule.span 𝕜 (x '' Jᶜ)))
    {j k : n} (hkj : k < j) {r : ℝ} (hr0 : 0 ≤ r) (hr : ∀ j', k < j' → ‖l j'‖ ≤ r)
    (hrk : r < ‖l k‖) :
    ∃ C : ℝ, ∀ ν, ‖qrIterate A ν j k‖ ≤ C * (r / ‖l k‖) ^ ν := by
  have hqon : ∀ ν, Orthonormal 𝕜 (Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν) :=
    orthonormal_orthogonalIterate_euclideanCol_one hA
  have hspan : ∀ ν, Submodule.span 𝕜
      (Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν '' Set.Iic k) =
        Krylov.subspaceIterate (toEuclideanLin A)
          (Submodule.span 𝕜 (euclideanCol (1 : Matrix n n 𝕜) '' Set.Iic k)) ν := fun ν => by
    rw [← orthogonalIterate_euclideanCol_one_zero A]
    exact Krylov.span_orthogonalIterate_of_isLowerSet _ _ _ (isLowerSet_Iic k)
  have hρ : 0 < ‖l k‖ := hr0.trans_lt hrk
  have hJρ : ∀ j' ∈ Set.Iic k, ‖l k‖ ≤ ‖l j'‖ := fun j' hj' => by
    rcases (Set.mem_Iic.1 hj').lt_or_eq with h | h
    · exact (hsep _ _ h).le
    · rw [h]
  have hJr : ∀ j' ∉ Set.Iic k, ‖l j'‖ ≤ r := fun j' hj' => hr j' (by simpa using hj')
  have hrank := Krylov.finrank_span_image_eq_of_linearIndependent
    (orthonormal_euclideanCol (by simp : (1 : Matrix n n 𝕜)ᴴ * 1 = 1)).linearIndependent hx
    (Set.Iic k)
  obtain ⟨D, hD⟩ := Krylov.exists_gap_subspaceIterate_span_image_le hx hxtop heig hρ hJρ hr0 hrk
    hJr (hgen _ (isLowerSet_Iic k)) hrank
  set M := ‖LinearMap.toContinuousLinearMap (toEuclideanLin A)‖ with hMdef
  have hM : 0 ≤ M := norm_nonneg _
  have hAb : ∀ y, ‖toEuclideanLin A y‖ ≤ M * ‖y‖ := fun y =>
    (LinearMap.toContinuousLinearMap (toEuclideanLin A)).le_opNorm y
  refine ⟨2 * M * D, fun ν => ?_⟩
  rw [qrIterate_apply hA]
  have hbound := Krylov.norm_inner_le_of_gap (T := Submodule.span 𝕜 (x '' Set.Iic k))
    (S := Submodule.span 𝕜
      (Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν '' Set.Iic k)) hM hAb
    (Krylov.mapsTo_span_image_of_eigen heig (Set.Iic k))
    (Submodule.subset_span ⟨k, Set.mem_Iic.2 le_rfl, rfl⟩) ((hqon ν).1 k).le
    (Krylov.mem_orthogonal_span_image_of_orthonormal (hqon ν) (J := Set.Iic k)
      (by simpa using hkj)) ((hqon ν).1 j).le
  rw [Submodule.gap_congr _ _ (hspan ν)] at hbound
  refine hbound.trans ?_
  calc 2 * M * _ ≤ 2 * M * (D * (r / ‖l k‖) ^ ν) :=
        mul_le_mul_of_nonneg_left (hD ν) (mul_nonneg zero_le_two hM)
    _ = _ := by ring

omit [DecidableEq n] in
/-- The QR iterates of a Hermitian matrix are Hermitian, being unitary conjugates of it; so for a
Hermitian matrix the iterates converge to a *diagonal* matrix whenever they converge to a
triangular one ([quarteroni2000numerical] Property 5.9, last sentence). -/
theorem isHermitian_qrIterate {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    (qrIterate A k).IsHermitian := by
  rw [qrIterate_eq_conj_qrAccum]
  exact isHermitian_conjTranspose_mul_mul _ hA

/-- The unitary factor of a nonsingular upper Hessenberg matrix is upper Hessenberg
([quarteroni2000numerical] §5.6.3): the canonical instance of
`Matrix.IsUpperHessenberg.isUpperHessenberg_of_eq_mul`, which holds for every QR factorization. -/
theorem isUpperHessenberg_qrQ {A : Matrix n n 𝕜} (hA : IsUnit A.det) (hH : A.IsUpperHessenberg) :
    (qrQ A).IsUpperHessenberg :=
  hH.isUpperHessenberg_of_eq_mul hA (isUpperTriangular_qrR A) (qrQ_mul_qrR A).symm

/-- **The QR iteration preserves upper Hessenberg form** ([quarteroni2000numerical] §5.6.4): each
iterate is a nonsingular QR step of the previous one (`Matrix.isShiftedQrStep_qrIterate`), and
Hessenberg form survives such a step (`Matrix.IsShiftedQrStep.isUpperHessenberg`). -/
theorem isUpperHessenberg_qrIterate {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    (hH : A.IsUpperHessenberg) (k : ℕ) : (qrIterate A k).IsUpperHessenberg := by
  induction k with
  | zero => exact hH
  | succ k ih =>
    exact (isShiftedQrStep_qrIterate A k).isUpperHessenberg ih
      (by rw [zero_smul, sub_zero]; exact isUnit_det_qrIterate hA k)

/-! ### Shifts -/

/-- **One QR step with shift `μ`** ([quarteroni2000numerical] (5.52)): factor `T - μ I = Q R` and
return `R Q + μ I`. -/
noncomputable def shiftedQrStep (μ : 𝕜) (T : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  qrR (T - μ • 1) * qrQ (T - μ • 1) + μ • 1

/-- The shifted step is a unitary similarity, `R Q + μ I = Qᴴ T Q` (the display after
[quarteroni2000numerical] (5.52)). -/
theorem shiftedQrStep_eq_conj (μ : 𝕜) (T : Matrix n n 𝕜) :
    shiftedQrStep μ T = (qrQ (T - μ • 1))ᴴ * T * qrQ (T - μ • 1) := by
  rw [shiftedQrStep, qrR_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, conjTranspose_qrQ_mul_self, sub_add_cancel]

/-- The canonical shifted step is a shifted QR step in the sense of `Matrix.IsShiftedQrStep`. -/
theorem isShiftedQrStep_shiftedQrStep (μ : 𝕜) (T : Matrix n n 𝕜) :
    IsShiftedQrStep μ T (shiftedQrStep μ T) :=
  ⟨qrQ _, qrQ_mem_unitaryGroup _, qrR _, isUpperTriangular_qrR _, (qrQ_mul_qrR _).symm, rfl⟩

/-- **The QR iteration with a fixed shift `μ`** ([quarteroni2000numerical] §5.7.1): `T₀ = A` and
`T_{k+1} = shiftedQrStep μ T_k`. -/
noncomputable def shiftedQrIterate (A : Matrix n n 𝕜) (μ : 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => A
  | k + 1 => shiftedQrStep μ (shiftedQrIterate A μ k)

/-- The shifted iteration starts at `A`. -/
@[simp]
theorem shiftedQrIterate_zero (A : Matrix n n 𝕜) (μ : 𝕜) : shiftedQrIterate A μ 0 = A := rfl

/-- One step of the shifted iteration, by definition. -/
theorem shiftedQrIterate_succ (A : Matrix n n 𝕜) (μ : 𝕜) (k : ℕ) :
    shiftedQrIterate A μ (k + 1) = shiftedQrStep μ (shiftedQrIterate A μ k) := rfl

/-- **A fixed shift is the basic iteration on the shifted matrix**: `shiftedQrIterate A μ k =
qrIterate (A - μ I) k + μ I`. Consequently `Matrix.tendsto_qrIterate` and
`Matrix.exists_abs_qrIterate_apply_le` applied to `A - μ • 1` are the convergence claim of
[quarteroni2000numerical] §5.7.1: the subdiagonal entries decay like `|(λ_j - μ)/(λ_{j-1} - μ)|^k`
when `|λ_1 - μ| > … > |λ_n - μ| > 0`, under the general-position hypothesis for the same
eigenvector matrix. -/
theorem shiftedQrIterate_eq_qrIterate_sub_add (A : Matrix n n 𝕜) (μ : 𝕜) (k : ℕ) :
    shiftedQrIterate A μ k = qrIterate (A - μ • 1) k + μ • 1 := by
  induction k with
  | zero => rw [shiftedQrIterate_zero, qrIterate_zero, sub_add_cancel]
  | succ k ih => rw [shiftedQrIterate_succ, ih, shiftedQrStep, add_sub_cancel_right, qrIterate_succ]

/-- Every iterate of the fixed-shift iteration is a unitary conjugate of the starting matrix, by
the accumulated unitary factor of the iteration on `A - μ I`. -/
theorem shiftedQrIterate_eq_conj_qrAccum (A : Matrix n n 𝕜) (μ : 𝕜) (k : ℕ) :
    shiftedQrIterate A μ k =
      (qrAccum (A - μ • 1) k)ᴴ * A * qrAccum (A - μ • 1) k := by
  rw [shiftedQrIterate_eq_qrIterate_sub_add, qrIterate_eq_conj_qrAccum, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, conjTranspose_mul_qrAccum,
    sub_add_cancel]

/-- **The double-shift step** ([quarteroni2000numerical] (5.55)): two consecutive shifted steps
with the complex-conjugate pair of shifts `μ`, `conj μ`, the shifts being the two eigenvalues of
a `2 × 2` trailing block that the single-shift iteration cannot split. For a real matrix it is the
real step `Matrix.doubleShiftQrStep_map_ofReal`; the real-arithmetic Francis implementation is
specified by `Matrix.IsFrancisStep` and implemented in the Golub–Van Loan surface (Algorithm
7.5.1). -/
noncomputable def doubleShiftQrStep (T : Matrix n n 𝕜) (μ : 𝕜) : Matrix n n 𝕜 :=
  shiftedQrStep (starRingEnd 𝕜 μ) (shiftedQrStep μ T)

/-- The double-shift step is a unitary similarity. -/
theorem doubleShiftQrStep_eq_conj (T : Matrix n n 𝕜) (μ : 𝕜) :
    doubleShiftQrStep T μ =
      (qrQ (T - μ • 1) * qrQ (shiftedQrStep μ T - starRingEnd 𝕜 μ • 1))ᴴ * T *
        (qrQ (T - μ • 1) * qrQ (shiftedQrStep μ T - starRingEnd 𝕜 μ • 1)) := by
  rw [doubleShiftQrStep, shiftedQrStep_eq_conj (starRingEnd 𝕜 μ), conjTranspose_mul]
  generalize qrQ (shiftedQrStep μ T - starRingEnd 𝕜 μ • 1) = Q₂
  rw [shiftedQrStep_eq_conj μ T]
  simp only [Matrix.mul_assoc]

/-- The double-shift step is a unitary similarity, in existential form. -/
theorem exists_unitary_conj_doubleShiftQrStep (T : Matrix n n 𝕜) (μ : 𝕜) :
    ∃ Q ∈ Matrix.unitaryGroup n 𝕜, doubleShiftQrStep T μ = Qᴴ * T * Q :=
  ⟨_, mul_mem (qrQ_mem_unitaryGroup _) (qrQ_mem_unitaryGroup _), doubleShiftQrStep_eq_conj T μ⟩

end GramSchmidt

section Rayleigh

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- **The QR iteration with the Rayleigh-quotient shift** ([quarteroni2000numerical] (5.53)):
`T₀ = A` and `T_{k+1}` is the step with shift `μ_k = (T_k)_{nn}`, the current last diagonal entry.
No convergence theorem is stated: the book's quadratic-convergence claim is a local statement about
Rayleigh quotient iteration that it does not prove. -/
noncomputable def rayleighShiftQrIterate (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜
  | 0 => A
  | k + 1 =>
    shiftedQrStep (rayleighShiftQrIterate A k (Fin.last N) (Fin.last N))
      (rayleighShiftQrIterate A k)

/-- The Rayleigh-shift iteration starts at `A`. -/
@[simp]
theorem rayleighShiftQrIterate_zero (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    rayleighShiftQrIterate A 0 = A := rfl

/-- One step of the Rayleigh-shift iteration, by definition: the shift is the current last
diagonal entry. -/
theorem rayleighShiftQrIterate_succ (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) (k : ℕ) :
    rayleighShiftQrIterate A (k + 1) =
      shiftedQrStep (rayleighShiftQrIterate A k (Fin.last N) (Fin.last N))
        (rayleighShiftQrIterate A k) := rfl

/-- Every Rayleigh-shift iterate is a unitary conjugate of the starting matrix. -/
theorem exists_unitary_conj_rayleighShiftQrIterate (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜)
    (k : ℕ) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin (N + 1)) 𝕜, rayleighShiftQrIterate A k = Qᴴ * A * Q := by
  induction k with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ k ih =>
    obtain ⟨Q, hQ, hk⟩ := ih
    refine ⟨Q * qrQ (rayleighShiftQrIterate A k -
      rayleighShiftQrIterate A k (Fin.last N) (Fin.last N) • 1),
      mul_mem hQ (qrQ_mem_unitaryGroup _), ?_⟩
    rw [rayleighShiftQrIterate_succ, shiftedQrStep_eq_conj, conjTranspose_mul]
    generalize qrQ (rayleighShiftQrIterate A k -
      rayleighShiftQrIterate A k (Fin.last N) (Fin.last N) • 1) = Q'
    rw [hk]
    simp only [Matrix.mul_assoc]

end Rayleigh

/-! ### The Francis double-shift step

`Matrix.doubleShiftQrStep` takes two complex-conjugate shifts in complex arithmetic. For a real
matrix its result is real (`Matrix.doubleShiftQrStep_map_ofReal`): it is the orthogonal
similarity by the orthogonal factor of the real matrix `M = H² − s H + t I`. The implicit
(Francis) step computes such a similarity without forming `M`; its specification is
`Matrix.IsFrancisStep`, and the implicit Q theorem identifies every Francis step of an unreduced
Hessenberg matrix with the explicit one up to signs (`Matrix.IsFrancisStep.eq_diagonal_conj`).
The implementation is [golub2013matrix] Algorithm 7.5.1, in the surface. -/

section Francis

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- A nonsingular matrix has a nonsingular canonical triangular factor. -/
theorem isUnit_det_qrR {A : Matrix (Fin N) (Fin N) 𝕜} (hA : IsUnit A.det) :
    IsUnit (qrR A).det := by
  rw [det_of_isUpperTriangular (isUpperTriangular_qrR A), isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun j _ => (qrR_diag_pos hA j).ne'

/-- For a nonsingular real `M` commuting with `H`, the orthogonal factor `Z` of `M = Z R`
conjugates `H` to `R H R⁻¹`: `Zᵀ H Z = Zᵀ H M R⁻¹ = Zᵀ M H R⁻¹ = R H R⁻¹`. -/
theorem transpose_qrQ_mul_mul_qrQ {H M : Matrix (Fin N) (Fin N) ℝ} (hM : IsUnit M.det)
    (hHM : H * M = M * H) : (qrQ M)ᵀ * H * qrQ M = qrR M * H * (qrR M)⁻¹ := by
  have hZ : qrQ M = M * (qrR M)⁻¹ := by
    calc qrQ M = qrQ M * qrR M * (qrR M)⁻¹ :=
          (mul_nonsing_inv_cancel_right _ _ (isUnit_det_qrR hM)).symm
      _ = M * (qrR M)⁻¹ := by rw [qrQ_mul_qrR]
  have hRM : (qrQ M)ᵀ * M = qrR M := by
    rw [← conjTranspose_eq_transpose_of_trivial, ← qrR_eq]
  calc (qrQ M)ᵀ * H * qrQ M = (qrQ M)ᵀ * H * (M * (qrR M)⁻¹) := by rw [← hZ]
    _ = (qrQ M)ᵀ * (H * M) * (qrR M)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (qrQ M)ᵀ * M * H * (qrR M)⁻¹ := by rw [hHM]; simp only [Matrix.mul_assoc]
    _ = qrR M * H * (qrR M)⁻¹ := by rw [hRM]

/-- `H` commutes with the double-shift polynomial `H² − s H + t I`. -/
theorem mul_francisPoly_comm (H : Matrix (Fin N) (Fin N) ℝ) (s t : ℝ) :
    H * (H * H - s • H + t • 1) = (H * H - s • H + t • 1) * H := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

/-- **The specification of the implicit double-shift (Francis) step** ([golub2013matrix]
Algorithm 7.5.1, header): `H' = Zᵀ H Z` for an orthogonal `Z` such that `H'` is upper Hessenberg
and `Zᵀ (H² − s H + t I)` is upper triangular — i.e. `Z` is the orthogonal factor of *some* QR
factorization of `M = H² − s H + t I`. (In the algorithm `s`, `t` are the trace and determinant of
the trailing `2 × 2` block; the predicate is for any real `s`, `t`.) -/
def IsFrancisStep (s t : ℝ) (H H' : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ Z ∈ orthogonalGroup (Fin N) ℝ, H' = Zᵀ * H * Z ∧ H'.IsUpperHessenberg ∧
    (Zᵀ * (H * H - s • H + t • 1)).IsUpperTriangular

/-- **Existence through the explicit route** ([golub2013matrix] §7.5.4: "explicitly form `M`,
compute `M = Z R`, set `H₂ = Zᵀ H Z`"): for upper Hessenberg `H` and nonsingular
`M = H² − s H + t I`, the canonical orthogonal factor of `M` gives a Francis step, `Zᵀ H Z =
R H R⁻¹` being Hessenberg. -/
theorem isFrancisStep_qrQ {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsUpperHessenberg) {s t : ℝ}
    (hM : IsUnit (H * H - s • H + t • 1).det) :
    IsFrancisStep s t H
      ((qrQ (H * H - s • H + t • 1))ᵀ * H * qrQ (H * H - s • H + t • 1)) := by
  refine ⟨qrQ _, qrQ_mem_unitaryGroup _, rfl, ?_, ?_⟩
  · rw [transpose_qrQ_mul_mul_qrQ hM (mul_francisPoly_comm H s t)]
    exact ((isUpperTriangular_qrR _).mul_isUpperHessenberg hH).mul_isUpperTriangular
      (isUpperTriangular_qrR _).inv
  · rw [← conjTranspose_eq_transpose_of_trivial, ← qrR_eq]
    exact isUpperTriangular_qrR _

/-- The first column of `M = Z T` with `T` upper triangular is `T₀₀ Z e₀`. -/
theorem col_zero_eq_smul_of_eq_mul {K : Type*} [CommRing K] {M Z T : Matrix (Fin (N + 1))
    (Fin (N + 1)) K} (hM : M = Z * T) (hT : T.IsUpperTriangular) : M.col 0 = T 0 0 • Z.col 0 := by
  ext i
  rw [hM, col_apply, mul_apply, Finset.sum_eq_single 0, Pi.smul_apply, col_apply, smul_eq_mul,
    mul_comm]
  · intro l _ hl
    rw [hT (Fin.pos_iff_ne_zero.2 hl), mul_zero]
  · simp

/-- **Essential uniqueness of the Francis step** ([golub2013matrix] §7.5.5: "the implicit Q
theorem permits us to conclude that … they are essentially equal"): for unreduced upper Hessenberg
`H` and nonsingular `M = H² − s H + t I`, every Francis step is the explicit one up to a
`±1` diagonal similarity. The first columns of `Z` and of `Z₀ = qrQ M` are both multiples of
`M e₀ ≠ 0`, hence equal up to sign; after flipping the sign of `Z`, `Matrix.implicitQ_real` applies
with the unreduced `Z₀ᵀ H Z₀ = R H R⁻¹`. -/
theorem IsFrancisStep.eq_diagonal_conj {H H' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hH : H.IsUnreducedUpperHessenberg) {s t : ℝ} (hM : IsUnit (H * H - s • H + t • 1).det)
    (h : IsFrancisStep s t H H') :
    ∃ d : Fin (N + 1) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧
      H' = diagonal d * ((qrQ (H * H - s • H + t • 1))ᵀ * H *
        qrQ (H * H - s • H + t • 1)) * diagonal d := by
  set M := H * H - s • H + t • 1 with hMdef
  obtain ⟨Z, hZ, rfl, hH', hT⟩ := h
  have hstar : ∀ X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ, star X = Xᵀ :=
    conjTranspose_eq_transpose_of_trivial
  have hZZ : Z * Zᵀ = 1 := by rw [← hstar]; exact (mem_unitaryGroup_iff).1 hZ
  have hZZ' : Zᵀ * Z = 1 := by rw [← hstar]; exact (mem_unitaryGroup_iff').1 hZ
  -- the explicit step is unreduced
  have hG₀ : ((qrQ M)ᵀ * H * qrQ M).IsUnreducedUpperHessenberg := by
    rw [transpose_qrQ_mul_mul_qrQ hM (mul_francisPoly_comm H s t)]
    exact hH.mul_mul_inv_of_isUpperTriangular (isUpperTriangular_qrR M)
      fun i => (qrR_diag_pos hM i).ne'
  -- the first columns
  have hc : M.col 0 = (Zᵀ * M) 0 0 • Z.col 0 :=
    col_zero_eq_smul_of_eq_mul (by rw [← Matrix.mul_assoc, hZZ, Matrix.one_mul]) hT
  have hc₀ : M.col 0 = qrR M 0 0 • (qrQ M).col 0 :=
    col_zero_eq_smul_of_eq_mul (qrQ_mul_qrR M).symm (isUpperTriangular_qrR M)
  have hM0 : M.col 0 ≠ 0 :=
    (linearIndependent_cols_of_det_ne_zero (isUnit_iff_ne_zero.1 hM)).ne_zero 0
  have hT0 : (Zᵀ * M) 0 0 ≠ 0 := fun h0 => hM0 (by rw [hc, h0, zero_smul])
  set σ := qrR M 0 0 / (Zᵀ * M) 0 0 with hσ
  have hZcol : Z.col 0 = σ • (qrQ M).col 0 := by
    rw [hσ, div_eq_inv_mul, ← smul_smul, ← hc₀, hc, smul_smul, inv_mul_cancel₀ hT0, one_smul]
  have hunit : ∀ X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ, Xᵀ * X = 1 →
      X.col 0 ⬝ᵥ X.col 0 = 1 := fun X hX => by
    have := congrFun (congrFun hX 0) 0
    rwa [mul_apply, one_apply_eq] at this
  have hσσ : σ * σ = 1 := by
    have h1 := hunit Z hZZ'
    have hQM : (qrQ M)ᵀ * qrQ M = 1 := by
      rw [← hstar]
      exact (mem_unitaryGroup_iff').1 (qrQ_mem_unitaryGroup M)
    have h2 := hunit (qrQ M) hQM
    rw [hZcol, smul_dotProduct, dotProduct_smul, h2, smul_eq_mul, smul_eq_mul, mul_one] at h1
    exact h1
  -- flip the sign of `Z`
  have hV : σ • Z ∈ orthogonalGroup (Fin (N + 1)) ℝ := by
    rw [mem_unitaryGroup_iff', hstar]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hZZ', smul_smul, hσσ, one_smul]
  have hVHV : (σ • Z)ᵀ * H * (σ • Z) = Zᵀ * H * Z := by
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hσσ, one_smul]
  have hV0 : (σ • Z).col 0 = (qrQ M).col 0 := by
    ext i
    have := congrFun hZcol i
    simp only [col_apply, smul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this, ← mul_assoc, hσσ, one_mul]
  obtain ⟨d, hd, -, -, hGH⟩ := implicitQ_real (qrQ_mem_unitaryGroup M) hV hG₀
    (by rw [hVHV]; exact hH') hV0
  exact ⟨d, hd, by rw [← hVHV, hGH]⟩

/-- If `μ` is not an eigenvalue of `A`, then `A − μ I` is nonsingular. -/
theorem isUnit_det_sub_smul_one_of_notMem_spectrum {K : Type*} [Field K] {m : Type*}
    [Fintype m] [DecidableEq m] {A : Matrix m m K} {μ : K} (h : μ ∉ spectrum K A) :
    IsUnit (A - μ • 1).det := by
  rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det] at h
  rw [show A - μ • 1 = -(μ • 1 - A) by abel, det_neg]
  exact (isUnit_one.neg.pow _).mul h

/-- **The double-shift step of a real matrix is real** ([golub2013matrix] §7.5.4): for real `H` and
a complex shift `a` that is not an eigenvalue, the two canonical complex steps with shifts `a`,
`ā` give the real orthogonal similarity by the orthogonal factor of
`M = H² − 2 re(a) H + |a|² I`. By the product identity the two steps give the factorization
`(U₁ U₂)(R₂ R₁) = (H − a)(H − ā) = M` with positive diagonal, and so does the complexified
`qrQ M * qrR M`; `Matrix.qr_unique` identifies them. -/
theorem doubleShiftQrStep_map_ofReal (H : Matrix (Fin N) (Fin N) ℝ) {a : ℂ}
    (ha : a ∉ spectrum ℂ H.complexify) :
    doubleShiftQrStep H.complexify a =
      ((qrQ (H * H - (2 * a.re) • H + Complex.normSq a • 1))ᵀ * H *
        qrQ (H * H - (2 * a.re) • H + Complex.normSq a • 1)).complexify := by
  set M := H * H - (2 * a.re) • H + Complex.normSq a • 1 with hMdef
  have hdet₁ : IsUnit (H.complexify - a • 1).det := isUnit_det_sub_smul_one_of_notMem_spectrum ha
  have hdetc : IsUnit (H.complexify - starRingEnd ℂ a • 1).det :=
    isUnit_det_sub_smul_one_of_notMem_spectrum fun h =>
      ha ((star_mem_spectrum_complexify_iff H a).1 h)
  set U₁ := qrQ (H.complexify - a • 1) with hU₁
  set R₁ := qrR (H.complexify - a • 1) with hR₁
  have hU₁R₁ : U₁ * R₁ = H.complexify - a • 1 := qrQ_mul_qrR _
  have hU₁u : U₁ᴴ * U₁ = 1 := conjTranspose_qrQ_mul_self _
  have hH₁ : shiftedQrStep a H.complexify - starRingEnd ℂ a • 1 =
      U₁ᴴ * (H.complexify - starRingEnd ℂ a • 1) * U₁ := by
    rw [shiftedQrStep_eq_conj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hU₁u]
  have hdet₂ : IsUnit (shiftedQrStep a H.complexify - starRingEnd ℂ a • 1).det := by
    rw [hH₁, det_mul, det_mul, mul_right_comm, ← det_mul, hU₁u, det_one, one_mul]
    exact hdetc
  set U₂ := qrQ (shiftedQrStep a H.complexify - starRingEnd ℂ a • 1) with hU₂
  set R₂ := qrR (shiftedQrStep a H.complexify - starRingEnd ℂ a • 1) with hR₂
  have hU₂R₂ : U₂ * R₂ = shiftedQrStep a H.complexify - starRingEnd ℂ a • 1 := qrQ_mul_qrR _
  -- the two steps multiply out to `M`
  have hMc : M.complexify = (H.complexify - a • 1) * (H.complexify - starRingEnd ℂ a • 1) := by
    have h1 : Matrix.complexify (1 : Matrix (Fin N) (Fin N) ℝ) = 1 := by
      ext i j; by_cases hij : i = j <;> simp [complexify_apply, one_apply, hij]
    rw [hMdef, complexify_add, complexify_sub, complexify_mul, complexify_smul, complexify_smul,
      h1]
    have h2 : ((2 * a.re : ℝ) : ℂ) = a + starRingEnd ℂ a := (Complex.add_conj a).symm
    have h3 : ((Complex.normSq a : ℝ) : ℂ) = a * starRingEnd ℂ a := (Complex.mul_conj a).symm
    rw [h2, h3]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
    module
  have hprod : U₁ * U₂ * (R₂ * R₁) = M.complexify := by
    have hstep : shiftedQrStep a H.complexify = R₁ * U₁ + a • 1 := rfl
    calc U₁ * U₂ * (R₂ * R₁) = U₁ * (U₂ * R₂) * R₁ := by simp only [Matrix.mul_assoc]
      _ = U₁ * R₁ * (U₁ * R₁) + (a - starRingEnd ℂ a) • (U₁ * R₁) := by
          rw [hU₂R₂, hstep]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
          module
      _ = M.complexify := by
          rw [hU₁R₁, hMc]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one, Matrix.one_mul]
          module
  -- `M` is nonsingular
  have hMdet : IsUnit M.det := by
    have hc : IsUnit (M.complexify).det := by
      rw [hMc, det_mul]; exact hdet₁.mul hdetc
    have : (M.complexify).det = (M.det : ℂ) := (Complex.ofRealHom.map_det M).symm
    rw [this, isUnit_iff_ne_zero, Complex.ofReal_ne_zero] at hc
    exact isUnit_iff_ne_zero.2 hc
  -- two factorizations with positive diagonal
  have hQM : (qrQ M).complexify ᴴ * (qrQ M).complexify = 1 := by
    rw [← complexify_conjTranspose, ← complexify_mul, conjTranspose_qrQ_mul_self]
    ext i j; by_cases hij : i = j <;> simp [complexify_apply, one_apply, hij]
  have hUU : (U₁ * U₂)ᴴ * (U₁ * U₂) = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₁ᴴ, hU₁u, Matrix.one_mul,
      conjTranspose_qrQ_mul_self]
  have htri : (R₂ * R₁).IsUpperTriangular := (isUpperTriangular_qrR _).mul (isUpperTriangular_qrR _)
  have hpos : ∀ j, 0 < (R₂ * R₁).diag j := fun j => by
    rw [diag_apply, IsUpperTriangular.diag_mul (isUpperTriangular_qrR _) (isUpperTriangular_qrR _)]
    exact mul_pos (qrR_diag_pos hdet₂ j) (qrR_diag_pos hdet₁ j)
  have htriM : ((qrR M).complexify).IsUpperTriangular := fun i j hij => by
    rw [complexify_apply, isUpperTriangular_qrR M hij, Complex.ofReal_zero]
  have hposM : ∀ j, 0 < ((qrR M).complexify).diag j := fun j => by
    rw [diag_apply, complexify_apply]
    exact Complex.zero_lt_real.2 (qrR_diag_pos hMdet j)
  obtain ⟨hU, -⟩ := qr_unique hprod.symm (by rw [← complexify_mul, qrQ_mul_qrR]) hUU hQM htri
    htriM hpos hposM
  rw [doubleShiftQrStep_eq_conj, ← hU₁, ← hU₂, hU, ← complexify_conjTranspose, ← complexify_mul,
    ← complexify_mul, conjTranspose_eq_transpose_of_trivial]

end Francis

section LeadingPrincipal

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- Summing a function that vanishes from `m` on over `Fin N` is summing over `Fin m`. -/
private theorem sum_castLE {M : Type*} [AddCommMonoid M] {m : ℕ} (hm : m ≤ N) (F : Fin N → M)
    (hF : ∀ l : Fin N, m ≤ (l : ℕ) → F l = 0) :
    ∑ l, F l = ∑ l : Fin m, F (Fin.castLE hm l) := by
  have h := Finset.sum_map Finset.univ (Fin.castLEEmb hm) F
  simp only [Fin.coe_castLEEmb] at h
  rw [← h]
  refine (Finset.sum_subset (Finset.subset_univ _) fun l _ hl => hF l ?_).symm
  by_contra hlt
  exact hl (Finset.mem_map.2 ⟨⟨l, not_le.1 hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/-- **The general-position hypothesis of `Matrix.tendsto_qrIterate` is the LU condition on the
inverse eigenvector matrix** ([golub1989matrix] Theorem 7.3.1; the hypothesis
[quarteroni2000numerical] Property 5.9 omits): for an invertible `X` with columns `x_j` and the
lower set `J = {i | i < m}`, the span of the first `m` canonical vectors meets the span of the
eigenvectors `x_j`, `j ≥ m`, only in `0` exactly when the leading principal `m × m` minor of `X⁻¹`
is nonzero. The rows of `X⁻¹` are the dual basis of the columns of `X`, so a vector supported on
`J` lying in that span is a kernel vector of the leading block of `X⁻¹`, and conversely. -/
theorem disjoint_span_euclideanCol_iff_isUnit_leadingPrincipal {X : Matrix (Fin N) (Fin N) 𝕜}
    (hX : IsUnit X.det) {m : ℕ} (hm : m ≤ N) :
    Disjoint (Submodule.span 𝕜 (euclideanCol (1 : Matrix (Fin N) (Fin N) 𝕜) '' {i | (i : ℕ) < m}))
        (Submodule.span 𝕜 (euclideanCol X '' {i | (i : ℕ) < m}ᶜ)) ↔
      IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det := by
  have hkey : ∀ v : Fin N → 𝕜, (∀ l : Fin N, m ≤ (l : ℕ) → v l = 0) → ∀ i : Fin m,
      (X⁻¹ *ᵥ v) (Fin.castLE hm i) =
        ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm) *ᵥ fun i => v (Fin.castLE hm i)) i := by
    intro v hv i
    simp only [mulVec, dotProduct, submatrix_apply]
    exact sum_castLE hm _ fun l hl => by rw [hv l hl, mul_zero]
  have hmemJ : ∀ i : Fin m, (Fin.castLE hm i : Fin N) ∈ {i : Fin N | (i : ℕ) < m} := fun i => by
    simp
  rw [span_euclideanCol_eq_map X, Submodule.disjoint_def]
  constructor
  · intro hdisj
    by_contra hL0
    rw [isUnit_iff_ne_zero, not_not] at hL0
    obtain ⟨a, ha0, haL⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hL0
    obtain ⟨v, hv⟩ : ∃ v : Fin N → 𝕜,
        v = fun l : Fin N => if h : (l : ℕ) < m then a ⟨l, h⟩ else 0 := ⟨_, rfl⟩
    have hvsupp : ∀ l : Fin N, m ≤ (l : ℕ) → v l = 0 := fun l hl => by
      rw [hv]
      exact dite_eq_right (not_lt.2 hl)
    have hva : (fun i : Fin m => v (Fin.castLE hm i)) = a := by
      funext i
      rw [hv]
      exact dite_eq_left i.isLt
    have hvP : (WithLp.toLp 2 v : EuclideanSpace 𝕜 (Fin N)) ∈
        Submodule.span 𝕜 (euclideanCol (1 : Matrix (Fin N) (Fin N) 𝕜) '' {i | (i : ℕ) < m}) :=
      (mem_span_euclideanCol_one_iff _ _).2 fun i hi => hvsupp i (not_lt.1 hi)
    have hw : (WithLp.toLp 2 (X⁻¹ *ᵥ v) : EuclideanSpace 𝕜 (Fin N)) ∈
        Submodule.span 𝕜 (euclideanCol (1 : Matrix (Fin N) (Fin N) 𝕜) '' {i | (i : ℕ) < m}ᶜ) := by
      refine (mem_span_euclideanCol_one_iff _ _).2 fun i hi => ?_
      have hi' : (i : ℕ) < m := by simpa using hi
      have h := hkey v hvsupp ⟨i, hi'⟩
      rw [hva, haL] at h
      exact h
    have hvmem : (WithLp.toLp 2 v : EuclideanSpace 𝕜 (Fin N)) ∈
        (Submodule.span 𝕜 (euclideanCol (1 : Matrix (Fin N) (Fin N) 𝕜) '' {i | (i : ℕ) < m}ᶜ)).map
          (toEuclideanLin X) := by
      refine ⟨WithLp.toLp 2 (X⁻¹ *ᵥ v), hw, ?_⟩
      rw [toEuclideanLin_toLp, mulVec_mulVec, mul_nonsing_inv _ hX, one_mulVec]
    have h0 := hdisj _ hvP hvmem
    refine ha0 ?_
    rw [← hva]
    funext i
    exact congrArg (fun z : EuclideanSpace 𝕜 (Fin N) => z (Fin.castLE hm i)) h0
  · intro hL v hvP hvmem
    obtain ⟨w, hw, rfl⟩ := hvmem
    rw [mem_span_euclideanCol_one_iff] at hvP
    rw [SetLike.mem_coe, mem_span_euclideanCol_one_iff] at hw
    have hu : ∀ l : Fin N, m ≤ (l : ℕ) → (X *ᵥ WithLp.ofLp w) l = 0 := fun l hl =>
      hvP l (by simp; omega)
    have hXw : X⁻¹ *ᵥ (X *ᵥ WithLp.ofLp w) = WithLp.ofLp w := by
      rw [mulVec_mulVec, nonsing_inv_mul _ hX, one_mulVec]
    have hLa : (X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm) *ᵥ
        (fun i => (X *ᵥ WithLp.ofLp w) (Fin.castLE hm i)) = 0 := by
      funext i
      rw [← hkey _ hu i, hXw]
      exact hw _ (by simp)
    have ha := eq_zero_of_mulVec_eq_zero (isUnit_iff_ne_zero.1 hL) hLa
    ext l
    rw [toEuclideanLin_apply]
    by_cases hl : (l : ℕ) < m
    · exact congrFun ha ⟨l, hl⟩
    · exact hu l (not_lt.1 hl)

/-- The initial segments of `Fin N` are lower sets. -/
theorem isLowerSet_setOf_val_lt (m : ℕ) : IsLowerSet {i : Fin N | (i : ℕ) < m} :=
  fun _ _ hba ha => (Fin.le_def.1 hba).trans_lt ha

/-- Every lower set of `Fin N` is an initial segment `{i | i < m}` with `m ≤ N`. -/
theorem exists_eq_setOf_val_lt_of_isLowerSet {J : Set (Fin N)} (hJ : IsLowerSet J) :
    ∃ m ≤ N, J = {i : Fin N | (i : ℕ) < m} := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, Nat.zero_le _, by ext i; simp⟩
  · obtain ⟨a, haJ, hmax⟩ := Set.exists_max_image J id J.toFinite hne
    refine ⟨a + 1, a.isLt, ?_⟩
    ext i
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hi
      have := Fin.le_def.1 (hmax i hi)
      simp only [id] at this
      omega
    · intro hi
      exact hJ (Fin.le_def.2 (by omega)) haJ

/-- **The general-position hypothesis of `Matrix.tendsto_qrIterate` for an invertible eigenvector
matrix `X` is the nonvanishing of every leading principal minor of `X⁻¹`** ([golub1989matrix]
Theorem 7.3.1, the hypothesis [quarteroni2000numerical] Property 5.9 omits), since the lower sets
of `Fin N` are the initial segments. -/
theorem forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal {X : Matrix (Fin N) (Fin N) 𝕜}
    (hX : IsUnit X.det) :
    (∀ J : Set (Fin N), IsLowerSet J →
      Disjoint (Submodule.span 𝕜 (euclideanCol (1 : Matrix (Fin N) (Fin N) 𝕜) '' J))
        (Submodule.span 𝕜 (euclideanCol X '' Jᶜ))) ↔
      ∀ (m : ℕ) (hm : m ≤ N), IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det := by
  constructor
  · intro h m hm
    exact (disjoint_span_euclideanCol_iff_isUnit_leadingPrincipal hX hm).1
      (h _ (isLowerSet_setOf_val_lt m))
  · intro h J hJ
    obtain ⟨m, hm, rfl⟩ := exists_eq_setOf_val_lt_of_isLowerSet hJ
    exact (disjoint_span_euclideanCol_iff_isUnit_leadingPrincipal hX hm).2 (h m hm)

end LeadingPrincipal

end Matrix
