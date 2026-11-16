/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.PowerMethod
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.KrylovDecomposition
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.Similar

/-!
# Orthogonal iteration and the QR algorithm

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $A$ be a
linear operator on $E$, and let $(q_i)_{i \in \iota}$ be a family in $E$ indexed by a well-ordered
set. **Orthogonal iteration** (simultaneous iteration) takes the Gram–Schmidt orthonormalization
$(q^{(k)}_i)_i$ of the family $(A^k q_i)_i$. For every index $m$, the span of the $q^{(k)}_i$ with
$i \le m$ is $A^k \operatorname{span}\{q_i : i \le m\}$, so the iteration runs subspace iteration on
a whole flag of subspaces at once. The orthonormalization keeps the family from collapsing onto the
dominant eigendirection; without it, the family does collapse. The **QR algorithm** for a square
matrix $A$ is the same iteration written without subspaces: $A_0 = A$, and $A_{k+1} = R_k Q_k$ for
the QR decomposition $A_k = Q_k R_k$. With $\tilde Q_k = Q_0 Q_1 \cdots Q_{k-1}$ the iterate is
$A_k = \tilde Q_k^H A \tilde Q_k$, and the columns of $\tilde Q_k$ are the orthogonal iterates of
the standard basis. Hence convergence of the flag is convergence of $A_k$ to upper triangular form.
The definitions and the convergence theorems follow [kress1998numerical], §7.4.

The module also treats the variants that the textbooks use, after [golub2013matrix] §7.3–7.5 and
§10.5 and [quarteroni2000numerical] §5.6–5.7: a QR step with shift $\mu$, $H - \mu I = QR$ and
$H' = RQ + \mu I$, for an arbitrary QR factorization; chains of such steps and their product
identity; the iterations with a fixed shift, with the Rayleigh-quotient shift and with a pair of
complex conjugate shifts; the specification of the implicit double-shift (Francis) step; and
orthogonal iteration for an arbitrary thin QR factorization.

## Main definitions

* `Krylov.orthogonalIterate`: the Gram–Schmidt orthonormalization of the family $(A^k q_i)_i$.
* `Matrix.qrQ`, `Matrix.qrR`: the QR decomposition $A = QR$ obtained by Gram–Schmidt on the columns
  of $A$; the diagonal of $R$ is positive when $A$ is nonsingular, which makes the decomposition
  unique.
* `Matrix.qrIterate`, `Matrix.qrAccum`, `Matrix.qrTriangle`: the QR iterates $A_k$, the accumulated
  unitary factor $\tilde Q_k = Q_0 \cdots Q_{k-1}$ and the accumulated triangular factor
  $\tilde R_k = R_{k-1} \cdots R_0$.
* `Matrix.IsShiftedQrStep`: $H'$ is one QR step from $H$ with shift $\mu$ for some QR factorization
  (Givens or Householder, any signs).
* `Matrix.IsShiftedQrChain`: a chain of shifted QR steps with given factors, as in (10.5.4) of
  [golub2013matrix].
* `Matrix.IsOrthogonalIterationStep`: one step $AQ = Q'R$ of orthogonal iteration for some thin QR
  factorization, as in (7.3.6) and (8.2.8) of [golub2013matrix].
* `Matrix.shiftedQrStep`, `Matrix.shiftedQrIterate`, `Matrix.rayleighShiftQrIterate`,
  `Matrix.doubleShiftQrStep`: the canonical shifted QR step and the iterations of
  [quarteroni2000numerical] §5.7 with a fixed shift, with the Rayleigh-quotient shift and with a
  pair of complex conjugate shifts.
* `Matrix.IsFrancisStep`: the specification of the implicit double-shift (Francis) step,
  $H' = Z^T H Z$ upper Hessenberg with $Z$ orthogonal and $Z^T(H^2 - sH + tI)$ upper triangular.

## Main results

* `Krylov.span_orthogonalIterate`: the orthogonal iterates span the iterated subspaces.
* `Krylov.tendsto_orthogonalIterate`: for a diagonalizable operator whose eigenvalues have distinct
  moduli and a starting flag in general position, the compressions
  $\langle q^{(\nu)}_j, A q^{(\nu)}_k \rangle$ tend to $0$ below the diagonal and to $\lambda_j$ on
  it (Theorem 7.19 of [kress1998numerical]).
* `Matrix.exists_isOrthogonalIterationStep`, `Matrix.IsOrthogonalIterationStep.range_eq`,
  `Matrix.exists_pow_mul_eq_mul_of_isOrthogonalIterationStep`,
  `Matrix.range_eq_subspaceIterate_of_isOrthogonalIterationStep`: orthogonal iteration exists for
  any factorization, and under full column rank it computes $A^k \operatorname{ran} Q_0$, with
  $A^k Q_0 = Q_k (R_k \cdots R_1)$.
* `Matrix.IsOrthogonalIterationStep.isShiftedQrStep`: a square step of orthogonal iteration is an
  unshifted QR step of $Q^H A Q$ ([golub2013matrix] §7.3.3).
* `Matrix.qrQ_mul_qrR`: $A = QR$, with $Q$ unitary (`Matrix.qrQ_mem_unitaryGroup`) and $R$ upper
  triangular (`Matrix.isUpperTriangular_qrR`).
* `Matrix.euclideanCol_eq_gramSchmidtNormed_of_eq_mul`: uniqueness of the QR decomposition: if
  $M = UT$ with $U$ unitary and $T$ upper triangular with positive diagonal, then the columns of $U$
  are the Gram–Schmidt orthonormalization of the columns of $M$.
* `Matrix.pow_eq_qrAccum_mul_qrTriangle`: $A^k = \tilde Q_k \tilde R_k$, so $\tilde Q_k$
  orthonormalizes the columns of $A^k$.
* `Matrix.qrAccum_eq_orthogonalIterate`, `Matrix.qrIterate_eq_conj_orthogonalIterate`: the QR
  algorithm is orthogonal iteration on the standard basis.
* `Matrix.tendsto_qrIterate`: under the hypotheses of the convergence theorem for orthogonal
  iteration, the QR iterates tend to upper triangular form with the eigenvalues in order on the
  diagonal (Theorem 7.20 of [kress1998numerical]).
* `Matrix.exists_abs_qrIterate_apply_le`: the entry $(j, k)$, $k < j$, of $A_\nu$ is
  $O((r/|\lambda_k|)^\nu)$ for every $r < |\lambda_k|$ that bounds the moduli of the later
  eigenvalues.
* `Matrix.disjoint_span_euclideanCol_iff_isUnit_leadingPrincipal`,
  `Matrix.forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal`: the general-position hypothesis
  is the nonvanishing of the leading principal minors of the inverse eigenvector matrix, a
  hypothesis that Property 5.9 of [quarteroni2000numerical] omits.
* `Matrix.isHermitian_qrIterate`, `Matrix.isUpperHessenberg_qrIterate`: the QR algorithm preserves
  Hermitian and upper Hessenberg form ([quarteroni2000numerical] §5.6.4).
* `Matrix.shiftedQrStep_eq_conj`, `Matrix.doubleShiftQrStep_eq_conj`,
  `Matrix.exists_unitary_conj_rayleighShiftQrIterate`: each shifted iteration is a unitary
  similarity; `Matrix.shiftedQrIterate_eq_qrIterate_sub_add` reduces a fixed shift $\mu$ to the
  basic iteration on $A - \mu I$.
* `Matrix.IsShiftedQrStep.eq_conj`, `Matrix.IsShiftedQrStep.unique_of_isUnit`,
  `Matrix.IsShiftedQrStep.isUpperHessenberg`: for arbitrary factorizations, a shifted step is a
  unitary similarity, two steps are similar by a unimodular diagonal matrix when $H - \mu I$ is
  nonsingular, and Hessenberg form survives a nonsingular step.
* `Matrix.IsUnreducedUpperHessenberg.isShiftedQrStep_apply_last`: an exact shift deflates an
  unreduced Hessenberg matrix in one step (Theorem 7.5.1 of [golub2013matrix]).
* `Matrix.prod_mul_prod_reverse_eq_prod_sub_smul_one`: a chain of shifted steps multiplies out to
  the shift polynomial, $(V_0 \cdots V_{p-1})(R_{p-1} \cdots R_0) = \prod_i (H_0 - \mu_i I)$
  ((7.5.7) and Theorem 10.5.1 of [golub2013matrix]); `Matrix.exists_isShiftedQrChain`: Givens chains
  exist for arbitrary shifts.
* `Matrix.exists_norm_apply_le_of_isShiftedQrStep`: the rate of convergence of a fixed-shift
  iteration, for any factorizations.
* `Matrix.doubleShiftQrStep_map_ofReal`, `Matrix.isFrancisStep_qrQ`,
  `Matrix.IsFrancisStep.eq_diagonal_conj`: the double-shift step of a real matrix is real, the
  explicit construction gives a Francis step, and every Francis step of an unreduced Hessenberg
  matrix is that one up to a $\pm 1$ diagonal similarity, by the implicit Q theorem
  `Matrix.implicitQ_real` of `Numlib.LinearAlgebra.Matrix.KrylovDecomposition`.

## Proof outline

The QR algorithm defines no subspaces. The product identity $A^k = \tilde Q_k \tilde R_k$ and the
uniqueness of the QR decomposition identify the columns of $\tilde Q_k$ with the Gram–Schmidt
orthonormalization of the columns of $A^k$, that is, with orthogonal iteration on the standard
basis. Then $A_k = \tilde Q_k^H A \tilde Q_k$ is the compression of $A$ on the orthogonal iterates.
Theorem 7.19 of [kress1998numerical] rests on his Lemma 7.18, the gap form of subspace iteration,
which is `Krylov.exists_gap_subspaceIterate_span_image_le` of `Numlib.Eigen.PowerMethod`. Applied to
every initial segment of the flag, it brings the iterated subspaces close to the invariant subspaces
of the dominant eigenvalues, and two estimates on orthonormal families close to an invariant flag
turn this into convergence of the entries.

## Implementation notes

* The index type of a matrix carries a `LinearOrder` and a `LocallyFiniteOrderBot`, because
  Gram–Schmidt orthonormalizes from left to right and so has to know which indices come earlier.
  Both hold for `Fin n`.
* `Numlib.LinearAlgebra.Matrix.QR` has the QR factorization as the existence statement
  `Matrix.exists_isThinQR`, with its uniqueness `Matrix.IsThinQR.unique`. An existence statement
  cannot be iterated, so the algorithm needs the factorization as a function of the matrix, which
  `Matrix.qrQ` and `Matrix.qrR` are. The two agree: both take $Q$ to be the Gram–Schmidt
  orthonormalization of the columns, and `Matrix.IsThinQR.unique` identifies them with any other
  factorization with positive diagonal, a product of Householder reflectors included. The reverse
  reading, `Matrix.euclideanCol_eq_gramSchmidtNormed_of_eq_mul`, is proved here: it is about the
  columns rather than the factors, and orthogonal iteration speaks of the columns.
* The hypothesis `IsUnit A.det` (nonsingularity) makes the QR decomposition unique, through the
  positivity of the diagonal of $R$. At a singular matrix a column can lie in the span of the
  earlier columns; the corresponding Gram–Schmidt vector is $0$, and
  `InnerProductSpace.gramSchmidtOrthonormalBasis` completes the family by an arbitrary choice. Every
  statement that identifies a factor assumes nonsingularity; the decomposition $A = QR$ itself does
  not.
* The standard basis vector $e_j$ is the $j$-th column `Matrix.euclideanCol 1 j` of the identity,
  and a matrix acts on `EuclideanSpace 𝕜 n` through `Matrix.toEuclideanLin`.
-/

open Filter Topology InnerProductSpace Submodule

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- Let $A$ be a linear operator on $E$ and let $(q_i)_{i \in \iota}$ be a family in $E$. The $k$-th
**orthogonal iterate** (simultaneous iterate) of $q$ is the family $(q^{(k)}_i)_i$ obtained by
Gram–Schmidt orthonormalization of $(A^k q_i)_i$ in the order of $\iota$.

Orthonormalizing after every step and orthonormalizing once at the end give the same family,
because Gram–Schmidt depends only on the flag of subspaces that its input spans. The definition
uses the second form, which has a closed form. The whole family is iterated at once so that each
initial segment iterates its own subspace (`Krylov.span_orthogonalIterate`). The definition is
`gramSchmidtNormed` of `fun i => (A ^ k) (q i)`; where $A^k q_i$ lies in the span of the earlier
vectors, $q^{(k)}_i = 0$. -/
noncomputable def orthogonalIterate (A : E →ₗ[𝕜] E) (q : ι → E) (k : ℕ) : ι → E :=
  gramSchmidtNormed 𝕜 fun i => (A ^ k) (q i)

/-- The orthogonal iterates span the iterated subspaces. Let $A$ be a linear operator on $E$, let
$(q_i)_{i \in \iota}$ be a family in $E$, and let $k \in \mathbb{N}$ and $m \in \iota$. Then
$$\operatorname{span}\{q^{(k)}_i : i \le m\} = A^k \operatorname{span}\{q_i : i \le m\},$$
where the right side is the $k$-th subspace iterate `Krylov.subspaceIterate` of the span of the
$q_i$ with $i \le m$. No independence of the family is assumed. -/
theorem span_orthogonalIterate (A : E →ₗ[𝕜] E) (q : ι → E) (k : ℕ) (m : ι) :
    span 𝕜 (orthogonalIterate A q k '' Set.Iic m) =
      subspaceIterate A (span 𝕜 (q '' Set.Iic m)) k := by
  simp only [orthogonalIterate, subspaceIterate]
  rw [span_gramSchmidtNormed, span_gramSchmidt_Iic, ← Submodule.span_image, Set.image_image]

/-- Let $A$ be a linear operator on $E$, let $(q_i)_{i \in \iota}$ be a family in $E$, and let
$J \subseteq \iota$ be a lower set. Then for every $k$
$$\operatorname{span}\{q^{(k)}_i : i \in J\} = A^k \operatorname{span}\{q_i : i \in J\}.$$

So the whole flag of subspaces, and not only one member of it, is iterated at once. -/
theorem span_orthogonalIterate_of_isLowerSet (A : E →ₗ[𝕜] E) (q : ι → E) (k : ℕ) {J : Set ι}
    (hJ : IsLowerSet J) :
    span 𝕜 (orthogonalIterate A q k '' J) = subspaceIterate A (span 𝕜 (q '' J)) k := by
  simp only [orthogonalIterate, subspaceIterate]
  rw [span_gramSchmidtNormed, span_gramSchmidt_of_isLowerSet _ hJ, ← Submodule.span_image,
    Set.image_image]

/-- Let $A$ be a linear operator on $E$ and $(q_i)_{i \in \iota}$ a family in $E$. If the family
$(A^k q_i)_i$ is linearly independent, then the orthogonal iterates $(q^{(k)}_i)_i$ form an
orthonormal family. -/
theorem orthonormal_orthogonalIterate {A : E →ₗ[𝕜] E} {q : ι → E} {k : ℕ}
    (h : LinearIndependent 𝕜 fun i => (A ^ k) (q i)) : Orthonormal 𝕜 (orthogonalIterate A q k) :=
  gramSchmidtNormed_orthonormal h

/-- If the family $q$ is orthonormal, then its orthogonal iterate at step $0$ is $q$ itself. -/
theorem orthogonalIterate_zero {A : E →ₗ[𝕜] E} {q : ι → E} (hq : Orthonormal 𝕜 q) :
    orthogonalIterate A q 0 = q := by
  have h0 : (fun i => (A ^ 0) (q i)) = q := by funext j; simp
  funext i
  simp only [orthogonalIterate, h0, gramSchmidtNormed,
    congrFun (gramSchmidt_of_orthogonal 𝕜 fun _ _ hab => hq.2 hab) i, hq.1 i]
  simp

/-!
### Convergence of orthogonal iteration

This section proves Theorem 7.19 of [kress1998numerical]. The gap bound
`Krylov.exists_gap_subspaceIterate_span_image_le`, applied to every initial segment of the flag,
says that the iterated subspaces converge to the invariant subspaces of the dominant eigenvalues.
The section adds that the compressions $Q_\nu^H A Q_\nu$ then converge to the upper triangular
matrix with the eigenvalues on the diagonal.

The two halves are `Krylov.norm_inner_le_of_gap`, for the entries below the diagonal, and
`Krylov.norm_inner_self_sub_le`, for the diagonal entries. Neither mentions the iteration: they are
statements about an orthonormal family whose initial segments are close to an invariant flag. In the
second, the eigenvalue enters through the Schur property $Ab - \lambda_j b \in T_{<j}$ of the
component $b$ of $q_j$ in $T_{\le j} \cap T_{<j}^\perp$.
-/

section Triangular

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $A$ be a linear operator on $E$ with $\|Ay\| \le M \|y\|$ for all $y$, where $M \ge 0$. Let
$T$ and $S$ be subspaces of $E$ that admit orthogonal projections, with $T$ invariant under $A$.
If $v \in S$ and $w \in S^\perp$ satisfy $\|v\| \le 1$ and $\|w\| \le 1$, then
$$|\langle w, Av \rangle| \le 2M \operatorname{gap}(T, S),$$
where $\operatorname{gap}(T, S) = \|P_T - P_S\|$ is `Submodule.gap`.

This bounds the entries below the diagonal of the compression of $A$ on an orthonormal family. -/
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

/-- Let $A$ be a linear operator on $E$ with $\|Ay\| \le M \|y\|$ for all $y$, where $M \ge 0$. Let
$T_< \subseteq T_\le$, $S$ and $S_<$ be subspaces of $E$ that admit orthogonal projections, and
let $\lambda \in \mathbb{K}$ satisfy $Ab - \lambda b \in T_<$ for every $b \in T_\le$. If $v$ is
a unit vector with $v \in S$ and $v \in S_<^\perp$, then
$$|\langle v, Av \rangle - \lambda| \le (M + |\lambda|)\,(g_< + g_\le)\,(2 + g_< + g_\le),$$
where $g_< = \operatorname{gap}(T_<, S_<)$ and $g_\le = \operatorname{gap}(T_\le, S)$.

This bounds the diagonal entries of the compression: the Rayleigh quotient of $v$ is close to
$\lambda$ once $S$ is close to $T_\le$ and $S_<$ is close to $T_<$. The subspaces $T_\le$,
$T_<$, $S$, $S_<$ are `Tle`, `Tlt`, `S`, `Slt`. -/
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
  gcongr

/-- Let $(x_j)_{j \in \iota}$ be eigenvectors of $A$, $A x_j = \lambda_j x_j$. For every set
$J \subseteq \iota$, the span of the $x_j$ with $j \in J$ is invariant under $A$. -/
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

/-- Let $(q_i)_{i \in \iota}$ be an orthonormal family, let $J \subseteq \iota$ and let
$j \notin J$. Then $q_j$ is orthogonal to the span of the $q_i$ with $i \in J$. -/
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

/-- Let $\iota$ be finite and let $(q_i)_{i \in \iota}$ and $(x_i)_{i \in \iota}$ be linearly
independent families. For every $J \subseteq \iota$, the span of the $q_i$ with $i \in J$ and
the span of the $x_i$ with $i \in J$ have the same dimension. -/
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
/-- The flag of iterated subspaces converges to the flag of dominant invariant subspaces. Let $E$ be
finite-dimensional and $\iota$ finite and linearly ordered. Let $(x_j)_{j \in \iota}$ be a basis
of $E$ of eigenvectors of $A$, $A x_j = \lambda_j x_j$, with $\lambda_j \neq 0$ for all $j$ and
$|\lambda_k| < |\lambda_j|$ for $j < k$. Let $(q^{(\nu)})_{\nu \in \mathbb{N}}$ be a sequence of
orthonormal families indexed by $\iota$ such that, for every lower set $J \subseteq \iota$ and
every $\nu$,
$$\operatorname{span}\{q^{(\nu)}_i : i \in J\} = A^\nu \operatorname{span}\{q^{(0)}_i : i \in
  J\},$$
and such that $\operatorname{span}\{q^{(0)}_i : i \in J\} \cap \operatorname{span}\{x_i : i
\notin J\} = \{0\}$ for every lower set $J$. Then for every lower set $J$
$$\operatorname{gap}\bigl(\operatorname{span}\{x_i : i \in J\}, \operatorname{span}\{q^{(\nu)}_i
  : i \in J\}\bigr) \to 0 \quad (\nu \to \infty).$$

The bound on the gap comes from `Krylov.exists_gap_subspaceIterate_span_image_le`. -/
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

/-- **Convergence of orthogonal iteration to triangular form.** Let $E$ be finite-dimensional and
$\iota$ finite and linearly ordered. Let $(x_j)_{j \in \iota}$ be a basis of $E$ of eigenvectors
of $A$, $A x_j = \lambda_j x_j$, with $\lambda_j \neq 0$ for all $j$ and
$|\lambda_k| < |\lambda_j|$ for $j < k$. Let $(q^{(\nu)})_{\nu \in \mathbb{N}}$ be a sequence of
orthonormal families indexed by $\iota$ such that, for every lower set $J \subseteq \iota$ and
every $\nu$,
$$\operatorname{span}\{q^{(\nu)}_i : i \in J\} = A^\nu \operatorname{span}\{q^{(0)}_i : i \in
  J\},$$
and such that $\operatorname{span}\{q^{(0)}_i : i \in J\} \cap \operatorname{span}\{x_i : i
\notin J\} = \{0\}$ for every lower set $J$. Then, as $\nu \to \infty$,
$$\langle q^{(\nu)}_j, A q^{(\nu)}_k \rangle \to 0 \quad (k < j), \qquad
  \langle q^{(\nu)}_j, A q^{(\nu)}_j \rangle \to \lambda_j.$$
This is Theorem 7.19 of [kress1998numerical].

The orthogonal iterates `Krylov.orthogonalIterate` satisfy the span hypothesis by
`Krylov.span_orthogonalIterate_of_isLowerSet`. The proof combines
`Krylov.tendsto_gap_span_image` with `Krylov.norm_inner_le_of_gap` and
`Krylov.norm_inner_self_sub_le`. -/
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
    simpa using (hgapJ (Set.Iic k) (IsLowerSet.Iic k)).const_mul (2 * M)
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
      simpa using (hgapJ (Set.Iio j) (IsLowerSet.Iio j)).add (hgapJ (Set.Iic j) (IsLowerSet.Iic j))
    have := ((hlim.const_mul (M + ‖l j‖)).mul ((tendsto_const_nhds (x := (2 : ℝ))).add hlim))
    simpa using this

end Triangular


end Krylov

namespace Matrix

open scoped ComplexOrder

section Column

variable {𝕜 : Type*} {n : Type*}

/-! ### Columns as Euclidean vectors -/

/-- The $j$-th column $A_{\cdot j}$ of a square matrix $A$, as a vector of `EuclideanSpace 𝕜 n`. -/
noncomputable def euclideanCol (A : Matrix n n 𝕜) (j : n) : EuclideanSpace 𝕜 n :=
  WithLp.toLp 2 (Aᵀ j)

/-- The $i$-th entry of the $j$-th column of $A$ is $A_{ij}$. -/
@[simp]
theorem euclideanCol_apply (A : Matrix n n 𝕜) (i j : n) :
    (euclideanCol A j).ofLp i = A i j := rfl

/-- A square matrix is determined by its columns. -/
theorem euclideanCol_injective :
    Function.Injective (euclideanCol : Matrix n n 𝕜 → n → EuclideanSpace 𝕜 n) := by
  intro A B h
  ext i j
  exact congrFun (congrArg WithLp.ofLp (congrFun h j)) i

end Column

section Ring

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix applied to a standard basis vector gives a column: $M e_j = M_{\cdot j}$. -/
theorem toEuclideanLin_euclideanCol_one (M : Matrix n n 𝕜) (j : n) :
    toEuclideanLin M (euclideanCol 1 j) = euclideanCol M j := by
  ext i
  simp [euclideanCol, toLpLin_apply, mulVec, dotProduct, Matrix.one_apply]

set_option linter.unusedDecidableInType false in
/-- The columns of a product: $(UT)_{\cdot j} = \sum_p T_{pj} U_{\cdot p}$. -/
theorem euclideanCol_mul (U T : Matrix n n 𝕜) (j : n) :
    euclideanCol (U * T) j = ∑ p, T p j • euclideanCol U p := by
  have h : euclideanCol (U * T) j = toEuclideanLin U (euclideanCol T j) := by
    ext i
    simp [euclideanCol, toLpLin_apply, mulVec, dotProduct, Matrix.mul_apply, mul_comm]
  rw [h, euclideanCol, toEuclideanLin_apply_eq_sum]
  rfl

/-- If $U^H U = I$, the columns of $U$ form an orthonormal family. -/
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
    Matrix.linearIndependent_col_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 hA)
  exact LinearIndependent.of_comp (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).toLinearMap h

/-- The columns of a nonsingular matrix $A \in \mathbb{K}^{n \times n}$ span $\mathbb{K}^n$. -/
theorem span_range_euclideanCol_eq_top {A : Matrix n n 𝕜} (hA : IsUnit A.det) :
    Submodule.span 𝕜 (Set.range (euclideanCol A)) = ⊤ :=
  (linearIndependent_euclideanCol hA).span_eq_top_of_card_eq_finrank'
    (by rw [finrank_euclideanSpace])

/-- Let $X$ be an invertible matrix with $X^{-1} A X = \operatorname{diag}(\lambda)$. Then the
$j$-th column $x_j$ of $X$ is an eigenvector of $A$: $A x_j = \lambda_j x_j$. -/
theorem toEuclideanLin_euclideanCol_of_conj_eq_diagonal {A X : Matrix n n 𝕜} (hX : IsUnit X)
    {lam : n → 𝕜} (hD : X⁻¹ * A * X = diagonal lam) (j : n) :
    toEuclideanLin A (euclideanCol X j) = lam j • euclideanCol X j := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hAX : A * X = X * diagonal lam := by
    rw [← hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.one_mul]
  have hcol : euclideanCol (diagonal lam) j = lam j • euclideanCol (1 : Matrix n n 𝕜) j := by
    ext i
    simp [euclideanCol, diagonal_apply, Matrix.one_apply]
  rw [← toEuclideanLin_euclideanCol_one, ← toEuclideanLin_mul_apply, hAX, toEuclideanLin_mul_apply,
    toEuclideanLin_euclideanCol_one, hcol, map_smul, toEuclideanLin_euclideanCol_one]

/-- Let $X$ be an invertible matrix with $X^{-1} A X = \operatorname{diag}(\lambda)$ and
$\lambda_i \neq 0$ for all $i$. Then $A$ is nonsingular. -/
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
/-- The $i$-th column of the identity matrix is the standard basis vector $e_i$. -/
theorem euclideanCol_one (i : n) :
    euclideanCol (1 : Matrix n n 𝕜) i = EuclideanSpace.single i 1 := by
  ext j
  simp [euclideanCol, Matrix.one_apply, PiLp.single_apply, eq_comm]

omit [Fintype n] in
/-- Let the index set be finite and let $S$ be a set of indices. A vector $v$ lies in
$\operatorname{span}\{e_i : i \in S\}$ if and only if $v_i = 0$ for every $i \notin S$. -/
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

/-- For a square matrix $A$ and a set $S$ of indices,
$$\operatorname{span}\{A_{\cdot i} : i \in S\} = A \operatorname{span}\{e_i : i \in S\}.$$
-/
theorem span_euclideanCol_eq_map (A : Matrix n n 𝕜) (S : Set n) :
    span 𝕜 (euclideanCol A '' S) =
      (span 𝕜 (euclideanCol (1 : Matrix n n 𝕜) '' S)).map (toEuclideanLin A) := by
  rw [Submodule.map_span, Set.image_image]
  simp only [toEuclideanLin_euclideanCol_one]


end Ring

/-!
### Shifted QR steps for arbitrary factorizations

The canonical steps `Matrix.shiftedQrStep` and `Matrix.qrIterate` below use one fixed QR
factorization, the Gram–Schmidt one with a positive diagonal. The textbook algorithms compute some
QR factorization, by Givens rotations or Householder reflectors and with their own signs. Their
specifications are therefore stated for any factorization: `Matrix.IsShiftedQrStep μ H H'` says that
$H'$ is one QR step from $H$ with shift $\mu$ for some factorization, and `Matrix.IsShiftedQrChain`
records a chain of steps together with its factors, as in (10.5.4) of [golub2013matrix].
-/

section ShiftedStep

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- Let $H, H' \in \mathbb{K}^{n \times n}$ and $\mu \in \mathbb{K}$. The matrix $H'$ is obtained
from $H$ by **one QR step with shift $\mu$** if there are a unitary $Q$ and an upper triangular
$R$ with
$$H - \mu I = QR, \qquad H' = RQ + \mu I.$$
This is (7.3.1) of [golub2013matrix] for $\mu = 0$, and (7.4.1) and (7.5.3) there.

Any QR factorization is allowed: no condition is put on the diagonal of $R$. -/
def IsShiftedQrStep (μ : 𝕜) (H H' : Matrix n n 𝕜) : Prop :=
  ∃ Q ∈ unitaryGroup n 𝕜, ∃ R : Matrix n n 𝕜, R.IsUpperTriangular ∧ H - μ • 1 = Q * R ∧
    H' = R * Q + μ • 1

omit [LinearOrder n] in
/-- **A QR step with a given unitary factor is a unitary similarity.** If $Q$ is unitary and
$H - \mu I = QR$ for some matrix $R$, then
$$RQ + \mu I = Q^H H Q.$$
No condition on $R$ is needed. This is the display after (7.5.3) of [golub2013matrix]. -/
theorem mul_add_smul_one_eq_star_mul_mul {μ : 𝕜} {H Q R : Matrix n n 𝕜}
    (hQ : Q ∈ unitaryGroup n 𝕜) (hQR : H - μ • 1 = Q * R) : R * Q + μ • 1 = star Q * H * Q := by
  have h1 : star Q * Q = 1 := (mem_unitaryGroup_iff').1 hQ
  have hR : R = star Q * (H - μ • 1) := by rw [hQR, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1,
    sub_add_cancel]

/-- Every shifted QR step is a unitary similarity: if $H'$ is a QR step from $H$ with shift $\mu$,
then $H' = Q^H H Q$ for some unitary $Q$. In the factorization $H - \mu I = QR$ of the step,
$RQ + \mu I = Q^H (QR + \mu I) Q$; this is the display after (7.5.3) of [golub2013matrix]. -/
theorem IsShiftedQrStep.eq_conj {μ : 𝕜} {H H' : Matrix n n 𝕜} (h : IsShiftedQrStep μ H H') :
    ∃ Q ∈ unitaryGroup n 𝕜, H' = star Q * H * Q := by
  obtain ⟨Q, hQ, R, -, hQR, rfl⟩ := h
  exact ⟨Q, hQ, mul_add_smul_one_eq_star_mul_mul hQ hQR⟩

/-- Let $H_1$ and $H_2$ be QR steps from $H$ with the same shift $\mu$, and let $H - \mu I$ be
nonsingular. Then there is $d \in \mathbb{K}^n$ with $|d_i| = 1$ for all $i$ such that, with
$D = \operatorname{diag}(d)$,
$$H_2 = D^H H_1 D.$$

The two QR factorizations $Q_1 R_1 = Q_2 R_2$ of $H - \mu I$ differ by a unimodular diagonal
matrix: $Q_1^H Q_2 = R_1 R_2^{-1}$ is unitary and upper triangular, hence diagonal. -/
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
  · refine CStarRing.norm_of_mem_unitary (Unitary.mem_iff_star_mul_self.2 ?_)
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

/-- Let $M$, $Q$ and $T$ be square matrices over a commutative ring, with $M$ upper Hessenberg,
$\det M$ a unit and $T$ upper triangular. If $M = QT$, then $Q$ is upper Hessenberg.

Here $T$ is invertible and $Q = M T^{-1}$ is a Hessenberg matrix times an upper triangular one;
see [golub2013matrix] §7.4.2 and [quarteroni2000numerical] §5.6.3. -/
theorem IsUpperHessenberg.isUpperHessenberg_of_eq_mul {R : Type*} [CommRing R]
    {M Q T : Matrix n n R} (hM : M.IsUpperHessenberg) (hdet : IsUnit M.det)
    (hT : T.IsUpperTriangular) (hMQT : M = Q * T) : Q.IsUpperHessenberg := by
  have hTu : IsUnit T.det := by
    rw [hMQT, det_mul] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  rw [← mul_nonsing_inv_cancel_right T Q hTu, ← hMQT]
  exact hM.mul_isUpperTriangular hT.inv

/-- Hessenberg form survives a nonsingular shifted QR step, for any factorization. Let $H$ be upper
Hessenberg and let $H - \mu I$ be nonsingular. Then every QR step $H'$ from $H$ with shift $\mu$
is upper Hessenberg ([golub2013matrix] §7.4.2).

In the factorization $H - \mu I = QR$ of the step, $Q = (H - \mu I) R^{-1}$ is upper Hessenberg
by `Matrix.IsUpperHessenberg.isUpperHessenberg_of_eq_mul`, and so is $RQ + \mu I$. -/
theorem IsShiftedQrStep.isUpperHessenberg {μ : 𝕜} {H H' : Matrix n n 𝕜}
    (h : IsShiftedQrStep μ H H') (hH : H.IsUpperHessenberg) (hdet : IsUnit (H - μ • 1).det) :
    H'.IsUpperHessenberg := by
  obtain ⟨Q, -, R, hR, hQR, rfl⟩ := h
  exact (hR.mul_isUpperHessenberg ((hH.sub_smul_one μ).isUpperHessenberg_of_eq_mul hdet hR
    hQR)).add_smul_one μ

/-- **An exact shift deflates in one step.** Let $H \in \mathbb{K}^{n \times n}$, $n = N + 1$, be
unreduced upper Hessenberg, let $\mu$ be an eigenvalue of $H$, and let $H'$ be a QR step from
$H$ with shift $\mu$. Then the last row of $H'$ is $\mu e_n^T$: $h'_{nj} = 0$ for $j \neq n$ and
$h'_{nn} = \mu$. This is Theorem 7.5.1 of [golub2013matrix].

In $H - \mu I = QR$ the leading $N \times N$ block of $R$ is nonsingular: deleting the first row
and the last column of $H - \mu I$ leaves an upper triangular block whose diagonal is the
nonzero subdiagonal of $H$, and this block is $Q(2{:}n, 1{:}N)\, R(1{:}N, 1{:}N)$. Then
$\det(H - \mu I) = 0$ forces $r_{nn} = 0$, so the last row of $R$, and hence of $RQ$, is zero.
The index $n$ is `Fin.last N`, and "eigenvalue" is membership in `spectrum 𝕜 H`. -/
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
    rw [hM, submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
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
  rw [Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero fun l _ => by rw [hrow l, zero_mul],
      zero_add,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hj : j = Fin.last N
  · subst hj
    simp
  · rw [one_apply_ne (Ne.symm hj), mul_zero]
    exact (ite_eq_right_iff.2 fun h => absurd h hj).symm

end ShiftedStep

/-!
### Orthogonal iteration for arbitrary thin QR factorizations

`Krylov.orthogonalIterate` uses one orthonormalization, Gram–Schmidt. The textbook statement of
orthogonal iteration ((7.3.6) and (8.2.8) of [golub2013matrix]) factors $Z_k = A Q_{k-1} = Q_k R_k$
by some thin QR factorization, so its specification is a relation between consecutive blocks,
`Matrix.IsOrthogonalIterationStep A Q Q'`. Such a step always exists
(`Matrix.exists_isOrthogonalIterationStep`). Under full column rank it iterates subspaces
(`Matrix.IsOrthogonalIterationStep.range_eq`,
`Matrix.range_eq_subspaceIterate_of_isOrthogonalIterationStep`), and a square step is one unshifted
QR step (`Matrix.IsOrthogonalIterationStep.isShiftedQrStep`).
-/

section OrthogonalIteration

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] {r : ℕ}

/-- Let $A \in \mathbb{K}^{m \times m}$ and $Q, Q' \in \mathbb{K}^{m \times r}$. The block $Q'$ is
**one step of orthogonal iteration** (simultaneous or subspace iteration) from $Q$ if $Q'$ is
the orthonormal factor of a thin QR factorization
$$AQ = Q'R, \qquad Q'^H Q' = I, \qquad R \in \mathbb{K}^{r \times r} \text{ upper triangular}.$$
This is (7.3.6) and (8.2.8) of [golub2013matrix].

Every factorization is allowed (Gram–Schmidt, Householder, Givens, any signs); the Gram–Schmidt
iterates `Krylov.orthogonalIterate` are one instance. A sequence
$Q_0, Q_1, \dots \in \mathbb{K}^{m \times r}$ is an orthogonal iteration when $Q_0^H Q_0 = I$
and every consecutive pair is a step. The thin factorization is `Matrix.IsThinQR`. -/
def IsOrthogonalIterationStep (A : Matrix m m 𝕜) (Q Q' : Matrix m (Fin r) 𝕜) : Prop :=
  ∃ R, IsThinQR (A * Q) Q' R

/-- **Every block has a next step of orthogonal iteration.** Let $A \in \mathbb{K}^{n \times n}$ and
$Q \in \mathbb{K}^{n \times r}$ with $r \le n$. Then there is a step $Q'$ of orthogonal
iteration from $Q$. No rank condition on $AQ$ is needed, so an orthogonal iteration exists from
every $Q_0$ with orthonormal columns.

The full QR factorization of $AQ$ exists (`Matrix.exists_isQR`), and the first $r$ columns of
its orthogonal factor and the first $r$ rows of its triangular factor form a thin one
(`Matrix.IsQR.isThinQR`). -/
theorem exists_isOrthogonalIterationStep {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜)
    (Q : Matrix (Fin n) (Fin r) 𝕜) (hr : r ≤ n) : ∃ Q', IsOrthogonalIterationStep A Q Q' := by
  obtain ⟨Q₀, R₀, h⟩ := exists_isQR (A * Q)
  exact ⟨_, _, h.isThinQR hr⟩

variable [DecidableEq m]

/-- **Orthogonal iteration iterates subspaces.** Let $Q'$ be a step of orthogonal iteration from $Q$
for $A$, and let $AQ$ have linearly independent columns. Then
$$\operatorname{ran} Q' = A \operatorname{ran} Q.$$
This is the statement $\operatorname{ran}(Q_k) = A \operatorname{ran}(Q_{k-1})$ of
[golub2013matrix] §7.3.2.

The triangular factor $R$ of $AQ = Q'R$ is nonsingular, so $\operatorname{ran} Q' =
\operatorname{ran}(Q'R) = \operatorname{ran}(AQ)$. The range of a matrix is the range of
`Matrix.toEuclideanLin`. -/
theorem IsOrthogonalIterationStep.range_eq {A : Matrix m m 𝕜} {Q Q' : Matrix m (Fin r) 𝕜}
    (h : IsOrthogonalIterationStep A Q Q') (hAQ : LinearIndependent 𝕜 (A * Q)ᵀ) :
    LinearMap.range (toEuclideanLin Q') =
      (LinearMap.range (toEuclideanLin Q)).map (toEuclideanLin A) := by
  obtain ⟨R, hR⟩ := h
  rw [← LinearMap.range_comp, ← toEuclideanLin_mul, ← hR.mul_eq, toEuclideanLin_mul,
    LinearMap.range_comp_of_range_eq_top _
      (range_toEuclideanLin_eq_top_of_isUnit (hR.isUnit_of_linearIndependent hAQ))]

/-- **The accumulated triangular factor of orthogonal iteration.** Let
$Q_0, Q_1, \dots \in \mathbb{K}^{m \times r}$ be such that $Q_{k+1}$ is a step of orthogonal
iteration from $Q_k$ for $A$ for every $k$, and let $A^K Q_0$ have linearly independent columns.
Then there is a nonsingular upper triangular $S \in \mathbb{K}^{r \times r}$ with
$$A^K Q_0 = Q_K S.$$
This is the first display of the proof of Theorem 7.3.1 in the appendix of [golub2013matrix].

The matrix $S$ is the product $R_K \cdots R_1$ of the triangular factors of the steps. Each
$A Q_k = A^{k+1} Q_0 S_k^{-1}$ has full column rank, which makes the factor $R_{k+1}$
nonsingular. -/
theorem exists_pow_mul_eq_mul_of_isOrthogonalIterationStep {A : Matrix m m 𝕜}
    {Q : ℕ → Matrix m (Fin r) 𝕜} (hQ : ∀ k, IsOrthogonalIterationStep A (Q k) (Q (k + 1)))
    {K : ℕ} (hK : LinearIndependent 𝕜 (A ^ K * Q 0)ᵀ) :
    ∃ S : Matrix (Fin r) (Fin r) 𝕜, IsUnit S ∧ S.IsUpperTriangular ∧ A ^ K * Q 0 = Q K * S := by
  have hinj : ∀ j ≤ K, Function.Injective (A ^ j * Q 0).mulVec := fun j hj x y hxy => by
    have h := mulVec_injective_iff.2 hK
    rw [← Nat.sub_add_cancel hj, pow_add, Matrix.mul_assoc] at h
    apply h
    simp only [← mulVec_mulVec] at hxy ⊢
    rw [hxy]
  have key : ∀ k ≤ K, ∃ S : Matrix (Fin r) (Fin r) 𝕜,
      IsUnit S ∧ S.IsUpperTriangular ∧ A ^ k * Q 0 = Q k * S := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, isUnit_one, blockTriangular_one, by rw [pow_zero, Matrix.one_mul, Matrix.mul_one]⟩
    | succ k ih =>
      intro hk
      obtain ⟨S, hS, hSt, hSeq⟩ := ih (by omega)
      obtain ⟨R, hR⟩ := hQ k
      have hAQS : A * Q k * S = A ^ (k + 1) * Q 0 := by
        rw [Matrix.mul_assoc, ← hSeq, ← Matrix.mul_assoc, ← pow_succ']
      have hRu : IsUnit R := by
        refine hR.isUnit_of_linearIndependent (mulVec_injective_iff.1 ?_)
        intro x y hxy
        obtain ⟨x', rfl⟩ := mulVec_surjective_iff_isUnit.2 hS x
        obtain ⟨y', rfl⟩ := mulVec_surjective_iff_isUnit.2 hS y
        suffices x' = y' by rw [this]
        apply hinj (k + 1) hk
        rw [← hAQS]
        simp only [← mulVec_mulVec] at hxy ⊢
        exact hxy
      refine ⟨R * S, hRu.mul hS, BlockTriangular.mul hR.isUpperTriangular hSt, ?_⟩
      rw [← hAQS, ← hR.mul_eq, Matrix.mul_assoc]
  exact key K le_rfl

/-- **Orthogonal iteration computes the iterated subspace.** Let
$Q_0, Q_1, \dots \in \mathbb{K}^{m \times r}$ be such that $Q_{k+1}$ is a step of orthogonal
iteration from $Q_k$ for $A$ for every $k$, and let $A^K Q_0$ have linearly independent columns.
Then
$$\operatorname{ran} Q_K = A^K \operatorname{ran} Q_0,$$
the $K$-th subspace iterate `Krylov.subspaceIterate` of $\operatorname{ran} Q_0$
([golub2013matrix] §7.3.2).

For the Gram–Schmidt iterates the same fact is `Krylov.span_orthogonalIterate`. -/
theorem range_eq_subspaceIterate_of_isOrthogonalIterationStep {A : Matrix m m 𝕜}
    {Q : ℕ → Matrix m (Fin r) 𝕜} (hQ : ∀ k, IsOrthogonalIterationStep A (Q k) (Q (k + 1)))
    {K : ℕ} (hK : LinearIndependent 𝕜 (A ^ K * Q 0)ᵀ) :
    LinearMap.range (toEuclideanLin (Q K)) =
      Krylov.subspaceIterate (toEuclideanLin A) (LinearMap.range (toEuclideanLin (Q 0))) K := by
  obtain ⟨S, hS, -, hSeq⟩ := exists_pow_mul_eq_mul_of_isOrthogonalIterationStep hQ hK
  rw [Krylov.subspaceIterate, ← LinearMap.range_comp, ← toEuclideanLin_pow, ← toEuclideanLin_mul,
    hSeq, toEuclideanLin_mul,
    LinearMap.range_comp_of_range_eq_top _ (range_toEuclideanLin_eq_top_of_isUnit hS)]

/-- **A square step of orthogonal iteration is an unshifted QR step.** Let
$A, Q, Q' \in \mathbb{K}^{n \times n}$ with $Q$ unitary, and let $Q'$ be a step $AQ = Q'R$ of
orthogonal iteration from $Q$. Then $T' = Q'^H A Q'$ is a QR step from $T = Q^H A Q$ with shift
$0$. This is [golub2013matrix] §7.3.3, where (7.3.1) is derived from (7.3.6), and §8.2.5.

The step has the unitary factor $Q^H Q'$: $T = (Q^H Q') R$ and $T' = R (Q^H Q')$. The matrix
$Q'$ is unitary because it is square with orthonormal columns. -/
theorem IsOrthogonalIterationStep.isShiftedQrStep {n : ℕ} {A Q Q' : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ unitaryGroup (Fin n) 𝕜) (h : IsOrthogonalIterationStep A Q Q') :
    IsShiftedQrStep 0 (Qᴴ * A * Q) (Q'ᴴ * A * Q') := by
  obtain ⟨R, hR⟩ := h
  have hQ' : Q' ∈ unitaryGroup (Fin n) 𝕜 := mem_unitaryGroup_iff'.2 hR.conjTranspose_mul_self
  have hQQ : Q * Qᴴ = 1 := mem_unitaryGroup_iff.1 hQ
  have hA : A = Q' * R * Qᴴ := by rw [hR.mul_eq, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  refine ⟨Qᴴ * Q', Submonoid.mul_mem _ (Unitary.star_mem hQ) hQ', R, hR.isUpperTriangular, ?_, ?_⟩
  · rw [zero_smul, sub_zero, Matrix.mul_assoc, ← hR.mul_eq, Matrix.mul_assoc]
  · rw [zero_smul, add_zero, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q'ᴴ Q', hR.conjTranspose_mul_self, Matrix.one_mul]

end OrthogonalIteration

section Chain

variable {𝕜 : Type*} [CommRing 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Let $H_i, V_i, R_i$ be square matrices over a commutative ring and $\mu_i$ scalars, for
$i \in \mathbb{N}$, and let $p \in \mathbb{N}$. They form a **chain of $p$ shifted QR steps with
explicit factors** if for every $i < p$
$$H_i - \mu_i I = V_i R_i, \qquad H_{i+1} = R_i V_i + \mu_i I.$$
This is the loop (10.5.4) of [golub2013matrix].

The definition requires neither unitarity of the $V_i$ nor triangularity of the $R_i$; each
theorem adds what it uses. The loop (10.5.4) is printed with the range $i = 0{:}p$; the intended
range is $i = 1{:}p$. -/
structure IsShiftedQrChain (H V R : ℕ → Matrix n n 𝕜) (μ : ℕ → 𝕜) (p : ℕ) : Prop where
  /-- For every $i < p$, $H_i - \mu_i I = V_i R_i$. -/
  sub_eq : ∀ i < p, H i - μ i • 1 = V i * R i
  /-- For every $i < p$, $H_{i+1} = R_i V_i + \mu_i I$. -/
  succ_eq : ∀ i < p, H (i + 1) = R i * V i + μ i • 1

namespace IsShiftedQrChain

variable {H V R : ℕ → Matrix n n 𝕜} {μ : ℕ → 𝕜} {p : ℕ}

/-- A chain of length $p$ is a chain of every length $q \le p$. -/
theorem mono (h : IsShiftedQrChain H V R μ p) {q : ℕ} (hq : q ≤ p) :
    IsShiftedQrChain H V R μ q :=
  ⟨fun i hi => h.sub_eq i (by omega), fun i hi => h.succ_eq i (by omega)⟩

/-- In a chain of length $p$, $H_i V_i = V_i H_{i+1}$ for every $i < p$. -/
theorem mul_eq_mul_succ (h : IsShiftedQrChain H V R μ p) {i : ℕ} (hi : i < p) :
    H i * V i = V i * H (i + 1) := by
  rw [h.succ_eq i hi, Matrix.mul_add, ← Matrix.mul_assoc, ← h.sub_eq i hi, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_add_cancel]

/-- In a chain of length $p$, $H_0 V_{<p} = V_{<p} H_p$, where $V_{<p} = V_0 V_1 \cdots V_{p-1}$. -/
theorem mul_prod (h : IsShiftedQrChain H V R μ p) :
    H 0 * ((List.range p).map V).prod = ((List.range p).map V).prod * H p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, ← Matrix.mul_assoc, ih (h.mono p.le_succ), Matrix.mul_assoc,
      h.mul_eq_mul_succ (lt_add_one p), ← Matrix.mul_assoc]

end IsShiftedQrChain

/-- **The product identity of a chain of shifted QR steps.** For a chain of length $p$,
$$(V_0 V_1 \cdots V_{p-1})(R_{p-1} \cdots R_1 R_0) = \prod_{i < p} (H_0 - \mu_i I).$$
This is (7.5.7), P7.5.5 and Theorem 10.5.1 of [golub2013matrix].

No unitarity or triangularity is used. The proof uses
$V_{<p}(H_p - \mu_p I) = (H_0 - \mu_p I) V_{<p}$, from `Matrix.IsShiftedQrChain.mul_prod`, and
the fact that the factors $H_0 - \mu_i I$ commute. The products are list products over
`List.range p`. -/
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

/-- Let the scalars form a commutative ring with an involution, and let $V_i$ be unitary for every
$i < p$. Then $V_{<p} = V_0 \cdots V_{p-1}$ is unitary and
$$H_p = V_{<p}^H H_0 V_{<p}.$$
This is (10.5.6) of [golub2013matrix]. -/
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

/-- Hessenberg form along a chain. Let the index set be linearly ordered. If $H_0$ is upper
Hessenberg, and $R_i$ is upper triangular and $V_i$ upper Hessenberg for every $i < p$, then
$H_i$ is upper Hessenberg for every $i \le p$. This is the statement "each $H^{(i)}$ is upper
Hessenberg" of [golub2013matrix] §10.5.3. -/
theorem isUpperHessenberg [LinearOrder n] (h : IsShiftedQrChain H V R μ p)
    (h0 : (H 0).IsUpperHessenberg) (hR : ∀ i < p, (R i).IsUpperTriangular)
    (hV : ∀ i < p, (V i).IsUpperHessenberg) : ∀ i ≤ p, (H i).IsUpperHessenberg := by
  intro i hi
  induction i with
  | zero => exact h0
  | succ i ih =>
    rw [h.succ_eq i (by omega)]
    exact ((hR i (by omega)).mul_isUpperHessenberg (hV i (by omega))).add_smul_one _

/-- Let the index set be linearly ordered. If $V_i$ is upper Hessenberg for every $i < p$, then
$V_{<p} = V_0 \cdots V_{p-1}$ has lower bandwidth $p$: its entry $(i, j)$ vanishes when more
than $p$ indices lie in $[j, i)$, that is, when $i > j + p$ for `Fin N`. This is the statement
$V(m, 1{:}m-p-1) = 0$ of [golub2013matrix] §10.5.3. -/
theorem hasLowerBandwidth_prod [LinearOrder n] (hV : ∀ i < p, (V i).IsUpperHessenberg) :
    (((List.range p).map V).prod).HasLowerBandwidth p := by
  induction p with
  | zero => exact hasLowerBandwidth_zero_iff.2 (by simpa using blockTriangular_one)
  | succ p ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
    exact (ih fun i hi => hV i (by omega)).mul
      (isUpperHessenberg_iff_hasLowerBandwidth_one.1 (hV p (lt_add_one p)))

/-- The first column of the accumulated factor. Let the index set be linearly ordered with a least
index, and let $e_1$ be the standard basis vector of that index. If $R_i$ is upper triangular
for every $i < p$, then
$$\Bigl(\prod_{i < p} (H_0 - \mu_i I)\Bigr) e_1 = (R_{<p})_{11}\, V_{<p} e_1,$$
where $V_{<p} = V_0 \cdots V_{p-1}$ and $R_{<p} = R_{p-1} \cdots R_0$.

This is the statement "$V(:,1) = p(H_c) e_1$ with $c = 1/R(1,1)$" of [golub2013matrix] §10.5.3,
written without the division. The least index is `⊥`. -/
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

/-- **Existence of Givens chains for arbitrary shifts.** Let $H \in \mathbb{R}^{m \times m}$ be
upper Hessenberg and let $(\mu_i)_{i \in \mathbb{N}}$ be real shifts. Then there are matrices
$H_i$, $V_i$, $R_i$ with $H_0 = H$ that form a chain of shifted QR steps of every length, such
that for every $i$ the matrix $V_i$ is orthogonal and upper Hessenberg, $R_i$ is upper
triangular and $H_i$ is upper Hessenberg. This is (10.5.4) of [golub2013matrix] with the Givens
QR factorization.

No nonsingularity is needed, so exact shifts are allowed. The factors come from the Givens QR
factorization `Matrix.hessenbergGivensQR`. -/
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

/-- If $V_i$ is unitary and $R_i$ upper triangular for every $i < p$, then for every $i < p$ the
matrix $H_{i+1}$ is a QR step from $H_i$ with shift $\mu_i$ in the sense of
`Matrix.IsShiftedQrStep`. -/
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

/-- The orthonormal basis of $\mathbb{K}^n$ obtained by Gram–Schmidt from the columns of $A$, in the
order of the index set. Where a column lies in the span of the earlier ones,
`InnerProductSpace.gramSchmidtOrthonormalBasis` completes the family by an arbitrary choice. Its
vectors are the columns of the unitary factor `Matrix.qrQ A`. -/
noncomputable def qrBasis (A : Matrix n n 𝕜) : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  gramSchmidtOrthonormalBasis finrank_euclideanSpace (euclideanCol A)

/-- The **unitary factor** $Q$ of the QR decomposition of a square matrix $A$: the $j$-th column of
$Q$ is the $j$-th vector $q_j$ of the Gram–Schmidt basis `Matrix.qrBasis A` of the columns of
$A$.

Mathlib has no QR decomposition. This one, with `Matrix.qrR`, is normalized so that $R$ has a
positive diagonal when $A$ is nonsingular (`Matrix.qrR_diag_pos`). This makes it unique and lets
it be recognized inside a product. -/
noncomputable def qrQ (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (qrBasis A).toBasis

/-- The **upper triangular factor** $R$ of the QR decomposition of a square matrix $A$: the matrix
of coordinates of the columns of $A$ in the orthonormal basis `Matrix.qrBasis A`, so that
$R_{ij} = \langle q_i, A_{\cdot j} \rangle$. -/
noncomputable def qrR (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (qrBasis A).toBasis.toMatrix (euclideanCol A)

omit [DecidableEq n] in
/-- **The QR decomposition.** Every square matrix $A$ satisfies $A = QR$, where $Q$ is
`Matrix.qrQ A` and $R$ is `Matrix.qrR A`. No nonsingularity is needed. -/
theorem qrQ_mul_qrR (A : Matrix n n 𝕜) : qrQ A * qrR A = A := by
  rw [qrQ, qrR, Module.Basis.toMatrix_mul_toMatrix]
  ext i j
  simp [Module.Basis.toMatrix]

/-- The factor $Q$ = `Matrix.qrQ A` of every square matrix $A$ is unitary. -/
theorem qrQ_mem_unitaryGroup (A : Matrix n n 𝕜) : qrQ A ∈ Matrix.unitaryGroup n 𝕜 :=
  (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary (qrBasis A)

omit [DecidableEq n] in
/-- The factor $R$ = `Matrix.qrR A` of every square matrix $A$ is upper triangular. -/
theorem isUpperTriangular_qrR (A : Matrix n n 𝕜) : (qrR A).IsUpperTriangular :=
  gramSchmidtOrthonormalBasis_inv_isUpperTriangular _ _

omit [DecidableEq n] in
/-- The $j$-th column of `Matrix.qrQ A` is the $j$-th vector of `Matrix.qrBasis A`. -/
theorem euclideanCol_qrQ (A : Matrix n n 𝕜) (j : n) : euclideanCol (qrQ A) j = qrBasis A j := by
  ext i
  simp [euclideanCol, qrQ, Module.Basis.toMatrix]

omit [DecidableEq n] in
/-- The entries of the triangular factor are $R_{ij} = \langle q_i, A_{\cdot j} \rangle$, where
$q_i$ is the $i$-th vector of `Matrix.qrBasis A`. -/
theorem qrR_apply (A : Matrix n n 𝕜) (i j : n) :
    qrR A i j = inner 𝕜 (qrBasis A i) (euclideanCol A j) := by
  simp [qrR, Module.Basis.toMatrix, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]

/-- Let $A$ be nonsingular. Then every diagonal entry $R_{jj}$ of $R$ = `Matrix.qrR A` is real and
positive: it is the norm of the $j$-th unnormalized Gram–Schmidt vector. This normalization
makes the QR decomposition unique.

In $\mathbb{K}$, the inequality $0 < z$ means that $z$ is real and positive. -/
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

/-- **Uniqueness of the QR decomposition**, in the form that the QR algorithm needs. Let $M = UT$,
where $U^H U = I$ and $T$ is upper triangular with real positive diagonal entries. Then the
columns of $U$ are the Gram–Schmidt orthonormalization of the columns of $M$: for every $j$, the
$j$-th column of $U$ is the $j$-th vector of `gramSchmidtNormed` applied to the columns of $M$.

This identifies the accumulated unitary factor of the QR algorithm with orthogonal iteration on
the standard basis, and it is where the normalization of `Matrix.qrR` is used. -/
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

/-- **The QR algorithm.** The iterates of a square matrix $A$ are $A_0 = A$ and $A_{k+1} = R_k Q_k$,
where $A_k = Q_k R_k$ is the QR decomposition by `Matrix.qrQ` and `Matrix.qrR`. -/
noncomputable def qrIterate (A : Matrix n n 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => A
  | k + 1 => qrR (qrIterate A k) * qrQ (qrIterate A k)

/-- The **accumulated unitary factor** $\tilde Q_k = Q_0 Q_1 \cdots Q_{k-1}$ of the QR algorithm,
with $\tilde Q_0 = I$. -/
noncomputable def qrAccum (A : Matrix n n 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => 1
  | k + 1 => qrAccum A k * qrQ (qrIterate A k)

/-- The **accumulated triangular factor** $\tilde R_k = R_{k-1} \cdots R_1 R_0$ of the QR algorithm,
with $\tilde R_0 = I$. -/
noncomputable def qrTriangle (A : Matrix n n 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => 1
  | k + 1 => qrR (qrIterate A k) * qrTriangle A k

omit [DecidableEq n] in
/-- The QR iteration starts at $A_0 = A$. -/
@[simp]
theorem qrIterate_zero (A : Matrix n n 𝕜) : qrIterate A 0 = A := rfl

omit [DecidableEq n] in
/-- One QR step: $A_{k+1} = R_k Q_k$, where $A_k = Q_k R_k$ is the QR decomposition. -/
theorem qrIterate_succ (A : Matrix n n 𝕜) (k : ℕ) :
    qrIterate A (k + 1) = qrR (qrIterate A k) * qrQ (qrIterate A k) := rfl

/-- The accumulated unitary factor starts at $\tilde Q_0 = I$. -/
@[simp]
theorem qrAccum_zero (A : Matrix n n 𝕜) : qrAccum A 0 = 1 := rfl

/-- The accumulated unitary factor satisfies $\tilde Q_{k+1} = \tilde Q_k Q_k$. -/
theorem qrAccum_succ (A : Matrix n n 𝕜) (k : ℕ) :
    qrAccum A (k + 1) = qrAccum A k * qrQ (qrIterate A k) := rfl

/-- The accumulated triangular factor starts at $\tilde R_0 = I$. -/
@[simp]
theorem qrTriangle_zero (A : Matrix n n 𝕜) : qrTriangle A 0 = 1 := rfl

/-- The accumulated triangular factor satisfies $\tilde R_{k+1} = R_k \tilde R_k$. -/
theorem qrTriangle_succ (A : Matrix n n 𝕜) (k : ℕ) :
    qrTriangle A (k + 1) = qrR (qrIterate A k) * qrTriangle A k := rfl

/-- Each QR iterate $A_{k+1}$ is a QR step from $A_k$ with shift $0$ in the sense of
`Matrix.IsShiftedQrStep`. -/
theorem isShiftedQrStep_qrIterate (A : Matrix n n 𝕜) (k : ℕ) :
    IsShiftedQrStep 0 (qrIterate A k) (qrIterate A (k + 1)) :=
  ⟨qrQ _, qrQ_mem_unitaryGroup _, qrR _, isUpperTriangular_qrR _,
    by rw [zero_smul, sub_zero, qrQ_mul_qrR], by rw [zero_smul, add_zero, qrIterate_succ]⟩

/-- The QR iterates $A_k$, with the factors $Q_k$ and $R_k$ and the shifts $\mu_k = 0$, form a chain
of shifted QR steps of every length $p$. -/
theorem isShiftedQrChain_qrIterate (A : Matrix n n 𝕜) (p : ℕ) :
    IsShiftedQrChain (qrIterate A) (fun k => qrQ (qrIterate A k)) (fun k => qrR (qrIterate A k))
      (fun _ => 0) p :=
  ⟨fun _ _ => by rw [zero_smul, sub_zero, qrQ_mul_qrR], fun _ _ => by rw [zero_smul, add_zero]; rfl⟩

/-- The accumulated unitary factor is the product $\tilde Q_k = Q_0 Q_1 \cdots Q_{k-1}$ of the
factors of the chain, a list product over `List.range k`. -/
theorem qrAccum_eq_prod (A : Matrix n n 𝕜) (k : ℕ) :
    qrAccum A k = ((List.range k).map fun i => qrQ (qrIterate A i)).prod := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qrAccum_succ, ih, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]

/-- The accumulated triangular factor is the product $\tilde R_k = R_{k-1} \cdots R_0$ of the
factors of the chain, a list product over the reverse of `List.range k`. -/
theorem qrTriangle_eq_prod (A : Matrix n n 𝕜) (k : ℕ) :
    qrTriangle A k = ((List.range k).reverse.map fun i => qrR (qrIterate A i)).prod := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qrTriangle_succ, ih, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.prod_cons]

/-- The accumulated unitary factor $\tilde Q_k$ of the QR algorithm is unitary. -/
theorem qrAccum_mem_unitaryGroup (A : Matrix n n 𝕜) (k : ℕ) :
    qrAccum A k ∈ Matrix.unitaryGroup n 𝕜 := by
  induction k with
  | zero => rw [qrAccum_zero]; exact one_mem _
  | succ k ih => exact mul_mem ih (qrQ_mem_unitaryGroup _)

/-- The accumulated unitary factor satisfies $\tilde Q_k^H \tilde Q_k = I$. -/
theorem conjTranspose_mul_qrAccum (A : Matrix n n 𝕜) (k : ℕ) :
    (qrAccum A k)ᴴ * qrAccum A k = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff'.1 (qrAccum_mem_unitaryGroup A k)

/-- The accumulated unitary factor satisfies $\tilde Q_k \tilde Q_k^H = I$. -/
theorem qrAccum_mul_conjTranspose (A : Matrix n n 𝕜) (k : ℕ) :
    qrAccum A k * (qrAccum A k)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff.1 (qrAccum_mem_unitaryGroup A k)

/-- The unitary factor $Q$ of the QR decomposition satisfies $Q^H Q = I$. -/
theorem conjTranspose_qrQ_mul_self (A : Matrix n n 𝕜) : (qrQ A)ᴴ * qrQ A = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff'.1 (qrQ_mem_unitaryGroup A)

/-- Let $A \in \mathbb{K}^{N \times N}$ be upper triangular with real positive diagonal entries.
Then its QR decomposition is $Q = I$ and $R = A$.

The proof uses the uniqueness of the QR factorization, `Matrix.IsThinQR.unique`. -/
theorem qrQ_eq_one_of_isUpperTriangular {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsUpperTriangular) (hd : ∀ j, 0 < A j j) : qrQ A = 1 ∧ qrR A = A := by
  have hdet : IsUnit A.det := by
    rw [det_of_isUpperTriangular hA]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.2 fun j _ => (hd j).ne')
  exact IsThinQR.unique ⟨qrQ_mul_qrR A, conjTranspose_qrQ_mul_self A, isUpperTriangular_qrR A⟩
    ⟨Matrix.one_mul A, by simp, hA⟩ (qrR_diag_pos hdet) hd

set_option linter.unusedDecidableInType false in
/-- The triangular factor of the QR decomposition $A = QR$ is $R = Q^H A$. -/
theorem qrR_eq (A : Matrix n n 𝕜) : qrR A = (qrQ A)ᴴ * A := by
  have h : (qrQ A)ᴴ * A = (qrQ A)ᴴ * (qrQ A * qrR A) := by rw [qrQ_mul_qrR]
  rw [h, ← Matrix.mul_assoc, conjTranspose_qrQ_mul_self, Matrix.one_mul]

/-- The $k$-th QR iterate is $A$ conjugated by the accumulated unitary factor:
$$A_k = \tilde Q_k^H A \tilde Q_k.$$
So every iterate is unitarily similar to $A$, which is why the QR algorithm computes
eigenvalues. This is (7.26) of [kress1998numerical]. -/
theorem qrIterate_eq_conj_qrAccum (A : Matrix n n 𝕜) (k : ℕ) :
    qrIterate A k = (qrAccum A k)ᴴ * A * qrAccum A k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [qrIterate_succ, qrR_eq, qrAccum_succ, Matrix.conjTranspose_mul]
    generalize qrQ (qrIterate A k) = Q
    rw [ih]
    simp only [Matrix.mul_assoc]

/-- For every square matrix $A$ and every $k$,
$$A^k = \tilde Q_k \tilde R_k.$$
Since $\tilde R_k$ is upper triangular, the accumulated unitary factor orthonormalizes the
columns of $A^k$, which identifies the QR algorithm with orthogonal iteration. This is (7.25) of
[kress1998numerical].

It is the unshifted canonical instance of the product identity
`Matrix.prod_mul_prod_reverse_eq_prod_sub_smul_one`, for the chain of QR iterates
`Matrix.isShiftedQrChain_qrIterate`. -/
theorem pow_eq_qrAccum_mul_qrTriangle (A : Matrix n n 𝕜) (k : ℕ) :
    A ^ k = qrAccum A k * qrTriangle A k := by
  rw [qrAccum_eq_prod, qrTriangle_eq_prod,
    prod_mul_prod_reverse_eq_prod_sub_smul_one (isShiftedQrChain_qrIterate A k)]
  simp [List.map_const', List.prod_replicate]

/-- The accumulated triangular factor $\tilde R_k$ is upper triangular. -/
theorem isUpperTriangular_qrTriangle (A : Matrix n n 𝕜) (k : ℕ) :
    (qrTriangle A k).IsUpperTriangular := by
  induction k with
  | zero =>
    intro i j hij
    rw [qrTriangle_zero]
    exact Matrix.one_apply_ne hij.ne'
  | succ k ih => exact (isUpperTriangular_qrR _).mul ih

/-- If $A$ is nonsingular, every QR iterate $A_k$ is nonsingular, since it is a unitary conjugate of
$A$. -/
theorem isUnit_det_qrIterate {A : Matrix n n 𝕜} (hA : IsUnit A.det) (k : ℕ) :
    IsUnit (qrIterate A k).det := by
  have hunit : IsUnit ((qrAccum A k)ᴴ.det * (qrAccum A k).det) := by
    rw [← Matrix.det_mul, conjTranspose_mul_qrAccum, Matrix.det_one]
    exact isUnit_one
  rw [qrIterate_eq_conj_qrAccum, Matrix.det_mul, Matrix.det_mul, mul_right_comm]
  exact (isUnit_of_mul_isUnit_left hunit |>.mul (isUnit_of_mul_isUnit_right hunit)).mul hA

/-- Let $A$ be nonsingular. Then the diagonal entries of the accumulated triangular factor
$\tilde R_k$ are real and positive: $\tilde R_k$ is a product of the factors $R_j$, each of
which has this property by `Matrix.qrR_diag_pos`. -/
theorem qrTriangle_diag_pos {A : Matrix n n 𝕜} (hA : IsUnit A.det) (k : ℕ) (j : n) :
    0 < qrTriangle A k j j := by
  induction k with
  | zero =>
    rw [qrTriangle_zero, Matrix.one_apply_eq]
    exact zero_lt_one
  | succ k ih =>
    rw [qrTriangle_succ,
      IsUpperTriangular.mul_apply_self (isUpperTriangular_qrR _) (isUpperTriangular_qrTriangle A k)]
    exact mul_pos (qrR_diag_pos (isUnit_det_qrIterate hA k) j) ih

/-- **The accumulated unitary factor of the QR algorithm is orthogonal iteration on the standard
basis.** Let $A$ be nonsingular. For every $k$, the columns of $\tilde Q_k$ are the Gram–Schmidt
orthonormalization of the columns of $A^k$, that is, the orthogonal iterates
`Krylov.orthogonalIterate` of the standard basis $(e_j)_j$ under $A$ at step $k$
([kress1998numerical], §7.4).

The QR algorithm is defined without reference to any subspace. This theorem makes
`Krylov.span_orthogonalIterate` apply to it, so that convergence of the iterated flag becomes
convergence of the QR iterates. The operator is `Matrix.toEuclideanLin A`. -/
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

/-- **The QR algorithm is orthogonal iteration on the standard basis.** Let $A$ be nonsingular, and
let $Q$ be the matrix whose columns are the orthogonal iterates at step $k$ of the standard
basis under $A$. Then
$$A_k = Q^H A Q.$$
This is (7.25)–(7.26) of [kress1998numerical].

The matrix $Q$ is a hypothesis with prescribed columns rather than a construction. It is
determined by its columns (`Matrix.euclideanCol_injective`), and this form lets a user supply
any expression for the orthogonal iterates. -/
theorem qrIterate_eq_conj_orthogonalIterate {A Q : Matrix n n 𝕜} (hA : IsUnit A.det) (k : ℕ)
    (hQ : euclideanCol Q = Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) k) :
    qrIterate A k = Qᴴ * A * Q := by
  have hQeq : Q = qrAccum A k :=
    euclideanCol_injective (hQ.trans (qrAccum_eq_orthogonalIterate hA k).symm)
  rw [hQeq, qrIterate_eq_conj_qrAccum]

/-! ### Convergence of the QR algorithm -/

omit [LinearOrder n] [LocallyFiniteOrderBot n] in
set_option linter.unusedDecidableInType false in
/-- For square matrices $U$ and $M$,
$$(U^H M U)_{jk} = \langle u_j, M u_k \rangle,$$
where $u_j$ is the $j$-th column of $U$. This turns the QR iterates into the compressions of $A$
on the orthogonal iterates. -/
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

/-- **The QR iterates are the compressions of $A$ on the orthogonal iterates of the standard
basis.** Let $A$ be nonsingular, and let $q^{(\nu)}_j$ be the orthogonal iterates of the
standard basis under $A$. Then for all $\nu$, $j$ and $k$
$$(A_\nu)_{jk} = \langle q^{(\nu)}_j, A q^{(\nu)}_k \rangle.$$
-/
theorem qrIterate_apply {A : Matrix n n 𝕜} (hA : IsUnit A.det) (ν : ℕ) (j k : n) :
    qrIterate A ν j k =
      inner 𝕜 (Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν j)
        (toEuclideanLin A (Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν k)) := by
  rw [qrIterate_eq_conj_qrAccum, conjTranspose_mul_mul_apply, qrAccum_eq_orthogonalIterate hA]

/-- At step $0$ the orthogonal iterates of the standard basis are the standard basis. -/
theorem orthogonalIterate_euclideanCol_one_zero (A : Matrix n n 𝕜) :
    Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol (1 : Matrix n n 𝕜)) 0 =
      euclideanCol 1 :=
  Krylov.orthogonalIterate_zero (orthonormal_euclideanCol (by simp))

/-- If $A$ is nonsingular, the orthogonal iterates of the standard basis under $A$ are orthonormal
at every step: they are the columns of $\tilde Q_\nu$. -/
theorem orthonormal_orthogonalIterate_euclideanCol_one {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    (ν : ℕ) : Orthonormal 𝕜 (Krylov.orthogonalIterate (toEuclideanLin A) (euclideanCol 1) ν) := by
  rw [← qrAccum_eq_orthogonalIterate hA ν]
  exact orthonormal_euclideanCol (conjTranspose_mul_qrAccum A ν)

/-- **Convergence of the QR algorithm.** Let the index set of $A \in \mathbb{K}^{n \times n}$ be
linearly ordered, and let $A$ be nonsingular. Let $(x_j)_j$ be a basis of $\mathbb{K}^n$ of
eigenvectors of $A$, $A x_j = \lambda_j x_j$, with $\lambda_j \neq 0$ for all $j$ and
$|\lambda_k| < |\lambda_j|$ for $j < k$. Suppose that the standard basis is in general position:
for every lower set $J$ of indices,
$$\operatorname{span}\{e_i : i \in J\} \cap \operatorname{span}\{x_i : i \notin J\} = \{0\}.$$
Then, as $\nu \to \infty$,
$$(A_\nu)_{jk} \to 0 \quad (k < j), \qquad (A_\nu)_{jj} \to \lambda_j.$$
This is Theorem 7.20 of [kress1998numerical]; the general-position condition is his (7.24).

The theorem is `Krylov.tendsto_orthogonalIterate` read through `Matrix.qrIterate_apply`: the QR
algorithm is orthogonal iteration on the standard basis, so its iterates are the compressions
$Q_\nu^H A Q_\nu$ of that theorem. The nonsingularity of $A$ follows from the other hypotheses,
since the eigenvalues are nonzero and there are $n$ independent eigenvectors. It is assumed
rather than derived because `Matrix.qrAccum_eq_orthogonalIterate` needs it and a derivation
would take the determinant through the eigenbasis. For the columns of an invertible matrix $X$,
the general-position condition is the nonvanishing of the leading principal minors of $X^{-1}$
(`Matrix.forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal`). -/
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

/-- **The rate of convergence of the QR algorithm.** Let the index set of
$A \in \mathbb{K}^{n \times n}$ be linearly ordered, and let $A$ be nonsingular. Let $(x_j)_j$
be a basis of $\mathbb{K}^n$ of eigenvectors of $A$, $A x_j = \lambda_j x_j$, with
$|\lambda_k| < |\lambda_j|$ for $j < k$, and let the standard basis be in general position as in
`Matrix.tendsto_qrIterate`. Let $k < j$, and let $r \ge 0$ satisfy $|\lambda_{j'}| \le r$ for
every $j' > k$ and $r < |\lambda_k|$. Then there is a constant $C$ with
$$|(A_\nu)_{jk}| \le C \Bigl(\frac{r}{|\lambda_k|}\Bigr)^\nu \quad \text{for all } \nu.$$
This is (5.37) of [quarteroni2000numerical]: for $j = k + 1$ and $r = |\lambda_{k+1}|$, which
the hypotheses allow, it is the bound $|t^{(k)}_{i,i-1}| = O(|\lambda_i / \lambda_{i-1}|^k)$ of
the source.

The constant $C$ is not explicit. The entry is $\langle q^{(\nu)}_j, A q^{(\nu)}_k \rangle$
(`Matrix.qrIterate_apply`), with $q^{(\nu)}_k$ in the $\nu$-th iterate of the span of the
standard basis vectors $e_i$, $i \le k$, and $q^{(\nu)}_j$ orthogonal to it. So
`Krylov.norm_inner_le_of_gap` bounds the entry by the gap between that iterate and the span of
the eigenvectors $x_i$, $i \le k$, and `Krylov.exists_gap_subspaceIterate_span_image_le` bounds
the gap. -/
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
    exact Krylov.span_orthogonalIterate_of_isLowerSet _ _ _ (IsLowerSet.Iic k)
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
    hJr (hgen _ (IsLowerSet.Iic k)) hrank
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
/-- If $A$ is Hermitian, every QR iterate $A_k$ is Hermitian, being a unitary conjugate of $A$. So
for a Hermitian matrix the iterates converge to a diagonal matrix whenever they converge to an
upper triangular one ([quarteroni2000numerical] Property 5.9, last sentence). -/
theorem isHermitian_qrIterate {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    (qrIterate A k).IsHermitian := by
  rw [qrIterate_eq_conj_qrAccum]
  exact isHermitian_conjTranspose_mul_mul _ hA

/-- If $A$ is nonsingular and upper Hessenberg, its unitary factor `Matrix.qrQ A` is upper
Hessenberg ([quarteroni2000numerical] §5.6.3).

This is the canonical instance of `Matrix.IsUpperHessenberg.isUpperHessenberg_of_eq_mul`, which
holds for every QR factorization. -/
theorem isUpperHessenberg_qrQ {A : Matrix n n 𝕜} (hA : IsUnit A.det) (hH : A.IsUpperHessenberg) :
    (qrQ A).IsUpperHessenberg :=
  hH.isUpperHessenberg_of_eq_mul hA (isUpperTriangular_qrR A) (qrQ_mul_qrR A).symm

/-- **The QR algorithm preserves upper Hessenberg form.** If $A$ is nonsingular and upper
Hessenberg, every QR iterate $A_k$ is upper Hessenberg ([quarteroni2000numerical] §5.6.4).

Each iterate is a QR step from the previous one (`Matrix.isShiftedQrStep_qrIterate`), the
previous one is nonsingular, and Hessenberg form survives such a step
(`Matrix.IsShiftedQrStep.isUpperHessenberg`). -/
theorem isUpperHessenberg_qrIterate {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    (hH : A.IsUpperHessenberg) (k : ℕ) : (qrIterate A k).IsUpperHessenberg := by
  induction k with
  | zero => exact hH
  | succ k ih =>
    exact (isShiftedQrStep_qrIterate A k).isUpperHessenberg ih
      (by rw [zero_smul, sub_zero]; exact isUnit_det_qrIterate hA k)

/-! ### Shifts -/

/-- **One QR step with shift $\mu$** ([quarteroni2000numerical] (5.52)): factor $T - \mu I = QR$ by
`Matrix.qrQ` and `Matrix.qrR`, and return $RQ + \mu I$. -/
noncomputable def shiftedQrStep (μ : 𝕜) (T : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  qrR (T - μ • 1) * qrQ (T - μ • 1) + μ • 1

/-- The shifted QR step is a unitary similarity: $RQ + \mu I = Q^H T Q$, where $Q$ is the unitary
factor of $T - \mu I$. This is the display after (5.52) of [quarteroni2000numerical]. No
nonsingularity is needed. -/
theorem shiftedQrStep_eq_conj (μ : 𝕜) (T : Matrix n n 𝕜) :
    shiftedQrStep μ T = (qrQ (T - μ • 1))ᴴ * T * qrQ (T - μ • 1) := by
  rw [shiftedQrStep, qrR_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, conjTranspose_qrQ_mul_self, sub_add_cancel]

/-- The canonical shifted step `Matrix.shiftedQrStep μ T` is a QR step from $T$ with shift $\mu$ in
the sense of `Matrix.IsShiftedQrStep`. -/
theorem isShiftedQrStep_shiftedQrStep (μ : 𝕜) (T : Matrix n n 𝕜) :
    IsShiftedQrStep μ T (shiftedQrStep μ T) :=
  ⟨qrQ _, qrQ_mem_unitaryGroup _, qrR _, isUpperTriangular_qrR _, (qrQ_mul_qrR _).symm, rfl⟩

/-- **The QR iteration with a fixed shift $\mu$** ([quarteroni2000numerical] §5.7.1): $T_0 = A$, and
$T_{k+1}$ is the canonical QR step from $T_k$ with shift $\mu$. -/
noncomputable def shiftedQrIterate (A : Matrix n n 𝕜) (μ : 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => A
  | k + 1 => shiftedQrStep μ (shiftedQrIterate A μ k)

/-- The fixed-shift iteration starts at $T_0 = A$. -/
@[simp]
theorem shiftedQrIterate_zero (A : Matrix n n 𝕜) (μ : 𝕜) : shiftedQrIterate A μ 0 = A := rfl

/-- One step of the fixed-shift iteration: $T_{k+1}$ is the canonical QR step from $T_k$ with shift
$\mu$. -/
theorem shiftedQrIterate_succ (A : Matrix n n 𝕜) (μ : 𝕜) (k : ℕ) :
    shiftedQrIterate A μ (k + 1) = shiftedQrStep μ (shiftedQrIterate A μ k) := rfl

/-- **A fixed shift is the basic iteration on the shifted matrix.** For every $k$, the fixed-shift
iterate is
$$T_k = (A - \mu I)_k + \mu I,$$
where $(A - \mu I)_k$ is the $k$-th QR iterate of $A - \mu I$.

Consequently `Matrix.tendsto_qrIterate` and `Matrix.exists_abs_qrIterate_apply_le`, applied to
$A - \mu I$, give the convergence claim of [quarteroni2000numerical] §5.7.1: the subdiagonal
entries decay like $|(\lambda_j - \mu)/(\lambda_{j-1} - \mu)|^k$ when $|\lambda_1 - \mu| >
\cdots > |\lambda_n - \mu| > 0$, under the general-position hypothesis for the same eigenvector
matrix. -/
theorem shiftedQrIterate_eq_qrIterate_sub_add (A : Matrix n n 𝕜) (μ : 𝕜) (k : ℕ) :
    shiftedQrIterate A μ k = qrIterate (A - μ • 1) k + μ • 1 := by
  induction k with
  | zero => rw [shiftedQrIterate_zero, qrIterate_zero, sub_add_cancel]
  | succ k ih => rw [shiftedQrIterate_succ, ih, shiftedQrStep, add_sub_cancel_right, qrIterate_succ]

/-- Every iterate of the fixed-shift iteration is a unitary conjugate of the starting matrix:
$T_k = \tilde Q_k^H A \tilde Q_k$, where $\tilde Q_k$ is the accumulated unitary factor of the
QR algorithm on $A - \mu I$. -/
theorem shiftedQrIterate_eq_conj_qrAccum (A : Matrix n n 𝕜) (μ : 𝕜) (k : ℕ) :
    shiftedQrIterate A μ k =
      (qrAccum (A - μ • 1) k)ᴴ * A * qrAccum (A - μ • 1) k := by
  rw [shiftedQrIterate_eq_qrIterate_sub_add, qrIterate_eq_conj_qrAccum, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, conjTranspose_mul_qrAccum,
    sub_add_cancel]

/-! ### Fixed-shift iterations for arbitrary factorizations -/

omit [LinearOrder n] in
/-- If $|d_i| = 1$ for all $i$, then $\operatorname{diag}(d)$ is unitary. -/
theorem diagonal_mem_unitaryGroup {d : n → 𝕜} (hd : ∀ i, ‖d i‖ = 1) :
    diagonal d ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul, hd i]
  simp

omit [LinearOrder n] in
/-- Let $|d_i| = 1$ for all $i$ and $D = \operatorname{diag}(d)$. Then $|(D^H S D)_{ij}| = |S_{ij}|$
for every square matrix $S$ and all $i$, $j$. -/
theorem norm_diagonal_conj_apply {d : n → 𝕜} (hd : ∀ i, ‖d i‖ = 1) (S : Matrix n n 𝕜)
    (i j : n) : ‖(star (diagonal d) * S * diagonal d) i j‖ = ‖S i j‖ := by
  rw [star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
  simp [norm_mul, hd i, hd j]

omit [LinearOrder n] in
/-- Let $|d_i| = 1$ for all $i$ and $D = \operatorname{diag}(d)$. Then $(D^H S D)_{ii} = S_{ii}$ for
every square matrix $S$ and every $i$. -/
theorem diagonal_conj_apply_self {d : n → 𝕜} (hd : ∀ i, ‖d i‖ = 1) (S : Matrix n n 𝕜)
    (i : n) : (star (diagonal d) * S * diagonal d) i i = S i i := by
  rw [star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
  have hii : star (d i) * d i = 1 := by
    rw [RCLike.star_def, RCLike.conj_mul, hd i]
    simp
  simp only [Pi.star_apply]
  calc star (d i) * S i i * d i = (star (d i) * d i) * S i i := by ring
    _ = S i i := by rw [hii, one_mul]

omit [LocallyFiniteOrderBot n] in
/-- Let $|d_i| = 1$ for all $i$ and $D = \operatorname{diag}(d)$. If $H'$ is a QR step from $H$ with
shift $\mu$, then $H'$ is also a QR step from $D^H H D$ with shift $\mu$: if $H - \mu I = UR$,
the factors $D^H U$ and $RD$ give it. -/
theorem IsShiftedQrStep.diagonal_conj {μ : 𝕜} {H H' : Matrix n n 𝕜} {d : n → 𝕜}
    (hd : ∀ i, ‖d i‖ = 1) (h : IsShiftedQrStep μ H H') :
    IsShiftedQrStep μ (star (diagonal d) * H * diagonal d) H' := by
  obtain ⟨U, hU, R, hR, hQR, rfl⟩ := h
  have hD := diagonal_mem_unitaryGroup hd
  have hDD : star (diagonal d) * diagonal d = 1 := mem_unitaryGroup_iff'.1 hD
  have hDD' : diagonal d * star (diagonal d) = 1 := mem_unitaryGroup_iff.1 hD
  refine ⟨star (diagonal d) * U, Submonoid.mul_mem _ (Unitary.star_mem hD) hU, R * diagonal d,
    hR.mul (blockTriangular_diagonal d), ?_, ?_⟩
  · have hH : H = U * R + μ • 1 := by rw [← hQR, sub_add_cancel]
    rw [hH, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hDD, add_sub_cancel_right]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal d), hDD', Matrix.one_mul]

/-- **Every fixed-shift QR iteration is the canonical one up to a unimodular diagonal similarity.**
Let $A - \mu I$ be nonsingular, and let $H_0 = A$ and $H_{k+1}$ be a QR step from $H_k$ with
shift $\mu$ for every $k$, for any QR factorizations. Then for every $k$ there is $d$ with
$|d_i| = 1$ for all $i$ such that, with $D = \operatorname{diag}(d)$,
$$H_k = D^H T_k D,$$
where $T_k$ is the canonical fixed-shift iterate `Matrix.shiftedQrIterate A μ k`.

The QR factorization of a nonsingular matrix is unique up to such a diagonal matrix
(`Matrix.IsShiftedQrStep.unique_of_isUnit`). -/
theorem exists_eq_diagonal_conj_shiftedQrIterate {A : Matrix n n 𝕜} {μ : 𝕜}
    (hA : IsUnit (A - μ • 1).det) {H : ℕ → Matrix n n 𝕜} (hH0 : H 0 = A)
    (hH : ∀ k, IsShiftedQrStep μ (H k) (H (k + 1))) (k : ℕ) :
    ∃ d : n → 𝕜, (∀ i, ‖d i‖ = 1) ∧
      H k = star (diagonal d) * shiftedQrIterate A μ k * diagonal d := by
  induction k with
  | zero =>
    refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    rw [diagonal_one, star_one, Matrix.one_mul, Matrix.mul_one, hH0, shiftedQrIterate_zero]
  | succ k ih =>
    obtain ⟨d, hd, hk⟩ := ih
    have hD := diagonal_mem_unitaryGroup hd
    have hDD : star (diagonal d) * diagonal d = 1 := mem_unitaryGroup_iff'.1 hD
    have hDD' : diagonal d * star (diagonal d) = 1 := mem_unitaryGroup_iff.1 hD
    have hc : IsShiftedQrStep μ (H k) (shiftedQrIterate A μ (k + 1)) := by
      rw [hk, shiftedQrIterate_succ]
      exact (isShiftedQrStep_shiftedQrStep _ _).diagonal_conj hd
    have hsub : H k - μ • 1 = star (diagonal d) * qrIterate (A - μ • 1) k * diagonal d := by
      rw [hk, ← add_sub_cancel_right (qrIterate (A - μ • 1) k) (μ • 1),
        ← shiftedQrIterate_eq_qrIterate_sub_add, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hDD]
    have hdet : IsUnit (H k - μ • 1).det := by
      rw [hsub, det_mul, det_mul]
      exact ((isUnit_det_of_right_inverse hDD).mul (isUnit_det_qrIterate hA k)).mul
        (isUnit_det_of_right_inverse hDD')
    exact hc.unique_of_isUnit (hH k) hdet

/-- **The rate of convergence of a fixed-shift QR iteration, for any QR factorizations.** Let the
index set of $A \in \mathbb{K}^{n \times n}$ be linearly ordered, and let $A - \mu I$ be
nonsingular. Let $(x_j)_j$ be a basis of $\mathbb{K}^n$ of eigenvectors of $A$,
$A x_j = \lambda_j x_j$, with $|\lambda_k - \mu| < |\lambda_j - \mu|$ for $j < k$, and let the
standard basis be in general position as in `Matrix.tendsto_qrIterate`. Let $H_0 = A$ and let
$H_{k+1}$ be a QR step from $H_k$ with shift $\mu$ for every $k$, for any factorizations. Let
$k < j$, and let $r \ge 0$ satisfy $|\lambda_{j'} - \mu| \le r$ for every $j' > k$ and
$r < |\lambda_k - \mu|$. Then there is a constant $C$ with
$$|(H_\nu)_{jk}| \le C \Bigl(\frac{r}{|\lambda_k - \mu|}\Bigr)^\nu \quad \text{for all } \nu.$$
This is the convergence statement of [golub2013matrix] §7.5.2 and [quarteroni2000numerical]
§5.7.1.

The iteration is the canonical one up to unimodular diagonal similarities
(`Matrix.exists_eq_diagonal_conj_shiftedQrIterate`), which keep the moduli of the entries, and
the canonical one is the basic iteration on $A - \mu I$
(`Matrix.shiftedQrIterate_eq_qrIterate_sub_add`, `Matrix.exists_abs_qrIterate_apply_le`). -/
theorem exists_norm_apply_le_of_isShiftedQrStep {A : Matrix n n 𝕜} {μ : 𝕜}
    (hA : IsUnit (A - μ • 1).det) {x : n → EuclideanSpace 𝕜 n} {l : n → 𝕜}
    (hx : LinearIndependent 𝕜 x) (hxtop : Submodule.span 𝕜 (Set.range x) = ⊤)
    (heig : ∀ j, toEuclideanLin A (x j) = l j • x j)
    (hsep : ∀ j k : n, j < k → ‖l k - μ‖ < ‖l j - μ‖)
    (hgen : ∀ J : Set n, IsLowerSet J →
      Disjoint (Submodule.span 𝕜 (euclideanCol (1 : Matrix n n 𝕜) '' J))
        (Submodule.span 𝕜 (x '' Jᶜ)))
    {H : ℕ → Matrix n n 𝕜} (hH0 : H 0 = A) (hH : ∀ k, IsShiftedQrStep μ (H k) (H (k + 1)))
    {j k : n} (hkj : k < j) {r : ℝ} (hr0 : 0 ≤ r) (hr : ∀ j', k < j' → ‖l j' - μ‖ ≤ r)
    (hrk : r < ‖l k - μ‖) :
    ∃ C : ℝ, ∀ ν, ‖H ν j k‖ ≤ C * (r / ‖l k - μ‖) ^ ν := by
  have heig' : ∀ j, toEuclideanLin (A - μ • 1) (x j) = (l j - μ) • x j := fun j => by
    rw [map_sub, LinearMap.sub_apply, heig, map_smul, LinearMap.smul_apply, toEuclideanLin_one,
      LinearMap.id_apply, sub_smul]
  obtain ⟨C, hC⟩ := exists_abs_qrIterate_apply_le hA hx hxtop heig' hsep hgen hkj hr0 hr hrk
  refine ⟨C, fun ν => ?_⟩
  obtain ⟨d, hd, hν⟩ := exists_eq_diagonal_conj_shiftedQrIterate hA hH0 hH ν
  rw [hν, norm_diagonal_conj_apply hd, shiftedQrIterate_eq_qrIterate_sub_add, Matrix.add_apply,
    Matrix.smul_apply, one_apply_ne hkj.ne', smul_zero, add_zero]
  exact hC ν

/-- **The double-shift step** ([quarteroni2000numerical] (5.55)): two consecutive canonical shifted
QR steps from $T$, the first with shift $\mu$ and the second with shift $\bar\mu$. The pair of
shifts is meant to be the two complex conjugate eigenvalues of a trailing $2 \times 2$ block
that the single-shift iteration cannot split.

For a real matrix the result is real (`Matrix.doubleShiftQrStep_map_ofReal`). The implementation
in real arithmetic, the Francis step, is specified by `Matrix.IsFrancisStep` and implemented in
the surface library for [golub2013matrix] as Algorithm 7.5.1. -/
noncomputable def doubleShiftQrStep (T : Matrix n n 𝕜) (μ : 𝕜) : Matrix n n 𝕜 :=
  shiftedQrStep (starRingEnd 𝕜 μ) (shiftedQrStep μ T)

/-- The double-shift step is a unitary similarity. Let $Q_1$ be the unitary factor of $T - \mu I$,
let $T_1$ be the shifted step from $T$ with shift $\mu$, and let $Q_2$ be the unitary factor of
$T_1 - \bar\mu I$. Then the double-shift step is $(Q_1 Q_2)^H T (Q_1 Q_2)$. -/
theorem doubleShiftQrStep_eq_conj (T : Matrix n n 𝕜) (μ : 𝕜) :
    doubleShiftQrStep T μ =
      (qrQ (T - μ • 1) * qrQ (shiftedQrStep μ T - starRingEnd 𝕜 μ • 1))ᴴ * T *
        (qrQ (T - μ • 1) * qrQ (shiftedQrStep μ T - starRingEnd 𝕜 μ • 1)) := by
  rw [doubleShiftQrStep, shiftedQrStep_eq_conj (starRingEnd 𝕜 μ), conjTranspose_mul]
  generalize qrQ (shiftedQrStep μ T - starRingEnd 𝕜 μ • 1) = Q₂
  rw [shiftedQrStep_eq_conj μ T]
  simp only [Matrix.mul_assoc]

/-- The double-shift step from $T$ is $Q^H T Q$ for some unitary $Q$. -/
theorem exists_unitary_conj_doubleShiftQrStep (T : Matrix n n 𝕜) (μ : 𝕜) :
    ∃ Q ∈ Matrix.unitaryGroup n 𝕜, doubleShiftQrStep T μ = Qᴴ * T * Q :=
  ⟨_, mul_mem (qrQ_mem_unitaryGroup _) (qrQ_mem_unitaryGroup _), doubleShiftQrStep_eq_conj T μ⟩

end GramSchmidt

section Rayleigh

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- **The QR iteration with the Rayleigh-quotient shift** ([quarteroni2000numerical] (5.53)). For
$A$ of order $n = N + 1$, the iterates are $T_0 = A$ and the canonical QR step $T_{k+1}$ from
$T_k$ with shift $\mu_k = (T_k)_{nn}$, the current last diagonal entry.

This module states no convergence theorem for it: the quadratic convergence that the source
claims is a local statement about Rayleigh quotient iteration that the source does not prove. A
local bound for one step is in `Numlib.Eigen.RayleighQuotientIteration`. The index $n$ is
`Fin.last N`. -/
noncomputable def rayleighShiftQrIterate (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜
  | 0 => A
  | k + 1 =>
    shiftedQrStep (rayleighShiftQrIterate A k (Fin.last N) (Fin.last N))
      (rayleighShiftQrIterate A k)

/-- The Rayleigh-shift iteration starts at $T_0 = A$. -/
@[simp]
theorem rayleighShiftQrIterate_zero (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    rayleighShiftQrIterate A 0 = A := rfl

/-- One step of the Rayleigh-shift iteration: $T_{k+1}$ is the canonical QR step from $T_k$ with
shift $(T_k)_{nn}$, the current last diagonal entry. -/
theorem rayleighShiftQrIterate_succ (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) (k : ℕ) :
    rayleighShiftQrIterate A (k + 1) =
      shiftedQrStep (rayleighShiftQrIterate A k (Fin.last N) (Fin.last N))
        (rayleighShiftQrIterate A k) := rfl

/-- Every Rayleigh-shift iterate is a unitary conjugate of the starting matrix: $T_k = Q^H A Q$ for
some unitary $Q$. -/
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

/-!
### The Francis double-shift step

`Matrix.doubleShiftQrStep` takes two complex conjugate shifts in complex arithmetic. For a real
matrix its result is real (`Matrix.doubleShiftQrStep_map_ofReal`): it is the orthogonal similarity
by the orthogonal factor of the real matrix $M = H^2 - sH + tI$. The implicit (Francis) step
computes such a similarity without forming $M$. Its specification is `Matrix.IsFrancisStep`, and the
implicit Q theorem identifies every Francis step of an unreduced Hessenberg matrix with the explicit
one up to signs (`Matrix.IsFrancisStep.eq_diagonal_conj`). The implementation is Algorithm 7.5.1 of
[golub2013matrix], in the surface library.
-/

section Francis

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- If $A \in \mathbb{K}^{N \times N}$ is nonsingular, so is its triangular factor `Matrix.qrR A`.
-/
theorem isUnit_det_qrR {A : Matrix (Fin N) (Fin N) 𝕜} (hA : IsUnit A.det) :
    IsUnit (qrR A).det := by
  rw [det_of_isUpperTriangular (isUpperTriangular_qrR A), isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun j _ => (qrR_diag_pos hA j).ne'

/-- Let $H, M \in \mathbb{R}^{N \times N}$ with $M$ nonsingular and $HM = MH$, and let $M = ZR$ be
the QR decomposition by `Matrix.qrQ` and `Matrix.qrR`. Then
$$Z^T H Z = R H R^{-1}.$$
Indeed $Z^T H Z = Z^T H M R^{-1} = Z^T M H R^{-1} = R H R^{-1}$. -/
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

/-- A real square matrix $H$ commutes with the double-shift polynomial $H^2 - sH + tI$. -/
theorem mul_francisPoly_comm (H : Matrix (Fin N) (Fin N) ℝ) (s t : ℝ) :
    H * (H * H - s • H + t • 1) = (H * H - s • H + t • 1) * H := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

/-- Let $H, H' \in \mathbb{R}^{N \times N}$ and $s, t \in \mathbb{R}$. The matrix $H'$ is a
**Francis step** (implicit double-shift step) from $H$ if there is an orthogonal $Z$ such that
$$H' = Z^T H Z, \qquad H' \text{ is upper Hessenberg}, \qquad Z^T (H^2 - sH + tI) \text{ is
  upper triangular}.$$
Equivalently, $Z$ is the orthogonal factor of some QR factorization of $M = H^2 - sH + tI$. This
is the specification in the header of Algorithm 7.5.1 of [golub2013matrix].

In the algorithm, $s$ and $t$ are the trace and the determinant of the trailing $2 \times 2$
block; the definition allows any real $s$ and $t$. -/
def IsFrancisStep (s t : ℝ) (H H' : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ Z ∈ orthogonalGroup (Fin N) ℝ, H' = Zᵀ * H * Z ∧ H'.IsUpperHessenberg ∧
    (Zᵀ * (H * H - s • H + t • 1)).IsUpperTriangular

/-- **Existence of a Francis step through the explicit construction.** Let
$H \in \mathbb{R}^{N \times N}$ be upper Hessenberg, let $M = H^2 - sH + tI$ be nonsingular, and
let $Z$ be the orthogonal factor `Matrix.qrQ M`. Then $Z^T H Z$ is a Francis step from $H$. This
is [golub2013matrix] §7.5.4: "explicitly form $M$, compute $M = ZR$, set $H_2 = Z^T H Z$".

The matrix $Z^T H Z = R H R^{-1}$ (`Matrix.transpose_qrQ_mul_mul_qrQ`) is upper Hessenberg. -/
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

/-- **Essential uniqueness of the Francis step.** Let $H \in \mathbb{R}^{n \times n}$, $n = N + 1$,
be unreduced upper Hessenberg, let $M = H^2 - sH + tI$ be nonsingular, and let $Z_0$ be the
orthogonal factor `Matrix.qrQ M`. Then every Francis step $H'$ from $H$ satisfies
$$H' = D (Z_0^T H Z_0) D$$
for a diagonal matrix $D = \operatorname{diag}(d)$ with $d_i \in \{1, -1\}$ for all $i$. This is
[golub2013matrix] §7.5.5: "the implicit Q theorem permits us to conclude that … they are
essentially equal".

The first columns of the orthogonal matrix $Z$ of the step and of $Z_0$ are both multiples of
$M e_1 \neq 0$, hence equal up to sign. After a change of the sign of $Z$, the implicit Q
theorem `Matrix.implicitQ_real` applies, with the unreduced matrix $Z_0^T H Z_0 = R H R^{-1}$. -/
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
    rwa [Matrix.mul_apply, one_apply_eq] at this
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
    simp only [col_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this, ← mul_assoc, hσσ, one_mul]
  obtain ⟨d, hd, -, -, hGH⟩ := implicitQ_real (qrQ_mem_unitaryGroup M) hV hG₀
    (by rw [hVHV]; exact hH') hV0
  exact ⟨d, hd, by rw [← hVHV, hGH]⟩

/-- **The double-shift step of a real matrix is real.** Let $H \in \mathbb{R}^{N \times N}$ and let
$a \in \mathbb{C}$ not be an eigenvalue of $H$. Then the double-shift step from $H$ with the
shifts $a$ and $\bar a$, computed in complex arithmetic with the canonical factorizations, is
the real matrix $Z^T H Z$, where $Z$ is the orthogonal factor `Matrix.qrQ M` of
$$M = H^2 - 2 \operatorname{Re}(a) H + |a|^2 I.$$
This is [golub2013matrix] §7.5.4.

By the product identity the two steps give the factorization $(U_1 U_2)(R_2 R_1) = (H - aI)(H -
\bar a I) = M$ with positive diagonal, and so does the complexified factorization $M = ZR$;
`Matrix.IsThinQR.unique` identifies them. The real matrices are embedded by `Matrix.complexify`,
and the hypothesis on $a$ is that it is not in `spectrum ℂ H.complexify`. -/
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
    rw [hMdef, complexify_add, complexify_sub, complexify_mul, complexify_smul, complexify_smul,
      complexify_one]
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
    rw [det_complexify, isUnit_iff_ne_zero, Complex.ofReal_ne_zero] at hc
    exact isUnit_iff_ne_zero.2 hc
  -- two factorizations with positive diagonal
  have hQM : (qrQ M).complexify ᴴ * (qrQ M).complexify = 1 := by
    rw [← complexify_conjTranspose, ← complexify_mul, conjTranspose_qrQ_mul_self, complexify_one]
  have hUU : (U₁ * U₂)ᴴ * (U₁ * U₂) = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₁ᴴ, hU₁u, Matrix.one_mul,
      conjTranspose_qrQ_mul_self]
  have htri : (R₂ * R₁).IsUpperTriangular := (isUpperTriangular_qrR _).mul (isUpperTriangular_qrR _)
  have hpos : ∀ j, 0 < (R₂ * R₁).diag j := fun j => by
    rw [diag_apply, (isUpperTriangular_qrR _).mul_apply_self (isUpperTriangular_qrR _)]
    exact mul_pos (qrR_diag_pos hdet₂ j) (qrR_diag_pos hdet₁ j)
  have htriM : ((qrR M).complexify).IsUpperTriangular := fun i j hij => by
    rw [complexify_apply, isUpperTriangular_qrR M hij, Complex.ofReal_zero]
  have hposM : ∀ j, 0 < ((qrR M).complexify).diag j := fun j => by
    rw [diag_apply, complexify_apply]
    exact Complex.zero_lt_real.2 (qrR_diag_pos hMdet j)
  obtain ⟨hU, -⟩ := IsThinQR.unique ⟨hprod, hUU, htri⟩
    ⟨by rw [← complexify_mul, qrQ_mul_qrR], hQM, htriM⟩ hpos hposM
  rw [doubleShiftQrStep_eq_conj, ← hU₁, ← hU₂, hU, ← complexify_conjTranspose, ← complexify_mul,
    ← complexify_mul, conjTranspose_eq_transpose_of_trivial]

end Francis

section LeadingPrincipal

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- **The general-position hypothesis of `Matrix.tendsto_qrIterate` is the LU condition on the
inverse eigenvector matrix.** Let $X \in \mathbb{K}^{N \times N}$ be nonsingular with columns
$x_0, \dots, x_{N-1}$, and let $m \le N$. Then
$$\operatorname{span}\{e_i : i < m\} \cap \operatorname{span}\{x_i : i \ge m\} = \{0\}$$
if and only if the leading principal $m \times m$ submatrix of $X^{-1}$ is nonsingular.

This is the condition of Theorem 7.3.1 of the 1989 edition of Golub and Van Loan, *Matrix
Computations*; Property 5.9 of [quarteroni2000numerical] omits it. The rows of $X^{-1}$ are the
dual basis of the columns of $X$, so a vector supported on $\{i : i < m\}$ that lies in the span
of the $x_i$, $i \ge m$, is a kernel vector of the leading block of $X^{-1}$, and conversely.
Indices are $0$-based, and the leading block is `Matrix.submatrix` along `Fin.castLE hm`. -/
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
    rw [Fin.sum_castLE_eq_sum_ite hm (fun l => X⁻¹ (Fin.castLE hm i) l * v l)]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · rfl
    · rw [hv l (not_lt.1 hl), mul_zero]
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

/-- For every $m$, the set $\{i : i < m\}$ of indices in $\{0, \dots, N-1\}$ is a lower set. -/
theorem isLowerSet_setOf_val_lt (m : ℕ) : IsLowerSet {i : Fin N | (i : ℕ) < m} :=
  fun _ _ hba ha => (Fin.le_def.1 hba).trans_lt ha

/-- Every lower set $J$ of $\{0, \dots, N-1\}$ is an initial segment $\{i : i < m\}$ with $m \le N$.
-/
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

/-- **The general-position hypothesis for an invertible eigenvector matrix is the nonvanishing of
the leading principal minors of its inverse.** Let $X \in \mathbb{K}^{N \times N}$ be
nonsingular with columns $x_0, \dots, x_{N-1}$. Then
$$\operatorname{span}\{e_i : i \in J\} \cap \operatorname{span}\{x_i : i \notin J\} = \{0\}$$
for every lower set $J$ of indices if and only if the leading principal $m \times m$ submatrix
of $X^{-1}$ is nonsingular for every $m \le N$.

This is the hypothesis of `Matrix.tendsto_qrIterate` for the columns of $X$. It is the condition
of Theorem 7.3.1 of the 1989 edition of Golub and Van Loan, *Matrix Computations*, which
Property 5.9 of [quarteroni2000numerical] omits. The proof uses that the lower sets of `Fin N`
are the initial segments. -/
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
