import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.PowerMethod

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
  have hrank : Module.finrank 𝕜 ↥(span 𝕜 (q 0 '' J))
      = Module.finrank 𝕜 ↥(span 𝕜 (x '' J)) := by
    have h1 : Set.range (fun j : ↥J => q 0 ↑j) = q 0 '' J := by rw [← Set.image_eq_range]
    have h2 : Set.range (fun j : ↥J => x ↑j) = x '' J := by rw [← Set.image_eq_range]
    have hqli : LinearIndependent 𝕜 fun j : ↥J => q 0 ↑j :=
      (hq 0).linearIndependent.comp _ Subtype.val_injective
    have hxli : LinearIndependent 𝕜 fun j : ↥J => x ↑j := hx.comp _ Subtype.val_injective
    rw [← h1, ← h2, finrank_span_eq_card hqli, finrank_span_eq_card hxli]
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
  have hinv : ∀ (J : Set ι), ∀ y ∈ span 𝕜 (x '' J), A y ∈ span 𝕜 (x '' J) := by
    intro J
    have hle : span 𝕜 (x '' J) ≤ Submodule.comap A (span 𝕜 (x '' J)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, heig i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    exact fun y hy => hle hy
  have hmemS : ∀ (ν : ℕ) (J : Set ι) (i : ι), i ∈ J → q ν i ∈ span 𝕜 (q ν '' J) :=
    fun ν J i hi => Submodule.subset_span ⟨i, hi, rfl⟩
  have hperp : ∀ (ν : ℕ) (J : Set ι) (j : ι), j ∉ J → q ν j ∈ (span 𝕜 (q ν '' J))ᗮ := by
    intro ν J j hj
    rw [Submodule.mem_orthogonal']
    intro u hu
    have hle : span 𝕜 (q ν '' J) ≤
        LinearMap.ker ((innerSL 𝕜 (q ν j) : E →L[𝕜] 𝕜) : E →ₗ[𝕜] 𝕜) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact (hq ν).2 fun h => hj (h ▸ hi)
    exact hle hu
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
  induction k with
  | zero => simp
  | succ k ih =>
    have hcomm : A * qrAccum A k = qrAccum A k * qrIterate A k := by
      rw [qrIterate_eq_conj_qrAccum, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        qrAccum_mul_conjTranspose, Matrix.one_mul]
    have hsplit : qrIterate A k = qrQ (qrIterate A k) * qrR (qrIterate A k) :=
      (qrQ_mul_qrR _).symm
    rw [pow_succ', ih, ← Matrix.mul_assoc, hcomm, qrAccum_succ, qrTriangle_succ]
    conv_lhs => rw [hsplit]
    simp only [Matrix.mul_assoc]

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
  have honeH : (1 : Matrix n n 𝕜)ᴴ * 1 = 1 := by simp
  have hq0 : q 0 = euclideanCol (1 : Matrix n n 𝕜) :=
    Krylov.orthogonalIterate_zero (orthonormal_euclideanCol honeH)
  have hqon : ∀ ν, Orthonormal 𝕜 (q ν) := by
    intro ν
    have hcol : q ν = euclideanCol (qrAccum A ν) := (qrAccum_eq_orthogonalIterate hA ν).symm
    rw [hcol]
    exact orthonormal_euclideanCol (conjTranspose_mul_qrAccum A ν)
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

end GramSchmidt

end Matrix
