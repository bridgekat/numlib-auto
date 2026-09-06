import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Numlib.LinearAlgebra.Matrix.QR

/-!
# §1.7 Orthogonal vectors and subspaces

Section 1.7 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the Gram–Schmidt process (Algorithms 1.1 and 1.2), the QR factorization (1.19), and
Householder orthogonalization ((1.20)–(1.28) and Algorithm 1.3).

The vocabulary of the section — orthogonal and orthonormal sets, the orthogonal complement, the
orthogonal projector, and the existence of an orthonormal basis of a subspace — is Mathlib's
(`Orthonormal`, `Submodule.orthogonal`, `Submodule.starProjection`, `stdOrthonormalBasis`) and is
not restated here. What is left is the factorization and the reflectors, and both come from the
backbone module `Numlib/LinearAlgebra/Matrix/QR`, which this file specializes.

Algorithm 1.1 (classical Gram–Schmidt) is Mathlib's `InnerProductSpace.gramSchmidtNormed` applied
to the family `x₁, …, x_r`, so what is stated about it here is its breakdown criterion,
`gramSchmidt_completes_iff`, and the triangular expansion `gramSchmidt_expansion`, the two claims
the book makes about it. Algorithm 1.2 (modified Gram–Schmidt) is written out as the recursion
`modifiedGramSchmidt`, with running vector `mgsRun` and coefficients
`modifiedGramSchmidtCoeff`; `algorithm_1_2_eq` is the book's claim that in exact arithmetic it
computes the same `Q` and the same `R` as Algorithm 1.1. That the two differ in floating point is
not stated: that belongs to a floating-point layer.

Indices are `0`-based, as elsewhere in this library: the book's `x₁, …, x_r` are `x 0, …, x (r-1)`
and its `q_j` is `modifiedGramSchmidt x (j-1)`. Division by a vanishing norm is `0` in Lean, which
reproduces the book's "If r_jj = 0 then Stop": every vector the algorithm produces after a
breakdown is `0`, and the identities below hold past it with no hypothesis.

Saad's inner product `(x, y) = ∑ xᵢ ȳᵢ` is Mathlib's `inner 𝕜 y x`, so the book's
`r_ij = (x_j, q_i)` is `inner 𝕜 (q i) (x j)`.
-/

open InnerProductSpace Matrix

open scoped ComplexOrder Matrix

namespace SaadSparse.Ch01

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Gram–Schmidt, for an arbitrary index type

The two facts about `gramSchmidt` that the section uses and Mathlib does not state. Both are
index-general; the book's statements below are their instances at `Fin r` and at `ℕ`. -/

section Aux

variable {ι E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem inner_gramSchmidt_self (x : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidt 𝕜 x j) (x j) = ((‖gramSchmidt 𝕜 x j‖ : 𝕜)) ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' 𝕜 x j]
  rw [inner_add_right, inner_sum, inner_self_eq_norm_sq_to_K]
  convert add_zero _
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [inner_smul_right, gramSchmidt_orthogonal 𝕜 x (Finset.mem_Iio.1 hi).ne', mul_zero]

private theorem inner_gramSchmidtNormed_self (x : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidtNormed 𝕜 x j) (x j) = ((‖gramSchmidt 𝕜 x j‖ : 𝕜)) := by
  rw [gramSchmidtNormed, inner_smul_left, inner_gramSchmidt_self, RCLike.conj_inv,
    RCLike.conj_ofReal]
  rcases eq_or_ne ((‖gramSchmidt 𝕜 x j‖ : 𝕜)) 0 with h | h
  · simp [h]
  · rw [sq, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

private theorem inner_gramSchmidtNormed_smul (x : ι → E) (i j : ι) :
    inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) • gramSchmidtNormed 𝕜 x i
      = (inner 𝕜 (gramSchmidt 𝕜 x i) (x j) / ((‖gramSchmidt 𝕜 x i‖ : 𝕜)) ^ 2)
        • gramSchmidt 𝕜 x i := by
  rw [gramSchmidtNormed, inner_smul_left, RCLike.conj_inv, RCLike.conj_ofReal, smul_smul,
    div_eq_mul_inv, sq, mul_inv]
  ring_nf

private theorem gramSchmidtNormed_pairwise_orthogonal (x : ι → E) :
    Pairwise fun i j => inner 𝕜 (gramSchmidtNormed 𝕜 x i) (gramSchmidtNormed 𝕜 x j) = 0 := by
  intro i j hij
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 x hij]

/-- The Gram–Schmidt vector is what is left of `x j` after the projections on the previous
normalized vectors have been subtracted. -/
private theorem gramSchmidt_eq_sub_sum (x : ι → E) (j : ι) :
    gramSchmidt 𝕜 x j
      = x j - ∑ i ∈ Finset.Iio j,
          inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) • gramSchmidtNormed 𝕜 x i := by
  rw [eq_sub_iff_add_eq, Finset.sum_congr rfl fun i _ => inner_gramSchmidtNormed_smul x i j]
  exact (gramSchmidt_def'' 𝕜 x j).symm

/-- The diagonal term of the expansion: the `j`-th coefficient times the `j`-th normalized vector
is the `j`-th Gram–Schmidt vector, at a breakdown as well, where both sides vanish. -/
private theorem inner_gramSchmidtNormed_smul_self (x : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidtNormed 𝕜 x j) (x j) • gramSchmidtNormed 𝕜 x j = gramSchmidt 𝕜 x j := by
  rw [inner_gramSchmidtNormed_smul, inner_gramSchmidt_self]
  rcases eq_or_ne ((‖gramSchmidt 𝕜 x j‖ : 𝕜)) 0 with h | h
  · have h0 : gramSchmidt 𝕜 x j = 0 := by simpa using h
    simp [h0]
  · rw [div_self (pow_ne_zero 2 h), one_smul]

end Aux

/-! ### Algorithm 1.1: the Gram–Schmidt process -/

section Algorithm11

variable {r : ℕ}

/-- Saad §1.7: **Algorithm 1.1 completes all `r` steps if and only if `x₁, …, x_r` is linearly
independent**. "Completing step `j`" is `r_jj ≠ 0`, that is `gramSchmidtNormed 𝕜 x j ≠ 0`; the
algorithm stops at the first `j` where it fails.

Mathlib has the "only if" half (`InnerProductSpace.gramSchmidt_ne_zero`). The converse holds
because the Gram–Schmidt family is orthogonal whatever `x` is, so nonvanishing already makes it
linearly independent, and it spans what `x` spans. -/
theorem gramSchmidt_completes_iff (x : Fin r → 𝔼) :
    (∀ j, gramSchmidtNormed 𝕜 x j ≠ 0) ↔ LinearIndependent 𝕜 x := by
  refine ⟨fun h => ?_, fun h j h0 => ?_⟩
  · have hq : LinearIndependent 𝕜 (gramSchmidtNormed 𝕜 x) :=
      linearIndependent_of_ne_zero_of_inner_eq_zero h (gramSchmidtNormed_pairwise_orthogonal x)
    have hspan : Submodule.span 𝕜 (Set.range (gramSchmidtNormed 𝕜 x))
        = Submodule.span 𝕜 (Set.range x) := by
      rw [span_gramSchmidtNormed_range, span_gramSchmidt]
    refine linearIndependent_iff_card_eq_finrank_span.2 ?_
    rw [linearIndependent_iff_card_eq_finrank_span.1 hq]
    exact congrArg (fun p : Submodule 𝕜 𝔼 => Module.finrank 𝕜 p) hspan
  · simpa [h0] using gramSchmidtNormed_unit_length j h

/-- Saad §1.7: the triangular expansion that Algorithm 1.1 computes, `x_j = ∑_{i ≤ j} r_ij q_i`
with `r_ij = (x_j, q_i)`. It is the `j`-th column of the factorization (1.19), and it needs no
hypothesis on `x`: at a breakdown both `q_j` and the `j`-th coefficient vanish. -/
theorem gramSchmidt_expansion (x : Fin r → 𝔼) (j : Fin r) :
    x j = ∑ i ∈ Finset.Iic j,
      inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) • gramSchmidtNormed 𝕜 x i := by
  rw [← Finset.Iio_insert, Finset.sum_insert (by simp), inner_gramSchmidtNormed_smul_self,
    gramSchmidt_eq_sub_sum]
  abel

end Algorithm11

/-! ### Algorithm 1.2: modified Gram–Schmidt -/

/-- The inner loop of **Algorithm 1.2**: the running vector `q̂` after the projections on
`q_0, …, q_{k-1}` have been subtracted one at a time. -/
noncomputable def mgsRun (q : ℕ → 𝔼) (v : 𝔼) : ℕ → 𝔼
  | 0 => v
  | k + 1 => mgsRun q v k - inner 𝕜 (q k) (mgsRun q v k) • q k

/-- **Algorithm 1.2** (modified Gram–Schmidt), `0`-based: `q_j` is the running vector of the
inner loop, normalized. -/
noncomputable def modifiedGramSchmidt (x : ℕ → 𝔼) : ℕ → 𝔼
  | 0 => ((‖x 0‖ : 𝕜)⁻¹) • x 0
  | j + 1 =>
    let q : ℕ → 𝔼 := fun i => modifiedGramSchmidt x (min i j)
    ((‖mgsRun q (x (j + 1)) (j + 1)‖ : 𝕜)⁻¹) • mgsRun q (x (j + 1)) (j + 1)
  termination_by j => j
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/-- The coefficients `r_ij` of **Algorithm 1.2**: for `i < j` the inner product of `q_i` with the
*current* running vector, and `r_jj` the norm of the vector the inner loop leaves. -/
noncomputable def modifiedGramSchmidtCoeff (x : ℕ → 𝔼) (i j : ℕ) : 𝕜 :=
  if i < j then inner 𝕜 (modifiedGramSchmidt x i) (mgsRun (modifiedGramSchmidt x) (x j) i)
  else if i = j then ((‖mgsRun (modifiedGramSchmidt x) (x j) j‖ : 𝕜)) else 0

/-- The inner loop reads only `q_0, …, q_{k-1}`. -/
private theorem mgsRun_congr {q q' : ℕ → 𝔼} (v : 𝔼) {k : ℕ} (h : ∀ i < k, q i = q' i) :
    mgsRun q v k = mgsRun q' v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mgsRun, mgsRun, ih fun i hi => h i (hi.trans k.lt_succ_self), h k k.lt_succ_self]

/-- As soon as the `q_i` are pairwise orthogonal, the inner loop of modified Gram–Schmidt
subtracts the same total as classical Gram–Schmidt does in one step. -/
private theorem mgsRun_eq_sub_sum {q : ℕ → 𝔼}
    (ho : ∀ i j, i ≠ j → inner 𝕜 (q i) (q j) = 0) (v : 𝔼) (k : ℕ) :
    mgsRun q v k = v - ∑ i ∈ Finset.range k, inner 𝕜 (q i) v • q i := by
  induction k with
  | zero => simp [mgsRun]
  | succ k ih =>
    have hik : inner 𝕜 (q k) (mgsRun q v k) = inner 𝕜 (q k) v := by
      rw [ih, inner_sub_right, inner_sum]
      refine sub_eq_self.2 (Finset.sum_eq_zero fun i hi => ?_)
      rw [inner_smul_right, ho k i (Ne.symm (Finset.mem_range.1 hi).ne), mul_zero]
    rw [mgsRun, hik, ih, Finset.sum_range_succ]
    abel

/-- The coefficient the inner loop reads is the classical one. -/
private theorem inner_mgsRun_self {q : ℕ → 𝔼}
    (ho : ∀ i j, i ≠ j → inner 𝕜 (q i) (q j) = 0) (v : 𝔼) (k : ℕ) :
    inner 𝕜 (q k) (mgsRun q v k) = inner 𝕜 (q k) v := by
  rw [mgsRun_eq_sub_sum ho, inner_sub_right, inner_sum]
  refine sub_eq_self.2 (Finset.sum_eq_zero fun i hi => ?_)
  rw [inner_smul_right, ho k i (Ne.symm (Finset.mem_range.1 hi).ne), mul_zero]

private theorem mgsRun_gramSchmidtNormed (x : ℕ → 𝔼) (k : ℕ) :
    mgsRun (gramSchmidtNormed 𝕜 x) (x k) k = gramSchmidt 𝕜 x k := by
  rw [mgsRun_eq_sub_sum (fun i j hij => gramSchmidtNormed_pairwise_orthogonal x hij),
    ← Nat.Iio_eq_range]
  exact (gramSchmidt_eq_sub_sum x k).symm

/-- The first step of Algorithm 1.2: `q_1 = x_1 / ‖x_1‖`, the inner loop being empty. -/
@[simp]
theorem modifiedGramSchmidt_zero (x : ℕ → 𝔼) :
    modifiedGramSchmidt x 0 = ((‖x 0‖ : 𝕜)⁻¹) • x 0 := by
  rw [modifiedGramSchmidt]

/-- The later steps of Algorithm 1.2: the running vector of the inner loop, normalized. The
clamp in the definition is invisible, since the loop reads only the vectors already computed. -/
theorem modifiedGramSchmidt_succ (x : ℕ → 𝔼) (j : ℕ) :
    modifiedGramSchmidt x (j + 1)
      = ((‖mgsRun (modifiedGramSchmidt x) (x (j + 1)) (j + 1)‖ : 𝕜)⁻¹)
        • mgsRun (modifiedGramSchmidt x) (x (j + 1)) (j + 1) := by
  rw [modifiedGramSchmidt,
    mgsRun_congr (q := fun i => modifiedGramSchmidt x (min i j)) (q' := modifiedGramSchmidt x)
      (x (j + 1)) fun i hi => by rw [Nat.min_eq_left (Nat.lt_succ_iff.1 hi)]]

/-- Saad §1.7: **Algorithm 1.2 computes the vectors of Algorithm 1.1**, `q_j` for `q_j`. -/
theorem modifiedGramSchmidt_eq (x : ℕ → 𝔼) (j : ℕ) :
    modifiedGramSchmidt x j = gramSchmidtNormed 𝕜 x j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero =>
      have h0 : gramSchmidt 𝕜 x 0 = x 0 := (mgsRun_gramSchmidtNormed x 0).symm
      rw [modifiedGramSchmidt_zero, gramSchmidtNormed, h0]
    | succ k =>
      rw [modifiedGramSchmidt_succ, mgsRun_congr _ (fun i hi => ih i hi),
        mgsRun_gramSchmidtNormed, gramSchmidtNormed]

/-- Saad §1.7: **Algorithm 1.2 computes the coefficients of Algorithm 1.1**, `r_ij` for `r_ij`,
although it reads each of them off the running vector rather than off `x_j`. -/
theorem modifiedGramSchmidtCoeff_eq (x : ℕ → 𝔼) {i j : ℕ} (hij : i ≤ j) :
    modifiedGramSchmidtCoeff x i j = inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) := by
  have hvec : modifiedGramSchmidt x = gramSchmidtNormed 𝕜 x := funext (modifiedGramSchmidt_eq x)
  rw [modifiedGramSchmidtCoeff, hvec]
  rcases lt_or_eq_of_le hij with h | h
  · rw [ite_eq_left h]
    exact inner_mgsRun_self (fun a b hab => gramSchmidtNormed_pairwise_orthogonal x hab) (x j) i
  · subst h
    rw [ite_eq_right (lt_irrefl i), ite_eq_left rfl, mgsRun_gramSchmidtNormed,
      inner_gramSchmidtNormed_self]

/-- Saad §1.7: **in exact arithmetic Algorithm 1.2 computes the same `Q` and the same `R` as
Algorithm 1.1**. Neither half needs a hypothesis on `x`: past a breakdown both algorithms return
the zero vector and the zero coefficient. -/
theorem algorithm_1_2_eq (x : ℕ → 𝔼) :
    modifiedGramSchmidt x = gramSchmidtNormed 𝕜 x ∧
      ∀ i j, i ≤ j → modifiedGramSchmidtCoeff x i j = inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) :=
  ⟨funext (modifiedGramSchmidt_eq x), fun _ _ hij => modifiedGramSchmidtCoeff_eq x hij⟩

/-! ### (1.19): the QR factorization -/

/-- Saad **(1.19)**: a matrix `X` whose columns are linearly independent factors as `X = Q R`
with `Qᴴ Q = 1` and `R` upper triangular with positive diagonal, and the pair `(Q, R)` is unique.
`Q` is the Gram–Schmidt orthonormalization of the columns and `R i j = (x_j, q_i)`. -/
theorem equation_1_19 {r : ℕ} (X : Matrix (Fin n) (Fin r) 𝕜) (hX : LinearIndependent 𝕜 Xᵀ) :
    ∃! QR : Matrix (Fin n) (Fin r) 𝕜 × Matrix (Fin r) (Fin r) 𝕜,
      X = QR.1 * QR.2 ∧ QR.1ᴴ * QR.1 = 1 ∧ QR.2.IsUpperTriangular ∧ ∀ j, 0 < QR.2.diag j := by
  obtain ⟨Q, R, hXQR, hQ, hR, hd⟩ := Matrix.exists_qr X hX
  refine ⟨(Q, R), ⟨hXQR, hQ, hR, hd⟩, ?_⟩
  rintro ⟨Q', R'⟩ ⟨hXQR', hQ', hR', hd'⟩
  obtain ⟨hQQ, hRR⟩ := Matrix.qr_unique hXQR' hXQR hQ' hQ hR' hR hd' hd
  exact Prod.ext hQQ hRR

/-! ### (1.20)–(1.28): Householder orthogonalization -/

/-- Saad **(1.20)–(1.22)**: the Householder reflector `P = 1 - 2 w wᴴ` of the unit vector
`w = (x + sign(ξ_i) ‖x‖₂ e_i) / ‖x + sign(ξ_i) ‖x‖₂ e_i‖₂` is involutive and unitary, and it sends
`x` to `-sign(ξ_i) ‖x‖₂ e_i`: one reflector annihilates every entry of `x` but the `i`-th.

The book's `sign(ξ₁)` is `Matrix.phase`, which is `1` at `0` and `z/|z|` elsewhere, so the
statement is the complex one of §1.7 as well as the real one. The derivation printed in the book,
`2 (x - α e₁)ᵀ x = ‖x - α e₁‖₂²` forcing `α = ± ‖x‖₂`, is the computation behind
`Matrix.householder_mulVec_eq_smul_single`; the `‖x‖₁²` printed there is an error for `‖x‖₂²`. -/
theorem equation_1_22 {x : Fin n → 𝕜} (hx : x ≠ 0) (i : Fin n) :
    householder (householderVec x i) * householder (householderVec x i) = 1 ∧
      householder (householderVec x i) ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧
      householder (householderVec x i) *ᵥ x
        = (-(phase (x i) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 (Fin n))‖ : 𝕜))))
          • (Pi.single i 1 : Fin n → 𝕜) :=
  ⟨householder_mul_self (star_dotProduct_householderVec_self hx i),
    householder_householderVec_mem_unitaryGroup hx i,
    householder_mulVec_eq_smul_single hx i⟩

/-- Saad **(1.23)–(1.26)**: the `k`-th reflector of Algorithm 1.3 acts on the entries from `k` on
only. Where `x` already vanishes away from the pivot, so does the reflector's axis, and the
reflector leaves that entry of every vector alone.

The book's (1.25) prints the axis as `z_i = β + x_ii`, a transcription slip for `β + x_kk`, the
pivot of the `k`-th step; the backbone's `Matrix.householderAxis` has the correct form, which is
the one Algorithm 1.3 needs. -/
theorem householder_mulVec_apply_of_eq_zero {x : Fin n → 𝕜} {i s : Fin n} (hsi : s ≠ i)
    (hs : x s = 0) (z : Fin n → 𝕜) : (householder (householderVec x i) *ᵥ z) s = z s := by
  rw [householder_mulVec, Pi.sub_apply, Pi.smul_apply, householderVec_apply_eq_zero hsi hs,
    smul_zero, sub_zero]

/-- Saad's `E_m = [e₁, e₂, …, e_m]` of (1.28): the first `m` columns of the `n × n` identity
matrix. -/
def stdCols (𝕜 : Type*) [RCLike 𝕜] (n m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

/-- The entries of `E_m`: `1` on the diagonal and `0` elsewhere. -/
@[simp]
theorem stdCols_apply {m : ℕ} (i : Fin n) (j : Fin m) :
    stdCols 𝕜 n m i j = if (i : ℕ) = (j : ℕ) then 1 else 0 := rfl

/-- `E_mᴴ E_m = 1`: the columns of `E_m` are orthonormal, since there are no more of them than
there are rows. -/
theorem conjTranspose_stdCols_mul_self {m : ℕ} (hmn : m ≤ n) :
    (stdCols 𝕜 n m)ᴴ * stdCols 𝕜 n m = 1 := by
  ext i j
  rw [mul_apply, Finset.sum_eq_single (Fin.castLE hmn i), one_apply]
  · rw [conjTranspose_apply, stdCols_apply, stdCols_apply]
    simp [Fin.ext_iff]
  · intro k _ hk
    have hki : ¬((k : ℕ) = (i : ℕ)) := fun h => hk (Fin.ext h)
    rw [conjTranspose_apply, stdCols_apply, ite_eq_right hki, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `E_mᴴ` selects the first `m` rows. -/
theorem conjTranspose_stdCols_mul_apply {m k : ℕ} (hmn : m ≤ n) (M : Matrix (Fin n) (Fin k) 𝕜)
    (i : Fin m) (j : Fin k) : ((stdCols 𝕜 n m)ᴴ * M) i j = M (Fin.castLE hmn i) j := by
  rw [mul_apply, Finset.sum_eq_single (Fin.castLE hmn i)]
  · rw [conjTranspose_apply, stdCols_apply]
    simp
  · intro k' _ hk'
    have hki : ¬((k' : ℕ) = (i : ℕ)) := fun h => hk' (Fin.ext h)
    rw [conjTranspose_apply, stdCols_apply, ite_eq_right hki, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `E_m E_mᴴ` restores a matrix whose rows below the `m`-th vanish. -/
theorem stdCols_mul_conjTranspose_stdCols_mul {m k : ℕ} (hmn : m ≤ n)
    {M : Matrix (Fin n) (Fin k) 𝕜} (hM : ∀ (i : Fin n) (j : Fin k), m ≤ (i : ℕ) → M i j = 0) :
    stdCols 𝕜 n m * ((stdCols 𝕜 n m)ᴴ * M) = M := by
  ext i j
  rw [mul_apply]
  by_cases hi : (i : ℕ) < m
  · rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin m)]
    · rw [stdCols_apply, conjTranspose_stdCols_mul_apply hmn]
      have hcast : Fin.castLE hmn (⟨(i : ℕ), hi⟩ : Fin m) = i := Fin.ext rfl
      rw [hcast]
      simp
    · intro k' _ hk'
      have hik : ¬((i : ℕ) = (k' : ℕ)) := fun h => hk' (Fin.ext h.symm)
      rw [stdCols_apply, ite_eq_right hik, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [hM i j (Nat.not_lt.1 hi)]
    refine Finset.sum_eq_zero fun k' _ => ?_
    have hik : ¬((i : ℕ) = (k' : ℕ)) := by
      have := k'.isLt
      omega
    rw [stdCols_apply, ite_eq_right hik, zero_mul]

/-- The algebra behind (1.28): once a unitary `P` has made `P X` upper triangular, `Q = Pᴴ E_m`
has orthonormal columns, `R = E_mᴴ P X` is upper triangular, and `X = Q R`. -/
private theorem factorization_of_unitary_mul_upperTriangular {m : ℕ} (hmn : m ≤ n)
    {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P ∈ Matrix.unitaryGroup (Fin n) 𝕜)
    {X : Matrix (Fin n) (Fin m) 𝕜}
    (hT : ∀ (i : Fin n) (j : Fin m), (j : ℕ) < (i : ℕ) → (P * X) i j = 0) :
    X = (Pᴴ * stdCols 𝕜 n m) * ((stdCols 𝕜 n m)ᴴ * (P * X)) ∧
      (Pᴴ * stdCols 𝕜 n m)ᴴ * (Pᴴ * stdCols 𝕜 n m) = 1 ∧
      ((stdCols 𝕜 n m)ᴴ * (P * X)).IsUpperTriangular := by
  have hPP : Pᴴ * P = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hP
    rwa [Matrix.star_eq_conjTranspose] at h
  have hPPh : P * Pᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.1 hP
    rwa [Matrix.star_eq_conjTranspose] at h
  refine ⟨?_, ?_, ?_⟩
  · have hrows : ∀ (i : Fin n) (j : Fin m), m ≤ (i : ℕ) → (P * X) i j = 0 := fun i j hi =>
      hT i j (by have := j.isLt; omega)
    calc X = Pᴴ * (P * X) := by rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
      _ = Pᴴ * (stdCols 𝕜 n m * ((stdCols 𝕜 n m)ᴴ * (P * X))) := by
          rw [stdCols_mul_conjTranspose_stdCols_mul hmn hrows]
      _ = (Pᴴ * stdCols 𝕜 n m) * ((stdCols 𝕜 n m)ᴴ * (P * X)) := (Matrix.mul_assoc _ _ _).symm
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (stdCols 𝕜 n m)ᴴ * P * (Pᴴ * stdCols 𝕜 n m)
        = (stdCols 𝕜 n m)ᴴ * (P * Pᴴ * stdCols 𝕜 n m) := by simp only [Matrix.mul_assoc]
      _ = (stdCols 𝕜 n m)ᴴ * stdCols 𝕜 n m := by rw [hPPh, Matrix.one_mul]
      _ = 1 := conjTranspose_stdCols_mul_self hmn
  · intro i j hji
    rw [conjTranspose_stdCols_mul_apply hmn]
    exact hT (Fin.castLE hmn i) j hji

/-- Saad **(1.27)–(1.28)** and **Algorithm 1.3**: a product `P = P_m ⋯ P_1` of Householder
reflectors carries `X` to upper triangular form, `P X = E_m R`, so that `X = Pᴴ E_m R` with
`Q = Pᴴ E_m` of orthonormal columns and `R = E_mᴴ P X` upper triangular. No hypothesis on the
columns of `X` is needed for this; how the pair compares with the factorization (1.19), whose `R`
has a positive diagonal, is `equation_1_28_normalized`. -/
theorem equation_1_28 {m : ℕ} (hmn : m ≤ n) (X : Matrix (Fin n) (Fin m) 𝕜) :
    ∃ P ∈ Matrix.unitaryGroup (Fin n) 𝕜,
      (∀ (i : Fin n) (j : Fin m), (j : ℕ) < (i : ℕ) → (P * X) i j = 0) ∧
        X = (Pᴴ * stdCols 𝕜 n m) * ((stdCols 𝕜 n m)ᴴ * (P * X)) ∧
        (Pᴴ * stdCols 𝕜 n m)ᴴ * (Pᴴ * stdCols 𝕜 n m) = 1 ∧
        ((stdCols 𝕜 n m)ᴴ * (P * X)).IsUpperTriangular := by
  obtain ⟨P, hP, hT⟩ := Matrix.exists_unitary_mul_upperTriangular X
  exact ⟨P, hP, hT, factorization_of_unitary_mul_upperTriangular hmn hP hT⟩

/-- Two factorizations of the same matrix with orthonormal columns differ by the unitary matrix
`D = R₀ R⁻¹`: it carries `Q₀` to `Q` and `R₀` to `R`. This is the computation inside
`Matrix.qr_unique`, kept without the normalization that makes `D = 1`. -/
private theorem qr_change_of_factor {m : ℕ} {X Q₀ Q : Matrix (Fin n) (Fin m) 𝕜}
    {R₀ R : Matrix (Fin m) (Fin m) 𝕜} (hX₀ : X = Q₀ * R₀) (hX : X = Q * R)
    (hQ₀ : Q₀ᴴ * Q₀ = 1) (hQ : Qᴴ * Q = 1) (hdet : IsUnit R.det) :
    (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹) = 1 ∧ Q = Q₀ * (R₀ * R⁻¹) ∧ R = (R₀ * R⁻¹)ᴴ * R₀ := by
  have hRR : R₀ᴴ * R₀ = Rᴴ * R := by
    have h1 : Xᴴ * X = R₀ᴴ * R₀ := by
      rw [hX₀, conjTranspose_mul]
      calc R₀ᴴ * Q₀ᴴ * (Q₀ * R₀) = R₀ᴴ * (Q₀ᴴ * Q₀ * R₀) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = R₀ᴴ * R₀ := by rw [hQ₀, Matrix.one_mul]
    have h2 : Xᴴ * X = Rᴴ * R := by
      rw [hX, conjTranspose_mul]
      calc Rᴴ * Qᴴ * (Q * R) = Rᴴ * (Qᴴ * Q * R) := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = Rᴴ * R := by rw [hQ, Matrix.one_mul]
    rw [← h1, h2]
  have hDu : (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹) = 1 := by
    have h1 : (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹) = (R⁻¹)ᴴ * (R₀ᴴ * R₀ * R⁻¹) := by
      rw [conjTranspose_mul]; noncomm_ring
    have h2 : (R⁻¹)ᴴ * (Rᴴ * R * R⁻¹) = (R * R⁻¹)ᴴ * (R * R⁻¹) := by
      rw [conjTranspose_mul]; noncomm_ring
    rw [h1, hRR, h2, mul_nonsing_inv R hdet, conjTranspose_one, mul_one]
  refine ⟨hDu, ?_, ?_⟩
  · calc Q = Q * (R * R⁻¹) := by rw [mul_nonsing_inv R hdet, Matrix.mul_one]
      _ = Q * R * R⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = Q₀ * R₀ * R⁻¹ := by rw [← hX, hX₀]
      _ = Q₀ * (R₀ * R⁻¹) := Matrix.mul_assoc _ _ _
  · have hDR : R₀ * R⁻¹ * R = R₀ := by
      rw [Matrix.mul_assoc, nonsing_inv_mul R hdet, Matrix.mul_one]
    calc R = (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹) * R := by rw [hDu, Matrix.one_mul]
      _ = (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹ * R) := Matrix.mul_assoc _ _ _
      _ = (R₀ * R⁻¹)ᴴ * R₀ := by rw [hDR]

/-- Saad §1.7: **Algorithm 1.3 and the Gram–Schmidt process differ only by the signs of the
columns**. Given the factorization (1.19) of `X`, there is a product `P` of Householder reflectors
and a unitary upper triangular — hence diagonal, of unit-modulus entries — matrix `D` with
`Q = Pᴴ E_m D` and `R = Dᴴ E_mᴴ P X`. Normalizing those signs, that is replacing the reflector
factors by `Pᴴ E_m D` and `Dᴴ E_mᴴ P X`, therefore produces the pair of (1.19) itself, which by
the uniqueness there is the Gram–Schmidt pair. -/
theorem equation_1_28_normalized {m : ℕ} (hmn : m ≤ n) {X Q : Matrix (Fin n) (Fin m) 𝕜}
    {R : Matrix (Fin m) (Fin m) 𝕜} (hXQR : X = Q * R) (hQ : Qᴴ * Q = 1)
    (hR : R.IsUpperTriangular) (hd : ∀ j, 0 < R.diag j) :
    ∃ P ∈ Matrix.unitaryGroup (Fin n) 𝕜, ∃ D : Matrix (Fin m) (Fin m) 𝕜,
      (∀ (i : Fin n) (j : Fin m), (j : ℕ) < (i : ℕ) → (P * X) i j = 0) ∧
        Dᴴ * D = 1 ∧ D.IsUpperTriangular ∧ Q = (Pᴴ * stdCols 𝕜 n m) * D ∧
        R = Dᴴ * ((stdCols 𝕜 n m)ᴴ * (P * X)) := by
  obtain ⟨P, hP, hT⟩ := Matrix.exists_unitary_mul_upperTriangular X
  obtain ⟨hX₀, hQ₀, hR₀⟩ := factorization_of_unitary_mul_upperTriangular hmn hP hT
  have hd' : ∀ j, 0 < R j j := hd
  have hdet : IsUnit R.det := by
    rw [det_of_isUpperTriangular hR, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (hd' j).ne'
  have : Invertible R := invertibleOfIsUnitDet R hdet
  obtain ⟨hDu, hQeq, hReq⟩ := qr_change_of_factor hX₀ hXQR hQ₀ hQ hdet
  exact ⟨P, hP, _, hT, hDu, hR₀.mul (blockTriangular_inv_of_blockTriangular hR), hQeq, hReq⟩

end SaadSparse.Ch01
