import Numlib.LinearAlgebra.Matrix.SaddlePoint
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.Analysis.Matrix.ToEuclideanLin
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Null space reduction for saddle-point systems

For a constraint $Bx=g$, a null basis $Z$ parametrizes the feasible affine space as
$x=\hat x+Zv$, where $B\hat x=g$. Projecting the first saddle-point equation against $Z$
gives the reduced matrix $Z^TAZ$. When $B$ has full row rank, the multiplier is recovered
by solving a system with coefficient $BB^T$.

## Main definitions

* `Matrix.IsNullBasis`: the columns of $Z$ are independent and span the kernel of $B$.

## Main results

* `Matrix.IsNullBasis.mulVec_eq_iff_existsUnique`: feasible vectors have unique null coordinates.
* `Matrix.IsNullBasis.isUnit_compress_of_hermitianPart`: semidefiniteness and a trivial kernel
  intersection imply invertibility of the reduced matrix.
* `Matrix.IsNullBasis.posDef_compress`: the compression is positive definite if $A$ is symmetric.
* `Matrix.fromBlocks_transpose_zero_mulVec_eq_iff_nullSpace`: the projected primal equation and
  the multiplier normal equation are equivalent to the full equations, with reconstruction.
* `Matrix.isNullBasis_fundamental` and `Matrix.isNullBasis_of_split_qr`: nonsingular pivot
  columns and a split orthogonal QR factorization give two ways to obtain a null basis.
* `Matrix.inv_fromBlocks_transpose_zero_of_nullBasis`: the inverse is expressible using the
  reduced Hessian and multiplier Gram matrix, with no inverse of $A$.
-/

open scoped Matrix
open WithLp

namespace Matrix

variable {K n m k p : Type*} [Fintype n] [Fintype m] [Fintype k]

section Field

variable [Field K] {B : Matrix m n K} {Z : Matrix n k K}

/-- For finite matrices over a field, $Z$ is a **null basis** of $B$ if $v\mapsto Zv$ is
injective and its range is $\ker B$. Thus each vector of the kernel has unique coordinates. -/
structure IsNullBasis (B : Matrix m n K) (Z : Matrix n k K) : Prop where
  /-- The columns of $Z$ are linearly independent. -/
  injective : Function.Injective Z.mulVec
  /-- The columns of $Z$ span the kernel of $B$. -/
  range_eq_ker : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin

omit [Fintype m] in
/-- For a null basis $Z$ of a matrix $B$ over a field, $BZ=0$. -/
theorem IsNullBasis.mul_eq_zero (hZ : IsNullBasis B Z) : B * Z = 0 := by
  apply Matrix.mulVec_injective
  funext v
  rw [← mulVec_mulVec, zero_mulVec]
  have hv : Z *ᵥ v ∈ LinearMap.range Z.mulVecLin := ⟨v, rfl⟩
  rw [hZ.range_eq_ker] at hv
  exact hv

omit [Fintype m] in
/-- Let $Z$ be a null basis of $B$, and let $B\hat x=g$. A vector $x$ satisfies $Bx=g$ if
and only if there is a unique coordinate vector $v$ such that $x=Zv+\hat x$. -/
theorem IsNullBasis.mulVec_eq_iff_existsUnique (hZ : IsNullBasis B Z)
    {x xhat : n → K} {g : m → K} (hxhat : B *ᵥ xhat = g) :
    B *ᵥ x = g ↔ ∃! v : k → K, x = Z *ᵥ v + xhat := by
  have hmem : B *ᵥ x = g ↔ x - xhat ∈ LinearMap.range Z.mulVecLin := by
    rw [hZ.range_eq_ker, LinearMap.mem_ker, mulVecLin_apply, mulVec_sub, hxhat, sub_eq_zero]
  rw [hmem, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    have hx : x = Z *ᵥ v + xhat := (sub_eq_iff_eq_add.mp hv.symm)
    refine ⟨v, hx, fun w hw => hZ.injective ?_⟩
    exact add_right_cancel (hw.symm.trans hx)
  · rintro ⟨v, hv, -⟩
    exact ⟨v, (sub_eq_iff_eq_add.mpr hv).symm⟩

omit [Fintype m] in
/-- The number of columns of a null basis equals the dimension of the kernel. -/
theorem IsNullBasis.finrank (hZ : IsNullBasis B Z) :
    Module.finrank K (LinearMap.ker B.mulVecLin) = Fintype.card k := by
  rw [← hZ.range_eq_ker, LinearMap.finrank_range_of_inj hZ.injective,
    Module.finrank_fintype_fun_eq_card]

omit [Fintype m] in
/-- Reordering the primal coordinates by an equivalence $e:p\simeq n$ preserves a null basis:
if $Z$ is a null basis of $B$, reindexing the rows of $Z$ and the columns of $B$ by $e$ gives
a null basis of the reindexed matrix. -/
theorem IsNullBasis.reindex [Fintype p] (hZ : IsNullBasis B Z) (e : p ≃ n) :
    IsNullBasis (B.submatrix id e) (Z.submatrix e id) := by
  have hZapply (v : k → K) : Z.submatrix e id *ᵥ v = (Z *ᵥ v) ∘ e := rfl
  have hBapply (x : p → K) : B.submatrix id e *ᵥ x = B *ᵥ (x ∘ e.symm) := by
    simpa using submatrix_mulVec_equiv B x id e
  refine ⟨fun u v huv => hZ.injective ?_, ?_⟩
  · rw [hZapply, hZapply] at huv
    exact e.surjective.injective_comp_right huv
  · ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker, mulVecLin_apply, hBapply]
    simp only [mulVecLin_apply, hZapply]
    constructor
    · rintro ⟨v, rfl⟩
      rw [Function.comp_assoc, e.self_comp_symm, Function.comp_id, mulVec_mulVec, hZ.mul_eq_zero,
        zero_mulVec]
    · intro hx
      have hx' : x ∘ e.symm ∈ LinearMap.range Z.mulVecLin := by
        rwa [hZ.range_eq_ker, LinearMap.mem_ker, mulVecLin_apply]
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hx'
      exact ⟨v, by rw [show Z *ᵥ v = x ∘ e.symm from hv, Function.comp_assoc,
        e.symm_comp_self, Function.comp_id]⟩

/-- For a column partition $B=[B_b\ B_n]$ over a field with $B_b$ invertible, the
**fundamental basis** $\begin{bmatrix}-B_b^{-1} B_n\\I\end{bmatrix}$ is a null basis of $B$. -/
theorem isNullBasis_fundamental [DecidableEq m] [DecidableEq k]
    {Bb : Matrix m m K} (Bn : Matrix m k K) (hBb : IsUnit Bb) :
    IsNullBasis (fromCols Bb Bn) (fromRows (-(Bb⁻¹ * Bn)) 1) := by
  have hcancel := mul_nonsing_inv_cancel_left Bb Bn ((isUnit_iff_isUnit_det _).mp hBb)
  refine ⟨fun u v huv => ?_, ?_⟩
  · simp only [fromRows_mulVec, one_mulVec, Sum.elim_eq_iff] at huv
    exact huv.2
  · ext x
    rw [← Sum.elim_comp_inl_inr x]
    simp only [LinearMap.mem_range, LinearMap.mem_ker, mulVecLin_apply, fromRows_mulVec,
      fromCols_mulVec_sumElim, one_mulVec, Sum.elim_eq_iff]
    constructor
    · rintro ⟨v, hv, hcoord⟩
      rw [← hv, ← hcoord, neg_mulVec, mulVec_neg, mulVec_mulVec, hcancel, neg_add_cancel]
    · intro hx
      refine ⟨x ∘ Sum.inr, (mulVec_injective_of_isUnit hBb) ?_, rfl⟩
      rw [neg_mulVec, mulVec_neg, mulVec_mulVec, hcancel]
      exact (eq_neg_iff_add_eq_zero.mpr hx).symm

end Field

section Real

variable {A : Matrix n n ℝ} {B : Matrix m n ℝ} {Z : Matrix n k ℝ}

omit [Fintype m] in
private theorem IsNullBasis.dotProduct_compress_pos (hZ : IsNullBasis B Z)
    (hA : (hermitianPart A).PosSemidef)
    (hker : LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {v : k → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((Zᵀ * A * Z) *ᵥ v) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm,
    ← dotProduct_mulVec_hermitianPart]
  have hz : Z *ᵥ v ≠ 0 := fun h => hv (hZ.injective (h.trans (mulVec_zero _).symm))
  have hBv : Z *ᵥ v ∈ LinearMap.ker B.mulVecLin := hZ.range_eq_ker ▸ ⟨v, rfl⟩
  have hn : hermitianPart A *ᵥ (Z *ᵥ v) ≠ 0 := fun h =>
    hz ((Submodule.eq_bot_iff _).1 hker _ ⟨h, hBv⟩)
  have hnonneg : 0 ≤ (Z *ᵥ v) ⬝ᵥ (hermitianPart A *ᵥ (Z *ᵥ v)) := by
    simpa using hA.dotProduct_mulVec_nonneg (Z *ᵥ v)
  refine lt_of_le_of_ne hnonneg (Ne.symm fun h => hn (hA.dotProduct_mulVec_zero_iff.mp ?_))
  simpa using h

omit [Fintype m] in
/-- Let $Z$ be a null basis of a real matrix $B$. If the symmetric part $H$ of $A$ is
positive semidefinite and $\ker H\cap\ker B=\{0\}$, then $Z^TAZ$ is nonsingular. -/
theorem IsNullBasis.isUnit_compress_of_hermitianPart [DecidableEq k] (hZ : IsNullBasis B Z)
    (hA : (hermitianPart A).PosSemidef)
    (hker : LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    IsUnit (Zᵀ * A * Z) := by
  apply isUnit_of_posDef_hermitianPart
  exact (posDef_hermitianPart_iff_forall_dotProduct_mulVec_pos _).2
    (fun v hv => by simpa using hZ.dotProduct_compress_pos hA hker hv)

omit [Fintype m] in
/-- Let $Z$ be a null basis of a real matrix $B$. If $A$ is symmetric positive semidefinite
and $\ker A\cap\ker B=\{0\}$, then $Z^TAZ$ is symmetric positive definite. -/
theorem IsNullBasis.posDef_compress (hZ : IsNullBasis B Z) (hA : A.PosSemidef)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    (Zᵀ * A * Z).PosDef := by
  have hH := hA.isHermitian.hermitianPart_eq
  have hsym := isHermitian_conjTranspose_mul_mul Z hA.isHermitian
  refine PosDef.of_dotProduct_mulVec_pos (by simpa using hsym) fun v hv => ?_
  simpa using hZ.dotProduct_compress_pos (hH.symm ▸ hA) (by rwa [hH]) hv

omit [Fintype m] in
private theorem range_toEuclideanLin_eq_ker [DecidableEq k] [DecidableEq n]
    (hZ : IsNullBasis B Z) : LinearMap.range Z.toEuclideanLin = LinearMap.ker B.toEuclideanLin := by
  ext x
  rw [← toLp_ofLp 2 x, LinearMap.mem_range, LinearMap.mem_ker, toEuclideanLin_toLp]
  constructor
  · rintro ⟨v, hv⟩
    rw [← toLp_ofLp 2 v, toEuclideanLin_toLp] at hv
    have hx : ofLp x ∈ LinearMap.range Z.mulVecLin :=
      ⟨ofLp v, congrArg ofLp hv⟩
    rw [hZ.range_eq_ker, LinearMap.mem_ker, mulVecLin_apply] at hx
    rw [hx, WithLp.toLp_zero]
  · intro hx
    have hx' : ofLp x ∈ LinearMap.range Z.mulVecLin := by
      rw [hZ.range_eq_ker, LinearMap.mem_ker, mulVecLin_apply]
      exact congrArg ofLp hx
    obtain ⟨v, hv⟩ := hx'
    exact ⟨toLp 2 v, by rw [toEuclideanLin_toLp]; exact congrArg (toLp 2) hv⟩

private theorem exists_transpose_mulVec_eq_of_nullBasis
    (hZ : IsNullBasis B Z) {r : n → ℝ} (hr : Zᵀ *ᵥ r = 0) :
    ∃ y, Bᵀ *ᵥ y = r := by
  classical
  have h := (Z.toEuclideanLin : _ →ₗ[ℝ] _).orthogonal_range
  rw [range_toEuclideanLin_eq_ker hZ, LinearMap.orthogonal_ker,
    ← toEuclideanLin_transpose_eq_adjoint, ← toEuclideanLin_transpose_eq_adjoint] at h
  have hm : toLp 2 r ∈ LinearMap.range Bᵀ.toEuclideanLin := by
    rw [h, LinearMap.mem_ker, toEuclideanLin_toLp, hr, WithLp.toLp_zero]
  obtain ⟨y, hy⟩ := hm
  exact ⟨ofLp y, congrArg ofLp hy⟩

/-- Let $Z$ be a null basis of a real matrix $B$ of full row rank, and let $B\hat x=g$.
A pair $(x,y)$ solves $Ax+B^Ty=f$, $Bx=g$ if and only if some $v$ satisfies
$$x=Zv+\hat x,\qquad Z^TAZv=Z^T(f-A\hat x),\qquad BB^Ty=B(f-Ax).$$
No nonsingularity of $A$ or $Z^TAZ$ is needed for this equivalence. -/
theorem fromBlocks_transpose_zero_mulVec_eq_iff_nullSpace (hZ : IsNullBasis B Z)
    (hB : Function.Injective Bᵀ.mulVec) {xhat x f : n → ℝ} {y g : m → ℝ}
    (hxhat : B *ᵥ xhat = g) :
    fromBlocks A Bᵀ B (0 : Matrix m m ℝ) *ᵥ Sum.elim x y = Sum.elim f g ↔
      ∃ v : k → ℝ, x = Z *ᵥ v + xhat ∧
        (Zᵀ * A * Z) *ᵥ v = Zᵀ *ᵥ (f - A *ᵥ xhat) ∧
        (B * Bᵀ) *ᵥ y = B *ᵥ (f - A *ᵥ x) := by
  classical
  have hZB : Zᵀ * Bᵀ = 0 := by rw [← transpose_mul, hZ.mul_eq_zero, transpose_zero]
  have hproj (v : k → ℝ) :
      (Zᵀ * A * Z) *ᵥ v = Zᵀ *ᵥ (f - A *ᵥ xhat) ↔
        Zᵀ *ᵥ (f - A *ᵥ (Z *ᵥ v + xhat)) = 0 := by
    simp only [← mulVec_mulVec, mulVec_add, mulVec_sub, sub_eq_zero, eq_sub_iff_add_eq]
    exact eq_comm
  simp only [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero,
    Sum.elim_eq_iff]
  constructor
  · rintro ⟨htop, hbot⟩
    obtain ⟨v, hx, -⟩ := (hZ.mulVec_eq_iff_existsUnique hxhat).1 hbot
    have hr : f - A *ᵥ x = Bᵀ *ᵥ y := sub_eq_iff_eq_add.mpr (htop.symm.trans (add_comm _ _))
    refine ⟨v, hx, (hproj v).2 ?_, ?_⟩
    · rw [← hx, hr, mulVec_mulVec, hZB, zero_mulVec]
    · rw [hr, mulVec_mulVec]
  · rintro ⟨v, hx, hv, hy⟩
    have hr : Zᵀ *ᵥ (f - A *ᵥ x) = 0 := by rw [hx]; exact (hproj v).1 hv
    obtain ⟨w, hw⟩ := exists_transpose_mulVec_eq_of_nullBasis hZ hr
    have hGram : (B * Bᵀ).PosDef := by
      simpa using PosDef.one.conjTranspose_mul_mul_same (B := Bᵀ) hB
    have hyw := (mulVec_injective_of_isUnit hGram.isUnit)
      (hy.trans (by rw [← hw, mulVec_mulVec]))
    refine ⟨?_, ?_⟩
    · rw [hyw, hw, add_comm, sub_add_cancel]
    · rw [hx, mulVec_add, mulVec_mulVec, hZ.mul_eq_zero, zero_mulVec, zero_add, hxhat]

/-- Let $Q=[Q_1\ Q_2]$ be a real square orthogonal matrix and suppose
$B^T=Q\begin{bmatrix}R\\0\end{bmatrix}$ with $R$ square and nonsingular.
Then the trailing columns $Q_2$ form a null basis of $B$ and satisfy $Q_2^TQ_2=I$. -/
theorem isNullBasis_of_split_qr [DecidableEq m] [DecidableEq k]
    {B : Matrix m (m ⊕ k) ℝ} {Q₁ : Matrix (m ⊕ k) m ℝ} {Q₂ : Matrix (m ⊕ k) k ℝ}
    {R : Matrix m m ℝ}
    (hQ : (fromCols Q₁ Q₂)ᵀ * fromCols Q₁ Q₂ = 1)
    (hfact : Bᵀ = fromCols Q₁ Q₂ * fromRows R 0) (hR : IsUnit R) :
    IsNullBasis B Q₂ ∧ Q₂ᵀ * Q₂ = 1 := by
  have h₂ : Q₂ᵀ * Q₂ = 1 := by
    have h := congrArg toBlocks₂₂ hQ
    rw [transpose_fromCols, fromRows_mul_fromCols, toBlocks_fromBlocks₂₂] at h
    exact h.trans (by ext row col; simp [toBlocks₂₂, Matrix.one_apply])
  have hBQ : B * fromCols Q₁ Q₂ = fromCols Rᵀ (0 : Matrix m k ℝ) := by
    conv_lhs => rw [← transpose_transpose B, hfact, transpose_mul, Matrix.mul_assoc, hQ,
      Matrix.mul_one, transpose_fromRows, transpose_zero]
  have hnull : B * Q₂ = 0 := by
    rw [mul_fromCols] at hBQ
    exact congrArg (fun M : Matrix m (m ⊕ k) ℝ => M.submatrix id Sum.inr) hBQ
  have hinj : Function.Injective Q₂.mulVec := by
    intro u v huv
    have h := congrArg (fun w => Q₂ᵀ *ᵥ w) huv
    simpa only [mulVec_mulVec, h₂, one_mulVec] using h
  refine ⟨⟨hinj, ?_⟩, h₂⟩
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · rintro ⟨v, rfl⟩
    rw [mulVecLin_apply, mulVec_mulVec, hnull, zero_mulVec]
  · intro hx
    let Q := fromCols Q₁ Q₂
    let w := Qᵀ *ᵥ x
    have hw : Q *ᵥ w = x := by
      rw [show w = Qᵀ *ᵥ x from rfl, mulVec_mulVec, mul_eq_one_comm.mp hQ, one_mulVec]
    have hhead : Rᵀ *ᵥ (w ∘ Sum.inl) = 0 := by
      have hz : B *ᵥ (Q *ᵥ w) = 0 := by rwa [hw]
      rwa [mulVec_mulVec, show B * Q = _ from hBQ, fromCols_mulVec, zero_mulVec, add_zero] at hz
    have hzero : w ∘ Sum.inl = 0 :=
      (mulVec_injective_of_isUnit ((isUnit_transpose R).2 hR)) (hhead.trans (mulVec_zero _).symm)
    exact ⟨w ∘ Sum.inr, by simpa [Q, hzero] using hw⟩

/-- Let $Z$ be a null basis of a real matrix $B$ of full row rank, and suppose $Z^TAZ$ is
nonsingular. Set $G=BB^T$ and $W=Z(Z^TAZ)^{-1}Z^T$. Then
$$\begin{bmatrix}A&B^T\\B&0\end{bmatrix}^{-1}
 = \begin{bmatrix}
     W & (I-WA)B^TG^{-1}\\
     G^{-1}B(I-AW) & -G^{-1}B(A-AWA)B^TG^{-1}
   \end{bmatrix}.$$
Neither invertibility of $A$ nor orthonormality of $Z$ is required. This is (3.8) of
[benzi2005numerical]. -/
theorem inv_fromBlocks_transpose_zero_of_nullBasis [DecidableEq n] [DecidableEq m] [DecidableEq k]
    (hZ : IsNullBasis B Z) (hB : Function.Injective Bᵀ.mulVec) (hK : IsUnit (Zᵀ * A * Z)) :
    let G := B * Bᵀ
    let W := Z * (Zᵀ * A * Z)⁻¹ * Zᵀ
    (fromBlocks A Bᵀ B (0 : Matrix m m ℝ))⁻¹ =
      fromBlocks W ((1 - W * A) * (Bᵀ * G⁻¹))
        (G⁻¹ * B * (1 - A * W)) (-(G⁻¹ * B * (A - A * W * A) * (Bᵀ * G⁻¹))) := by
  intro G W
  let P := Bᵀ * G⁻¹
  let Q := G⁻¹ * B
  let T := 1 - A * W
  have hG : IsUnit G := by
    apply PosDef.isUnit
    simpa only [G, conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
      PosDef.conjTranspose_mul_self Bᵀ hB
  have hGdet := (isUnit_iff_isUnit_det G).1 hG
  have hBP : B * P = 1 := by
    rw [show P = Bᵀ * G⁻¹ from rfl, ← Matrix.mul_assoc]
    exact mul_nonsing_inv G hGdet
  have hQB : Q * Bᵀ = 1 := by
    rw [show Q = G⁻¹ * B from rfl, Matrix.mul_assoc]
    exact nonsing_inv_mul G hGdet
  have hBW : B * W = 0 := by
    dsimp only [W]
    simp only [← Matrix.mul_assoc, hZ.mul_eq_zero, Matrix.zero_mul]
  have hZW : Zᵀ * A * W = Zᵀ := by
    dsimp only [W]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hK), Matrix.one_mul]
  have hZT : Zᵀ * T = 0 := by
    dsimp only [T]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hZW, sub_self]
  have hQT : Bᵀ * Q * T = T := by
    apply Matrix.mulVec_injective
    funext f
    have hf : Zᵀ *ᵥ (T *ᵥ f) = 0 := by rw [mulVec_mulVec, hZT, zero_mulVec]
    obtain ⟨y, hy⟩ := exists_transpose_mulVec_eq_of_nullBasis hZ hf
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hy, mulVec_mulVec y Q Bᵀ, hQB, one_mulVec]
  have hTA : T * A = A - A * W * A := by
    dsimp only [T]
    rw [Matrix.sub_mul, Matrix.one_mul]
  have hAT : A * (1 - W * A) = T * A := by
    rw [hTA, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc A W A]
  have h11 : A * W + Bᵀ * (Q * T) = 1 := by
    rw [← Matrix.mul_assoc Bᵀ Q T, hQT]
    exact add_sub_cancel _ _
  have h12 : A * ((1 - W * A) * P) + Bᵀ * (-(Q * (A - A * W * A) * P)) = 0 := by
    calc
      _ = T * A * P - (Bᵀ * Q * T) * A * P := by
        rw [← hTA, ← Matrix.mul_assoc A, hAT, Matrix.mul_neg, sub_eq_add_neg]
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQT, sub_self]
  have h22 : B * ((1 - W * A) * P) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc B W,
      hBW, Matrix.zero_mul, sub_zero, hBP]
  apply inv_eq_right_inv
  change fromBlocks A Bᵀ B 0 *
    fromBlocks W ((1 - W * A) * P) (Q * T) (-(Q * (A - A * W * A) * P)) = 1
  rw [fromBlocks_multiply, ← fromBlocks_one]
  simp only [Matrix.zero_mul, add_zero, h11, h12, hBW, h22]

end Real

end Matrix
