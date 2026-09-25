/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Kronecker`, `Mathlib.Analysis.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.Kronecker
import Numlib.LinearAlgebra.Matrix.LU
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Schur

/-!
# Norms, spectra and triangular factors of Kronecker products

The facts of [golub2013matrix] §12.3.1 about a Kronecker product `B ⊗ C` that need the
factorization layer: its Frobenius and spectral norms are the products of those of the factors, its
singular values and eigenvalues are the pairwise products, and the Kronecker products of triangular
(LU, Cholesky) factors of `B` and `C` are the corresponding factors of `B ⊗ C` in the positional
layout `Matrix.kroneckerFin`.

The singular values are the column-indexed `Matrix.singularValues`, so `singularValues_kronecker`
is an identity up to a permutation of the column index `n₁ × n₂`.

## Main statements

* `Matrix.frobenius_norm_kronecker`, `Matrix.l2_opNorm_kronecker`.
* `Matrix.singularValues_kronecker`: `σ(B ⊗ C) = {σ_i(B) σ_j(C)}`.
* `Matrix.charpoly_kronecker`: `λ(B ⊗ C) = {β_i γ_j}` over `ℂ`.
* `Matrix.IsUpperTriangular.kroneckerFin`, `Matrix.IsLU.kroneckerFin`,
  `Matrix.IsCholesky.kroneckerFin`.

## References

* [golub2013matrix], §12.3.1.
-/

open scoped Kronecker Matrix
open Polynomial

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m₁ n₁ m₂ n₂ : Type*} [Fintype m₁] [Fintype n₁] [Fintype m₂]
  [Fintype n₂]

/-! ### Norms -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- `‖B ⊗ C‖_F = ‖B‖_F ‖C‖_F` ([golub2013matrix] §12.3.1). -/
theorem frobenius_norm_kronecker (B : Matrix m₁ n₁ 𝕜) (C : Matrix m₂ n₂ 𝕜) :
    ‖B ⊗ₖ C‖ = ‖B‖ * ‖C‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq,
    frobenius_norm_sq_eq_sum_sq, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => by
    rw [kroneckerMap_apply, norm_mul, mul_pow]

end Frobenius

/-! ### Singular values -/

/-- The characteristic polynomial of a conjugate `star U * M * U` by a unitary `U` is that of
`M`. -/
private theorem charpoly_star_mul_mul {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) (M : Matrix n n 𝕜) : (star U * M * U).charpoly = M.charpoly := by
  rw [charpoly_mul_comm, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.one_mul]

/-- The Kronecker product of the right singular unitaries diagonalizes `(B ⊗ C)ᴴ (B ⊗ C)`. -/
private theorem conjTranspose_kronecker_mul_self_eq [DecidableEq n₁] [DecidableEq n₂]
    (B : Matrix m₁ n₁ 𝕜) (C : Matrix m₂ n₂ 𝕜) :
    (B ⊗ₖ C)ᴴ * (B ⊗ₖ C)
      = (B.rightSingularUnitary ⊗ₖ C.rightSingularUnitary)
        * diagonal (fun q : n₁ × n₂ => ((B.singularValues q.1 ^ 2 * C.singularValues q.2 ^ 2 : ℝ)
          : 𝕜))
        * star (B.rightSingularUnitary ⊗ₖ C.rightSingularUnitary) := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, conjTranspose_mul_self_eq_conj_diagonal,
    conjTranspose_mul_self_eq_conj_diagonal, mul_kronecker_mul, mul_kronecker_mul,
    diagonal_kronecker_diagonal, star_eq_conjTranspose (_ ⊗ₖ _), conjTranspose_kronecker,
    star_eq_conjTranspose, star_eq_conjTranspose]
  simp only [RCLike.ofReal_mul]

/-- **The singular values of `B ⊗ C` are the products `σ_i(B) σ_j(C)`** ([golub2013matrix]
§12.3.1, via (12.3.4)), up to a relabelling of the columns `n₁ × n₂`. -/
theorem singularValues_kronecker [DecidableEq n₁] [DecidableEq n₂] (B : Matrix m₁ n₁ 𝕜)
    (C : Matrix m₂ n₂ 𝕜) :
    ∃ e : n₁ × n₂ ≃ n₁ × n₂,
      ∀ q, (B ⊗ₖ C).singularValues (e q) = B.singularValues q.1 * C.singularValues q.2 := by
  set hG := isHermitian_conjTranspose_mul_self (B ⊗ₖ C)
  set d : n₁ × n₂ → ℝ := fun q => B.singularValues q.1 ^ 2 * C.singularValues q.2 ^ 2
  have hU : star (B.rightSingularUnitary ⊗ₖ C.rightSingularUnitary)
      ∈ unitaryGroup (n₁ × n₂) 𝕜 :=
    Unitary.star_mem (kronecker_mem_unitary B.rightSingularUnitary_mem_unitaryGroup
      C.rightSingularUnitary_mem_unitaryGroup)
  have hchar : ((B ⊗ₖ C)ᴴ * (B ⊗ₖ C)).charpoly = (diagonal fun q => ((d q : ℝ) : 𝕜)).charpoly := by
    rw [conjTranspose_kronecker_mul_self_eq]
    have := charpoly_star_mul_mul hU (diagonal fun q => ((d q : ℝ) : 𝕜))
    rwa [star_star] at this
  have hmult : Multiset.map hG.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
    have h1 := hG.roots_charpoly_eq_eigenvalues
    have h2 : (diagonal fun q => ((d q : ℝ) : 𝕜)).charpoly.roots
        = Multiset.map (RCLike.ofReal ∘ d) Finset.univ.val := by
      rw [charpoly_diagonal, roots_prod]
      · simp
      · simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero]
    rw [hchar, h2] at h1
    have h3 := congrArg (Multiset.map RCLike.re) h1
    simpa [Multiset.map_map, Function.comp_def] using h3.symm
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_val_eq hmult
  refine ⟨e, fun q => ?_⟩
  rw [singularValues, he q, show d q = (B.singularValues q.1 * C.singularValues q.2) ^ 2 by
    simp only [d]; ring, Real.sqrt_sq (mul_nonneg (B.singularValues_nonneg _)
    (C.singularValues_nonneg _))]

section L2

open scoped Matrix.Norms.L2Operator

/-- The spectral norm of a matrix with a nonempty column type is one of its singular values. -/
private theorem exists_l2_opNorm_eq_singularValues {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq q] [Nonempty q] (A : Matrix p q 𝕜) : ∃ i, ‖A‖ = A.singularValues i := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := A.singularValues)
  refine ⟨i, le_antisymm ?_ (singularValues_le_l2_opNorm A i)⟩
  rw [hi]
  exact l2_opNorm_le_of_forall_norm_toEuclideanLin_le A (hi ▸ A.singularValues_nonneg i)
    (A.norm_toEuclideanLin_le_iSup_singularValues)

/-- `‖B ⊗ C‖₂ = ‖B‖₂ ‖C‖₂` ([golub2013matrix] §12.3.1): the largest singular value of `B ⊗ C` is
the product of the largest singular values of the factors. -/
theorem l2_opNorm_kronecker [DecidableEq n₁] [DecidableEq n₂] (B : Matrix m₁ n₁ 𝕜)
    (C : Matrix m₂ n₂ 𝕜) : ‖B ⊗ₖ C‖ = ‖B‖ * ‖C‖ := by
  rcases isEmpty_or_nonempty n₁ with h₁ | h₁
  · have h0 : B ⊗ₖ C = 0 := by
      ext i j
      exact isEmptyElim j.1
    have hB : B = 0 := by
      ext i j
      exact isEmptyElim j
    rw [h0, hB, norm_zero, norm_zero, zero_mul]
  rcases isEmpty_or_nonempty n₂ with h₂ | h₂
  · have h0 : B ⊗ₖ C = 0 := by
      ext i j
      exact isEmptyElim j.2
    have hC : C = 0 := by
      ext i j
      exact isEmptyElim j
    rw [h0, hC, norm_zero, norm_zero, mul_zero]
  obtain ⟨e, he⟩ := singularValues_kronecker B C
  obtain ⟨q, hq⟩ := exists_l2_opNorm_eq_singularValues (B ⊗ₖ C)
  obtain ⟨i, hi⟩ := exists_l2_opNorm_eq_singularValues B
  obtain ⟨j, hj⟩ := exists_l2_opNorm_eq_singularValues C
  refine le_antisymm ?_ ?_
  · rw [hq, ← e.apply_symm_apply q, he]
    exact mul_le_mul (singularValues_le_l2_opNorm _ _) (singularValues_le_l2_opNorm _ _)
      (C.singularValues_nonneg _) (norm_nonneg _)
  · rw [hi, hj, ← he (i, j)]
    exact singularValues_le_l2_opNorm _ _

end L2

/-! ### Eigenvalues -/

/-- Two families with the same multiset of values have the same product under any function. -/
private theorem prod_comp_eq_of_map_eq {ι α M : Type*} [Fintype ι] [CommMonoid M] {a b : ι → α}
    (h : Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val) (g : α → M) :
    ∏ i, g (a i) = ∏ i, g (b i) := by
  have e : ∀ c : ι → α, Multiset.map (fun i => g (c i)) Finset.univ.val
      = (Multiset.map c Finset.univ.val).map g := fun c => (Multiset.map_map g c _).symm
  rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod, e a, e b, h]

/-- The roots of a split polynomial `∏ (X - a_i)` are the `a_i`. -/
private theorem map_univ_eq_of_prod_eq {ι : Type*} [Fintype ι] {a b : ι → 𝕜}
    (h : ∏ i, (X - C (a i)) = ∏ i, (X - C (b i))) :
    Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val := by
  have key : ∀ c : ι → 𝕜, (∏ i, (X - C (c i))).roots = Multiset.map c Finset.univ.val := by
    intro c
    rw [roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero]
  rw [← key a, ← key b, h]


/-! ### Triangular factors in positional layout -/

section Triangular

variable {R : Type*} {m₁ m₂ : ℕ}

/-- The positional indices compare lexicographically. -/
private theorem finProdFinEquiv_lt_iff {i₁ j₁ : Fin m₁} {i₂ j₂ : Fin m₂}
    (h : finProdFinEquiv (j₁, j₂) < finProdFinEquiv (i₁, i₂)) : j₁ < i₁ ∨ j₁ = i₁ ∧ j₂ < i₂ := by
  rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val] at h
  dsimp only at h
  rcases lt_trichotomy j₁ i₁ with h₁ | rfl | h₁
  · exact Or.inl h₁
  · exact Or.inr ⟨rfl, Fin.lt_def.2 (by omega)⟩
  · exfalso
    have hle : m₂ * (i₁ : ℕ) + m₂ ≤ m₂ * j₁ := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ (Fin.lt_def.1 h₁)
    have := i₂.2
    omega

/-- The Kronecker product of upper triangular matrices is upper triangular in positional layout
([golub2013matrix] §12.3.1). -/
theorem IsUpperTriangular.kroneckerFin [MulZeroClass R] {B : Matrix (Fin m₁) (Fin m₁) R}
    {C : Matrix (Fin m₂) (Fin m₂) R} (hB : B.IsUpperTriangular) (hC : C.IsUpperTriangular) :
    (kroneckerFin B C).IsUpperTriangular := by
  intro i j h
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [kroneckerFin_apply]
  rcases finProdFinEquiv_lt_iff h with h₁ | ⟨h₁, h₂⟩
  · rw [hB h₁, zero_mul]
  · rw [hC h₂, mul_zero]

/-- The Kronecker product of lower triangular matrices is lower triangular in positional layout. -/
theorem IsLowerTriangular.kroneckerFin [MulZeroClass R] {B : Matrix (Fin m₁) (Fin m₁) R}
    {C : Matrix (Fin m₂) (Fin m₂) R} (hB : B.IsLowerTriangular) (hC : C.IsLowerTriangular) :
    (kroneckerFin B C).IsLowerTriangular := by
  intro i j h
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [kroneckerFin_apply]
  rcases finProdFinEquiv_lt_iff (show finProdFinEquiv (i₁, i₂) < finProdFinEquiv (j₁, j₂) from h)
    with h₁ | ⟨h₁, h₂⟩
  · rw [hB (show OrderDual.toDual j₁ < OrderDual.toDual i₁ from h₁), zero_mul]
  · rw [hC (show OrderDual.toDual j₂ < OrderDual.toDual i₂ from h₂), mul_zero]

/-- The Kronecker product of unit lower triangular matrices is unit lower triangular in positional
layout. -/
theorem IsUnitLowerTriangular.kroneckerFin [MulZeroOneClass R] {B : Matrix (Fin m₁) (Fin m₁) R}
    {C : Matrix (Fin m₂) (Fin m₂) R} (hB : B.IsUnitLowerTriangular)
    (hC : C.IsUnitLowerTriangular) : (kroneckerFin B C).IsUnitLowerTriangular where
  isLowerTriangular := hB.isLowerTriangular.kroneckerFin hC.isLowerTriangular
  diag_eq_one i := by
    obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
    rw [kroneckerFin_apply, hB.diag_eq_one, hC.diag_eq_one, one_mul]

/-- The Kronecker product of LU factorizations is the LU factorization of the Kronecker product
([golub2013matrix] §12.3.1): `B ⊗ C = (L_B ⊗ L_C)(U_B ⊗ U_C)`. -/
theorem IsLU.kroneckerFin [CommSemiring R] {B L_B U_B : Matrix (Fin m₁) (Fin m₁) R}
    {C L_C U_C : Matrix (Fin m₂) (Fin m₂) R} (hB : IsLU B L_B U_B) (hC : IsLU C L_C U_C) :
    IsLU (kroneckerFin B C) (kroneckerFin L_B L_C) (kroneckerFin U_B U_C) where
  isUnitLowerTriangular := hB.isUnitLowerTriangular.kroneckerFin hC.isUnitLowerTriangular
  isUpperTriangular := hB.isUpperTriangular.kroneckerFin hC.isUpperTriangular
  mul_eq := by rw [kroneckerFin_mul_kroneckerFin, hB.mul_eq, hC.mul_eq]

/-- `(B ⊗ C)ᴴ = Bᴴ ⊗ Cᴴ` in positional layout. -/
theorem conjTranspose_kroneckerFin [CommMagma R] [StarMul R] {n₁ n₂ : ℕ}
    (B : Matrix (Fin m₁) (Fin n₁) R) (C : Matrix (Fin m₂) (Fin n₂) R) :
    (kroneckerFin B C)ᴴ = kroneckerFin Bᴴ Cᴴ := by
  rw [kroneckerFin, kroneckerFin, conjTranspose_submatrix, conjTranspose_kronecker]

open scoped ComplexOrder in
/-- The Kronecker product of Cholesky factors is the Cholesky factor of the Kronecker product
([golub2013matrix] §12.3.1): `B ⊗ C = (G_B ⊗ G_C)ᴴ (G_B ⊗ G_C)`. -/
theorem IsCholesky.kroneckerFin {B H_B : Matrix (Fin m₁) (Fin m₁) 𝕜}
    {C H_C : Matrix (Fin m₂) (Fin m₂) 𝕜} (hB : IsCholesky B H_B) (hC : IsCholesky C H_C) :
    IsCholesky (kroneckerFin B C) (kroneckerFin H_B H_C) where
  isUpperTriangular := hB.isUpperTriangular.kroneckerFin hC.isUpperTriangular
  diag_pos i := by
    obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
    rw [kroneckerFin_apply]
    exact mul_pos (hB.diag_pos i₁) (hC.diag_pos i₂)
  conjTranspose_mul_self := by
    rw [conjTranspose_kroneckerFin, kroneckerFin_mul_kroneckerFin, hB.conjTranspose_mul_self,
      hC.conjTranspose_mul_self]

end Triangular

section Charpoly

variable [IsAlgClosed 𝕜]

/-- `charpoly_kronecker` for `Fin`-indexed factors, where the Schur forms are triangular for the
native order and their Kronecker product is triangular in positional layout. -/
private theorem charpoly_kronecker_fin {a b : ℕ} (A : Matrix (Fin a) (Fin a) 𝕜)
    (B : Matrix (Fin b) (Fin b) 𝕜) {β : Fin a → 𝕜} {γ : Fin b → 𝕜}
    (hA : A.charpoly = ∏ i, (X - C (β i))) (hB : B.charpoly = ∏ j, (X - C (γ j))) :
    (A ⊗ₖ B).charpoly = ∏ i, ∏ j, (X - C (β i * γ j)) := by
  obtain ⟨P, hP, hPt, hPc⟩ := exists_unitary_conj_upperTriangular A
  obtain ⟨Q, hQ, hQt, hQc⟩ := exists_unitary_conj_upperTriangular B
  set T := star P * A * P
  set S := star Q * B * Q
  have hPQ : P ⊗ₖ Q ∈ unitaryGroup (Fin a × Fin b) 𝕜 := kronecker_mem_unitary hP hQ
  have hconj : star (P ⊗ₖ Q) * (A ⊗ₖ B) * (P ⊗ₖ Q) = T ⊗ₖ S := by
    rw [star_eq_conjTranspose, conjTranspose_kronecker, ← star_eq_conjTranspose,
      ← star_eq_conjTranspose, ← mul_kronecker_mul, ← mul_kronecker_mul]
  have hK := charpoly_of_isUpperTriangular (kroneckerFin T S) (hPt.kroneckerFin hQt)
  unfold kroneckerFin at hK
  have hTS : (A ⊗ₖ B).charpoly = ∏ p : Fin a × Fin b, (X - C (T p.1 p.1 * S p.2 p.2)) := by
    rw [← charpoly_star_mul_mul hPQ, hconj, ← charpoly_reindex finProdFinEquiv, reindex_apply,
      hK]
    exact Fintype.prod_equiv finProdFinEquiv.symm _ _ fun _ => rfl
  have hT := map_univ_eq_of_prod_eq (hPc.symm.trans hA)
  have hS := map_univ_eq_of_prod_eq (hQc.symm.trans hB)
  rw [hTS, Fintype.prod_prod_type]
  calc ∏ i, ∏ j, (X - C (T i i * S j j)) = ∏ i, ∏ j, (X - C (T i i * γ j)) :=
        Finset.prod_congr rfl fun i _ => prod_comp_eq_of_map_eq hS fun s => X - C (T i i * s)
    _ = ∏ j, ∏ i, (X - C (T i i * γ j)) := Finset.prod_comm
    _ = ∏ j, ∏ i, (X - C (β i * γ j)) :=
        Finset.prod_congr rfl fun j _ => prod_comp_eq_of_map_eq hT fun t => X - C (t * γ j)
    _ = ∏ i, ∏ j, (X - C (β i * γ j)) := Finset.prod_comm

/-- **The eigenvalues of `B ⊗ C` are the products `β_i γ_j`** ([golub2013matrix] §12.3.1, via
(12.3.3)), over an algebraically closed field (`ℂ`): if `A.charpoly = ∏ (X - β_i)` and
`B.charpoly = ∏ (X - γ_j)` then `(A ⊗ B).charpoly = ∏ (X - β_i γ_j)`. Both factors are unitarily
triangularized (Schur), and the Kronecker product of upper triangular matrices is upper triangular
in positional layout. -/
theorem charpoly_kronecker {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) {β : m → 𝕜} {γ : n → 𝕜}
    (hA : A.charpoly = ∏ i, (X - C (β i))) (hB : B.charpoly = ∏ j, (X - C (γ j))) :
    (A ⊗ₖ B).charpoly = ∏ i, ∏ j, (X - C (β i * γ j)) := by
  set e₁ := Fintype.equivFin m
  set e₂ := Fintype.equivFin n
  have hA' : (reindex e₁ e₁ A).charpoly = ∏ i, (X - C (β (e₁.symm i))) := by
    rw [charpoly_reindex, hA]
    exact Fintype.prod_equiv e₁ _ _ fun i => by simp
  have hB' : (reindex e₂ e₂ B).charpoly = ∏ j, (X - C (γ (e₂.symm j))) := by
    rw [charpoly_reindex, hB]
    exact Fintype.prod_equiv e₂ _ _ fun j => by simp
  have hK : reindex e₁ e₁ A ⊗ₖ reindex e₂ e₂ B
      = reindex (e₁.prodCongr e₂) (e₁.prodCongr e₂) (A ⊗ₖ B) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  rw [← charpoly_reindex (e₁.prodCongr e₂) (A ⊗ₖ B), ← hK, charpoly_kronecker_fin _ _ hA' hB']
  exact (Fintype.prod_equiv e₁ _ _ fun i => Fintype.prod_equiv e₂ _ _ fun j => by simp).symm

end Charpoly

end Matrix
