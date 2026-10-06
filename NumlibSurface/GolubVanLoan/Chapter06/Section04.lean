import Numlib.Analysis.InnerProductSpace.PrincipalAngles
import Numlib.LinearAlgebra.Matrix.Polar
import Numlib.LinearAlgebra.Matrix.Procrustes
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter02.Section05
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section04
import NumlibSurface.GolubVanLoan.Chapter06.Section03

/-!
# Golub–Van Loan §6.4: subspace computations with the SVD

Surface file for [golub2013matrix] §6.4: the orthogonal Procrustes problem (6.4.1)–(6.4.2) and
Algorithm 6.4.1, with the polar decomposition read off an SVD (§6.4.1); the intersection of null
spaces (Theorem 6.4.1, Algorithm 6.4.2, §6.4.2); principal angles and vectors (6.4.3)–(6.4.6) and
the distance of equal-dimensional subspaces (§6.4.3); the intersection of ranges
(Theorem 6.4.2, §6.4.4).

## Conventions

Real matrices, 0-based. Subspaces of `ℝᵐ` are `Submodule ℝ (EuclideanSpace ℝ (Fin m))`; the range
of `A` is `LinearMap.range (toEuclideanLin A)`, its null space `LinearMap.ker (toEuclideanLin A)`.
"The columns of `Z` are orthonormal" is `Zᵀ * Z = 1`. The Frobenius norm is the scoped
`Matrix.Norms.Frobenius` norm, the 2-norm the scoped `Matrix.Norms.L2Operator` one, each opened in
the declarations that use it. An SVD is the factorization `Matrix.IsSVD A U σ V`
(`Uᵀ A V = rectDiagonal σ`), the book's principal angles and vectors are the backbone's
`Submodule.cosPrincipalAngle`, `Submodule.principalAngle` (0-based: `θ_{i+1}` is
`principalAngle F G i`) and `Submodule.IsPrincipalVectors`.

Algorithms 6.4.1–6.4.3 follow the algorithm conventions of `NumlibSurface/GolubVanLoan`: the
matrix products are chapter 1's `algorithm_1_1_5` (every product and sum through the rounding hook
`rnd`), and "Compute the SVD" is a monadic parameter `svd` (the book's SVD algorithm is chapter
8's), whose specification the exact-arithmetic theorems assume. The ranks "`r = rank(A)`",
"`q = rank(C)`" of Algorithm 6.4.2 are the numbers of nonzero computed singular values, a comparison
on the values the program holds, and its column ranges are `trailingColumns` (§6.3).
The thin QR factorizations of Algorithm 6.4.3 are chapter 5's Householder QR
(`Chapter05.algorithm_5_2_1`) with the orthogonal factor accumulated forward from the returned
reflector data (`Chapter05.forwardAccumulation`, `Chapter05.storedReflectors`), of which the first
columns (`Matrix.firstColumns`) are kept. The null spaces of Theorem 6.4.1 and Algorithm 6.4.2 are
those of `mulVecLin` (no Euclidean structure is needed).

## Sources and errata

Backbone `Numlib/LinearAlgebra/Matrix/{Procrustes,Polar}`,
`Numlib/Analysis/InnerProductSpace/PrincipalAngles`; Mathlib's `Submodule.map_comap_eq`; chapter
2's `subspaceDist`. Algorithm 6.4.3's heading "computes the cosines of the principal angles
`θ₁ ≥ ⋯ ≥ θ_q`" has the order reversed: the cosines decrease, the angles increase. The one-line
proof of Theorem 6.4.2 ("if `cos(θ_i) = 1`, then `f_i = g_i`") gives only the inclusion `⊇`; the
backbone proves both. §6.4.3 says the subspaces lie in `ℝᵐ` while `A ∈ ℝ^{n×p}`, and writes
"`v = Q_B z₁ = g₁`" for `g = …`.
-/

open Matrix

namespace GolubVanLoan.Chapter06

variable {m p : ℕ}

/-! ### §6.4.1 Rotation of subspaces -/

section Procrustes

open scoped Matrix.Norms.Frobenius

/-- **§6.4.1, the Procrustes expansion.** "If `Q ∈ ℝ^{p×p}` is orthogonal, then
`‖A − BQ‖_F² = ‖A‖_F² + ‖B‖_F² − 2 tr(Qᵀ(BᵀA))`. Thus, (6.4.1) is equivalent to the problem
`max_{QᵀQ = I_p} tr(QᵀBᵀA)`": an orthogonal `Q` minimizes `‖A − BQ‖_F` iff it maximizes
`tr(QᵀBᵀA)`. -/
theorem procrustes_iff_trace {A B : Matrix (Fin m) (Fin p) ℝ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin p) ℝ) :
    ‖A - B * Q‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * trace (Qᵀ * (Bᵀ * A)) ∧
      ((∀ Q' ∈ orthogonalGroup (Fin p) ℝ, ‖A - B * Q‖ ≤ ‖A - B * Q'‖) ↔
        ∀ Q' ∈ orthogonalGroup (Fin p) ℝ, trace (Q'ᵀ * (Bᵀ * A)) ≤ trace (Qᵀ * (Bᵀ * A))) := by
  have key : ∀ Q' ∈ orthogonalGroup (Fin p) ℝ,
      ‖A - B * Q'‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * trace (Q'ᵀ * (Bᵀ * A)) := fun Q' hQ' => by
    have := frobenius_norm_sub_mul_sq hQ' A B
    simpa [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this
  refine ⟨key Q hQ, forall₂_congr fun Q' hQ' => ?_⟩
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, key Q hQ, key Q' hQ']
  constructor <;> intro h <;> linarith

/-- **(6.4.2).** "If `C₁` and `C₂` have the same row and column dimension, then
`tr(C₁ᵀC₂) = tr(C₂ᵀC₁)`." -/
theorem equation_6_4_2 {n : ℕ} (C₁ C₂ : Matrix (Fin m) (Fin n) ℝ) :
    trace (C₁ᵀ * C₂) = trace (C₂ᵀ * C₁) := by
  rw [← trace_transpose, transpose_mul, transpose_transpose]

/-- The trace of `V Uᵀ C` for an SVD `Uᵀ C V = Σ` is the sum of the diagonal of `Σ`. -/
private theorem trace_mul_transpose_mul_eq_sum {C U V : Matrix (Fin p) (Fin p) ℝ} {σ : ℕ → ℝ}
    (h : IsSVD C U σ V) : trace ((U * Vᵀ)ᵀ * C) = ∑ i : Fin p, σ i := by
  have hS := h.star_mul_mul
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hS
  rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, trace_mul_comm, hS]
  simp [trace, rectDiagonal_apply]

/-- **§6.4.1, the solution of the Procrustes problem.** "If `Uᵀ(BᵀA)V = Σ = diag(σ₁, …, σ_p)` is
the SVD of `BᵀA` and we define the orthogonal matrix `Z` by `Z = VᵀQᵀU`, then …
`tr(QᵀBᵀA) = tr(ZΣ) = ∑ z_ii σ_i ≤ ∑ σ_i`. The upper bound is clearly attained by setting
`Z = I_p`, i.e., `Q = UVᵀ`": the trace bound, its attainment, and the minimality of `UVᵀ`. -/
theorem procrustes_solution {A B : Matrix (Fin m) (Fin p) ℝ} {U V : Matrix (Fin p) (Fin p) ℝ}
    {σ : ℕ → ℝ} (h : IsSVD (Bᵀ * A) U σ V) :
    (∀ Q ∈ orthogonalGroup (Fin p) ℝ, trace (Qᵀ * (Bᵀ * A)) ≤ ∑ i : Fin p, σ i) ∧
      trace ((U * Vᵀ)ᵀ * (Bᵀ * A)) = ∑ i : Fin p, σ i ∧
      U * Vᵀ ∈ orthogonalGroup (Fin p) ℝ ∧
      ∀ Q ∈ orthogonalGroup (Fin p) ℝ, ‖A - B * (U * Vᵀ)‖ ≤ ‖A - B * Q‖ := by
  have hsum : ∑ i : Fin p, σ i = ∑ i, (Bᵀ * A).colSingularValues i := by
    rw [← trace_mul_transpose_mul_eq_sum h]
    have := h.re_trace_mul_eq_sum
    simpa [conjTranspose_eq_transpose_of_trivial, transpose_mul] using this
  have hB : Bᴴ * A = Bᵀ * A := by rw [conjTranspose_eq_transpose_of_trivial]
  obtain ⟨hmem, hmin⟩ := frobenius_norm_sub_mul_le_of_isSVD (hB ▸ h)
  rw [conjTranspose_eq_transpose_of_trivial] at hmem hmin
  refine ⟨fun Q hQ => ?_, trace_mul_transpose_mul_eq_sum h, hmem, hmin⟩
  have hQt : Qᵀ ∈ unitaryGroup (Fin p) ℝ := by
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
    exact Unitary.star_mem hQ
  have := re_trace_mul_le_sum_colSingularValues (Bᵀ * A) hQt
  rw [hsum]
  simpa using this

/-- **§6.4.1, the Procrustes solution as a polar factor.** The minimizer `UVᵀ` is the orthogonal
factor of the polar decomposition `BᵀA = QP` ("if `B = I_p`, then the problem (6.4.1) is related to
the polar decomposition"): any orthogonal polar factor of `BᵀA` minimizes `‖A − BQ‖_F`. -/
theorem procrustes_solution_of_isPolarDecomposition {A B : Matrix (Fin m) (Fin p) ℝ}
    {Q₀ P : Matrix (Fin p) (Fin p) ℝ} (h : IsPolarDecomposition (Bᵀ * A) Q₀ P) :
    Q₀ ∈ orthogonalGroup (Fin p) ℝ ∧
      ∀ Q ∈ orthogonalGroup (Fin p) ℝ, ‖A - B * Q₀‖ ≤ ‖A - B * Q‖ := by
  have hB : Bᴴ * A = Bᵀ * A := by rw [conjTranspose_eq_transpose_of_trivial]
  exact frobenius_norm_sub_mul_le_of_isPolarDecomposition (hB ▸ h)

end Procrustes

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.4.1 (orthogonal Procrustes).** "Given `A` and `B` in `ℝ^{m×p}`, the following
algorithm finds an orthogonal `Q ∈ ℝ^{p×p}` such that `‖A − BQ‖_F` is minimum.
```
C = BᵀA
Compute the SVD UᵀCV = Σ and save U and V.
Q = UVᵀ
```"
The products are chapter 1's `algorithm_1_1_5` (from `0`); "Compute the SVD" is the parameter
`svd`, returning `(U, σ, V)`. -/
def algorithm_6_4_1
    (svd : Matrix (Fin p) (Fin p) ℝ →
      M (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin p) (Fin p) ℝ))
    (A B : Matrix (Fin m) (Fin p) ℝ) : M (Matrix (Fin p) (Fin p) ℝ) := do
  let C ← Chapter01.algorithm_1_1_5 rnd Bᵀ A 0
  let USV ← svd C
  Chapter01.algorithm_1_1_5 rnd USV.1 USV.2.2ᵀ 0

end Programs

section ProcrustesAlgorithm

open scoped Matrix.Norms.Frobenius

/-- **Algorithm 6.4.1 is correct in exact arithmetic**: if the `svd` subroutine returns an SVD,
the output `Q` is orthogonal and minimizes `‖A − BQ‖_F` over all orthogonal matrices. -/
theorem algorithm_6_4_1_spec
    (svd : Matrix (Fin p) (Fin p) ℝ →
      Id (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin p) (Fin p) ℝ))
    (hsvd : ∀ C, IsSVD C (Id.run (svd C)).1 (Id.run (svd C)).2.1 (Id.run (svd C)).2.2)
    (A B : Matrix (Fin m) (Fin p) ℝ) :
    Id.run (algorithm_6_4_1 pure svd A B) ∈ orthogonalGroup (Fin p) ℝ ∧
      ∀ Q ∈ orthogonalGroup (Fin p) ℝ,
        ‖A - B * Id.run (algorithm_6_4_1 pure svd A B)‖ ≤ ‖A - B * Q‖ := by
  have e : Id.run (algorithm_6_4_1 pure svd A B) =
      (Id.run (svd (Bᵀ * A))).1 * (Id.run (svd (Bᵀ * A))).2.2ᵀ := by
    simp only [algorithm_6_4_1]
    change Id.run (Chapter01.algorithm_1_1_5 pure
      (Id.run (svd (Id.run (Chapter01.algorithm_1_1_5 pure Bᵀ A 0)))).1
      (Id.run (svd (Id.run (Chapter01.algorithm_1_1_5 pure Bᵀ A 0)))).2.2ᵀ 0) = _
    rw [Chapter01.algorithm_1_1_5_spec, Chapter01.algorithm_1_1_5_spec, zero_add, zero_add]
  rw [e]
  obtain ⟨-, -, h1, h2⟩ := procrustes_solution (hsvd (Bᵀ * A))
  exact ⟨h1, h2⟩

end ProcrustesAlgorithm

/-- **§6.4.1, the polar decomposition from the SVD.** "If `A = UΣVᵀ` is the SVD of `A`, then
`A = (UVᵀ)(VΣVᵀ)` is its polar decomposition": `UVᵀ` is orthogonal and `VΣVᵀ` symmetric positive
semidefinite. -/
theorem polar_of_svd {n : ℕ} {A U V : Matrix (Fin n) (Fin n) ℝ} {σ : ℕ → ℝ}
    (h : IsSVD A U σ V) :
    IsPolarDecomposition A (U * Vᵀ) (V * diagonal (fun i : Fin n => σ i) * Vᵀ) ∧
      U * Vᵀ ∈ orthogonalGroup (Fin n) ℝ := by
  have hp := h.isPolarDecomposition_of_square
  simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at hp
  exact ⟨hp, hp.mem_unitaryGroup⟩

/-! ### §6.4.2 Intersection of null spaces -/

/-- **Theorem 6.4.1.** "Suppose `A ∈ ℝ^{m×n}` and let `{z₁, …, z_t}` be an orthonormal basis for
`null(A)`. Define `Z = [z₁ | ⋯ | z_t]` and let `{w₁, …, w_q}` be an orthonormal basis for
`null(BZ)` where `B ∈ ℝ^{p×n}`. If `W = [w₁ | ⋯ | w_q]`, then the columns of `ZW` form an
orthonormal basis for `null(A) ∩ null(B)`." Null spaces and ranges are those of `mulVecLin`. -/
theorem theorem_6_4_1 {n t q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin p) (Fin n) ℝ}
    {Z : Matrix (Fin n) (Fin t) ℝ} {W : Matrix (Fin t) (Fin q) ℝ} (hZ : Zᵀ * Z = 1)
    (hZA : LinearMap.range Z.mulVecLin = LinearMap.ker A.mulVecLin) (hW : Wᵀ * W = 1)
    (hWB : LinearMap.range W.mulVecLin = LinearMap.ker (B * Z).mulVecLin) :
    (Z * W)ᵀ * (Z * W) = 1 ∧
      LinearMap.range (Z * W).mulVecLin =
        LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
  refine ⟨?_, ?_⟩
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ, hZ, Matrix.one_mul, hW]
  · rw [mulVecLin_mul, LinearMap.range_comp, hWB, mulVecLin_mul, LinearMap.ker_comp,
      Submodule.map_comap_eq, hZA]

section NullSpaces

/-- For sorted nonnegative values, the nonzero ones among the first `k` are exactly the first
`Chapter05.deltaRank k 0 σ`: chapter 5's numerical rank (5.4.5) at `δ = 0` is the book's
"`r = rank(A)`" read off a computed diagonal of singular values (§5.4.1). -/
private theorem ne_zero_iff_lt_deltaRank {σ : ℕ → ℝ} (hσ : Antitone σ) (h0 : ∀ i, 0 ≤ σ i)
    {k i : ℕ} (hi : i < k) : σ i ≠ 0 ↔ i < Chapter05.deltaRank k 0 σ := by
  obtain ⟨-, h1, h2⟩ := Chapter05.deltaRank_spec (n := k) (δ := 0) hσ
  constructor
  · intro h
    by_contra hle
    exact h (le_antisymm (h2 i (not_lt.1 hle) hi) (h0 i))
  · intro h
    exact (h1 i h).ne'

/-- **The null space from an SVD**: if `U_Aᵀ A V_A = diag(σ_i)` and `r` is the number of nonzero
`σ_i`, the trailing columns `V_A(:, r+1:n)` span `null(A)`. -/
theorem range_trailingColumns_eq_ker {n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A U σ V) :
    LinearMap.range (trailingColumns V (Chapter05.deltaRank (min m n) 0 σ)).mulVecLin =
      LinearMap.ker A.mulVecLin := by
  have hr := (Chapter05.deltaRank_spec (n := min m n) (δ := 0) h.antitone).1
  have hset : ∀ j : Fin n,
      (m ≤ (j : ℕ) ∨ σ j = 0) ↔ Chapter05.deltaRank (min m n) 0 σ ≤ j := by
    intro j
    have hjn := j.isLt
    by_cases hj : (j : ℕ) < min m n
    · have hiff := ne_zero_iff_lt_deltaRank h.antitone h.nonneg hj
      constructor
      · rintro (hm | hz)
        · exact absurd hj (by have := min_le_left m n; omega)
        · by_contra hlt
          exact hiff.2 (by omega) hz
      · intro hle
        right
        by_contra hne
        have := hiff.1 hne
        omega
    · constructor
      · intro _
        omega
      · intro _
        left
        omega
  rw [range_mulVecLin, h.ker_mulVecLin_eq_span]
  congr 1
  ext w
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨⟨Chapter05.deltaRank (min m n) 0 σ + j, by have := j.isLt; omega⟩,
      (hset _).2 (by simp), ?_⟩
    rfl
  · rintro ⟨j, hj, rfl⟩
    have hle := (hset j).1 hj
    refine ⟨⟨j - Chapter05.deltaRank (min m n) 0 σ, by have := j.isLt; omega⟩, ?_⟩
    funext k
    change V k ⟨Chapter05.deltaRank (min m n) 0 σ + (↑j - Chapter05.deltaRank (min m n) 0 σ), _⟩ =
      V k j
    congr 1
    exact Fin.ext (by rw [Fin.val_mk]; omega)

/-- A matrix with no columns has trivial range. -/
private theorem range_mulVecLin_eq_bot {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) (hk : k = 0) :
    LinearMap.range Y.mulVecLin = ⊥ := by
  subst hk
  rw [range_mulVecLin, Set.range_eq_empty, Submodule.span_empty]

/-- A matrix with orthonormal columns spanning `K` has as many columns as `K` has dimensions. -/
private theorem eq_finrank_of_range_eq {n s : ℕ} {Y : Matrix (Fin n) (Fin s) ℝ}
    {K : Submodule ℝ (Fin n → ℝ)} (hY : Yᵀ * Y = 1) (hK : LinearMap.range Y.mulVecLin = K) :
    s = Module.finrank ℝ K := by
  have hinj : Function.Injective Y.mulVecLin := fun x y hxy => by
    have := congrArg (Yᵀ *ᵥ ·) hxy
    simpa only [mulVecLin_apply, mulVec_mulVec, hY, one_mulVec] using this
  rw [← hK, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.4.2 (intersection of null spaces).** "Given `A ∈ ℝ^{m×n}` and `B ∈ ℝ^{p×n}`,
the following algorithm computes an integer `s` and a matrix `Y = [y₁ | ⋯ | y_s]` having
orthonormal columns which span `null(A) ∩ null(B)`. If the intersection is trivial, then `s = 0`.
```
Compute the SVD U_Aᵀ A V_A = diag(σ_i), save V_A, and set r = rank(A).
if r < n
    C = B V_A(:, r+1:n)
    Compute the SVD U_Cᵀ C V_C = diag(γ_i), save V_C, and set q = rank(C).
    if q < n − r
        s = n − r − q
        Y = V_A(:, r+1:n) V_C(:, q+1:n−r)
    else
        s = 0
    end
else
    s = 0
end
```"
The two SVDs are the parameters `svdA`, `svdC` (the latter for each column count), the ranks the
numbers of nonzero computed singular values (`Chapter05.deltaRank` at `δ = 0`), the products chapter
1's `algorithm_1_1_5`. -/
noncomputable def algorithm_6_4_2 {n : ℕ}
    (svdA : Matrix (Fin m) (Fin n) ℝ →
      M (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (svdC : ∀ k, Matrix (Fin p) (Fin k) ℝ →
      M (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin k) (Fin k) ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin p) (Fin n) ℝ) :
    M (Σ s : ℕ, Matrix (Fin n) (Fin s) ℝ) := do
  let SA ← svdA A
  let r := Chapter05.deltaRank (min m n) 0 SA.2.1
  if r < n then
    let C ← Chapter01.algorithm_1_1_5 rnd B (trailingColumns SA.2.2 r) 0
    let SC ← svdC (n - r) C
    let q := Chapter05.deltaRank (min p (n - r)) 0 SC.2.1
    if q < n - r then
      let Y ← Chapter01.algorithm_1_1_5 rnd (trailingColumns SA.2.2 r)
        (trailingColumns SC.2.2 q) 0
      pure ⟨n - r - q, Y⟩
    else pure ⟨0, 0⟩
  else pure ⟨0, 0⟩

end Programs

/-- The output `⟨0, 0⟩` meets the specification when the intersection is trivial. -/
private theorem spec_of_eq_zero {n : ℕ} {K : Submodule ℝ (Fin n → ℝ)} (hK : K = ⊥) {s : ℕ}
    {Y : Matrix (Fin n) (Fin s) ℝ} (h : (⟨0, 0⟩ : Σ s : ℕ, Matrix (Fin n) (Fin s) ℝ) = ⟨s, Y⟩) :
    Yᵀ * Y = 1 ∧ LinearMap.range Y.mulVecLin = K ∧ s = Module.finrank ℝ K := by
  subst hK
  obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.1 h
  obtain rfl := eq_of_heq h'.symm
  exact ⟨Subsingleton.elim _ _, range_mulVecLin_eq_bot _ rfl, by simp⟩

/-- **Algorithm 6.4.2 is correct in exact arithmetic**: if both SVD subroutines return SVDs, the
output `⟨s, Y⟩` has orthonormal columns spanning `null(A) ∩ null(B)`, and
`s = dim(null(A) ∩ null(B))`, so `s = 0` exactly when the intersection is trivial. -/
theorem algorithm_6_4_2_spec {n : ℕ}
    (svdA : Matrix (Fin m) (Fin n) ℝ →
      Id (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (svdC : ∀ k, Matrix (Fin p) (Fin k) ℝ →
      Id (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin k) (Fin k) ℝ))
    (hA : ∀ A', IsSVD A' (Id.run (svdA A')).1 (Id.run (svdA A')).2.1 (Id.run (svdA A')).2.2)
    (hC : ∀ k (C : Matrix (Fin p) (Fin k) ℝ),
      IsSVD C (Id.run (svdC k C)).1 (Id.run (svdC k C)).2.1 (Id.run (svdC k C)).2.2)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin p) (Fin n) ℝ) {s : ℕ}
    {Y : Matrix (Fin n) (Fin s) ℝ} (hY : Id.run (algorithm_6_4_2 pure svdA svdC A B) = ⟨s, Y⟩) :
    Yᵀ * Y = 1 ∧
      LinearMap.range Y.mulVecLin = LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin ∧
      s = Module.finrank ℝ ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) := by
  have hsA := hA A
  simp only [algorithm_6_4_2, Id.run_bind] at hY
  generalize Id.run (svdA A) = SA at hY hsA
  generalize hr : Chapter05.deltaRank (min m n) 0 SA.2.1 = r at hY
  have hZ := trailingColumns_transpose_mul_self hsA.mem_unitaryGroup_right r
  have hZA := range_trailingColumns_eq_ker hsA
  rw [hr] at hZA
  split_ifs at hY with h1
  · simp only [Id.run_bind, Chapter01.algorithm_1_1_5_spec, zero_add] at hY
    have hsC := hC (n - r) (B * trailingColumns SA.2.2 r)
    generalize Id.run (svdC (n - r) (B * trailingColumns SA.2.2 r)) = SC at hY hsC
    generalize hq : Chapter05.deltaRank (min p (n - r)) 0 SC.2.1 = q at hY
    have hW := trailingColumns_transpose_mul_self hsC.mem_unitaryGroup_right q
    have hWB := range_trailingColumns_eq_ker hsC
    rw [hq] at hWB
    obtain ⟨hZW, hK⟩ := theorem_6_4_1 hZ hZA hW hWB
    split_ifs at hY with h2
    · simp only [Id.run_bind, Chapter01.algorithm_1_1_5_spec, zero_add] at hY
      obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.1 hY
      obtain rfl := eq_of_heq h'.symm
      exact ⟨hZW, hK, eq_finrank_of_range_eq hZW hK⟩
    · refine spec_of_eq_zero ?_ hY
      rw [← hK]
      exact range_mulVecLin_eq_bot _ (by omega)
  · refine spec_of_eq_zero ?_ hY
    rw [← hZA, range_mulVecLin_eq_bot _ (by omega), bot_inf_eq]

end NullSpaces

/-! ### §6.4.3 Angles between subspaces -/

section Angles

variable (F G : Submodule ℝ (EuclideanSpace ℝ (Fin m)))

/-- **(6.4.3).** "The principal angles `{θ_i}` between these two subspaces and the associated
principal vectors `{f_i, g_i}` are defined recursively by
`cos(θ_k) = f_kᵀg_k = max_{f ∈ F, ‖f‖₂ = 1} max_{g ∈ G, ‖g‖₂ = 1} fᵀg` subject to
`fᵀ[f₁, …, f_{k−1}] = 0`, `gᵀ[g₁, …, g_{k−1}] = 0`", for `dim F ≥ dim G`: (a) principal vectors
exist; (b) for principal vectors, `cos θ_k` is the maximum of the recursion at step `k`, attained at
`(f_k, g_k)`; (c) any sequence produced by the recursion has `f_kᵀg_k = cos θ_k`, so the recursion
defines the angles unambiguously. -/
theorem equation_6_4_3 (h : Module.finrank ℝ G ≤ Module.finrank ℝ F) :
    (∃ f g : Fin (Module.finrank ℝ G) → EuclideanSpace ℝ (Fin m), F.IsPrincipalVectors G f g) ∧
      (∀ {q : ℕ} {f g : Fin q → EuclideanSpace ℝ (Fin m)}, F.IsPrincipalVectors G f g →
        ∀ k : Fin q, IsGreatest {r : ℝ | ∃ u ∈ F, ∃ v ∈ G, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
          (∀ i < k, inner ℝ (f i) u = 0) ∧ (∀ i < k, inner ℝ (g i) v = 0) ∧ inner ℝ u v = r}
          (F.cosPrincipalAngle G k)) ∧
      ∀ {q : ℕ} {f g : Fin q → EuclideanSpace ℝ (Fin m)}, F.IsRecursivePrincipalVectors G f g →
        ∀ k : Fin q, inner ℝ (f k) (g k) = F.cosPrincipalAngle G k := by
  refine ⟨F.exists_isPrincipalVectors G h, fun hfg k => ?_, fun hfg k => ?_⟩
  · simpa using hfg.isGreatest_re_inner k
  · simpa using F.cosPrincipalAngle_eq_of_isRecursivePrincipalVectors G h hfg k

/-- **§6.4.3.** "Note that the principal angles satisfy `0 ≤ θ₁ ≤ ⋯ ≤ θ_q ≤ π/2`." -/
theorem principalAngle_mono :
    Monotone (F.principalAngle G) ∧ ∀ i, F.principalAngle G i ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨F.monotone_principalAngle G, F.principalAngle_mem_Icc G⟩

/-- **§6.4.3, the distance of equal-dimensional subspaces.** "If `p = q`, then
`dist(F, G) = √(1 − cos(θ_p)²) = sin(θ_p)`", `dist` the subspace distance of §2.5.3. -/
theorem dist_eq_sin_principalAngle {q : ℕ} (hF : Module.finrank ℝ F = q + 1)
    (hG : Module.finrank ℝ G = q + 1) :
    Chapter02.subspaceDist F G = Real.sqrt (1 - F.cosPrincipalAngle G q ^ 2) ∧
      Chapter02.subspaceDist F G = Real.sin (F.principalAngle G q) := by
  have h := F.gap_eq_sin_principalAngle G hF hG
  refine ⟨?_, h⟩
  rw [Chapter02.subspaceDist, h, Submodule.principalAngle, Real.sin_arccos]

end Angles

section Matrices

variable {q : ℕ}

open scoped Matrix.Norms.L2Operator in
/-- **§6.4.3, the singular values of `Q_AᵀQ_B`.** With `A = Q_AR_A`, `B = Q_BR_B` thin QR
factorizations (`Q_A`, `Q_B` with orthonormal columns): "Since `‖Q_AᵀQ_B‖₂ ≤ 1`, all the singular
values are between 0 and 1 and we may write `σ_i = cos(θ_i)`." -/
theorem singularValues_transpose_mul_eq_cosPrincipalAngle {QA : Matrix (Fin m) (Fin p) ℝ}
    {QB : Matrix (Fin m) (Fin q) ℝ}
    (hA : QAᵀ * QA = 1) (hB : QBᵀ * QB = 1) :
    ‖QAᵀ * QB‖ ≤ 1 ∧ ∀ i : ℕ,
      (LinearMap.range (toEuclideanLin QA)).cosPrincipalAngle
          (LinearMap.range (toEuclideanLin QB)) i =
        (toEuclideanLin (QAᵀ * QB)).singularValues i ∧
      0 ≤ (toEuclideanLin (QAᵀ * QB)).singularValues i ∧
      (toEuclideanLin (QAᵀ * QB)).singularValues i ≤ 1 := by
  have hA' : QAᴴ * QA = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hB' : QBᴴ * QB = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  refine ⟨?_, fun i => ?_⟩
  · calc ‖QAᵀ * QB‖ ≤ ‖QAᵀ‖ * ‖QB‖ := l2_opNorm_mul _ _
      _ ≤ 1 * 1 := by
          rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
          exact mul_le_mul (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hA')
            (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hB') (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have e := Submodule.cosPrincipalAngle_eq_singularValues hA' hB' i
    rw [conjTranspose_eq_transpose_of_trivial] at e
    refine ⟨e, ?_, ?_⟩
    · rw [← e]; exact Submodule.cosPrincipalAngle_nonneg _ _ i
    · rw [← e]; exact Submodule.cosPrincipalAngle_le_one _ _ i

/-- **(6.4.6).** "If `f ∈ F` and `g ∈ G` are unit vectors, then there exist unit vectors
`u ∈ ℝᵖ` and `v ∈ ℝ^q` so that `f = Q_A u` and `g = Q_B v`. Thus,
`fᵀg = uᵀ(Q_AᵀQ_B)v = (Yᵀu)ᵀΣ(Zᵀv) = ∑_{i=1}^q σ_i (y_iᵀu)(z_iᵀv)`", for the SVD
`Q_AᵀQ_B = YΣZᵀ` (`p ≥ q`); the identity holds for all `u`, `v`. -/
theorem equation_6_4_6 {QA : Matrix (Fin m) (Fin p) ℝ} {QB : Matrix (Fin m) (Fin q) ℝ}
    (hqp : q ≤ p) {Y : Matrix (Fin p) (Fin p) ℝ} {σ : ℕ → ℝ} {Z : Matrix (Fin q) (Fin q) ℝ}
    (h : IsSVD (QAᵀ * QB) Y σ Z) (u : Fin p → ℝ) (v : Fin q → ℝ) :
    (QA *ᵥ u) ⬝ᵥ (QB *ᵥ v) =
      ∑ i : Fin q, σ i * (Y.col (Fin.castLE hqp i) ⬝ᵥ u) * (Z.col i ⬝ᵥ v) := by
  have hC := h.eq_mul_mul_star
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, id_eq] at hC
  rw [← vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, hC, ← vecMul_vecMul, ← vecMul_vecMul,
    ← dotProduct_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hS : (u ᵥ* Y ᵥ* (rectDiagonal σ : Matrix (Fin p) (Fin q) ℝ)) j =
      (u ᵥ* Y) (Fin.castLE hqp j) * σ j := by
    rw [vecMul, dotProduct, Finset.sum_eq_single (Fin.castLE hqp j)]
    · simp [rectDiagonal_apply]
    · intro i _ hi
      rw [rectDiagonal_apply, ite_eq_right (fun hij => hi (Fin.ext (by simpa using hij))),
        mul_zero]
    · simp
  rw [hS]
  have e1 : (u ᵥ* Y) (Fin.castLE hqp j) = Y.col (Fin.castLE hqp j) ⬝ᵥ u := by
    simp only [vecMul, dotProduct, col_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have e2 : (Zᵀ *ᵥ v) j = Z.col j ⬝ᵥ v := by
    simp only [mulVec, dotProduct, col_apply, transpose_apply]
  rw [e1, e2]
  ring

end Matrices

section PrincipalAnglesAlgorithm

variable {q : ℕ}

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.4.3 (principal angles and vectors).** "Given `A ∈ ℝ^{m×p}` and `B ∈ ℝ^{m×q}`
(`p ≥ q`) each with linearly independent columns, the following algorithm computes the cosines of
the principal angles `θ₁ ≥ ⋯ ≥ θ_q` between `ran(A)` and `ran(B)`. The vectors `f₁, …, f_q` and
`g₁, …, g_q` are the associated principal vectors.
```
Compute the thin QR factorizations A = Q_A R_A and B = Q_B R_B.
C = Q_Aᵀ Q_B
Compute the SVD YᵀCZ = diag(cos(θ_k)).
Q_A Y(:, 1:q) = [f₁ | ⋯ | f_q]
Q_B Z(:, 1:q) = [g₁ | ⋯ | g_q]
```"
The thin QR factorizations are chapter 5's Householder QR (Algorithm 5.2.1) with the orthogonal
factor accumulated forward from the returned reflector data (`storedReflectors`, the returned
`β`), of which the first `p` (resp. `q`) columns are kept; the products are chapter 1's
`algorithm_1_1_5`; "Compute the SVD" is the parameter `svd`. The output is the diagonal returned
by `svd` and the matrices `[f₁ | ⋯ | f_q]`, `[g₁ | ⋯ | g_q]`. The shape conditions `q ≤ p ≤ m` of
the book (independent columns) are explicit arguments. -/
noncomputable def algorithm_6_4_3
    (svd : Matrix (Fin p) (Fin q) ℝ →
      M (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin q) (Fin q) ℝ))
    (hqp : q ≤ p) (hpm : p ≤ m) (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ) :
    M ((ℕ → ℝ) × Matrix (Fin m) (Fin q) ℝ × Matrix (Fin m) (Fin q) ℝ) := do
  let RA ← Chapter05.algorithm_5_2_1 rnd A
  let QA ← Chapter05.forwardAccumulation rnd (Chapter05.storedReflectors RA.1 RA.2)
  let RB ← Chapter05.algorithm_5_2_1 rnd B
  let QB ← Chapter05.forwardAccumulation rnd (Chapter05.storedReflectors RB.1 RB.2)
  let C ← Chapter01.algorithm_1_1_5 rnd (firstColumns QA hpm)ᵀ
    (firstColumns QB (hqp.trans hpm)) 0
  let S ← svd C
  let F ← Chapter01.algorithm_1_1_5 rnd (firstColumns QA hpm) (firstColumns S.1 hqp) 0
  let G ← Chapter01.algorithm_1_1_5 rnd (firstColumns QB (hqp.trans hpm)) S.2.2 0
  pure (S.2.1, F, G)

end Programs

/-- The columns of a matrix with `Mᵀ M = 1` are orthonormal vectors of Euclidean space. -/
private theorem orthonormal_toLp_col {k : ℕ} {N : Matrix (Fin m) (Fin k) ℝ} (hN : Nᵀ * N = 1) :
    Orthonormal ℝ fun j => (WithLp.toLp 2 (N.col j) : EuclideanSpace ℝ (Fin m)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrFun (congrFun hN i) j
  rw [mul_apply, one_apply] at h
  rw [← h, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [col_apply, mul_comm]

/-- Ranges spanned by the same columns agree as ranges of the Euclidean operators. -/
private theorem range_toEuclideanLin_le_of_range_mulVecLin_le {k l : ℕ}
    {N : Matrix (Fin m) (Fin k) ℝ} {N' : Matrix (Fin m) (Fin l) ℝ}
    (h : LinearMap.range N.mulVecLin ≤ LinearMap.range N'.mulVecLin) :
    LinearMap.range (toEuclideanLin N) ≤ LinearMap.range (toEuclideanLin N') := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := h ⟨WithLp.ofLp x, rfl⟩
  refine ⟨WithLp.toLp 2 y, ?_⟩
  rw [toEuclideanLin_toLp, toEuclideanLin_apply]
  exact congrArg _ hy

/-- The first columns of the orthogonal factor of a QR factorization of a matrix with independent
columns span its range. -/
private theorem range_toEuclideanLin_firstColumns {k : ℕ} {N : Matrix (Fin m) (Fin k) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {R : Matrix (Fin m) (Fin k) ℝ} (h : IsQR N Q R) (hkm : k ≤ m)
    (hN : LinearIndependent ℝ Nᵀ) :
    LinearMap.range (toEuclideanLin (firstColumns Q hkm)) = LinearMap.range (toEuclideanLin N) := by
  have hr : LinearMap.range (firstColumns Q hkm).mulVecLin = LinearMap.range N.mulVecLin := by
    rw [range_mulVecLin, range_mulVecLin]
    exact h.span_firstColumns_eq hkm hN
  exact le_antisymm (range_toEuclideanLin_le_of_range_mulVecLin_le hr.le)
    (range_toEuclideanLin_le_of_range_mulVecLin_le hr.ge)

/-- **The SVD step of Algorithm 6.4.3**: for `Q_A`, `Q_B` with orthonormal columns and an SVD
`Q_AᵀQ_B = YΣZᵀ`, the diagonal of `Σ` is the list of cosines of the principal angles between the
ranges, and the columns of `Q_A Y(:, 1:q)`, `Q_B Z` are principal vectors: the backbone's
`Submodule.cosPrincipalAngle_eq_of_isSVD` and `Submodule.isPrincipalVectors_of_isSVD`. -/
theorem isPrincipalVectors_of_isSVD {QA : Matrix (Fin m) (Fin p) ℝ}
    {QB : Matrix (Fin m) (Fin q) ℝ} (hA : QAᵀ * QA = 1) (hB : QBᵀ * QB = 1) (hqp : q ≤ p)
    {F G : Submodule ℝ (EuclideanSpace ℝ (Fin m))} (hF : LinearMap.range (toEuclideanLin QA) = F)
    (hG : LinearMap.range (toEuclideanLin QB) = G)
    {Y : Matrix (Fin p) (Fin p) ℝ} {σ : ℕ → ℝ} {Z : Matrix (Fin q) (Fin q) ℝ}
    (h : IsSVD (QAᵀ * QB) Y σ Z) :
    (∀ k < q, σ k = F.cosPrincipalAngle G k) ∧
    F.IsPrincipalVectors G
      (fun k => (WithLp.toLp 2 ((QA * firstColumns Y hqp).col k) : EuclideanSpace ℝ (Fin m)))
      (fun k => (WithLp.toLp 2 ((QB * Z).col k) : EuclideanSpace ℝ (Fin m))) := by
  subst hF hG
  have hA' : QAᴴ * QA = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hB' : QBᴴ * QB = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have h' : IsSVD (QAᴴ * QB) Y σ Z := by rwa [conjTranspose_eq_transpose_of_trivial]
  exact ⟨fun k hk => (Submodule.cosPrincipalAngle_eq_of_isSVD hA' hB' h' (by omega) hk).symm,
    Submodule.isPrincipalVectors_of_isSVD hA' hB' hqp h'⟩

/-- **Algorithm 6.4.3 is correct in exact arithmetic**: for `A`, `B` with linearly independent
columns (`q ≤ p ≤ m`; the Householder QR factorizations of chapter 5 need no further hypothesis)
and an `svd` subroutine returning SVDs, the output `(c, F, G)` has `c k = cos θ_{k+1}` for `k < q`
and the columns of `F` and `G` are principal vectors of `(ran(A), ran(B))`: orthonormal, in the
ranges, and `P_{ran A} g_k = cos θ_k f_k`. -/
theorem algorithm_6_4_3_spec
    (svd : Matrix (Fin p) (Fin q) ℝ →
      Id (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin q) (Fin q) ℝ))
    (hsvd : ∀ C, IsSVD C (Id.run (svd C)).1 (Id.run (svd C)).2.1 (Id.run (svd C)).2.2)
    (hqp : q ≤ p) (hpm : p ≤ m) {A : Matrix (Fin m) (Fin p) ℝ} {B : Matrix (Fin m) (Fin q) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (hB : LinearIndependent ℝ Bᵀ) :
    (∀ k < q, (Id.run (algorithm_6_4_3 pure svd hqp hpm A B)).1 k =
      (LinearMap.range (toEuclideanLin A)).cosPrincipalAngle
        (LinearMap.range (toEuclideanLin B)) k) ∧
    (LinearMap.range (toEuclideanLin A)).IsPrincipalVectors (LinearMap.range (toEuclideanLin B))
      (fun k => (WithLp.toLp 2 ((Id.run (algorithm_6_4_3 pure svd hqp hpm A B)).2.1.col k) :
        EuclideanSpace ℝ (Fin m)))
      (fun k => (WithLp.toLp 2 ((Id.run (algorithm_6_4_3 pure svd hqp hpm A B)).2.2.col k) :
        EuclideanSpace ℝ (Fin m))) := by
  have hqm := hqp.trans hpm
  obtain ⟨hQRA, -⟩ := Chapter05.algorithm_5_2_1_spec hpm A
  obtain ⟨hQRB, -⟩ := Chapter05.algorithm_5_2_1_spec hqm B
  set QA := Chapter05.factoredQ (Id.run (Chapter05.algorithm_5_2_1 pure A)).2
    (Id.run (Chapter05.algorithm_5_2_1 pure A)).1 with hQA
  set QB := Chapter05.factoredQ (Id.run (Chapter05.algorithm_5_2_1 pure B)).2
    (Id.run (Chapter05.algorithm_5_2_1 pure B)).1 with hQB
  have hrun : Id.run (algorithm_6_4_3 pure svd hqp hpm A B) =
      ((Id.run (svd ((firstColumns QA hpm)ᵀ * firstColumns QB hqm))).2.1,
        firstColumns QA hpm *
          firstColumns (Id.run (svd ((firstColumns QA hpm)ᵀ * firstColumns QB hqm))).1 hqp,
        firstColumns QB hqm *
          (Id.run (svd ((firstColumns QA hpm)ᵀ * firstColumns QB hqm))).2.2) := by
    simp only [algorithm_6_4_3, Id.run_bind, Chapter05.forwardAccumulation_spec,
      Chapter01.algorithm_1_1_5_spec, zero_add]
    rfl
  rw [hrun]
  have h1 := hQRA.conjTranspose_firstColumns_mul_self hpm
  have h2 := hQRB.conjTranspose_firstColumns_mul_self hqm
  rw [conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact isPrincipalVectors_of_isSVD h1 h2 hqp (range_toEuclideanLin_firstColumns hQRA hpm hA)
    (range_toEuclideanLin_firstColumns hQRB hqm hB)
    (hsvd ((firstColumns QA hpm)ᵀ * firstColumns QB hqm))

end PrincipalAnglesAlgorithm

/-! ### §6.4.4 Intersection of subspaces -/

/-- **Theorem 6.4.2.** "Let `{cos(θ_i)}` and `{f_i, g_i}` be defined by Algorithm 6.4.3. If the
index `s` is defined by `1 = cos(θ₁) = ⋯ = cos(θ_s) > cos(θ_{s+1})`, then
`ran(A) ∩ ran(B) = span{f₁, …, f_s} = span{g₁, …, g_s}`." Stated for any principal vectors of
`(ran(A), ran(B))`, which is what Algorithm 6.4.3 computes; `s` is characterized by
`cos θ_{i+1} = 1 ↔ i < s`. -/
theorem theorem_6_4_2 {q : ℕ} {A : Matrix (Fin m) (Fin p) ℝ} {B : Matrix (Fin m) (Fin q) ℝ}
    {f g : Fin q → EuclideanSpace ℝ (Fin m)}
    (hfg : (LinearMap.range (toEuclideanLin A)).IsPrincipalVectors
      (LinearMap.range (toEuclideanLin B)) f g) {s : ℕ}
    (hs : ∀ i : Fin q, (LinearMap.range (toEuclideanLin A)).cosPrincipalAngle
      (LinearMap.range (toEuclideanLin B)) i = 1 ↔ (i : ℕ) < s) :
    LinearMap.range (toEuclideanLin A) ⊓ LinearMap.range (toEuclideanLin B) =
        Submodule.span ℝ (f '' {i : Fin q | (i : ℕ) < s}) ∧
      LinearMap.range (toEuclideanLin A) ⊓ LinearMap.range (toEuclideanLin B) =
        Submodule.span ℝ (g '' {i : Fin q | (i : ℕ) < s}) := by
  have hset : {i : Fin q | (LinearMap.range (toEuclideanLin A)).cosPrincipalAngle
      (LinearMap.range (toEuclideanLin B)) i = 1} = {i : Fin q | (i : ℕ) < s} := Set.ext hs
  have h1 := hfg.inf_eq_span
  rw [hset] at h1
  refine ⟨h1, h1.trans ?_⟩
  congr 1
  refine Set.image_congr fun i hi => ?_
  exact hfg.eq_of_cosPrincipalAngle_eq_one ((hs i).2 hi)

end GolubVanLoan.Chapter06
