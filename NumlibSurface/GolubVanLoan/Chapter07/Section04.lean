import Numlib.LinearAlgebra.Matrix.Companion
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.KrylovDecomposition
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import NumlibSurface.GolubVanLoan.Chapter07.Section03

/-!
# Golub–Van Loan §7.4: the Hessenberg and real Schur forms

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.4: the real Schur decomposition (Theorem 7.4.1), the Hessenberg
decomposition (7.4.3) and the array reading of Algorithm 7.4.2 (`hessenbergPart`), the implicit Q
theorem (Theorem 7.4.2), Krylov matrices and unreduced Hessenberg matrices (Theorem 7.4.3),
geometric multiplicity one (Theorem 7.4.4), and the companion matrix decomposition (7.4.4) with
nonderogatory matrices (§7.4.6).

## Conventions

Real: `Matrix (Fin n) (Fin n) ℝ`, orthogonal `Q ∈ Matrix.orthogonalGroup (Fin n) ℝ`, `Qᵀ`. Upper
quasi-triangular is the backbone's `Matrix.IsQuasiUpperTriangular`; unreduced is
`Matrix.IsUnreducedUpperHessenberg` (the surface's `IsUnreduced`). Indices are 0-based: the book's
`H(k+1, k)`, `k = 1:n-1`, is `H ⟨k+1, _⟩ ⟨k, _⟩`, `k < n - 1`. Complex eigenvalues of a real matrix
are those of `Matrix.complexify`.

## Algorithms

Algorithms 7.4.1 (the Hessenberg QR step) and 7.4.2 (Householder reduction to Hessenberg form)
call chapter 5's shared helpers (`givensApplyLeft/Right`, `houseOn`, `householderApplyLeft/Right`),
which are not yet available; they are planned in this section's group and not written here.

## Not formalized

§7.4.4 (level-3 block Hessenberg reduction and the WY form: BLAS-level discussion); flop counts;
"this calculation can be highly unstable" for companion-matrix methods (no statement).
-/

open Matrix Polynomial

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-- Over `ℝ` the star of a matrix is its transpose. -/
private theorem star_eq_transpose_real {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) : star M = Mᵀ := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-! ### §7.4.1 The real Schur decomposition -/

/-- **Theorem 7.4.1 (real Schur decomposition)** (7.4.2). For `A ∈ ℝ^{n×n}` there is an orthogonal
`Q` with `Qᵀ A Q` upper quasi-triangular: block upper triangular for a monotone block index `p` with
blocks `R_ii` of size `1` or `2`, each `2 × 2` block having a pair of complex conjugate (nonreal)
eigenvalues — it has no real eigenvalue. -/
theorem theorem_7_4_1 (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, (Qᵀ * A * Q).IsQuasiUpperTriangular ∧
      ∃ p : Fin n → ℕ, Monotone p ∧ (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
        (Qᵀ * A * Q).BlockTriangular p ∧
        ∀ k, (Finset.univ.filter fun i => p i = k).card = 2 → ∀ μ : ℝ,
          μ ∉ spectrum ℝ ((Qᵀ * A * Q).toBlock (fun i => p i = k) (fun i => p i = k)) := by
  obtain ⟨Q, hQ, p, hp, hcard, htri, hirr⟩ :=
    exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks A
  exact ⟨Q, hQ, ⟨p, hp, hcard, htri⟩, p, hp, hcard, htri, hirr⟩

/-! ### §7.4.2–7.4.3 The Hessenberg decomposition -/

/-- **(7.4.3), the Hessenberg decomposition**: for `A ∈ ℝ^{n×n}` there is an orthogonal `U₀` with
`U₀ᵀ A U₀` upper Hessenberg and `U₀ e₁ = e₁` (the Householder reduction's reflectors act on the
coordinates `≥ 2` only). -/
theorem equation_7_4_3 {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∃ U₀ ∈ orthogonalGroup (Fin (N + 1)) ℝ, (U₀ᵀ * A * U₀).IsUpperHessenberg ∧
      U₀ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  refine ⟨hessenbergQ A, hessenbergQ_mem_orthogonalGroup A, ?_, ?_⟩
  · have h := isUpperHessenberg_hessenbergReduce (A := A)
    rwa [hessenbergReduce_eq_conj, conjTranspose_eq_transpose_of_trivial] at h
  · ext i
    rw [mulVec_single_one, col_apply, hessenbergQ_apply_zero, one_apply, Pi.single_apply]

/-- **§7.4.3, the array of Algorithm 7.4.2**: the book's reading of an array that holds `H` in its
upper Hessenberg part and the essential parts of the Householder vectors below the subdiagonal
("The `k`th Householder matrix can be represented in `A(k+2:n, k)`"): the entries on or above the
subdiagonal, `hessenbergPart A i j = A i j` for `i ≤ j + 1`, and `0` below. -/
def hessenbergPart (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) ≤ j + 1 then A i j else 0

/-! ### §7.4.5 The implicit Q theorem -/

/-- **§7.4.5, Definition**: an upper Hessenberg matrix is *unreduced* if it has no zero subdiagonal
entries — the backbone's `Matrix.IsUnreducedUpperHessenberg`; `isUnreduced_iff` spells it out
along the subdiagonal. -/
def IsUnreduced (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  H.IsUnreducedUpperHessenberg

/-- An unreduced upper Hessenberg matrix: upper Hessenberg with `h_{k+1,k} ≠ 0` for every
`k < n - 1` (0-based). -/
theorem isUnreduced_iff {H : Matrix (Fin n) (Fin n) ℝ} :
    IsUnreduced H ↔
      H.IsUpperHessenberg ∧ ∀ (k : ℕ) (hk : k + 1 < n), H ⟨k + 1, hk⟩ ⟨k, by omega⟩ ≠ 0 :=
  isUnreducedUpperHessenberg_iff_fin

/-- **Theorem 7.4.2 (implicit Q theorem).** Let `Q`, `V` be orthogonal with `Qᵀ A Q = H` and
`Vᵀ A V = G` upper Hessenberg and the same first column, `q₁ = v₁`. If the first `k` subdiagonal
entries `h_{i+1,i}`, `i < k` (0-based), are nonzero — the book's "`k + 1` is the smallest index with
`h_{k+1,k} = 0`", or `k = n - 1` when `H` is unreduced — then `v_i = ± q_i` for `i ≤ k`,
`|g_{i+1,i}| = |h_{i+1,i}|` for `i < k`, and `g_{k+1,k} = 0` when `h_{k+1,k} = 0`. -/
theorem theorem_7_4_2 {N : ℕ} {A Q V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hV : V ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hH : (Qᵀ * A * Q).IsUpperHessenberg) (hG : (Vᵀ * A * V).IsUpperHessenberg)
    (h0 : V.col 0 = Q.col 0) {k : ℕ} (hk : k ≤ N)
    (hsub : ∀ i : Fin N, (i : ℕ) < k → (Qᵀ * A * Q) i.succ i.castSucc ≠ 0) :
    (∀ i : Fin (N + 1), (i : ℕ) ≤ k → V.col i = Q.col i ∨ V.col i = -Q.col i) ∧
      (∀ i : Fin N, (i : ℕ) < k →
        |(Vᵀ * A * V) i.succ i.castSucc| = |(Qᵀ * A * Q) i.succ i.castSucc|) ∧
      (∀ i : Fin N, (i : ℕ) = k → (Qᵀ * A * Q) i.succ i.castSucc = 0 →
        (Vᵀ * A * V) i.succ i.castSucc = 0) :=
  implicitQ_of_apply_eq_zero_real hQ hV hH hG h0 hk hsub

/-- **The gist of Theorem 7.4.2**: if `Qᵀ A Q = H` is unreduced upper Hessenberg, `Zᵀ A Z = G` is
upper Hessenberg, and `Q`, `Z` have the same first column, then `Z = Q D` and `G = D H D` for a
diagonal `D = diag(±1, …, ±1)` (`D⁻¹ = D`) — "`G` and `H` are essentially equal". -/
theorem theorem_7_4_2_essential {N : ℕ} {A Q Z : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hZ : Z ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hH : IsUnreduced (Qᵀ * A * Q)) (hG : (Zᵀ * A * Z).IsUpperHessenberg)
    (h0 : Z.col 0 = Q.col 0) :
    ∃ d : Fin (N + 1) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ d 0 = 1 ∧ Z = Q * diagonal d ∧
      Zᵀ * A * Z = diagonal d * (Qᵀ * A * Q) * diagonal d :=
  implicitQ_real hQ hZ hH hG h0

/-- **§7.4.5, Definition: the Krylov matrix** `K(A, v, j) = [v | Av | ⋯ | A^{j-1} v] ∈ ℝ^{n×j}`,
the backbone's `Matrix.krylovMatrix`. -/
def krylovMatrix (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (j : ℕ) :
    Matrix (Fin n) (Fin j) ℝ :=
  Matrix.krylovMatrix A v j

/-- **Theorem 7.4.3.** For orthogonal `Q`, `Qᵀ A Q = H` is unreduced upper Hessenberg if and only if
`Qᵀ K(A, Q(:, 1), n) = R` is nonsingular and upper triangular. -/
theorem theorem_7_4_3 {N : ℕ} {Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    IsUnreduced (Qᵀ * A * Q) ↔
      (Qᵀ * krylovMatrix A (Q.col 0) (N + 1)).IsUpperTriangular ∧
        IsUnit (Qᵀ * krylovMatrix A (Q.col 0) (N + 1)).det := by
  have h := isUnreducedUpperHessenberg_conj_iff_krylovMatrix hQ A
  rwa [star_eq_transpose_real] at h

/-- The geometric multiplicity of an eigenvalue is at least one. -/
private theorem one_le_finrank_eigenspace {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ M) : 1 ≤ Module.finrank ℂ (Module.End.eigenspace (toLin' M) μ) := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul M μ).1 hμ
  refine Submodule.one_le_finrank_iff.2 fun h => hv0 ?_
  have hmem : v ∈ Module.End.eigenspace (toLin' M) μ := by
    rw [Module.End.mem_eigenspace_iff, toLin'_apply]; exact hv
  rw [h, Submodule.mem_bot] at hmem
  exact hmem

/-- The geometric multiplicity of every eigenvalue of an unreduced upper Hessenberg matrix is at
most one (the backbone's rank argument, after complexification). -/
private theorem finrank_eigenspace_le_one_of_isUnreduced {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUnreduced H) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (toLin' H.complexify) μ) ≤ 1 := by
  cases n with
  | zero =>
    have : Module.finrank ℂ (Fin 0 → ℂ) = 0 := by simp
    exact (Submodule.finrank_le _).trans (by omega)
  | succ N =>
    exact IsUnreducedUpperHessenberg.finrank_eigenspace_le_one
      (hH.map (f := Complex.ofRealHom) Complex.ofReal_injective) μ

/-- **Theorem 7.4.4.** If `λ` is an eigenvalue of an unreduced upper Hessenberg `H ∈ ℝ^{n×n}`, its
geometric multiplicity is `1`: `rank(H - λI) ≥ n - 1` because the first `n - 1` columns of
`H - λI` are independent. (The book writes `A - λI` for `H - λI` in the proof.) -/
theorem theorem_7_4_4 {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUnreduced H) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ H.complexify) :
    Module.finrank ℂ (Module.End.eigenspace (toLin' H.complexify) μ) = 1 :=
  le_antisymm (finrank_eigenspace_le_one_of_isUnreduced hH μ) (one_le_finrank_eigenspace hμ)

/-! ### §7.4.6 The companion matrix decomposition -/

/-- **(7.4.4), the companion matrix** in the book's layout: ones on the subdiagonal, last column
`-c`, zeros elsewhere. Its relation to the backbone's `Matrix.companion` (first-row layout) is
`companion_eq`. -/
def companion (c : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (j : ℕ) + 1 = n then -c i else if (i : ℕ) = j + 1 then 1 else 0

/-- The monic polynomial `z^n + c_{n-1} z^{n-1} + ⋯ + c₀` with coefficients `c`. -/
private theorem coeff_X_pow_add_sum (c : Fin n → ℝ) (i : Fin n) :
    (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).coeff i = c i := by
  have hi : (i : ℕ) ≠ n := i.isLt.ne
  simp only [coeff_add, coeff_X_pow, hi, ↓reduceIte, zero_add, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)]
  · simp
  · rw [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext h).symm hji

/-- The companion matrix (7.4.4) is the transpose of the backbone's `Matrix.companion p n` of
`p = z^n + ∑ c_i z^i`, read in reverse order. -/
theorem companion_eq (c : Fin n → ℝ) :
    companion c = ((Matrix.companion (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)) n)ᵀ).submatrix
      Fin.rev Fin.rev := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [companion, of_apply, submatrix_apply, transpose_apply, companion_apply, Fin.val_rev]
  by_cases hjn : (j : ℕ) + 1 = n
  · have h2 : n - 1 - (n - ((i : ℕ) + 1)) = i := by omega
    simp only [hjn, Nat.sub_self, h2, ↓reduceIte, coeff_X_pow_add_sum]
  · have h1 : n - ((j : ℕ) + 1) ≠ 0 := by omega
    have h3 : ((i : ℕ) = j + 1) ↔ (n - ((j : ℕ) + 1) = n - ((i : ℕ) + 1) + 1) := by omega
    simp only [hjn, h1, ↓reduceIte, h3]

/-- **§7.4.6**: `det(zI - C) = c₀ + c₁ z + ⋯ + c_{n-1} z^{n-1} + z^n` for the companion matrix
(7.4.4). -/
theorem charpoly_companion' (c : Fin n → ℝ) :
    (companion c).charpoly = X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ) := by
  have hdeg := degree_sum_fin_lt c
  have hmonic : (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).Monic := monic_X_pow_add hdeg
  have hnat : (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).natDegree = n := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  rw [companion_eq, show ∀ M : Matrix (Fin n) (Fin n) ℝ, M.submatrix Fin.rev Fin.rev =
      reindex Fin.revPerm Fin.revPerm M from fun M => rfl, charpoly_reindex, charpoly_transpose,
    charpoly_companion hmonic hnat]

/-- **§7.4.6 with (7.4.4).** If the Krylov matrix `K = K(A, x, n)` satisfies `K c = -A^n x`, then
`A K = K C` for the companion matrix `C` of `c`, whose characteristic polynomial is
`c₀ + c₁ z + ⋯ + c_{n-1} z^{n-1} + z^n`; so if `K` is nonsingular, `K⁻¹ A K = C` displays `A`'s
characteristic polynomial. -/
theorem equation_7_4_4 {A : Matrix (Fin n) (Fin n) ℝ} {x c : Fin n → ℝ}
    (hc : krylovMatrix A x n *ᵥ c = -(A ^ n *ᵥ x)) :
    A * krylovMatrix A x n = krylovMatrix A x n * companion c ∧
      (companion c).charpoly = X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ) ∧
      (IsUnit (krylovMatrix A x n) →
        (krylovMatrix A x n)⁻¹ * A * krylovMatrix A x n = companion c ∧
          A.charpoly = X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)) := by
  set K := krylovMatrix A x n
  have hAK : A * K = K * companion c := by
    ext r j
    have hj := j.isLt
    have lhs : (A * K) r j = (A ^ ((j : ℕ) + 1) *ᵥ x) r := by
      rw [pow_succ', ← mulVec_mulVec]
      rfl
    rw [lhs, mul_apply]
    by_cases hjn : (j : ℕ) + 1 = n
    · have hsum : ∑ i, K r i * companion c i j = -(K *ᵥ c) r := by
        simp only [companion, of_apply, hjn, ↓reduceIte, mulVec, dotProduct,
          ← Finset.sum_neg_distrib, mul_neg]
      rw [hsum, hc, Pi.neg_apply, neg_neg, hjn]
    · have hj1 : (j : ℕ) + 1 < n := by omega
      rw [Finset.sum_eq_single ⟨(j : ℕ) + 1, hj1⟩]
      · simp only [companion, of_apply, hjn, ↓reduceIte, mul_one]
        rfl
      · intro i _ hi
        have hi' : ¬ ((i : ℕ) = j + 1) := fun h => hi (Fin.ext h)
        simp only [companion, of_apply, hjn, hi', ↓reduceIte, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hchar := charpoly_companion' c
  refine ⟨hAK, hchar, fun hK => ⟨?_, ?_⟩⟩
  · rw [Matrix.mul_assoc, hAK, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det K).1 hK), Matrix.one_mul]
  · have hsim : IsSimilar A (K⁻¹ * A * K) := ⟨K, hK, rfl⟩
    rw [hsim.charpoly_eq, Matrix.mul_assoc, hAK, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det K).1 hK), Matrix.one_mul, hchar]

/-- **§7.4.6, Definition**: `A` is *nonderogatory* if each (complex) eigenvalue has unit geometric
multiplicity, `dim null(A - λI) ≤ 1` for every `λ`. -/
def IsNonderogatory (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ μ : ℂ, Module.finrank ℂ (Module.End.eigenspace (toLin' A.complexify) μ) ≤ 1

/-- **§7.4.6: "`A` is similar to an unreduced Hessenberg matrix only if each eigenvalue has unit
geometric multiplicity"** — Theorem 7.4.4 transported along the (complexified) similarity. -/
theorem isNonderogatory_of_isSimilar_unreduced {A H : Matrix (Fin n) (Fin n) ℝ}
    (hs : IsSimilar A H) (hH : IsUnreduced H) : IsNonderogatory A := by
  obtain ⟨X, hX, rfl⟩ := hs
  have hsim : IsSimilar A.complexify (X⁻¹ * A * X).complexify :=
    ⟨X.complexify, (isUnit_complexify_iff X).2 hX, by
      rw [complexify_mul, complexify_mul, complexify_inv]⟩
  intro μ
  have h := finrank_eigenspace_le_one_of_isUnreduced hH μ
  have e1 := eigenspace_mulVecLin_eq_ker A.complexify μ
  have e2 := eigenspace_mulVecLin_eq_ker (X⁻¹ * A * X).complexify μ
  change Module.finrank ℂ (Module.End.eigenspace (A.complexify).mulVecLin μ) ≤ 1
  change Module.finrank ℂ (Module.End.eigenspace ((X⁻¹ * A * X).complexify).mulVecLin μ) ≤ 1 at h
  rw [e1, (hsim.sub_smul_one μ).finrank_ker_mulVecLin_eq, ← e2]
  exact h

end GolubVanLoan.Chapter07
