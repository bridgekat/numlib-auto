import Numlib.LinearAlgebra.Matrix.Semiseparable
import Numlib.LinearAlgebra.Matrix.RealSchur
import NumlibSurface.GolubVanLoan.Chapter12.Section01

/-!
# Golub–Van Loan §12.2: structured-rank problems

Surface file for §12.2 of Golub and Van Loan, *Matrix Computations* (4th edition): semiseparable and
quasiseparable matrices (12.2.1)–(12.2.8), the inverse facts of §12.2.3, triangular semiseparable
matrices and the fast product (12.2.9), the LU Algorithm 12.2.1, the Givens-vector representation
(12.2.11) and the QR Algorithm 12.2.2 with (12.2.14), (12.2.16), the banded inverses of §12.2.8, and
the orthogonal Hessenberg eigenproblem (12.2.18)–(12.2.19) with the facts of §12.2.10.

## Design

Matrices are real, `Matrix (Fin n) (Fin n) ℝ`, 0-based. The book's `B(r)` with `r ∈ ℝ^{n−1}` is the
backbone's `Matrix.unitBidiagonal n r` with `r : ℕ → ℝ` (entries past `n − 2` unused);
`𝐒(u, v, t, d, p, q, r)` is `Matrix.quasiseparableOf u v t d p q r` (the book's (12.2.8) order),
whose entries use the products `t_j ⋯ t_{i−1}`; the corrected quasiseparable representation with the
Eidelman–Gohberg transfer products `t_{j+1} ⋯ t_{i−1}` is `Matrix.quasiseparableRep`. MATLAB's
`tril(A, −1)`, `triu(A, 1)` and `diag` are `Matrix.strictLower`, `Matrix.strictUpper` and
`Matrix.diagPart`; `.*` is `⊙`. The chain `Qᵀ = G₁ ⋯ G_{n−1}` of `2 × 2` blocks in consecutive
coordinate planes is `Matrix.givensChain`.

## Not formalized here

The operation and storage counts, §12.2.8's misprinted `{p, q}`-semiseparable definition and the
extended, sequentially semiseparable and hierarchical classes ((12.2.17) is a shape), §12.2.9
(eigenvalue methods: prose with citations), the pivoting variant of Algorithm 12.2.1 (described in
words), and Fact 3 of §12.2.10 (it names neither the perfect shuffles nor the block positions).
-/

open Matrix

namespace GolubVanLoan.Chapter12

variable {n : ℕ}

/-! ### Semiseparable and quasiseparable matrices (§12.2.1–12.2.3) -/

/-- **(12.2.1)** as a characterization: `A` is semiseparable, every submatrix `A(i₁:i₂, j₁:j₂)` with
`j₂ ≤ i₁` or `i₂ ≤ j₁` having rank at most one, iff the maximal such blocks do
(`Matrix.IsSemiseparable`). -/
theorem equation_12_2_1 (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsSemiseparable ↔ ∀ i₁ i₂ j₁ j₂ : Fin n, j₂ ≤ i₁ ∨ i₂ ≤ j₁ →
      (A.toBlock (· ∈ Set.Icc i₁ i₂) (· ∈ Set.Icc j₁ j₂)).rank ≤ 1 := by
  convert isSemiseparable_iff_forall_rank_toBlock_Icc_le (A := A)

/-- **(12.2.3)** and the sentence before it: `B(r)⁻¹` has the entries `r_i ⋯ r_{j−1}` on and above
the diagonal (`1` on it) and zero below, and it is semiseparable (P12.2.1). -/
theorem equation_12_2_3 (r : ℕ → ℝ) :
    (unitBidiagonal n r)⁻¹ =
        of (fun (i j : Fin n) => if i ≤ j then ∏ l ∈ Finset.Ico (i : ℕ) j, r l else 0) ∧
      (unitBidiagonal n r)⁻¹.IsSemiseparable :=
  ⟨inv_unitBidiagonal r, isSemiseparable_inv_unitBidiagonal r⟩

/-- **§12.2.1**: if `x_1, …, x_{n−1} ≠ 0` and `r = x(2:n) ./ x(1:n−1)`, then `B(r)ᵀ x = x₁ e₁`. -/
theorem unitBidiagonal_introduces_zeros {x : Fin (n + 1) → ℝ} {r : ℕ → ℝ}
    (hx : ∀ (l : ℕ) (h : l < n), x ⟨l, by omega⟩ ≠ 0)
    (hr : ∀ (l : ℕ) (h : l < n), r l = x ⟨l + 1, by omega⟩ / x ⟨l, by omega⟩) :
    (unitBidiagonal (n + 1) r)ᵀ *ᵥ x = Pi.single 0 (x 0) :=
  unitBidiagonal_transpose_mulVec_eq_single hx hr

/-- **(12.2.4)**: the product `M = M₁ ⋯ M_{n−1}` of the `2 × 2` blocks `M_k = [α_k β_k; γ_k δ_k]`
embedded in the consecutive coordinate planes has the displayed entries — `γ_j` on the subdiagonal,
`δ_{i−1} β_i ⋯ β_{j−1} α_j` on and above the diagonal (with `δ_0 = 1` in the first row and `α_{n−1}
= 1` in the last column), zero below the subdiagonal — and it is quasiseparable. -/
theorem equation_12_2_4 {N : ℕ} (M : ℕ → Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ i j : Fin (N + 1), givensChain N M i j =
      if (i : ℕ) = j + 1 then M j 1 0
      else if (i : ℕ) ≤ j then
        ((if (i : ℕ) = 0 then 1 else M (i - 1) 1 1) * ∏ l ∈ Finset.Ico (i : ℕ) j, M l 0 1) *
          (if (j : ℕ) = N then 1 else M j 0 0)
      else 0) ∧
      (givensChain N M).IsQuasiseparable :=
  ⟨givensChain_apply, givensChain_isQuasiseparable⟩

/-- **(12.2.5)** as a characterization: `A` is quasiseparable, every submatrix `A(i₁:i₂, j₁:j₂)`
with `j₂ < i₁` or `i₂ < j₁` having rank at most one, iff the maximal such blocks do; and every
semiseparable matrix is quasiseparable (the sentence after (12.2.5)). -/
theorem equation_12_2_5 (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.IsQuasiseparable ↔ ∀ i₁ i₂ j₁ j₂ : Fin n, j₂ < i₁ ∨ i₂ < j₁ →
      (A.toBlock (· ∈ Set.Icc i₁ i₂) (· ∈ Set.Icc j₁ j₂)).rank ≤ 1) ∧
      (A.IsSemiseparable → A.IsQuasiseparable) := by
  refine ⟨?_, IsSemiseparable.isQuasiseparable⟩
  convert isQuasiseparable_iff_forall_rank_toBlock_Icc_le (A := A)

/-- **(12.2.6)**: the generator representation `tril(u vᵀ, −1) + diag(d) + triu(p qᵀ, 1)` is
`𝐒(u, v, 1, d, p, q, 1)`; it is quasiseparable, and semiseparable when `d = u .* v = p .* q`. -/
theorem equation_12_2_6 (u v d p q : Fin n → ℝ) :
    (vecMulVec u v).strictLower + diagonal d + (vecMulVec p q).strictUpper =
        quasiseparableOf u v 1 d p q 1 ∧
      (quasiseparableOf u v 1 d p q 1).IsQuasiseparable ∧
      (d = u * v → d = p * q → (quasiseparableOf u v 1 d p q 1).IsSemiseparable) := by
  refine ⟨?_, isQuasiseparable_quasiseparableOf _ _ _ _ _ _ _,
    isSemiseparable_quasiseparableOf _ _ _ _ _ _ _⟩
  ext i j
  simp only [Matrix.add_apply, strictLower, strictUpper, of_apply, vecMulVec_apply,
    diagonal_apply, quasiseparableOf, Pi.one_apply, Finset.prod_const_one, mul_one]
  rcases lt_trichotomy j i with h | rfl | h
  · simp [h, h.ne', not_lt.2 h.le]
  · simp
  · simp [h, h.ne, not_lt.2 h.le]

/-- **§12.2.3**: for `n ≥ 3` and `r` with nonzero entries (`r₁, r₂ ≠ 0` suffice), `B(r)` has no
generator representation (12.2.6). -/
theorem unitBidiagonal_not_generatorRepresentable {r : ℕ → ℝ} (hn : 3 ≤ n) (h₀ : r 0 ≠ 0)
    (h₁ : r 1 ≠ 0) (u v d p q : Fin n → ℝ) :
    unitBidiagonal n r ≠ quasiseparableOf u v 1 d p q 1 :=
  unitBidiagonal_ne_generatorRep hn h₀ h₁ u v d p q

/-- **(12.2.7)**: the Hadamard product of two quasiseparable matrices is quasiseparable (P12.2.8).
-/
theorem equation_12_2_7 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsQuasiseparable)
    (hB : B.IsQuasiseparable) : (A ⊙ B).IsQuasiseparable :=
  hA.hadamard hB

/-- **(12.2.8)**, corrected: `A` is quasiseparable iff it has the Eidelman–Gohberg representation
`Matrix.quasiseparableRep u v t d p q r` (subdiagonal entries `u_i t_{j+1} ⋯ t_{i−1} v_j`,
superdiagonal ones `p_i r_{i+1} ⋯ r_{j−1} q_j`). **As printed the book's claim is false for `n ≥
3`**: the quasiseparable `B(r)` with `r₀ r₁ ≠ 0` has no representation `𝐒(u, v, t, d, p, q, r')` of
(12.2.8), whose entries force `a₀₁ a₁₂ = a₀₂ p₁ q₁`. -/
theorem equation_12_2_8 (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.IsQuasiseparable ↔ ∃ u v t d p q r, A = quasiseparableRep u v t d p q r) ∧
      (3 ≤ n → ∀ r : ℕ → ℝ, r 0 ≠ 0 → r 1 ≠ 0 → (unitBidiagonal n r).IsQuasiseparable ∧
        ∀ u v t d p q r', unitBidiagonal n r ≠ quasiseparableOf u v t d p q r') :=
  ⟨exists_quasiseparableRep, fun hn r h₀ h₁ =>
    ⟨isQuasiseparable_unitBidiagonal r,
      fun u v t d p q r' => unitBidiagonal_ne_quasiseparableOf hn h₀ h₁ u v t d p q r'⟩⟩

/-- **The specializations listed after (12.2.8)**: `d = u .* v = p .* q` gives a semiseparable
matrix, `t = r = 1` the generator representation (12.2.6), `u = q`, `v = p`, `t = r` a symmetric
matrix, and `u .* v = p .* q` with free `d` the semiseparable-plus-diagonal class:
`𝐒(u, v, t, d, p, q, r) − diag(d − u .* v)` is semiseparable. -/
theorem equation_12_2_8_b (u v d p q : Fin n → ℝ) (t r : ℕ → ℝ) :
    (d = u * v → d = p * q → (quasiseparableOf u v t d p q r).IsSemiseparable) ∧
      (quasiseparableOf u v t d v u t)ᵀ = quasiseparableOf u v t d v u t ∧
      (u * v = p * q →
        (quasiseparableOf u v t d p q r - diagonal (d - u * v)).IsSemiseparable) := by
  refine ⟨isSemiseparable_quasiseparableOf _ _ _ _ _ _ _, transpose_quasiseparableOf _ _ _ _ _ _ _,
    fun h => ?_⟩
  have : quasiseparableOf u v t d p q r - diagonal (d - u * v) =
      quasiseparableOf u v t (u * v) p q r := by
    ext i j
    simp only [Matrix.sub_apply, quasiseparableOf, of_apply, diagonal_apply, Pi.sub_apply,
      Pi.mul_apply]
    rcases lt_trichotomy j i with hji | rfl | hji
    · simp [hji, hji.ne']
    · simp
    · simp [hji.ne, not_lt.2 hji.le]
  rw [this]
  exact isSemiseparable_quasiseparableOf _ _ _ _ _ _ _ rfl h

/-- **Fact 1 of §12.2.3**: the inverse of a nonsingular tridiagonal matrix is semiseparable, and
generator-representable when the sub- and superdiagonal entries are nonzero. -/
theorem inv_tridiagonal_isSemiseparable {A : Matrix (Fin n) (Fin n) ℝ} (hT : A.IsTridiagonal)
    (hA : IsUnit A) :
    A⁻¹.IsSemiseparable ∧
      ((∀ i j : Fin n, (i : ℕ) = j + 1 → A i j ≠ 0) → (∀ i j : Fin n, (j : ℕ) = i + 1 → A i j ≠ 0) →
        ∃ u v p q, u * v = p * q ∧ A⁻¹ = quasiseparableOf u v 1 (u * v) p q 1) :=
  ⟨hT.isSemiseparable_inv hA, fun hsub hsup => hT.inv_eq_generatorRep hA hsub hsup⟩

/-- **Fact 2 of §12.2.3**: the inverse of a nonsingular quasiseparable matrix is quasiseparable. -/
theorem inv_isQuasiseparable {A : Matrix (Fin n) (Fin n) ℝ} (h : A.IsQuasiseparable)
    (hA : IsUnit A) : A⁻¹.IsQuasiseparable :=
  h.inv hA

/-- **Fact 3 of §12.2.3**: if `A = D + S` is nonsingular with `D` diagonal nonsingular and `S`
semiseparable, then `A⁻¹ = D⁻¹ + S₁` with `S₁` semiseparable. -/
theorem inv_diagonal_add_semiseparable {δ : Fin n → ℝ} (hδ : ∀ i, δ i ≠ 0)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsSemiseparable) (hu : IsUnit (diagonal δ + S)) :
    ∃ S₁ : Matrix (Fin n) (Fin n) ℝ, S₁.IsSemiseparable ∧
      (diagonal δ + S)⁻¹ = (diagonal δ)⁻¹ + S₁ :=
  inv_diagonal_add_eq_add hδ hS hu

/-! ### Triangular semiseparable matrices (§12.2.4–12.2.5) -/

/-- **§12.2.4**: a lower triangular semiseparable `L` is `𝐒(u, v, t, u .* v, 0, 0, 0)`, and an upper
triangular semiseparable `U` is `𝐒(0, 0, 0, p .* q, p, q, r)`, for suitable vectors. -/
theorem triangular_semiseparable_rep (L U : Matrix (Fin n) (Fin n) ℝ) :
    (L.IsSemiseparable → L.IsLowerTriangular → ∃ u v t, L = quasiseparableOf u v t (u * v) 0 0 0) ∧
      (U.IsSemiseparable → U.IsUpperTriangular →
        ∃ p q r, U = quasiseparableOf 0 0 0 (p * q) p q r) := by
  refine ⟨exists_lower_semiseparable_rep, fun hS hU => ?_⟩
  obtain ⟨u, v, t, h⟩ := exists_lower_semiseparable_rep hS.transpose hU.transpose
  refine ⟨v, u, t, ?_⟩
  rw [← transpose_transpose U, h, transpose_quasiseparableOf, mul_comm v u]

/-- **(12.2.9)** and the displays after it: `(triu(p qᵀ) .* B(r)⁻¹) x = p .* (B(r)⁻¹ (q .* x))` —
the upper triangular semiseparable matrix is `diag(p) B(r)⁻¹ diag(q)` (`triu` is immaterial,
`B(r)⁻¹` being upper triangular) — and for `p`, `q` with nonzero entries the system `(triu(p qᵀ) .*
B(r)⁻¹) x = y` is solved by `x = (B(r) (y ./ p)) ./ q`. -/
theorem equation_12_2_9 (p q : Fin n → ℝ) (r : ℕ → ℝ) :
    (∀ x, (vecMulVec p q ⊙ (unitBidiagonal n r)⁻¹) *ᵥ x = p * ((unitBidiagonal n r)⁻¹ *ᵥ (q * x))) ∧
      ((∀ i, p i ≠ 0) → (∀ i, q i ≠ 0) → ∀ x y,
        (vecMulVec p q ⊙ (unitBidiagonal n r)⁻¹) *ᵥ x = y →
          x = (unitBidiagonal n r *ᵥ (y / p)) / q) :=
  ⟨vecMulVec_hadamard_inv_unitBidiagonal_mulVec p q r, fun hp hq _ _ h =>
    eq_div_of_vecMulVec_hadamard_inv_unitBidiagonal_mulVec_eq r hp hq h⟩

/-- **§12.2.5**: if the semiseparable `A` has an LU factorization then `U` is semiseparable, and so
is `L` when the strict leading principal submatrices of `A` are nonsingular. The book's unqualified
claim for `L` is false for singular `A`: `L = [1 0 0; 0 1 0; 1 0 1]`, `U = [0 0 0; 0 1 z; 0 0 1]`
give `A = L U = U` semiseparable while `L(2:3, 1:2)` has rank two. -/
theorem semiseparable_lu_factors {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U)
    (hA : A.IsSemiseparable) :
    U.IsSemiseparable ∧
      ((∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) → L.IsSemiseparable) :=
  ⟨h.isSemiseparable_upper hA, h.isSemiseparable_lower hA⟩

/-! ### LU of a semiseparable matrix (Algorithm 12.2.1) -/

section LU

/-- One step of Algorithm 12.2.1 (0-based `k`, the book's `k + 1`): `τ_k = t_k u_{k+1} / u_k` (two
roundings) and `p̃_{k+1} = p_{k+1} − p_k τ_k r_k` (three roundings, left to right). -/
noncomputable def algorithm_12_2_1Step {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (u p : Fin n → ℝ) (t r : ℕ → ℝ) (k : Fin (n - 1)) : M (ℝ × ℝ) := do
  let τk ← rnd ((← rnd (t k * u ⟨k + 1, by omega⟩)) / u ⟨k, by omega⟩)
  let pk ← rnd (p ⟨k + 1, by omega⟩ - (← rnd ((← rnd (p ⟨k, by omega⟩ * τk)) * r k)))
  pure (τk, pk)

/-- **Algorithm 12.2.1**: for `A = 𝐒(u, v, t, u .* v, p, q, r)` with `u .* v = p .* q`, the vectors
`p̃ ∈ ℝⁿ` and `τ ∈ ℝ^{n−1}` of `A = L U`, `L = B(τ)⁻ᵀ`, `U = triu(p̃ qᵀ) .* B(r)⁻¹`:
`for k = n−1:−1:1, τ_k = t_k u_{k+1}/u_k, p̃_{k+1} = p_{k+1} − p_k τ_k r_k, end; p̃₁ = p₁`. The loop
stores the pair `(τ_k, p̃_{k+1})` of step `k`; `v`, `q` enter only the specification. -/
noncomputable def algorithm_12_2_1 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) (u p : Fin n → ℝ)
    (t r : ℕ → ℝ) : M ((Fin n → ℝ) × (ℕ → ℝ)) := do
  let st ← vecLoopOn (List.finRange (n - 1)).reverse (algorithm_12_2_1Step rnd u p t r)
  pure (fun i => if h : (i : ℕ) = 0 then p i else (st ⟨i - 1, by omega⟩).2,
    fun k => if h : k < n - 1 then (st ⟨k, h⟩).1 else 0)

/-- **Correctness of Algorithm 12.2.1**: if `u .* v = p .* q` and `u_k ≠ 0` for `k < n` (the book's
`1 : n − 1`; its "has an LU factorization" does not ensure these divisions), the computed `(p̃, τ)`
satisfy `A = B(τ)⁻ᵀ (triu(p̃ qᵀ) .* B(r)⁻¹)` for `A = 𝐒(u, v, t, u .* v, p, q, r)`, with the closed
forms after the algorithm: `τ = (u(2:n) .* t) ./ u(1:n−1)`, `p̃ = [p₁; p(2:n) − p(1:n−1) .* τ .*
r]`. The text's "`M = B(τ)`" should read `M = B(τ)ᵀ`. -/
theorem algorithm_12_2_1_spec (u v p q : Fin n → ℝ) (t r : ℕ → ℝ) (huv : u * v = p * q)
    (hu : ∀ k : Fin n, (k : ℕ) + 1 < n → u k ≠ 0) :
    IsLU (quasiseparableOf u v t (u * v) p q r)
        (unitBidiagonal n (Id.run (algorithm_12_2_1 pure u p t r)).2)ᵀ⁻¹
        (vecMulVec (Id.run (algorithm_12_2_1 pure u p t r)).1 q ⊙ (unitBidiagonal n r)⁻¹) ∧
      (∀ k (h : k + 1 < n), (Id.run (algorithm_12_2_1 pure u p t r)).2 k =
        t k * u ⟨k + 1, h⟩ / u ⟨k, by omega⟩) ∧
      (∀ h : 0 < n, (Id.run (algorithm_12_2_1 pure u p t r)).1 ⟨0, h⟩ = p ⟨0, h⟩) ∧
      ∀ k (h : k + 1 < n), (Id.run (algorithm_12_2_1 pure u p t r)).1 ⟨k + 1, h⟩ =
        p ⟨k + 1, h⟩ - p ⟨k, by omega⟩ * (Id.run (algorithm_12_2_1 pure u p t r)).2 k * r k := by
  have hrun : Id.run (algorithm_12_2_1 pure u p t r) =
      (fun i : Fin n => if h : (i : ℕ) = 0 then p i else
          p i - p ⟨i - 1, by omega⟩ * (t (i - 1) * u i / u ⟨i - 1, by omega⟩) * r (i - 1),
        fun k => if h : k < n - 1 then t k * u ⟨k + 1, by omega⟩ / u ⟨k, by omega⟩ else 0) := by
    simp only [algorithm_12_2_1, Id.run_bind, Id.run_pure]
    rw [idRun_vecLoopOn _ (List.nodup_reverse.2 (List.nodup_finRange _))
      (fun i => List.mem_reverse.2 (List.mem_finRange i))]
    simp only [algorithm_12_2_1Step, Id.run_bind, Id.run_pure]
    ext i
    · dsimp only
      split_ifs with h
      · rfl
      · have : (⟨(i : ℕ) - 1 + 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
        simp only [this, mul_assoc]
    · rfl
  have hτ : ∀ k (h : k + 1 < n), (Id.run (algorithm_12_2_1 pure u p t r)).2 k =
      t k * u ⟨k + 1, h⟩ / u ⟨k, by omega⟩ := fun k h => by
    rw [hrun]
    simp [show k < n - 1 by omega]
  have hp : ∀ k (h : k + 1 < n), (Id.run (algorithm_12_2_1 pure u p t r)).1 ⟨k + 1, h⟩ =
      p ⟨k + 1, h⟩ - p ⟨k, by omega⟩ * (Id.run (algorithm_12_2_1 pure u p t r)).2 k * r k :=
    fun k h => by
      rw [hτ k h, hrun]
      simp
  have hp₀ : ∀ h : 0 < n, (Id.run (algorithm_12_2_1 pure u p t r)).1 ⟨0, h⟩ = p ⟨0, h⟩ :=
    fun h => by rw [hrun]; simp
  refine ⟨isLU_quasiseparableOf u v p q _ t r _ huv (fun k h => ?_) hp₀ hp, hτ, hp₀, hp⟩
  rw [hτ k h, div_mul_cancel₀ _ (hu ⟨k, by omega⟩ h)]

end LU

/-! ### The Givens-vector representation and QR (§12.2.6–12.2.7) -/

/-- **(12.2.11)**, the Givens-vector representation: a lower triangular semiseparable `A_L` with
`(A_L)_{n1} ≠ 0` equals `B(s)⁻ᵀ .* tril(c vᵀ)`: `(A_L)_{ij} = c_i s_j ⋯ s_{i−1} v_j` for `j ≤ i`,
with `c = [c₁, …, c_{n−1}, 1]` and `(c_k, s_k)` cosine–sine pairs, `s_k ≠ 0`. The hypothesis
`(A_L)_{n1} ≠ 0` is what the book's "it is not hard to show" needs (with a zero first column the
form forces `A_L` diagonal). -/
theorem equation_12_2_11 {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hA : A.IsSemiseparable) (hL : A.IsLowerTriangular) (h0 : A (Fin.last m) 0 ≠ 0) :
    ∃ c s : ℕ → ℝ, (∀ k, c k ^ 2 + s k ^ 2 = 1) ∧ (∀ k, s k ≠ 0) ∧ ∃ v : Fin (m + 1) → ℝ,
      ∀ i j, A i j =
        if j ≤ i then ((if (i : ℕ) = m then 1 else c i) * ∏ l ∈ Finset.Ico (j : ℕ) i, s l) * v j
        else 0 :=
  exists_givensVector_rep hA hL h0

/-- **(12.2.14)** and the sentences after it: with `Qᵀ = G₁ ⋯ G_{n−1}` built from the Givens-vector
representation of `tril(A)`, `Qᵀ tril(A) = triu((𝒟_n c) vᵀ) .* B(s)⁻¹`, `Qᵀ` is upper Hessenberg and
`Qᵀ triu(A, 1)` is upper triangular, so `Qᵀ A = R` is upper triangular (a QR factorization,
P12.2.9). -/
theorem equation_12_2_14 {N : ℕ} {c s : ℕ → ℝ} (hcs : ∀ k, c k ^ 2 + s k ^ 2 = 1)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {v : Fin (N + 1) → ℝ}
    (hA : ∀ i j : Fin (N + 1), j ≤ i →
      A i j = ((if (i : ℕ) = N then 1 else c i) * ∏ l ∈ Finset.Ico (j : ℕ) i, s l) * v j) :
    (givensChain N fun k => !![c k, s k; -s k, c k]) * (A.strictLower + A.diagPart) =
        vecMulVec (fun i : Fin (N + 1) => if (i : ℕ) = 0 then 1 else c ((i : ℕ) - 1)) v ⊙
          (unitBidiagonal (N + 1) s)⁻¹ ∧
      (givensChain N fun k => !![c k, s k; -s k, c k]).IsUpperHessenberg ∧
      ((givensChain N fun k => !![c k, s k; -s k, c k]) * A.strictUpper).IsUpperTriangular ∧
      ((givensChain N fun k => !![c k, s k; -s k, c k]) * A).IsUpperTriangular := by
  obtain ⟨h1, h2⟩ := transpose_givensChain_mul_strictLower_add_diagPart hcs hA
  refine ⟨h1, givensChain_isUpperHessenberg, h2, ?_⟩
  have hsplit : A = (A.strictLower + A.diagPart) + A.strictUpper := by
    ext i j
    simp only [Matrix.add_apply, strictLower, strictUpper, diagPart, of_apply, diagonal_apply,
      diag_apply]
    rcases lt_trichotomy j i with h | rfl | h
    · simp [h, h.ne', not_lt.2 h.le]
    · simp
    · simp [h, h.ne, not_lt.2 h.le]
  rw [hsplit, Matrix.mul_add, h1]
  intro i j hij
  have hij' : j < i := hij
  rw [Matrix.add_apply, h2 hij, add_zero, hadamard_apply, inv_unitBidiagonal, of_apply,
    ite_eq_right (not_le.2 hij'), mul_zero]

/-! ### Banded inverses (§12.2.8) -/

/-- **§12.2.8**: a nonsingular `{p, q}`-generator representable matrix (`tril(A, p−1) = tril(U Vᵀ,
p−1)`, `triu(A, −q+1) = triu(P Qᵀ, −q+1)`, `U, V ∈ ℝ^{n×p}`, `P, Q ∈ ℝ^{n×q}`) has an inverse of
lower bandwidth `p` and upper bandwidth `q`. -/
theorem inv_banded_of_generatorRepresentable {A : Matrix (Fin n) (Fin n) ℝ} {p q : ℕ}
    (h : A.IsGeneratorRepresentableOfOrder p q) (hA : IsUnit A) :
    A⁻¹.HasLowerBandwidth p ∧ A⁻¹.HasUpperBandwidth q :=
  h.hasBandwidth_inv hA

/-! ### The orthogonal Hessenberg eigenproblem (§12.2.10) -/

/-- **(12.2.18)**: an orthogonal upper Hessenberg `H` with positive subdiagonal, `det H = 1` and
even order (the cases the text deflates away) is `G₁ ⋯ G_{n−1} G_n` with the reflections `G_k =
G(φ_k)`, `0 < φ_k < π`, in the planes `(k, k+1)` and `G_n = diag(1, …, 1, −1)`. The book assumes a
nonzero subdiagonal; positivity is reached by a diagonal `±1` similarity. -/
theorem equation_12_2_18 {N : ℕ} {H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hH : H ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hHess : H.IsUpperHessenberg)
    (hsub : ∀ i : Fin N, 0 < H i.succ i.castSucc) (hdet : H.det = 1) (heven : Even (N + 1)) :
    ∃ φ : ℕ → ℝ, (∀ k < N, 0 < φ k ∧ φ k < Real.pi) ∧
      H = givensChain N (fun k => planeReflector (φ k)) *
        diagonal fun i : Fin (N + 1) => if (i : ℕ) = N then -1 else 1 :=
  exists_orthogonalHessenberg_eq_prod_planeReflector hH hHess hsub hdet heven

/-- **(12.2.19)**: the eigenvalues of an orthogonal upper Hessenberg `H ∈ ℝ^{2m×2m}` with `det H =
1` are `cos θ_k ± i sin θ_k = e^{± iθ_k}`, `k = 1 : m` — `m` conjugate pairs on the unit circle — as
the characteristic polynomial of `H` over `ℂ`. (The Hessenberg structure plays no role.) -/
theorem equation_12_2_19 {m : ℕ} {H : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    (hH : H ∈ orthogonalGroup (Fin (2 * m)) ℝ) (_hHess : H.IsUpperHessenberg) (hdet : H.det = 1) :
    ∃ θ : Fin m → ℝ, (H.map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (Complex.exp (θ k * Complex.I))) *
        (Polynomial.X - Polynomial.C (Complex.exp (-θ k * Complex.I))) :=
  exists_charpoly_eq_prod_of_mem_specialOrthogonalGroup
    (mem_specialOrthogonalGroup_iff.2 ⟨hH, hdet⟩)

/-- **§12.2.10**: "(12.2.4) and (12.2.18) tell us that `H` is quasiseparable": every orthogonal
upper Hessenberg matrix is quasiseparable. -/
theorem orthogonalHessenberg_isQuasiseparable {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H ∈ orthogonalGroup (Fin n) ℝ) (hHess : H.IsUpperHessenberg) : H.IsQuasiseparable :=
  Matrix.orthogonalHessenberg_isQuasiseparable hH hHess

/-- **Fact 1 of §12.2.10**: `H = G₁ ⋯ G_n` is similar to `H̃ = H_o H_e` with
`H_o = G₁ G₃ ⋯ G_{n−1} = diag(R(φ₁), R(φ₃), …)` and `H_e = G₂ G₄ ⋯ G_n = diag(1, R(φ₂), …,
R(φ_{n−2}), −1)` (0-based, the even-indexed and odd-indexed factors of `Matrix.reflectorFactor`). -/
theorem orthogonalHessenberg_fact_1 {N : ℕ} (φ : ℕ → ℝ) :
    (prodFwd (reflectorFactor N φ) (N + 1)).IsSimilar
      (prodFwdEven (reflectorFactor N φ) (N + 1) * prodFwdOdd (reflectorFactor N φ) (N + 1)) :=
  isSimilar_prod_planeReflector_oddEven φ

/-- **Fact 2 of §12.2.10**: for `H = G₁ ⋯ G_n` of (12.2.18) of order `n = 2m` with eigenvalues
`e^{± iθ_k}` (12.2.19), `C = (H_o + H_e)/2` and `S = (H_o − H_e)/2` are symmetric tridiagonal with
`λ(C) = {± cos(θ_k/2)}` and `λ(S) = {± sin(θ_k/2)}`. The angles `θ` exist by (12.2.19), `H` being
special orthogonal. -/
theorem orthogonalHessenberg_fact_2 {N m : ℕ} (hNm : N + 1 = 2 * m) (φ : ℕ → ℝ)
    (hH : prodFwd (reflectorFactor N φ) (N + 1) ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hdet : (prodFwd (reflectorFactor N φ) (N + 1)).det = 1) :
    ∃ θ : Fin m → ℝ,
      ((prodFwd (reflectorFactor N φ) (N + 1)).map (algebraMap ℝ ℂ)).charpoly =
        ∏ k, (Polynomial.X - Polynomial.C (Complex.exp (θ k * Complex.I))) *
          (Polynomial.X - Polynomial.C (Complex.exp (-θ k * Complex.I))) ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) +
          prodFwdOdd (reflectorFactor N φ) (N + 1))).IsSymm ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) +
          prodFwdOdd (reflectorFactor N φ) (N + 1))).IsTridiagonal ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) +
          prodFwdOdd (reflectorFactor N φ) (N + 1))).charpoly =
        ∏ k, (Polynomial.X - Polynomial.C (Real.cos (θ k / 2))) *
          (Polynomial.X + Polynomial.C (Real.cos (θ k / 2))) ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) -
          prodFwdOdd (reflectorFactor N φ) (N + 1))).IsSymm ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) -
          prodFwdOdd (reflectorFactor N φ) (N + 1))).IsTridiagonal ∧
      ((1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) -
          prodFwdOdd (reflectorFactor N φ) (N + 1))).charpoly =
        ∏ k, (Polynomial.X - Polynomial.C (Real.sin (θ k / 2))) *
          (Polynomial.X + Polynomial.C (Real.sin (θ k / 2))) := by
  set H := prodFwd (reflectorFactor N φ) (N + 1)
  set e : Fin (N + 1) ≃ Fin (2 * m) := finCongr hNm
  have hH' : H.reindex e e ∈ specialOrthogonalGroup (Fin (2 * m)) ℝ := by
    refine mem_specialOrthogonalGroup_iff.2 ⟨?_, by rw [det_reindex_self, hdet]⟩
    rw [mem_orthogonalGroup_iff] at hH ⊢
    rw [reindex_apply, transpose_submatrix, submatrix_mul_equiv, hH, submatrix_one_equiv]
  obtain ⟨θ, hθ⟩ := exists_charpoly_eq_prod_of_mem_specialOrthogonalGroup hH'
  have hθ' : (H.map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (Complex.exp (θ k * Complex.I))) *
        (Polynomial.X - Polynomial.C (Complex.exp (-θ k * Complex.I))) := by
    rw [← hθ, ← charpoly_reindex e (H.map (algebraMap ℝ ℂ))]
    rfl
  obtain ⟨hC1, hC2, hS1, hS2⟩ := isTridiagonal_oddEven_half_sum (N := N) φ
  obtain ⟨hC3, hS3⟩ := charpoly_oddEven_half_sum φ θ hθ'
  exact ⟨θ, hθ', hC1, hC2, hC3, hS1, hS2, hS3⟩

end GolubVanLoan.Chapter12
