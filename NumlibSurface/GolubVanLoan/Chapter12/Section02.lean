import Numlib.LinearAlgebra.Matrix.Semiseparable
import Numlib.LinearAlgebra.Matrix.RealSchur
import NumlibSurface.GolubVanLoan.Chapter05.Section01
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
coordinate planes is `Matrix.givensChain`. Algorithm 12.2.2 follows the algorithm conventions of
`NumlibSurface/GolubVanLoan`: its Givens pairs are chapter 5's Algorithm 5.1.3, its state the
structure `SemiseparableQRState`, and its exact specification is a downward induction on the book's
`A⁽ᵏ⁾`.

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

/-! #### Algorithm 12.2.2 -/

/-- The state of Algorithm 12.2.2 before the step `k` (0-based): `ũ_{k+1}`, `f̃_{k+1}` and the
arrays `c`, `s`, `f`, `g`, `h` (the entry `h_{k+1}` holding the book's `h̃_{k+1}`). -/
structure SemiseparableQRState (N : ℕ) where
  /-- The book's `ũ`. -/
  ut : ℝ
  /-- The book's `f̃`. -/
  ft : ℝ
  /-- The cosines `c_k`. -/
  c : ℕ → ℝ
  /-- The sines `s_k`. -/
  s : ℕ → ℝ
  /-- The vector `f`. -/
  f : Fin (N + 1) → ℝ
  /-- The vector `g`. -/
  g : Fin (N + 1) → ℝ
  /-- The vector `h`. -/
  h : Fin (N + 1) → ℝ

section QR

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {N : ℕ}

/-- One step of Algorithm 12.2.2 (0-based `k`, the book's `k + 1`): "Determine `c_k` and `s_k`
so that `[c_k s_k; −s_k c_k] [u_k; ũ_{k+1}] = [ũ_k; 0]`; `f̃_k = s_k f̃_{k+1}`,
`f_{k+1} = c_k f̃_{k+1}`; `[h_k; h_{k+1}] = [c_k s_k; −s_k c_k] [p_k; h_{k+1}]`;
`g_k = (ũ_k v_k − h_k q_k)/f̃_k`". The pair is chapter 5's Algorithm 5.1.3 on `(u_k, ũ_{k+1})`,
whose rotation is the transpose of the book's here (so `s_k` is its sine negated, exactly); `ũ_k`
is the rotated first entry; `g_k` uses `ũ_k`, as the derivation does (the book's display prints
`u_k`). Every product, sum and quotient is rounded. -/
noncomputable def algorithm_12_2_2Step (u v p q : Fin (N + 1) → ℝ) (st : SemiseparableQRState N)
    (k : Fin N) : M (SemiseparableQRState N) := do
  let cs ← Chapter05.algorithm_5_1_3 rnd (u k.castSucc) st.ut
  let cc := cs.1
  let ss := -cs.2
  let ut ← rnd ((← rnd (cc * u k.castSucc)) + (← rnd (ss * st.ut)))
  let ft ← rnd (ss * st.ft)
  let fk ← rnd (cc * st.ft)
  let hk ← rnd ((← rnd (cc * p k.castSucc)) + (← rnd (ss * st.h k.succ)))
  let hk' ← rnd ((← rnd (cc * st.h k.succ)) - (← rnd (ss * p k.castSucc)))
  let gk ← rnd ((← rnd ((← rnd (ut * v k.castSucc)) - (← rnd (hk * q k.castSucc)))) / ft)
  pure
    { ut := ut
      ft := ft
      c := Function.update st.c k cc
      s := Function.update st.s k ss
      f := Function.update st.f k.succ fk
      g := Function.update st.g k.castSucc gk
      h := Function.update (Function.update st.h k.succ hk') k.castSucc hk }

/-- **Algorithm 12.2.2.** "Suppose `u`, `v`, `p` and `q` are `n`-vectors that satisfy `u .* v =
p .* q` and `u_n ≠ 0`. If `A = tril(u vᵀ) + triu(p qᵀ, 1)`, then this algorithm computes cosine-sine
pairs `{c₁, s₁}, …, {c_{n−1}, s_{n−1}}` and vectors `f, g, h ∈ ℝⁿ` so that if `Q` is defined by
(12.2.12) and (12.2.13), then `QᵀA = R = triu(f gᵀ + h qᵀ)`":
```
ũ_n = u_n, f̃_n = u_n, g_n = v_n, h_n = 0
for k = n − 1 : −1 : 1
    (the step algorithm_12_2_2Step)
end
f₁ = f̃₁
```
On `Fin (N + 1)` (`n = N + 1`), 0-based; it returns `(c, s, f, g, h)`, the pairs `ℕ`-indexed for
`Matrix.givensChain`. -/
noncomputable def algorithm_12_2_2 (u v p q : Fin (N + 1) → ℝ) :
    M ((ℕ → ℝ) × (ℕ → ℝ) × (Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) := do
  let st ← (List.finRange N).reverse.foldlM (algorithm_12_2_2Step rnd u v p q)
    { ut := u (Fin.last N), ft := u (Fin.last N), c := 0, s := 0, f := 0,
      g := Function.update 0 (Fin.last N) (v (Fin.last N)), h := 0 }
  pure (st.c, st.s, Function.update st.f 0 st.ft, st.g, st.h)

end QR

/-- A fold satisfies a property of the processed prefix, if every step does. -/
private theorem foldl_prefix_induction {α β : Type*} (f : β → α → β) (l : List α)
    (P : List α → β → Prop) {b : β} (h0 : P [] b)
    (hs : ∀ p a q s, l = p ++ a :: q → P p s → P (p ++ [a]) (f s a)) : P l (l.foldl f b) := by
  suffices h : ∀ q p s, l = p ++ q → P p s → P l (q.foldl f s) from h l [] b rfl h0
  intro q
  induction q with
  | nil => intro p s hl hp; simpa [hl] using hp
  | cons a q ih =>
    intro p s hl hp
    exact ih (p ++ [a]) (f s a) (by simp [hl]) (hs p a q s hl hp)

/-- A forward product peels off its first factor. -/
private theorem prodFwd_succ_left {n : ℕ} (f : ℕ → Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    prodFwd f (m + 1) = f 0 * prodFwd (fun k => f (k + 1)) m := by
  induction m with
  | zero => simp [prodFwd_succ]
  | succ m ih => rw [prodFwd_succ, ih, prodFwd_succ, Matrix.mul_assoc]

/-- A forward product only reads its first `m` factors. -/
private theorem prodFwd_congr' {n : ℕ} {f f' : ℕ → Matrix (Fin n) (Fin n) ℝ} {m : ℕ}
    (h : ∀ k < m, f k = f' k) : prodFwd f m = prodFwd f' m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [prodFwd_succ, prodFwd_succ, ih fun k hk => h k (by omega), h m (by omega)]

/-- The rotation block of Algorithm 12.2.2, `[c s; −s c]`. -/
private abbrev rotBlock (c s : ℕ → ℝ) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![c k, s k; -s k, c k]

/-- The matrix `A⁽ᵗ⁾ = G_t ⋯ G_{n−1} A` of the book's derivation, from the state before step
`t − 1`: rows above `t` are those of `A`; row `t` is `ũ_t v_j` left of the diagonal and
`f̃_t g_j + h̃_t q_j` from it on; rows below `t` are `triu(f gᵀ + h qᵀ)`. -/
private def stage {N : ℕ} (u v p q : Fin (N + 1) → ℝ) (t : ℕ) (st : SemiseparableQRState N) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  of fun i j => if (i : ℕ) < t then (if j ≤ i then u i * v j else p i * q j)
    else if (i : ℕ) = t then (if (j : ℕ) < t then st.ut * v j else st.ft * st.g j + st.h i * q j)
    else if j < i then 0 else st.f i * st.g j + st.h i * q j

/-- One rotation of the derivation: `G_k A⁽ᵏ⁺¹⁾ = A⁽ᵏ⁾`, for a pair `(c, s)` that annihilates
`ũ_{k+1}` (`−s u_k + c ũ_{k+1} = 0`) and a nonzero `f̃_k = s f̃_{k+1}`. -/
private theorem stage_step {N : ℕ} (u v p q : Fin (N + 1) → ℝ) (st : SemiseparableQRState N)
    (a : Fin N) {c s : ℝ} {c' s' : ℕ → ℝ} (hz : -s * u a.castSucc + c * st.ut = 0)
    (hft : s * st.ft ≠ 0) :
    planeEmbed a.castSucc a.succ !![c, s; -s, c] * stage u v p q ((a : ℕ) + 1) st =
      stage u v p q (a : ℕ)
        { ut := c * u a.castSucc + s * st.ut, ft := s * st.ft, c := c', s := s',
          f := Function.update st.f a.succ (c * st.ft),
          g := Function.update st.g a.castSucc
            (((c * u a.castSucc + s * st.ut) * v a.castSucc -
              (c * p a.castSucc + s * st.h a.succ) * q a.castSucc) / (s * st.ft)),
          h := Function.update (Function.update st.h a.succ (c * st.h a.succ - s * p a.castSucc))
            a.castSucc (c * p a.castSucc + s * st.h a.succ) } := by
  have hne : a.castSucc ≠ a.succ := a.castSucc_lt_succ.ne
  ext i j
  rw [planeEmbed_mul_apply _ hne]
  simp only [stage, of_apply, Function.update_apply, Fin.ext_iff, Fin.le_def, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  split_ifs <;> first
    | (exfalso; omega)
    | ring1
    | skip
  · have hj : j = a.castSucc := Fin.ext (by assumption)
    subst hj
    have hs : s ≠ 0 := left_ne_zero_of_mul hft
    have hf : st.ft ≠ 0 := right_ne_zero_of_mul hft
    field_simp
    ring
  · linear_combination (v j) * hz

/-- A `givensFactor` only reads its own block. -/
private theorem givensFactor_congr {N : ℕ} {M M' : ℕ → Matrix (Fin 2) (Fin 2) ℝ} {k : ℕ}
    (h : M k = M' k) : givensFactor N M k = givensFactor N M' k := by
  simp only [givensFactor, h]

/-- The factor `G_k` of the chain, `k < N`, is the block in the plane `(k, k + 1)`. -/
private theorem givensFactor_of_lt {N : ℕ} (M : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (a : Fin N) :
    givensFactor N M a = planeEmbed a.castSucc a.succ (M a) := by
  rw [givensFactor, dite_eq_left_of_eq_true (eq_true a.isLt)]
  rfl

/-- **Correctness of Algorithm 12.2.2**: if `u_n ≠ 0` and `A = tril(u vᵀ) + triu(p qᵀ, 1)`, the
exact run `(c, s, f, g, h)` gives an orthogonal `Qᵀ = G₁ ⋯ G_{n−1}` ((12.2.12)–(12.2.13), the
`Matrix.givensChain` of the blocks `[c_k s_k; −s_k c_k]`) with `QᵀA = R = triu(f gᵀ + h qᵀ)`, and
"the `s_k` are nonzero because `|ũ_k| = ‖u(k:n)‖₂ ≠ 0`", so that every division `/ f̃_k` of the
algorithm is by `f̃_k = s_k ⋯ s_{n−1} u_n ≠ 0`. The hypothesis `u .* v = p .* q` is not needed.
Downward induction on the book's `A⁽ᵏ⁾ = G_k ⋯ G_{n−1} A`, one rotation per step
(`stage_step`). -/
theorem algorithm_12_2_2_spec {N : ℕ} (u v p q : Fin (N + 1) → ℝ) (hu : u (Fin.last N) ≠ 0) :
    givensChain N (fun k => !![(Id.run (algorithm_12_2_2 pure u v p q)).1 k,
        (Id.run (algorithm_12_2_2 pure u v p q)).2.1 k;
        -(Id.run (algorithm_12_2_2 pure u v p q)).2.1 k,
        (Id.run (algorithm_12_2_2 pure u v p q)).1 k]) ∈ orthogonalGroup (Fin (N + 1)) ℝ ∧
      givensChain N (fun k => !![(Id.run (algorithm_12_2_2 pure u v p q)).1 k,
          (Id.run (algorithm_12_2_2 pure u v p q)).2.1 k;
          -(Id.run (algorithm_12_2_2 pure u v p q)).2.1 k,
          (Id.run (algorithm_12_2_2 pure u v p q)).1 k]) *
          (of fun i j => if j ≤ i then u i * v j else p i * q j) =
        (of fun i j => if i ≤ j then
          (Id.run (algorithm_12_2_2 pure u v p q)).2.2.1 i *
            (Id.run (algorithm_12_2_2 pure u v p q)).2.2.2.1 j +
          (Id.run (algorithm_12_2_2 pure u v p q)).2.2.2.2 i * q j else 0) ∧
      ∀ k < N, (Id.run (algorithm_12_2_2 pure u v p q)).2.1 k ≠ 0 := by
  set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    of fun i j => if j ≤ i then u i * v j else p i * q j with hA
  let st₀ : SemiseparableQRState N :=
    { ut := u (Fin.last N)
      ft := u (Fin.last N)
      c := 0
      s := 0
      f := 0
      g := Function.update 0 (Fin.last N) (v (Fin.last N))
      h := 0 }
  -- the exact step
  have hstep : ∀ (st : SemiseparableQRState N) (a : Fin N),
      Id.run (algorithm_12_2_2Step pure u v p q st a) =
        { ut := (Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * u a.castSucc +
            -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 * st.ut
          ft := -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 * st.ft
          c := Function.update st.c a
            (Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1
          s := Function.update st.s a
            (-(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2)
          f := Function.update st.f a.succ
            ((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * st.ft)
          g := Function.update st.g a.castSucc
            ((((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * u a.castSucc +
              -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 * st.ut) *
                v a.castSucc -
              ((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * p a.castSucc +
                -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 *
                  st.h a.succ) * q a.castSucc) /
              (-(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 * st.ft))
          h := Function.update (Function.update st.h a.succ
              ((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * st.h a.succ -
                -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 *
                  p a.castSucc)) a.castSucc
            ((Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).1 * p a.castSucc +
              -(Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut)).2 *
                st.h a.succ) } :=
    fun _ _ => rfl
  -- the invariant after the steps `N − 1, …, t`
  let Inv : ℕ → SemiseparableQRState N → Prop := fun t st =>
    t ≤ N ∧ prodFwd (fun k => givensFactor N (rotBlock st.c st.s) (t + k)) (N - t) * A =
      stage u v p q t st ∧ st.ut ≠ 0 ∧ st.ft ≠ 0 ∧
      ∀ k, t ≤ k → k < N → st.c k ^ 2 + st.s k ^ 2 = 1 ∧ st.s k ≠ 0
  have hfin := foldl_prefix_induction (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k))
    (List.finRange N).reverse (fun pre st => Inv (N - pre.length) st) (b := st₀) ?h0 ?hs
  case h0 =>
    refine ⟨Nat.sub_le _ _, ?_, hu, hu, fun k hk hk' => absurd hk' (by simp at hk; omega)⟩
    simp only [List.length_nil, Nat.sub_zero, Nat.sub_self, prodFwd_zero, Matrix.one_mul]
    ext i j
    simp only [stage, hA, of_apply]
    by_cases hiN : (i : ℕ) < N
    · rw [ite_eq_left hiN]
    · have hiL : i = Fin.last N := Fin.ext (by simp; omega)
      subst hiL
      rw [ite_eq_right hiN, ite_eq_left (Fin.val_last N)]
      by_cases hj : (j : ℕ) < N
      · rw [ite_eq_left hj, ite_eq_left (Fin.le_last j)]
      · have hjL : j = Fin.last N := Fin.ext (by simp; omega)
        subst hjL
        simp [st₀]
  case hs =>
    intro pre a rest st hl hInv
    have hlen : pre.length < N := by
      have := congrArg List.length hl
      simp at this
      omega
    have ha : (a : ℕ) = N - 1 - pre.length := by
      have h1 : (List.finRange N).reverse[pre.length]'(by simpa using hlen) = a := by
        simp [hl]
      rw [List.getElem_reverse, List.getElem_finRange] at h1
      rw [← h1]
      simp
    obtain ⟨-, hprod, hut, hft, hcs⟩ := hInv
    rw [show N - pre.length = (a : ℕ) + 1 by omega] at hprod hcs
    simp only [List.length_append, List.length_singleton,
      show N - (pre.length + 1) = (a : ℕ) by omega]
    obtain ⟨hcs1, hcs2, hcs3⟩ := Chapter05.algorithm_5_1_3_spec (u a.castSucc) st.ut
    set cs := Id.run (Chapter05.algorithm_5_1_3 pure (u a.castSucc) st.ut) with hcsdef
    have hs0 : cs.2 ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_add] at hcs2
      have hc : cs.1 ≠ 0 := by
        intro hc
        rw [hc, h0] at hcs1
        norm_num at hcs1
      exact hut ((mul_eq_zero.1 hcs2).resolve_left hc)
    rw [hstep]
    refine ⟨by omega, ?_, ?_, mul_ne_zero (neg_ne_zero.2 hs0) hft, fun k hk hk' => ?_⟩
    · rw [show N - (a : ℕ) = (N - ((a : ℕ) + 1)) + 1 by omega, prodFwd_succ_left,
        Matrix.mul_assoc]
      have htail : prodFwd (fun k => givensFactor N (rotBlock (Function.update st.c a cs.1)
          (Function.update st.s a (-cs.2))) ((a : ℕ) + (k + 1))) (N - ((a : ℕ) + 1)) =
          prodFwd (fun k => givensFactor N (rotBlock st.c st.s) ((a : ℕ) + 1 + k))
            (N - ((a : ℕ) + 1)) := by
        refine prodFwd_congr' fun k _ => ?_
        rw [show (a : ℕ) + (k + 1) = (a : ℕ) + 1 + k by omega]
        refine givensFactor_congr ?_
        have hne : (a : ℕ) + 1 + k ≠ (a : ℕ) := by omega
        simp only [rotBlock, Function.update_of_ne hne]
      rw [htail, hprod, add_zero, givensFactor_of_lt]
      simp only [rotBlock, Function.update_self]
      exact stage_step u v p q st a (by rw [neg_neg]; linarith)
        (mul_ne_zero (neg_ne_zero.2 hs0) hft)
    · -- `|ũ_k| = √(u_k² + ũ_{k+1}²) > 0`
      intro h0
      have h2 : cs.1 * u a.castSucc - cs.2 * st.ut = 0 := by linarith
      rw [h2, abs_zero] at hcs3
      have := (Real.sqrt_eq_zero (by positivity)).1 hcs3.symm
      exact hut (by nlinarith [sq_nonneg (u a.castSucc), sq_nonneg st.ut])
    · rcases eq_or_lt_of_le hk with hk | hk
      · subst hk
        simp only [Function.update_self]
        exact ⟨by rw [neg_sq]; exact hcs1, neg_ne_zero.2 hs0⟩
      · have hne : k ≠ (a : ℕ) := by omega
        simp only [Function.update_of_ne hne]
        exact hcs k (by omega) hk'
  -- read off the final state
  obtain ⟨-, hprod, -, -, hcs⟩ := hfin
  simp only [List.length_reverse, List.length_finRange, Nat.sub_self, zero_add,
    Nat.sub_zero] at hprod hcs
  have hrun : Id.run (algorithm_12_2_2 pure u v p q) =
      (((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).c,
        ((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).s,
        Function.update ((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).f 0
          ((List.finRange N).reverse.foldl
            (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).ft,
        ((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).g,
        ((List.finRange N).reverse.foldl
          (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀).h) := by
    rw [algorithm_12_2_2, Id.run_bind, List.idRun_foldlM, Id.run_pure]
  rw [hrun]
  generalize (List.finRange N).reverse.foldl
    (fun st k => Id.run (algorithm_12_2_2Step pure u v p q st k)) st₀ = st at hprod hcs ⊢
  refine ⟨prodFwd_mem_orthogonalGroup (fun k => ?_) N, ?_, fun k hk => (hcs k (Nat.zero_le _) hk).2⟩
  · by_cases hk : k < N
    · rw [givensFactor, dite_eq_left_of_eq_true (eq_true hk)]
      have h := planeRotation_mem_orthogonalGroup (j := (⟨k, by omega⟩ : Fin (N + 1)))
        (k := ⟨k + 1, by omega⟩) (Fin.ne_of_lt (Fin.mk_lt_mk.2 (Nat.lt_succ_self k)))
        (c := st.c k) (s := -st.s k) (by rw [neg_sq]; exact (hcs k (Nat.zero_le _) hk).1)
      rw [planeRotation, neg_neg] at h
      exact h
    · rw [givensFactor, dite_eq_right_of_eq_false (eq_false hk)]
      exact one_mem _
  · change prodFwd (fun k => givensFactor N (rotBlock st.c st.s) k) N * A = _
    rw [hprod]
    ext i j
    simp only [stage, of_apply, Nat.not_lt_zero, ↓reduceIte, Function.update_apply]
    by_cases hi : (i : ℕ) = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst hi0
      simp
    · rw [ite_eq_right hi, ite_eq_right (fun h : i = 0 => hi (by rw [h]; rfl))]
      by_cases hji : j < i
      · rw [ite_eq_left hji, ite_eq_right (not_le.2 hji)]
      · rw [ite_eq_right hji, ite_eq_left (not_lt.1 hji)]

/-- **(12.2.16)**: for `A = tril(u vᵀ) + triu(p qᵀ, 1)` (the generator representation
(12.2.15)) with `u_n ≠ 0`, "`R` is the upper triangular portion of a rank-2 matrix, i.e.,
`R = triu(f gᵀ + h qᵀ)`, `f, g, h ∈ ℝⁿ`": some orthogonal `Qᵀ` has `QᵀA = triu(f gᵀ + h qᵀ)` —
the one of Algorithm 12.2.2 (`algorithm_12_2_2_spec`). -/
theorem equation_12_2_16 {N : ℕ} (u v p q : Fin (N + 1) → ℝ) (hu : u (Fin.last N) ≠ 0) :
    ∃ Qt ∈ orthogonalGroup (Fin (N + 1)) ℝ, ∃ f g h : Fin (N + 1) → ℝ,
      Qt * (of fun i j => if j ≤ i then u i * v j else p i * q j) =
        of fun i j => if i ≤ j then f i * g j + h i * q j else 0 := by
  obtain ⟨h1, h2, -⟩ := algorithm_12_2_2_spec u v p q hu
  exact ⟨_, h1, _, _, _, h2⟩

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
