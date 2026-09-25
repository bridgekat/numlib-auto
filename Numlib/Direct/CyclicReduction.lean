import Numlib.LinearAlgebra.Matrix.BlockTridiagonal

/-!
# Block cyclic reduction

Block cyclic reduction ([golub2013matrix] §4.5.3; Buzbee, Golub and Nielson 1970) solves the block
tridiagonal system with constant commuting blocks ((4.5.9))
`D x₁ + F x₂ = b₁`, `F x_{i−1} + D x_i + F x_{i+1} = b_i`, `F x_{N−1} + D x_N = b_N`, `D F = F D`
(the discrete Poisson matrix of §4.8.4 is the case `D = 𝒯^{(DD)} + 2I`, `F = −I`).

One reduction step eliminates every other unknown: multiplying three consecutive equations by
`F`, `−D`, `F` and adding leaves a system of the same shape for the unknowns `x₁, x₃, …`
(0-based) with blocks `D⁽¹⁾ = 2F² − D²`, `F⁽¹⁾ = F²`, which commute again
(`CyclicReduction.constBlockTridiagonal_reduce`, `CyclicReduction.commute_reduced`); the eliminated
unknowns are recovered from `q × q` systems with matrix `D`
(`CyclicReduction.constBlockTridiagonal_odd_eq`). For `N = 2^k − 1` unknowns
(`CyclicReduction.size k`) the reduction can be iterated down to a single `q × q` system for the
middle unknown (`CyclicReduction.constBlockTridiagonal_iterate_reduce`).

## Design

The operator is written directly on block vectors `x : Fin N → Fin q → K`, with the missing
neighbours of the first and last unknown read as zero through the zero extension
`CyclicReduction.extend x : ℤ → Fin q → K`, so that no boundary case is special. It is the block
tridiagonal matrix `Matrix.blockTridiagonal` of `Numlib.LinearAlgebra.Matrix.BlockTridiagonal`
applied to the flattened vector
(`CyclicReduction.constBlockTridiagonal_eq_blockTridiagonal_mulVec`).
The sizes `2^k − 1` are the recursion `size (k + 1) = 2 size k + 1`, so that one reduction step
maps a system of size `size (k + 1)` to one of size `size k` with no cast.

The stabilized variant of Buneman and the operation counts are not formalized.

## References

* [golub2013matrix] §4.5.3.
-/

open Matrix

namespace CyclicReduction

variable {K : Type*} [CommRing K] {q N M : ℕ}

/-! ### The operator -/

/-- The zero extension of a block vector to all integer indices. -/
def extend (x : Fin N → Fin q → K) (i : ℤ) : Fin q → K :=
  if h : 0 ≤ i ∧ i < N then x ⟨i.toNat, by omega⟩ else 0

/-- The zero extension inside the index range. -/
theorem extend_of_lt (x : Fin N → Fin q → K) {i : ℤ} (h₀ : 0 ≤ i) (h : i < N) :
    extend x i = x ⟨i.toNat, by omega⟩ := dite_eq_left ⟨h₀, h⟩

/-- The zero extension at an index of `Fin N`. -/
@[simp]
theorem extend_coe (x : Fin N → Fin q → K) (i : Fin N) : extend x (i : ℕ) = x i := by
  rw [extend_of_lt x (by omega) (by exact_mod_cast i.isLt)]
  congr

/-- The zero extension vanishes at negative indices. -/
theorem extend_of_neg (x : Fin N → Fin q → K) {i : ℤ} (h : i < 0) : extend x i = 0 :=
  dite_eq_right (by omega)

/-- The zero extension vanishes from index `N` on. -/
theorem extend_of_le (x : Fin N → Fin q → K) {i : ℤ} (h : (N : ℤ) ≤ i) : extend x i = 0 :=
  dite_eq_right (by omega)

/-- The zero extension commutes with a block multiplication. -/
theorem extend_mulVec (A : Matrix (Fin q) (Fin q) K) (x : Fin N → Fin q → K) (i : ℤ) :
    extend (fun j => A *ᵥ x j) i = A *ᵥ extend x i := by
  unfold extend
  split_ifs <;> simp

/-- The constant-block tridiagonal operator of [golub2013matrix] (4.5.9):
`(T x)_i = D x_i + F x_{i−1} + F x_{i+1}`, the missing neighbours at the ends being zero. -/
def constBlockTridiagonal (D F : Matrix (Fin q) (Fin q) K) (x : Fin N → Fin q → K) (i : Fin N) :
    Fin q → K :=
  D *ᵥ x i + F *ᵥ extend x ((i : ℕ) - 1) + F *ᵥ extend x ((i : ℕ) + 1)

/-- The system `T x = b` read on the zero extensions, at every integer index in range. -/
theorem constBlockTridiagonal_eq_iff {D F : Matrix (Fin q) (Fin q) K}
    {x b : Fin N → Fin q → K} :
    constBlockTridiagonal D F x = b ↔ ∀ i : ℤ, 0 ≤ i → i < N →
      D *ᵥ extend x i + F *ᵥ extend x (i - 1) + F *ᵥ extend x (i + 1) = extend b i := by
  constructor
  · rintro rfl i h₀ h
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h₀
    have hn : n < N := by omega
    have := extend_coe (constBlockTridiagonal D F x) ⟨n, hn⟩
    simp only at this
    rw [this, constBlockTridiagonal]
    exact congrArg (fun v => D *ᵥ v + F *ᵥ extend x (n - 1) + F *ᵥ extend x (n + 1))
      (extend_coe x ⟨n, hn⟩)
  · intro h
    funext i
    have := h (i : ℕ) (by omega) (by exact_mod_cast i.isLt)
    rwa [extend_coe, extend_coe] at this

/-- The predecessor sum of a tridiagonal product, read on the zero extension. -/
private theorem sum_ite_succ_eq (v : Fin (N + 1) → Fin q → K) (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1), (if (j : ℕ) + 1 = i then v j else 0) = extend v ((i : ℕ) - 1) := by
  have := sum_dite_val_add_one_eq i (fun j (_ : (j : ℕ) + 1 = i) => v j)
  simp only [dite_eq_ite] at this
  rw [this]
  split_ifs with h
  · rw [extend_of_lt v (by omega) (by omega)]
    congr
    omega
  · rw [extend_of_neg v (by omega)]

/-- The successor sum of a tridiagonal product, read on the zero extension. -/
private theorem sum_ite_eq_succ (v : Fin (N + 1) → Fin q → K) (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1), (if (j : ℕ) = i + 1 then v j else 0) = extend v ((i : ℕ) + 1) := by
  have := sum_dite_val_eq_add_one i (fun j (_ : (j : ℕ) = i + 1) => v j)
  simp only [dite_eq_ite] at this
  rw [this]
  split_ifs with h
  · rw [extend_of_lt v (by omega) (by omega)]
    congr
  · rw [extend_of_le v (by omega)]

/-- **Block tridiagonal form**: `constBlockTridiagonal D F x` is the block tridiagonal matrix with
diagonal blocks `D` and off-diagonal blocks `F`, applied to the flattened `x`. -/
theorem constBlockTridiagonal_eq_blockTridiagonal_mulVec (D F : Matrix (Fin q) (Fin q) K)
    (x : Fin (N + 1) → Fin q → K) (i : Fin (N + 1)) (k : Fin q) :
    (blockTridiagonal (fun _ => F) (fun _ => F) (fun _ => D) *ᵥ fun p => x p.1 p.2) (i, k) =
      constBlockTridiagonal D F x i k := by
  have hsum : (blockTridiagonal (fun _ => F) (fun _ => F) (fun _ => D) *ᵥ
      fun p => x p.1 p.2) (i, k) =
      (∑ j : Fin (N + 1), tridiagonalOf (fun _ : Fin N => F) (fun _ => D) (fun _ => F) i j *ᵥ
        x j) k := by
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, blockTridiagonal_apply,
      Finset.sum_apply]
  have hterm : ∀ j : Fin (N + 1),
      tridiagonalOf (fun _ : Fin N => F) (fun _ => D) (fun _ => F) i j *ᵥ x j =
        (if i = j then D *ᵥ x j else 0) +
        (if (j : ℕ) + 1 = i then F *ᵥ x j else 0) +
        (if (j : ℕ) = i + 1 then F *ᵥ x j else 0) := by
    intro j
    by_cases hij : i = j
    · subst hij
      simp
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp only [tridiagonalOf, of_apply, hij', ite_false, hij]
      split_ifs <;> first | omega | simp
  rw [hsum, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_ite_succ_eq (fun j => F *ᵥ x j),
    sum_ite_eq_succ (fun j => F *ᵥ x j), extend_mulVec, extend_mulVec]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

/-! ### One reduction step -/

/-- The diagonal block after one reduction step, `D⁽¹⁾ = 2F² − D²` ([golub2013matrix] §4.5.3). -/
def reducedDiag (D F : Matrix (Fin q) (Fin q) K) : Matrix (Fin q) (Fin q) K :=
  2 • (F * F) - D * D

/-- The off-diagonal block after one reduction step, `F⁽¹⁾ = F²`. -/
def reducedOff (F : Matrix (Fin q) (Fin q) K) : Matrix (Fin q) (Fin q) K :=
  F * F

/-- The right-hand side after one reduction step (0-based):
`b⁽¹⁾_j = F (b_{2j} + b_{2j+2}) − D b_{2j+1}`. -/
def reducedRhs (D F : Matrix (Fin q) (Fin q) K) (b : Fin (2 * M + 1) → Fin q → K) (j : Fin M) :
    Fin q → K :=
  F *ᵥ (b ⟨2 * j, by omega⟩ + b ⟨2 * j + 2, by omega⟩) - D *ᵥ b ⟨2 * j + 1, by omega⟩

/-- **The reduced blocks commute** ([golub2013matrix] §4.5.3), so the reduction can be
repeated. -/
theorem commute_reduced {D F : Matrix (Fin q) (Fin q) K} (h : D * F = F * D) :
    reducedDiag D F * reducedOff F = reducedOff F * reducedDiag D F := by
  have h' : D * (F * F) = F * F * D := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, h, Matrix.mul_assoc]
  have h'' : D * (D * (F * F)) = F * (F * (D * D)) := by
    rw [h', ← Matrix.mul_assoc, h', Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [reducedDiag, reducedOff, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc]
  rw [h'']

/-- The zero extension of the odd-indexed unknowns (0-based) is read off the zero extension of
the whole vector. -/
theorem extend_odd (x : Fin (2 * M + 1) → Fin q → K) (j : ℤ) :
    extend (fun j : Fin M => x ⟨2 * j + 1, by omega⟩) j = extend x (2 * j + 1) := by
  unfold extend
  split_ifs with h₁ h₂ h₂
  · refine congrArg x (Fin.ext ?_)
    change 2 * j.toNat + 1 = (2 * j + 1).toNat
    omega
  · exfalso; omega
  · exfalso; omega
  · rfl

/-- **One cyclic reduction step** ([golub2013matrix] §4.5.3): if `D F = F D` and
`T x = b` on `2M + 1` unknowns, then the odd-indexed unknowns (0-based) `x' j = x (2j + 1)`
solve the system with blocks `D⁽¹⁾ = 2F² − D²`, `F⁽¹⁾ = F²` and right-hand side
`b⁽¹⁾_j = F (b_{2j} + b_{2j+2}) − D b_{2j+1}`. -/
theorem constBlockTridiagonal_reduce {D F : Matrix (Fin q) (Fin q) K} (hDF : D * F = F * D)
    {x b : Fin (2 * M + 1) → Fin q → K} (h : constBlockTridiagonal D F x = b) :
    constBlockTridiagonal (reducedDiag D F) (reducedOff F)
      (fun j : Fin M => x ⟨2 * j + 1, by omega⟩) = reducedRhs D F b := by
  rw [constBlockTridiagonal_eq_iff] at h ⊢
  intro j h₀ hj
  simp only [extend_odd]
  have e0 := h (2 * j) (by omega) (by push_cast; omega)
  have e1 := h (2 * j + 1) (by omega) (by push_cast; omega)
  have e2 := h (2 * j + 2) (by omega) (by push_cast; omega)
  rw [show 2 * j + 1 - 1 = 2 * j by ring, show 2 * j + 1 + 1 = 2 * j + 2 by ring] at e1
  rw [show 2 * j + 2 - 1 = 2 * j + 1 by ring, show 2 * j + 2 + 1 = 2 * j + 3 by ring] at e2
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
  have hb : extend (reducedRhs D F b) j =
      F *ᵥ (extend b (2 * j) + extend b (2 * j + 2)) - D *ᵥ extend b (2 * j + 1) := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h₀
    have hn : n < M := by omega
    have := extend_coe (reducedRhs D F b) ⟨n, hn⟩
    simp only at this
    rw [this, reducedRhs]
    have c0 := extend_coe b ⟨2 * n, by omega⟩
    have c1 := extend_coe b ⟨2 * n + 1, by omega⟩
    have c2 := extend_coe b ⟨2 * n + 2, by omega⟩
    push_cast at c0 c1 c2
    rw [c0, c1, c2]
  rw [hb, ← e0, ← e1, ← e2]
  simp only [reducedDiag, reducedOff, mulVec_add, sub_mulVec, mulVec_mulVec, smul_mulVec, hDF]
  abel

/-- **The back substitution of cyclic reduction** ([golub2013matrix] §4.5.3): the even-indexed
unknowns (0-based) are determined by the odd-indexed ones through `q × q` systems with matrix `D`,
`D x_{2j} = b_{2j} − F (x_{2j−1} + x_{2j+1})`, the out-of-range neighbours being zero. -/
theorem constBlockTridiagonal_odd_eq {D F : Matrix (Fin q) (Fin q) K}
    {x b : Fin (2 * M + 1) → Fin q → K} (h : constBlockTridiagonal D F x = b) (j : Fin (M + 1)) :
    D *ᵥ x ⟨2 * j, by omega⟩ =
      b ⟨2 * j, by omega⟩ - F *ᵥ (extend x (2 * (j : ℕ) - 1) + extend x (2 * (j : ℕ) + 1)) := by
  rw [← h, constBlockTridiagonal, mulVec_add]
  push_cast
  abel

/-! ### Iterated reduction -/

/-- The sizes `2^k − 1` of the systems that reduce down to one unknown:
`size 0 = 0`, `size (k + 1) = 2 size k + 1`. -/
def size : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * size k + 1

/-- `size k = 2^k − 1`. -/
theorem size_eq (k : ℕ) : size k = 2 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [size, ih, pow_succ]
    have := Nat.one_le_two_pow (n := k)
    omega

/-- The diagonal block after `k` reduction steps. -/
def diagIter : ℕ → Matrix (Fin q) (Fin q) K → Matrix (Fin q) (Fin q) K →
    Matrix (Fin q) (Fin q) K
  | 0, D, _ => D
  | k + 1, D, F => diagIter k (reducedDiag D F) (reducedOff F)

/-- The right-hand side of the single system for the middle unknown after `k` reduction steps of
a system of size `size (k + 1) = 2^{k+1} − 1`. -/
def rhsIter : (k : ℕ) → Matrix (Fin q) (Fin q) K → Matrix (Fin q) (Fin q) K →
    (Fin (size (k + 1)) → Fin q → K) → Fin q → K
  | 0, _, _, b => b ⟨0, by simp [size]⟩
  | k + 1, D, F, b =>
    rhsIter k (reducedDiag D F) (reducedOff F) (reducedRhs (M := size (k + 1)) D F b)

/-- **Iterated cyclic reduction** ([golub2013matrix] §4.5.3): for `N = 2^{k+1} − 1` unknowns
(`size (k + 1)`) and commuting `D`, `F`, after `k` reduction steps the middle unknown
`x_{2^k − 1}` (0-based) solves the single `q × q` system `D_k x_{2^k − 1} = b_k`, with
`(D_{p+1}, F_{p+1}) = (2F_p² − D_p², F_p²)` and `b_k` the iterated reduced right-hand side ("we are
left with a single `q × q` system"). -/
theorem constBlockTridiagonal_iterate_reduce (k : ℕ) {D F : Matrix (Fin q) (Fin q) K}
    (hDF : D * F = F * D) {x b : Fin (size (k + 1)) → Fin q → K}
    (h : constBlockTridiagonal D F x = b) :
    diagIter k D F *ᵥ x ⟨size k, by simp only [size]; omega⟩ = rhsIter k D F b := by
  induction k generalizing D F with
  | zero =>
    have := congrFun h ⟨0, by simp [size]⟩
    rw [constBlockTridiagonal, extend_of_neg x (by simp),
      extend_of_le x (by simp [size])] at this
    simpa [diagIter, rhsIter, size] using this
  | succ k ih =>
    have hr := constBlockTridiagonal_reduce (M := size (k + 1)) hDF h
    exact ih (commute_reduced hDF) hr

end CyclicReduction
