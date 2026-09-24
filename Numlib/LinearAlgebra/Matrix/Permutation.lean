/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Permutation`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Named permutation and shift matrices

The permutation matrices that recur in matrix computations, on `Fin n`, as instances of Mathlib's
permutation-matrix API (`Equiv.Perm.permMatrix`, `PEquiv.toMatrix`):

* the **exchange** matrix `ℰ_n` (`Matrix.exchange`), which turns a vector upside down — the
  permutation matrix of `Fin.revPerm`;
* the **downshift** `𝒟_n` (`Matrix.downshift`), which pushes the components of a vector down one
  place with wraparound — the permutation matrix of `(finRotate n).symm`, and the circulant of the
  first unit vector after `e₀`;
* the mod-`p` **perfect shuffle** `Π_{p,r}` (`Matrix.perfectShuffle`), which cuts a deck of `p r`
  cards into `p` piles of `r` cards and reassembles it by taking one card from each pile in turn —
  the matrix of the index map `Matrix.finPerfectShuffle`;
* the `φ`-**cyclic shift** `Z_φ` (`Matrix.cyclicShift`), the downshift with the wraparound entry
  replaced by `φ`; `Z_1 = 𝒟_n`, `Z_0` is the lower shift, and `Z_φ ^ n = φ I`.

The perfect shuffle is typed `Matrix (Fin (r * p)) (Fin (p * r)) R`: both index types have `p r`
elements, and keeping them apart makes `(Π_{p,r})ᵀ = Π_{r,p}` and the conjugation of a Kronecker
product (`Numlib.LinearAlgebra.Matrix.Kronecker`) hold with no cast. Position `b r + a` of the input
(card `a` of pile `b`) is position `a p + b` of the output, which is the index map
`finProdFinEquiv (b, a) ↦ finProdFinEquiv (a, b)`.

What uses these matrices stays with its subject: persymmetry and Toeplitz structure, the
commutation of the Kronecker product, displacement structure.

## Main definitions

* `Matrix.exchange`, `Matrix.downshift`, `Matrix.finPerfectShuffle`, `Matrix.perfectShuffle`,
  `Matrix.cyclicShift`.

## Main statements

* `Matrix.exchange_eq_permMatrix`, `Matrix.exchange_mul_exchange`, `Matrix.transpose_exchange`.
* `Matrix.downshift_eq_circulant`, `Matrix.downshift_pow`, `Matrix.downshift_pow_card`.
* `Matrix.perfectShuffle_mulVec`, `Matrix.transpose_perfectShuffle`,
  `Matrix.perfectShuffle_mul_transpose`.
* `Matrix.cyclicShift_one`, `Matrix.cyclicShift_pow_card`.

## References

* [golub2013matrix], §1.2.11 (exchange, downshift, perfect shuffle), §4.7.1, §4.8.2, (12.1.7).
-/

open Equiv

namespace Matrix

variable {R : Type*}

/-! ### The exchange matrix -/

section Exchange

section Basic

variable [Zero R] [One R]

/-- The exchange matrix `ℰ_n`, with ones on the antidiagonal: `ℰ_n x` is `x` turned upside down. -/
def exchange (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  of fun i j => if j = Fin.rev i then 1 else 0

/-- The entries of the exchange matrix: ones on the antidiagonal. -/
theorem exchange_apply (n : ℕ) (i j : Fin n) :
    (exchange n : Matrix (Fin n) (Fin n) R) i j = if j = Fin.rev i then 1 else 0 := rfl

/-- The exchange matrix is the permutation matrix of the reversal `Fin.revPerm`. -/
theorem exchange_eq_permMatrix (n : ℕ) :
    (exchange n : Matrix (Fin n) (Fin n) R) = (Fin.revPerm : Perm (Fin n)).permMatrix R := by
  ext i j
  simp [exchange, PEquiv.toMatrix_apply, eq_comm]

/-- The exchange matrix is symmetric. -/
@[simp]
theorem transpose_exchange (n : ℕ) : (exchange n : Matrix (Fin n) (Fin n) R)ᵀ = exchange n := by
  ext i j
  simp only [transpose_apply, exchange_apply]
  exact if_congr ⟨fun h => h ▸ (Fin.rev_rev j).symm, fun h => h ▸ (Fin.rev_rev i).symm⟩ rfl rfl

end Basic

variable [NonAssocSemiring R] {n : ℕ}

/-- The exchange matrix reverses a vector: `(ℰ_n v) i = v (rev i)`. -/
@[simp]
theorem exchange_mulVec_apply (v : Fin n → R) (i : Fin n) :
    (exchange n *ᵥ v) i = v (Fin.rev i) := by
  rw [exchange_eq_permMatrix, PEquiv.toMatrix_toPEquiv_mulVec]
  rfl

/-- Multiplying by the exchange matrix on the right reverses a row vector. -/
@[simp]
theorem vecMul_exchange_apply (v : Fin n → R) (j : Fin n) :
    (v ᵥ* exchange n) j = v (Fin.rev j) := by
  rw [exchange_eq_permMatrix, PEquiv.vecMul_toMatrix_toPEquiv]
  rfl

/-- Multiplying by the exchange matrix on the left reverses the order of the rows. -/
@[simp]
theorem exchange_mul_apply {m : Type*} (A : Matrix (Fin n) m R) (i : Fin n) (j : m) :
    (exchange n * A : Matrix (Fin n) m R) i j = A (Fin.rev i) j := by
  rw [exchange_eq_permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  rfl

/-- Multiplying by the exchange matrix on the right reverses the order of the columns. -/
@[simp]
theorem mul_exchange_apply {m : Type*} (A : Matrix m (Fin n) R) (i : m) (j : Fin n) :
    (A * exchange n : Matrix m (Fin n) R) i j = A i (Fin.rev j) := by
  rw [exchange_eq_permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The exchange matrix is an involution: `ℰ_n ℰ_n = I`. -/
@[simp]
theorem exchange_mul_exchange : (exchange n : Matrix (Fin n) (Fin n) R) * exchange n = 1 := by
  ext i j
  rw [exchange_mul_apply, exchange_apply, one_apply, Fin.rev_rev]
  exact if_congr eq_comm rfl rfl

end Exchange

/-! ### The downshift -/

section Downshift

section Basic

variable [Zero R] [One R]

/-- The downshift permutation `𝒟_n`: `𝒟_n e_j = e_{j+1}` cyclically, so `𝒟_n x` pushes the
components of `x` down one place with wraparound. -/
def downshift (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Equiv.Perm.permMatrix R (finRotate n).symm

/-- The entries of the downshift: `𝒟_n i j = 1` exactly when `i = j + 1` cyclically. -/
theorem downshift_apply (n : ℕ) (i j : Fin n) :
    (downshift n : Matrix (Fin n) (Fin n) R) i j = if finRotate n j = i then 1 else 0 := by
  simp only [downshift, Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  exact if_congr (((finRotate n).symm_apply_eq).trans eq_comm) rfl rfl

/-- The downshift is the circulant matrix of `e₁`. -/
theorem downshift_eq_circulant (n : ℕ) [NeZero n] :
    (downshift n : Matrix (Fin n) (Fin n) R) = circulant (Pi.single 1 1) := by
  ext i j
  rw [downshift_apply, circulant_apply, finRotate_apply]
  simp only [Pi.single_apply]
  exact if_congr (by rw [sub_eq_iff_eq_add, add_comm, eq_comm]) rfl rfl

end Basic

variable [Semiring R]

/-- The downshift moves a vector down one place: `(𝒟_n x) i = x (i - 1)`. -/
theorem downshift_mulVec {n : ℕ} (x : Fin n → R) :
    downshift n *ᵥ x = x ∘ (finRotate n).symm :=
  PEquiv.toMatrix_toPEquiv_mulVec (finRotate n).symm x

open Fin.NatCast in
/-- The powers of the downshift are the circulants of the unit vectors. -/
theorem downshift_pow (n : ℕ) [NeZero n] (k : ℕ) :
    (downshift n : Matrix (Fin n) (Fin n) R) ^ k = circulant (Pi.single (k : Fin n) 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, downshift_eq_circulant, circulant_mul]
    congr 1
    ext i
    simp only [mulVec, dotProduct, circulant_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Nat.cast_succ, sub_eq_iff_eq_add]

open Fin.NatCast in
/-- `𝒟_n ^ n = I`. -/
theorem downshift_pow_card (n : ℕ) : (downshift n : Matrix (Fin n) (Fin n) R) ^ n = 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact Subsingleton.elim _ _
  · have := NeZero.of_pos hn
    rw [downshift_pow, Fin.natCast_self, circulant_single_one]

end Downshift

/-! ### The perfect shuffle -/

section PerfectShuffle

/-- The perfect-shuffle index map: position `b r + a` of a deck of `p` piles of `r` cards (card `a`
of pile `b`) goes to position `a p + b`. -/
def finPerfectShuffle (p r : ℕ) : Fin (p * r) ≃ Fin (r * p) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin p) (Fin r)).trans finProdFinEquiv)

/-- The perfect shuffle on positions: card `a` of pile `b`, at position `b r + a`, goes to
position `a p + b`. -/
@[simp]
theorem finPerfectShuffle_apply (p r : ℕ) (b : Fin p) (a : Fin r) :
    finPerfectShuffle p r (finProdFinEquiv (b, a)) = finProdFinEquiv (a, b) := by
  simp [finPerfectShuffle]

/-- The inverse of the mod-`p` perfect shuffle is the mod-`r` perfect shuffle. -/
@[simp]
theorem finPerfectShuffle_symm (p r : ℕ) :
    (finPerfectShuffle p r).symm = finPerfectShuffle r p := by
  refine Equiv.ext fun x => ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective x
  rw [Equiv.symm_apply_eq, finPerfectShuffle_apply, finPerfectShuffle_apply]

section Basic

variable [Zero R] [One R]

/-- The mod-`p` perfect shuffle `Π_{p,r}`: the deck `x ∈ R^{pr}` is cut into `p` piles of `r`
cards, and reassembled by taking one card from each pile in turn, so that
`(Π_{p,r} x) (a p + b) = x (b r + a)`. -/
def perfectShuffle (p r : ℕ) : Matrix (Fin (r * p)) (Fin (p * r)) R :=
  (finPerfectShuffle p r).symm.toPEquiv.toMatrix

/-- `(Π_{p,r})ᵀ = Π_{r,p}`. -/
@[simp]
theorem transpose_perfectShuffle (p r : ℕ) :
    (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R)ᵀ = perfectShuffle r p := by
  rw [perfectShuffle, perfectShuffle, ← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm,
    Equiv.symm_symm, finPerfectShuffle_symm]

end Basic

variable [NonAssocSemiring R]

/-- The perfect shuffle acting on a vector: `Π_{p,r} x = x ∘ (finPerfectShuffle p r).symm`. -/
theorem perfectShuffle_mulVec (p r : ℕ) (x : Fin (p * r) → R) :
    perfectShuffle p r *ᵥ x = x ∘ (finPerfectShuffle p r).symm :=
  PEquiv.toMatrix_toPEquiv_mulVec (finPerfectShuffle p r).symm x

/-- The perfect shuffle on a vector, entrywise: `(Π_{p,r} x) (a p + b) = x (b r + a)`. -/
@[simp]
theorem perfectShuffle_mulVec_apply (p r : ℕ) (x : Fin (p * r) → R) (b : Fin p) (a : Fin r) :
    (perfectShuffle p r *ᵥ x) (finProdFinEquiv (a, b)) = x (finProdFinEquiv (b, a)) := by
  rw [perfectShuffle_mulVec, Function.comp_apply, finPerfectShuffle_symm, finPerfectShuffle_apply]

/-- The perfect shuffle is orthogonal: `Π_{p,r} Π_{p,r}ᵀ = I` and `Π_{p,r}ᵀ Π_{p,r} = I`. -/
theorem perfectShuffle_mul_transpose (p r : ℕ) :
    (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R) *
        (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R)ᵀ = 1 ∧
      (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R)ᵀ *
        (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) R) = 1 := by
  rw [transpose_perfectShuffle, perfectShuffle, perfectShuffle, ← PEquiv.toMatrix_trans,
    ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, ← Equiv.toPEquiv_trans,
    finPerfectShuffle_symm, finPerfectShuffle_symm, ← finPerfectShuffle_symm r p,
    Equiv.symm_trans_self, Equiv.self_trans_symm, Equiv.toPEquiv_refl, Equiv.toPEquiv_refl,
    PEquiv.toMatrix_refl, PEquiv.toMatrix_refl]
  exact ⟨rfl, rfl⟩

end PerfectShuffle

/-! ### The `φ`-cyclic shift -/

section CyclicShift

section Basic

variable [Zero R] [One R]

/-- The `φ`-cyclic shift `Z_φ`: ones on the subdiagonal, `φ` in the top right corner, zero
elsewhere. `Z_1` is the downshift and `Z_0` the lower shift. -/
def cyclicShift (n : ℕ) (φ : R) : Matrix (Fin n) (Fin n) R :=
  of fun i j => if (i : ℕ) = j + 1 then 1 else if (i : ℕ) = 0 ∧ (j : ℕ) + 1 = n then φ else 0

/-- The entries of the `φ`-cyclic shift. -/
theorem cyclicShift_apply (n : ℕ) (φ : R) (i j : Fin n) :
    cyclicShift n φ i j
      = if (i : ℕ) = j + 1 then 1 else if (i : ℕ) = 0 ∧ (j : ℕ) + 1 = n then φ else 0 := rfl

/-- `Z_1` is the downshift `𝒟_n`. -/
theorem cyclicShift_one (n : ℕ) : cyclicShift n (1 : R) = downshift n := by
  ext i j
  rw [cyclicShift_apply, downshift_apply]
  rcases n with _ | n
  · exact i.elim0
  have key : finRotate (n + 1) j = i ↔ (i : ℕ) = j + 1 ∨ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = n + 1) := by
    rw [Fin.ext_iff, coe_finRotate]
    split_ifs with h
    · rw [Fin.ext_iff, Fin.val_last] at h
      omega
    · rw [Fin.ext_iff, Fin.val_last] at h
      omega
  by_cases h1 : (i : ℕ) = j + 1
  · rw [ite_eq_left h1, ite_eq_left (key.2 (Or.inl h1))]
  · by_cases h2 : (i : ℕ) = 0 ∧ (j : ℕ) + 1 = n + 1
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (key.2 (Or.inr h2))]
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right fun h => (key.1 h).elim h1 h2]

end Basic

variable [Semiring R]

/-- `Z_φ` moves a vector down one place and multiplies the wrapped-around component by `φ`. -/
theorem cyclicShift_mulVec_apply {n : ℕ} (φ : R) (x : Fin n → R) (i : Fin n) :
    (cyclicShift n φ *ᵥ x) i
      = if h : (i : ℕ) = 0 then φ * x ⟨n - 1, by omega⟩ else x ⟨i - 1, by omega⟩ := by
  have hi := i.is_lt
  rw [mulVec, dotProduct]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
    · have h1 : ¬ (i : ℕ) = n - 1 + 1 := by omega
      have h2 : (i : ℕ) = 0 ∧ n - 1 + 1 = n := by omega
      rw [cyclicShift_apply, ite_eq_right h1, ite_eq_left h2]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ n - 1 := fun h' => hj (Fin.ext h')
      have h1 : ¬ (i : ℕ) = j + 1 := by omega
      have h2 : ¬ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = n) := by omega
      rw [cyclicShift_apply, ite_eq_right h1, ite_eq_right h2, zero_mul]
    · simp
  · rw [Finset.sum_eq_single ⟨i - 1, by omega⟩]
    · have h1 : (i : ℕ) = i - 1 + 1 := by omega
      rw [cyclicShift_apply, ite_eq_left h1, one_mul]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ i - 1 := fun h' => hj (Fin.ext h')
      have h1 : ¬ (i : ℕ) = j + 1 := by omega
      have h2 : ¬ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = n) := by omega
      rw [cyclicShift_apply, ite_eq_right h1, ite_eq_right h2, zero_mul]
    · simp

/-- The powers of `Z_φ` on a vector: for `k ≤ n`, `(Z_φ^k x) i = x (i - k)` when `k ≤ i`, and
`φ x (i + n - k)` otherwise. -/
theorem cyclicShift_pow_mulVec_apply {n : ℕ} (φ : R) (x : Fin n → R) {k : ℕ} (hk : k ≤ n)
    (i : Fin n) :
    (cyclicShift n φ ^ k *ᵥ x) i
      = if h : k ≤ i then x ⟨i - k, by omega⟩ else φ * x ⟨i + n - k, by omega⟩ := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    have hi := i.is_lt
    rw [pow_succ', ← mulVec_mulVec, cyclicShift_mulVec_apply]
    split_ifs with h0 h1 h1
    · omega
    · rw [ih (by omega)]
      split_ifs with h2
      · congr 2
        ext
        simp only
        omega
      · simp only at h2
        omega
    · rw [ih (by omega)]
      split_ifs with h2
      · congr 1
        ext
        simp only
        omega
      · simp only at h2
        omega
    · rw [ih (by omega)]
      split_ifs with h2
      · simp only at h2
        omega
      · congr 2
        ext
        simp only
        omega

/-- `Z_φ ^ n = φ I`: going once around the cycle multiplies every component by `φ`. -/
theorem cyclicShift_pow_card (n : ℕ) (φ : R) : cyclicShift n φ ^ n = φ • (1 : Matrix _ _ R) := by
  refine ext_of_mulVec_single fun j => funext fun i => ?_
  have hi : ¬ n ≤ (i : ℕ) := by have := i.is_lt; omega
  rw [cyclicShift_pow_mulVec_apply φ _ le_rfl, dite_eq_right hi, smul_mulVec, one_mulVec]
  simp only [Nat.add_sub_cancel, Fin.eta, Pi.smul_apply, smul_eq_mul]

end CyclicShift

end Matrix
