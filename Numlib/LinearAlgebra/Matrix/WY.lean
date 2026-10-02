/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Numlib.LinearAlgebra.Matrix.Products

/-!
# The WY representation of a product of reflectors

A product `Q = Q₁ ⋯ Q_r` of rank-one modifications of the identity `Q_j = 1 - β_j v_j v_jᴴ` (for
instance Householder reflectors) is a rank-`r` modification of the identity,

* `Q = 1 - W Yᴴ`, the **WY representation** ([golub2013matrix] §5.1.7, (5.1.6); Bischof–Van Loan
  1987), with `Y` the matrix whose columns are the vectors `v_j`, and
* `Q = 1 - Y T Yᴴ` with `T` upper triangular, the **compact WY representation** (Schreiber–Van
  Loan 1989), the form used by blocked Householder algorithms.

## Main results

* `Matrix.IsWY Q W Y`: the statement `Q = 1 - W Yᴴ`.
* `Matrix.IsWY.mul_one_sub_smul_vecMulVec` ([golub2013matrix] Lemma 5.1.1): multiplying on the right
  by `1 - β v vᴴ` appends the column `z = β Q v` to `W` and the column `v` to `Y`.
* `Matrix.wyW`, `Matrix.isWY_prod`: the `W` factor built by that recursion ([golub2013matrix]
  Algorithm 5.1.2) represents the whole product (`Matrix.isWY_prodFwd` for the product written as
  `prodFwd` of a sequence); `Y` is the matrix of the vectors themselves, and
  `Matrix.wyW_apply_eq_zero_of_apply_eq_zero` reads off the shape of `W`.
* `Matrix.exists_compactWY`, `Matrix.exists_compactWY_prodFwd`: the compact representation
  `Q = 1 - Y T Yᴴ`.
* `Matrix.one_sub_two_mul_conjTranspose_mem_unitaryGroup`: a *block reflector* `1 - 2 V Vᴴ`
  with `Vᴴ V = 1` is unitary (Schreiber–Parlett 1987).

## Implementation notes

The algebra holds over any commutative `*`-ring, and none of it needs `Q` or the factors to be
unitary (the book assumes orthogonality in Lemma 5.1.1 but does not use it). The factors are indexed
by `Fin r` and the product is `(List.ofFn fun j => 1 - β j • vecMulVec (v j) (star (v j))).prod`, in
the order `Q₁ ⋯ Q_r`, which is `prodFwd` of the factors (`prodFwd_eq_prod_ofFn`);
columns are appended with `Fin.snoc` on the column index,
`Matrix.of fun i => Fin.snoc (W i) (z i)`, which is how the recursion grows `W` and `Y`.

## References

* [golub2013matrix] §5.1.7.
-/

open scoped Matrix

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] {r : ℕ}

/-- **The WY representation** ([golub2013matrix] (5.1.6)): `Q = 1 - W Yᴴ` with `W`, `Y` of
width `r`, so that `Q` is a rank-`r` modification of the identity. -/
def IsWY [Ring R] [Star R] (Q : Matrix n n R) (W Y : Matrix n (Fin r) R) : Prop :=
  Q = 1 - W * Yᴴ

section CommRing

variable [CommRing R] [StarRing R]

omit [Fintype n] [DecidableEq n] in
/-- Appending a column to each factor adds the outer product of the new columns:
`[W | z] [Y | v]ᴴ = W Yᴴ + z vᴴ`. -/
theorem of_snoc_mul_conjTranspose_of_snoc (W Y : Matrix n (Fin r) R) (z v : n → R) :
    (of fun i => Fin.snoc (W i) (z i) : Matrix n (Fin (r + 1)) R) *
        (of fun i => Fin.snoc (Y i) (v i) : Matrix n (Fin (r + 1)) R)ᴴ =
      W * Yᴴ + vecMulVec z (star v) := by
  ext i j
  simp [mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply]

/-- **[golub2013matrix] Lemma 5.1.1.** If `Q = 1 - W Yᴴ` and `P = 1 - β v vᴴ`, then
`Q P = 1 - [W | z] [Y | v]ᴴ` with `z = β Q v`. (No orthogonality is needed.) -/
theorem IsWY.mul_one_sub_smul_vecMulVec {Q : Matrix n n R} {W Y : Matrix n (Fin r) R}
    (h : IsWY Q W Y) (β : R) (v : n → R) :
    IsWY (Q * (1 - β • vecMulVec v (star v))) (of fun i => Fin.snoc (W i) ((β • (Q *ᵥ v)) i))
      (of fun i => Fin.snoc (Y i) (v i)) := by
  rw [IsWY, of_snoc_mul_conjTranspose_of_snoc, smul_vecMulVec, ← sub_sub, ← h, mul_sub, mul_one,
    mul_smul_comm, mul_vecMulVec]

/-- **The `W` factor of the WY representation** of `Q₁ ⋯ Q_r`, `Q_j = 1 - β_j v_j v_jᴴ`, by the
recursion of [golub2013matrix] Algorithm 5.1.2: `W₁ = β₁ v₁` and
`W_{j+1} = [W_j | β_{j+1} (1 - W_j Y_jᴴ) v_{j+1}]`, `Y_j` the first `j` vectors as columns. -/
def wyW : {r : ℕ} → (Fin r → R) → (Fin r → n → R) → Matrix n (Fin r) R
  | 0, _, _ => 0
  | r + 1, β, v =>
    of fun i => Fin.snoc (α := fun _ => R) (wyW (Fin.init β) (Fin.init v) i)
      ((β (Fin.last r) • ((1 - wyW (Fin.init β) (Fin.init v) *
        (of fun i j => Fin.init v j i : Matrix n (Fin r) R)ᴴ) *ᵥ v (Fin.last r))) i)

/-- The recursion defining `Matrix.wyW`. -/
theorem wyW_succ (β : Fin (r + 1) → R) (v : Fin (r + 1) → n → R) :
    wyW β v = of fun i => Fin.snoc (α := fun _ => R) (wyW (Fin.init β) (Fin.init v) i)
      ((β (Fin.last r) • ((1 - wyW (Fin.init β) (Fin.init v) *
        (of fun i j => Fin.init v j i : Matrix n (Fin r) R)ᴴ) *ᵥ v (Fin.last r))) i) :=
  rfl

/-- **Every product of `r` rank-one modifications of the identity has a WY representation**
([golub2013matrix] (5.1.6), Algorithm 5.1.2): `Q₁ ⋯ Q_r = 1 - W Yᴴ` with `W = Matrix.wyW β v` and
`Y` the matrix whose columns are the vectors `v_j`. -/
theorem isWY_prod (β : Fin r → R) (v : Fin r → n → R) :
    IsWY (List.ofFn fun j => 1 - β j • vecMulVec (v j) (star (v j))).prod (wyW β v)
      (of fun i j => v j i) := by
  induction r with
  | zero => simp [IsWY]
  | succ r ih =>
    have h := ih (Fin.init β) (Fin.init v)
    have h' := h.mul_one_sub_smul_vecMulVec (β (Fin.last r)) (v (Fin.last r))
    rw [IsWY] at h
    convert h' using 1
    · rw [List.ofFn_succ', List.prod_concat]
      rfl
    · rw [wyW_succ, h]
    · ext i j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Fin.init]

/-- **Rows on which every vector vanishes are zero rows of `W`** ([golub2013matrix] §5.2.3: "the
first `λ - 1` rows of `W_k` and `Y_k` are zero"): each new column `β (1 - W Yᴴ) v` of `W` is a
combination of the vectors `v_j`. -/
theorem wyW_apply_eq_zero_of_apply_eq_zero {S : Set n} (β : Fin r → R) (v : Fin r → n → R)
    (hv : ∀ j, ∀ i ∈ S, v j i = 0) : ∀ i ∈ S, ∀ k, wyW β v i k = 0 := by
  induction r with
  | zero => exact fun _ _ k => k.elim0
  | succ r ih =>
    intro i hi k
    have ih' := ih (Fin.init β) (Fin.init v) (fun j => hv j.castSucc) i hi
    rw [wyW_succ, of_apply]
    refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [Fin.snoc_last, Pi.smul_apply, sub_mulVec, one_mulVec, ← mulVec_mulVec, Pi.sub_apply,
        hv _ i hi, mulVec, dotProduct]
      simp [ih']
    · rw [Fin.snoc_castSucc, ih']

omit [StarRing R] in
/-- The bordered matrix `[T, t; 0, b]` of the compact WY recursion. -/
private def compactWYStep (T : Matrix (Fin r) (Fin r) R) (t : Fin r → R) (b : R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  of (Fin.snoc (α := fun _ => Fin (r + 1) → R) (fun i => Fin.snoc (α := fun _ => R) (T i) (t i))
    (Fin.snoc (α := fun _ => R) 0 b))

omit [StarRing R] in
private theorem compactWYStep_isUpperTriangular {T : Matrix (Fin r) (Fin r) R}
    (hT : T.IsUpperTriangular) (t : Fin r → R) (b : R) :
    (compactWYStep T t b).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  induction i using Fin.lastCases with
  | last =>
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hji)
    simp [compactWYStep]
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact absurd hji (not_lt.2 (Fin.castSucc_lt_last i).le)
    | cast j => simpa [compactWYStep] using hT (Fin.castSucc_lt_castSucc_iff.1 hji)

omit [Fintype n] [DecidableEq n] [StarRing R] in
private theorem of_snoc_mul_compactWYStep (Y : Matrix n (Fin r) R) (w : n → R)
    (T : Matrix (Fin r) (Fin r) R) (t : Fin r → R) (b : R) :
    (of fun i => Fin.snoc (Y i) (w i) : Matrix n (Fin (r + 1)) R) * compactWYStep T t b =
      of fun i => Fin.snoc ((Y * T) i) ((Y *ᵥ t + b • w) i) := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [compactWYStep, mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct, mul_comm]

/-- One step of the compact WY recursion: if `Q = 1 - Y T Yᴴ`, then
`Q (1 - b w wᴴ) = 1 - [Y | w] [T, t; 0, b] [Y | w]ᴴ` with `t = -b T Yᴴ w`. -/
private theorem compactWY_step {Q : Matrix n n R} {Y : Matrix n (Fin r) R}
    {T : Matrix (Fin r) (Fin r) R} (hQ : Q = 1 - Y * T * Yᴴ) (b : R) (w : n → R) :
    Q * (1 - b • vecMulVec w (star w)) =
      1 - (of fun i => Fin.snoc (Y i) (w i) : Matrix n (Fin (r + 1)) R) *
        compactWYStep T (-b • (T *ᵥ (Yᴴ *ᵥ w))) b *
        (of fun i => Fin.snoc (Y i) (w i) : Matrix n (Fin (r + 1)) R)ᴴ := by
  have h := IsWY.mul_one_sub_smul_vecMulVec (W := Y * T) hQ b w
  rw [IsWY, of_snoc_mul_conjTranspose_of_snoc] at h
  rw [h, of_snoc_mul_compactWYStep, of_snoc_mul_conjTranspose_of_snoc, hQ, sub_mulVec,
    one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_smul, smul_sub, neg_smul, add_comm]
  abel_nf

/-- **The compact WY representation** (Schreiber–Van Loan 1989; [golub2013matrix] §5.1.7): with
`Y` as in `Matrix.isWY_prod`, `Q₁ ⋯ Q_r = 1 - Y T Yᴴ` for an upper triangular `T`, built by
`T₁ = β₁`, `T_{j+1} = [T_j, -β_{j+1} T_j Y_jᴴ v_{j+1}; 0, β_{j+1}]`. -/
theorem exists_compactWY (β : Fin r → R) (v : Fin r → n → R) :
    ∃ T : Matrix (Fin r) (Fin r) R, T.IsUpperTriangular ∧
      (List.ofFn fun j => 1 - β j • vecMulVec (v j) (star (v j))).prod =
        1 - (of fun i j => v j i) * T * (of fun i j => v j i)ᴴ := by
  induction r with
  | zero => exact ⟨0, fun i => i.elim0, by simp⟩
  | succ r ih =>
    obtain ⟨T, hT, hQ⟩ := ih (Fin.init β) (Fin.init v)
    have hY : (of fun i j => v j i : Matrix n (Fin (r + 1)) R) =
        of fun i => Fin.snoc ((of fun i j => Fin.init v j i : Matrix n (Fin r) R) i)
          (v (Fin.last r) i) := by
      ext i j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Fin.init]
    refine ⟨_, compactWYStep_isUpperTriangular hT (-β (Fin.last r) • (T *ᵥ
      ((of fun i j => Fin.init v j i : Matrix n (Fin r) R)ᴴ *ᵥ v (Fin.last r))))
      (β (Fin.last r)), ?_⟩
    rw [List.ofFn_succ', List.prod_concat, hY]
    exact compactWY_step hQ _ _

/-- **The WY representation of a forward product** (`Matrix.isWY_prod` for `prodFwd`): for
sequences `β`, `v`, `Q₁ ⋯ Q_r = 1 - W Yᴴ` with `W = Matrix.wyW` of the first `r` terms and `Y`
the matrix whose columns are `v 0, …, v (r-1)`. -/
theorem isWY_prodFwd (β : ℕ → R) (v : ℕ → n → R) (r : ℕ) :
    IsWY (prodFwd (fun k => 1 - β k • vecMulVec (v k) (star (v k))) r)
      (wyW (fun j : Fin r => β j) fun j => v j) (of fun i (j : Fin r) => v j i) := by
  rw [prodFwd_eq_prod_ofFn]
  exact isWY_prod _ _

/-- **The compact WY representation of a forward product** (`Matrix.exists_compactWY` for
`prodFwd`): `Q₁ ⋯ Q_r = 1 - Y T Yᴴ` with `T` upper triangular and `Y` the matrix whose
columns are `v 0, …, v (r-1)`. -/
theorem exists_compactWY_prodFwd (β : ℕ → R) (v : ℕ → n → R) (r : ℕ) :
    ∃ T : Matrix (Fin r) (Fin r) R, T.IsUpperTriangular ∧
      prodFwd (fun k => 1 - β k • vecMulVec (v k) (star (v k))) r =
        1 - (of fun i (j : Fin r) => v j i) * T * (of fun i (j : Fin r) => v j i)ᴴ := by
  rw [prodFwd_eq_prod_ofFn]
  exact exists_compactWY (fun j : Fin r => β j) fun j => v j

/-- **Block reflectors are unitary** ([golub2013matrix] §5.1.7; Schreiber–Parlett 1987): if
`Vᴴ V = 1`, then `1 - 2 V Vᴴ` is unitary (it is Hermitian and involutive). -/
theorem one_sub_two_mul_conjTranspose_mem_unitaryGroup {κ : Type*} [Fintype κ]
    [DecidableEq κ] {V : Matrix n κ R} (hV : Vᴴ * V = 1) :
    1 - (2 : R) • (V * Vᴴ) ∈ unitaryGroup n R := by
  have hX : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_sub, conjTranspose_one,
    conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose, star_ofNat, two_smul]
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hX]
  abel

end CommRing

end Matrix
