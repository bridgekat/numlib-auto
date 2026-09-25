import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.LinearAlgebra.Matrix.Cholesky

/-!
# Updating the QR and Cholesky factorizations

Updating matrix factorizations ([golub2013matrix] §6.5, after Gill–Golub–Murray–Saunders 1974):
the full QR factorization after a rank-one change, after deleting or inserting a column, after
inserting or deleting a row; the Cholesky factorization after adding (`A + z zᵀ`, plane rotations)
or removing (`A − z zᵀ`, hyperbolic rotations) a rank-one term. Real matrices, as the book and as
`Matrix.planeRotation`, except where the argument works over any ring.

The backbone states *what* the updates compute, not how: each update is an existence theorem
saying that there are rotations in prescribed planes — the structural content that makes the
update cost `O(n²)` — whose product carries the old factorization to the new one. The step-by-step
procedures of §6.5 are surface definitions, proved correct against the two general lemmas below.

## Main definitions

* `Matrix.adjacentEmbed j G`: a `2 × 2` block in the plane `(j, j + 1)` of `Fin M`, the identity
  when `j + 1 ≥ M`, so that sweeps are products over lists of natural numbers.
* `Matrix.adjacentRotationProd a n c s`: the sweep `G_a ⋯ G_{a+n−1}` of rotations in adjacent
  planes; applied on the left it acts bottom-up, its transpose top-down.
* `Matrix.consDiag a Q`: the block diagonal `diag(a, Q)` of §6.5.3.

## Main results

* `Matrix.prod_planeEmbed_mul_apply_eq_zero` ((6.5.2)): embeddings of *arbitrary* blocks in the
  planes `(b, b + 1), (b + 1, b + 2), …`, applied bottom-up to an upper trapezoidal matrix, leave
  it upper Hessenberg and triangular before column `b`.
* `Matrix.upperTrapezoidal_of_adjacentRotations`: a top-down sweep of arbitrary blocks, each
  zeroing its subdiagonal target, triangularizes a rectangular Hessenberg matrix; the zeroing is
  a hypothesis, so any Givens routine instantiates it.
  `Matrix.exists_rotations_triangularize_of_hessenberg` and
  `Matrix.exists_adjacentRotationProd_mulVec_eq_zero` are the Givens existence statements.
* The QR updates: `Matrix.exists_isQR_rankOne_update` (§6.5.1), `Matrix.IsQR.exists_deleteColumn`,
  `Matrix.IsQR.exists_insertColumn` (§6.5.2), `Matrix.IsQR.exists_insertRow`,
  `Matrix.IsQR.exists_deleteFirstRow`, `Matrix.IsQR.exists_deleteRow` (§6.5.3), with the shape
  lemmas `IsQR.conjTranspose_mul_deleteColumn`, `…_insertColumn`, `…_insertRow`.
* The stacked matrix `[H; zᵀ]` (`Matrix.fromRows H (replicateRow Unit z)`):
  `Matrix.transpose_mul_self_fromRows` ((6.5.6)), `transpose_mul_indefiniteDiagonal_mul_fromRows`
  ((6.5.10)), `transpose_mul_self_eq_of_mem_orthogonalGroup` ((6.5.7)),
  `transpose_mul_self_sub_eq_of_isJOrthogonal` ((6.5.11)–(6.5.12)), and the one-step shape lemma
  `Matrix.fromRows_rotate_step` shared by both Cholesky sweeps.
* `Matrix.exists_choleskyUpdate`, `Matrix.exists_choleskyDowndate` (§6.5.4), the step
  `Matrix.hyperbolicDowndate_step` ([golub2013matrix] Theorem 6.5.1), and the sign normalization
  `Matrix.isCholesky_diagonal_sign_mul`.

## Implementation notes

Rectangular shapes use `Matrix.HasLowerBandwidthRect`: upper Hessenberg is bandwidth `1`, upper
trapezoidal (the `R` of `Matrix.IsQR`) bandwidth `0`. The signature `S = diag(I_n, −1)` of (6.5.9)
is Mathlib's `LieAlgebra.Orthogonal.indefiniteDiagonal n Unit`, and the Cholesky factor is the
backbone's upper triangular `H = Gᵀ` (`Matrix.IsCholesky A H`: `Hᴴ H = A`).

The downdate does not follow the book's induction on the order through Theorem 6.5.1 and a
reindexing `Fin (n + 1) ≃ Unit ⊕ Fin n`: it sweeps the planes `(k, last)` in order with the
invariant that the current `[R'; z'ᵀ]` has `R'ᵀ R' − z' z'ᵀ = A − z zᵀ`; positive definiteness
tested on `R'⁻¹ e_k` gives `|z'_k| < r'_kk`, so the hyperbolic pair of step `k` exists.

A Givens sweep can leave negative diagonal entries in a triangular factor (the book's routine
Algorithm 5.1.3 may return a negative `r`); the book's "the updated Cholesky factor is `G̃ = Rᵀ`"
holds up to the signs that `Matrix.isCholesky_diagonal_sign_mul` normalizes. The sweeps here use
the backbone's `Matrix.givensPair` and `Matrix.hyperbolicPair`, whose diagonal stays positive.
-/

open scoped Matrix

namespace Matrix

/-! ### Embeddings in adjacent planes -/

section AdjacentEmbed

variable {α : Type*} {M : ℕ}

/-- Left multiplication of a rectangular matrix by a plane embedding combines the rows `j` and `k`
(`Matrix.planeEmbed_mul_apply` for a square right factor). Stated locally; it belongs in
`Numlib/LinearAlgebra/Matrix/PlaneRotation` as the rectangular form of `planeEmbed_mul_apply`. -/
private theorem planeEmbed_mul_apply_rect {n m : Type*} [DecidableEq n] [Fintype n]
    [NonAssocSemiring α] {j k : n} (G : Matrix (Fin 2) (Fin 2) α) (hjk : j ≠ k) (X : Matrix n m α)
    (p : n) (q : m) :
    (planeEmbed j k G * X) p q =
      if p = j then G 0 0 * X j q + G 0 1 * X k q
      else if p = k then G 1 0 * X j q + G 1 1 * X k q
      else X p q :=
  planeEmbed_mulVec_apply G hjk (fun r => X r q) p

/-- **The embedding in an adjacent plane**: the `2 × 2` block `G` placed in the coordinate plane
`(j, j + 1)` of `Fin M` (`Matrix.planeEmbed`), and the identity when `j + 1 ≥ M`. Indexing the
planes by `j : ℕ` makes a sweep over the planes `(j, j + 1)` a product over a list of natural
numbers, with no bounds to carry. -/
def adjacentEmbed [Zero α] [One α] (j : ℕ) (G : Matrix (Fin 2) (Fin 2) α) :
    Matrix (Fin M) (Fin M) α :=
  if h : j + 1 < M then planeEmbed ⟨j, by omega⟩ ⟨j + 1, h⟩ G else 1

section Basic

variable [Zero α] [One α] {j : ℕ} (G : Matrix (Fin 2) (Fin 2) α)

/-- Inside `Fin M`, the adjacent embedding is the plane embedding. -/
theorem adjacentEmbed_of_lt (h : j + 1 < M) :
    (adjacentEmbed j G : Matrix (Fin M) (Fin M) α) = planeEmbed ⟨j, by omega⟩ ⟨j + 1, h⟩ G :=
  dite_eq_left h

/-- Beyond `Fin M`, the adjacent embedding is the identity. -/
theorem adjacentEmbed_of_le (h : M ≤ j + 1) : (adjacentEmbed j G : Matrix (Fin M) (Fin M) α) = 1 :=
  dite_eq_right (by omega)

/-- Transposition commutes with the embedding. -/
theorem adjacentEmbed_transpose :
    (adjacentEmbed j G : Matrix (Fin M) (Fin M) α)ᵀ = adjacentEmbed j Gᵀ := by
  unfold adjacentEmbed
  split_ifs
  · exact planeEmbed_transpose G (Fin.ne_of_val_ne (by simp))
  · exact transpose_one

end Basic

section Mul

variable [NonAssocSemiring α] (j : ℕ) (G : Matrix (Fin 2) (Fin 2) α)

/-- Away from the rows `j`, `j + 1` an adjacent embedding leaves a vector alone. -/
theorem adjacentEmbed_mulVec_apply_of_ne (x : Fin M → α) {i : Fin M} (h₀ : (i : ℕ) ≠ j)
    (h₁ : (i : ℕ) ≠ j + 1) : (adjacentEmbed j G *ᵥ x) i = x i := by
  unfold adjacentEmbed
  split_ifs with h
  · exact planeEmbed_mulVec_apply_of_ne G (Fin.ne_of_val_ne (by simp)) x (Fin.ne_of_val_ne h₀)
      (Fin.ne_of_val_ne h₁)
  · rw [one_mulVec]

/-- The `j`-th entry after an adjacent embedding. -/
theorem adjacentEmbed_mulVec_apply_self (h : j + 1 < M) (x : Fin M → α) :
    (adjacentEmbed j G *ᵥ x) ⟨j, by omega⟩ =
      G 0 0 * x ⟨j, by omega⟩ + G 0 1 * x ⟨j + 1, h⟩ := by
  rw [adjacentEmbed_of_lt G h, planeEmbed_mulVec_apply G (Fin.ne_of_val_ne (by simp)),
    ite_eq_left rfl]

/-- The `(j + 1)`-th entry after an adjacent embedding. -/
theorem adjacentEmbed_mulVec_apply_succ (h : j + 1 < M) (x : Fin M → α) :
    (adjacentEmbed j G *ᵥ x) ⟨j + 1, h⟩ =
      G 1 0 * x ⟨j, by omega⟩ + G 1 1 * x ⟨j + 1, h⟩ := by
  rw [adjacentEmbed_of_lt G h, planeEmbed_mulVec_apply G (Fin.ne_of_val_ne (by simp)),
    ite_eq_right (Fin.ne_of_val_ne (by simp)), ite_eq_left rfl]

/-- An adjacent embedding keeps the zeros a vector has in both rows `j`, `j + 1`. -/
theorem adjacentEmbed_mulVec_apply_eq_zero {x : Fin M → α}
    (hx : ∀ r : Fin M, (r : ℕ) = j ∨ (r : ℕ) = j + 1 → x r = 0) {i : Fin M}
    (hi : (i : ℕ) = j ∨ (i : ℕ) = j + 1) : (adjacentEmbed j G *ᵥ x) i = 0 := by
  unfold adjacentEmbed
  split_ifs with h
  · rw [planeEmbed_mulVec_apply G (Fin.ne_of_val_ne (by simp)), hx ⟨j, by omega⟩ (Or.inl rfl),
      hx ⟨j + 1, h⟩ (Or.inr rfl), hx i hi]
    simp
  · rw [one_mulVec, hx i hi]

variable {N : ℕ} (X : Matrix (Fin M) (Fin N) α)

/-- Away from the rows `j`, `j + 1` an adjacent embedding leaves a matrix alone. -/
theorem adjacentEmbed_mul_apply_of_ne {i : Fin M} (h₀ : (i : ℕ) ≠ j) (h₁ : (i : ℕ) ≠ j + 1)
    (l : Fin N) : ((adjacentEmbed j G : Matrix (Fin M) (Fin M) α) * X) i l = X i l :=
  adjacentEmbed_mulVec_apply_of_ne j G (fun r => X r l) h₀ h₁

/-- The `(j + 1, l)` entry after an adjacent embedding. -/
theorem adjacentEmbed_mul_apply_succ (h : j + 1 < M) (l : Fin N) :
    ((adjacentEmbed j G : Matrix (Fin M) (Fin M) α) * X) ⟨j + 1, h⟩ l =
      G 1 0 * X ⟨j, by omega⟩ l + G 1 1 * X ⟨j + 1, h⟩ l :=
  adjacentEmbed_mulVec_apply_succ j G h (fun r => X r l)

/-- An adjacent embedding keeps the zeros a column has in both rows `j`, `j + 1`. -/
theorem adjacentEmbed_mul_apply_eq_zero {l : Fin N}
    (hX : ∀ r : Fin M, (r : ℕ) = j ∨ (r : ℕ) = j + 1 → X r l = 0) {i : Fin M}
    (hi : (i : ℕ) = j ∨ (i : ℕ) = j + 1) :
    ((adjacentEmbed j G : Matrix (Fin M) (Fin M) α) * X) i l = 0 :=
  adjacentEmbed_mulVec_apply_eq_zero j G hX hi

end Mul

/-- An adjacent embedding of a unitary block is unitary. -/
theorem adjacentEmbed_mem_unitaryGroup [CommRing α] [StarRing α] (j : ℕ)
    {G : Matrix (Fin 2) (Fin 2) α} (hG : G ∈ unitaryGroup (Fin 2) α) :
    (adjacentEmbed j G : Matrix (Fin M) (Fin M) α) ∈ unitaryGroup (Fin M) α := by
  unfold adjacentEmbed
  split_ifs
  · exact (planeEmbed_mem_unitaryGroup_iff G (Fin.ne_of_val_ne (by simp))).2 hG
  · exact one_mem _

end AdjacentEmbed

/-! ### Sweeps of rotations in adjacent planes -/

section AdjacentRotationProd

variable {M : ℕ}

/-- **A sweep of rotations in adjacent planes**: the product `G_a G_{a+1} ⋯ G_{a+n-1}`, in
increasing order, of the rotations `G_j = !![c j, -s j; s j, c j]` of the planes `(j, j + 1)`
(`Matrix.planeRotation`, embedded by `Matrix.adjacentEmbed`). Applied on the left to a matrix, the
last factor acts first: `adjacentRotationProd a n c s * X` sweeps the planes bottom-up, and its
transpose `(adjacentRotationProd a n c s)ᵀ * X`, the product of the transposed rotations in
decreasing order, sweeps them top-down. -/
noncomputable def adjacentRotationProd (a n : ℕ) (c s : ℕ → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  ((List.range' a n).map fun j => adjacentEmbed j !![c j, -s j; s j, c j]).prod

variable {a n : ℕ} {c s : ℕ → ℝ}

/-- The empty sweep is the identity. -/
@[simp]
theorem adjacentRotationProd_zero :
    (adjacentRotationProd a 0 c s : Matrix (Fin M) (Fin M) ℝ) = 1 := by
  simp [adjacentRotationProd]

/-- Peeling off the first rotation of a sweep. -/
theorem adjacentRotationProd_succ :
    (adjacentRotationProd a (n + 1) c s : Matrix (Fin M) (Fin M) ℝ) =
      adjacentEmbed a !![c a, -s a; s a, c a] * adjacentRotationProd (a + 1) n c s := by
  simp [adjacentRotationProd, List.range'_succ]

/-- Peeling off the last rotation of a sweep. -/
theorem adjacentRotationProd_succ' :
    (adjacentRotationProd a (n + 1) c s : Matrix (Fin M) (Fin M) ℝ) =
      adjacentRotationProd a n c s * adjacentEmbed (a + n) !![c (a + n), -s (a + n);
        s (a + n), c (a + n)] := by
  simp [adjacentRotationProd, List.range'_concat]

/-- A sweep depends only on the angles of its own planes. -/
theorem adjacentRotationProd_congr {c' s' : ℕ → ℝ}
    (h : ∀ j, a ≤ j → j < a + n → c j = c' j ∧ s j = s' j) :
    (adjacentRotationProd a n c s : Matrix (Fin M) (Fin M) ℝ) = adjacentRotationProd a n c' s' := by
  unfold adjacentRotationProd
  congr 1
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨h₁, h₂⟩ := List.mem_range'_1.1 hj
  obtain ⟨hc, hs⟩ := h j h₁ h₂
  rw [hc, hs]

/-- A sweep of rotations is orthogonal. -/
theorem adjacentRotationProd_mem_orthogonalGroup (h : ∀ j, c j ^ 2 + s j ^ 2 = 1) :
    (adjacentRotationProd a n c s : Matrix (Fin M) (Fin M) ℝ) ∈ orthogonalGroup (Fin M) ℝ := by
  refine Submonoid.list_prod_mem _ fun G hG => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hG
  unfold adjacentEmbed
  split_ifs
  · exact planeRotation_mem_orthogonalGroup (Fin.ne_of_val_ne (by simp)) (h j)
  · exact one_mem _

/-- The transposed rotation block. -/
private theorem rotationBlock_transpose (c s : ℝ) : !![c, -s; s, c]ᵀ = !![c, s; -s, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end AdjacentRotationProd

/-! ### The Hessenberg lemmas -/

section Hessenberg

variable {α : Type*} {M N : ℕ}

/-- **Bottom-up rotations of a triangular matrix give a Hessenberg matrix** ([golub2013matrix]
(6.5.2), and the row deletion of §6.5.3). For an upper trapezoidal `T : Matrix (Fin M) (Fin N) α`
and *any* `2 × 2` blocks `G j`, the product `P = E_b E_{b+1} ⋯ E_{b+n-1}` of their embeddings
`E_j` in the adjacent planes `(j, j + 1)` (the book's `J_1ᵀ ⋯ J_{n-1}ᵀ`, applied right to left)
makes `P T` vanish at `(i, l)` whenever `l + 1 < i` — `P T` is upper Hessenberg — and whenever
`l < i` and `l < b`: the columns before the first plane stay triangular. The invariant, by
induction on `n` from the left: the rows `b`, `b + 1` of `E_{b+1} ⋯ T` both vanish before
column `b`, so mixing them creates nothing there. -/
theorem prod_planeEmbed_mul_apply_eq_zero [Semiring α] {T : Matrix (Fin M) (Fin N) α}
    (hT : T.HasLowerBandwidthRect 0) (G : ℕ → Matrix (Fin 2) (Fin 2) α) (b n : ℕ) {i : Fin M}
    {l : Fin N} (h : (l : ℕ) + 1 < i ∨ (l : ℕ) < i ∧ (l : ℕ) < b) :
    (((List.range' b n).map fun j =>
      (adjacentEmbed j (G j) : Matrix (Fin M) (Fin M) α)).prod * T) i l = 0 := by
  induction n generalizing b i with
  | zero => simpa using hT i l (by omega)
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, List.prod_cons, Matrix.mul_assoc]
    by_cases hi : (i : ℕ) = b ∨ (i : ℕ) = b + 1
    · exact adjacentEmbed_mul_apply_eq_zero b (G b) _
        (fun r hr => ih (b + 1) (by omega)) hi
    · rw [adjacentEmbed_mul_apply_of_ne b (G b) _ (by omega) (by omega)]
      exact ih (b + 1) (by omega)

/-- **The square case of (6.5.2)**: a product of embeddings in the planes `(0, 1), (1, 2), …` in
increasing order, times an upper trapezoidal matrix, is upper Hessenberg. -/
theorem hasLowerBandwidthRect_prod_adjacentEmbed_mul [Semiring α] {T : Matrix (Fin M) (Fin N) α}
    (hT : T.HasLowerBandwidthRect 0) (G : ℕ → Matrix (Fin 2) (Fin 2) α) (n : ℕ) :
    (((List.range n).map fun j =>
      (adjacentEmbed j (G j) : Matrix (Fin M) (Fin M) α)).prod * T).HasLowerBandwidthRect 1 :=
  fun _ _ h => by
    rw [List.range_eq_range']
    exact prod_planeEmbed_mul_apply_eq_zero hT G 0 n (Or.inl h)

/-- **Any zeroing sweep triangularizes a Hessenberg matrix** ([golub2013matrix] §6.5.1–6.5.3,
"we compute Givens rotations … `G_{n−1}ᵀ ⋯ G_1ᵀ H₁ = R₁`"). Let `H : Matrix (Fin M) (Fin N) α`
be upper Hessenberg and already triangular in its first `a` columns, and let a sweep
`Hs 0 = H`, `Hs (t + 1) = E_{a+t} * Hs t` multiply by embeddings `E_j` of *arbitrary* blocks
`G j` in the planes `(j, j + 1)`, each step zeroing its target,
`Hs (t + 1) (a + t + 1) (a + t) = 0`,
for `a + t < L := min N (M − 1)`. Then `Hs (L − a)` is upper trapezoidal. The zeroing is a
hypothesis and not a choice of `(c, s)`, so any Givens routine instantiates the lemma; the
rectangular, parameterized form of the invariant behind `Matrix.hessenbergGivensQR_spec`. -/
theorem upperTrapezoidal_of_adjacentRotations [NonAssocSemiring α]
    {H : Matrix (Fin M) (Fin N) α} (hH : H.HasLowerBandwidthRect 1) {a : ℕ}
    (ha : ∀ (i : Fin M) (l : Fin N), (l : ℕ) < i → (l : ℕ) < a → H i l = 0)
    (G : ℕ → Matrix (Fin 2) (Fin 2) α) (Hs : ℕ → Matrix (Fin M) (Fin N) α) (h0 : Hs 0 = H)
    (hstep : ∀ t, a + t < min N (M - 1) → Hs (t + 1) =
      (adjacentEmbed (a + t) (G (a + t)) : Matrix (Fin M) (Fin M) α) * Hs t)
    (hzero : ∀ t, a + t < min N (M - 1) → ∀ (i : Fin M) (l : Fin N), (i : ℕ) = a + t + 1 →
      (l : ℕ) = a + t → Hs (t + 1) i l = 0) :
    (Hs (min N (M - 1) - a)).HasLowerBandwidthRect 0 := by
  have key : ∀ t, t ≤ min N (M - 1) - a → (Hs t).HasLowerBandwidthRect 1 ∧
      ∀ (i : Fin M) (l : Fin N), (l : ℕ) < i → (l : ℕ) < a + t → Hs t i l = 0 := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [h0]
      exact ⟨hH, fun i l h₁ h₂ => ha i l h₁ (by omega)⟩
    | succ t ih =>
      intro ht
      obtain ⟨ih₁, ih₂⟩ := ih (by omega)
      have hlt : a + t < min N (M - 1) := by omega
      have hz := hzero t hlt
      rw [hstep t hlt] at hz ⊢
      refine ⟨fun i l hil => ?_, fun i l hil hla => ?_⟩
      · by_cases hi : (i : ℕ) = a + t ∨ (i : ℕ) = a + t + 1
        · exact adjacentEmbed_mul_apply_eq_zero _ _ _
            (fun r hr => ih₂ r l (by omega) (by omega)) hi
        · rw [adjacentEmbed_mul_apply_of_ne _ _ _ (by omega) (by omega)]
          exact ih₁ i l hil
      · by_cases hi : (i : ℕ) = a + t ∨ (i : ℕ) = a + t + 1
        · by_cases hl : (l : ℕ) = a + t
          · exact hz i l (by omega) hl
          · exact adjacentEmbed_mul_apply_eq_zero _ _ _
              (fun r hr => ih₂ r l (by omega) (by omega)) hi
        · rw [adjacentEmbed_mul_apply_of_ne _ _ _ (by omega) (by omega)]
          by_cases hl : (l : ℕ) < a + t
          · exact ih₂ i l hil hl
          · exact ih₁ i l (by omega)
  intro i l hil
  have hi := i.isLt
  have hl := l.isLt
  exact (key _ le_rfl).2 i l (by omega) (by omega)

end Hessenberg

/-! ### Givens sweeps exist -/

section Givens

variable {M N : ℕ}

/-- **Bottom-up zeroing of a vector by a sweep of Givens rotations** ([golub2013matrix] §6.5.1,
"rotations `J_{n−1}, …, J_1` … such that `J_1ᵀ ⋯ J_{n−1}ᵀ w = ± ‖w‖₂ e₁`"): for every
`x : Fin M → ℝ` there are angles making the sweep `adjacentRotationProd b n c s` — whose last
plane `(b + n − 1, b + n)` acts first — annihilate the entries `b < i ≤ b + n` of `x`, leaving
the entries before `b` alone. Each rotation is the Givens pair of the two entries it mixes. -/
theorem exists_adjacentRotationProd_mulVec_eq_zero (x : Fin M → ℝ) (b n : ℕ) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      (∀ i : Fin M, b < (i : ℕ) → (i : ℕ) ≤ b + n →
        (adjacentRotationProd b n c s *ᵥ x) i = 0) ∧
      ∀ i : Fin M, (i : ℕ) < b → (adjacentRotationProd b n c s *ᵥ x) i = x i := by
  induction n generalizing b with
  | zero =>
    exact ⟨fun _ => 1, fun _ => 0, fun _ => by norm_num, fun i h₁ h₂ => by omega,
      fun i _ => by simp⟩
  | succ n ih =>
    obtain ⟨c, s, hcs, hz, hx⟩ := ih (b + 1)
    by_cases hb : b + 1 < M
    · obtain ⟨p, hp⟩ : ∃ p, p = givensPair ((adjacentRotationProd (b + 1) n c s *ᵥ x)
          ⟨b, by omega⟩) ((adjacentRotationProd (b + 1) n c s *ᵥ x) ⟨b + 1, hb⟩) := ⟨_, rfl⟩
      have hcongr : (adjacentRotationProd (b + 1) n (Function.update c b p.1)
          (Function.update s b (-p.2)) : Matrix (Fin M) (Fin M) ℝ) =
          adjacentRotationProd (b + 1) n c s :=
        adjacentRotationProd_congr fun j hj _ => by
          simp [Function.update_of_ne (show j ≠ b by omega)]
      have hP : (adjacentRotationProd b (n + 1) (Function.update c b p.1)
          (Function.update s b (-p.2)) : Matrix (Fin M) (Fin M) ℝ) *ᵥ x =
          adjacentEmbed b !![p.1, -(-p.2); -p.2, p.1] *ᵥ
            (adjacentRotationProd (b + 1) n c s *ᵥ x) := by
        rw [adjacentRotationProd_succ, ← mulVec_mulVec, hcongr, Function.update_self,
          Function.update_self]
      refine ⟨Function.update c b p.1, Function.update s b (-p.2), fun j => ?_,
        fun i h₁ h₂ => ?_, fun i hi => ?_⟩
      · by_cases hj : j = b
        · subst hj
          simpa [hp] using givensPair_sq_add_sq _ _
        · simpa [Function.update_of_ne hj] using hcs j
      · rw [hP]
        by_cases hi : (i : ℕ) = b + 1
        · obtain rfl : i = ⟨b + 1, hb⟩ := Fin.ext hi
          rw [adjacentEmbed_mulVec_apply_succ b _ hb]
          simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
            cons_val_fin_one, Fin.isValue]
          rw [hp]
          linear_combination (givensPair_fst_mul_add_snd_mul _ _).2
        · rw [adjacentEmbed_mulVec_apply_of_ne _ _ _ (by omega) hi]
          exact hz i (by omega) (by omega)
      · rw [hP, adjacentEmbed_mulVec_apply_of_ne _ _ _ (by omega) (by omega)]
        exact hx i (by omega)
    · refine ⟨c, s, hcs, fun i h₁ _ => by omega, fun i hi => ?_⟩
      rw [adjacentRotationProd_succ, adjacentEmbed_of_le _ (by omega), Matrix.one_mul]
      exact hx i (by omega)

/-- One step of a top-down sweep, on the left of a matrix: the transpose of the sweep through the
plane `(a + t, a + t + 1)` is that plane's transposed rotation times the transpose of the sweep
before it. -/
private theorem transpose_adjacentRotationProd_succ_mul (a t : ℕ) (c s : ℕ → ℝ)
    (X : Matrix (Fin M) (Fin N) ℝ) :
    (adjacentRotationProd a (t + 1) c s : Matrix (Fin M) (Fin M) ℝ)ᵀ * X =
      adjacentEmbed (a + t) !![c (a + t), s (a + t); -s (a + t), c (a + t)] *
        ((adjacentRotationProd a t c s)ᵀ * X) := by
  rw [adjacentRotationProd_succ', transpose_mul, Matrix.mul_assoc, adjacentEmbed_transpose,
    rotationBlock_transpose]

/-- **Givens triangularization of a rectangular Hessenberg matrix exists** ([golub2013matrix]
§6.5.1–6.5.3, after Algorithm 5.2.5): if `H : Matrix (Fin M) (Fin N) ℝ` is upper Hessenberg and
already triangular in its first `a` columns, there are angles `c j ^ 2 + s j ^ 2 = 1` such that
the sweep `J = G_a ⋯ G_{L−1}` of rotations in the planes `(j, j + 1)`, `L = min N (M − 1)`, makes
`Jᵀ H` upper trapezoidal (`J` is orthogonal, `Matrix.adjacentRotationProd_mem_orthogonalGroup`).
Each `G_j` is the Givens pair of the current entries `(j, j)`, `(j + 1, j)`; the rest is
`Matrix.upperTrapezoidal_of_adjacentRotations`. -/
theorem exists_rotations_triangularize_of_hessenberg {H : Matrix (Fin M) (Fin N) ℝ}
    (hH : H.HasLowerBandwidthRect 1) {a : ℕ}
    (ha : ∀ (i : Fin M) (l : Fin N), (l : ℕ) < i → (l : ℕ) < a → H i l = 0) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      ((adjacentRotationProd a (min N (M - 1) - a) c s : Matrix (Fin M) (Fin M) ℝ)ᵀ *
        H).HasLowerBandwidthRect 0 := by
  have key : ∀ t, ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧ ∀ t' < t,
      ∀ (i : Fin M) (l : Fin N), (i : ℕ) = a + t' + 1 → (l : ℕ) = a + t' →
        ((adjacentRotationProd a (t' + 1) c s : Matrix (Fin M) (Fin M) ℝ)ᵀ * H) i l = 0 := by
    intro t
    induction t with
    | zero => exact ⟨fun _ => 1, fun _ => 0, fun _ => by norm_num, fun t' ht' => by omega⟩
    | succ t ih =>
      obtain ⟨c, s, hcs, hz⟩ := ih
      by_cases hb : a + t + 1 < M ∧ a + t < N
      · obtain ⟨p, hp⟩ : ∃ p, p = givensPair
            (((adjacentRotationProd a t c s : Matrix (Fin M) (Fin M) ℝ)ᵀ * H) ⟨a + t, by omega⟩
              ⟨a + t, hb.2⟩)
            (((adjacentRotationProd a t c s : Matrix (Fin M) (Fin M) ℝ)ᵀ * H) ⟨a + t + 1, hb.1⟩
              ⟨a + t, hb.2⟩) := ⟨_, rfl⟩
        have hcongr : ∀ u ≤ t, (adjacentRotationProd a u (Function.update c (a + t) p.1)
            (Function.update s (a + t) p.2) : Matrix (Fin M) (Fin M) ℝ) =
            adjacentRotationProd a u c s :=
          fun u hu => adjacentRotationProd_congr fun j _ hj => by
            simp [Function.update_of_ne (show j ≠ a + t by omega)]
        refine ⟨Function.update c (a + t) p.1, Function.update s (a + t) p.2, fun j => ?_,
          fun t' ht' i l hi hl => ?_⟩
        · by_cases hj : j = a + t
          · subst hj
            simpa [hp] using givensPair_sq_add_sq _ _
          · simpa [Function.update_of_ne hj] using hcs j
        · rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with ht' | rfl
          · rw [hcongr (t' + 1) (by omega)]
            exact hz t' ht' i l hi hl
          · obtain rfl : i = ⟨a + t' + 1, hb.1⟩ := Fin.ext hi
            obtain rfl : l = ⟨a + t', hb.2⟩ := Fin.ext hl
            rw [transpose_adjacentRotationProd_succ_mul, hcongr t' le_rfl,
              adjacentEmbed_mul_apply_succ _ _ _ hb.1]
            simp only [Function.update_self, of_apply, cons_val', cons_val_zero, cons_val_one,
              empty_val', cons_val_fin_one, Fin.isValue]
            rw [hp]
            linear_combination (givensPair_fst_mul_add_snd_mul _ _).2
      · refine ⟨c, s, hcs, fun t' ht' i l hi hl => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with ht' | rfl
        · exact hz t' ht' i l hi hl
        · exact absurd ⟨by have := i.isLt; omega, by have := l.isLt; omega⟩ hb
  obtain ⟨c, s, hcs, hz⟩ := key (min N (M - 1) - a)
  exact ⟨c, s, hcs, upperTrapezoidal_of_adjacentRotations hH ha
    (fun j => !![c j, s j; -s j, c j]) (fun t => (adjacentRotationProd a t c s)ᵀ * H)
    (by simp) (fun t _ => transpose_adjacentRotationProd_succ_mul a t c s H)
    (fun t ht i l hi hl => hz t (by omega) i l hi hl)⟩

end Givens

/-! ### QR updating -/

section QR

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- The triangular factor of a full QR factorization is `Qᴴ A`. -/
theorem IsQR.conjTranspose_mul_eq {A : Matrix (Fin m) (Fin n) 𝕜} {Q R} (h : IsQR A Q R) :
    Qᴴ * A = R := by
  rw [← h.mul_eq, ← Matrix.mul_assoc, ← star_eq_conjTranspose,
    Unitary.star_mul_self_of_mem h.mem_unitaryGroup, Matrix.one_mul]

/-- The triangular factor of a full QR factorization is upper trapezoidal. -/
theorem IsQR.hasLowerBandwidthRect {A : Matrix (Fin m) (Fin n) 𝕜} {Q R} (h : IsQR A Q R) :
    R.HasLowerBandwidthRect 0 :=
  fun i j hij => h.apply_eq_zero i j (by simpa using hij)

/-- A unitary `Q` with `Qᴴ A` upper trapezoidal gives the full QR factorization `A = Q (Qᴴ A)`. -/
theorem isQR_conjTranspose_mul {A : Matrix (Fin m) (Fin n) 𝕜} {Q : Matrix (Fin m) (Fin m) 𝕜}
    (hQ : Q ∈ unitaryGroup (Fin m) 𝕜) (hR : (Qᴴ * A).HasLowerBandwidthRect 0) :
    IsQR A Q (Qᴴ * A) where
  mem_unitaryGroup := hQ
  apply_eq_zero i j hij := hR i j (by simpa using hij)
  mul_eq := by
    rw [← Matrix.mul_assoc, ← star_eq_conjTranspose, Unitary.mul_star_self_of_mem hQ,
      Matrix.one_mul]

/-- For real matrices the conjugate transpose of the orthogonal factor is its transpose. -/
private theorem transpose_mem_orthogonalGroup {P : Matrix (Fin m) (Fin m) ℝ}
    (hP : P ∈ orthogonalGroup (Fin m) ℝ) : Pᵀ ∈ orthogonalGroup (Fin m) ℝ := by
  simpa [star_eq_conjTranspose] using Unitary.star_mem hP

/-- **QR after a rank-one change** ([golub2013matrix] §6.5.1, (6.5.1)–(6.5.3)): if `A = Q R`
(`A` real and square) and `u v : Fin n → ℝ`, there are two sweeps of rotations in the adjacent
planes `(k, k + 1)`: `J = J_{n−2} ⋯ J_0` (the transpose of
`P = adjacentRotationProd 0 (n − 1) c s`),
with `Jᵀ (Qᵀ u)` a multiple of `e₀`, and `G = G_0 ⋯ G_{n−2}`, such that
`A + u vᵀ = (Q J G) (Gᵀ Jᵀ (R + (Qᵀ u) vᵀ))` is a full QR factorization. By (6.5.1)
`A + u vᵀ = Q (R + w vᵀ)`, `w = Qᵀ u`; `Jᵀ R` is upper Hessenberg
(`Matrix.prod_planeEmbed_mul_apply_eq_zero`) and `Jᵀ w vᵀ` lives in row `0`, so
`H₁ = Jᵀ (R + w vᵀ)` is upper Hessenberg (6.5.3), and `G` triangularizes it
(`Matrix.exists_rotations_triangularize_of_hessenberg`). -/
theorem exists_isQR_rankOne_update {A Q R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR A Q R)
    (u v : Fin n → ℝ) :
    ∃ c s c' s' : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧ (∀ j, c' j ^ 2 + s' j ^ 2 = 1) ∧
      (∀ i : Fin n, (i : ℕ) ≠ 0 → (adjacentRotationProd 0 (n - 1) c s *ᵥ (Qᵀ *ᵥ u)) i = 0) ∧
      IsQR (A + vecMulVec u v)
        (Q * (adjacentRotationProd 0 (n - 1) c s)ᵀ * adjacentRotationProd 0 (n - 1) c' s')
        ((adjacentRotationProd 0 (n - 1) c' s')ᵀ * adjacentRotationProd 0 (n - 1) c s *
          (R + vecMulVec (Qᵀ *ᵥ u) v)) := by
  obtain ⟨c, s, hcs, hz, -⟩ := exists_adjacentRotationProd_mulVec_eq_zero (Qᵀ *ᵥ u) 0 (n - 1)
  have hz' : ∀ i : Fin n, (i : ℕ) ≠ 0 →
      (adjacentRotationProd 0 (n - 1) c s *ᵥ (Qᵀ *ᵥ u)) i = 0 :=
    fun i hi => hz i (by omega) (by have := i.isLt; omega)
  have hH : ((adjacentRotationProd 0 (n - 1) c s : Matrix (Fin n) (Fin n) ℝ) *
      (R + vecMulVec (Qᵀ *ᵥ u) v)).HasLowerBandwidthRect 1 := by
    intro i l hil
    rw [Matrix.mul_add, add_apply, mul_vecMulVec, vecMulVec_apply, hz' i (by omega), zero_mul,
      add_zero]
    exact prod_planeEmbed_mul_apply_eq_zero h.hasLowerBandwidthRect
      (fun j => !![c j, -s j; s j, c j]) 0 (n - 1) (Or.inl hil)
  obtain ⟨c', s', hcs', hT⟩ := exists_rotations_triangularize_of_hessenberg hH (a := 0)
    (fun _ _ _ h => absurd h (Nat.not_lt_zero _))
  rw [show min n (n - 1) - 0 = n - 1 by omega] at hT
  refine ⟨c, s, c', s', hcs, hcs', hz', ?_⟩
  have hP := adjacentRotationProd_mem_orthogonalGroup (M := n) (a := 0) (n := n - 1) hcs
  have hG := adjacentRotationProd_mem_orthogonalGroup (M := n) (a := 0) (n := n - 1) hcs'
  have hQ : Q ∈ orthogonalGroup (Fin n) ℝ := h.mem_unitaryGroup
  refine ⟨mul_mem (mul_mem hQ (transpose_mem_orthogonalGroup hP)) hG,
    fun i j hij => ?_, ?_⟩
  · rw [Matrix.mul_assoc]
    exact hT i j (by simpa using hij)
  · rw [show Q * (adjacentRotationProd 0 (n - 1) c s)ᵀ * adjacentRotationProd 0 (n - 1) c' s' *
        ((adjacentRotationProd 0 (n - 1) c' s')ᵀ * adjacentRotationProd 0 (n - 1) c s *
          (R + vecMulVec (Qᵀ *ᵥ u) v)) =
        Q * ((adjacentRotationProd 0 (n - 1) c s)ᵀ *
          ((adjacentRotationProd 0 (n - 1) c' s' * (adjacentRotationProd 0 (n - 1) c' s')ᵀ) *
            adjacentRotationProd 0 (n - 1) c s)) * (R + vecMulVec (Qᵀ *ᵥ u) v) by
        simp only [Matrix.mul_assoc],
      (mem_orthogonalGroup_iff (Fin n) ℝ).1 hG, Matrix.one_mul,
      (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hP, Matrix.mul_one, Matrix.mul_add, h.mul_eq,
      mul_vecMulVec, mulVec_mulVec, (mem_orthogonalGroup_iff (Fin n) ℝ).1 hQ, one_mulVec]

/-- The index `k.succAbove j` is `j` or `j + 1`. -/
private theorem val_succAbove_le (k : Fin (n + 1)) (j : Fin n) : (k.succAbove j : ℕ) ≤ j + 1 := by
  unfold Fin.succAbove
  split_ifs <;> simp

private theorem le_val_succAbove (k : Fin (n + 1)) (j : Fin n) : (j : ℕ) ≤ k.succAbove j := by
  unfold Fin.succAbove
  split_ifs <;> simp

private theorem val_succAbove_of_lt {k : Fin (n + 1)} {j : Fin n} (h : (j : ℕ) < k) :
    (k.succAbove j : ℕ) = j := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), Fin.val_castSucc]

private theorem val_succAbove_of_le {k : Fin (n + 1)} {j : Fin n} (h : (k : ℕ) ≤ j) :
    (k.succAbove j : ℕ) = j + 1 := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h), Fin.val_succ]

/-- **Deleting a column leaves a Hessenberg matrix** ([golub2013matrix] §6.5.2): if `A = Q R` and
`Ã = A.submatrix id k.succAbove` is `A` with its `k`-th column deleted, then `Qᴴ Ã` is `R` with
its `k`-th column deleted, which is upper Hessenberg and still triangular in its first `k`
columns. -/
theorem IsQR.conjTranspose_mul_deleteColumn {A : Matrix (Fin m) (Fin (n + 1)) 𝕜} {Q R}
    (h : IsQR A Q R) (k : Fin (n + 1)) :
    Qᴴ * A.submatrix id k.succAbove = R.submatrix id k.succAbove ∧
      (R.submatrix id k.succAbove).HasLowerBandwidthRect 1 ∧
      ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < k →
        R.submatrix id k.succAbove i j = 0 := by
  refine ⟨?_, fun i j hij => h.apply_eq_zero i (k.succAbove j) ?_,
    fun i j hij hjk => h.apply_eq_zero i (k.succAbove j) ?_⟩
  · rw [← h.conjTranspose_mul_eq]
    ext i j
    simp [mul_apply]
  · have := val_succAbove_le k j
    omega
  · rw [val_succAbove_of_lt hjk]
    exact hij

/-- **QR after deleting a column** ([golub2013matrix] §6.5.2, `Q₁ = Q G_k ⋯ G_{n−1}`): if `A = Q R`
and `Ã` is `A` with its `k`-th column deleted, there is a sweep `G = G_k ⋯ G_{L−1}` of rotations
in the planes `(j, j + 1)`, `k ≤ j < L = min n (m − 1)`, with `Ã = (Q G) (Gᵀ Qᵀ Ã)` a full QR
factorization; `Qᵀ Ã` is `IsQR.conjTranspose_mul_deleteColumn`. -/
theorem IsQR.exists_deleteColumn {A : Matrix (Fin m) (Fin (n + 1)) ℝ} {Q R} (h : IsQR A Q R)
    (k : Fin (n + 1)) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      IsQR (A.submatrix id k.succAbove) (Q * adjacentRotationProd k (min n (m - 1) - k) c s)
        ((adjacentRotationProd k (min n (m - 1) - k) c s)ᵀ * R.submatrix id k.succAbove) := by
  obtain ⟨h₁, h₂, h₃⟩ := h.conjTranspose_mul_deleteColumn k
  obtain ⟨c, s, hcs, hT⟩ := exists_rotations_triangularize_of_hessenberg h₂ h₃
  refine ⟨c, s, hcs, ?_⟩
  have hG := adjacentRotationProd_mem_orthogonalGroup (M := m) (a := k)
    (n := min n (m - 1) - k) hcs
  have e : (Q * adjacentRotationProd k (min n (m - 1) - k) c s)ᴴ * A.submatrix id k.succAbove =
      (adjacentRotationProd k (min n (m - 1) - k) c s)ᵀ * R.submatrix id k.succAbove := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h₁, conjTranspose_eq_transpose_of_trivial]
  have := isQR_conjTranspose_mul (mul_mem h.mem_unitaryGroup hG) (by rw [e]; exact hT)
  rwa [e] at this

/-- Multiplying a matrix with an inserted column: `P [A₁ | z | A₂] = [P A₁ | P z | P A₂]`. -/
theorem mul_of_insertNth {α l : Type*} [NonUnitalNonAssocSemiring α] (P : Matrix l (Fin m) α)
    (z : Fin m → α) (A : Matrix (Fin m) (Fin n) α) (k : Fin (n + 1)) :
    P * of (fun i => Fin.insertNth k (z i) (A i)) =
      of fun i => Fin.insertNth k ((P *ᵥ z) i) ((P * A) i) := by
  ext i j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove k j
  · simp [mul_apply, mulVec, dotProduct]
  · simp [mul_apply]

/-- **Inserting a column leaves a spike** ([golub2013matrix] §6.5.2): if `A = Q R` and `Ã` is `A`
with `z` inserted as column `k`, then `Qᴴ Ã` is `R` with `Qᴴ z` inserted as column `k`: upper
trapezoidal except in column `k`, below the diagonal. -/
theorem IsQR.conjTranspose_mul_insertColumn {A : Matrix (Fin m) (Fin n) 𝕜} {Q R}
    (h : IsQR A Q R) (z : Fin m → 𝕜) (k : Fin (n + 1)) :
    Qᴴ * of (fun i => Fin.insertNth k (z i) (A i)) =
        of (fun i => Fin.insertNth k ((Qᴴ *ᵥ z) i) (R i)) ∧
      ∀ (i : Fin m) (j : Fin (n + 1)), (j : ℕ) < i → j ≠ k →
        (Qᴴ * of fun i => Fin.insertNth k (z i) (A i)) i j = 0 := by
  have e : Qᴴ * of (fun i => Fin.insertNth k (z i) (A i)) =
      of (fun i => Fin.insertNth k ((Qᴴ *ᵥ z) i) (R i)) := by
    rw [mul_of_insertNth, h.conjTranspose_mul_eq]
  refine ⟨e, fun i j hij hjk => ?_⟩
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hjk
  rw [e, of_apply, Fin.insertNth_apply_succAbove]
  exact h.apply_eq_zero i j (by have := le_val_succAbove k j; omega)

/-- **QR after inserting a column** ([golub2013matrix] §6.5.2, the rotations `J_{m−1}, …, J_{k+1}`):
if `A = Q R` and `Ã` is `A` with `z` inserted as column `k`, there is a sweep of rotations in the
planes `(j, j + 1)`, `k ≤ j < m − 1`, applied bottom-up
(`P = adjacentRotationProd k (m − 1 − k) c s`, the book's `Jᵀ`), zeroing the spike of `Qᵀ Ã`
below row `k`, with `Ã = (Q Pᵀ) (P Qᵀ Ã)` a full QR factorization. The rotations mix rows `≥ k`
only, where the other columns of `Qᵀ Ã` vanish or are upper Hessenberg, so no fill-in occurs
(`Matrix.prod_planeEmbed_mul_apply_eq_zero`). -/
theorem IsQR.exists_insertColumn {A : Matrix (Fin m) (Fin n) ℝ} {Q R} (h : IsQR A Q R)
    (z : Fin m → ℝ) (k : Fin (n + 1)) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      IsQR (of fun i => Fin.insertNth k (z i) (A i))
        (Q * (adjacentRotationProd k (m - 1 - k) c s)ᵀ)
        (adjacentRotationProd k (m - 1 - k) c s * (Qᵀ * of fun i => Fin.insertNth k (z i) (A i)))
        := by
  obtain ⟨c, s, hcs, hz, -⟩ := exists_adjacentRotationProd_mulVec_eq_zero (Qᵀ *ᵥ z) k (m - 1 - k)
  refine ⟨c, s, hcs, ?_⟩
  have hP := adjacentRotationProd_mem_orthogonalGroup (M := m) (a := k) (n := m - 1 - k) hcs
  have hQt : Qᴴ = Qᵀ := conjTranspose_eq_transpose_of_trivial Q
  obtain ⟨e, -⟩ := h.conjTranspose_mul_insertColumn z k
  rw [hQt] at e
  have e' : (Q * (adjacentRotationProd k (m - 1 - k) c s)ᵀ)ᴴ *
      (of fun i => Fin.insertNth k (z i) (A i)) =
      adjacentRotationProd k (m - 1 - k) c s * (Qᵀ * of fun i => Fin.insertNth k (z i) (A i)) := by
    rw [conjTranspose_mul, conjTranspose_eq_transpose_of_trivial, transpose_transpose, hQt,
      Matrix.mul_assoc]
  have hT : ((adjacentRotationProd k (m - 1 - k) c s : Matrix (Fin m) (Fin m) ℝ) *
      (Qᵀ * of fun i => Fin.insertNth k (z i) (A i))).HasLowerBandwidthRect 0 := by
    intro i j hij
    rw [e, mul_of_insertNth, of_apply]
    obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove k j
    · rw [Fin.insertNth_apply_same]
      exact hz i (by omega) (by have := i.isLt; omega)
    · rw [Fin.insertNth_apply_succAbove]
      refine prod_planeEmbed_mul_apply_eq_zero h.hasLowerBandwidthRect
        (fun j => !![c j, -s j; s j, c j]) k (m - 1 - k) ?_
      rcases lt_or_ge (j : ℕ) k with hjk | hjk
      · rw [val_succAbove_of_lt hjk] at hij
        exact Or.inr ⟨by omega, hjk⟩
      · rw [val_succAbove_of_le hjk] at hij
        exact Or.inl (by omega)
  have := isQR_conjTranspose_mul (mul_mem h.mem_unitaryGroup (transpose_mem_orthogonalGroup hP))
    (by rw [e']; exact hT)
  rwa [e'] at this

end QR

/-! ### Rows: `diag(a, Q)` and the cyclic row permutation -/

section ConsDiag

variable {α : Type*} {m n p : ℕ}

/-! The tuple lemmas `Fin.cons_zero`, `Fin.cons_succ`, `Fin.insertNth_apply_same` and
`Fin.insertNth_apply_succAbove` do not fire on a tuple of rows given as a `Matrix`, whose type is
not syntactically a function type; these are their row forms. -/

@[simp]
private theorem cons_rows_zero (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α) (j : Fin n) :
    (Fin.cons w A : Fin (m + 1) → Fin n → α) 0 j = w j := rfl

@[simp]
private theorem cons_rows_succ (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α) (i : Fin m)
    (j : Fin n) : (Fin.cons w A : Fin (m + 1) → Fin n → α) i.succ j = A i j := rfl

@[simp]
private theorem insertNth_rows_same (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α)
    (k : Fin (m + 1)) (j : Fin n) :
    (Fin.insertNth k w A : Fin (m + 1) → Fin n → α) k j = w j := by
  have h := Fin.insertNth_apply_same (α := fun _ => Fin n → α) k w (fun i => A i)
  exact congrFun h j

@[simp]
private theorem insertNth_rows_succAbove (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α)
    (k : Fin (m + 1)) (i : Fin m) (j : Fin n) :
    (Fin.insertNth k w A : Fin (m + 1) → Fin n → α) (k.succAbove i) j = A i j := by
  have h := Fin.insertNth_apply_succAbove (α := fun _ => Fin n → α) k w (fun i => A i) i
  exact congrFun h j

/-- **The block diagonal matrix `diag(a, Q)`** on `Fin (m + 1) × Fin (n + 1)`: `a` in the corner
`(0, 0)`, `Q` on the trailing block, zero elsewhere ([golub2013matrix] §6.5.3, `diag(1, Q)`). -/
def consDiag [Zero α] (a : α) (Q : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) α :=
  of (Fin.cons (Fin.cons a 0) fun i => Fin.cons 0 (Q i))

section Apply

variable [Zero α] (a : α) (Q : Matrix (Fin m) (Fin n) α)

/-- The corner entry of `diag(a, Q)`. -/
@[simp] theorem consDiag_zero_zero : consDiag a Q 0 0 = a := rfl

/-- The first row of `diag(a, Q)` vanishes off the corner. -/
@[simp] theorem consDiag_zero_succ (j : Fin n) : consDiag a Q 0 j.succ = 0 := rfl

/-- The first column of `diag(a, Q)` vanishes off the corner. -/
@[simp] theorem consDiag_succ_zero (i : Fin m) : consDiag a Q i.succ 0 = 0 := rfl

/-- The trailing block of `diag(a, Q)` is `Q`. -/
@[simp] theorem consDiag_succ_succ (i : Fin m) (j : Fin n) : consDiag a Q i.succ j.succ = Q i j :=
  rfl

end Apply

/-- `diag(a, Q) [wᵀ; X] = [a wᵀ; Q X]`. -/
theorem consDiag_mul_of_cons [NonUnitalNonAssocSemiring α] (a : α) (Q : Matrix (Fin m) (Fin n) α)
    (w : Fin p → α) (X : Matrix (Fin n) (Fin p) α) :
    consDiag a Q * of (Fin.cons w X) = of (Fin.cons (a • w) (Q * X)) := by
  ext i j
  induction i using Fin.cases <;> simp [mul_apply, Fin.sum_univ_succ]

/-- `diag(a, Q) diag(b, Q') = diag(a b, Q Q')`. -/
theorem consDiag_mul_consDiag [NonUnitalNonAssocSemiring α] (a b : α)
    (Q : Matrix (Fin m) (Fin n) α) (Q' : Matrix (Fin n) (Fin p) α) :
    consDiag a Q * consDiag b Q' = consDiag (a * b) (Q * Q') := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [mul_apply, Fin.sum_univ_succ]

/-- `diag(1, 1) = 1`. -/
@[simp]
theorem consDiag_one [Zero α] [One α] : consDiag (1 : α) (1 : Matrix (Fin m) (Fin m) α) = 1 := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- `diag(a, Q)ᴴ = diag(a⋆, Qᴴ)`. -/
theorem conjTranspose_consDiag [AddMonoid α] [StarAddMonoid α] (a : α)
    (Q : Matrix (Fin m) (Fin n) α) : (consDiag a Q)ᴴ = consDiag (star a) Qᴴ := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;> simp

/-- `diag(a, Q)` is unitary when `a` is and `Q` is. -/
theorem consDiag_mem_unitaryGroup [CommRing α] [StarRing α] {a : α} (ha : a * star a = 1)
    {Q : Matrix (Fin m) (Fin m) α} (hQ : Q ∈ unitaryGroup (Fin m) α) :
    consDiag a Q ∈ unitaryGroup (Fin (m + 1)) α := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_consDiag, consDiag_mul_consDiag,
    ha, ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hQ, consDiag_one]

/-- Permuting the rows of a unitary matrix keeps it unitary. -/
theorem submatrix_mem_unitaryGroup [CommRing α] [StarRing α] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {U : Matrix ι ι α} (hU : U ∈ unitaryGroup ι α) (e : ι ≃ ι) :
    U.submatrix e id ∈ unitaryGroup ι α := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_submatrix,
    show U.submatrix e id * Uᴴ.submatrix id e = (U * Uᴴ).submatrix e e from
      submatrix_mul_equiv U Uᴴ e (Equiv.refl ι) e, ← star_eq_conjTranspose,
    mem_unitaryGroup_iff.1 hU, submatrix_one_equiv]

/-- Permuting the rows of a left factor permutes the rows of the product. -/
theorem submatrix_id_mul [NonUnitalNonAssocSemiring α] {ι κ ι' : Type*} [Fintype ι]
    (X : Matrix ι' ι α) (Y : Matrix ι κ α) {ι'' : Type*} (e : ι'' → ι') :
    X.submatrix e id * Y = (X * Y).submatrix e id := by
  ext i j
  simp [mul_apply]

/-- **Moving an inserted row to the top**: with `σ = (Fin.cycleRange k)⁻¹` (`σ 0 = k`,
`σ (j + 1) = k.succAbove j`), the rows of `Fin.insertNth k w A` permuted by `σ` are `[wᵀ; A]`
([golub2013matrix] §6.5.3, the permutation `P`). -/
theorem submatrix_insertNth_cycleRange (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α)
    (k : Fin (m + 1)) :
    (of (Fin.insertNth k w A) : Matrix (Fin (m + 1)) (Fin n) α).submatrix
      (Fin.cycleRange k).symm id = of (Fin.cons w A) := by
  ext i j
  induction i using Fin.cases <;> simp [Fin.cycleRange_symm_succ]

end ConsDiag

section QRRows

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- **Inserting a row leaves a Hessenberg matrix** ([golub2013matrix] §6.5.3): if `A = Q R` and
`Ã = Fin.insertNth k w A` is `A` with the row `wᵀ` inserted at position `k`, and `P` moves row `k`
to the top (`Matrix.submatrix_insertNth_cycleRange`), then `diag(1, Qᴴ) P Ã = [wᵀ; R]`, which is
upper Hessenberg. -/
theorem IsQR.conjTranspose_mul_insertRow {A : Matrix (Fin m) (Fin n) 𝕜} {Q R} (h : IsQR A Q R)
    (w : Fin n → 𝕜) (k : Fin (m + 1)) :
    consDiag 1 Qᴴ * (of (Fin.insertNth k w A)).submatrix (Fin.cycleRange k).symm id =
        of (Fin.cons w R) ∧
      (of (Fin.cons w R) : Matrix (Fin (m + 1)) (Fin n) 𝕜).HasLowerBandwidthRect 1 := by
  refine ⟨by rw [submatrix_insertNth_cycleRange, consDiag_mul_of_cons, one_smul,
    h.conjTranspose_mul_eq], fun i j hij => ?_⟩
  induction i using Fin.cases with
  | zero => simp at hij
  | succ i =>
    simp only [of_apply, cons_rows_succ]
    exact h.apply_eq_zero i j (by simp at hij; omega)

/-- **QR after inserting a row** ([golub2013matrix] §6.5.3, `Q₁ = diag(1, Q) J₁ ⋯ J_n`): if
`A = Q R` and `Ã` is `A` with the row `wᵀ` inserted at position `k`, there is a sweep
`J = J_0 ⋯ J_{L−1}` of rotations in the planes `(j, j + 1)`, `L = min n m`, with
`Ã = (Pᵀ diag(1, Q) J) (Jᵀ [wᵀ; R])` a full QR factorization, `Pᵀ` the row permutation
`Fin.cycleRange k` putting the top row back at position `k`. -/
theorem IsQR.exists_insertRow {A : Matrix (Fin m) (Fin n) ℝ} {Q R} (h : IsQR A Q R)
    (w : Fin n → ℝ) (k : Fin (m + 1)) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      IsQR (of (Fin.insertNth k w A))
        ((consDiag 1 Q * adjacentRotationProd 0 (min n m) c s).submatrix (Fin.cycleRange k) id)
        ((adjacentRotationProd 0 (min n m) c s)ᵀ * of (Fin.cons w R)) := by
  obtain ⟨-, hH⟩ := h.conjTranspose_mul_insertRow w k
  obtain ⟨c, s, hcs, hT⟩ := exists_rotations_triangularize_of_hessenberg hH (a := 0)
    (fun _ _ _ h => absurd h (Nat.not_lt_zero _))
  rw [show min n (m + 1 - 1) - 0 = min n m by omega] at hT
  have hG := adjacentRotationProd_mem_orthogonalGroup (M := m + 1) (a := 0) (n := min n m) hcs
  refine ⟨c, s, hcs, submatrix_mem_unitaryGroup (mul_mem (consDiag_mem_unitaryGroup
    (by simp) h.mem_unitaryGroup) hG) _, fun i j hij => hT i j (by simpa using hij), ?_⟩
  rw [submatrix_id_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (adjacentRotationProd 0 (min n m) c s),
    (mem_orthogonalGroup_iff _ ℝ).1 hG, Matrix.one_mul, consDiag_mul_of_cons, one_smul, h.mul_eq,
    ← submatrix_insertNth_cycleRange w A k, submatrix_submatrix, Equiv.symm_comp_self,
    Function.id_comp, submatrix_id_id]

/-- **QR after deleting the first row** ([golub2013matrix] §6.5.3): if `A = Q R` with
`A : Matrix (Fin (m + 1)) (Fin n) ℝ`, there are rotations `G = G_{m−1} ⋯ G_0` in the planes
`(j, j + 1)` (`Gᵀ = adjacentRotationProd 0 m c s`, zeroing the first row `q` of `Q` bottom-up,
`Gᵀ q = a e₀`) such that `Q G = diag(a, Q₁)` with `a = ±1`, `Gᵀ R = [vᵀ; R₁]`, and
`A₁ = Q₁ R₁` is a full QR factorization of `A` with its first row deleted. `Gᵀ R` is upper
Hessenberg (`Matrix.prod_planeEmbed_mul_apply_eq_zero`), so `R₁` is upper trapezoidal; the first
row of the orthogonal `Q G` is `a e₀ᵀ`, which forces its first column to be `a e₀`. -/
theorem IsQR.exists_deleteFirstRow {A : Matrix (Fin (m + 1)) (Fin n) ℝ} {Q R} (h : IsQR A Q R) :
    ∃ (c s : ℕ → ℝ) (a : ℝ) (Q₁ : Matrix (Fin m) (Fin m) ℝ) (v : Fin n → ℝ)
      (R₁ : Matrix (Fin m) (Fin n) ℝ), (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧ a ^ 2 = 1 ∧
      Q * (adjacentRotationProd 0 m c s)ᵀ = consDiag a Q₁ ∧
      adjacentRotationProd 0 m c s * R = of (Fin.cons v R₁) ∧
      IsQR (A.submatrix Fin.succ id) Q₁ R₁ := by
  obtain ⟨c, s, hcs, hz, -⟩ := exists_adjacentRotationProd_mulVec_eq_zero (fun j => Q 0 j) 0 m
  have hP := adjacentRotationProd_mem_orthogonalGroup (M := m + 1) (a := 0) (n := m) hcs
  have hQ : Q ∈ orthogonalGroup (Fin (m + 1)) ℝ := h.mem_unitaryGroup
  have hX : Q * (adjacentRotationProd 0 m c s)ᵀ ∈ orthogonalGroup (Fin (m + 1)) ℝ :=
    mul_mem hQ (transpose_mem_orthogonalGroup hP)
  set X := Q * (adjacentRotationProd 0 m c s)ᵀ with hXdef
  have hrow : ∀ j : Fin m, X 0 j.succ = 0 := fun j => by
    have e : X 0 j.succ = (adjacentRotationProd 0 m c s *ᵥ fun r => Q 0 r) j.succ := by
      simp [hXdef, mul_apply, mulVec, dotProduct, mul_comm]
    rw [e]
    exact hz j.succ (by simp) (by simp)
  have hXX := (mem_orthogonalGroup_iff _ ℝ).1 hX
  have hXX' := (mem_orthogonalGroup_iff' _ ℝ).1 hX
  have ha : X 0 0 ^ 2 = 1 := by
    have := congrFun (congrFun hXX 0) 0
    simpa [mul_apply, Fin.sum_univ_succ, hrow, sq] using this
  have hcol : ∀ i : Fin m, X i.succ 0 = 0 := by
    have h1 := congrFun (congrFun hXX' 0) 0
    simp only [mul_apply, transpose_apply, Fin.sum_univ_succ, one_apply_eq] at h1
    have h2 : ∑ i : Fin m, X i.succ 0 * X i.succ 0 = 0 := by nlinarith
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (X i.succ 0))).1 h2 i
      (Finset.mem_univ _)
    exact mul_self_eq_zero.1 this
  have hXcons : X = consDiag (X 0 0) (X.submatrix Fin.succ Fin.succ) := by
    ext i j
    induction i using Fin.cases <;> induction j using Fin.cases <;> simp [hrow, hcol]
  have hQ₁ : X.submatrix Fin.succ Fin.succ ∈ orthogonalGroup (Fin m) ℝ := by
    rw [mem_orthogonalGroup_iff]
    have := hXX
    rw [hXcons, ← conjTranspose_eq_transpose_of_trivial, conjTranspose_consDiag,
      consDiag_mul_consDiag, ← consDiag_one] at this
    ext i j
    simpa [conjTranspose_eq_transpose_of_trivial] using congrFun (congrFun this i.succ) j.succ
  set H := adjacentRotationProd 0 m c s * R with hHdef
  have hH : H.HasLowerBandwidthRect 1 := fun i l hil =>
    prod_planeEmbed_mul_apply_eq_zero h.hasLowerBandwidthRect
      (fun j => !![c j, -s j; s j, c j]) 0 m (Or.inl hil)
  have hHcons : H = of (Fin.cons (H 0) (H.submatrix Fin.succ id)) := by
    ext i j
    induction i using Fin.cases <;> rfl
  refine ⟨c, s, X 0 0, X.submatrix Fin.succ Fin.succ, H 0, H.submatrix Fin.succ id, hcs, ha,
    hXcons, hHcons, hQ₁, fun i j hij => hH i.succ j (by simp; omega), ?_⟩
  have hA : A = X * H := by
    rw [hXdef, hHdef, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adjacentRotationProd 0 m c s),
      (mem_orthogonalGroup_iff' _ ℝ).1 hP, Matrix.one_mul, h.mul_eq]
  rw [hA]
  ext i j
  simp [mul_apply, Fin.sum_univ_succ, hcol]

/-- **QR after deleting any row** ([golub2013matrix] §6.5.3, "the procedure is similar when an
arbitrary row is deleted"): if `A = Q R` with `A : Matrix (Fin (m + 1)) (Fin n) ℝ`, `k` a row, and
`P` the cyclic permutation moving row `k` to the top, the update of
`IsQR.exists_deleteFirstRow` applied to `P A = (P Q) R` gives a full QR factorization
`A₁ = Q₁ R₁` of `A` with its `k`-th row deleted. -/
theorem IsQR.exists_deleteRow {A : Matrix (Fin (m + 1)) (Fin n) ℝ} {Q R} (h : IsQR A Q R)
    (k : Fin (m + 1)) :
    ∃ (c s : ℕ → ℝ) (a : ℝ) (Q₁ : Matrix (Fin m) (Fin m) ℝ) (v : Fin n → ℝ)
      (R₁ : Matrix (Fin m) (Fin n) ℝ), (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧ a ^ 2 = 1 ∧
      Q.submatrix (Fin.cycleRange k).symm id * (adjacentRotationProd 0 m c s)ᵀ = consDiag a Q₁ ∧
      adjacentRotationProd 0 m c s * R = of (Fin.cons v R₁) ∧
      IsQR (A.submatrix k.succAbove id) Q₁ R₁ := by
  have h' : IsQR (A.submatrix (Fin.cycleRange k).symm id) (Q.submatrix (Fin.cycleRange k).symm id)
      R := ⟨submatrix_mem_unitaryGroup h.mem_unitaryGroup _, h.apply_eq_zero,
        by rw [submatrix_id_mul, h.mul_eq]⟩
  obtain ⟨c, s, a, Q₁, v, R₁, h₁, h₂, h₃, h₄, h₅⟩ := h'.exists_deleteFirstRow
  refine ⟨c, s, a, Q₁, v, R₁, h₁, h₂, h₃, h₄, ?_⟩
  rwa [submatrix_submatrix, Function.id_comp,
    show (⇑(Fin.cycleRange k).symm ∘ Fin.succ) = k.succAbove from
      funext (Fin.cycleRange_symm_succ k)] at h₅

end QRRows

/-! ### The stacked matrix `[H; zᵀ]` and its Gram matrices -/

section Stacked

variable {α : Type*} [CommRing α] {m n p : Type*} [Fintype m]

/-- The Gram matrix of a single row is `z zᵀ`. -/
private theorem transpose_replicateRow_mul_self (z : n → α) :
    (replicateRow Unit z)ᵀ * replicateRow Unit z = vecMulVec z z := by
  ext i j
  simp [mul_apply, vecMulVec_apply]

/-- **The stacked Gram matrix** ([golub2013matrix] (6.5.6)): appending the row `zᵀ` to `H` adds
`z zᵀ` to its Gram matrix, `[H; zᵀ]ᵀ [H; zᵀ] = Hᵀ H + z zᵀ`. -/
theorem transpose_mul_self_fromRows (H : Matrix m n α) (z : n → α) :
    (fromRows H (replicateRow Unit z))ᵀ * fromRows H (replicateRow Unit z) =
      Hᵀ * H + vecMulVec z z := by
  rw [transpose_fromRows, fromCols_mul_fromRows, transpose_replicateRow_mul_self]

/-- **The signed stacked Gram matrix** ([golub2013matrix] (6.5.10)): with the signature
`S = diag(I, −1)` (`LieAlgebra.Orthogonal.indefiniteDiagonal m Unit`),
`[H; zᵀ]ᵀ S [H; zᵀ] = Hᵀ H − z zᵀ`. -/
theorem transpose_mul_indefiniteDiagonal_mul_fromRows [DecidableEq m] (H : Matrix m n α)
    (z : n → α) :
    (fromRows H (replicateRow Unit z))ᵀ * LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α *
        fromRows H (replicateRow Unit z) = Hᵀ * H - vecMulVec z z := by
  have hS : LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α * fromRows H (replicateRow Unit z) =
      fromRows H (-replicateRow Unit z) := by
    ext (i | u) j <;> simp [LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_mul]
  rw [Matrix.mul_assoc, hS, transpose_fromRows, fromCols_mul_fromRows, Matrix.mul_neg,
    transpose_replicateRow_mul_self, sub_eq_add_neg]

variable [DecidableEq m] [Fintype p] [DecidableEq p]

/-- **An orthogonal reduction preserves the Gram matrix** ([golub2013matrix] (6.5.7) ⇒
`Ã = RᵀR`): if `Q` is orthogonal and `Qᵀ M = [R; 0]`, then `Mᵀ M = Rᵀ R`. (The book prints
`Ã = RRᵀ`, a typo for `RᵀR`; it concludes `G̃ = Rᵀ` correctly.) -/
theorem transpose_mul_self_eq_of_mem_orthogonalGroup {Q : Matrix (m ⊕ p) (m ⊕ p) α}
    (hQ : Q ∈ orthogonalGroup (m ⊕ p) α) {M : Matrix (m ⊕ p) n α} {R : Matrix m n α}
    (h : Qᵀ * M = fromRows R 0) : Mᵀ * M = Rᵀ * R := by
  have e : Mᵀ * M = (Qᵀ * M)ᵀ * (Qᵀ * M) := by
    rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Q,
      (mem_orthogonalGroup_iff _ α).1 hQ, Matrix.one_mul]
  rw [e, h, transpose_fromRows, fromCols_mul_fromRows, transpose_zero, Matrix.zero_mul,
    add_zero]

/-- A `J`-orthogonal reduction of a stacked matrix preserves its signed Gram matrix: if
`Hyᵀ [H; zᵀ] = [R; z'ᵀ]` with `Hy` `S`-orthogonal, then `Hᵀ H − z zᵀ = Rᵀ R − z' z'ᵀ`. -/
theorem transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows
    {Hy : Matrix (m ⊕ Unit) (m ⊕ Unit) α}
    (hHy : IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α) Hy)
    {H R : Matrix m n α} {z z' : n → α}
    (h : Hyᵀ * fromRows H (replicateRow Unit z) = fromRows R (replicateRow Unit z')) :
    Hᵀ * H - vecMulVec z z = Rᵀ * R - vecMulVec z' z' := by
  rw [← transpose_mul_indefiniteDiagonal_mul_fromRows,
    ← transpose_mul_indefiniteDiagonal_mul_fromRows, ← h, transpose_mul, transpose_transpose]
  conv_lhs => rw [← hHy]
  simp only [Matrix.mul_assoc]

/-- **A `J`-orthogonal reduction downdates the Gram matrix** ([golub2013matrix]
(6.5.10)–(6.5.12)): with `S = diag(I, −1)`, if `Hy` is `S`-orthogonal and `Hyᵀ [H; zᵀ] = [R; 0]`,
then `Hᵀ H − z zᵀ = Rᵀ R`. -/
theorem transpose_mul_self_sub_eq_of_isJOrthogonal {Hy : Matrix (m ⊕ Unit) (m ⊕ Unit) α}
    (hHy : IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α) Hy)
    {H R : Matrix m n α} {z : n → α}
    (h : Hyᵀ * fromRows H (replicateRow Unit z) = fromRows R 0) :
    Hᵀ * H - vecMulVec z z = Rᵀ * R := by
  rw [transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows hHy (z' := 0)
    (by rw [h, replicateRow_zero]), vecMulVec_zero, sub_zero]

end Stacked

section RotateStep

variable {α : Type*} [CommRing α] {n : Type*} [Fintype n] [LinearOrder n]

/-- **One step of a Cholesky update or downdate keeps the triangular shape** ([golub2013matrix]
§6.5.4, the zeroing sequence `Q₁, Q₂, Q₃` and Theorem 6.5.1's first rotation): for `R` upper
triangular, `z` vanishing before `k`, and *any* `2 × 2` block `G`, embedding `G` in the plane of
the row `k` and the appended row gives again a stacked matrix `[R'; z'ᵀ]`, with `R'` upper
triangular, equal to `R` outside row `k`, and `z'` vanishing before `k`; row `k` of `R'` and the
new last row are the combinations `G [R_k; zᵀ]`. Rows `k` and last are both zero before column
`k`. Serves both the Givens (update) and the hyperbolic (downdate) sweeps. -/
theorem fromRows_rotate_step {R : Matrix n n α} (hR : R.IsUpperTriangular) {z : n → α} {k : n}
    (hz : ∀ j < k, z j = 0) (G : Matrix (Fin 2) (Fin 2) α) :
    ∃ (R' : Matrix n n α) (z' : n → α),
      planeEmbed (Sum.inl k) (Sum.inr ()) G * fromRows R (replicateRow Unit z) =
        fromRows R' (replicateRow Unit z') ∧
      R'.IsUpperTriangular ∧ (∀ j < k, z' j = 0) ∧ (∀ i, i ≠ k → R' i = R i) ∧
      (∀ j, R' k j = G 0 0 * R k j + G 0 1 * z j) ∧ ∀ j, z' j = G 1 0 * R k j + G 1 1 * z j := by
  have hne : (Sum.inl k : n ⊕ Unit) ≠ Sum.inr () := Sum.inl_ne_inr
  set M := planeEmbed (Sum.inl k) (Sum.inr ()) G * fromRows R (replicateRow Unit z) with hM
  have hinl : ∀ i j, M (Sum.inl i) j =
      if i = k then G 0 0 * R k j + G 0 1 * z j else R i j := fun i j => by
    rw [hM, planeEmbed_mul_apply_rect G hne]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik]
  have hinr : ∀ j, M (Sum.inr ()) j = G 1 0 * R k j + G 1 1 * z j := fun j => by
    rw [hM, planeEmbed_mul_apply_rect G hne]
    simp
  refine ⟨M.toRows₁, fun j => M (Sum.inr ()) j, ?_, fun i j hji => ?_, fun j hj => ?_,
    fun i hik => funext fun j => ?_, fun j => ?_, hinr⟩
  · ext (i | u) j
    · rfl
    · rfl
  · rw [toRows₁_apply, hinl]
    split_ifs with hik
    · subst hik
      rw [hR hji, hz j hji]
      ring
    · exact hR hji
  · change M (Sum.inr ()) j = 0
    rw [hinr, hR hj, hz j hj]
    ring
  · rw [toRows₁_apply, hinl, ite_eq_right hik]
  · rw [toRows₁_apply, hinl, ite_eq_left rfl]

end RotateStep

/-! ### Cholesky updating and downdating -/

section CholeskyUpdate

/-- **Sign normalization of a triangular factor** ([golub2013matrix] §6.5.4, "the updated
Cholesky factor is given by `G̃ = Rᵀ`", up to signs): if `R` is upper triangular with nonzero
diagonal and `Rᵀ R = A`, then `D R` with `D = diag(sign r_ii)` is the Cholesky factor of `A`:
`D² = 1`, and `D R` has the diagonal `|r_ii| > 0`. -/
theorem isCholesky_diagonal_sign_mul {n : Type*} [Fintype n] [LinearOrder n]
    {A R : Matrix n n ℝ} (hR : R.IsUpperTriangular) (hd : ∀ i, R i i ≠ 0) (hA : Rᵀ * R = A) :
    IsCholesky A (diagonal (fun i => (SignType.sign (R i i) : ℝ)) * R) := by
  have hsq : ∀ i, (SignType.sign (R i i) : ℝ) * SignType.sign (R i i) = 1 := fun i => by
    rcases lt_or_gt_of_ne (hd i) with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]
  refine ⟨(blockTriangular_diagonal _).mul hR, fun i => ?_, ?_⟩
  · rw [diagonal_mul]
    rcases lt_or_gt_of_ne (hd i) with h | h
    · simp [sign_neg h, h]
    · simp [sign_pos h, h]
  · rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, diagonal_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    simp only [hsq, diagonal_one, Matrix.one_mul, hA]

/-- The product of a list of `J`-orthogonal matrices is `J`-orthogonal. -/
private theorem isJOrthogonal_list_prod {α ι : Type*} [CommRing α] [Fintype ι] [DecidableEq ι]
    {J : Matrix ι ι α} (l : List (Matrix ι ι α)) (h : ∀ H ∈ l, IsJOrthogonal J H) :
    IsJOrthogonal J l.prod := by
  induction l with
  | nil => exact isJOrthogonal_one J
  | cons H l ih =>
    rw [List.prod_cons]
    exact (h H (by simp)).mul (ih fun H' hH' => h H' (by simp [hH']))

/-- **A sweep through the planes `(0, last), (1, last), …`**: if an invariant `Inv t` of the
current matrix can be advanced through step `t` by some rotation parameters `p` with `Ok p`, then
there are parameters for all the steps, and `Inv n` holds after the sweep
`(E₀ ⋯ E_{n−1})ᵀ M₀ = E_{n−1}ᵀ ⋯ E₀ᵀ M₀`. -/
private theorem exists_ofFn_prod_transpose_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (E : Fin n → ℝ × ℝ → Matrix ι ι ℝ) (Ok : ℝ × ℝ → Prop) (Inv : ℕ → Matrix ι κ ℝ → Prop)
    {M₀ : Matrix ι κ ℝ} (h0 : Inv 0 M₀)
    (hstep : ∀ t (ht : t < n) M, Inv t M → ∃ p, Ok p ∧ Inv (t + 1) ((E ⟨t, ht⟩ p)ᵀ * M)) :
    ∃ cs : Fin n → ℝ × ℝ, (∀ k, Ok (cs k)) ∧
      Inv n ((List.ofFn fun k => E k (cs k)).prodᵀ * M₀) := by
  suffices h : ∀ t (ht : t ≤ n), ∃ cs : Fin t → ℝ × ℝ, (∀ k, Ok (cs k)) ∧
      Inv t ((List.ofFn fun k => E (Fin.castLE ht k) (cs k)).prodᵀ * M₀) by
    obtain ⟨cs, h₁, h₂⟩ := h n le_rfl
    exact ⟨cs, h₁, h₂⟩
  intro t
  induction t with
  | zero => exact fun _ => ⟨Fin.elim0, fun k => k.elim0, by simpa using h0⟩
  | succ t ih =>
    intro ht
    obtain ⟨cs, hok, hinv⟩ := ih (by omega)
    obtain ⟨p, hp, hinv'⟩ := hstep t (by omega) _ hinv
    refine ⟨Fin.snoc (α := fun _ => ℝ × ℝ) cs p, fun k => ?_, ?_⟩
    · induction k using Fin.lastCases with
      | last => simpa using hp
      | cast k => simpa using hok k
    · have e : (List.ofFn fun k : Fin (t + 1) =>
            E (Fin.castLE ht k) (Fin.snoc (α := fun _ => ℝ × ℝ) cs p k)).prod =
          (List.ofFn fun k : Fin t => E (Fin.castLE (by omega) k) (cs k)).prod *
            E ⟨t, by omega⟩ p := by
        rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rfl
      rw [e, transpose_mul, Matrix.mul_assoc]
      exact hinv'

/-- **Cholesky updating by plane rotations** ([golub2013matrix] §6.5.4, (6.5.5)–(6.5.7)): if
`A = Hᵀ H` is a Cholesky factorization and `z : Fin n → ℝ`, there are rotations `Q_k` in the
planes `(k, last)` of the stacked matrix `[H; zᵀ]` (the book: "the `Q_k` update involves only rows
`k` and `n+1`"), with `Q = Q₀ ⋯ Q_{n−1}` orthogonal and `Qᵀ [H; zᵀ] = [R; 0]`, where `R` is the
Cholesky factor of `A + z zᵀ`. The rotation `Q_k` is the Givens pair of the current `(k, k)` and
`(last, k)` entries; the new diagonal entry `√(r_kk² + z_k'²)` is positive, so no sign
normalization is needed. -/
theorem exists_choleskyUpdate {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℝ} (hH : IsCholesky A H)
    (z : Fin n → ℝ) :
    ∃ c s : Fin n → ℝ, (∀ k, c k ^ 2 + s k ^ 2 = 1) ∧ ∃ R : Matrix (Fin n) (Fin n) ℝ,
      (List.ofFn fun k => planeRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prod ∈
        orthogonalGroup (Fin n ⊕ Unit) ℝ ∧
      (List.ofFn fun k => planeRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prodᵀ *
        fromRows H (replicateRow Unit z) = fromRows R 0 ∧
      IsCholesky (A + vecMulVec z z) R := by
  have hne : ∀ k : Fin n, (Sum.inl k : Fin n ⊕ Unit) ≠ Sum.inr () := fun _ => Sum.inl_ne_inr
  obtain ⟨cs, hok, R, z', hM, hRt, hRd, hz'⟩ := exists_ofFn_prod_transpose_mul
    (fun k p => planeRotation (Sum.inl k) (Sum.inr ()) p.1 p.2) (fun p => p.1 ^ 2 + p.2 ^ 2 = 1)
    (fun t M => ∃ (R : Matrix (Fin n) (Fin n) ℝ) (z' : Fin n → ℝ),
      M = fromRows R (replicateRow Unit z') ∧ R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧
        ∀ j : Fin n, (j : ℕ) < t → z' j = 0)
    ⟨H, z, rfl, hH.isUpperTriangular, hH.diag_pos, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    (by
      rintro t ht M ⟨R, z', rfl, hRt, hRd, hz'⟩
      set k : Fin n := ⟨t, ht⟩ with hk
      refine ⟨givensPair (R k k) (z' k), givensPair_sq_add_sq _ _, ?_⟩
      rw [planeRotation_transpose (hne k), planeRotation]
      obtain ⟨R', z'', e, hR't, hz'', hR'i, hR'k, hz''k⟩ :=
        fromRows_rotate_step hRt (k := k) (fun j hj => hz' j hj) _
      have hg := givensPair_fst_mul_add_snd_mul (R k k) (z' k)
      refine ⟨R', z'', e, hR't, fun i => ?_, fun j hj => ?_⟩
      · by_cases hik : i = k
        · subst hik
          rw [hR'k]
          simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
            cons_val_fin_one, Fin.isValue, neg_neg]
          rw [hg.1]
          exact Real.sqrt_pos.2 (by nlinarith [hRd k, sq_nonneg (z' k)])
        · rw [hR'i i hik]
          exact hRd i
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact hz'' j hj
        · obtain rfl : j = k := Fin.ext hj
          rw [hz''k]
          simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
            cons_val_fin_one, Fin.isValue]
          exact hg.2)
  have hz0 : z' = 0 := funext fun j => hz' j j.isLt
  subst hz0
  rw [replicateRow_zero] at hM
  have hQ : (List.ofFn fun k => planeRotation (Sum.inl k) (Sum.inr ()) (cs k).1 (cs k).2).prod ∈
      orthogonalGroup (Fin n ⊕ Unit) ℝ :=
    Submonoid.list_prod_mem _ fun G hG => by
      obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hG
      exact planeRotation_mem_orthogonalGroup (hne k) (hok k)
  refine ⟨fun k => (cs k).1, fun k => (cs k).2, hok, R, hQ, hM, hRt, hRd, ?_⟩
  rw [conjTranspose_eq_transpose_of_trivial,
    ← transpose_mul_self_eq_of_mem_orthogonalGroup hQ hM, transpose_mul_self_fromRows,
    ← hH.conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial]

/-- The quadratic form of a signed Gram matrix: `xᵀ (Rᵀ R − z zᵀ) x = ‖R x‖² − (z ⬝ x)²`. -/
private theorem dotProduct_transpose_mul_self_sub_mulVec {n : Type*} [Fintype n]
    (R : Matrix n n ℝ) (z x : n → ℝ) :
    x ⬝ᵥ ((Rᵀ * R - vecMulVec z z) *ᵥ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) - (z ⬝ᵥ x) ^ 2 := by
  have h1 : x ⬝ᵥ ((Rᵀ * R) *ᵥ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have h2 : x ⬝ᵥ (vecMulVec z z *ᵥ x) = (z ⬝ᵥ x) ^ 2 := by
    rw [dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul, dotProduct_comm x z, sq]
  rw [sub_mulVec, dotProduct_sub, h1, h2]

/-- **The hyperbolic pair exists at every step of a downdate**: if `R` is upper triangular with
positive diagonal, `z` vanishes before `k`, and `Rᵀ R − z zᵀ` is positive definite, then
`z_k² < r_kk²`. Test the form on `x = R⁻¹ e_k`, supported on the indices `≤ k`: `R x = e_k` and
`z ⬝ x = z_k / r_kk`, so `0 < 1 − z_k²/r_kk²`. -/
private theorem sq_lt_sq_of_posDef_transpose_mul_self_sub {n : Type*} [Fintype n] [LinearOrder n]
    {R : Matrix n n ℝ} (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) {z : n → ℝ} {k : n}
    (hz : ∀ j < k, z j = 0) (hP : (Rᵀ * R - vecMulVec z z).PosDef) : z k ^ 2 < R k k ^ 2 := by
  have hU : IsUnit R.det := (isUnit_iff_isUnit_det R).1
    ((isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hR).2 fun i => (hd i).ne')
  have hT := hR.inv
  set x : n → ℝ := fun j => R⁻¹ j k with hx
  have hRx : R *ᵥ x = Pi.single k 1 := by
    ext i
    have := congrFun (congrFun (mul_nonsing_inv R hU) i) k
    rw [mul_apply] at this
    rw [Pi.single_apply, ← one_apply, ← this]
    rfl
  have hkk : R⁻¹ k k * R k k = 1 := by
    have := congrFun (congrFun (nonsing_inv_mul R hU) k) k
    rw [mul_apply, one_apply_eq, Finset.sum_eq_single k] at this
    · exact this
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · rw [hT h, zero_mul]
      · rw [hR h, mul_zero]
    · simp
  have hzx : z ⬝ᵥ x = z k * R⁻¹ k k := by
    rw [dotProduct, Finset.sum_eq_single k]
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · rw [hz j h, zero_mul]
      · rw [hx]
        dsimp only
        rw [hT h, mul_zero]
    · simp
  have hx0 : x ≠ 0 := fun h => by
    have := congrFun h k
    simp only [hx, Pi.zero_apply] at this
    rw [this, zero_mul] at hkk
    exact zero_ne_one hkk
  have hpos := hP.dotProduct_mulVec_pos hx0
  rw [star_trivial, dotProduct_transpose_mul_self_sub_mulVec, hRx, hzx] at hpos
  simp only [dotProduct_single, Pi.single_eq_same, mul_one] at hpos
  have hr := hd k
  have e : z k ^ 2 = (z k * R⁻¹ k k) ^ 2 * R k k ^ 2 := by
    rw [mul_pow, mul_assoc, ← mul_pow, hkk, one_pow, mul_one]
  rw [e]
  nlinarith [sq_nonneg (z k * R⁻¹ k k), pow_pos hr 2]

/-- The column `k` of a product, as the action on the column. -/
private theorem mul_apply_eq_mulVec {ι κ : Type*} [Fintype ι] (E : Matrix ι ι ℝ)
    (M : Matrix ι κ ℝ) (i : ι) (k : κ) : (E * M) i k = (E *ᵥ fun r => M r k) i := rfl

/-- **Cholesky downdating by hyperbolic rotations** ([golub2013matrix] §6.5.4, "The theorem
provides the key step in an induction proof that the factorization (6.5.12) exists"): if
`A = Hᵀ H` is a Cholesky factorization and `A − z zᵀ` is positive definite, there are hyperbolic
rotations `Hy_k` (`c_k² − s_k² = 1`) in the planes `(k, last)` of `[H; zᵀ]` whose product
`Hy = Hy₀ ⋯ Hy_{n−1}` is `S`-orthogonal and reduces `[H; zᵀ]` to `[R; 0]`, with `R` the Cholesky
factor of `A − z zᵀ`. At step `k` the current stacked matrix `[R'; z'ᵀ]` still has
`R'ᵀ R' − z' z'ᵀ = A − z zᵀ` positive definite, which forces `|z'_k| < r'_kk` (the hyperbolic
pair (6.5.13) exists), and the new diagonal entry `√(r'_kk² − z'_k²)` is positive. -/
theorem exists_choleskyDowndate {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℝ} (hH : IsCholesky A H)
    {z : Fin n → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    ∃ c s : Fin n → ℝ, (∀ k, c k ^ 2 - s k ^ 2 = 1) ∧ ∃ R : Matrix (Fin n) (Fin n) ℝ,
      IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit ℝ)
        (List.ofFn fun k => hyperbolicRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prod ∧
      (List.ofFn fun k => hyperbolicRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prodᵀ *
        fromRows H (replicateRow Unit z) = fromRows R 0 ∧
      IsCholesky (A - vecMulVec z z) R := by
  have hne : ∀ k : Fin n, (Sum.inl k : Fin n ⊕ Unit) ≠ Sum.inr () := fun _ => Sum.inl_ne_inr
  have hJ : ∀ (k : Fin n) {c s : ℝ}, c ^ 2 - s ^ 2 = 1 →
      IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit ℝ)
        (hyperbolicRotation (Sum.inl k) (Sum.inr ()) c s) :=
    fun k _ _ hcs => isJOrthogonal_hyperbolicRotation (hne k) (ε := Sum.elim (fun _ => 1)
      fun _ => -1) rfl rfl hcs
  have hA' : Hᵀ * H = A := by
    rw [← conjTranspose_eq_transpose_of_trivial, hH.conjTranspose_mul_self]
  obtain ⟨cs, hok, R, z', hM, hRt, hRd, hz', hG⟩ := exists_ofFn_prod_transpose_mul
    (fun k p => hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2)
    (fun p => p.1 ^ 2 - p.2 ^ 2 = 1)
    (fun t M => ∃ (R : Matrix (Fin n) (Fin n) ℝ) (z' : Fin n → ℝ),
      M = fromRows R (replicateRow Unit z') ∧ R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧
        (∀ j : Fin n, (j : ℕ) < t → z' j = 0) ∧ Rᵀ * R - vecMulVec z' z' = A - vecMulVec z z)
    ⟨H, z, rfl, hH.isUpperTriangular, hH.diag_pos, fun _ h => absurd h (Nat.not_lt_zero _),
      by rw [hA']⟩
    (by
      rintro t ht M ⟨R, z', rfl, hRt, hRd, hz', hG⟩
      set k : Fin n := ⟨t, ht⟩ with hk
      have hlt : |z' k| < |R k k| := by
        rw [← sq_lt_sq]
        exact sq_lt_sq_of_posDef_transpose_mul_self_sub hRt hRd (fun j hj => hz' j hj)
          (hG ▸ hA)
      set x : Fin n ⊕ Unit → ℝ := fun r => fromRows R (replicateRow Unit z') r k with hx
      have hxi : x (Sum.inl k) = R k k := rfl
      have hxr : x (Sum.inr ()) = z' k := rfl
      have hxk : |x (Sum.inr ())| < |x (Sum.inl k)| := by rwa [hxi, hxr]
      obtain ⟨p, hp⟩ : ∃ p, p = hyperbolicPair (x (Sum.inl k)) (x (Sum.inr ())) := ⟨_, rfl⟩
      obtain ⟨hcs, -⟩ := hyperbolicPair_sq_sub_sq hxk
      obtain ⟨hzero, hdiag⟩ := hyperbolicRotation_hyperbolicPair_mulVec (hne k) hxk
      rw [← hp] at hcs hzero hdiag
      refine ⟨p, hcs, ?_⟩
      rw [hyperbolicRotation_transpose (hne k)]
      obtain ⟨R', z'', e, hR't, hz'', hR'i, -, -⟩ :=
        fromRows_rotate_step hRt (k := k) (fun j hj => hz' j hj) !![p.1, -p.2; -p.2, p.1]
      have e' : hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *
          fromRows R (replicateRow Unit z') = fromRows R' (replicateRow Unit z'') := e
      have hcol : ∀ i, fromRows R' (replicateRow Unit z'') i k =
          (hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *ᵥ x) i := fun i => by
        rw [← e']
        rfl
      refine ⟨R', z'', e', hR't, fun i => ?_, fun j hj => ?_, ?_⟩
      · by_cases hik : i = k
        · rw [hik]
          have h1 := hcol (Sum.inl k)
          rw [hdiag, fromRows_apply_inl, hxi, hxr, sign_pos (hRd k), SignType.coe_one,
            one_mul] at h1
          rw [h1]
          have h2 := hlt
          rw [abs_of_pos (hRd k)] at h2
          exact Real.sqrt_pos.2 (by nlinarith [abs_lt.1 h2])
        · rw [hR'i i hik]
          exact hRd i
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact hz'' j hj
        · obtain rfl : j = k := Fin.ext hj
          have h1 := hcol (Sum.inr ())
          rw [hzero, fromRows_apply_inr] at h1
          simpa using h1
      · rw [← hG]
        exact (transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows (hJ k hcs)
          (by rw [hyperbolicRotation_transpose (hne k)]; exact e')).symm)
  have hz0 : z' = 0 := funext fun j => hz' j j.isLt
  subst hz0
  rw [replicateRow_zero] at hM
  rw [vecMulVec_zero, sub_zero] at hG
  refine ⟨fun k => (cs k).1, fun k => (cs k).2, hok, R,
    isJOrthogonal_list_prod _ fun G hG => ?_, hM, hRt, hRd, ?_⟩
  · obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hG
    exact hJ k (hok k)
  · rw [conjTranspose_eq_transpose_of_trivial, hG]

/-- **One hyperbolic downdating step** ([golub2013matrix] Theorem 6.5.1, (6.5.14)–(6.5.15)): let
`A = Hᵀ H` be a Cholesky factorization on `Fin (n + 1)`, `α = a₀₀`, `μ = z₀`, and `A − z zᵀ`
positive definite. Then `μ² < α`, and with `c = √α/√(α − μ²)`, `s = μ/√(α − μ²)` (`c² − s² = 1`)
the hyperbolic rotation in the plane of the first and the appended rows maps `[H; zᵀ]` to
`[R'; z'ᵀ]` with `z'₀ = 0`, `r'₀₀ > 0`, the rows of `H` after the first unchanged,
`w₁ = z'_{1:} = −s g₁ + c w`, and `G₁G₁ᵀ − w₁w₁ᵀ` positive definite, where `G₁ᵀ` is the trailing
block of `H` — it is the Schur complement of the `(0, 0)` entry `α − μ²` of `A − z zᵀ` (the book
says "of `α`"). -/
theorem hyperbolicDowndate_step {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) {z : Fin (n + 1) → ℝ} (hA : (A - vecMulVec z z).PosDef) {c s : ℝ}
    (hc : c = √(A 0 0) / √(A 0 0 - z 0 ^ 2)) (hs : s = z 0 / √(A 0 0 - z 0 ^ 2)) :
    z 0 ^ 2 < A 0 0 ∧ c ^ 2 - s ^ 2 = 1 ∧
      ∃ (R' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z' : Fin (n + 1) → ℝ),
        hyperbolicRotation (Sum.inl (0 : Fin (n + 1))) (Sum.inr ()) c s *
            fromRows H (replicateRow Unit z) =
          fromRows R' (replicateRow Unit z') ∧
        z' 0 = 0 ∧ 0 < R' 0 0 ∧ (∀ i, i ≠ 0 → R' i = H i) ∧
        (∀ j : Fin n, z' j.succ = -s * H 0 j.succ + c * z j.succ) ∧
        ((H.submatrix Fin.succ Fin.succ)ᵀ * H.submatrix Fin.succ Fin.succ -
          vecMulVec (fun j : Fin n => z' j.succ) (fun j : Fin n => z' j.succ)).PosDef := by
  have hA' : Hᵀ * H = A := by
    rw [← conjTranspose_eq_transpose_of_trivial, hH.conjTranspose_mul_self]
  have h00 : A 0 0 = H 0 0 ^ 2 := by
    rw [← hA', mul_apply, Finset.sum_eq_single 0]
    · simp [sq]
    · intro j _ hj
      rw [transpose_apply, hH.isUpperTriangular (Fin.pos_iff_ne_zero.2 hj), zero_mul]
    · simp
  have hpos : 0 < A 0 0 - z 0 ^ 2 := by
    simpa [vecMulVec_apply, sq] using hA.diag_pos (i := 0)
  have hH0 := hH.diag_pos 0
  have hsqrtα : √(A 0 0) = H 0 0 := by rw [h00, Real.sqrt_sq hH0.le]
  set d := √(A 0 0 - z 0 ^ 2) with hd
  have hd0 : 0 < d := Real.sqrt_pos.2 hpos
  have hdd : d ^ 2 = A 0 0 - z 0 ^ 2 := Real.sq_sqrt hpos.le
  rw [hsqrtα] at hc
  have hcs : c ^ 2 - s ^ 2 = 1 := by
    rw [hc, hs, div_pow, div_pow, ← sub_div, hdd, ← h00, div_self hpos.ne']
  obtain ⟨R', z', e, -, -, hR'i, hR'k, hz'⟩ :=
    fromRows_rotate_step hH.isUpperTriangular (k := 0)
      (fun j hj => absurd hj (Fin.not_lt_zero j)) !![c, -s; -s, c]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    Fin.isValue] at hR'k hz'
  have hz'0 : z' 0 = 0 := by
    rw [hz', hc, hs]
    field_simp
    ring
  have hR'0 : R' 0 0 = d := by
    rw [hR'k, hc, hs]
    field_simp
    rw [hdd, h00]
    ring
  refine ⟨by linarith, hcs, R', z', e, hz'0, hR'0 ▸ hd0, hR'i, fun j => by rw [hz'], ?_⟩
  -- the signed Gram matrix of the rotated stacked matrix is still `A − z zᵀ`
  have hG : R'ᵀ * R' - vecMulVec z' z' = A - vecMulVec z z := by
    rw [← hA']
    exact (transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows
      (isJOrthogonal_hyperbolicRotation Sum.inl_ne_inr (ε := Sum.elim (fun _ => 1) fun _ => -1)
        rfl rfl hcs) (by rw [hyperbolicRotation_transpose Sum.inl_ne_inr]; exact e)).symm
  set B := H.submatrix Fin.succ Fin.succ with hB
  set w : Fin n → ℝ := fun j => z' j.succ with hw
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_mul,
      transpose_transpose, transpose_vecMulVec]
  -- test the form of `A − z zᵀ` on `y = [−(r'₁ᵀ x)/r'₀₀; x]`
  set y : Fin (n + 1) → ℝ := Fin.cons (-(∑ j, R' 0 j.succ * x j) / R' 0 0) x with hy
  have hy0 : y ≠ 0 := fun h => hx (funext fun j => by simpa [hy] using congrFun h j.succ)
  have hRy : R' *ᵥ y = Fin.cons 0 (B *ᵥ x) := by
    ext i
    induction i using Fin.cases with
    | zero =>
      have hr : R' 0 0 ≠ 0 := hR'0 ▸ hd0.ne'
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, hy, Fin.cons_zero, Fin.cons_succ]
      field_simp
      ring
    | succ i =>
      have hrow : R' i.succ = H i.succ := hR'i i.succ (Fin.succ_ne_zero i)
      have h0 : H i.succ 0 = 0 := hH.isUpperTriangular (Fin.succ_pos i)
      simp [mulVec, dotProduct, Fin.sum_univ_succ, hrow, hy, hB, h0]
  have hzy : z' ⬝ᵥ y = w ⬝ᵥ x := by
    rw [dotProduct, Fin.sum_univ_succ, hz'0, zero_mul, zero_add]
    simp [hy, hw, dotProduct]
  have key := hA.dotProduct_mulVec_pos hy0
  rw [star_trivial, ← hG, dotProduct_transpose_mul_self_sub_mulVec, hRy, hzy] at key
  rw [star_trivial, dotProduct_transpose_mul_self_sub_mulVec]
  simpa [dotProduct, Fin.sum_univ_succ] using key

end CholeskyUpdate

end Matrix
