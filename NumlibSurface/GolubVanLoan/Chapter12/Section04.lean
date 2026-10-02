import Numlib.LinearAlgebra.Tensor.MultilinearProduct

/-!
# Golub–Van Loan §12.4: tensor unfoldings and contractions

Surface file for §12.4 of Golub and Van Loan, *Matrix Computations* (4th edition): order-`d`
tensors, subtensors and the Frobenius norm (§12.4.2), `vec` (12.4.2)–(12.4.5), transposition
(§12.4.4), modal and general unfoldings (12.4.6), (12.4.8), outer products and rank-one tensors
(12.4.9)–(12.4.10), contractions (12.4.11)–(12.4.13), modal and multilinear products
(12.4.14)–(12.4.19) and Theorem 12.4.1.

## Design

The book's `ℝ^{n₁ × ⋯ × n_d}` is `RTensor n := Tensor (fun k : Fin d => Fin (n k)) ℝ`, the
backbone's concrete tensors (`Numlib/LinearAlgebra/Tensor/Basic`); the entry `𝒜(i)` is `A i` for a
0-based index tuple `i : ∀ k, Fin (n k)`. The book's `col(i, n)` is Mathlib's little-endian
`finPiFinEquiv` (the first index runs fastest), and the book's `vec` is `Tensor.vecFin`.

The backbone's unfoldings are typed (`Tensor.modeUnfold`, `Tensor.unfold`: rows and columns are
index tuples); the book's are flattened matrices on `Fin`. The surface definitions
`modalUnfolding` and `generalUnfolding` flatten the typed ones by `finPiFinEquiv` in the book's
column order, and every flattened statement carries the Kronecker products in the book's reversed
order `M_d ⊗ ⋯ ⊗ M_1` as the flattening of the backbone's family product `Matrix.piKronecker` by
`finPiFinEquiv` (`Matrix.piKronecker_reindex_finPiFinEquiv` identifies it with the positional
`Matrix.kroneckerFin` product, last factor outermost).

A general unfolding `𝒜_{r × c}` lists its row modes `r` and column modes `c`; here the listing is
an equivalence `p : Fin e ⊕ Fin f ≃ Fin d`, the row modes being `p (inl 0), …, p (inl (e−1))` and
the column modes `p (inr 0), …`, in the book's listed order.

The mode-`k` product with a rectangular `M ∈ ℝ^{m × n_k}` changes the `k`-th size, so its result
has shape `Function.update n k m`; `modeProduct` is the backbone's rectangular mode product
`Tensor.rectModeProd`, the shapes off `k` matched by `Function.update_of_ne`. Its laws
(12.4.14)–(12.4.17) are the backbone's (`Tensor.modeUnfold_rectModeProd`,
`Tensor.vecFin_rectModeProd`, `Tensor.rectModeProd_comm`, `Tensor.rectModeProd_rectModeProd`), read
through `castShape` where two shapes are only propositionally equal. The table after (12.4.19)
(the multilinear product as a sequence of mode products, in any order) is stated for square
factors, through the backbone's shape-preserving `Tensor.modeProd`.

## Main results

* `RTensor`, `fiber`, `slice`, `subtensor`, `frobenius_norm_tensor` — §12.4.2.
* `equation_12_4_4`, `equation_12_4_2` — `vec`.
* `tensorTranspose_apply` — §12.4.4.
* `modalUnfolding`, `equation_12_4_6`; `generalUnfolding`, `equation_12_4_8`; `outer_kronecker`.
* `equation_12_4_9`, `equation_12_4_10`, `eq_sum_rankOne` — rank-one tensors.
* `equation_12_4_11`, `equation_12_4_13` — contractions.
* `modeProduct`, `equation_12_4_14` … `equation_12_4_19`, `theorem_12_4_1`, `theorem_12_4_1_b`;
  `lowerSize`, `upperSize` for (12.4.15).

## Not formalized here

The loops (12.4.1) and (12.4.12), the numerical examples (the `2 × 2 × 3 × 4` unfolding of
§12.4.1, the vec and transposition examples of §12.4.3–12.4.4, (12.4.7)), the misprinted vec formula
for `𝒜^{<[3 2 1]>}` (the correct one is `(𝒫_{n₂,n₁} ⊗ I_{n₃}) 𝒫_{n₃,n₁n₂}`), the space–time
contraction example of §12.4.12 and all flop counts.
-/

open Matrix

namespace GolubVanLoan.Chapter12

variable {d : ℕ}

/-! ### Order-`d` tensors (§12.4.2) -/

/-- **§12.4**, the book's order-`d` tensor space `ℝ^{n₁ × ⋯ × n_d}`, 0-based: an entry `𝒜(i)` is
`A i` for `i : ∀ k, Fin (n k)`. -/
abbrev RTensor (n : Fin d → ℕ) : Type :=
  Tensor (fun k : Fin d => Fin (n k)) ℝ

/-- **§12.4.2**, a fiber: the order-1 subtensor obtained by fixing every index but the `k`-th
(the book's `𝒜(1, :, 2, 4)`). -/
def fiber {n : Fin d → ℕ} (A : RTensor n) (k : Fin d) (c : ∀ i : {i // ¬i = k}, Fin (n i)) :
    Tensor (fun i : {i // i = k} => Fin (n i)) ℝ :=
  Tensor.restrict (· = k) c A

/-- **§12.4.2**, a slice: the order-2 subtensor obtained by fixing every index but the `k`-th and
the `l`-th. -/
def slice {n : Fin d → ℕ} (A : RTensor n) (k l : Fin d)
    (c : ∀ i : {i // ¬(i = k ∨ i = l)}, Fin (n i)) :
    Tensor (fun i : {i // i = k ∨ i = l} => Fin (n i)) ℝ :=
  Tensor.restrict (fun i => i = k ∨ i = l) c A

/-- **§12.4.2**, the colon subtensor `𝒜(L:R)`: the entries whose `k`-th index lies in
`[L_k, R_k]` for every `k`. -/
def subtensor {n : Fin d → ℕ} (A : RTensor n) (L R : ∀ k, Fin (n k)) :
    Tensor (fun k => {x : Fin (n k) // L k ≤ x ∧ x ≤ R k}) ℝ :=
  Tensor.of fun a => A fun k => a k

/-- **§12.4.2**: the Frobenius norm of a tensor, `‖𝒜‖_F = √(∑_{i=1}^{n} 𝒜(i)²)`. -/
theorem frobenius_norm_tensor {n : Fin d → ℕ} (A : RTensor n) : ‖A‖ = √(∑ i, A i ^ 2) := by
  rw [Tensor.frobenius_norm_def]
  simp only [Real.norm_eq_abs, sq_abs]

/-! ### Vectorization (12.4.2)–(12.4.5) -/

/-- **(12.4.4)–(12.4.5)**: with `col(i, n) = i₁ + (i₂ − 1) n₁ + ⋯ + (i_d − 1) n₁ ⋯ n_{d−1}`, the
vector `a = vec(𝒜)` satisfies `a(col(i, n)) = 𝒜(i)`. 0-based, `col(i, n) − 1` is `finPiFinEquiv i`,
whose value is `∑_k i_k ∏_{j < k} n_j`. -/
theorem equation_12_4_4 {n : Fin d → ℕ} (A : RTensor n) (i : ∀ k, Fin (n k)) :
    ((finPiFinEquiv i : Fin (∏ k, n k)) : ℕ) =
        ∑ k, (i k : ℕ) * ∏ j : Fin k, n (Fin.castLE k.2.le j) ∧
      Tensor.vecFin A (finPiFinEquiv i) = A i :=
  ⟨finPiFinEquiv_apply i, Tensor.vecFin_apply A i⟩

/-- **(12.4.2)–(12.4.3)**: `vec(𝒜) = [vec(𝒜⁽¹⁾); ⋯; vec(𝒜⁽ⁿᵈ⁾)]` with the last-mode slices
`𝒜⁽ˣ⁾(i₁, …, i_{d−1}) = 𝒜(i₁, …, i_{d−1}, x)`: the block `x` of `vec(𝒜)` (in the positional layout
`finProdFinEquiv`) is `vec(𝒜⁽ˣ⁾)`. So the book's recursive definition agrees with the closed form
(12.4.4)–(12.4.5) (P12.4.2). -/
theorem equation_12_4_2 {n : Fin (d + 1) → ℕ} (A : RTensor n) (x : Fin (n (Fin.last d)))
    (t : Fin (∏ k : Fin d, n k.castSucc)) :
    Tensor.vecFin A (Fin.cast (by rw [Fin.prod_univ_castSucc, mul_comm]) (finProdFinEquiv (x, t)))
      = Tensor.vecFin (Tensor.of fun i => A (Fin.snoc (α := fun k => Fin (n k)) i x) :
          RTensor fun k : Fin d => n k.castSucc) t :=
  Tensor.vecFin_snoc A x t

/-! ### Transposition (§12.4.4) -/

/-- **§12.4.4**, Definition: for a permutation `p` of `1:d`, the `p`-transpose
`𝒜^{<p>} ∈ ℝ^{n_{p₁} × ⋯ × n_{p_d}}` (`Tensor.permute p A`) satisfies `𝒜^{<p>}(j(p)) = 𝒜(j)`. -/
theorem tensorTranspose_apply {n : Fin d → ℕ} (p : Equiv.Perm (Fin d)) (A : RTensor n)
    (j : ∀ k, Fin (n k)) :
    (Tensor.permute p A : RTensor (n ∘ p)) (fun k => j (p k)) = A j :=
  Tensor.permute_apply p A j

/-! ### Modal unfoldings (12.4.6) -/

section Modal

variable {n : Fin (d + 1) → ℕ}

/-- The column order of the mode-`k` unfolding: the tuple of the other indices, relabelled by
`Fin d` through `k.succAbove`, then flattened by `col` (`finPiFinEquiv`). -/
def modalColumnEquiv (n : Fin (d + 1) → ℕ) (k : Fin (d + 1)) :
    (∀ j : {j // j ≠ k}, Fin (n j)) ≃ Fin (∏ j : Fin d, n (k.succAbove j)) :=
  (Equiv.piCongrLeft' (fun j : {j // j ≠ k} => Fin (n j)) (finSuccAboveEquiv k).symm).trans
    (finPiFinEquiv (n := fun j : Fin d => n (k.succAbove j)))

/-- The column of the mode-`k` unfolding holding the entry `𝒜(i)`: `col` of `i` with its `k`-th
index deleted. -/
theorem modalColumnEquiv_apply (k : Fin (d + 1)) (i : ∀ j, Fin (n j)) :
    modalColumnEquiv n k (fun j => i j) = finPiFinEquiv fun j => i (k.succAbove j) :=
  rfl

/-- The index tuple of the column `c` of the mode-`k` unfolding, read at the `i`-th remaining
mode. -/
theorem modalColumnEquiv_symm_apply (k : Fin (d + 1)) (c : ∀ j : {j // j ≠ k}, Fin (n j))
    (i : Fin d) :
    finPiFinEquiv.symm (modalColumnEquiv n k c) i = c ⟨k.succAbove i, Fin.succAbove_ne k i⟩ :=
  congrFun (finPiFinEquiv.symm_apply_apply
    (Equiv.piCongrLeft' _ (finSuccAboveEquiv k).symm c :
      ∀ j : Fin d, Fin (n (k.succAbove j)))) i

/-- **§12.4.5**, Definition: the book's mode-`k` unfolding `𝒜_(k) ∈ ℝ^{n_k × (n₁ ⋯ n_d / n_k)}`,
the columns being the mode-`k` fibers ordered "left to right according to the vec ordering": the
backbone's typed `Tensor.modeUnfold` with its columns flattened by `modalColumnEquiv`. -/
def modalUnfolding (A : RTensor n) (k : Fin (d + 1)) :
    Matrix (Fin (n k)) (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ :=
  (A.modeUnfold k).reindex (Equiv.refl _) (modalColumnEquiv n k)

/-- **(12.4.6)**: `𝒜_(k)(i_k, col(ĩ_k, ñ_k)) = 𝒜(i)`, `ĩ_k` and `ñ_k` being `i` and `n` with their
`k`-th entries deleted. -/
theorem equation_12_4_6 (A : RTensor n) (k : Fin (d + 1)) (i : ∀ j, Fin (n j)) :
    modalUnfolding A k (i k) (finPiFinEquiv fun j => i (k.succAbove j)) = A i := by
  rw [modalUnfolding, reindex_apply, submatrix_apply, ← modalColumnEquiv_apply,
    Equiv.symm_apply_apply]
  exact Tensor.modeUnfold_apply A k i

end Modal

/-! ### General unfoldings (12.4.8) -/

section General

variable {e f : ℕ} {n : Fin d → ℕ}

/-- **§12.4.6**, Definition: the general unfolding `𝒜_{r × c}` with row modes
`r = (p (inl 0), …, p (inl (e−1)))` and column modes `c = (p (inr 0), …, p (inr (f−1)))`, rows and
columns flattened by `col` in the listed orders. -/
def generalUnfolding (A : RTensor n) (p : Fin e ⊕ Fin f ≃ Fin d) :
    Matrix (Fin (∏ j : Fin e, n (p (.inl j)))) (Fin (∏ j : Fin f, n (p (.inr j)))) ℝ :=
  Matrix.of fun R C => (Tensor.permute p A : Tensor (fun s => Fin (n (p s))) ℝ)
    (Sum.rec (motive := fun s => Fin (n (p s))) (finPiFinEquiv.symm R) (finPiFinEquiv.symm C))

/-- The entries of a general unfolding. -/
theorem generalUnfolding_apply (A : RTensor n) (p : Fin e ⊕ Fin f ≃ Fin d)
    (i : ∀ k, Fin (n k)) :
    generalUnfolding A p (finPiFinEquiv fun j => i (p (.inl j)))
      (finPiFinEquiv fun j => i (p (.inr j))) = A i := by
  rw [generalUnfolding, of_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have h : (Sum.rec (motive := fun s => Fin (n (p s))) (fun j => i (p (.inl j)))
      (fun j => i (p (.inr j))) : ∀ s, Fin (n (p s))) = fun s => i (p s) := by
    funext s
    cases s <;> rfl
  rw [h]
  exact Tensor.permute_apply p A i

/-- The listing of the modes of the mode-`k` unfolding: row mode `k`, then the column modes in
increasing order. -/
def modalModes (k : Fin (d + 1)) : Fin 1 ⊕ Fin d ≃ Fin (d + 1) where
  toFun := Sum.elim (fun _ => k) k.succAbove
  invFun x := if h : x = k then .inl 0 else .inr ((finSuccAboveEquiv k).symm ⟨x, h⟩)
  left_inv s := by
    rcases s with s | s
    · simp [Fin.fin_one_eq_zero s]
    · change (if h : k.succAbove s = k then _ else _) = _
      split_ifs with h
      · exact absurd h (Fin.succAbove_ne k s)
      · exact congrArg Sum.inr
          ((finSuccAboveEquiv k).symm_apply_eq.2 (finSuccAboveEquiv_apply k s).symm)
  right_inv x := by
    by_cases h : x = k
    · simp [h]
    · have := (finSuccAboveEquiv k).apply_symm_apply ⟨x, h⟩
      simp only [finSuccAboveEquiv_apply, Subtype.ext_iff] at this
      simp [h, this]

/-- **(12.4.8)**: `𝒜_{r × c}(col(i(r), n(r)), col(i(c), n(c))) = 𝒜(i)`; and its special cases (the
sentences after (12.4.8)): `r = [k]`, `c = [1, …, k−1, k+1, …, d]` gives the modal unfolding, and
`r = 1:d`, `c = ∅` gives `vec(𝒜)` as a one-column matrix. -/
theorem equation_12_4_8 (A : RTensor n) (p : Fin e ⊕ Fin f ≃ Fin d) (i : ∀ k, Fin (n k)) :
    generalUnfolding A p (finPiFinEquiv fun j => i (p (.inl j)))
        (finPiFinEquiv fun j => i (p (.inr j))) = A i ∧
      (∀ {d' : ℕ} {n' : Fin (d' + 1) → ℕ} (A' : RTensor n') (k : Fin (d' + 1))
          (i' : ∀ j, Fin (n' j)),
        generalUnfolding A' (modalModes k) (finPiFinEquiv fun j => i' (modalModes k (.inl j)))
            (finPiFinEquiv fun j => i' (modalModes k (.inr j))) =
          modalUnfolding A' k (i' k) (finPiFinEquiv fun j => i' (k.succAbove j))) ∧
      ∀ c, generalUnfolding A (Equiv.sumEmpty (Fin d) (Fin 0)) (finPiFinEquiv i) c =
        Tensor.vecFin A (finPiFinEquiv i) := by
  refine ⟨generalUnfolding_apply A p i, fun A' k i' => ?_, fun c => ?_⟩
  · rw [generalUnfolding_apply, equation_12_4_6]
  · obtain ⟨c, rfl⟩ := finPiFinEquiv.surjective c
    have h : c = fun j => i (Equiv.sumEmpty (Fin d) (Fin 0) (.inr j)) := funext fun j => j.elim0
    rw [h, Tensor.vecFin_apply]
    exact generalUnfolding_apply A _ i

end General

/-! ### Outer products and rank-one tensors (§12.4.7–12.4.8) -/

section Outer

variable {m₁ n₁ m₂ n₂ : ℕ}

/-- The listing `r = [3 1]`, `c = [4 2]` of the modes of an order-4 tensor (0-based: rows `2, 0`,
columns `3, 1`). -/
def kroneckerModes : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![2, 0] ![3, 1]
  invFun := ![.inl 1, .inr 1, .inl 0, .inr 0]
  left_inv s := by rcases s with s | s <;> fin_cases s <;> rfl
  right_inv x := by fin_cases x <;> rfl

/-- **§12.4.7**: for matrices `B ∈ ℝ^{n₁×n₂}`, `C ∈ ℝ^{n₃×n₄}` and the order-4 tensor `𝒜 = B ∘ C`,
`𝒜(i₁, i₂, j₁, j₂) = B(i₁, i₂) C(j₁, j₂)`, the unfolding `𝒜_{[3 1] × [4 2]}` is the Kronecker
product `B ⊗ C` (`Matrix.kroneckerFin`, the book's layout), up to the identification of the sizes
`n₃ n₁ = n₁ n₃`, `n₄ n₂ = n₂ n₄`: the Kronecker product of two matrices is their outer product as
tensors. -/
theorem outer_kronecker {n : Fin 4 → ℕ} (B : Matrix (Fin (n 0)) (Fin (n 1)) ℝ)
    (C : Matrix (Fin (n 2)) (Fin (n 3)) ℝ) :
    generalUnfolding (Tensor.of fun i => B (i 0) (i 1) * C (i 2) (i 3) : RTensor n)
        kroneckerModes =
      (kroneckerFin B C).submatrix
        (finCongr (by simp [kroneckerModes, Fin.prod_univ_two, mul_comm]))
        (finCongr (by simp [kroneckerModes, Fin.prod_univ_two, mul_comm])) := by
  ext R C'
  obtain ⟨r, rfl⟩ := finPiFinEquiv.surjective R
  obtain ⟨c, rfl⟩ := finPiFinEquiv.surjective C'
  set i : ∀ k, Fin (n k) := (Equiv.piCongrLeft (fun k => Fin (n k)) kroneckerModes)
    (Sum.rec (motive := fun s => Fin (n (kroneckerModes s))) r c) with hi
  have hr : r = fun j => i (kroneckerModes (.inl j)) := by
    funext j; rw [hi, Equiv.piCongrLeft_apply_apply]
  have hc : c = fun j => i (kroneckerModes (.inr j)) := by
    funext j; rw [hi, Equiv.piCongrLeft_apply_apply]
  rw [hr, hc, generalUnfolding_apply, submatrix_apply]
  have e1 : finCongr (by simp [kroneckerModes, Fin.prod_univ_two, mul_comm])
      (finPiFinEquiv fun j => i (kroneckerModes (.inl j))) =
        (finProdFinEquiv (i 0, i 2) : Fin (n 0 * n 2)) := by
    apply Fin.ext
    rw [finCongr_apply, Fin.val_cast, finPiFinEquiv_apply, Fin.sum_univ_two]
    (try simp [kroneckerModes]); ring
  have e2 : finCongr (by simp [kroneckerModes, Fin.prod_univ_two, mul_comm])
      (finPiFinEquiv fun j => i (kroneckerModes (.inr j))) =
        (finProdFinEquiv (i 1, i 3) : Fin (n 1 * n 3)) := by
    apply Fin.ext
    rw [finCongr_apply, Fin.val_cast, finPiFinEquiv_apply, Fin.sum_univ_two]
    (try simp [kroneckerModes]); ring
  rw [e1, e2, kroneckerFin_apply, Tensor.of_apply]

end Outer

section RankOne

variable {n : Fin d → ℕ}

/-- **§12.4.8**, last display: `𝒜 = ∑_{i=1}^{n} 𝒜(i) I_{n₁}(:, i₁) ∘ ⋯ ∘ I_{n_d}(:, i_d)`, the
column `I_{n_k}(:, i_k)` being `Pi.single (i k) 1`. -/
theorem eq_sum_rankOne (A : RTensor n) :
    A = ∑ i, A i • Tensor.rankOne (κ := fun k : Fin d => Fin (n k))
      (fun k => (Pi.single (i k) (1 : ℝ) : Fin (n k) → ℝ)) :=
  Tensor.eq_sum_rankOne_single A

/-- The vectorization of a rank-one tensor is the Kronecker product `z⁽ᵈ⁾ ⊗ ⋯ ⊗ z⁽¹⁾` of its
factors, each a one-column matrix (the flattened family product,
`Matrix.piKronecker_reindex_finPiFinEquiv`), e.g. `vec(u ∘ v ∘ w) = w ⊗ v ⊗ u`. -/
theorem vecFin_rankOne (z : ∀ k, Fin (n k) → ℝ) (t : Fin (∏ k, n k)) :
    Tensor.vecFin (Tensor.rankOne z : RTensor n) t =
      ((piKronecker fun k => replicateCol (Fin 1) (z k)).reindex finPiFinEquiv finPiFinEquiv) t
        (finPiFinEquiv fun _ => 0) := by
  obtain ⟨a, rfl⟩ := finPiFinEquiv.surjective t
  simp [reindex_apply, replicateCol_apply]

/-- **(12.4.9)**: for `𝒜 = z⁽¹⁾ ∘ ⋯ ∘ z⁽ᵈ⁾`, `𝒜_(k) = z⁽ᵏ⁾ (z⁽ᵈ⁾ ⊗ ⋯ ⊗ z⁽ᵏ⁺¹⁾ ⊗ z⁽ᵏ⁻¹⁾ ⊗ ⋯ ⊗
z⁽¹⁾)ᵀ`, the Kronecker product of the other factors being the vectorization of their rank-one tensor
(`vecFin_rankOne`). -/
theorem equation_12_4_9 {n : Fin (d + 1) → ℕ} (z : ∀ k, Fin (n k) → ℝ) (k : Fin (d + 1)) :
    modalUnfolding (Tensor.rankOne z : RTensor n) k =
      vecMulVec (z k) (Tensor.vecFin (Tensor.rankOne fun j : Fin d => z (k.succAbove j) :
        RTensor fun j => n (k.succAbove j))) := by
  ext x c
  obtain ⟨b, rfl⟩ := finPiFinEquiv.surjective c
  have := equation_12_4_6 (Tensor.rankOne z : RTensor n) k (Fin.insertNth k x b)
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at this
  rw [this, vecMulVec_apply, Tensor.vecFin_apply, Tensor.rankOne_apply, Tensor.rankOne_apply,
    Fin.prod_univ_succAbove _ k]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- **(12.4.10)**: for a rank-one `𝒜` and row and column modes `r = p(1:e)`, `c = p(e+1:d)`,
`𝒜_{r × c} = (z⁽ᵖᵉ⁾ ⊗ ⋯ ⊗ z⁽ᵖ¹⁾)(z⁽ᵖᵈ⁾ ⊗ ⋯ ⊗ z⁽ᵖᵉ⁺¹⁾)ᵀ`, each Kronecker product of vectors being the
vectorization of the rank-one tensor of its factors. -/
theorem equation_12_4_10 {e f : ℕ} (z : ∀ k, Fin (n k) → ℝ) (p : Fin e ⊕ Fin f ≃ Fin d) :
    generalUnfolding (Tensor.rankOne z : RTensor n) p =
      vecMulVec (Tensor.vecFin (Tensor.rankOne fun j : Fin e => z (p (.inl j)) :
          RTensor fun j => n (p (.inl j))))
        (Tensor.vecFin (Tensor.rankOne fun j : Fin f => z (p (.inr j)) :
          RTensor fun j => n (p (.inr j)))) := by
  ext R C
  obtain ⟨r, rfl⟩ := finPiFinEquiv.surjective R
  obtain ⟨c, rfl⟩ := finPiFinEquiv.surjective C
  set i : ∀ k, Fin (n k) := (Equiv.piCongrLeft (fun k => Fin (n k)) p)
    (Sum.rec (motive := fun s => Fin (n (p s))) r c) with hi
  have hr : r = fun j => i (p (.inl j)) := by
    funext j; rw [hi, Equiv.piCongrLeft_apply_apply]
  have hc : c = fun j => i (p (.inr j)) := by
    funext j; rw [hi, Equiv.piCongrLeft_apply_apply]
  rw [hr, hc, generalUnfolding_apply, vecMulVec_apply, Tensor.vecFin_apply, Tensor.vecFin_apply,
    Tensor.rankOne_apply, Tensor.rankOne_apply, Tensor.rankOne_apply,
    ← Equiv.prod_comp p, Fintype.prod_sum_type]

end RankOne

/-! ### Contractions (12.4.11)–(12.4.13) -/

/-- **(12.4.11)** and the slice form after it: the contraction
`𝒜(i, j, α₃, α₄, β₃, β₄, β₅) = ∑_{k=1}^{n₂} ℬ(i, k, α₃, α₄) 𝒞(k, j, β₃, β₄, β₅)` is, at every fixed
`(α, β)`, the matrix product of the slices, `𝒜(:, :, α, β) = ℬ(:, :, α) 𝒞(:, :, β)`. The tensors are
read as functions of their indices (`ℬ ∈ ℝ^{n₁ × t × p₃ × p₄}`, `𝒞 ∈ ℝ^{t × n₂ × q₃ × q₄ × q₅}`). -/
theorem equation_12_4_11 {n₁ t n₂ p₃ p₄ q₃ q₄ q₅ : ℕ}
    (B : Fin n₁ → Fin t → Fin p₃ → Fin p₄ → ℝ) (C : Fin t → Fin n₂ → Fin q₃ → Fin q₄ → Fin q₅ → ℝ)
    (A : Fin n₁ → Fin n₂ → Fin p₃ → Fin p₄ → Fin q₃ → Fin q₄ → Fin q₅ → ℝ)
    (hA : ∀ i j a₃ a₄ b₃ b₄ b₅, A i j a₃ a₄ b₃ b₄ b₅ = ∑ k, B i k a₃ a₄ * C k j b₃ b₄ b₅)
    (a₃ : Fin p₃) (a₄ : Fin p₄) (b₃ : Fin q₃) (b₄ : Fin q₄) (b₅ : Fin q₅) :
    (Matrix.of fun i j => A i j a₃ a₄ b₃ b₄ b₅) =
      (Matrix.of fun i k => B i k a₃ a₄) * Matrix.of fun k j => C k j b₃ b₄ b₅ := by
  ext i j
  rw [of_apply, hA, mul_apply]
  rfl

/-- **(12.4.12)–(12.4.13)** and the display after it: the contraction `𝒜(i, j) = ∑_k ℬ(i, k) 𝒞(k,
j)` over a multi-index `k` satisfies `𝒜_{[1 2] × [3 4 5]} = ℬ_{[1 2] × [3 4]} 𝒞_{[1 2] × [3 4 5]}`:
typed, `𝒜 = Tensor.contract ℬ 𝒞` with the free modes of `ℬ`, the contracted modes and the free modes
of `𝒞` as the three blocks of a `Sum`-indexed family, and the unfolding identity is
`Tensor.sumUnfold_contract`. -/
theorem equation_12_4_13 {ι₁ ι₂ ι₃ : Type} [Fintype ι₂] [DecidableEq ι₂] {κ₁ : ι₁ → Type}
    {κ₂ : ι₂ → Type} {κ₃ : ι₃ → Type} [∀ j, Fintype (κ₂ j)]
    (B : Tensor (Sum.elim κ₁ κ₂) ℝ) (C : Tensor (Sum.elim κ₂ κ₃) ℝ) :
    (∀ (x : ∀ i, κ₁ i) (z : ∀ l, κ₃ l),
      Tensor.contract B C ((Equiv.sumPiEquivProdPi _).symm (x, z)) =
        ∑ y : ∀ j, κ₂ j, B ((Equiv.sumPiEquivProdPi _).symm (x, y)) *
          C ((Equiv.sumPiEquivProdPi _).symm (y, z))) ∧
      Tensor.sumUnfold (Tensor.contract B C) = Tensor.sumUnfold B * Tensor.sumUnfold C :=
  ⟨Tensor.contract_apply B C, Tensor.sumUnfold_contract B C⟩

/-! ### Modal and multilinear products (12.4.14)–(12.4.19) -/

section ModeProduct

variable {n : Fin d → ℕ}

/-- **§12.4.10**, Definition: the mode-`k` product `𝒮 ×_k M` with a rectangular `M ∈ ℝ^{m × n_k}`,
of shape `Function.update n k m`: the backbone's rectangular mode product `Tensor.rectModeProd`,
the shapes off `k` matched by `Function.update_of_ne`. -/
def modeProduct (n : Fin d → ℕ) (S : RTensor n) (k : Fin d) {m : ℕ}
    (M : Matrix (Fin m) (Fin (n k)) ℝ) : RTensor (Function.update n k m) :=
  S.rectModeProd k (μ := fun i => Fin (Function.update n k m i))
    (fun _ h => finCongr (Function.update_of_ne h m n))
    (M.reindex (finCongr (Function.update_self k m n).symm) (Equiv.refl _))

/-- The index of `𝒮` met by the entry `a` of `𝒮 ×_k M` at the summation index `y` of mode `k`: `a`
with its `k`-th entry replaced by `y`, read in the shape `n`. -/
def spliceIndex (k : Fin d) {m : ℕ} (a : ∀ i, Fin (Function.update n k m i)) (y : Fin (n k)) :
    ∀ i, Fin (n i) := fun i =>
  if h : i = k then Fin.cast (congrArg n h.symm) y
  else Fin.cast (Function.update_of_ne h m n) (a i)

/-- The value of `spliceIndex k a y` at mode `i`: `y` at `k`, the entry of `a` elsewhere. -/
theorem val_spliceIndex (k : Fin d) {m : ℕ} (a : ∀ i, Fin (Function.update n k m i))
    (y : Fin (n k)) (i : Fin d) :
    (spliceIndex k a y i : ℕ) = if i = k then (y : ℕ) else a i := by
  unfold spliceIndex
  split_ifs <;> simp

/-- **(12.4.14)** and the entry formula after it: `(𝒮 ×_k M)_(k) = M 𝒮_(k)` (typed, up to the
identifications `Function.update n k m k = m` and `Function.update n k m j = n j` for `j ≠ k`), and
`(𝒮 ×_k M)(α₁, …, i, …, α_d) = ∑_j M(i, j) 𝒮(α₁, …, j, …, α_d)`. The backbone's
`Tensor.modeUnfold_rectModeProd`. -/
theorem equation_12_4_14 (S : RTensor n) (k : Fin d) {m : ℕ} (M : Matrix (Fin m) (Fin (n k)) ℝ) :
    (modeProduct n S k M).modeUnfold k =
        (M * S.modeUnfold k).reindex (finCongr (Function.update_self k m n).symm)
          (Equiv.piCongrRight fun j : {j // j ≠ k} =>
            finCongr (Function.update_of_ne j.2 m n).symm) ∧
      ∀ a : ∀ i, Fin (Function.update n k m i), modeProduct n S k M a =
        ∑ y : Fin (n k), M (Fin.cast (Function.update_self k m n) (a k)) y *
          S (spliceIndex k a y) := by
  have h1 : (modeProduct n S k M).modeUnfold k =
      (M * S.modeUnfold k).reindex (finCongr (Function.update_self k m n).symm)
        (Equiv.piCongrRight fun j : {j // j ≠ k} =>
          finCongr (Function.update_of_ne j.2 m n).symm) := by
    rw [modeProduct, Tensor.modeUnfold_rectModeProd]
    ext x c
    simp only [submatrix_apply, reindex_apply, mul_apply, id, Equiv.refl_symm, Equiv.coe_refl]
    rfl
  refine ⟨h1, fun a => ?_⟩
  rw [← Tensor.modeUnfold_apply (modeProduct n S k M) k a, h1, reindex_apply, submatrix_apply,
    mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  simp only [Tensor.modeUnfold, of_apply]
  congr 1
  funext i
  by_cases h : i = k
  · subst h
    simp [spliceIndex, Equiv.piSplitAt_symm_apply]
  · simp [spliceIndex, Equiv.piSplitAt_symm_apply, h]

/-- The entries of a rectangular mode product (the second half of `equation_12_4_14`). -/
theorem modeProduct_apply (S : RTensor n) (k : Fin d) {m : ℕ} (M : Matrix (Fin m) (Fin (n k)) ℝ)
    (a : ∀ i, Fin (Function.update n k m i)) :
    modeProduct n S k M a = ∑ y : Fin (n k),
      M (Fin.cast (Function.update_self k m n) (a k)) y * S (spliceIndex k a y) :=
  (equation_12_4_14 S k M).2 a

/-- A tensor read in an equal shape: the transport of `A : RTensor n` along `n = n'`. -/
def castShape {n' : Fin d → ℕ} (h : n = n') (A : RTensor n) : RTensor n' :=
  h ▸ A

/-- Reading a tensor through an equality of shapes: the entries are those at the cast indices. -/
theorem castShape_apply {n' : Fin d → ℕ} (h : n = n') (A : RTensor n) (i : ∀ k, Fin (n' k)) :
    castShape h A i = A fun k => Fin.cast (congrFun h k).symm (i k) := by
  subst h
  rfl

/-- A rectangular mode product read in an equal shape is the rectangular mode product into that
shape, the equivalences and the rows of the factor read through the casts. -/
theorem castShape_rectModeProd {s s' : Fin d → ℕ} (h : s = s') (S : RTensor n) (k : Fin d)
    (e : ∀ i, i ≠ k → Fin (s i) ≃ Fin (n i)) (M : Matrix (Fin (s k)) (Fin (n k)) ℝ) :
    castShape h (S.rectModeProd k (μ := fun i => Fin (s i)) e M) =
      S.rectModeProd k (μ := fun i => Fin (s' i))
        (fun i hi => (finCongr (congrFun h i).symm).trans (e i hi))
        (M.submatrix (finCongr (congrFun h k).symm) id) := by
  subst h
  rfl

/-- **(12.4.16)**: mode products in distinct modes commute, `(𝒮 ×_k F) ×_j G = (𝒮 ×_j G) ×_k F` for
`j ≠ k` and rectangular `F ∈ ℝ^{p × n_k}`, `G ∈ ℝ^{q × n_j}`; the two shapes are identified along
`Function.update_comm` (and each second factor reads its columns in the updated shape). The
backbone's `Tensor.rectModeProd_comm`. -/
theorem equation_12_4_16 (S : RTensor n) {j k : Fin d} (hjk : j ≠ k) {p q : ℕ}
    (F : Matrix (Fin p) (Fin (n k)) ℝ) (G : Matrix (Fin q) (Fin (n j)) ℝ) :
    modeProduct (Function.update n k p) (modeProduct n S k F) j
        (G.reindex (Equiv.refl _) (finCongr (Function.update_of_ne hjk p n).symm)) =
      castShape (Function.update_comm hjk q p n)
        (modeProduct (Function.update n j q) (modeProduct n S j G) k
          (F.reindex (Equiv.refl _) (finCongr (Function.update_of_ne hjk.symm q n).symm))) := by
  rw [modeProduct, modeProduct, modeProduct, modeProduct, castShape_rectModeProd,
    Tensor.rectModeProd_comm _ hjk (f := fun _ h => finCongr (Function.update_of_ne h q n))
      (f' := fun i hi => (finCongr (congrFun (Function.update_comm hjk q p n) i).symm).trans
        (finCongr (Function.update_of_ne hi p (Function.update n j q))))]
  · congr 1
  · intro i hj hk
    ext x
    simp

/-- **(12.4.17)**, corrected: `(𝒮 ×_k F) ×_k G = 𝒮 ×_k (G F)` for rectangular `F ∈ ℝ^{p × n_k}`,
`G ∈ ℝ^{q × p}`; the two shapes are identified along `Function.update_idem`. The book prints
`𝒮 ×_k (F G)`, which is false (`(𝒮 ×_k F)_(k) = F 𝒮_(k)`, so the second product gives `G F 𝒮_(k)`)
and does not typecheck for rectangular `F`, `G`. The backbone's `Tensor.rectModeProd_rectModeProd`.
-/
theorem equation_12_4_17 (S : RTensor n) (k : Fin d) {p q : ℕ} (F : Matrix (Fin p) (Fin (n k)) ℝ)
    (G : Matrix (Fin q) (Fin p) ℝ) :
    modeProduct (Function.update n k p) (modeProduct n S k F) k
        (G.reindex (Equiv.refl _) (finCongr (Function.update_self k p n).symm)) =
      castShape (Function.update_idem (a := k) p q n).symm (modeProduct n S k (G * F)) := by
  rw [modeProduct, modeProduct, modeProduct, castShape_rectModeProd,
    Tensor.rectModeProd_rectModeProd]
  congr 1
  ext a b
  simp only [reindex_apply, submatrix_apply, mul_apply, id, Equiv.refl_symm, Equiv.coe_refl]
  rw [← (finCongr (Function.update_self k p n)).sum_comp]
  rfl

/-- **(12.4.14)** for a square factor: the rectangular mode product agrees with the backbone's
shape-preserving `Tensor.modeProd` up to the identification `Function.update n k (n k) = n`. -/
theorem modeProduct_eq_modeProd (S : RTensor n) (k : Fin d)
    (M : Matrix (Fin (n k)) (Fin (n k)) ℝ) :
    modeProduct n S k M = castShape (Function.update_eq_self k n).symm (S.modeProd k M) := by
  rw [← Tensor.rectModeProd_refl, castShape_rectModeProd, modeProduct]
  congr 1

end ModeProduct

/-! ### Vectorizing a mode product (12.4.15) -/

section VecModeProduct

/-- The size `n₁ ⋯ n_{k−1}` of the modes before mode `k` (0-based: the modes `0, …, k − 1`). -/
def lowerSize (n : Fin d → ℕ) (k : Fin d) : ℕ :=
  ∏ j : Fin k, n (Fin.castLE k.2.le j)

/-- The size `n_{k+1} ⋯ n_d` of the modes after mode `k`. -/
def upperSize (n : Fin d → ℕ) (k : Fin d) : ℕ :=
  ∏ j : Fin (d - (k + 1)), n ⟨k + 1 + j, by have := j.2; omega⟩

/-- `n₁ ⋯ n_d = (n_{k+1} ⋯ n_d) n_k (n₁ ⋯ n_{k−1})`. -/
theorem prod_eq_upperSize_mul (n : Fin d → ℕ) (k : Fin d) :
    ∏ i, n i = upperSize n k * n k * lowerSize n k := by
  set g : ℕ → ℕ := fun l => if h : l < d then n ⟨l, h⟩ else 1 with hg
  have hT : ∏ i, n i = ∏ i : Fin d, g i := Finset.prod_congr rfl fun i _ => by
    rw [hg]; simp only [i.2, ↓reduceDIte]
  have hL : lowerSize n k = ∏ j : Fin k, g j := Finset.prod_congr rfl fun j _ => by
    rw [hg]; simp only [show (j : ℕ) < d by omega, ↓reduceDIte]; rfl
  have hU : upperSize n k = ∏ j : Fin (d - (k + 1)), g (k + 1 + j) :=
    Finset.prod_congr rfl fun j _ => by
      rw [hg]; simp only [show (k : ℕ) + 1 + j < d by omega, ↓reduceDIte]
  have hk : g k = n k := by rw [hg]; simp only [k.2, ↓reduceDIte]
  have hd : d = k + 1 + (d - (k + 1)) := by omega
  rw [hT, hL, hU, Fin.prod_univ_eq_prod_range g d, Fin.prod_univ_eq_prod_range g k,
    Fin.prod_univ_eq_prod_range (fun j => g (k + 1 + j)),
    show Finset.range d = Finset.range (k + 1 + (d - (k + 1))) by rw [← hd],
    Finset.prod_range_add, Finset.prod_range_succ, hk]
  ring

/-- The size of `𝒮 ×_k M` for `M ∈ ℝ^{m × n_k}`: `(n_{k+1} ⋯ n_d) m (n₁ ⋯ n_{k−1})`. -/
theorem prod_update_eq_upperSize_mul (n : Fin d → ℕ) (k : Fin d) (m : ℕ) :
    ∏ i, Function.update n k m i = upperSize n k * m * lowerSize n k := by
  have hU : upperSize (Function.update n k m) k = upperSize n k :=
    Finset.prod_congr rfl fun j _ => Function.update_of_ne
      (Fin.ne_of_val_ne (show (k : ℕ) + 1 + j ≠ k by omega)) _ _
  have hL : lowerSize (Function.update n k m) k = lowerSize n k :=
    Finset.prod_congr rfl fun j _ => Function.update_of_ne
      (Fin.ne_of_val_ne (show (j : ℕ) ≠ k by omega)) _ _
  rw [prod_eq_upperSize_mul (Function.update n k m) k, Function.update_self, hU, hL]

/-- Reading the middle factor of `I ⊗ M ⊗ I` through an equality of its row count. -/
private theorem kroneckerFin_reindex_cast {R : Type*} [CommSemiring R] {H L a b p N P : ℕ}
    (h : a = b) (M : Matrix (Fin a) (Fin p) R) (hN : N = H * b * L) (hN' : N = H * a * L)
    (c : Fin P → Fin (H * p * L)) :
    (kroneckerFin (kroneckerFin (1 : Matrix (Fin H) (Fin H) R)
        (M.reindex (finCongr h) (Equiv.refl _))) (1 : Matrix (Fin L) (Fin L) R)).submatrix
        (finCongr hN) c =
      (kroneckerFin (kroneckerFin (1 : Matrix (Fin H) (Fin H) R) M)
        (1 : Matrix (Fin L) (Fin L) R)).submatrix (finCongr hN') c := by
  subst h
  rfl

/-- **(12.4.15)**: `vec(𝒮 ×_k M) = (I_{n_{k+1}⋯n_d} ⊗ M ⊗ I_{n₁⋯n_{k−1}}) vec(𝒮)` for a rectangular
`M ∈ ℝ^{m × n_k}`, with chapter 1's positional `Matrix.kroneckerFin` and the book's `vec`
(`Tensor.vecFin`, the little-endian `col`), up to the identification of the size products. The
backbone's `Tensor.vecFin_rectModeProd`. -/
theorem equation_12_4_15 {n : Fin d → ℕ} (S : RTensor n) (k : Fin d) {m : ℕ}
    (M : Matrix (Fin m) (Fin (n k)) ℝ) :
    Tensor.vecFin (modeProduct n S k M) =
      (kroneckerFin (kroneckerFin (1 : Matrix (Fin (upperSize n k)) (Fin (upperSize n k)) ℝ) M)
          (1 : Matrix (Fin (lowerSize n k)) (Fin (lowerSize n k)) ℝ)).submatrix
        (finCongr (prod_update_eq_upperSize_mul n k m)) (finCongr (prod_eq_upperSize_mul n k)) *ᵥ
        Tensor.vecFin S := by
  have h := Tensor.vecFin_rectModeProd S k (m := Function.update n k m)
    (fun _ h => Function.update_of_ne h m n)
    (M.reindex (finCongr (Function.update_self k m n).symm) (Equiv.refl _))
  rw [modeProduct, h, kroneckerFin_reindex_cast (Function.update_self k m n).symm M]
  rfl

end VecModeProduct

/-! ### The multilinear product of order 4 (12.4.18)–(12.4.19) -/

section Order4

/-- The positional index of an order-4 index tuple: `col(i, n) − 1` is the big-endian index of
`(i₄, (i₃, (i₂, i₁)))`. -/
theorem finPiFinEquiv_four {n : Fin 4 → ℕ} (h : ∏ k, n k = n 3 * (n 2 * (n 1 * n 0)))
    (a : ∀ k, Fin (n k)) :
    finCongr h (finPiFinEquiv a) =
      finProdFinEquiv (a 3, finProdFinEquiv (a 2, finProdFinEquiv (a 1, a 0))) := by
  apply Fin.ext
  rw [finCongr_apply, Fin.val_cast, finPiFinEquiv_apply]
  simp [Fin.sum_univ_four, finProdFinEquiv_apply_val, Fin.prod_univ_succ]
  ring

/-- **(12.4.18) ⇔ (12.4.19)**, order 4: `𝒜(i) = ∑_j 𝒮(j) M₁(i₁, j₁) M₂(i₂, j₂) M₃(i₃, j₃) M₄(i₄,
j₄)` is `vec(𝒜) = (M₄ ⊗ M₃ ⊗ M₂ ⊗ M₁) vec(𝒮)` (chapter 1's positional `Matrix.kroneckerFin`, up to
the identification of the size products); and, for square factors, the table after (12.4.19): the
multilinear product is the sequence of the four mode products, in any order
(`𝒮 ×₁ M₁ ×₂ M₂ ×₃ M₃ ×₄ M₄ = 𝒮 ×₄ M₄ ×₁ M₁ ×₂ M₂ ×₃ M₃`). -/
theorem equation_12_4_19 {n m : Fin 4 → ℕ} (M : ∀ k, Matrix (Fin (m k)) (Fin (n k)) ℝ)
    (S : RTensor n) :
    (∀ i, (Tensor.multilinearProd M S : RTensor m) i = ∑ j, S j * ∏ k, M k (i k) (j k)) ∧
      Tensor.vecFin (Tensor.multilinearProd M S : RTensor m) =
        (kroneckerFin (M 3) (kroneckerFin (M 2) (kroneckerFin (M 1) (M 0)))).submatrix
          (finCongr (by rw [Fin.prod_univ_four]; ring))
          (finCongr (by rw [Fin.prod_univ_four]; ring)) *ᵥ
          Tensor.vecFin S ∧
      ∀ (N : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ),
        Tensor.multilinearProd N S =
            [0, 1, 2, 3].foldl (fun T k => T.modeProd k (N k)) S ∧
          Tensor.multilinearProd N S =
            [3, 0, 1, 2].foldl (fun T k => T.modeProd k (N k)) S := by
  refine ⟨fun i => ?_, ?_, fun N => ⟨?_, ?_⟩⟩
  · rw [Tensor.multilinearProd_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rw [Tensor.vecFin_multilinearProd]
    congr 1
    ext I J
    obtain ⟨a, rfl⟩ := finPiFinEquiv.surjective I
    obtain ⟨b, rfl⟩ := finPiFinEquiv.surjective J
    rw [reindex_apply, submatrix_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, finPiFinEquiv_four, finPiFinEquiv_four, kroneckerFin_apply,
      kroneckerFin_apply, kroneckerFin_apply, piKronecker_apply, Fin.prod_univ_four]
    ring
  · exact Tensor.multilinearProd_eq_modeProd N (by decide) (by decide) S
  · exact Tensor.multilinearProd_eq_modeProd N (by decide) (by decide) S

end Order4

/-! ### Theorem 12.4.1 -/

section Theorem1241

variable {n m : Fin (d + 1) → ℕ}

/-- **Theorem 12.4.1**: for `𝒮 ∈ ℝ^{n₁ × ⋯ × n_d}`, `M_k ∈ ℝ^{m_k × n_k}` and
`𝒜 = 𝒮 ×₁ M₁ ⋯ ×_d M_d` (`Tensor.multilinearProd M S`),
`𝒜_(k) = M_k 𝒮_(k) (M_d ⊗ ⋯ ⊗ M_{k+1} ⊗ M_{k−1} ⊗ ⋯ ⊗ M₁)ᵀ` for the book's flattened unfoldings,
the Kronecker product of the other factors being their flattened family product (the book's
reversed order, `Matrix.piKronecker_reindex_finPiFinEquiv`). -/
theorem theorem_12_4_1 (M : ∀ k, Matrix (Fin (m k)) (Fin (n k)) ℝ) (S : RTensor n)
    (k : Fin (d + 1)) :
    modalUnfolding (Tensor.multilinearProd M S : RTensor m) k =
      M k * modalUnfolding S k *
        ((piKronecker fun j : Fin d => M (k.succAbove j)).reindex finPiFinEquiv
          finPiFinEquiv)ᵀ := by
  have hP : (piKronecker fun j : {j // j ≠ k} => M j).reindex (modalColumnEquiv m k)
      (modalColumnEquiv n k) =
        (piKronecker fun j : Fin d => M (k.succAbove j)).reindex finPiFinEquiv finPiFinEquiv := by
    ext a b
    obtain ⟨a', rfl⟩ := (modalColumnEquiv m k).surjective a
    obtain ⟨b', rfl⟩ := (modalColumnEquiv n k).surjective b
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, piKronecker_apply,
      modalColumnEquiv_symm_apply]
    rw [← (finSuccAboveEquiv k).prod_comp]
    rfl
  rw [modalUnfolding, Tensor.modeUnfold_multilinearProd, modalUnfolding, ← hP]
  simp only [reindex_apply, Equiv.refl_symm, Equiv.coe_refl, transpose_submatrix]
  rw [Matrix.submatrix_mul _ _ id (modalColumnEquiv n k).symm _
      (modalColumnEquiv n k).symm.bijective,
    Matrix.submatrix_mul _ _ id id _ Function.bijective_id, submatrix_id_id]

/-- **Theorem 12.4.1**, second statement: if `M₁, …, M_d` are all nonsingular then
`𝒮 = 𝒜 ×₁ M₁⁻¹ ⋯ ×_d M_d⁻¹`. -/
theorem theorem_12_4_1_b {n : Fin d → ℕ} (M : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ)
    (hM : ∀ k, IsUnit (M k)) (S A : RTensor n) (h : A = Tensor.multilinearProd M S) :
    S = Tensor.multilinearProd (fun k => (M k)⁻¹) A :=
  Tensor.multilinearProd_inv hM h

end Theorem1241

end GolubVanLoan.Chapter12
