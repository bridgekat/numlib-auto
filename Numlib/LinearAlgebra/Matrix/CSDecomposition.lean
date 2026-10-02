/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside a future SVD.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv

/-!
# The CS decomposition

The blocks of a matrix with orthonormal columns, and of a unitary matrix partitioned into 2-by-2
blocks, have simultaneously diagonalizable SVDs: the *cosine–sine* (CS) decomposition
([golub2013matrix] §2.5.4, Theorems 2.5.2 and 2.5.3, after C. C. Paige and M. A. Saunders,
SIAM J. Numer. Anal. 18 (1981)).

## Main definitions

* `Matrix.IsThinCSD Q₁ Q₂ U₁ U₂ V θ`: a thin CS decomposition of the stacked matrix `[Q₁; Q₂]`:
  unitary `U₁`, `U₂`, `V` and angles `0 ≤ θ₀ ≤ θ₁ ≤ ⋯ ≤ π/2` with `U₁ᴴ Q₁ V = diag(cos θ)` and
  `U₂ᴴ Q₂ V = diag(sin θ)`, the latter shifted by `p = n₁ − min n₁ m₂` columns when `Q₂` has fewer
  rows than columns.
* `Matrix.IsCSD Q₁₁ Q₁₂ Q₂₁ Q₂₂ U₁ U₂ V₁ V₂ θ`: a CS decomposition of the unitary matrix
  `fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂`, in the 5-by-5 block form of [golub2013matrix] Theorem 2.5.3; it
  extends the thin CS decomposition `Matrix.IsThinCSD Q₁₁ Q₂₁ U₁ U₂ V₁ θ` of the first block column.

The field names follow the two-sided factorizations (`Matrix.IsUnitaryEquiv`): *left* and *right*
name the side of the factored block, the subscripts the block row or column (`U₁`, `U₂` on the
left, `V₁`, `V₂` on the right), and `star_mul_mul₁` … `star_mul_mul₂₂` the blocks
(`Matrix.IsThinCSD.isUnitaryEquiv₁`, `Matrix.IsThinCSD.isUnitaryEquiv₂` package the two blocks of
a thin CS decomposition as unitary equivalences).

## Main results

* `Matrix.exists_isThinCSD`: [golub2013matrix] Theorem 2.5.2, without its hypothesis `m₂ ≥ n₁`.
* `Matrix.exists_isCSD`: [golub2013matrix] Theorem 2.5.3.

## Implementation notes

The shapes are `Fin` so that the diagonal factors are `Matrix.rectDiagonal` and
`Matrix.shiftedRectDiagonal` of a function `ℕ → 𝕜`, as in `Matrix.exists_svd`; one monotone
`θ : ℕ → ℝ` carries the angles (a monotone extension past `n₁` always exists). "The columns of
`[Q₁; Q₂]` are orthonormal" is `Q₁ᴴ Q₁ + Q₂ᴴ Q₂ = 1`. When `m₂ < n₁` at least `p = n₁ − m₂` of the
cosines equal `1`: the nonzero columns of `Q₂ V` are orthogonal vectors of `𝕜^{m₂}`.

## References

* [golub2013matrix] §2.5.4; C. C. Paige, M. A. Saunders, *Towards a generalized singular value
  decomposition*, SIAM J. Numer. Anal. 18 (1981).
-/

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Thin

variable {m₁ m₂ n₁ : ℕ}

/-- **A thin CS decomposition, as a specification** ([golub2013matrix] Theorem 2.5.2, without its
hypothesis `m₂ ≥ n₁`): unitary `U₁`, `U₂`, `V` and monotone angles `θ i ∈ [0, π/2]`, the first
`p = n₁ − min n₁ m₂` of them `0`, with `U₁ᴴ Q₁ V = rectDiagonal (cos θ)` and
`U₂ᴴ Q₂ V = shiftedRectDiagonal p (sin θ)`. For `m₂ ≥ n₁` (the book's case) `p = 0` and the sine
block is `rectDiagonal` (`Matrix.shiftedRectDiagonal_zero`). -/
structure IsThinCSD (Q₁ : Matrix (Fin m₁) (Fin n₁) 𝕜) (Q₂ : Matrix (Fin m₂) (Fin n₁) 𝕜)
    (U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜) (U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜)
    (V : Matrix (Fin n₁) (Fin n₁) 𝕜) (θ : ℕ → ℝ) : Prop where
  /-- The first left factor is unitary. -/
  mem_unitaryGroup_left₁ : U₁ ∈ unitaryGroup (Fin m₁) 𝕜
  /-- The second left factor is unitary. -/
  mem_unitaryGroup_left₂ : U₂ ∈ unitaryGroup (Fin m₂) 𝕜
  /-- The right factor is unitary. -/
  mem_unitaryGroup_right : V ∈ unitaryGroup (Fin n₁) 𝕜
  /-- The angles are sorted. -/
  monotone : Monotone θ
  /-- The angles lie in `[0, π/2]`. -/
  mem_Icc : ∀ i, θ i ∈ Set.Icc 0 (Real.pi / 2)
  /-- The first `p = n₁ − min n₁ m₂` angles vanish. -/
  eq_zero_of_lt : ∀ i < n₁ - min n₁ m₂, θ i = 0
  /-- The cosine block `U₁ᴴ Q₁ V`. -/
  star_mul_mul₁ : star U₁ * Q₁ * V = rectDiagonal fun i => ((Real.cos (θ i) : ℝ) : 𝕜)
  /-- The sine block `U₂ᴴ Q₂ V`. -/
  star_mul_mul₂ :
    star U₂ * Q₂ * V = shiftedRectDiagonal (n₁ - min n₁ m₂) fun i => ((Real.sin (θ i) : ℝ) : 𝕜)

variable {Q₁ : Matrix (Fin m₁) (Fin n₁) 𝕜} {Q₂ : Matrix (Fin m₂) (Fin n₁) 𝕜}

section Deprecated

variable {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜}
  {V : Matrix (Fin n₁) (Fin n₁) 𝕜} {θ : ℕ → ℝ}

/-- The cosine block (the former field name). -/
@[deprecated IsThinCSD.star_mul_mul₁ (since := "2026-09-30")]
theorem IsThinCSD.star_mul_mul_left (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) :
    star U₁ * Q₁ * V = rectDiagonal fun i => ((Real.cos (θ i) : ℝ) : 𝕜) :=
  h.star_mul_mul₁

/-- The sine block (the former field name). -/
@[deprecated IsThinCSD.star_mul_mul₂ (since := "2026-09-30")]
theorem IsThinCSD.star_mul_mul_right (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) :
    star U₂ * Q₂ * V = shiftedRectDiagonal (n₁ - min n₁ m₂) fun i => ((Real.sin (θ i) : ℝ) : 𝕜) :=
  h.star_mul_mul₂

end Deprecated

/-- The cosine block of a thin CS decomposition as a two-sided unitary equivalence. -/
theorem IsThinCSD.isUnitaryEquiv₁ {U₁ U₂ V θ} (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) :
    IsUnitaryEquiv Q₁ U₁ (rectDiagonal fun i => ((Real.cos (θ i) : ℝ) : 𝕜)) V :=
  ⟨h.mem_unitaryGroup_left₁, h.mem_unitaryGroup_right, h.star_mul_mul₁⟩

/-- The sine block of a thin CS decomposition as a two-sided unitary equivalence. -/
theorem IsThinCSD.isUnitaryEquiv₂ {U₁ U₂ V θ} (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) :
    IsUnitaryEquiv Q₂ U₂
      (shiftedRectDiagonal (n₁ - min n₁ m₂) fun i => ((Real.sin (θ i) : ℝ) : 𝕜)) V :=
  ⟨h.mem_unitaryGroup_left₂, h.mem_unitaryGroup_right, h.star_mul_mul₂⟩

/-- The angles of a thin CS decomposition have nonnegative cosines. -/
theorem IsThinCSD.cos_nonneg {U₁ U₂ V θ} (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) (i : ℕ) :
    0 ≤ Real.cos (θ i) :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [(h.mem_Icc i).1, Real.pi_pos], (h.mem_Icc i).2⟩

/-- The angles of a thin CS decomposition have nonnegative sines. -/
theorem IsThinCSD.sin_nonneg {U₁ U₂ V θ} (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) (i : ℕ) :
    0 ≤ Real.sin (θ i) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (h.mem_Icc i).1 (by linarith [(h.mem_Icc i).2, Real.pi_pos])

/-- The Gram matrix of `Q₂ V` in the proof of the thin CS decomposition: if `Q₁ᴴ Q₁ + Q₂ᴴ Q₂ = 1`
and `U₁ᴴ Q₁ V = diag(c)` with `n₁ ≤ m₁`, then `(Q₂ V)ᴴ (Q₂ V) = diag(1 − |c_j|²)`. -/
private theorem gram_mul_eq_diagonal (hQ : Q₁ᴴ * Q₁ + Q₂ᴴ * Q₂ = 1) (hnm : n₁ ≤ m₁)
    {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {V : Matrix (Fin n₁) (Fin n₁) 𝕜}
    (hU₁ : U₁ ∈ unitaryGroup (Fin m₁) 𝕜) (hV : V ∈ unitaryGroup (Fin n₁) 𝕜) {c : ℕ → ℝ}
    (hc : star U₁ * Q₁ * V = rectDiagonal fun i => ((c i : ℝ) : 𝕜)) :
    (Q₂ * V)ᴴ * (Q₂ * V) = diagonal fun j : Fin n₁ => ((1 - c j ^ 2 : ℝ) : 𝕜) := by
  have hQ₁ : Q₁ * V = U₁ * rectDiagonal fun i => ((c i : ℝ) : 𝕜) := by
    rw [← hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU₁,
      Matrix.one_mul]
  have hVV := conjTranspose_mul_self_of_mem_unitaryGroup hV
  have hUU := conjTranspose_mul_self_of_mem_unitaryGroup hU₁
  have h1 : (Q₂ * V)ᴴ * (Q₂ * V) = 1 - (Q₁ * V)ᴴ * (Q₁ * V) := by
    rw [eq_sub_iff_add_eq, conjTranspose_mul, conjTranspose_mul]
    calc Vᴴ * Q₂ᴴ * (Q₂ * V) + Vᴴ * Q₁ᴴ * (Q₁ * V) = Vᴴ * (Q₁ᴴ * Q₁ + Q₂ᴴ * Q₂) * V := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]; abel
      _ = 1 := by rw [hQ, Matrix.mul_one, hVV]
  rw [h1, hQ₁, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₁ᴴ, hUU, Matrix.one_mul,
    conjTranspose_rectDiagonal_mul_self, ← diagonal_one, diagonal_sub]
  congr 1
  funext j
  rw [ite_eq_left (lt_of_lt_of_le j.isLt hnm)]
  simp [sq]

/-- A column of a matrix whose Gram diagonal entry vanishes is zero. -/
private theorem apply_eq_zero_of_gram_apply_eq_zero {m n : Type*} [Fintype m] {W : Matrix m n 𝕜}
    {j : n} (h : (Wᴴ * W) j j = 0) (k : m) : W k j = 0 := by
  have h0 : star (fun k => W k j) ⬝ᵥ (fun k => W k j) = 0 := by
    rw [← h, mul_apply]
    rfl
  exact congrFun (dotProduct_star_self_eq_zero.1 h0) k

/-- **The thin CS decomposition** ([golub2013matrix] Theorem 2.5.2, without its hypothesis
`m₂ ≥ n₁`): if `Q₁ᴴ Q₁ + Q₂ᴴ Q₂ = 1` and `n₁ ≤ m₁`, then `[Q₁; Q₂]` has a thin CS decomposition.
Following the book: an SVD `U₁ᴴ Q₁ V = diag(c)` has `1 ≥ c₀ ≥ ⋯ ≥ 0`; the columns of `Q₂ V` are
pairwise orthogonal with squared norms `1 − c_j²`, so at most `m₂` of them are nonzero, whence the
first `p = n₁ − min n₁ m₂` cosines are `1`; the normalized nonzero columns, placed at the positions
`j − p`, extend to a unitary `U₂` (`Matrix.exists_mem_unitaryGroup_submatrix_eq`), and
`θ_j = arccos c_j`. -/
theorem exists_isThinCSD (Q₁ : Matrix (Fin m₁) (Fin n₁) 𝕜) (Q₂ : Matrix (Fin m₂) (Fin n₁) 𝕜)
    (hQ : Q₁ᴴ * Q₁ + Q₂ᴴ * Q₂ = 1) (hnm : n₁ ≤ m₁) :
    ∃ U₁ U₂ V θ, IsThinCSD Q₁ Q₂ U₁ U₂ V θ := by
  classical
  obtain ⟨U₁, c, V, hs⟩ := exists_isSVD Q₁
  set p := n₁ - min n₁ m₂ with hp
  set W := Q₂ * V with hW
  have hWW := gram_mul_eq_diagonal hQ hnm hs.mem_unitaryGroup_left hs.mem_unitaryGroup_right
    hs.star_mul_mul
  rw [← hW] at hWW
  -- the cosines lie in `[0, 1]`
  have hc1 : ∀ j : Fin n₁, c j ≤ 1 := fun j => by
    have h := (posSemidef_conjTranspose_mul_self W).diag_nonneg (i := j)
    rw [hWW, diagonal_apply_eq, RCLike.ofReal_nonneg] at h
    nlinarith [hs.nonneg j]
  -- a column of `W` with `c_j = 1` vanishes
  have hWz : ∀ j : Fin n₁, c j = 1 → ∀ k, W k j = 0 := fun j hj =>
    apply_eq_zero_of_gram_apply_eq_zero (by rw [hWW, diagonal_apply_eq, hj]; simp)
  -- at most `m₂` of the cosines differ from `1`
  have hcard : Fintype.card {j : Fin n₁ // c j ≠ 1} ≤ m₂ := by
    have h := rank_le_card_height W
    rw [← rank_conjTranspose_mul_self, hWW, rank_diagonal, Fintype.card_fin] at h
    refine le_trans (le_of_eq (Fintype.card_congr (Equiv.subtypeEquivRight fun j => ?_))) h
    rw [ne_eq, ne_eq, RCLike.ofReal_eq_zero, sub_eq_zero, @eq_comm ℝ 1 (c j ^ 2),
      pow_eq_one_iff_of_nonneg (hs.nonneg j) two_ne_zero]
  -- hence the first `p` cosines are `1`
  have hcp : ∀ j : Fin n₁, (j : ℕ) < p → c j = 1 := by
    intro j hj
    by_contra hne
    have hlt : ∀ k : Fin n₁, (j : ℕ) ≤ k → c k ≠ 1 := fun k hk hk1 =>
      hne (le_antisymm (hc1 j) (hk1 ▸ hs.antitone hk))
    have hinj : Fintype.card (Fin (n₁ - j)) ≤ Fintype.card {k : Fin n₁ // c k ≠ 1} :=
      Fintype.card_le_of_injective
        (fun k => ⟨⟨j + k, by omega⟩, hlt _ (by simp)⟩)
        (fun a b hab => by
          simp only [Subtype.mk.injEq, Fin.mk.injEq, Nat.add_left_cancel_iff] at hab
          exact Fin.ext hab)
    rw [Fintype.card_fin] at hinj
    omega
  have hpj : ∀ j : Fin n₁, c j ≠ 1 → p ≤ j := fun j hj => by
    by_contra h
    exact hj (hcp j (by omega))
  -- the sines
  set s : ℕ → ℝ := fun j => Real.sqrt (1 - c j ^ 2) with hsdef
  have hs0 : ∀ j : Fin n₁, c j ≠ 1 → s j ≠ 0 := fun j hj => by
    have hlt : c j < 1 := lt_of_le_of_ne (hc1 j) hj
    have : 0 < 1 - c j ^ 2 := by nlinarith [hs.nonneg j]
    exact (Real.sqrt_pos.2 this).ne'
  have hsq : ∀ j : ℕ, c j ≤ 1 → s j ^ 2 = 1 - c j ^ 2 := fun j hj =>
    Real.sq_sqrt (by nlinarith [hs.nonneg j])
  -- the normalized nonzero columns of `W`
  set r := {j : Fin n₁ // c j ≠ 1}
  set Z : Matrix (Fin m₂) r 𝕜 :=
    W.submatrix id Subtype.val * diagonal fun k : r => (((s k : ℝ) : 𝕜))⁻¹ with hZ
  have hZZ : Zᴴ * Z = 1 := by
    have hW1 : (W.submatrix id Subtype.val)ᴴ * W.submatrix id (Subtype.val : r → Fin n₁)
        = diagonal fun k : r => ((1 - c k ^ 2 : ℝ) : 𝕜) := by
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id, hWW,
        submatrix_diagonal _ _ Subtype.val_injective]
      rfl
    rw [hZ, conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ _ (diagonal _), hW1, diagonal_mul_diagonal, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext k
    have hk : ((s k : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (hs0 k.1 k.2)
    rw [← hsq k (hc1 k)]
    simp only [Pi.star_apply, star_inv₀, RCLike.star_def, RCLike.conj_ofReal]
    push_cast
    field_simp
  -- the placement `j ↦ j − p`
  have hfle : ∀ k : r, (k.1 : ℕ) - p < m₂ := fun k => by
    have := k.1.isLt
    have := hpj k.1 k.2
    omega
  let f : r ↪ Fin m₂ := ⟨fun k => ⟨k.1 - p, hfle k⟩, fun a b hab => by
    have ha := hpj a.1 a.2
    have hb := hpj b.1 b.2
    simp only [Fin.mk.injEq] at hab
    exact Subtype.ext (Fin.ext (by omega))⟩
  obtain ⟨U₂, hU₂, hU₂Z⟩ := exists_mem_unitaryGroup_submatrix_eq Z hZZ f
  -- the angles
  set θ : ℕ → ℝ := fun i => if i < n₁ then Real.arccos (c i) else Real.pi / 2 with hθ
  have hcos : ∀ i : ℕ, i < n₁ → Real.cos (θ i) = c i := fun i hi => by
    rw [hθ]
    dsimp only
    rw [ite_eq_left hi]
    exact Real.cos_arccos (by linarith [hs.nonneg i]) (hc1 ⟨i, hi⟩)
  have hsin : ∀ i : ℕ, i < n₁ → Real.sin (θ i) = s i := fun i hi => by
    rw [hθ]
    dsimp only
    rw [ite_eq_left hi, Real.sin_arccos]
  refine ⟨U₁, U₂, V, θ, hs.mem_unitaryGroup_left, hU₂, hs.mem_unitaryGroup_right, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro i i' hii'
    simp only [hθ]
    split_ifs with h1 h2 h2
    · exact Real.arccos_le_arccos (hs.antitone hii')
    · exact Real.arccos_le_pi_div_two.2 (hs.nonneg i)
    · omega
    · exact le_rfl
  · intro i
    simp only [hθ]
    split_ifs
    · exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (hs.nonneg i)⟩
    · exact ⟨by linarith [Real.pi_pos], le_rfl⟩
  · intro i hi
    have hin : i < n₁ := by omega
    rw [hθ]
    dsimp only
    rw [ite_eq_left hin, hcp ⟨i, hin⟩ hi, Real.arccos_one]
  · rw [hs.star_mul_mul]
    exact rectDiagonal_congr fun i _ hi => by rw [hcos i hi]
  · rw [Matrix.mul_assoc, ← hW]
    ext i j
    rw [mul_apply, shiftedRectDiagonal_apply, hsin j j.isLt]
    by_cases hj : c j = 1
    · have hsj : s j = 0 := by rw [hsdef]; simp [hj]
      rw [hsj, RCLike.ofReal_zero, ite_self]
      exact Finset.sum_eq_zero fun k _ => by rw [hWz j hj k, mul_zero]
    · set jr : r := ⟨j, hj⟩
      have hWk : ∀ k, W k j = ((s j : ℝ) : 𝕜) * U₂ k (f jr) := fun k => by
        have := congrFun (congrFun hU₂Z k) jr
        rw [submatrix_apply, id] at this
        rw [this, hZ, mul_diagonal, submatrix_apply, id, mul_comm (W k _), ← mul_assoc,
          mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 (hs0 j hj)), one_mul]
      simp only [hWk, star_apply]
      have hsum : ∑ k, star (U₂ k i) * (((s j : ℝ) : 𝕜) * U₂ k (f jr))
          = ((s j : ℝ) : 𝕜) * (star U₂ * U₂) i (f jr) := by
        rw [mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [star_apply]; ring
      rw [hsum, mem_unitaryGroup_iff'.1 hU₂, one_apply]
      have hpj' := hpj j hj
      have hf : ((f jr : Fin m₂) : ℕ) = j - p := rfl
      by_cases hij : (j : ℕ) = i + p
      · rw [ite_eq_left hij, ite_eq_left (Fin.ext (by rw [hf]; omega)), mul_one]
      · rw [ite_eq_right hij, ite_eq_right (fun h => hij (by
          have := congrArg Fin.val h; rw [hf] at this; omega)), mul_zero]

end Thin

/-! ### The full CS decomposition -/

section Full

/-- **The upper right block of a CS decomposition** ([golub2013matrix] Theorem 2.5.3): `s_i` at
`(i, i − p)` for `p ≤ i < n₁`, and an identity block from `(n₁, n₁ − p + q)` on, `0` elsewhere.
This is the book's `[0 0; S 0; 0 I]` with row blocks `p, n₁ − p, m₁ − n₁` and column blocks
`n₁ − p, q, m₁ − n₁`. -/
def csdUpperRight {α : Type*} [Zero α] [One α] {m n : ℕ} (n₁ p q : ℕ) (s : ℕ → α) :
    Matrix (Fin m) (Fin n) α :=
  of fun i j => if p ≤ (i : ℕ) ∧ (i : ℕ) < n₁ ∧ (j : ℕ) = i - p then s i
    else if n₁ ≤ (i : ℕ) ∧ (j : ℕ) = i - p + q then 1 else 0

variable {m₁ m₂ n₁ n₂ : ℕ}

/-- **A CS decomposition of a unitary matrix, as a specification** ([golub2013matrix]
Theorem 2.5.3). For `Q = fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂` (given by its four blocks), unitary
`U₁, U₂, V₁, V₂` and monotone angles `θ i ∈ [0, π/2]`, the first `p = n₁ − min n₁ m₂` of them `0`,
with `q = m₂ − min n₁ m₂`, `c_i = cos θ_i`, `s_i = sin θ_i`:
* `U₁ᴴ Q₁₁ V₁ = diag(c)` and `U₂ᴴ Q₂₁ V₁ = S` shifted by `p` (a thin CS decomposition of the first
  block column, `Matrix.IsCSD.toIsThinCSD`),
* `U₁ᴴ Q₁₂ V₂ = Matrix.csdUpperRight n₁ p q s` and
  `U₂ᴴ Q₂₂ V₂ = diag(−c_p, …, −c_{n₁−1}, 1, …, 1)`.
This is the book's 5-by-5 block form with row blocks `p, n₁ − p, m₁ − n₁ | n₁ − p, q` and column
blocks `p, n₁ − p | n₁ − p, q, m₁ − n₁`; the printed display has its row labels mangled, and this
reading is the one whose block sizes add up. -/
structure IsCSD (Q₁₁ : Matrix (Fin m₁) (Fin n₁) 𝕜) (Q₁₂ : Matrix (Fin m₁) (Fin n₂) 𝕜)
    (Q₂₁ : Matrix (Fin m₂) (Fin n₁) 𝕜) (Q₂₂ : Matrix (Fin m₂) (Fin n₂) 𝕜)
    (U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜) (U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜)
    (V₁ : Matrix (Fin n₁) (Fin n₁) 𝕜) (V₂ : Matrix (Fin n₂) (Fin n₂) 𝕜) (θ : ℕ → ℝ) : Prop
    extends IsThinCSD Q₁₁ Q₂₁ U₁ U₂ V₁ θ where
  /-- The second right factor is unitary. -/
  mem_unitaryGroup_right₂ : V₂ ∈ unitaryGroup (Fin n₂) 𝕜
  /-- The `(1, 2)` block. -/
  star_mul_mul₁₂ : star U₁ * Q₁₂ * V₂ = csdUpperRight n₁ (n₁ - min n₁ m₂) (m₂ - min n₁ m₂)
    fun i => ((Real.sin (θ i) : ℝ) : 𝕜)
  /-- The `(2, 2)` block. -/
  star_mul_mul₂₂ : star U₂ * Q₂₂ * V₂ = rectDiagonal fun i =>
    if i < n₁ - (n₁ - min n₁ m₂) then -((Real.cos (θ (i + (n₁ - min n₁ m₂))) : ℝ) : 𝕜) else 1

section Deprecated

variable {Q₁₁ : Matrix (Fin m₁) (Fin n₁) 𝕜} {Q₁₂ : Matrix (Fin m₁) (Fin n₂) 𝕜}
  {Q₂₁ : Matrix (Fin m₂) (Fin n₁) 𝕜} {Q₂₂ : Matrix (Fin m₂) (Fin n₂) 𝕜}
  {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜}
  {V₁ : Matrix (Fin n₁) (Fin n₁) 𝕜} {V₂ : Matrix (Fin n₂) (Fin n₂) 𝕜} {θ : ℕ → ℝ}

@[deprecated (since := "2026-09-30")] alias IsCSD.isThinCSD := IsCSD.toIsThinCSD

/-- The first right factor is unitary (the former field name). -/
@[deprecated IsThinCSD.mem_unitaryGroup_right +typeChanged (since := "2026-09-30")]
theorem IsCSD.mem_unitaryGroup_right₁ (h : IsCSD Q₁₁ Q₁₂ Q₂₁ Q₂₂ U₁ U₂ V₁ V₂ θ) :
    V₁ ∈ unitaryGroup (Fin n₁) 𝕜 :=
  h.mem_unitaryGroup_right

/-- The `(1, 1)` block (the former field name). -/
@[deprecated IsThinCSD.star_mul_mul₁ +typeChanged (since := "2026-09-30")]
theorem IsCSD.star_mul_mul₁₁ (h : IsCSD Q₁₁ Q₁₂ Q₂₁ Q₂₂ U₁ U₂ V₁ V₂ θ) :
    star U₁ * Q₁₁ * V₁ = rectDiagonal fun i => ((Real.cos (θ i) : ℝ) : 𝕜) :=
  h.star_mul_mul₁

/-- The `(2, 1)` block (the former field name). -/
@[deprecated IsThinCSD.star_mul_mul₂ +typeChanged (since := "2026-09-30")]
theorem IsCSD.star_mul_mul₂₁ (h : IsCSD Q₁₁ Q₁₂ Q₂₁ Q₂₂ U₁ U₂ V₁ V₂ θ) :
    star U₂ * Q₂₁ * V₁ =
      shiftedRectDiagonal (n₁ - min n₁ m₂) fun i => ((Real.sin (θ i) : ℝ) : 𝕜) :=
  h.star_mul_mul₂

end Deprecated

/-- `(Uᴴ X V)(U'ᴴ Y V)ᴴ = Uᴴ (X Yᴴ) U'` for unitary `V`. -/
private theorem star_mul_mul_mul_conjTranspose {a b c : ℕ} (U : Matrix (Fin a) (Fin a) 𝕜)
    (U' : Matrix (Fin b) (Fin b) 𝕜) {V : Matrix (Fin c) (Fin c) 𝕜}
    (hV : V ∈ unitaryGroup (Fin c) 𝕜) (X : Matrix (Fin a) (Fin c) 𝕜)
    (Y : Matrix (Fin b) (Fin c) 𝕜) :
    (star U * X * V) * (star U' * Y * V)ᴴ = star U * (X * Yᴴ) * U' := by
  have hVV := mul_conjTranspose_self_of_mem_unitaryGroup hV
  rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose U', conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V, hVV, Matrix.one_mul]

variable {Q₁₁ : Matrix (Fin m₁) (Fin n₁) 𝕜} {Q₁₂ : Matrix (Fin m₁) (Fin n₂) 𝕜}
  {Q₂₁ : Matrix (Fin m₂) (Fin n₁) 𝕜} {Q₂₂ : Matrix (Fin m₂) (Fin n₂) 𝕜}

/-- **The CS decomposition** ([golub2013matrix] Theorem 2.5.3, which defers the proof to Paige
and Saunders (1981)): a unitary `Q = fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂` with `n₁ ≤ m₁` has a
CS decomposition (the book's second hypothesis `m₂ ≤ m₁` is not needed). Unitarity is given as
`Qᴴ Q = 1` for the square shape `m₁ + m₂ = n₁ + n₂`, which gives `Q Qᴴ = 1`. Take a thin CS
decomposition `(U₁, U₂, V₁, θ)` of the first block column
(`Matrix.exists_isThinCSD`). With `Yᵢ = Uᵢᴴ Qᵢ₂`, `[C; S]` the transformed first block column
and `[T₁; T₂]` the target second block column, set `V₂ = Y₁ᴴ T₁ + Y₂ᴴ T₂`. The rows of the unitary
`diag(U₁, U₂)ᴴ Q diag(V₁, I)` are orthonormal, so `Y Yᴴ = I − [C; S][C; S]ᴴ`; and `[T₁; T₂]` has
orthonormal columns orthogonal to those of `[C; S]` (an entrywise computation with
`c_i² + s_i² = 1`). Hence `Y V₂ = T` and `V₂ᴴ V₂ = Tᴴ T = I`. -/
theorem exists_isCSD (hmn : m₁ + m₂ = n₁ + n₂)
    (hQ : (fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂)ᴴ * fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂ = 1) (hn₁ : n₁ ≤ m₁) :
    ∃ U₁ U₂ V₁ V₂ θ, IsCSD Q₁₁ Q₁₂ Q₂₁ Q₂₂ U₁ U₂ V₁ V₂ θ := by
  classical
  have hQ' : fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂ * (fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂)ᴴ = 1 :=
    (mul_eq_one_comm_of_card_eq _ _ _
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)).1 hQ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one] at hQ hQ'
  obtain ⟨h11, -, -, -⟩ := fromBlocks_inj.1 hQ
  obtain ⟨k11, k12, k21, k22⟩ := fromBlocks_inj.1 hQ'
  obtain ⟨U₁, U₂, V₁, θ, hc⟩ := exists_isThinCSD Q₁₁ Q₂₁ h11 hn₁
  set p := n₁ - min n₁ m₂ with hp
  set q := m₂ - min n₁ m₂ with hq
  set c : ℕ → 𝕜 := fun i => ((Real.cos (θ i) : ℝ) : 𝕜) with hcdef
  set s : ℕ → 𝕜 := fun i => ((Real.sin (θ i) : ℝ) : 𝕜) with hsdef
  set σ : ℕ → 𝕜 := fun i => if i < n₁ - p then -c (i + p) else 1 with hσdef
  set T₁ : Matrix (Fin m₁) (Fin n₂) 𝕜 := csdUpperRight n₁ p q s with hT₁
  set T₂ : Matrix (Fin m₂) (Fin n₂) 𝕜 := rectDiagonal σ with hT₂
  obtain ⟨Y₁, hY₁⟩ : ∃ Y, Y = star U₁ * Q₁₂ * (1 : Matrix (Fin n₂) (Fin n₂) 𝕜) := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y, Y = star U₂ * Q₂₂ * (1 : Matrix (Fin n₂) (Fin n₂) 𝕜) := ⟨_, rfl⟩
  have hC := hc.star_mul_mul₁
  have hS := hc.star_mul_mul₂
  have hV₁ := hc.mem_unitaryGroup_right
  have hU₁ : star U₁ * U₁ = 1 := mem_unitaryGroup_iff'.1 hc.mem_unitaryGroup_left₁
  have hU₂ : star U₂ * U₂ = 1 := mem_unitaryGroup_iff'.1 hc.mem_unitaryGroup_left₂
  have hs0 : ∀ i < p, s i = 0 := fun i hi => by simp [hsdef, hc.eq_zero_of_lt i hi]
  have hc1 : ∀ i < p, c i = 1 := fun i hi => by simp [hcdef, hc.eq_zero_of_lt i hi]
  have hcs : ∀ i, star (c i) * c i + star (s i) * s i = 1 := fun i => by
    simp only [hcdef, hsdef, RCLike.star_def, RCLike.conj_ofReal]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, ← RCLike.ofReal_add, ← sq, ← sq,
      Real.cos_sq_add_sin_sq, RCLike.ofReal_one]
  -- the rows of the transformed unitary
  have r1 : (star U₁ * Q₁₁ * V₁) * (star U₁ * Q₁₁ * V₁)ᴴ + Y₁ * Y₁ᴴ = 1 := by
    rw [star_mul_mul_mul_conjTranspose _ _ hV₁, hY₁,
      star_mul_mul_mul_conjTranspose _ _ (one_mem _), ← Matrix.add_mul, ← Matrix.mul_add, k11,
      Matrix.mul_one, hU₁]
  have r2 : (star U₂ * Q₂₁ * V₁) * (star U₁ * Q₁₁ * V₁)ᴴ + Y₂ * Y₁ᴴ = 0 := by
    rw [star_mul_mul_mul_conjTranspose _ _ hV₁, hY₂, hY₁,
      star_mul_mul_mul_conjTranspose _ _ (one_mem _), ← Matrix.add_mul, ← Matrix.mul_add, k21,
      Matrix.mul_zero, Matrix.zero_mul]
  have r3 : (star U₂ * Q₂₁ * V₁) * (star U₂ * Q₂₁ * V₁)ᴴ + Y₂ * Y₂ᴴ = 1 := by
    rw [star_mul_mul_mul_conjTranspose _ _ hV₁, hY₂,
      star_mul_mul_mul_conjTranspose _ _ (one_mem _), ← Matrix.add_mul, ← Matrix.mul_add, k22,
      Matrix.mul_one, hU₂]
  have r4 : (star U₁ * Q₁₁ * V₁) * (star U₂ * Q₂₁ * V₁)ᴴ + Y₁ * Y₂ᴴ = 0 := by
    rw [star_mul_mul_mul_conjTranspose _ _ hV₁, hY₁, hY₂,
      star_mul_mul_mul_conjTranspose _ _ (one_mem _), ← Matrix.add_mul, ← Matrix.mul_add, k12,
      Matrix.mul_zero, Matrix.zero_mul]
  rw [hC] at r1 r2 r4
  rw [hS] at r2 r3 r4
  set C : Matrix (Fin m₁) (Fin n₁) 𝕜 := rectDiagonal c with hCdef
  set S : Matrix (Fin m₂) (Fin n₁) 𝕜 := shiftedRectDiagonal p s with hSdef
  -- the target columns are orthogonal to `[C; S]` and orthonormal
  have t1 : Cᴴ * T₁ + Sᴴ * T₂ = 0 := by
    ext a b
    rw [add_apply, rectDiagonal_conjTranspose, rectDiagonal_mul_apply _ _ _ _
      (lt_of_lt_of_le a.isLt hn₁), conjTranspose_shiftedRectDiagonal_mul_apply, zero_apply]
    simp only [hT₁, hT₂, csdUpperRight, of_apply, rectDiagonal_apply, Function.comp_apply,
      hσdef]
    by_cases hpa : p ≤ (a : ℕ)
    · have hk : (a : ℕ) - p < m₂ := by
        have := a.isLt; have := min_le_right n₁ m₂; omega
      rw [dite_eq_left ⟨hpa, hk⟩]
      by_cases hb : (b : ℕ) = a - p
      · rw [ite_eq_left ⟨hpa, a.isLt, hb⟩, ite_eq_left hb.symm,
          ite_eq_left (by have := a.isLt; omega),
          Nat.sub_add_cancel hpa]
        simp only [hcdef, hsdef, RCLike.star_def, RCLike.conj_ofReal]
        ring
      · rw [ite_eq_right (fun h => hb h.2.2), ite_eq_right (fun h => by have := a.isLt; omega),
          ite_eq_right (fun h => hb h.symm)]
        simp
    · rw [dite_eq_right (fun h => hpa h.1), ite_eq_right (fun h => hpa h.1),
        ite_eq_right (fun h => by have := a.isLt; omega)]
      simp
  have t2 : T₁ᴴ * T₁ + T₂ᴴ * T₂ = 1 := by
    have hmin1 := min_le_left n₁ m₂
    have hmin2 := min_le_right n₁ m₂
    set ρ : ℕ → ℕ := fun j => if j < n₁ - p then j + p else j - q + p with hρdef
    set τ : ℕ → 𝕜 := fun j => if j < n₁ - p then s (j + p) else if n₁ - p + q ≤ j then 1 else 0
      with hτdef
    have hcol : ∀ (i : Fin m₁) (j : Fin n₂), T₁ i j = if (i : ℕ) = ρ j then τ j else 0 := by
      intro i j
      have := i.isLt
      have := j.isLt
      rw [hT₁, hρdef, hτdef]
      simp only [csdUpperRight, of_apply]
      split_ifs <;> first | rfl | (exfalso; omega) | congr 1
    have hsum : ∀ b b' : Fin n₂, (T₁ᴴ * T₁) b b'
        = if ρ b < m₁ ∧ ρ b = ρ b' then star (τ b) * τ b' else 0 := by
      intro b b'
      rw [mul_apply]
      simp only [conjTranspose_apply, hcol]
      split_ifs with h
      · rw [Finset.sum_eq_single ⟨ρ b, h.1⟩]
        · simp [h.2]
        · intro i _ hi
          rw [ite_eq_right (fun e => hi (Fin.ext e)), star_zero, zero_mul]
        · exact fun h' => absurd (Finset.mem_univ _) h'
      · refine Finset.sum_eq_zero fun i _ => ?_
        by_cases h1 : (i : ℕ) = ρ b
        · by_cases h2 : (i : ℕ) = ρ b'
          · exact absurd ⟨h1 ▸ i.isLt, h1.symm.trans h2⟩ h
          · rw [ite_eq_right h2, mul_zero]
        · rw [ite_eq_right h1, star_zero, zero_mul]
    rw [hT₂, conjTranspose_rectDiagonal_mul_self]
    ext b b'
    rw [add_apply, hsum, diagonal_apply, one_apply]
    have := b.isLt
    have := b'.isLt
    by_cases hbb : b = b'
    · subst hbb
      rw [ite_eq_left rfl, ite_eq_left rfl]
      by_cases hb1 : (b : ℕ) < n₁ - p
      · have hρ : ρ b = b + p := by rw [hρdef]; exact ite_eq_left hb1
        have hτ : τ b = s (b + p) := by rw [hτdef]; exact ite_eq_left hb1
        have hσ : σ b = -c (b + p) := by rw [hσdef]; exact ite_eq_left hb1
        rw [ite_eq_left ⟨by rw [hρ]; omega, rfl⟩, ite_eq_left (by omega), hτ, hσ, star_neg,
          neg_mul_neg,
          add_comm]
        exact hcs _
      · by_cases hb2 : (b : ℕ) < n₁ - p + q
        · have hτ : τ b = 0 := by
            rw [hτdef]; simp only [ite_eq_right hb1, ite_eq_right (not_le.2 hb2)]
          have hσ : σ b = 1 := by rw [hσdef]; exact ite_eq_right hb1
          rw [hτ, star_zero, zero_mul, ite_self, zero_add, ite_eq_left (by omega), hσ, star_one,
            one_mul]
        · have hρ : ρ b = b - q + p := by rw [hρdef]; exact ite_eq_right hb1
          have hτ : τ b = 1 := by
            rw [hτdef]; simp only [ite_eq_right hb1, ite_eq_left (not_lt.1 hb2)]
          rw [ite_eq_left ⟨by rw [hρ]; omega, rfl⟩, ite_eq_right (by omega), hτ, star_one, one_mul,
            add_zero]
    · rw [ite_eq_right hbb, ite_eq_right hbb, add_zero]
      split_ifs with h
      · obtain ⟨-, hρ⟩ := h
        have hb' : (b : ℕ) ≠ b' := fun e => hbb (Fin.ext e)
        rw [hρdef] at hρ
        rw [hτdef]
        simp only at hρ ⊢
        split_ifs at hρ ⊢ <;> first | (exfalso; omega) | simp
      · rfl
  -- the second right factor
  set V₂ := Y₁ᴴ * T₁ + Y₂ᴴ * T₂ with hV₂
  have hYV₁ : Y₁ * V₂ = T₁ := by
    have e1 : Y₁ * Y₁ᴴ = 1 - C * Cᴴ := eq_sub_of_add_eq' r1
    have e2 : Y₁ * Y₂ᴴ = -(C * Sᴴ) := eq_neg_of_add_eq_zero_right r4
    calc Y₁ * V₂ = (Y₁ * Y₁ᴴ) * T₁ + (Y₁ * Y₂ᴴ) * T₂ := by
          rw [hV₂, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = T₁ - C * (Cᴴ * T₁ + Sᴴ * T₂) := by
          rw [e1, e2, Matrix.sub_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_add,
            Matrix.mul_assoc, Matrix.mul_assoc]
          abel
      _ = T₁ := by rw [t1, Matrix.mul_zero, sub_zero]
  have hYV₂ : Y₂ * V₂ = T₂ := by
    have e1 : Y₂ * Y₂ᴴ = 1 - S * Sᴴ := eq_sub_of_add_eq' r3
    have e2 : Y₂ * Y₁ᴴ = -(S * Cᴴ) := eq_neg_of_add_eq_zero_right r2
    calc Y₂ * V₂ = (Y₂ * Y₁ᴴ) * T₁ + (Y₂ * Y₂ᴴ) * T₂ := by
          rw [hV₂, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = T₂ - S * (Cᴴ * T₁ + Sᴴ * T₂) := by
          rw [e1, e2, Matrix.sub_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_add,
            Matrix.mul_assoc, Matrix.mul_assoc]
          abel
      _ = T₂ := by rw [t1, Matrix.mul_zero, sub_zero]
  have hVV : star V₂ * V₂ = 1 := by
    have hVh : V₂ᴴ = T₁ᴴ * Y₁ + T₂ᴴ * Y₂ := by
      rw [hV₂, conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
        conjTranspose_conjTranspose, conjTranspose_conjTranspose]
    rw [star_eq_conjTranspose, hVh, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hYV₁,
      hYV₂, t2]
  refine ⟨U₁, U₂, V₁, V₂, θ, hc, mem_unitaryGroup_iff'.2 hVV, ?_, ?_⟩
  · have := hYV₁
    rw [hY₁, Matrix.mul_one] at this
    exact this
  · have := hYV₂
    rw [hY₂, Matrix.mul_one] at this
    exact this

end Full

/-! ### The off-diagonal blocks of a unitary matrix -/

section OffDiagonal

variable {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

open scoped Matrix.Norms.L2Operator in
/-- **The off-diagonal blocks of a unitary matrix with a square leading block have equal
`2`-norms** ([golub2013matrix] proof of Theorem 2.5.1): for `Q ∈ unitaryGroup (k ⊕ l) 𝕜`,
`‖Q₂₁‖₂ = ‖Q₁₂‖₂`. The first block column of `Q` and the first block column of `Qᴴ` are stacked
isometries with the square leading blocks `Q₁₁` and `Q₁₁ᴴ`, so by the stacked-isometry identity
`Matrix.l2_opNorm_sq_eq_one_sub_sq_sortedSingularValues` both squared norms are
`1 − σ_min(Q₁₁)²`, a square matrix and its adjoint having the same singular values. -/
theorem l2_opNorm_toBlocks₂₁_eq_toBlocks₁₂ {Q : Matrix (k ⊕ l) (k ⊕ l) 𝕜}
    (hQ : Q ∈ unitaryGroup (k ⊕ l) 𝕜) : ‖Q.toBlocks₂₁‖ = ‖Q.toBlocks₁₂‖ := by
  cases isEmpty_or_nonempty k with
  | inl hk =>
    rw [Subsingleton.elim Q.toBlocks₂₁ 0, Subsingleton.elim Q.toBlocks₁₂ 0, norm_zero,
      norm_zero]
  | inr hk =>
    have h₁ := mem_unitaryGroup_iff'.1 hQ
    have h₂ := mem_unitaryGroup_iff.1 hQ
    rw [star_eq_conjTranspose, ← fromBlocks_toBlocks Q, fromBlocks_conjTranspose,
      fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h₁ h₂
    have hcol := l2_opNorm_sq_eq_one_sub_sq_sortedSingularValues h₁.1
    have hrow := l2_opNorm_sq_eq_one_sub_sq_sortedSingularValues
      (Q₁ := Q.toBlocks₁₁ᴴ) (Q₂ := Q.toBlocks₁₂ᴴ) (by
        rw [conjTranspose_conjTranspose, conjTranspose_conjTranspose]
        exact h₂.1)
    rw [sortedSingularValues_conjTranspose, l2_opNorm_conjTranspose, ← hcol] at hrow
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hrow.symm

end OffDiagonal

end Matrix
