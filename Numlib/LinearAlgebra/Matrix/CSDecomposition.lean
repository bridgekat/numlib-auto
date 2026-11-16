/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside a future SVD.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.DotProduct
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv

/-!
# The CS decomposition

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The blocks of a matrix with orthonormal columns,
and the blocks of a unitary matrix partitioned into $2 \times 2$ blocks, have singular value
decompositions with common unitary factors. This is the **cosine–sine (CS) decomposition** of
[golub2013matrix], §2.5.4, Theorems 2.5.2 and 2.5.3, after C. C. Paige and M. A. Saunders, *Towards
a generalized singular value decomposition*, SIAM J. Numer. Anal. 18 (1981).

For the thin form, let $Q_1 \in \mathbb{K}^{m_1 \times n_1}$ and
$Q_2 \in \mathbb{K}^{m_2 \times n_1}$ with $Q_1^H Q_1 + Q_2^H Q_2 = I$ and $n_1 \le m_1$. Then there
are unitary $U_1$, $U_2$, $V$ and angles $0 \le \theta_0 \le \theta_1 \le \dots \le \pi/2$ with
$U_1^H Q_1 V = \operatorname{diag}(\cos \theta)$ and
$U_2^H Q_2 V = \operatorname{diag}(\sin \theta)$, where the sine block is shifted by
$p = n_1 - \min(n_1, m_2)$ columns when $Q_2$ has fewer rows than columns. The full form decomposes
all four blocks of a unitary matrix in this way. The module also proves that the two off-diagonal
blocks of a unitary matrix have equal $2$-norms.

## Main definitions

* `Matrix.IsThinCSD`: a thin CS decomposition of the stacked matrix
  $\begin{bmatrix} Q_1 \\ Q_2 \end{bmatrix}$.
* `Matrix.csdUpperRight`: the shape of the upper right block of a CS decomposition.
* `Matrix.IsCSD`: a CS decomposition of the unitary matrix $\begin{bmatrix} Q_{11} & Q_{12} \\
  Q_{21} & Q_{22} \end{bmatrix}$, in the $5 \times 5$ block form of Theorem 2.5.3 of
  [golub2013matrix]. It extends the thin CS decomposition of the first block column.

## Main results

* `Matrix.exists_isThinCSD`: Theorem 2.5.2 of [golub2013matrix], without its hypothesis
  $m_2 \ge n_1$.
* `Matrix.exists_isCSD`: Theorem 2.5.3 of [golub2013matrix], without its hypothesis $m_2 \le m_1$.
* `Matrix.l2_opNorm_toBlocks₂₁_eq_toBlocks₁₂`: the off-diagonal blocks $Q_{21}$ and $Q_{12}$ of a
  unitary matrix have equal $2$-norms.

## Implementation notes

* The shapes are indexed by `Fin`, so that the diagonal factors are `Matrix.rectDiagonal` and
  `Matrix.shiftedRectDiagonal` of a function on the natural numbers, as in `Matrix.exists_svd`.
  One monotone function $\theta \colon \mathbb{N} \to \mathbb{R}$ carries the angles; a monotone
  extension past $n_1$ always exists.
* "The columns of $\begin{bmatrix} Q_1 \\ Q_2 \end{bmatrix}$ are orthonormal" is
  $Q_1^H Q_1 + Q_2^H Q_2 = I$.
* When $m_2 < n_1$, at least $p = n_1 - m_2$ of the cosines equal $1$, because the nonzero columns
  of $Q_2 V$ are orthogonal vectors of $\mathbb{K}^{m_2}$.
* The field names follow the two-sided factorizations of `Matrix.IsUnitaryEquiv`. The words *left*
  and *right* name the side of the factored block, the subscripts name the block row or column
  ($U_1$, $U_2$ on the left, $V_1$, $V_2$ on the right), and `star_mul_mul₁` to `star_mul_mul₂₂`
  name the blocks. `Matrix.IsThinCSD.isUnitaryEquiv₁` and `Matrix.IsThinCSD.isUnitaryEquiv₂` package
  the two blocks of a thin CS decomposition as unitary equivalences.
-/

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Thin

variable {m₁ m₂ n₁ : ℕ}

/-- **A thin CS decomposition** ([golub2013matrix], Theorem 2.5.2, without its hypothesis
$m_2 \ge n_1$). Let $Q_1 \in \mathbb{K}^{m_1 \times n_1}$ and
$Q_2 \in \mathbb{K}^{m_2 \times n_1}$, and let $p = n_1 - \min(n_1, m_2)$. A thin CS
decomposition of $\begin{bmatrix} Q_1 \\ Q_2 \end{bmatrix}$ consists of unitary matrices $U_1$
of order $m_1$, $U_2$ of order $m_2$ and $V$ of order $n_1$, and a monotone sequence of angles
$\theta_i \in [0, \pi/2]$ with $\theta_i = 0$ for $i < p$, such that
$$U_1^H Q_1 V = \operatorname{diag}(\cos \theta_i), \qquad U_2^H Q_2 V = S_p,$$
where $\operatorname{diag}(\cos \theta_i)$ is the rectangular diagonal matrix with
$\cos \theta_i$ at $(i, i)$, and $S_p$ has $\sin \theta_j$ at $(j - p, j)$ for $j \ge p$ and $0$
elsewhere.

For $m_2 \ge n_1$, the case of the source, $p = 0$ and the sine block is the rectangular
diagonal matrix (`Matrix.shiftedRectDiagonal_zero`). The two blocks are `Matrix.rectDiagonal`
and `Matrix.shiftedRectDiagonal p` of the sequences $\cos \theta$ and $\sin \theta$. -/
structure IsThinCSD (Q₁ : Matrix (Fin m₁) (Fin n₁) 𝕜) (Q₂ : Matrix (Fin m₂) (Fin n₁) 𝕜)
    (U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜) (U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜)
    (V : Matrix (Fin n₁) (Fin n₁) 𝕜) (θ : ℕ → ℝ) : Prop where
  /-- The first left factor $U_1$ is unitary. -/
  mem_unitaryGroup_left₁ : U₁ ∈ unitaryGroup (Fin m₁) 𝕜
  /-- The second left factor $U_2$ is unitary. -/
  mem_unitaryGroup_left₂ : U₂ ∈ unitaryGroup (Fin m₂) 𝕜
  /-- The right factor $V$ is unitary. -/
  mem_unitaryGroup_right : V ∈ unitaryGroup (Fin n₁) 𝕜
  /-- The angles are sorted: $\theta$ is monotone. -/
  monotone : Monotone θ
  /-- Every angle lies in $[0, \pi/2]$. -/
  mem_Icc : ∀ i, θ i ∈ Set.Icc 0 (Real.pi / 2)
  /-- The first $p = n_1 - \min(n_1, m_2)$ angles are $0$. -/
  eq_zero_of_lt : ∀ i < n₁ - min n₁ m₂, θ i = 0
  /-- The cosine block: $U_1^H Q_1 V = \operatorname{diag}(\cos \theta_i)$. -/
  star_mul_mul₁ : star U₁ * Q₁ * V = rectDiagonal fun i => ((Real.cos (θ i) : ℝ) : 𝕜)
  /-- The sine block: $U_2^H Q_2 V$ has $\sin \theta_j$ at $(j - p, j)$ for $j \ge p$ and $0$
  elsewhere. -/
  star_mul_mul₂ :
    star U₂ * Q₂ * V = shiftedRectDiagonal (n₁ - min n₁ m₂) fun i => ((Real.sin (θ i) : ℝ) : 𝕜)

variable {Q₁ : Matrix (Fin m₁) (Fin n₁) 𝕜} {Q₂ : Matrix (Fin m₂) (Fin n₁) 𝕜}

/-- The cosine block of a thin CS decomposition is a two-sided unitary equivalence: $U_1^H Q_1 V =
\operatorname{diag}(\cos \theta_i)$ with $U_1$ and $V$ unitary. -/
theorem IsThinCSD.isUnitaryEquiv₁ {U₁ U₂ V θ} (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) :
    IsUnitaryEquiv Q₁ U₁ (rectDiagonal fun i => ((Real.cos (θ i) : ℝ) : 𝕜)) V :=
  ⟨h.mem_unitaryGroup_left₁, h.mem_unitaryGroup_right, h.star_mul_mul₁⟩

/-- The sine block of a thin CS decomposition is a two-sided unitary equivalence:
$U_2^H Q_2 V = S_p$ with $U_2$ and $V$ unitary. -/
theorem IsThinCSD.isUnitaryEquiv₂ {U₁ U₂ V θ} (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) :
    IsUnitaryEquiv Q₂ U₂
      (shiftedRectDiagonal (n₁ - min n₁ m₂) fun i => ((Real.sin (θ i) : ℝ) : 𝕜)) V :=
  ⟨h.mem_unitaryGroup_left₂, h.mem_unitaryGroup_right, h.star_mul_mul₂⟩

/-- The angles of a thin CS decomposition have nonnegative cosines: $\cos \theta_i \ge 0$ for every
$i$. -/
theorem IsThinCSD.cos_nonneg {U₁ U₂ V θ} (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) (i : ℕ) :
    0 ≤ Real.cos (θ i) :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [(h.mem_Icc i).1, Real.pi_pos], (h.mem_Icc i).2⟩

/-- The angles of a thin CS decomposition have nonnegative sines: $\sin \theta_i \ge 0$ for every
$i$. -/
theorem IsThinCSD.sin_nonneg {U₁ U₂ V θ} (h : IsThinCSD Q₁ Q₂ U₁ U₂ V θ) (i : ℕ) :
    0 ≤ Real.sin (θ i) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (h.mem_Icc i).1 (by linarith [(h.mem_Icc i).2, Real.pi_pos])

/-- If $Q_1^H Q_1 + Q_2^H Q_2 = I$, $n_1 \le m_1$, $U_1$ and $V$ are unitary and
$U_1^H Q_1 V = \operatorname{diag}(c)$, then $(Q_2 V)^H (Q_2 V) = \operatorname{diag}(1 -
c_j^2)$. -/
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

/-- **The thin CS decomposition** ([golub2013matrix], Theorem 2.5.2). Let
$Q_1 \in \mathbb{K}^{m_1 \times n_1}$ and $Q_2 \in \mathbb{K}^{m_2 \times n_1}$ with
$$Q_1^H Q_1 + Q_2^H Q_2 = I \qquad \text{and} \qquad n_1 \le m_1.$$
Then $\begin{bmatrix} Q_1 \\ Q_2 \end{bmatrix}$ has a thin CS decomposition in the sense of
`Matrix.IsThinCSD`.

The source also assumes $m_2 \ge n_1$; the statement here does not need it. The proof follows
the source. A singular value decomposition $U_1^H Q_1 V = \operatorname{diag}(c)$ has
$1 \ge c_0 \ge \dots \ge 0$. The columns of $Q_2 V$ are pairwise orthogonal with squared norms
$1 - c_j^2$, so at most $m_2$ of them are nonzero, and the first $p$ cosines are $1$. The
normalized nonzero columns, placed at the positions $j - p$, extend to a unitary $U_2$
(`Matrix.exists_mem_unitaryGroup_submatrix_eq`), and $\theta_j = \arccos c_j$. -/
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
    apply_eq_zero_of_conjTranspose_mul_self_apply_self_eq_zero
      (by rw [hWW, diagonal_apply_eq, hj]; simp)
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
    rw [Matrix.mul_apply, shiftedRectDiagonal_apply, hsin j j.isLt]
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
        rw [Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [star_apply]; ring
      rw [hsum, mem_unitaryGroup_iff'.1 hU₂, Matrix.one_apply]
      have hpj' := hpj j hj
      have hf : ((f jr : Fin m₂) : ℕ) = j - p := rfl
      by_cases hij : (j : ℕ) = i + p
      · rw [ite_eq_left hij, ite_eq_left (Fin.ext (by rw [hf]; omega)), mul_one]
      · rw [ite_eq_right hij, ite_eq_right (fun h => hij (by omega)), mul_zero]

end Thin

/-! ### The full CS decomposition -/

section Full

/-- **The upper right block of a CS decomposition** ([golub2013matrix], Theorem 2.5.3). For natural
numbers $n_1$, $p$, $q$ and a sequence $s$, this is the $m \times n$ matrix with $s_i$ at
$(i, i - p)$ for $p \le i < n_1$, with $1$ at $(i, i - p + q)$ for $i \ge n_1$, and with $0$
elsewhere.

This is the block $\begin{bmatrix} 0 & 0 & 0 \\ S & 0 & 0 \\ 0 & 0 & I \end{bmatrix}$ of the
source, with row blocks of sizes $p$, $n_1 - p$, $m_1 - n_1$ and column blocks of sizes
$n_1 - p$, $q$, $m_1 - n_1$. -/
def csdUpperRight {α : Type*} [Zero α] [One α] {m n : ℕ} (n₁ p q : ℕ) (s : ℕ → α) :
    Matrix (Fin m) (Fin n) α :=
  of fun i j => if p ≤ (i : ℕ) ∧ (i : ℕ) < n₁ ∧ (j : ℕ) = i - p then s i
    else if n₁ ≤ (i : ℕ) ∧ (j : ℕ) = i - p + q then 1 else 0

variable {m₁ m₂ n₁ n₂ : ℕ}

/-- **A CS decomposition of a unitary matrix** ([golub2013matrix], Theorem 2.5.3). Let $Q =
\begin{bmatrix} Q_{11} & Q_{12} \\ Q_{21} & Q_{22} \end{bmatrix}$ with
$Q_{11} \in \mathbb{K}^{m_1 \times n_1}$ and $Q_{22} \in \mathbb{K}^{m_2 \times n_2}$, let
$p = n_1 - \min(n_1, m_2)$ and $q = m_2 - \min(n_1, m_2)$, and write $c_i = \cos \theta_i$ and
$s_i = \sin \theta_i$. A CS decomposition of $Q$ consists of unitary matrices $U_1$, $U_2$,
$V_1$, $V_2$ of orders $m_1$, $m_2$, $n_1$, $n_2$, and a monotone sequence of angles
$\theta_i \in [0, \pi/2]$ with $\theta_i = 0$ for $i < p$, such that:

* $U_1^H Q_{11} V_1 = \operatorname{diag}(c)$ and $U_2^H Q_{21} V_1 = S_p$, the sine block
  shifted by $p$; this is a thin CS decomposition of the first block column
  (`Matrix.IsCSD.toIsThinCSD`);
* $U_1^H Q_{12} V_2$ is `Matrix.csdUpperRight n₁ p q s`;
* $U_2^H Q_{22} V_2 = \operatorname{diag}(-c_p, \dots, -c_{n_1 - 1}, 1, \dots, 1)$, a
  rectangular diagonal matrix.

This is the $5 \times 5$ block form of the source, with row blocks of sizes $p$, $n_1 - p$,
$m_1 - n_1$ and $n_1 - p$, $q$, and column blocks of sizes $p$, $n_1 - p$ and $n_1 - p$, $q$,
$m_1 - n_1$. The display printed in the source has wrong row labels; this reading is the one
whose block sizes add up. -/
structure IsCSD (Q₁₁ : Matrix (Fin m₁) (Fin n₁) 𝕜) (Q₁₂ : Matrix (Fin m₁) (Fin n₂) 𝕜)
    (Q₂₁ : Matrix (Fin m₂) (Fin n₁) 𝕜) (Q₂₂ : Matrix (Fin m₂) (Fin n₂) 𝕜)
    (U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜) (U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜)
    (V₁ : Matrix (Fin n₁) (Fin n₁) 𝕜) (V₂ : Matrix (Fin n₂) (Fin n₂) 𝕜) (θ : ℕ → ℝ) : Prop
    extends IsThinCSD Q₁₁ Q₂₁ U₁ U₂ V₁ θ where
  /-- The second right factor $V_2$ is unitary. -/
  mem_unitaryGroup_right₂ : V₂ ∈ unitaryGroup (Fin n₂) 𝕜
  /-- The $(1, 2)$ block: $U_1^H Q_{12} V_2$ is `Matrix.csdUpperRight n₁ p q s`, with
  $s_i = \sin \theta_i$. -/
  star_mul_mul₁₂ : star U₁ * Q₁₂ * V₂ = csdUpperRight n₁ (n₁ - min n₁ m₂) (m₂ - min n₁ m₂)
    fun i => ((Real.sin (θ i) : ℝ) : 𝕜)
  /-- The $(2, 2)$ block: $U_2^H Q_{22} V_2$ is the rectangular diagonal matrix with
  $-\cos \theta_{i + p}$ at $(i, i)$ for $i < n_1 - p$ and $1$ at the other diagonal entries. -/
  star_mul_mul₂₂ : star U₂ * Q₂₂ * V₂ = rectDiagonal fun i =>
    if i < n₁ - (n₁ - min n₁ m₂) then -((Real.cos (θ (i + (n₁ - min n₁ m₂))) : ℝ) : 𝕜) else 1

/-- If $V$ is unitary, then $(U^H X V)(U'^H Y V)^H = U^H (X Y^H) U'$. -/
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

/-- **The CS decomposition** ([golub2013matrix], Theorem 2.5.3). Let $Q = \begin{bmatrix} Q_{11} &
Q_{12} \\ Q_{21} & Q_{22} \end{bmatrix}$ with $Q_{11} \in \mathbb{K}^{m_1 \times n_1}$,
$Q_{12} \in \mathbb{K}^{m_1 \times n_2}$, $Q_{21} \in \mathbb{K}^{m_2 \times n_1}$ and
$Q_{22} \in \mathbb{K}^{m_2 \times n_2}$, where $m_1 + m_2 = n_1 + n_2$, $Q^H Q = I$ and
$n_1 \le m_1$. Then $Q$ has a CS decomposition in the sense of `Matrix.IsCSD`.

The source defers the proof to Paige and Saunders (1981). Its second hypothesis $m_2 \le m_1$ is
not needed. Unitarity is given as $Q^H Q = I$ for the square shape $m_1 + m_2 = n_1 + n_2$,
which implies $Q Q^H = I$.

The proof takes a thin CS decomposition $(U_1, U_2, V_1, \theta)$ of the first block column
(`Matrix.exists_isThinCSD`). Let $Y_i = U_i^H Q_{i2}$, let
$\begin{bmatrix} C \\ S \end{bmatrix}$ be the transformed first block column, and let
$\begin{bmatrix} T_1 \\ T_2 \end{bmatrix}$ be the target second block column; set
$V_2 = Y_1^H T_1 + Y_2^H T_2$. The rows of the unitary matrix $\operatorname{diag}(U_1, U_2)^H Q
\operatorname{diag}(V_1, I)$ are orthonormal, so $Y Y^H = I - \begin{bmatrix} C \\ S
\end{bmatrix} \begin{bmatrix} C \\ S \end{bmatrix}^H$. The columns of
$\begin{bmatrix} T_1 \\ T_2 \end{bmatrix}$ are orthonormal and orthogonal to those of
$\begin{bmatrix} C \\ S \end{bmatrix}$, by an entrywise computation with $c_i^2 + s_i^2 = 1$.
Hence $Y V_2 = T$ and $V_2^H V_2 = T^H T = I$. -/
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
    rw [Matrix.add_apply, rectDiagonal_conjTranspose, rectDiagonal_mul_apply _ _ _ _
      (lt_of_lt_of_le a.isLt hn₁), conjTranspose_shiftedRectDiagonal_mul_apply, Matrix.zero_apply]
    simp only [hT₁, hT₂, csdUpperRight, of_apply, rectDiagonal_apply, Function.comp_apply,
      hσdef]
    by_cases hpa : p ≤ (a : ℕ)
    · have hk : (a : ℕ) - p < m₂ := by
        have := min_le_right n₁ m₂; omega
      rw [dite_eq_left ⟨hpa, hk⟩]
      by_cases hb : (b : ℕ) = a - p
      · rw [ite_eq_left ⟨hpa, a.isLt, hb⟩, ite_eq_left hb.symm,
          ite_eq_left (by omega),
          Nat.sub_add_cancel hpa]
        simp only [hcdef, hsdef, RCLike.star_def, RCLike.conj_ofReal]
        ring
      · rw [ite_eq_right (fun h => hb h.2.2), ite_eq_right (fun h => by omega),
          ite_eq_right (fun h => hb h.symm)]
        simp
    · rw [dite_eq_right (fun h => hpa h.1), ite_eq_right (fun h => hpa h.1),
        ite_eq_right (fun h => by omega)]
      simp
  have t2 : T₁ᴴ * T₁ + T₂ᴴ * T₂ = 1 := by
    have hmin2 := min_le_right n₁ m₂
    set ρ : ℕ → ℕ := fun j => if j < n₁ - p then j + p else j - q + p with hρdef
    set τ : ℕ → 𝕜 := fun j => if j < n₁ - p then s (j + p) else if n₁ - p + q ≤ j then 1 else 0
      with hτdef
    have hcol : ∀ (i : Fin m₁) (j : Fin n₂), T₁ i j = if (i : ℕ) = ρ j then τ j else 0 := by
      intro i j
      rw [hT₁, hρdef, hτdef]
      simp only [csdUpperRight, of_apply]
      split_ifs <;> first | rfl | (exfalso; omega) | congr 1
    have hsum : ∀ b b' : Fin n₂, (T₁ᴴ * T₁) b b'
        = if ρ b < m₁ ∧ ρ b = ρ b' then star (τ b) * τ b' else 0 := by
      intro b b'
      rw [Matrix.mul_apply]
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
    rw [Matrix.add_apply, hsum, diagonal_apply, Matrix.one_apply]
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
/-- **The off-diagonal blocks of a unitary matrix have equal $2$-norms** ([golub2013matrix], proof
of Theorem 2.5.1). Let $Q = \begin{bmatrix} Q_{11} & Q_{12} \\ Q_{21} & Q_{22} \end{bmatrix}$ be
a unitary matrix over $\mathbb{K}$, with rows and columns both indexed by $k \sqcup l$, so that
$Q_{11}$ is square. Then
$$\|Q_{21}\|_2 = \|Q_{12}\|_2.$$

The norm is the operator norm induced by the Euclidean norm. The first block column of $Q$ and
the first block column of $Q^H$ have orthonormal columns, with the square leading blocks
$Q_{11}$ and $Q_{11}^H$. By `Matrix.l2_opNorm_sq_eq_one_sub_sq_sortedSingularValues`, both
squared norms are $1 - \sigma_{\min}(Q_{11})^2$, because a square matrix and its conjugate
transpose have the same singular values. -/
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
