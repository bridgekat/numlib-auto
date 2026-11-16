/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside a future SVD.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.CSDecomposition

/-!
# The generalized singular value decomposition

Let $A \in \mathbb{K}^{m_1 \times n}$ and $B \in \mathbb{K}^{m_2 \times n}$ over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $r$ be the rank of the stacked matrix
$\begin{bmatrix} A \\ B \end{bmatrix}$, and let $p = \max(r - m_2, 0)$. The **generalized singular
value decomposition** (GSVD) of the pair $(A, B)$ diagonalizes both matrices at once: there are
unitary $U_1$, $U_2$ and an invertible $X$ with $$U_1^H A X = D_A, \qquad U_2^H B X = D_B,$$ where
$D_A$ is rectangular diagonal with entries $\alpha_i$, and $D_B$ is rectangular diagonal shifted by
$p$ columns with entries $\beta_i$. The pairs $(\alpha_i, \beta_i)$ are $(1, 0)$ for $i < p$,
cosine–sine pairs for $p \le i < r$, and $(0, 0)$ for $i \ge r$. This is Theorem 6.1.1 of
[golub2013matrix] (§6.1.6), after Van Loan (*Generalizing the singular value decomposition*, SIAM J.
Numer. Anal. 13, 1976) and Paige and Saunders (SIAM J. Numer. Anal. 18, 1981).

The module proves that a GSVD exists when $n \le m_1$, and derives its consequences: $X^H (A^H A +
\lambda B^H B) X = \operatorname{diag}(\alpha_i^2 + \lambda \beta_i^2)$, the columns of $X$ are
generalized eigenvectors of the pencil $A^H A - \mu^2 B^H B$, the columns $x_i$ with $i \ge r$ span
$\ker A \cap \ker B$, and the GSVD of $(A, I)$ is a singular value decomposition of $A$.

## Main definitions

* `Matrix.IsGSVD`: the statement that $(U_1, U_2, X, \alpha, \beta)$ is a GSVD of $(A, B)$.

## Main results

* `Matrix.exists_isGSVD`: [golub2013matrix] Theorem 6.1.1; for $n \le m_1$ every pair $(A, B)$ has a
  GSVD.
* `Matrix.IsGSVD.conjTranspose_mul_gram_add_smul_gram_mul`: $X^H (A^H A + \lambda B^H B) X =
  \operatorname{diag}(\alpha_i^2 + \lambda \beta_i^2)$.
* `Matrix.IsGSVD.inv_gram_add_smul_gram_eq`: the inverse of $A^H A + \lambda B^H B$ in GSVD
  coordinates.
* `Matrix.IsGSVD.gram_mulVec_col`: $\beta_i^2 A^H A x_i = \alpha_i^2 B^H B x_i$ for every column
  $x_i$ of $X$.
* `Matrix.IsGSVD.ker_inf_ker`: $\ker A \cap \ker B$ is spanned by the columns $x_i$ with $i \ge r$.
* `Matrix.mulVec_col_eq_smul_col_of_mul_eq_mul_rectDiagonal`,
  `Matrix.conjTranspose_mul_gram_mul_of_star_mul_mul_eq_rectDiagonal`: for one factorization
  $U^H M X = \operatorname{diag}(\gamma)$ with $U$ unitary, $M x_k = \gamma_k u_k$ and $X^H M^H M
  X = \operatorname{diag}(|\gamma_k|^2)$. These also serve the unshifted form of [golub2013matrix]
  Theorem 8.7.4. The pencil forms are `Matrix.hasPencilEigenvector_col_of_conj_diagonal` and
  `Matrix.pencilSpectrum_eq_range_of_conj_diagonal` in `Numlib.Eigen.Pencil`.
* `Matrix.IsGSVD.star_mul_mul_eq_of_eq_one`, `Matrix.IsGSVD.pos_of_eq_one`: the GSVD of $(A, I)$
  gives the SVD $U_1^H A U_2 = \operatorname{diag}(\alpha_i / \beta_i)$ with $\beta_i > 0$.
* `Matrix.IsGSVD.conjTranspose_mul_conjTranspose_left`,
  `Matrix.IsGSVD.conjTranspose_mul_conjTranspose_right`, `Matrix.IsGSVD.sq_add_smul_sq_ne_zero`,
  `Matrix.IsGSVD.rank_eq_and_ne_zero`: facts in GSVD coordinates that the least-squares applications
  use.

## Proof outline

Take an SVD $\begin{bmatrix} A \\ B \end{bmatrix} Z = Q_1 \Sigma_r \begin{bmatrix} I & 0
\end{bmatrix}$, where $Q_1$ holds the first $r$ columns of a unitary $Q$. A thin CS decomposition of
$Q_1 = \begin{bmatrix} Q_{11} \\ Q_{21} \end{bmatrix}$ gives $U_1$, $U_2$ and $V_1$
(`Matrix.exists_isThinCSD`, in the general form without $m_2 \ge r$). Then $X = Z \cdot
\operatorname{blockdiag}(V_1^H \Sigma_r, I)^{-1}$.

## Implementation notes

* The rectangular diagonal matrices are `Matrix.rectDiagonal` and `Matrix.shiftedRectDiagonal`. The
  sequences $\alpha, \beta$ are functions on $\mathbb{N}$, indexed from $0$, and $p = r - m_2$ is
  truncated subtraction of natural numbers.
* The field names follow the thin CS decomposition `Matrix.IsThinCSD` that the proof uses. The two
  left factors are `mem_unitaryGroup_left₁` ($U_1$, of $A$) and `mem_unitaryGroup_left₂` ($U_2$, of
  $B$), and the two diagonal forms are `star_mul_mul₁` and `star_mul_mul₂`. The lemmas about $A$ and
  $B$ carry the same subscripts.
* The consequences that read $\alpha_i$ off $D_A$ assume the standing hypothesis $n \le m_1$ of the
  source. Without it, the entries $\alpha_i$ with $m_1 \le i < n$ do not appear in the
  $m_1 \times n$ matrix $D_A$.
-/

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Def

variable {m₁ m₂ n : ℕ}

/-- Let $A \in \mathbb{K}^{m_1 \times n}$, $B \in \mathbb{K}^{m_2 \times n}$, let $r$ be the rank of
$\begin{bmatrix} A \\ B \end{bmatrix}$ and $p = \max(r - m_2, 0)$. A tuple
$(U_1, U_2, X, \alpha, \beta)$ with $U_1 \in \mathbb{K}^{m_1 \times m_1}$,
$U_2 \in \mathbb{K}^{m_2 \times m_2}$, $X \in \mathbb{K}^{n \times n}$ and real sequences
$\alpha, \beta$ is a **generalized singular value decomposition** of $(A, B)$ if $U_1$ and $U_2$
are unitary, $X$ is invertible, $$U_1^H A X = D_A, \qquad U_2^H B X = D_B,$$ where $D_A$ has
$\alpha_i$ at position $(i, i)$ and $D_B$ has $\beta_{i+p}$ at position $(i, i + p)$ and both
are zero elsewhere, and the pairs satisfy $\alpha_i, \beta_i \ge 0$ for all $i$,
$(\alpha_i, \beta_i) = (1, 0)$ for $i < p$, $\alpha_i^2 + \beta_i^2 = 1$ for $p \le i < r$, and
$\alpha_i = \beta_i = 0$ for $i \ge r$. This is Theorem 6.1.1 of [golub2013matrix],
(6.1.22)–(6.1.23).

The columns of $X$ are the vectors $x_1, \dots, x_n$ of the source. In Lean the indices start at
$0$. -/
structure IsGSVD (A : Matrix (Fin m₁) (Fin n) 𝕜) (B : Matrix (Fin m₂) (Fin n) 𝕜)
    (U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜) (U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜)
    (X : Matrix (Fin n) (Fin n) 𝕜) (α β : ℕ → ℝ) : Prop where
  /-- The first left factor $U_1$, of $A$, is unitary. -/
  mem_unitaryGroup_left₁ : U₁ ∈ unitaryGroup (Fin m₁) 𝕜
  /-- The second left factor $U_2$, of $B$, is unitary. -/
  mem_unitaryGroup_left₂ : U₂ ∈ unitaryGroup (Fin m₂) 𝕜
  /-- The right factor $X$ is invertible. -/
  isUnit : IsUnit X
  /-- For $i < p$, $\alpha_i = 1$ and $\beta_i = 0$. -/
  eq_one_and_eq_zero_of_lt : ∀ i < (fromRows A B).rank - m₂, α i = 1 ∧ β i = 0
  /-- For $p \le i < r$, $\alpha_i^2 + \beta_i^2 = 1$. -/
  sq_add_sq : ∀ i, (fromRows A B).rank - m₂ ≤ i → i < (fromRows A B).rank →
    α i ^ 2 + β i ^ 2 = 1
  /-- For every $i$, $\alpha_i \ge 0$ and $\beta_i \ge 0$. -/
  nonneg : ∀ i, 0 ≤ α i ∧ 0 ≤ β i
  /-- For $i \ge r$, $\alpha_i = \beta_i = 0$. -/
  eq_zero_and_eq_zero_of_rank_le : ∀ i, (fromRows A B).rank ≤ i → α i = 0 ∧ β i = 0
  /-- The factorization $U_1^H A X = D_A$, with $D_A$ rectangular diagonal with entries $\alpha_i$.
  -/
  star_mul_mul₁ : star U₁ * A * X = rectDiagonal fun i => ((α i : ℝ) : 𝕜)
  /-- The factorization $U_2^H B X = D_B$, with $D_B$ rectangular diagonal shifted by $p$ columns
  with entries $\beta_i$. -/
  star_mul_mul₂ : star U₂ * B * X =
    shiftedRectDiagonal ((fromRows A B).rank - m₂) fun i => ((β i : ℝ) : 𝕜)

end Def

section Exists

variable {m₁ m₂ n : ℕ}

/-- **Theorem 6.1.1** of [golub2013matrix], existence of the GSVD. Let
$A \in \mathbb{K}^{m_1 \times n}$ and $B \in \mathbb{K}^{m_2 \times n}$ with $n \le m_1$. Then
$(A, B)$ has a generalized singular value decomposition $(U_1, U_2, X, \alpha, \beta)$.

Let $\begin{bmatrix} A \\ B \end{bmatrix} Z = Q \Sigma = Q_1 \Sigma_r \begin{bmatrix} I & 0
\end{bmatrix}$ be an SVD, with $Q_1 = \begin{bmatrix} Q_{11} \\ Q_{21} \end{bmatrix}$ the first
$r$ columns of $Q$, and let $U_1^H Q_{11} V_1 = C$, $U_2^H Q_{21} V_1 = S$ be a thin CS
decomposition (`Matrix.exists_isThinCSD`, with $r \le n \le m_1$). With
$R = \begin{bmatrix} I_r & 0 \end{bmatrix}$, $Y = R^T \Sigma_r^{-1} V_1 R + (I - R^T R)$ and
$X = ZY$, one gets $AX = Q_{11} V_1 R$ and $BX = Q_{21} V_1 R$, and so the two diagonal forms.
The matrix $Y$ is invertible, with inverse $R^T V_1^H \Sigma_r R + (I - R^T R)$. -/
theorem exists_isGSVD (hnm : n ≤ m₁) (A : Matrix (Fin m₁) (Fin n) 𝕜)
    (B : Matrix (Fin m₂) (Fin n) 𝕜) : ∃ U₁ U₂ X α β, IsGSVD A B U₁ U₂ X α β := by
  classical
  set r := (fromRows A B).rank with hr
  set M : Matrix (Fin (m₁ + m₂)) (Fin n) 𝕜 :=
    (fromRows A B).submatrix finSumFinEquiv.symm (Equiv.refl _) with hM
  have hMr : M.rank = r := rank_submatrix _ _ _
  obtain ⟨Q, σ, Z, hs⟩ := exists_isSVD M
  have hrn : r ≤ n := by
    have := rank_le_card_width (fromRows A B); rwa [Fintype.card_fin] at this
  have hrm : r ≤ m₁ + m₂ := by
    have := rank_le_card_height (fromRows A B)
    rwa [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at this
  have hσpos : ∀ i < r, σ i ≠ 0 := fun i hi => by
    rw [hs.singularValues_eq (by omega) (by omega), Ne, sortedSingularValues_eq_zero_iff_rank_le,
      hMr]
    omega
  have hσzero : ∀ i, r ≤ i → i < m₁ + m₂ → i < n → σ i = 0 := fun i h1 h2 h3 => by
    rw [hs.singularValues_eq h2 h3, sortedSingularValues_eq_zero_iff_rank_le, hMr]
    exact h1
  -- the first `r` columns of `Q`, split into blocks
  set Q₁₁ : Matrix (Fin m₁) (Fin r) 𝕜 := Q.submatrix (Fin.castAdd m₂) (Fin.castLE hrm)
  set Q₂₁ : Matrix (Fin m₂) (Fin r) 𝕜 := Q.submatrix (Fin.natAdd m₁) (Fin.castLE hrm)
  have hQQ := conjTranspose_mul_self_of_mem_unitaryGroup hs.mem_unitaryGroup_left
  have hQo : Q₁₁ᴴ * Q₁₁ + Q₂₁ᴴ * Q₂₁ = 1 := by
    ext i j
    have h := congrFun (congrFun hQQ (Fin.castLE hrm i)) (Fin.castLE hrm j)
    rw [Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply] at h
    simp only [(Fin.castLE_injective hrm).eq_iff] at h
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.one_apply]
    simpa [Q₁₁, Q₂₁, conjTranspose_apply, submatrix_apply] using h
  obtain ⟨U₁, U₂, V₁, θ, hc⟩ := exists_isThinCSD Q₁₁ Q₂₁ hQo (hrn.trans hnm)
  -- the selector `R = [I_r 0]` and the diagonal `Σ_r`
  set R : Matrix (Fin r) (Fin n) 𝕜 := rectDiagonal fun _ => 1 with hR
  set D : Matrix (Fin r) (Fin r) 𝕜 := diagonal fun i => ((σ i : ℝ) : 𝕜) with hD
  set Dinv : Matrix (Fin r) (Fin r) 𝕜 := diagonal fun i => ((σ i : ℝ) : 𝕜)⁻¹ with hDinv
  have hσ' : ∀ i : Fin r, ((σ i : ℝ) : 𝕜) ≠ 0 := fun i =>
    RCLike.ofReal_ne_zero.2 (hσpos i i.isLt)
  have hDX : ∀ Y : Matrix (Fin r) (Fin n) 𝕜, D * (Dinv * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hD, hDinv, diagonal_mul_diagonal,
      show (fun i : Fin r => ((σ i : ℝ) : 𝕜) * ((σ i : ℝ) : 𝕜)⁻¹) = fun _ => 1 from
        funext fun i => mul_inv_cancel₀ (hσ' i), diagonal_one, Matrix.one_mul]
  have hDX' : ∀ Y : Matrix (Fin r) (Fin n) 𝕜, Dinv * (D * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hD, hDinv, diagonal_mul_diagonal,
      show (fun i : Fin r => ((σ i : ℝ) : 𝕜)⁻¹ * ((σ i : ℝ) : 𝕜)) = fun _ => 1 from
        funext fun i => inv_mul_cancel₀ (hσ' i), diagonal_one, Matrix.one_mul]
  have hRRt : R * Rᵀ = 1 := by
    rw [hR, rectDiagonal_transpose, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    rw [ite_eq_left (lt_of_lt_of_le i.isLt hrn), mul_one]
  have hRX : ∀ Y : Matrix (Fin r) (Fin n) 𝕜, R * (Rᵀ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hRRt, Matrix.one_mul]
  have hVV := mul_conjTranspose_self_of_mem_unitaryGroup hc.mem_unitaryGroup_right
  have hVX : ∀ Y : Matrix (Fin r) (Fin n) 𝕜, V₁ * (V₁ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
  -- the right factor `X = Z Y`
  set Y : Matrix (Fin n) (Fin n) 𝕜 := Rᵀ * (Dinv * (V₁ * R)) + (1 - Rᵀ * R) with hY
  have hYinv : Y * (Rᵀ * (V₁ᴴ * (D * R)) + (1 - Rᵀ * R)) = 1 := by
    simp only [hY, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hRX, hVX, hDX']
    abel
  have hRY : R * Y = Dinv * (V₁ * R) := by
    simp only [hY, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, hRX, sub_self, add_zero]
  -- `[A; B] Z = Q₁ Σ_r R`
  have hMZ : ∀ i j, (M * Z) i j
      = if h : (j : ℕ) < r then Q i (Fin.castLE hrm ⟨j, h⟩) * ((σ j : ℝ) : 𝕜) else 0 := by
    have h1 : M * Z = Q * rectDiagonal fun i => ((σ i : ℝ) : 𝕜) := by
      rw [← hs.star_mul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        mem_unitaryGroup_iff.1 hs.mem_unitaryGroup_left, Matrix.one_mul]
    intro i j
    rw [h1, mul_rectDiagonal_apply]
    by_cases hj : (j : ℕ) < r
    · rw [dite_eq_left_of_eq_true (eq_true (lt_of_lt_of_le hj hrm)),
        dite_eq_left_of_eq_true (eq_true hj)]
      rfl
    · rw [dite_eq_right_of_eq_false (eq_false hj)]
      split_ifs with hj'
      · rw [hσzero j (not_lt.1 hj) hj' j.isLt, RCLike.ofReal_zero, mul_zero]
      · rfl
  have hAZ : A * Z = Q₁₁ * D * R := by
    ext i j
    rw [mul_rectDiagonal_apply,
      show (A * Z) i j = (M * Z) (Fin.castAdd m₂ i) j by simp [Matrix.mul_apply, hM], hMZ]
    split_ifs
    · simp [Q₁₁, hD, mul_diagonal]
    · rfl
  have hBZ : B * Z = Q₂₁ * D * R := by
    ext i j
    rw [mul_rectDiagonal_apply,
      show (B * Z) i j = (M * Z) (Fin.natAdd m₁ i) j by simp [Matrix.mul_apply, hM], hMZ]
    split_ifs
    · simp [Q₂₁, hD, mul_diagonal]
    · rfl
  have hAX : A * (Z * Y) = Q₁₁ * (V₁ * R) := by
    rw [← Matrix.mul_assoc, hAZ]
    simp only [Matrix.mul_assoc, hRY, hDX]
  have hBX : B * (Z * Y) = Q₂₁ * (V₁ * R) := by
    rw [← Matrix.mul_assoc, hBZ]
    simp only [Matrix.mul_assoc, hRY, hDX]
  -- the generalized singular values
  set α : ℕ → ℝ := fun i => if i < r then Real.cos (θ i) else 0 with hα
  set β : ℕ → ℝ := fun i => if i < r then Real.sin (θ i) else 0 with hβ
  have hp : r - min r m₂ = r - m₂ := by omega
  refine ⟨U₁, U₂, Z * Y, α, β, hc.mem_unitaryGroup_left₁, hc.mem_unitaryGroup_left₂,
    (isUnit_of_mem_unitaryGroup hs.mem_unitaryGroup_right).mul
      ((isUnit_iff_isUnit_det Y).2 (isUnit_det_of_right_inverse hYinv)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < r := by omega
    have hθ := hc.eq_zero_of_lt i (by omega)
    simp only [hα, hβ, hi', ↓reduceIte, hθ, Real.cos_zero, Real.sin_zero, and_self]
  · intro i _ hi
    have hi' : i < r := hi
    simp only [hα, hβ, hi', ↓reduceIte]
    exact Real.cos_sq_add_sin_sq _
  · intro i
    simp only [hα, hβ]
    split_ifs
    · exact ⟨hc.cos_nonneg i, hc.sin_nonneg i⟩
    · exact ⟨le_rfl, le_rfl⟩
  · intro i hi
    have hi' : ¬ i < r := not_lt.2 hi
    simp only [hα, hβ, hi', ↓reduceIte, and_self]
  · rw [Matrix.mul_assoc, hAX]
    simp only [← Matrix.mul_assoc]
    rw [hc.star_mul_mul₁]
    ext i j
    rw [mul_rectDiagonal_apply]
    by_cases hj : (j : ℕ) < r <;> by_cases hij : (i : ℕ) = j <;>
      simp [rectDiagonal_apply, hα, hj, hij]
  · rw [Matrix.mul_assoc, hBX]
    simp only [← Matrix.mul_assoc]
    rw [hc.star_mul_mul₂, hp]
    ext i j
    rw [mul_rectDiagonal_apply]
    by_cases hij : (j : ℕ) = i + (r - m₂)
    · by_cases hj : (i : ℕ) + (r - m₂) < r <;>
        simp [shiftedRectDiagonal_apply, hβ, hj, hij, ← hr]
    · by_cases hj : (j : ℕ) < r <;> simp [shiftedRectDiagonal_apply, hβ, hj, hij, ← hr]

end Exists

/-!
### Simultaneous diagonal forms

The results below use only one factorization $U^H M X = D$ with $U$ unitary and $D$ rectangular
diagonal, or a congruence of two matrices to diagonal ones by the same invertible $X$. They serve
the GSVD and its tall rectangular form ([golub2013matrix] Theorem 8.7.4) alike.
-/

section DiagonalForms

variable {m n : ℕ} {M : Matrix (Fin m) (Fin n) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜}
  {X : Matrix (Fin n) (Fin n) 𝕜}

/-- Let $M \in \mathbb{K}^{m \times n}$, $X \in \mathbb{K}^{n \times n}$ and let
$U \in \mathbb{K}^{m \times m}$ be unitary. If $U^H M X = D$, then $MX = UD$. -/
theorem mul_eq_mul_of_star_mul_mul_eq {D : Matrix (Fin m) (Fin n) 𝕜}
    (hU : U ∈ unitaryGroup (Fin m) 𝕜) (h : star U * M * X = D) : M * X = U * D := by
  rw [← h, Matrix.mul_assoc, ← Matrix.mul_assoc U, star_eq_conjTranspose,
    mul_conjTranspose_self_of_mem_unitaryGroup hU, Matrix.one_mul]

/-- Let $M \in \mathbb{K}^{m \times n}$, $X \in \mathbb{K}^{n \times n}$ and let
$U \in \mathbb{K}^{m \times m}$ be unitary. Then $X^H M^H M X = (U^H M X)^H (U^H M X)$. -/
theorem conjTranspose_mul_gram_mul_eq (hU : U ∈ unitaryGroup (Fin m) 𝕜) :
    Xᴴ * (Mᴴ * M) * X = (star U * M * X)ᴴ * (star U * M * X) := by
  simp only [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U, mul_conjTranspose_self_of_mem_unitaryGroup hU, Matrix.one_mul]

/-- Let $M \in \mathbb{K}^{m \times n}$ with $n \le m$, $X \in \mathbb{K}^{n \times n}$, and let
$U \in \mathbb{K}^{m \times m}$ be unitary. If $U^H M X = \operatorname{diag}(\gamma)$ is
rectangular diagonal, then $$X^H M^H M X = \operatorname{diag}(|\gamma_0|^2, \dots,
|\gamma_{n-1}|^2).$$ So **a unitary rectangular diagonal form diagonalizes the Gram matrix**.
The sequence $\gamma$ is indexed from $0$. -/
theorem conjTranspose_mul_gram_mul_of_star_mul_mul_eq_rectDiagonal (hnm : n ≤ m)
    (hU : U ∈ unitaryGroup (Fin m) 𝕜) {γ : ℕ → 𝕜} (h : star U * M * X = rectDiagonal γ) :
    Xᴴ * (Mᴴ * M) * X = diagonal fun k : Fin n => star (γ k) * γ k := by
  rw [conjTranspose_mul_gram_mul_eq hU, h, conjTranspose_rectDiagonal_mul_self]
  congr 1
  funext k
  rw [ite_eq_left (lt_of_lt_of_le k.isLt hnm)]

/-- Let $M \in \mathbb{K}^{m \times n}$ with $n \le m$, $X \in \mathbb{K}^{n \times n}$ and
$U \in \mathbb{K}^{m \times m}$. If $MX = U \operatorname{diag}(\gamma)$ with a rectangular
diagonal $\operatorname{diag}(\gamma)$, then $$M x_k = \gamma_k u_k$$ for every $k$, where $x_k$
and $u_k$ are the $k$-th columns of $X$ and $U$. -/
theorem mulVec_col_eq_smul_col_of_mul_eq_mul_rectDiagonal (hnm : n ≤ m) {γ : ℕ → 𝕜}
    (h : M * X = U * rectDiagonal γ) (k : Fin n) :
    M *ᵥ X.col k = γ k • U.col (Fin.castLE hnm k) := by
  rw [← col_mul_eq_mulVec_col, h]
  ext i
  simp only [col_apply, Matrix.mul_apply, rectDiagonal_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (Fin.castLE hnm k)]
  · simp [mul_comm]
  · intro j _ hj
    have hj' : ¬ ((j : ℕ) = k) := fun h => hj (Fin.ext (by simp [h]))
    simp [hj']
  · simp

end DiagonalForms

/-! ### Consequences of a GSVD -/

section Consequences

variable {m₁ m₂ n : ℕ} {A : Matrix (Fin m₁) (Fin n) 𝕜} {B : Matrix (Fin m₂) (Fin n) 𝕜}
  {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜}
  {X : Matrix (Fin n) (Fin n) 𝕜} {α β : ℕ → ℝ}

/-- In a GSVD of $(A, B)$, $AX = U_1 D_A$. -/
theorem IsGSVD.mul_eq₁ (h : IsGSVD A B U₁ U₂ X α β) :
    A * X = U₁ * rectDiagonal fun i => ((α i : ℝ) : 𝕜) :=
  mul_eq_mul_of_star_mul_mul_eq h.mem_unitaryGroup_left₁ h.star_mul_mul₁

/-- In a GSVD of $(A, B)$, $BX = U_2 D_B$. -/
theorem IsGSVD.mul_eq₂ (h : IsGSVD A B U₁ U₂ X α β) :
    B * X = U₂ * shiftedRectDiagonal ((fromRows A B).rank - m₂) fun i => ((β i : ℝ) : 𝕜) :=
  mul_eq_mul_of_star_mul_mul_eq h.mem_unitaryGroup_left₂ h.star_mul_mul₂

/-- Let $(U_1, U_2, X, \alpha, \beta)$ be a GSVD of $(A, B)$ with $n \le m_1$. Then $$X^H A^H A X =
\operatorname{diag}(\alpha_0^2, \dots, \alpha_{n-1}^2).$$
-/
theorem IsGSVD.conjTranspose_mul_gram_mul₁ (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) :
    Xᴴ * (Aᴴ * A) * X = diagonal fun i : Fin n => ((α i ^ 2 : ℝ) : 𝕜) := by
  rw [conjTranspose_mul_gram_mul_eq h.mem_unitaryGroup_left₁, h.star_mul_mul₁,
    conjTranspose_rectDiagonal_mul_self]
  congr 1
  funext j
  rw [ite_eq_left (lt_of_lt_of_le j.isLt hnm), RCLike.star_def, RCLike.conj_ofReal]
  push_cast
  ring

/-- Let $(U_1, U_2, X, \alpha, \beta)$ be a GSVD of $(A, B)$. Then $$X^H B^H B X =
\operatorname{diag}(\beta_0^2, \dots, \beta_{n-1}^2).$$

The shift of $D_B$ disappears, and the $\beta_j$ that $D_B$ does not contain vanish. -/
theorem IsGSVD.conjTranspose_mul_gram_mul₂ (h : IsGSVD A B U₁ U₂ X α β) :
    Xᴴ * (Bᴴ * B) * X = diagonal fun i : Fin n => ((β i ^ 2 : ℝ) : 𝕜) := by
  rw [conjTranspose_mul_gram_mul_eq h.mem_unitaryGroup_left₂, h.star_mul_mul₂,
    conjTranspose_shiftedRectDiagonal_mul_self]
  congr 1
  funext j
  split_ifs with hj
  · rw [RCLike.star_def, RCLike.conj_ofReal]
    push_cast
    ring
  · have hβ : β j = 0 := by
      rcases not_and_or.1 hj with hj | hj
      · exact (h.eq_one_and_eq_zero_of_lt j (not_le.1 hj)).2
      · exact (h.eq_zero_and_eq_zero_of_rank_le j (by omega)).2
    rw [hβ]
    simp

/-- Let $(U_1, U_2, X, \alpha, \beta)$ be a GSVD of $(A, B)$ with $n \le m_1$, and let
$\lambda \in \mathbb{R}$. Then $$X^H (A^H A + \lambda B^H B) X =
\operatorname{diag}(\alpha_i^2 + \lambda \beta_i^2).$$ This is the display before (6.1.26) in
§6.1.6 of [golub2013matrix], used again in §6.2.6. -/
theorem IsGSVD.conjTranspose_mul_gram_add_smul_gram_mul (h : IsGSVD A B U₁ U₂ X α β)
    (hnm : n ≤ m₁) (μ : ℝ) :
    Xᴴ * (Aᴴ * A + (μ : 𝕜) • (Bᴴ * B)) * X
      = diagonal fun i : Fin n => ((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    h.conjTranspose_mul_gram_mul₁ hnm, h.conjTranspose_mul_gram_mul₂, ← diagonal_smul,
    diagonal_add]
  congr 1
  funext i
  push_cast
  rw [Pi.smul_apply, smul_eq_mul]

/-- Let $(U_1, U_2, X, \alpha, \beta)$ be a GSVD of $(A, B)$ with $n \le m_1$, let
$\lambda \in \mathbb{R}$, and suppose that $\alpha_i^2 + \lambda \beta_i^2 \ne 0$ for every
$i < n$. Then $$(A^H A + \lambda B^H B)^{-1} = X \operatorname{diag}(\alpha_i^2 + \lambda
\beta_i^2)^{-1} X^H.$$
-/
theorem IsGSVD.inv_gram_add_smul_gram_eq (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) (μ : ℝ)
    (hd : ∀ i : Fin n, α i ^ 2 + μ * β i ^ 2 ≠ 0) :
    (Aᴴ * A + (μ : 𝕜) • (Bᴴ * B))⁻¹
      = X * diagonal (fun i : Fin n => (((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜))⁻¹) * Xᴴ := by
  have hG := h.conjTranspose_mul_gram_add_smul_gram_mul hnm μ
  have hXd : IsUnit X.det := (isUnit_iff_isUnit_det X).1 h.isUnit
  have hXG : Xᴴ * (Aᴴ * A + (μ : 𝕜) • (Bᴴ * B))
      = diagonal (fun i : Fin n => ((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜)) * X⁻¹ := by
    rw [← hG, Matrix.mul_assoc _ X, mul_nonsing_inv _ hXd, Matrix.mul_one]
  refine inv_eq_left_inv ?_
  rw [Matrix.mul_assoc, hXG, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),
    diagonal_mul_diagonal,
    show (fun i : Fin n => (((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜))⁻¹ *
        ((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜)) = fun _ => 1 from
      funext fun i => inv_mul_cancel₀ (RCLike.ofReal_ne_zero.2 (hd i)),
    diagonal_one, Matrix.one_mul, mul_nonsing_inv _ hXd]

/-- Let $(U_1, U_2, X, \alpha, \beta)$ be a GSVD of $(A, B)$ with $n \le m_1$. For every column
$x_i$ of $X$, $$\beta_i^2 A^H A x_i = \alpha_i^2 B^H B x_i,$$ so **the GSVD diagonalizes the
pencil $A^H A - \mu^2 B^H B$**. This is the remark in §6.1.6 of [golub2013matrix] that relates
the GSVD to $A^T A x = \mu^2 B^T B x$, taken up again in §8.7.4. -/
theorem IsGSVD.gram_mulVec_col (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) (i : Fin n) :
    ((β i ^ 2 : ℝ) : 𝕜) • ((Aᴴ * A) *ᵥ X.col i)
      = ((α i ^ 2 : ℝ) : 𝕜) • ((Bᴴ * B) *ᵥ X.col i) :=
  smul_mulVec_col_eq_of_conj_diagonal h.isUnit (h.conjTranspose_mul_gram_mul₁ hnm)
    h.conjTranspose_mul_gram_mul₂ i

/-- For matrices $A$ and $B$ with the same columns, $\ker A \cap \ker B = \ker \begin{bmatrix} A \\
B \end{bmatrix}$. -/
theorem ker_inf_ker_eq_ker_fromRows {m₁ m₂ n : Type*} [Fintype n] (A : Matrix m₁ n 𝕜)
    (B : Matrix m₂ n 𝕜) :
    LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin
      = LinearMap.ker (fromRows A B).mulVecLin := by
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker, mulVecLin_apply, fromRows_mulVec]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    ext (_ | _) <;> rfl
  · intro h0
    exact ⟨funext fun k => congrFun h0 (Sum.inl k), funext fun k => congrFun h0 (Sum.inr k)⟩

/-- Let $(U_1, U_2, X, \alpha, \beta)$ be a GSVD of $(A, B)$ and $r = \operatorname{rank}
\begin{bmatrix} A \\ B \end{bmatrix}$. Then $\ker A \cap \ker B$ is the span of the columns
$x_i$ of $X$ with $i \ge r$.

These columns are mapped to $0$ by both matrices, since $\alpha_i = \beta_i = 0$, and they are
linearly independent; $\ker A \cap \ker B = \ker \begin{bmatrix} A \\ B \end{bmatrix}$ has
dimension $n - r$. The result is used for (6.1.21) and (6.2.12) of [golub2013matrix]:
$\operatorname{null}(A) \cap \operatorname{null}(B) = \{0\}$ if and only if $r = n$. -/
theorem IsGSVD.ker_inf_ker (h : IsGSVD A B U₁ U₂ X α β) :
    LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin
      = Submodule.span 𝕜 (X.col '' {i | (fromRows A B).rank ≤ (i : ℕ)}) := by
  classical
  set r := (fromRows A B).rank with hr
  have hAX := h.mul_eq₁
  have hBX := h.mul_eq₂
  have hle : Submodule.span 𝕜 (X.col '' {i | r ≤ (i : ℕ)})
      ≤ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨hα, hβ⟩ := h.eq_zero_and_eq_zero_of_rank_le i hi
    refine ⟨?_, ?_⟩
    · change A *ᵥ X.col i = 0
      rw [← col_mul_eq_mulVec_col, hAX]
      ext k
      rw [col_apply, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [rectDiagonal_apply]
      split_ifs with hli
      · rw [hli, hα, RCLike.ofReal_zero, mul_zero]
      · rw [mul_zero]
    · change B *ᵥ X.col i = 0
      rw [← col_mul_eq_mulVec_col, hBX]
      ext k
      rw [col_apply, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun l _ => by simp [shiftedRectDiagonal_apply, hβ]
  have hcard : Fintype.card {i : Fin n // r ≤ (i : ℕ)} = n - r := by
    rw [← Fintype.card_fin (n - r)]
    exact Fintype.card_congr
      { toFun := fun i => ⟨i.1 - r, by omega⟩
        invFun := fun k => ⟨⟨k + r, by omega⟩, by
          change r ≤ (k : ℕ) + r; omega⟩
        left_inv := fun i => by
          apply Subtype.ext; apply Fin.ext
          simp only
          omega
        right_inv := fun k => by
          apply Fin.ext
          simp }
  have hspan : Submodule.span 𝕜 (X.col '' {i | r ≤ (i : ℕ)})
      = Submodule.span 𝕜 (Set.range fun k : {i : Fin n // r ≤ (i : ℕ)} => X.col k) := by
    congr 1
    ext v
    simp
  have hfin : Module.finrank 𝕜 (Submodule.span 𝕜 (X.col '' {i | r ≤ (i : ℕ)})) = n - r := by
    rw [hspan]
    exact (finrank_span_eq_card (b := fun k : {i : Fin n // r ≤ (i : ℕ)} => X.col k)
      ((linearIndependent_cols_of_isUnit h.isUnit).comp _ Subtype.val_injective)).trans hcard
  have hker : Module.finrank 𝕜 (LinearMap.ker (fromRows A B).mulVecLin) = n - r := by
    have := LinearMap.finrank_range_add_finrank_ker (fromRows A B).mulVecLin
    rw [Module.finrank_fin_fun] at this
    change r + _ = n at this
    omega
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [hfin, ker_inf_ker_eq_ker_fromRows, hker]

/-- For every $A \in \mathbb{K}^{m_1 \times n}$, the stacked matrix
$\begin{bmatrix} A \\ I \end{bmatrix}$ has rank $n$. -/
theorem rank_fromRows_one (A : Matrix (Fin m₁) (Fin n) 𝕜) :
    (fromRows A (1 : Matrix (Fin n) (Fin n) 𝕜)).rank = n := by
  have hker : LinearMap.ker (fromRows A (1 : Matrix (Fin n) (Fin n) 𝕜)).mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [mulVecLin_apply, fromRows_mulVec] at hv
    have := congrFun hv
    funext k
    simpa using this (Sum.inr k)
  have := LinearMap.finrank_range_add_finrank_ker
    (fromRows A (1 : Matrix (Fin n) (Fin n) 𝕜)).mulVecLin
  rw [Module.finrank_fin_fun, hker, finrank_bot] at this
  change (fromRows A (1 : Matrix (Fin n) (Fin n) 𝕜)).rank + 0 = n at this
  omega

section OfEqOne

variable {A : Matrix (Fin m₁) (Fin n) 𝕜} {U₂ : Matrix (Fin n) (Fin n) 𝕜}

/-- In a GSVD of $(A, I)$, the right factor is $X = U_2 \operatorname{diag}(\beta_0, \dots,
\beta_{n-1})$, because $p = 0$ when $\operatorname{rank} \begin{bmatrix} A \\ I \end{bmatrix} =
n$ (`Matrix.rank_fromRows_one`). -/
theorem IsGSVD.eq_mul_diagonal_of_eq_one
    (h : IsGSVD A (1 : Matrix (Fin n) (Fin n) 𝕜) U₁ U₂ X α β) :
    X = U₂ * diagonal fun i : Fin n => ((β i : ℝ) : 𝕜) := by
  have hX := h.mul_eq₂
  rw [Matrix.one_mul, rank_fromRows_one, Nat.sub_self, shiftedRectDiagonal_zero,
    rectDiagonal_eq_diagonal] at hX
  exact hX

/-- In a GSVD of $(A, I)$, $\beta_i > 0$ for every $i < n$, because
$X = U_2 \operatorname{diag}(\beta)$ is invertible. -/
theorem IsGSVD.pos_of_eq_one (h : IsGSVD A (1 : Matrix (Fin n) (Fin n) 𝕜) U₁ U₂ X α β) :
    ∀ i < n, 0 < β i := by
  intro i hi
  refine lt_of_le_of_ne (h.nonneg i).2 fun hβ => ?_
  have hdet := (isUnit_iff_isUnit_det X).1 h.isUnit
  rw [h.eq_mul_diagonal_of_eq_one, det_mul, det_diagonal] at hdet
  exact (isUnit_of_mul_isUnit_right hdet).ne_zero
    (Finset.prod_eq_zero (Finset.mem_univ ⟨i, hi⟩)
      (show ((β i : ℝ) : 𝕜) = 0 by rw [← hβ, RCLike.ofReal_zero]))

/-- Let $(U_1, U_2, X, \alpha, \beta)$ be a GSVD of $(A, I)$ with $I$ the $n \times n$ identity.
Then $$U_1^H A U_2 = \operatorname{diag}(\alpha_i / \beta_i),$$ a singular value decomposition
of $A$ with singular values $\alpha_i / \beta_i$ (not sorted). This makes precise the remark of
[golub2013matrix] §6.1.6 that the GSVD with $B = I$ gives the SVD of $A$.

The denominators are positive by `Matrix.IsGSVD.pos_of_eq_one`. The instruction "set $X = U_2$"
of the source is loose: $X$ itself is $U_2 D_B$ (`Matrix.IsGSVD.eq_mul_diagonal_of_eq_one`). -/
theorem IsGSVD.star_mul_mul_eq_of_eq_one
    (h : IsGSVD A (1 : Matrix (Fin n) (Fin n) 𝕜) U₁ U₂ X α β) :
    star U₁ * A * U₂ = rectDiagonal fun i => ((α i / β i : ℝ) : 𝕜) := by
  have hβ0 : ∀ i : Fin n, ((β i : ℝ) : 𝕜) ≠ 0 := fun i =>
    RCLike.ofReal_ne_zero.2 (h.pos_of_eq_one i i.isLt).ne'
  have hU₂ : U₂ = X * diagonal fun i : Fin n => (((β i : ℝ) : 𝕜))⁻¹ := by
    rw [h.eq_mul_diagonal_of_eq_one, Matrix.mul_assoc, diagonal_mul_diagonal]
    conv_lhs => rw [← Matrix.mul_one U₂]
    congr 1
    rw [← diagonal_one]
    congr 1
    funext i
    rw [mul_inv_cancel₀ (hβ0 i)]
  rw [hU₂, ← Matrix.mul_assoc, h.star_mul_mul₁]
  ext i j
  rw [mul_diagonal, rectDiagonal_apply, rectDiagonal_apply]
  split_ifs with hij
  · rw [hij]
    push_cast
    rw [div_eq_mul_inv]
  · rw [zero_mul]

end OfEqOne

end Consequences

/-! ### Facts used in GSVD coordinates -/

section Facts

variable {m₁ m₂ n : ℕ} {A : Matrix (Fin m₁) (Fin n) 𝕜} {B : Matrix (Fin m₂) (Fin n) 𝕜}
  {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜}
  {X : Matrix (Fin n) (Fin n) 𝕜} {α β : ℕ → ℝ}

/-- In a GSVD of $(A, B)$, $X^H A^H = D_A^H U_1^H$, where $D_A$ is real. -/
theorem IsGSVD.conjTranspose_mul_conjTranspose_left (h : IsGSVD A B U₁ U₂ X α β) :
    Xᴴ * Aᴴ = (rectDiagonal fun i => ((α i : ℝ) : 𝕜) : Matrix (Fin n) (Fin m₁) 𝕜) * star U₁ := by
  have hAX : A * X = U₁ * rectDiagonal fun i => ((α i : ℝ) : 𝕜) := by
    rw [← h.star_mul_mul₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      mem_unitaryGroup_iff.1 h.mem_unitaryGroup_left₁, Matrix.one_mul]
  rw [← conjTranspose_mul, hAX, conjTranspose_mul, rectDiagonal_conjTranspose,
    star_eq_conjTranspose]
  congr 2
  funext i
  simp

/-- In a GSVD of $(A, B)$, $X^H B^H = D_B^H U_2^H$. -/
theorem IsGSVD.conjTranspose_mul_conjTranspose_right (h : IsGSVD A B U₁ U₂ X α β) :
    Xᴴ * Bᴴ = (shiftedRectDiagonal ((fromRows A B).rank - m₂) fun i => ((β i : ℝ) : 𝕜) :
      Matrix (Fin m₂) (Fin n) 𝕜)ᴴ * star U₂ := by
  have hBX : B * X =
      U₂ * shiftedRectDiagonal ((fromRows A B).rank - m₂) fun i => ((β i : ℝ) : 𝕜) := by
    rw [← h.star_mul_mul₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      mem_unitaryGroup_iff.1 h.mem_unitaryGroup_left₂, Matrix.one_mul]
  rw [← conjTranspose_mul, hBX, conjTranspose_mul, star_eq_conjTranspose]

/-- Let $(U_1, U_2, X, \alpha, \beta)$ be a GSVD of $(A, B)$, let $\mu > 0$ and $i < r$. Then
$\alpha_i^2 + \mu \beta_i^2 \ne 0$, because the pair $(\alpha_i, \beta_i)$ is $(1, 0)$ or a
cosine–sine pair. -/
theorem IsGSVD.sq_add_smul_sq_ne_zero (h : IsGSVD A B U₁ U₂ X α β) {μ : ℝ} (hμ : 0 < μ)
    {i : ℕ} (hi : i < (fromRows A B).rank) : α i ^ 2 + μ * β i ^ 2 ≠ 0 := by
  by_cases hp : i < (fromRows A B).rank - m₂
  · rw [(h.eq_one_and_eq_zero_of_lt i hp).1, (h.eq_one_and_eq_zero_of_lt i hp).2]
    norm_num
  · have hs := h.sq_add_sq i (not_lt.1 hp) hi
    intro h0
    have hb : μ * β i ^ 2 = 0 := by
      nlinarith [sq_nonneg (α i), mul_nonneg hμ.le (sq_nonneg (β i))]
    have hb' : β i ^ 2 = 0 := (mul_eq_zero.1 hb).resolve_left hμ.ne'
    nlinarith [sq_nonneg (α i)]

/-- Let $(U_1, U_2, X, \alpha, \beta)$ be a GSVD of $(A, B)$, let the rows of $B$ be linearly
independent, and let $\ker A \cap \ker B = \{0\}$. Then $r = n$, $m_2 \le n$, and
$\beta_j \ne 0$ for $n - m_2 \le j < n$.

Here $p = n - m_2$. A zero $\beta_j$ would make a row of $D_B = U_2^H B X$ vanish. -/
theorem IsGSVD.rank_eq_and_ne_zero (h : IsGSVD A B U₁ U₂ X α β)
    (hB : LinearIndependent 𝕜 B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    (fromRows A B).rank = n ∧ m₂ ≤ n ∧ ∀ j : Fin n, n - m₂ ≤ (j : ℕ) → β j ≠ 0 := by
  classical
  have hrn : (fromRows A B).rank = n := by
    have := LinearMap.finrank_range_add_finrank_ker (fromRows A B).mulVecLin
    rw [Module.finrank_fin_fun, ← ker_inf_ker_eq_ker_fromRows, hAB, finrank_bot] at this
    change (fromRows A B).rank + 0 = n at this
    omega
  have hpn : m₂ ≤ n := by
    have := hB.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_fin_fun] at this
  refine ⟨hrn, hpn, fun j hj hβ => ?_⟩
  have hDB := h.star_mul_mul₂
  rw [hrn] at hDB
  -- the row `j − (n − m₂)` of `D_B` vanishes
  set k : Fin m₂ := ⟨j - (n - m₂), by omega⟩
  have hrow : Pi.single k 1 ᵥ* (star U₂ * B * X) = 0 ᵥ* (star U₂ * B * X) := by
    rw [hDB, zero_vecMul]
    ext l
    rw [single_one_vecMul, Pi.zero_apply]
    change shiftedRectDiagonal (n - m₂) (fun i => ((β i : ℝ) : 𝕜)) k l = 0
    rw [shiftedRectDiagonal_apply]
    split_ifs with hl
    · have : l = j := Fin.ext (by simp only [k] at hl; omega)
      rw [this, hβ, RCLike.ofReal_zero]
    · rfl
  have hinj : Function.Injective (star U₂ * B * X).vecMul := by
    intro u v huv
    have hU : Function.Injective (star U₂).vecMul :=
      vecMul_injective_iff_isUnit.2 (isUnit_of_mem_unitaryGroup (Unitary.star_mem
        h.mem_unitaryGroup_left₂))
    have hX : Function.Injective X.vecMul := vecMul_injective_iff_isUnit.2 h.isUnit
    have hBi : Function.Injective B.vecMul := vecMul_injective_iff.2 hB
    simp only [← vecMul_vecMul] at huv
    exact hU (hBi (hX huv))
  have := congrFun (hinj hrow) k
  simp at this

end Facts

end Matrix
