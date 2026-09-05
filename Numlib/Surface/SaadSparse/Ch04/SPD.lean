import Numlib.Surface.SaadSparse.Ch04.Convergence

/-!
# §4.2.4–§4.2.5 Symmetric positive definite matrices and Young's theory

Sections 4.2.4 and 4.2.5 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*,
2nd edition, SIAM, 2003.

Only Proposition 4.12 is proved here, by the similarity argument the book uses: for a
block anti-diagonal `B` the spectrum is symmetric under negation, and the spectrum of
`B(α) = α L + α⁻¹ U` does not depend on `α ≠ 0`.

Everything else in these two sections waits on phase 2 of the backbone
(`tracker/backbone.md` §2.3.5, `tracker/saadsparse-ch1-4-5.md` §3 item 5):

* Theorem 4.10 (SOR converges for `0 < ω < 2` iff `A` is positive definite): the
  Householder–John / Ostrowski–Reich criterion `M + Mᴴ - A` coercive ⇒ `ρ(M⁻¹N) < 1`, and its
  converse.
* Definition 4.11/4.13 (Property A, consistent ordering, T-matrices) and Propositions 4.14–4.15.
* Theorem 4.16 (the relation `(λ + ω - 1)² = λ ω² μ²` between the SOR and Jacobi spectra) and the
  optimal parameter (4.47).
-/

open Matrix

namespace SaadSparse.Ch04

/-- The index type of a two-block partition. -/
local notation "I" n₁ ", " n₂ => Fin n₁ ⊕ Fin n₂

variable {n₁ n₂ : ℕ}

/-- Saad, Proposition 4.12: the block anti-diagonal matrix `B = [[0, B₁₂], [B₂₁, 0]]`. -/
def antiDiag (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ) :
    Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 0 B₁₂ B₂₁ 0

/-- The strictly lower block of `B`. -/
def antiDiagL (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 0 0 B₂₁ 0

/-- The strictly upper block of `B`. -/
def antiDiagU (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 0 B₁₂ 0 0

/-- `B = L + U`: a block anti-diagonal matrix is the sum of its strictly lower and strictly upper
blocks, so the family `B(α) = α L + α⁻¹ U` of `proposition_4_12_alpha` passes through `B` at `α = 1`. -/
theorem antiDiag_eq_add (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ) :
    antiDiag B₁₂ B₂₁ = antiDiagL B₂₁ + antiDiagU B₁₂ := by
  rw [antiDiag, antiDiagL, antiDiagU, fromBlocks_add]
  simp

/-- The sign-flip similarity `diag(I, -I)`, an involution. -/
private def signFlip (n₁ n₂ : ℕ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ := fromBlocks 1 0 0 (-1)

private theorem signFlip_mul_self (n₁ n₂ : ℕ) : signFlip n₁ n₂ * signFlip n₁ n₂ = 1 := by
  rw [signFlip, fromBlocks_multiply]
  simp [← fromBlocks_one]

/-- `diag(I, -I)` as a unit. -/
private def signFlipUnit (n₁ n₂ : ℕ) : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ where
  val := signFlip n₁ n₂
  inv := signFlip n₁ n₂
  val_inv := signFlip_mul_self n₁ n₂
  inv_val := signFlip_mul_self n₁ n₂

/-- Saad, Proposition 4.12 (1): the spectrum of a block anti-diagonal matrix is symmetric under
negation. -/
theorem proposition_4_12_neg (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (antiDiag B₁₂ B₂₁)) :
    -μ ∈ spectrum ℂ (antiDiag B₁₂ B₂₁) := by
  have hconj : ((signFlipUnit n₁ n₂ : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ) * antiDiag B₁₂ B₂₁ *
      (((signFlipUnit n₁ n₂)⁻¹ : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ) = -antiDiag B₁₂ B₂₁ := by
    change signFlip n₁ n₂ * antiDiag B₁₂ B₂₁ * signFlip n₁ n₂ = _
    rw [signFlip, antiDiag, fromBlocks_multiply, fromBlocks_multiply]
    simp [fromBlocks_neg]
  have hspec : spectrum ℂ (-antiDiag B₁₂ B₂₁) = spectrum ℂ (antiDiag B₁₂ B₂₁) := by
    rw [← hconj]
    exact spectrum.units_conjugate
  have hneg : -spectrum ℂ (antiDiag B₁₂ B₂₁) = spectrum ℂ (antiDiag B₁₂ B₂₁) := by
    rw [spectrum.neg_eq, hspec]
  rw [← hneg, Set.mem_neg, neg_neg]
  exact hμ

/-- The scaling similarity `diag(I, α I)`. -/
private def scaleBlock (n₁ n₂ : ℕ) (α : ℂ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 1 0 0 (α • 1)

private theorem scaleBlock_mul_inv (n₁ n₂ : ℕ) {α : ℂ} (hα : α ≠ 0) :
    scaleBlock n₁ n₂ α * scaleBlock n₁ n₂ α⁻¹ = 1 := by
  rw [scaleBlock, scaleBlock, fromBlocks_multiply]
  simp [smul_smul, inv_mul_cancel₀ hα, ← fromBlocks_one]

/-- `diag(I, α I)` as a unit, for `α ≠ 0`. -/
private noncomputable def scaleBlockUnit (n₁ n₂ : ℕ) {α : ℂ} (hα : α ≠ 0) :
    (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ where
  val := scaleBlock n₁ n₂ α
  inv := scaleBlock n₁ n₂ α⁻¹
  val_inv := scaleBlock_mul_inv n₁ n₂ hα
  inv_val := by
    have h := scaleBlock_mul_inv n₁ n₂ (α := α⁻¹) (inv_ne_zero hα)
    rwa [inv_inv] at h

/-- Saad, Proposition 4.12 (2): the eigenvalues of `B(α) = α L + α⁻¹ U` do not depend on
`α ≠ 0`. -/
theorem proposition_4_12_alpha (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ)
    {α : ℂ} (hα : α ≠ 0) :
    spectrum ℂ (α • antiDiagL B₂₁ + α⁻¹ • antiDiagU B₁₂) =
      spectrum ℂ (antiDiag B₁₂ B₂₁) := by
  have hconj : ((scaleBlockUnit n₁ n₂ hα : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ) * antiDiag B₁₂ B₂₁ *
      (((scaleBlockUnit n₁ n₂ hα)⁻¹ : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ)
      = α • antiDiagL B₂₁ + α⁻¹ • antiDiagU B₁₂ := by
    change scaleBlock n₁ n₂ α * antiDiag B₁₂ B₂₁ * scaleBlock n₁ n₂ α⁻¹ = _
    rw [scaleBlock, scaleBlock, antiDiag, antiDiagL, antiDiagU, fromBlocks_multiply,
      fromBlocks_multiply, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
    simp [Matrix.smul_mul, Matrix.mul_smul]
  rw [← hconj]
  exact spectrum.units_conjugate

end SaadSparse.Ch04
