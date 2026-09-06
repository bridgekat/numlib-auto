import NumlibSurface.SaadSparse.Chapter13.Section05

/-!
# Saad §13.6: algebraic multigrid

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §13.6: algebraic multigrid, and specifically the exact part of §13.6.1, the characterization
of a smooth error by the quadratic form of `A`.

Algebraic multigrid keeps the Galerkin framework of §13.4 — the coarse matrix is still
`A_H = I_h^H A_h I_H^h` (13.66) and the restriction is still the transpose of the prolongation
(13.67) — and replaces the *geometric* construction of the prolongation by an algebraic one.  Lemma
13.1, the relations (13.59)–(13.61) and Theorem 13.3 apply verbatim, which is what
`NumlibSurface/SaadSparse/Chapter13/Section05.lean` already proves: nothing in that file mentions a
mesh.

What §13.6.1 adds is a reading of the smoothing property in terms of the matrix entries.  If the
smoother has barely reduced an error `s`, the smoothing property (13.62) forces
`‖A s‖_{D⁻¹} ≪ ‖s‖_A`, and Cauchy–Schwarz in the `D`-inner product — `equation_13_68_le` here,
`isDualSeminormPair_normD` of §13.5 — turns that into `(A s, s) ≪ (D s, s)`, Saad's (13.68): a
smooth error has a small Rayleigh quotient for `D^{-1/2} A D^{-1/2}`.  Since `(A s, s) ≈ 0` then
forces `A s ≈ 0`, the row equation (13.69) `a_ii s_i ≈ -∑_{j ≠ i} a_ij s_j` holds approximately,
and the quadratic-form expansion `equation_13_68` rewrites `(A s, s)` as a weighted sum of squared
differences `(s_j - s_i)²`.  For a matrix with zero row sums and nonpositive off-diagonal entries —
the model case — that expansion is the weighted graph-Laplacian identity
`(A s, s) = ½ ∑ |a_ij| (s_j - s_i)²` (`equation_13_68_of_rowSum_zero`), the same computation as
Mathlib's `SimpleGraph.lapMatrix_toLinearMap₂'` in the unweighted case.  Reading it as "the
components of `s` vary slowly along the strong connections" is what AMG uses to choose the coarse
space.

## Not formalized

The rest of §13.6 is heuristic and is not stated here.  The smoothness criterion (13.70) is obtained
by an averaging argument that Saad himself declines to call rigorous — "it cannot be rigorously
argued that the bracketed term must be of the order 2ε, but one can say that on average this will
be true" — and the interpolation weights (13.72)–(13.74), the C/F splitting of §13.6.2, the
coarsening heuristics of §13.6.3 and the multilevel ILU of §13.6.4 are constructions, not theorems:
once an AMG prolongation is chosen, everything provable about it is Theorem 13.3 with the coarse
space `Ran(I_H^h)`.
-/

open Finset Matrix

open scoped SaadSparse

namespace SaadSparse.Chapter13

variable {n : ℕ}

/-- **Saad (13.68)**, the expansion the AMG smoothness argument starts from: for a symmetric matrix,
`(A s, s) = ½ ∑_{i,j} (-a_ij)(s_j - s_i)² + ∑_i (∑_j a_ij) s_i²`.

The identity is the elementary `-a_ij ((s_j - s_i)² - s_i² - s_j²) = 2 a_ij s_i s_j` summed over all
pairs; symmetry enters once, to replace `∑_i ∑_j a_ij s_j²` by `∑_i ∑_j a_ij s_i²`. -/
theorem equation_13_68 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (s : Fin n → ℝ) :
    (A *ᵥ s) ⬝ᵥ s
      = (∑ i, ∑ j, -A i j * (s j - s i) ^ 2) / 2 + ∑ i, (∑ j, A i j) * s i ^ 2 := by
  have hsplit : ∀ f g h : Fin n → Fin n → ℝ,
      ∑ i, ∑ j, (f i j + g i j + h i j)
        = (∑ i, ∑ j, f i j) + (∑ i, ∑ j, g i j) + ∑ i, ∑ j, h i j := by
    intro f g h
    simp only [Finset.sum_add_distrib]
  have hlhs : (A *ᵥ s) ⬝ᵥ s = ∑ i, ∑ j, A i j * s i * s j := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hrow : ∑ i, (∑ j, A i j) * s i ^ 2 = ∑ i, ∑ j, A i j * s i ^ 2 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
  have hswap : ∑ i, ∑ j : Fin n, A i j * s j ^ 2 = ∑ i, ∑ j : Fin n, A i j * s i ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hA.apply j i]
  have hkey : ∑ i, ∑ j : Fin n, (-A i j * (s j - s i) ^ 2)
      = (∑ i, ∑ j : Fin n, 2 * (A i j * s i * s j))
        + (∑ i, ∑ j : Fin n, -(A i j * s i ^ 2)) + ∑ i, ∑ j : Fin n, -(A i j * s j ^ 2) := by
    rw [← hsplit]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hneg : ∀ f : Fin n → Fin n → ℝ,
      ∑ i, ∑ j : Fin n, -f i j = -∑ i, ∑ j : Fin n, f i j := by
    intro f
    simp only [Finset.sum_neg_distrib]
  have hmul : ∑ i, ∑ j : Fin n, 2 * (A i j * s i * s j)
      = 2 * ∑ i, ∑ j : Fin n, A i j * s i * s j := by
    simp only [← Finset.mul_sum]
  rw [hlhs, hrow, hkey, hneg, hneg, hmul, hswap]
  ring

/-- **Saad (13.68)** in the model case: for a symmetric matrix with zero row sums and nonpositive
off-diagonal entries, the quadratic form is the weighted graph-Laplacian one,
`(A s, s) = ½ ∑_{i,j} |a_ij| (s_j - s_i)²`.  This is the identity behind the AMG reading of
smoothness: `(A s, s)` is small exactly when `s` varies little across the strong couplings. -/
theorem equation_13_68_of_rowSum_zero {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hrow : ∀ i, ∑ j, A i j = 0) (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (s : Fin n → ℝ) :
    (A *ᵥ s) ⬝ᵥ s = (∑ i, ∑ j, |A i j| * (s j - s i) ^ 2) / 2 := by
  rw [equation_13_68 hA s]
  have hzero : ∑ i, (∑ j, A i j) * s i ^ 2 = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hrow i, zero_mul]
  have habs : ∑ i, ∑ j : Fin n, -A i j * (s j - s i) ^ 2
      = ∑ i, ∑ j : Fin n, |A i j| * (s j - s i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases eq_or_ne i j with rfl | hij
    · rw [sub_self]
      ring
    · rw [abs_of_nonpos (hoff i j hij)]
  rw [hzero, habs, add_zero]

/-- **Saad (13.69)**: the row equation `a_ii s_i = -∑_{j ≠ i} a_ij s_j`, which says that the `i`-th
component of the residual vanishes.  Saad uses it as an approximate identity for a smooth error,
`(A s, s) ≈ 0` forcing `A s ≈ 0`, and reads an interpolation formula off it. -/
theorem equation_13_69 (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) (i : Fin n) :
    (A *ᵥ s) i = 0 ↔ A i i * s i = -∑ j ∈ Finset.univ.erase i, A i j * s j := by
  rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  constructor <;> intro h <;> linarith

/-- **Saad §13.6.1**: the Cauchy–Schwarz step of the smoothness argument,
`(A s, s) ≤ ‖A s‖_{D⁻¹} ‖s‖_D`.  Written out, `(A s, s) = (D^{-1/2} A s, D^{1/2} s)`, so a smooth
error — one for which the smoothing property (13.62) leaves `‖A s‖_{D⁻¹}` far below `‖s‖_A` — has
`‖s‖_A ≪ ‖s‖_D`, which is Saad (13.68): the Rayleigh quotient of `D^{1/2} s` for
`D^{-1/2} A D^{-1/2}` is small. -/
theorem equation_13_68_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (s : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (A ⬝ s) s ≤ normDinv A (A ⬝ s) * normD A s := by
  have h := (isDualSeminormPair_normD hA).norm_inner_le (A ⬝ s) s
  calc inner ℝ (A ⬝ s) s ≤ ‖inner ℝ (A ⬝ s) s‖ := Real.le_norm_self _
    _ ≤ normDinv A (A ⬝ s) * normD A s := h

end SaadSparse.Chapter13
