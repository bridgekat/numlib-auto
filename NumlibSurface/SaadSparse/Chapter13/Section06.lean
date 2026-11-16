/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.SaadSparse.Chapter13.Section05

/-!
# Saad, Section 13.6: Algebraic multigrid

This module formalizes the exact part of Section 13.6.1 of [saad2003iterative]: the description of a
smooth error through the quadratic form of $A$. Algebraic multigrid keeps the Galerkin framework of
Section 13.4. The coarse matrix is still $A_H = I_h^H A_h I_H^h$ (13.66), and the restriction is
still the transpose of the prolongation (13.67). Only the construction of the prolongation changes:
it is algebraic, not geometric. Therefore Lemma 13.1, the relations (13.59)–(13.61) and Theorem 13.3
apply without change, and `NumlibSurface.SaadSparse.Chapter13.Section05` already proves them,
because nothing in that module mentions a mesh.

Section 13.6.1 reads the smoothing property in terms of the matrix entries. If the smoother has
barely reduced an error $s$, the smoothing property (13.62) forces $\|As\|_{D^{-1}} \ll \|s\|_A$,
and the Cauchy–Schwarz inequality in the $D$-inner product turns this into $(As, s) \ll (Ds, s)$,
which is (13.68): a smooth error has a small Rayleigh quotient for $D^{-1/2} A D^{-1/2}$. Then
$As \approx 0$, so the row equation (13.69) $a_{ii} s_i \approx -\sum_{j \ne i} a_{ij} s_j$ holds
approximately. The quadratic form $(As, s)$ expands as a weighted sum of the squared differences
$(s_j - s_i)^2$. For a symmetric matrix with zero row sums and nonpositive off-diagonal entries,
this expansion is the weighted graph-Laplacian identity $(As, s) = \frac{1}{2} \sum_{i,j} |a_{ij}|
(s_j - s_i)^2$. So a smooth error varies slowly along the strong connections, and algebraic
multigrid uses this to choose the coarse space.

## Main results

* Equation (13.68), `SaadSparse.Chapter13.equation_13_68`: for symmetric $A$, $(As, s) = \frac{1}{2}
  \sum_{i,j} (-a_{ij})(s_j - s_i)^2 + \sum_i (\sum_j a_{ij}) s_i^2$.
* Equation (13.68), `SaadSparse.Chapter13.equation_13_68_of_rowSum_zero`: for symmetric $A$ with
  zero row sums and nonpositive off-diagonal entries, $(As, s) = \frac{1}{2} \sum_{i,j} |a_{ij}|
  (s_j - s_i)^2$.
* Equation (13.69), `SaadSparse.Chapter13.equation_13_69`: $(As)_i = 0$ if and only if
  $a_{ii} s_i = -\sum_{j \ne i} a_{ij} s_j$.
* Section 13.6.1, `SaadSparse.Chapter13.equation_13_68_le`: for symmetric positive definite $A$,
  $(As, s) \le \|As\|_{D^{-1}} \|s\|_D$.
* Example 13.9, `SaadSparse.Chapter13.example_13_9`: the interpolation weights on the nine-point
  stencil of Figure 13.10 are nonnegative and add up to one.

## Implementation notes

* The Cauchy–Schwarz step `SaadSparse.Chapter13.equation_13_68_le` is the duality of the two norms,
  `SaadSparse.Chapter13.isDualSeminormPair_normD` of `NumlibSurface.SaadSparse.Chapter13.Section05`.
* The identity of `SaadSparse.Chapter13.equation_13_68_of_rowSum_zero` is the computation of
  Mathlib's `SimpleGraph.lapMatrix_toLinearMap₂'`, with weights in place of the unweighted edges.

## Not formalized

* **The smoothness criterion (13.70).** It comes from an averaging argument that the book does not
  call rigorous: "it cannot be rigorously argued that the bracketed term must be of the order 2ε,
  but one can say that on average this will be true".
* **The interpolation weights (13.72)–(13.74), the C/F splitting of Section 13.6.2, the coarsening
  heuristics of Section 13.6.3 and the multilevel ILU of Section 13.6.4.** These are constructions,
  not theorems. Once a prolongation is chosen, what can be proved about it is Theorem 13.3 with the
  coarse space $\operatorname{Ran}(I_H^h)$.
-/

open Finset Matrix

open scoped SaadSparse

namespace SaadSparse.Chapter13

variable {n : ℕ}

/-- **Equation (13.68)** of [saad2003iterative], the expansion of the quadratic form. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and let $s \in \mathbb{R}^n$. Then
$$(As, s) = \frac{1}{2} \sum_{i,j} (-a_{ij}) (s_j - s_i)^2 + \sum_i \Big(\sum_j a_{ij}\Big)
  s_i^2.$$

The smoothness argument of Section 13.6.1 starts from this expansion. The identity is the
elementary $-a_{ij} ((s_j - s_i)^2 - s_i^2 - s_j^2) = 2 a_{ij} s_i s_j$, summed over all pairs.
The symmetry of $A$ is used once, to replace $\sum_i \sum_j a_{ij} s_j^2$ by
$\sum_i \sum_j a_{ij} s_i^2$. The quadratic form $(As, s)$ is the dot product `(A *ᵥ s) ⬝ᵥ s`. -/
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

/-- **Equation (13.68)** of [saad2003iterative], the model case. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, with zero row sums $\sum_j a_{ij} = 0$ and nonpositive off-diagonal entries
$a_{ij} \le 0$ for $i \ne j$. Then for every $s \in \mathbb{R}^n$
$$(As, s) = \frac{1}{2} \sum_{i,j} |a_{ij}| (s_j - s_i)^2.$$

This is the weighted graph-Laplacian form of the quadratic form. It is the identity behind the
algebraic multigrid reading of smoothness: $(As, s)$ is small exactly when $s$ varies little
across the strong couplings. -/
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

/-- **Equation (13.69)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$,
$s \in \mathbb{R}^n$ and let $i$ be an index. Then the $i$-th component of $As$ vanishes if and
only if
$$a_{ii} s_i = -\sum_{j \ne i} a_{ij} s_j.$$

The book uses the row equation as an approximate identity for a smooth error, where
$(As, s) \approx 0$ forces $As \approx 0$, and it reads an interpolation formula from it. -/
theorem equation_13_69 (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) (i : Fin n) :
    (A *ᵥ s) i = 0 ↔ A i i * s i = -∑ j ∈ Finset.univ.erase i, A i j * s j := by
  rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  constructor <;> intro h <;> linarith

/-- **Section 13.6.1** of [saad2003iterative], the Cauchy–Schwarz step of the smoothness argument.
Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $D$ be its diagonal, and
let $s \in \mathbb{R}^n$. Then
$$(As, s) \le \|As\|_{D^{-1}} \, \|s\|_D.$$

The identity behind it is $(As, s) = (D^{-1/2} A s, D^{1/2} s)$. For a smooth error, the
smoothing property (13.62) makes $\|As\|_{D^{-1}}$ much smaller than $\|s\|_A$, and the
inequality then gives $\|s\|_A \ll \|s\|_D$. This is (13.68): the Rayleigh quotient of
$D^{1/2} s$ for $D^{-1/2} A D^{-1/2}$ is small. The norms are `SaadSparse.Chapter13.normDinv`
and `SaadSparse.Chapter13.normD`. -/
theorem equation_13_68_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (s : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (A ⬝ s) s ≤ normDinv A (A ⬝ s) * normD A s := by
  have h := (isDualSeminormPair_normD hA).norm_inner_le (A ⬝ s) s
  calc inner ℝ (A ⬝ s) s ≤ ‖inner ℝ (A ⬝ s) s‖ := Real.le_norm_self _
    _ ≤ normDinv A (A ⬝ s) * normD A s := h

/-- **Example 13.9** of [saad2003iterative]. For real numbers $s_S, s_N, s_W, s_E$, the
interpolation formula of the example satisfies
$$\frac{1}{18} \Big(4 s_S + 4 s_N + 3 s_W + 3 s_E + 2 \cdot \frac{3 s_N + 4 s_W}{7} + 2 \cdot
  \frac{3 s_N + 4 s_E}{7}\Big) = \frac{4}{18} s_S + \frac{4 + 12/7}{18} s_N + \frac{3 + 8/7}{18}
  s_W + \frac{3 + 8/7}{18} s_E,$$
the four weights $\frac{4}{18}$, $\frac{4 + 12/7}{18}$, $\frac{3 + 8/7}{18}$,
$\frac{3 + 8/7}{18}$ are nonnegative, and they add up to one.

The example evaluates the interpolation formula (13.73) on the nine-point stencil of Figure
13.10. A red-black colouring of the five-point graph makes the centre a fine node, with four
coarse neighbours $S$, $N$, $W$, $E$ and two strongly coupled fine neighbours. The book prints
the result twice, first with the two fine neighbours eliminated separately and then with the
terms collected. It closes with the point of the example: *the weights are all nonnegative and
they add up to one*, as the weights of an interpolation formula must.

The stencil entries $a_{ij}$ are given only in Figure 13.10, which the source text does not
reproduce. Therefore the example is stated at the formula that the text prints, and it is not
derived from (13.73). The formula (13.73) belongs to the construction of Section 13.6.2, which
this module does not formalize. -/
theorem example_13_9 (sS sN sW sE : ℝ) :
    (4 * sS + 4 * sN + 3 * sW + 3 * sE + 2 * ((3 * sN + 4 * sW) / 7)
          + 2 * ((3 * sN + 4 * sE) / 7)) / 18
        = (4 / 18) * sS + ((4 + 12 / 7) / 18) * sN + ((3 + 8 / 7) / 18) * sW
          + ((3 + 8 / 7) / 18) * sE ∧
      0 ≤ (4 : ℝ) / 18 ∧ 0 ≤ ((4 : ℝ) + 12 / 7) / 18 ∧ 0 ≤ ((3 : ℝ) + 8 / 7) / 18 ∧
      (4 : ℝ) / 18 + ((4 : ℝ) + 12 / 7) / 18 + ((3 : ℝ) + 8 / 7) / 18
          + ((3 : ℝ) + 8 / 7) / 18 = 1 :=
  ⟨by ring, by norm_num, by norm_num, by norm_num, by norm_num⟩

end SaadSparse.Chapter13
