/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 2.5: The finite volume method

This module formalizes §2.5 of [saad2003iterative], the cell-centred finite volume discretization of
a conservation law, and the one structural claim that the section makes about it. The semi-discrete
operator (2.54)–(2.55) for the linear flux $\vec F = \vec\lambda u$ has nonnegative diagonal
entries, nonpositive off-diagonal entries and zero row sums. Hence it is a Z-matrix that is weakly
diagonally dominant by rows.

The claim rests on the identity $\sum_j \vec s_j = 0$ for the outward edge vectors of a polygon
(Problem P-2.12), and on the upwind identity (2.53) for the positive and negative parts. Everything
here is plane linear algebra. The section discretizes in space only, so it forms no linear system;
what it produces is the operator `SaadSparse.Chapter02.equation_2_55`.

## Main definitions

* §2.5, `SaadSparse.Chapter02.edgeVec`: the outward edge vector $\vec s_j$ of a closed polygon.
* Equations (2.54)–(2.55), `SaadSparse.Chapter02.equation_2_55`: the semi-discrete finite volume
  operator.

## Main results

* Problem P-2.12, `SaadSparse.Chapter02.sum_edgeVec_eq_zero`: the outward edge vectors of a closed
  polygon sum to zero.
* Equation (2.53), `SaadSparse.Chapter02.posPart_add_negPart` and
  `SaadSparse.Chapter02.equation_2_53`: $z^+ + z^- = z$, and the upwind edge value $\frac{a + b}{2}
  z - \frac{|z|}{2}(b - a) = a z^+ + b z^-$.
* Equations (2.54)–(2.55), `SaadSparse.Chapter02.equation_2_55_apply_self` and
  `SaadSparse.Chapter02.equation_2_55_apply_ne`: the diagonal and the off-diagonal entries of the
  operator.
* §2.5, `SaadSparse.Chapter02.equation_2_55_isDiagDominant`: the operator has nonnegative diagonal,
  nonpositive off-diagonal entries and zero row sums, and is weakly diagonally dominant by rows.

## Conventions

* Vectors of the plane are `Fin 2 → ℝ`, so that the product $\vec\lambda \cdot \vec s$ of the source
  is Mathlib's `dotProduct`.
* The positive and negative parts of the source, $z^+ = (z + |z|)/2$ and $z^- = (z - |z|)/2$, are
  `max z 0` and `min z 0`. The negative part is nonpositive, unlike Mathlib's `negPart`.

## Deviations from the source

* **Equation (2.53)** (reading). The declaration gives the flux obtained after multiplying the
  edge value by the normal flux coefficient. See `SaadSparse.Chapter02.equation_2_53`.
* **Problem P-2.12** (generalization). The sum vanishes for any finite cyclic list of vertices.
  See `SaadSparse.Chapter02.sum_edgeVec_eq_zero`.
* **Equations (2.54)–(2.55)** (generalization). The operator sums the contributions of all edges
  with the same neighbour. See `SaadSparse.Chapter02.equation_2_55_apply_ne`.
* **§2.5, weak diagonal dominance** (generalization). The theorem uses abstract edge vectors
  summing to zero and a neighbour map with no self-neighbours. See
  `SaadSparse.Chapter02.equation_2_55_isDiagDominant`.

## Not formalized

* **The derivation of the scheme: the conservation law (2.48), its weak form, the cell integration
  (2.49) and the cell-averaging approximations (2.50)–(2.51).** The cell integration is the
  divergence theorem on a cell, and the source calls the approximations crude and states no error
  bound for them.
-/

open Finset Matrix

namespace SaadSparse.Chapter02

/-! ### The outward edge vectors of a polygon -/

section Polygon

variable {m : ℕ} [NeZero m]

/-- **Section 2.5** of [saad2003iterative], Figure 2.10, the outward edge vector. Let
$p_0, \dots, p_{m-1}$ be the vertices of a closed polygon in the plane, with the indices taken
modulo $m$. The edge vector $\vec s_j = s_j \vec n_j$ is the edge $p_{j+1} - p_j$ rotated by a
quarter turn:
$$\vec s_j = \big( (p_{j+1})_2 - (p_j)_2, \; (p_j)_1 - (p_{j+1})_1 \big).$$
Its length is the length of the edge, and its direction is the outward normal when the vertices
run counterclockwise.

The number of vertices is $m \ge 1$ (`NeZero m`), and `j + 1` is the successor in `Fin m`, which
wraps around. The Lean coordinates are 0-based, so `p j 0` is $(p_j)_1$. -/
def edgeVec (p : Fin m → Fin 2 → ℝ) (j : Fin m) : Fin 2 → ℝ :=
  ![p (j + 1) 1 - p j 1, p j 0 - p (j + 1) 0]

/-- The first coordinate of the edge vector is $(p_{j+1})_2 - (p_j)_2$. -/
@[simp]
theorem edgeVec_zero (p : Fin m → Fin 2 → ℝ) (j : Fin m) :
    edgeVec p j 0 = p (j + 1) 1 - p j 1 := rfl

/-- The second coordinate of the edge vector is $(p_j)_1 - (p_{j+1})_1$. -/
@[simp]
theorem edgeVec_one (p : Fin m → Fin 2 → ℝ) (j : Fin m) :
    edgeVec p j 1 = p j 0 - p (j + 1) 0 := rfl

/-- For every function $f$ on the indices $0, \dots, m - 1$, $\sum_j f(j + 1) = \sum_j f(j)$ with
$j + 1$ taken modulo $m$, because the cyclic successor is a permutation. This is why the edges
of a closed polygon telescope. -/
theorem sum_succ_eq_sum (f : Fin m → ℝ) : ∑ j, f (j + 1) = ∑ j, f j :=
  Fintype.sum_equiv (Equiv.addRight (1 : Fin m)) _ _ fun _ => rfl

/-- **Problem P-2.12** of [saad2003iterative]: the outward edge vectors of a closed polygon sum to
zero. For every $m \ge 1$ and all vertices $p_0, \dots, p_{m-1}$ in the plane,
$$\sum_{j=0}^{m-1} \vec s_j = 0.$$

**Generalization.** The exercise uses the outward edge vectors of a polygon. The theorem takes
an arbitrary cyclic list of vertices. The edge differences telescope and the quarter turn is
linear. -/
theorem sum_edgeVec_eq_zero (p : Fin m → Fin 2 → ℝ) : ∑ j, edgeVec p j = 0 := by
  have key : ∀ f : Fin m → ℝ, ∑ j, (f (j + 1) - f j) = 0 := fun f => by
    rw [Finset.sum_sub_distrib, sum_succ_eq_sum, sub_self]
  have key' : ∀ f : Fin m → ℝ, ∑ j, (f j - f (j + 1)) = 0 := fun f => by
    rw [Finset.sum_sub_distrib, sum_succ_eq_sum, sub_self]
  ext i
  rw [Finset.sum_apply, Pi.zero_apply]
  fin_cases i
  · simpa [edgeVec] using key fun j => p j 1
  · simpa [edgeVec] using key' fun j => p j 0

end Polygon

/-!
### Positive and negative parts in the sign convention of the source

The positive and negative parts of the source, $z^+ = (z + |z|)/2$ and $z^- = (z - |z|)/2$, are
`max z 0` and `min z 0`, by `SaadSparse.max_zero_eq_half` and `SaadSparse.min_zero_eq_half` of
`NumlibSurface.SaadSparse.Common`. The upwind scheme (2.22)–(2.23) of §2.2.4 uses them first, in
`SaadSparse.Chapter02.equation_2_23`. The negative part of the source is nonpositive, unlike
Mathlib's `negPart`, which is `max (-z) 0`.
-/

/-- **Equation (2.53)** of [saad2003iterative]: every $z \in \mathbb{R}$ is the sum of its positive
and negative parts, $z^+ + z^- = z$. -/
theorem posPart_add_negPart (z : ℝ) : max z 0 + min z 0 = z := by
  rw [max_zero_eq_half, min_zero_eq_half]; ring

/-- **Equation (2.53)** of [saad2003iterative], the upwind edge flux. For all
$a, b, z \in \mathbb{R}$,
$$\frac{a + b}{2} z - \frac{|z|}{2} (b - a) = a z^+ + b z^-.$$
So the average flux $\frac{a + b}{2} z$, corrected by the upwind term $\frac{|z|}{2}(b - a)$, is
$a z^+ + b z^-$. This identity produces the coefficients (2.54)–(2.55) from the flux balance.

**Reading.** Equation (2.53) gives the edge state. The declaration is its product with the
normal flux coefficient $z$, as used in the next display. It gives zero flux when $z=0$.

At $a = b = 1$ it is `SaadSparse.Chapter02.posPart_add_negPart`. -/
theorem equation_2_53 (a b z : ℝ) :
    (a + b) / 2 * z - |z| / 2 * (b - a) = a * max z 0 + b * min z 0 := by
  rw [max_zero_eq_half, min_zero_eq_half]; ring

/-! ### The semi-discrete finite volume operator (2.54)–(2.55) -/

section Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {lam : Fin 2 → ℝ} {s : (i : ι) → κ i → Fin 2 → ℝ} {nb : (i : ι) → κ i → ι}

/-- **Equations (2.54)–(2.55)** of [saad2003iterative], the semi-discrete finite volume operator for
the linear flux $\vec F = \vec\lambda u$. Let the cells be indexed by a finite set, let the
edges of cell $i$ be indexed by a finite set $\kappa_i$, and let edge $k$ of cell $i$ have the
outward edge vector $\vec s_{ik}$ and lead to the neighbour cell $\nu(i, k)$. The operator is
the matrix with entries
$$a_{ij} = \delta_{ij} \beta_i + \sum_{k \,:\, \nu(i, k) = j} (\vec\lambda \cdot \vec s_{ik})^-,
  \qquad \beta_i = \sum_{k \in \kappa_i} (\vec\lambda \cdot \vec s_{ik})^+.$$
So the diagonal entry is $\beta_i$ when no edge leads back to cell $i$, and the entry at a
neighbour $j$ collects $\alpha_{ij} = (\vec\lambda \cdot \vec s_{ik})^-$ over the edges $k$ that
lead to $j$.

**Generalization.** The source gives one edge contribution for each neighbour. The declaration
allows several edges to lead to the same cell and adds their contributions.

In Lean, `lam` and `nb` are the vector $\vec\lambda$ and the neighbour map $\nu$. The geometry
enters only through the hypothesis $\sum_k \vec s_{ik} = 0$ of
`SaadSparse.Chapter02.equation_2_55_isDiagDominant`, which
`SaadSparse.Chapter02.sum_edgeVec_eq_zero` supplies for polygonal cells. -/
def equation_2_55 (lam : Fin 2 → ℝ) (s : (i : ι) → κ i → Fin 2 → ℝ) (nb : (i : ι) → κ i → ι) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    (if i = j then ∑ k, max (lam ⬝ᵥ s i k) 0 else 0) +
      ∑ k with nb i k = j, min (lam ⬝ᵥ s i k) 0

omit [Fintype ι] in
/-- **Equation (2.54)** of [saad2003iterative], the diagonal entry. If no edge of any cell leads
back to the cell itself, then the diagonal entry of the finite volume operator is $a_{ii} =
\beta_i = \sum_k (\vec\lambda \cdot \vec s_{ik})^+$. -/
theorem equation_2_55_apply_self (hnb : ∀ i k, nb i k ≠ i) (i : ι) :
    equation_2_55 lam s nb i i = ∑ k, max (lam ⬝ᵥ s i k) 0 := by
  have h : (univ.filter fun k => nb i k = i) = ∅ :=
    filter_eq_empty_iff.mpr fun k _ => hnb i k
  simp [equation_2_55, h]

omit [Fintype ι] in
/-- **Equation (2.55)** of [saad2003iterative], the off-diagonal entry. For cells $i \neq j$, the
entry of the finite volume operator is the sum of the negative parts over the edges of cell $i$
that lead to cell $j$:
$$a_{ij} = \sum_{k \,:\, \nu(i, k) = j} (\vec\lambda \cdot \vec s_{ik})^-.$$

**Generalization.** Equation (2.55) gives a single contribution. Several edges with the same
neighbour contribute to the same entry, so the statement sums them. -/
theorem equation_2_55_apply_ne {i j : ι} (hij : i ≠ j) :
    equation_2_55 lam s nb i j = ∑ k with nb i k = j, min (lam ⬝ᵥ s i k) 0 := by
  simp [equation_2_55, hij]

/-- The row sums of the finite volume operator are $\sum_j a_{ij} = \vec\lambda \cdot \sum_k \vec
s_{ik}$, because the positive and the negative part of each edge recombine by
`SaadSparse.Chapter02.posPart_add_negPart`. -/
theorem sum_equation_2_55 (i : ι) :
    ∑ j, equation_2_55 lam s nb i j = lam ⬝ᵥ ∑ k, s i k := by
  have hdiag : ∑ j, (if i = j then ∑ k, max (lam ⬝ᵥ s i k) 0 else 0) =
      ∑ k, max (lam ⬝ᵥ s i k) 0 := by simp
  have hoff : ∑ j, ∑ k with nb i k = j, min (lam ⬝ᵥ s i k) 0 =
      ∑ k, min (lam ⬝ᵥ s i k) 0 := Finset.sum_fiberwise _ _ _
  calc ∑ j, equation_2_55 lam s nb i j
      = (∑ k, max (lam ⬝ᵥ s i k) 0) + ∑ k, min (lam ⬝ᵥ s i k) 0 := by
        simp only [equation_2_55, Matrix.of_apply, Finset.sum_add_distrib, hdiag, hoff]
    _ = ∑ k, (lam ⬝ᵥ s i k) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => posPart_add_negPart _
    _ = lam ⬝ᵥ ∑ k, s i k := (dotProduct_sum _ _ _).symm

/-- **Section 2.5** of [saad2003iterative], the structural claim of the section. Suppose that no
edge of a cell leads back to the cell itself, and that the outward edge vectors of each cell sum
to zero, $\sum_k \vec s_{ik} = 0$. Then the finite volume operator (2.54)–(2.55) has nonnegative
diagonal entries, nonpositive off-diagonal entries and zero row sums, and it is weakly
diagonally dominant by rows:
$$a_{ii} \ge 0, \qquad a_{ij} \le 0 \quad (i \neq j), \qquad \sum_j a_{ij} = 0, \qquad \sum_{j
  \neq i} |a_{ij}| \le |a_{ii}|.$$
So it is a Z-matrix with "the same desirable property of weak diagonal dominance seen in the
one-dimensional case".

**Generalization.** The source uses polygonal cells. The theorem assumes the two geometric
facts needed by the calculation directly, so it applies to abstract edge and neighbour data.

For polygonal cells, the hypothesis on the edge vectors is
`SaadSparse.Chapter02.sum_edgeVec_eq_zero`. -/
theorem equation_2_55_isDiagDominant (hnb : ∀ i k, nb i k ≠ i) (hs : ∀ i, ∑ k, s i k = 0) :
    (∀ i, 0 ≤ equation_2_55 lam s nb i i) ∧
      (∀ i j, i ≠ j → equation_2_55 lam s nb i j ≤ 0) ∧
      (∀ i, ∑ j, equation_2_55 lam s nb i j = 0) ∧
      ∀ i, ∑ j ∈ univ.erase i, |equation_2_55 lam s nb i j| ≤
        |equation_2_55 lam s nb i i| := by
  have hrow : ∀ i, ∑ j, equation_2_55 lam s nb i j = 0 := fun i => by
    rw [sum_equation_2_55 i, hs i, dotProduct_zero]
  have hdiag : ∀ i, 0 ≤ equation_2_55 lam s nb i i := fun i => by
    rw [equation_2_55_apply_self hnb i]
    exact Finset.sum_nonneg fun k _ => le_max_right _ _
  have hoff : ∀ i j, i ≠ j → equation_2_55 lam s nb i j ≤ 0 := fun i j hij => by
    rw [equation_2_55_apply_ne hij]
    exact Finset.sum_nonpos fun k _ => min_le_right _ _
  refine ⟨hdiag, hoff, hrow, fun i => ?_⟩
  have habs : ∑ j ∈ univ.erase i, |equation_2_55 lam s nb i j| =
      -∑ j ∈ univ.erase i, equation_2_55 lam s nb i j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj =>
      abs_of_nonpos (hoff i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  have hsplit :
      equation_2_55 lam s nb i i + ∑ j ∈ univ.erase i, equation_2_55 lam s nb i j = 0 := by
    have h := hrow i
    rwa [← Finset.add_sum_erase _ _ (mem_univ i)] at h
  rw [habs, abs_of_nonneg (hdiag i)]
  linarith

end Operator

end SaadSparse.Chapter02
