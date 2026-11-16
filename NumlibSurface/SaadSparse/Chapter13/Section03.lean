/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.Multigrid.Basic
import Numlib.Multigrid.ModelProblem

/-!
# Saad, Section 13.3: Inter-grid operations

This module formalizes Section 13.3 of [saad2003iterative]: the operators that move a vector between
a fine grid and the coarse grid obtained from it by dropping every other point, in one and two
dimensions. The **prolongation** $I_{2h}^h$ is linear interpolation (13.30), (13.31). The
**restriction** $I_h^{2h}$ is injection (13.32) or full weighting (13.33)–(13.34), (13.38). The
one-dimensional matrices are `Multigrid.linearInterpolation` and `Multigrid.fullWeighting` of
`Numlib.Multigrid.ModelProblem`, and the two-dimensional ones are their Kronecker products.

The main results say that full weighting is a scaled transpose of linear interpolation,
$I_h^{2h} = 2^{-d} (I_{2h}^h)^T$ in dimension $d$ (13.35)–(13.37), and that the two-dimensional
operators act on a product $v \otimes w$ of grid functions one coordinate at a time (13.31),
(13.38). The two-dimensional full-weighting stencil is therefore
$$\tfrac14 [1\ 2\ 1] \otimes \tfrac14 [1\ 2\ 1] = \frac{1}{16} \begin{bmatrix} 1 & 2 & 1 \\ 2 & 4 &
  2 \\ 1 & 2 & 1 \end{bmatrix}.$$
The coarse-grid correction of Section 13.4 does not change when the restriction is replaced by the
adjoint of the prolongation, because the factor $2^d$ cancels.

## Main definitions

* Equation (13.30), `SaadSparse.Chapter13.prolongation1D`: one-dimensional linear interpolation.
* Equation (13.31), `SaadSparse.Chapter13.prolongation2D`: two-dimensional linear interpolation, the
  Kronecker product of two one-dimensional interpolations.
* Equation (13.32), `SaadSparse.Chapter13.injection1D`: one-dimensional restriction by injection.
* Equations (13.33)–(13.34), `SaadSparse.Chapter13.restriction1D`: one-dimensional full weighting.
* Equation (13.38), `SaadSparse.Chapter13.restriction2D`: two-dimensional full weighting, the
  Kronecker product of two one-dimensional full weightings.

## Main results

* Equation (13.31) (Example 13.1), `SaadSparse.Chapter13.equation_13_31`: two-dimensional
  interpolation maps $v \otimes w$ to $(I_{2h}^h v) \otimes (I_{2h}^h w)$.
* Equation (13.35), `SaadSparse.Chapter13.equation_13_35`: in one dimension,
  $I_h^{2h} = \frac12 (I_{2h}^h)^T$.
* Equations (13.36)–(13.37), `SaadSparse.Chapter13.equation_13_37`: in two dimensions,
  $I_h^{2h} = \frac14 (I_{2h}^h)^T$.
* Equation (13.38), `SaadSparse.Chapter13.equation_13_38`: two-dimensional full weighting maps
  $v \otimes w$ to $(I_h^{2h} v) \otimes (I_h^{2h} w)$.
* `SaadSparse.Chapter13.injective_prolongation1D`: linear interpolation is injective, so the
  Galerkin coarse problem of Section 13.4 is well posed.

## Conventions

* The fine grid of the book has $n$ interior points $x_i^h = ih$, $i = 1, \dots, n$, with
  $h = 1/(n + 1)$. The coarse grid keeps every other point, $x_j^{2h} = x_{2j}^h$, so $n$ is odd.
  With $n = 2m + 1$ there are $m$ interior coarse points. The sizes are `2 * m + 1` and `m` by
  construction, so no divisibility hypothesis is needed.
* Interior points are numbered from $0$: a fine index `p : Fin (2 * m + 1)` is the book's
  $i = p + 1$, and a coarse index `q : Fin m` is the book's $j = q + 1$. The coarse point
  $x_j^{2h} = x_{2j}^h$ is therefore the fine point $p = 2q + 1$.
* With this numbering, (13.30) reads $v^h_{2q+1} = v^{2h}_q$ and
  $v^h_{2q} = (v^{2h}_{q-1} + v^{2h}_q)/2$, where a coarse value outside `Fin m` is the boundary
  value $0$. Column $q$ of `SaadSparse.Chapter13.prolongation1D` has the entry $1$ at row $2q + 1$
  and the entry $\frac12$ at rows $2q$ and $2q + 2$: the stencil $\frac12 [1\ 2\ 1]$. Row $q$ of
  `SaadSparse.Chapter13.restriction1D` has the stencil $\frac14 [1\ 2\ 1]$ on the columns $2q$,
  $2q + 1$, $2q + 2$, which is the full weighting (13.34).
* A two-dimensional grid function is a function on a product of index types, and $v \otimes w$ is
  `Matrix.kroneckerVec v w`.

## Implementation notes

* The backbone coarse-grid projector `Multigrid.coarseProjection A hA Pr` of
  `Numlib.Multigrid.Basic` is built from the prolongation alone, with the adjoint $(I_{2h}^h)^*$ as
  its restriction. It depends on the prolongation only through its range. By (13.35) the restriction
  of the book is a positive multiple of this adjoint, so the two give the same coarse-grid
  correction (`SaadSparse.Chapter13.coarseProjection_eq_of_scaled`,
  `SaadSparse.Chapter13.coarseProjection_apply_eq_of_smul`).
-/

open Matrix

open scoped Kronecker Matrix

namespace SaadSparse.Chapter13

/-! ### The one-dimensional inter-grid operators -/

/-- **Equation (13.30)** of [saad2003iterative]. The one-dimensional **linear interpolation**
(prolongation) matrix $I_{2h}^h \in \mathbb{R}^{(2m+1) \times m}$ carries the $m$ interior
coarse values to the $2m + 1$ interior fine values by
$$v^h_{2j} = v^{2h}_j, \qquad v^h_{2j+1} = \tfrac12 \left(v^{2h}_j + v^{2h}_{j+1}\right),$$
with the boundary values $v^{2h}_0 = v^{2h}_{m+1} = 0$.

Indices are $0$-based: column $q$ is the stencil $\frac12 [1\ 2\ 1]$ on the fine rows $2q$,
$2q + 1$, $2q + 2$. The fine point $2q + 1$ is the coarse point $q$ and takes its value, and the
two fine points beside it take the average of their coarse neighbours. For $m = 3$ this is the
$7 \times 3$ matrix that the book displays. The definition is `Multigrid.linearInterpolation m`. -/
noncomputable def prolongation1D (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin m) ℝ :=
  Multigrid.linearInterpolation m

/-- The entries of the interpolation matrix ($0$-based): $(I_{2h}^h)_{ij}$ is $1$ if $i = 2j + 1$,
$\frac12$ if $i = 2j$ or $i = 2j + 2$, and $0$ otherwise. -/
theorem prolongation1D_apply (m : ℕ) (i : Fin (2 * m + 1)) (j : Fin m) :
    prolongation1D m i j =
      if (i : ℕ) = 2 * (j : ℕ) + 1 then 1
      else if (i : ℕ) = 2 * (j : ℕ) then 1 / 2
      else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 2
      else 0 :=
  Multigrid.linearInterpolation_apply i j

/-- **Equation (13.32)** of [saad2003iterative]. The one-dimensional **restriction by injection**
$I_h^{2h} \in \mathbb{R}^{m \times (2m+1)}$ takes the fine value at each coarse point,
$v^{2h}_j = v^h_{2j}$.

With $0$-based indices, row $q$ has the entry $1$ in column $2q + 1$, the fine point that
carries the coarse point $q$, and $0$ elsewhere. -/
def injection1D (m : ℕ) : Matrix (Fin m) (Fin (2 * m + 1)) ℝ :=
  Matrix.of fun j i => if (i : ℕ) = 2 * (j : ℕ) + 1 then 1 else 0

/-- The entries of the injection matrix ($0$-based): $(I_h^{2h})_{ji}$ is $1$ if $i = 2j + 1$, and
$0$ otherwise. -/
theorem injection1D_apply (m : ℕ) (j : Fin m) (i : Fin (2 * m + 1)) :
    injection1D m j i = if (i : ℕ) = 2 * (j : ℕ) + 1 then 1 else 0 :=
  rfl

/-- **Equations (13.33)–(13.34)** of [saad2003iterative]. The one-dimensional **full weighting**
restriction $I_h^{2h} \in \mathbb{R}^{m \times (2m+1)}$ is
$$v^{2h}_j = \tfrac14 \left(v^h_{2j-1} + 2 v^h_{2j} + v^h_{2j+1}\right).$$

With $0$-based indices, row $q$ is the stencil $\frac14 [1\ 2\ 1]$ on the fine columns $2q$,
$2q + 1$, $2q + 2$, and the middle column is the fine point that carries the coarse point $q$.
Unlike interpolation, this needs no boundary convention: the three fine indices are interior for
every `q : Fin m`. The definition is `Multigrid.fullWeighting m`. -/
noncomputable def restriction1D (m : ℕ) : Matrix (Fin m) (Fin (2 * m + 1)) ℝ :=
  Multigrid.fullWeighting m

/-- The entries of the full-weighting matrix ($0$-based): $(I_h^{2h})_{ji}$ is $\frac12$ if
$i = 2j + 1$, $\frac14$ if $i = 2j$ or $i = 2j + 2$, and $0$ otherwise. -/
theorem restriction1D_apply (m : ℕ) (j : Fin m) (i : Fin (2 * m + 1)) :
    restriction1D m j i =
      if (i : ℕ) = 2 * (j : ℕ) + 1 then 1 / 2
      else if (i : ℕ) = 2 * (j : ℕ) then 1 / 4
      else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 4
      else 0 :=
  Multigrid.fullWeighting_apply j i

/-! ### How the one-dimensional operators act -/

/-- If the fine point $p = 2q + 1$ is the coarse point $q$, then the interpolation matrix has the
entry $(I_{2h}^h)_{pq} = 1$. -/
theorem prolongation1D_apply_of_odd (m : ℕ) {p : Fin (2 * m + 1)} {q : Fin m}
    (hp : (p : ℕ) = 2 * (q : ℕ) + 1) : prolongation1D m p q = 1 := by
  rw [prolongation1D_apply, ite_eq_left hp]

/-- If the fine point $p = 2q + 1$ is the coarse point $q$ and $b \neq q$, then
$(I_{2h}^h)_{pb} = 0$. So interpolation is exact at the fine points that are coarse points. -/
theorem prolongation1D_apply_of_odd_of_ne (m : ℕ) {p : Fin (2 * m + 1)} {q b : Fin m}
    (hp : (p : ℕ) = 2 * (q : ℕ) + 1) (hb : b ≠ q) : prolongation1D m p b = 0 := by
  have hbq : (b : ℕ) ≠ (q : ℕ) := fun h => hb (Fin.val_injective h)
  rw [prolongation1D_apply, hp, ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

/-- Linear interpolation is exact at the fine points that are coarse points: for
$u \in \mathbb{R}^m$ and $p = 2q + 1$, $(I_{2h}^h u)_p = u_q$. This is the first half of (13.30)
of [saad2003iterative]. -/
theorem prolongation1D_mulVec_odd (m : ℕ) (u : Fin m → ℝ) (q : Fin m)
    {p : Fin (2 * m + 1)} (hp : (p : ℕ) = 2 * (q : ℕ) + 1) :
    (prolongation1D m *ᵥ u) p = u q := by
  rw [mulVec_apply_eq_sum, Finset.sum_eq_single q]
  · rw [prolongation1D_apply_of_odd m hp, one_mul]
  · intro b _ hb
    rw [prolongation1D_apply_of_odd_of_ne m hp hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ q) h

/-- Restriction by injection reads off the fine value at the coarse point: for
$v \in \mathbb{R}^{2m+1}$ and $p = 2q + 1$, $(I_h^{2h} v)_q = v_p$. This is (13.32) of
[saad2003iterative]. -/
theorem injection1D_mulVec (m : ℕ) (v : Fin (2 * m + 1) → ℝ) (q : Fin m)
    {p : Fin (2 * m + 1)} (hp : (p : ℕ) = 2 * (q : ℕ) + 1) :
    (injection1D m *ᵥ v) q = v p := by
  rw [mulVec_apply_eq_sum, Finset.sum_eq_single p]
  · rw [injection1D_apply, ite_eq_left hp, one_mul]
  · intro b _ hb
    have hbp : (b : ℕ) ≠ (p : ℕ) := fun h => hb (Fin.val_injective h)
    rw [injection1D_apply, ite_eq_right (by omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- Full weighting as an action, (13.34) of [saad2003iterative]: for $v \in \mathbb{R}^{2m+1}$ and
the fine indices $a = 2q$, $b = 2q + 1$, $c = 2q + 2$,
$$(I_h^{2h} v)_q = \tfrac14 (v_a + 2 v_b + v_c).$$
-/
theorem restriction1D_mulVec (m : ℕ) (v : Fin (2 * m + 1) → ℝ) (q : Fin m)
    {a b c : Fin (2 * m + 1)} (ha : (a : ℕ) = 2 * (q : ℕ)) (hb : (b : ℕ) = 2 * (q : ℕ) + 1)
    (hc : (c : ℕ) = 2 * (q : ℕ) + 2) :
    (restriction1D m *ᵥ v) q = (v a + 2 * v b + v c) / 4 := by
  have hab : a ≠ b := fun h => by rw [h, hb] at ha; omega
  have hac : a ≠ c := fun h => by rw [h, hc] at ha; omega
  have hbc : b ≠ c := fun h => by rw [h, hc] at hb; omega
  have hzero : ∀ p ∈ Finset.univ, p ∉ ({a, b, c} : Finset (Fin (2 * m + 1))) →
      restriction1D m q p * v p = 0 := by
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    obtain ⟨hpa, hpb, hpc⟩ := hp
    have h1 : (p : ℕ) ≠ 2 * (q : ℕ) := fun h => hpa (Fin.val_injective (h.trans ha.symm))
    have h2 : (p : ℕ) ≠ 2 * (q : ℕ) + 1 := fun h => hpb (Fin.val_injective (h.trans hb.symm))
    have h3 : (p : ℕ) ≠ 2 * (q : ℕ) + 2 := fun h => hpc (Fin.val_injective (h.trans hc.symm))
    rw [restriction1D_apply, ite_eq_right h2, ite_eq_right h1, ite_eq_right h3, zero_mul]
  rw [mulVec_apply_eq_sum, ← Finset.sum_subset (Finset.subset_univ _) hzero,
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, restriction1D_apply, restriction1D_apply, restriction1D_apply,
    ite_eq_right (by omega), ite_eq_left ha, ite_eq_left hb, ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left hc]
  ring

/-- Restriction by injection is a left inverse of linear interpolation: the product of the injection
matrix and the interpolation matrix is the identity of $\mathbb{R}^{m \times m}$. -/
theorem injection1D_mul_prolongation1D (m : ℕ) : injection1D m * prolongation1D m = 1 := by
  ext q q'
  obtain ⟨p, hp⟩ : ∃ p : Fin (2 * m + 1), (p : ℕ) = 2 * (q : ℕ) + 1 :=
    ⟨⟨2 * (q : ℕ) + 1, by omega⟩, rfl⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · rw [injection1D_apply, ite_eq_left hp, one_mul, prolongation1D_apply, Matrix.one_apply]
    by_cases h : q = q'
    · subst h
      rw [ite_eq_left hp, ite_eq_left rfl]
    · have hne : (q : ℕ) ≠ (q' : ℕ) := fun hv => h (Fin.val_injective hv)
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right h]
  · intro b _ hb
    have hbp : (b : ℕ) ≠ (p : ℕ) := fun hv => hb (Fin.val_injective hv)
    rw [injection1D_apply, ite_eq_right (by omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Linear interpolation $I_{2h}^h$ is injective as a linear map
$\mathbb{R}^m \to \mathbb{R}^{2m+1}$.

This is the hypothesis of `Multigrid.galerkinCoarse_isSymmetricCoercive`, which makes the
Galerkin coarse problem of Section 13.4 well posed. -/
theorem injective_prolongation1D (m : ℕ) :
    Function.Injective (toEuclideanLin (prolongation1D m)) := by
  intro x y h
  have hxy : prolongation1D m *ᵥ WithLp.ofLp x = prolongation1D m *ᵥ WithLp.ofLp y :=
    congrArg WithLp.ofLp h
  have hres := congrArg (fun z => injection1D m *ᵥ z) hxy
  simp only [Matrix.mulVec_mulVec, injection1D_mul_prolongation1D, Matrix.one_mulVec] at hres
  exact WithLp.ofLp_injective 2 hres

/-! ### The transpose relation (13.35) -/

/-- **Equation (13.35)** of [saad2003iterative]. In one dimension, full weighting is the scaled
transpose of linear interpolation:
$$I_h^{2h} = 2^{-d} (I_{2h}^h)^T, \qquad d = 1.$$

Both stencils are $[1\ 2\ 1]$, and the scaling is the only difference between them:
$\frac14 [1\ 2\ 1]$ against $\frac12 [1\ 2\ 1]$. -/
theorem equation_13_35 (m : ℕ) : restriction1D m = (1 / 2 : ℝ) • (prolongation1D m)ᵀ :=
  rfl

/-- Equation (13.35) of [saad2003iterative] with the scaling on the other side: in one dimension,
$I_{2h}^h = 2^d (I_h^{2h})^T$ with $d = 1$. -/
theorem prolongation1D_eq_smul_transpose (m : ℕ) :
    prolongation1D m = (2 : ℝ) • (restriction1D m)ᵀ := by
  rw [equation_13_35, Matrix.transpose_smul, Matrix.transpose_transpose, smul_smul]
  norm_num

/-! ### The two-dimensional operators (13.31) and (13.38) -/

/-- **Equation (13.31)** of [saad2003iterative]. The two-dimensional **linear interpolation** on a
fine grid of $(2m_1 + 1) \times (2m_2 + 1)$ interior points is the Kronecker product
$P_1 \otimes P_2$ of the one-dimensional interpolations
$P_1 \in \mathbb{R}^{(2m_1+1) \times m_1}$ and $P_2 \in \mathbb{R}^{(2m_2+1) \times m_2}$ in the
two coordinate directions.

This is what (13.31) says: the bilinear interpolation weights $1$, $\frac12$, $\frac14$ are the
products of the one-dimensional weights $1$, $\frac12$. The fine grid is indexed by
`Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1)` and the coarse grid by `Fin m₁ × Fin m₂`. -/
noncomputable def prolongation2D (m₁ m₂ : ℕ) :
    Matrix (Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1)) (Fin m₁ × Fin m₂) ℝ :=
  prolongation1D m₁ ⊗ₖ prolongation1D m₂

/-- Each entry of the two-dimensional interpolation matrix is the product of two one-dimensional
entries, one for each coordinate direction: $(I_{2h}^h)_{(i_1, i_2), (j_1, j_2)} =
(I_{2h}^h)_{i_1 j_1} (I_{2h}^h)_{i_2 j_2}$. -/
theorem prolongation2D_apply (m₁ m₂ : ℕ) (i : Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1))
    (j : Fin m₁ × Fin m₂) :
    prolongation2D m₁ m₂ i j = prolongation1D m₁ i.1 j.1 * prolongation1D m₂ i.2 j.2 :=
  rfl

/-- **Equation (13.38)** of [saad2003iterative]. The two-dimensional **full weighting** restriction
is the Kronecker product of the one-dimensional full weightings in the two coordinate
directions.

Its stencil is therefore $\frac14 [1\ 2\ 1] \otimes \frac14 [1\ 2\ 1] = \frac{1}{16}
\begin{bmatrix} 1 & 2 & 1 \\ 2 & 4 & 2 \\ 1 & 2 & 1 \end{bmatrix}$, the display of Section
13.3.2 just before (13.36). -/
noncomputable def restriction2D (m₁ m₂ : ℕ) :
    Matrix (Fin m₁ × Fin m₂) (Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1)) ℝ :=
  restriction1D m₁ ⊗ₖ restriction1D m₂

/-- Each entry of the two-dimensional full-weighting matrix is the product of two one-dimensional
entries: $(I_h^{2h})_{(j_1, j_2), (i_1, i_2)} = (I_h^{2h})_{j_1 i_1} (I_h^{2h})_{j_2 i_2}$. This
gives the stencil $\frac{1}{16} \begin{bmatrix} 1 & 2 & 1 \\ 2 & 4 & 2 \\ 1 & 2 & 1
\end{bmatrix}$ of Section 13.3.2, whose centre $\frac14$, edge $\frac18$ and corner
$\frac{1}{16}$ are $\frac12 \cdot \frac12$, $\frac12 \cdot \frac14$ and $\frac14 \cdot \frac14$. -/
theorem restriction2D_apply (m₁ m₂ : ℕ) (j : Fin m₁ × Fin m₂)
    (i : Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1)) :
    restriction2D m₁ m₂ j i = restriction1D m₁ j.1 i.1 * restriction1D m₂ j.2 i.2 :=
  rfl

/-- **Equation (13.31)** of [saad2003iterative] (Example 13.1). Two-dimensional interpolation is the
tensor product of the one-dimensional interpolations, so it separates the variables: for coarse
grid functions $v \in \mathbb{R}^{m_1}$ and $w \in \mathbb{R}^{m_2}$,
$$I_{2h}^h (v \otimes w) = (I_{2h}^h v) \otimes (I_{2h}^h w).$$

The product $v \otimes w$ is `Matrix.kroneckerVec v w`. -/
theorem equation_13_31 (m₁ m₂ : ℕ) (v : Fin m₁ → ℝ) (w : Fin m₂ → ℝ) :
    prolongation2D m₁ m₂ *ᵥ kroneckerVec v w
      = kroneckerVec (prolongation1D m₁ *ᵥ v) (prolongation1D m₂ *ᵥ w) :=
  kronecker_mulVec _ _ v w

/-- **Equation (13.38)** of [saad2003iterative]. Two-dimensional full weighting is the tensor
product of the one-dimensional full weightings, so it separates the variables: for fine grid
functions $v \in \mathbb{R}^{2m_1+1}$ and $w \in \mathbb{R}^{2m_2+1}$,
$$I_h^{2h} (v \otimes w) = (I_h^{2h} v) \otimes (I_h^{2h} w).$$

The product $v \otimes w$ is `Matrix.kroneckerVec v w`. -/
theorem equation_13_38 (m₁ m₂ : ℕ) (v : Fin (2 * m₁ + 1) → ℝ) (w : Fin (2 * m₂ + 1) → ℝ) :
    restriction2D m₁ m₂ *ᵥ kroneckerVec v w
      = kroneckerVec (restriction1D m₁ *ᵥ v) (restriction1D m₂ *ᵥ w) :=
  kronecker_mulVec _ _ v w

/-- The first line of (13.31) of [saad2003iterative], $v^h_{2i,2j} = v^{2h}_{i,j}$: two-dimensional
interpolation is exact at the fine points that are coarse points. In $0$-based indices: for
every coarse grid function $u$, if $p_1 = 2q_1 + 1$ and $p_2 = 2q_2 + 1$, then
$(I_{2h}^h u)_{(p_1, p_2)} = u_{(q_1, q_2)}$.

This holds for an arbitrary coarse grid function, not only for a product $v \otimes w$. -/
theorem prolongation2D_mulVec_odd (m₁ m₂ : ℕ) (u : Fin m₁ × Fin m₂ → ℝ) (q : Fin m₁ × Fin m₂)
    {p : Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1)} (h₁ : (p.1 : ℕ) = 2 * (q.1 : ℕ) + 1)
    (h₂ : (p.2 : ℕ) = 2 * (q.2 : ℕ) + 1) :
    (prolongation2D m₁ m₂ *ᵥ u) p = u q := by
  rw [mulVec_apply_eq_sum, Fintype.sum_prod_type, Finset.sum_eq_single q.1]
  · rw [Finset.sum_eq_single q.2]
    · rw [prolongation2D_apply, prolongation1D_apply_of_odd m₁ h₁,
        prolongation1D_apply_of_odd m₂ h₂, one_mul, one_mul]
    · intro b _ hb
      rw [prolongation2D_apply, prolongation1D_apply_of_odd_of_ne m₂ h₂ hb, mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ q.2) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [prolongation2D_apply, prolongation1D_apply_of_odd_of_ne m₁ h₁ hb, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ q.1) h

/-- **Equations (13.36)–(13.37)** of [saad2003iterative]. In two dimensions, full weighting is the
scaled transpose of linear interpolation:
$$I_h^{2h} = 2^{-d} (I_{2h}^h)^T = \tfrac14 (I_{2h}^h)^T, \qquad d = 2.$$

The book writes (13.36) for the two-dimensional case and (13.37) for general $d$; this is
(13.37) at $d = 2$. The factor $\frac14$ is the product of the two one-dimensional factors
$\frac12$ of `SaadSparse.Chapter13.equation_13_35`, one for each coordinate direction, which is
why the exponent is the dimension. -/
theorem equation_13_37 (m₁ m₂ : ℕ) :
    restriction2D m₁ m₂ = (1 / 4 : ℝ) • (prolongation2D m₁ m₂)ᵀ := by
  have h₁ : restriction2D m₁ m₂ = restriction1D m₁ ⊗ₖ restriction1D m₂ := rfl
  have h₂ : (prolongation2D m₁ m₂)ᵀ = (prolongation1D m₁)ᵀ ⊗ₖ (prolongation1D m₂)ᵀ :=
    (kroneckerMap_transpose _ _ _).symm
  rw [h₁, h₂, equation_13_35, equation_13_35, smul_kronecker, kronecker_smul, smul_smul]
  norm_num

/-!
### Why the scaling does not matter

The coarse-grid correction of Section 13.4 is built from the pair $(I_{2h}^h, I_h^{2h})$, but the
backbone projector `Multigrid.coarseProjection` is built from the prolongation alone, with the
adjoint $(I_{2h}^h)^*$ as its restriction. By (13.35) the two restrictions differ by the positive
factor $2^d$. The results below show the two ways in which this factor cancels: it does not change
the range of the prolongation, and it multiplies both sides of the coarse equation.
-/

section Backbone

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A nonzero scalar multiple $c \, P$ of a linear map $P$ has the same range as $P$. -/
theorem range_smul_of_ne_zero {c : 𝕜} (hc : c ≠ 0) (Pr : F →ₗ[𝕜] E) :
    LinearMap.range (c • Pr) = LinearMap.range Pr := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨c • x, by simp⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨c⁻¹ • x, ?_⟩
    rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

variable [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive)

/-- The coarse-grid projector depends on the prolongation only through its range: if two
prolongations $P$ and $P'$ have the same range, then they give the same coarse-grid projector
for a symmetric coercive operator $A$. -/
theorem coarseProjection_congr_range {F' : Type*} [NormedAddCommGroup F']
    [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F'] (Pr : F →ₗ[𝕜] E) (Pr' : F' →ₗ[𝕜] E)
    (h : LinearMap.range Pr = LinearMap.range Pr') :
    Multigrid.coarseProjection A hA Pr = Multigrid.coarseProjection A hA Pr' := by
  simp only [Multigrid.coarseProjection, h]

/-- The scaling of (13.35) of [saad2003iterative] cancels. Let $A$ be a symmetric coercive operator
on $E$ and let $P : F \to E$ be a prolongation from a finite-dimensional space $F$. For every
scalar $c \neq 0$, the prolongation $c \, P$ gives the same coarse-grid projector as $P$,
because it has the same range. -/
theorem coarseProjection_eq_of_scaled (Pr : F →ₗ[𝕜] E) {c : 𝕜} (hc : c ≠ 0) :
    Multigrid.coarseProjection A hA (c • Pr) = Multigrid.coarseProjection A hA Pr :=
  coarseProjection_congr_range A hA (c • Pr) Pr (range_smul_of_ne_zero hc Pr)

/-- The same cancellation in the coarse equation. Let $A$ be a symmetric coercive operator on a
finite-dimensional space $E$, let $P : F \to E$ be a prolongation, let $c \neq 0$, and let
$x \in E$ and $y \in F$ satisfy
$$c \, (P^* A P) \, y = c \, P^* (A x).$$
Then the coarse-grid projector $Q$ of $P$ satisfies $Q x = P y$.

The book's coarse equation $A_H y = I_h^{2h} (A x)$, with $I_h^{2h} = c \, P^*$ and
$A_H = c \, P^* A P$, is the backbone coarse equation multiplied by $c$. So it has the same
solutions and gives the same correction. The operator $P^* A P$ is
`Multigrid.galerkinCoarse A Pr`. -/
theorem coarseProjection_apply_eq_of_smul [FiniteDimensional 𝕜 E] (Pr : F →ₗ[𝕜] E) {c : 𝕜}
    (hc : c ≠ 0) {x : E} {y : F}
    (hy : c • Multigrid.galerkinCoarse A Pr y = c • LinearMap.adjoint Pr (A x)) :
    Multigrid.coarseProjection A hA Pr x = Pr y :=
  Multigrid.coarseProjection_apply_eq A hA Pr (smul_right_injective F hc hy)

end Backbone

/-- The adjoint of one-dimensional linear interpolation is twice full weighting:
$(I_{2h}^h)^* = 2^d \, I_h^{2h}$ with $d = 1$, as linear maps between Euclidean spaces. The
restriction that the backbone uses and the restriction that the book uses differ by this factor
only. -/
theorem adjoint_toEuclideanLin_prolongation1D (m : ℕ) :
    LinearMap.adjoint (toEuclideanLin (prolongation1D m))
      = (2 : ℝ) • toEuclideanLin (restriction1D m) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← map_smul]
  congr 1
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial,
    prolongation1D_eq_smul_transpose, Matrix.smul_apply, Matrix.transpose_apply]

end SaadSparse.Chapter13
