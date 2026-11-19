/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Numlib.Analysis.Calculus.TaylorSegment
import Numlib.Approximation.MvPolynomial
import Numlib.Approximation.NodalInterpolation
import Numlib.Approximation.Unisolvent
import Numlib.Geometry.Triangulation
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 8.5: Extension to the two-dimensional case

This module formalizes Section 8.5 of [quarteroni2000numerical], which extends polynomial
interpolation to functions of two variables. Section 8.5.1 interpolates on a rectangular grid of
nodes $(x_i, y_j)$ by the tensor-product interpolant $\Pi_{n,m} f(x, y) = \sum_{i=0}^n \sum_{j=0}^m
f(x_i, y_j) l_i(x) l_j(y)$, and Remark 8.1 shows that interpolation by the bilinear polynomials
$a_3 xy + a_2 x + a_1 y + a_0$ at four arbitrary nodes need not be unisolvent. Section 8.5.2
interpolates piecewise on a triangulation. Each triangle $T$ with vertices $a_1, a_2, a_3$ is the
image of the reference triangle $\hat T$ with vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ under the affine
map $F_T(\hat x) = B_T \hat x + b_T$ of (8.34). The space $\mathbb{P}_k$ of polynomials of total
degree at most $k$ in two variables has dimension $d_k = (k+1)(k+2)/2$ (8.35). The element
interpolant $\Pi_T^k f$ is the reference interpolant read through $F_T$ (8.38), and it satisfies the
error bound $\|f - \Pi_T^k f\|_{\infty,T} \le C h_T^{k+1} \|f^{(k+1)}\|_{\infty,T}$ (8.39). The
piecewise interpolant $\Pi_h^k f$ on a triangulation with mesh size $h$ satisfies the global bound
$\|f - \Pi_h^k f\|_{\infty,\Omega} \le C h^{k+1} \|f^{(k+1)}\|_{\infty,\Omega}$ (8.40).

The algebra comes from the backbone modules `Numlib.Approximation.NodalInterpolation` (the nodal
interpolation operator `Approximation.nodalInterp`, the nodal bases `Approximation.IsNodalBasis`,
and the change of variables `Approximation.nodalInterp_comp`), `Numlib.Approximation.Unisolvent`
(`Approximation.IsUnisolvent`) and `Numlib.Approximation.MvPolynomial` (`Approximation.mvPolyLE` and
`Approximation.finrank_mvPolyLE`). The analysis behind (8.39) is Taylor's theorem along a segment
with the Lagrange bound, from `Numlib.Analysis.Calculus.TaylorSegment`. The triangulations of (8.40)
are `Triangulation` of `Numlib.Geometry.Triangulation`.

## Main definitions

* Section 8.5.1, `QuarteroniSaccoSaleri.Chapter08.tensorProductInterp`: the tensor-product
  interpolant $\Pi_{n,m} f$ on the grid $(x_i, y_j)$.
* Remark 8.1, `QuarteroniSaccoSaleri.Chapter08.remark_8_1_space`: the bilinear polynomials
  $a_3 xy + a_2 x + a_1 y + a_0$ on the square $[-1, 1]^2$.
* Remark 8.1, `QuarteroniSaccoSaleri.Chapter08.remark_8_1_node`: the four nodes $(-1, 0)$,
  $(0, -1)$, $(1, 0)$, $(0, 1)$.
* (8.34), `QuarteroniSaccoSaleri.Chapter08.equation_8_34`: the affine map
  $F_T(\hat x) = B_T \hat x + b_T$ from the reference triangle onto the triangle with vertices
  $a_1, a_2, a_3$.
* (8.34), `QuarteroniSaccoSaleri.Chapter08.equation_8_34_matrix`: the matrix
  $B_T = [a_2 - a_1 \mid a_3 - a_1]$.
* Section 8.5.2, `QuarteroniSaccoSaleri.Chapter08.referenceTriangle`: the closed reference triangle
  $\hat T$.
* Section 8.5.2, `QuarteroniSaccoSaleri.Chapter08.linearNodes` and
  `QuarteroniSaccoSaleri.Chapter08.linearShape`: for $k = 1$, the vertices of $\hat T$ and the
  barycentric coordinates.

## Main results

* Section 8.5.1, `QuarteroniSaccoSaleri.Chapter08.tensorProductInterp_isNodalBasis`: for distinct
  nodes, the products $l_i(x) l_j(y)$ are a nodal basis for the grid.
* Section 8.5.1, `QuarteroniSaccoSaleri.Chapter08.tensorProductInterp_apply_node`:
  $\Pi_{n,m} f(x_i, y_j) = f(x_i, y_j)$.
* Section 8.5.1, `QuarteroniSaccoSaleri.Chapter08.tensorProductInterp_mem_span`: $\Pi_{n,m} f$ is a
  polynomial of degree at most $n$ in $x$ and at most $m$ in $y$.
* Remark 8.1, `QuarteroniSaccoSaleri.Chapter08.remark_8_1_apply_node`: the product $xy$ vanishes at
  the four nodes.
* Remark 8.1, `QuarteroniSaccoSaleri.Chapter08.remark_8_1`: the bilinear interpolation problem at
  the four nodes is not unisolvent.
* (8.34), `QuarteroniSaccoSaleri.Chapter08.equation_8_34_vertex`: $F_T$ maps the vertices of
  $\hat T$ to $a_1, a_2, a_3$.
* (8.34), `QuarteroniSaccoSaleri.Chapter08.equation_8_34_bijective`: $F_T$ is a bijection if and
  only if $\det B_T \neq 0$.
* (8.35), `QuarteroniSaccoSaleri.Chapter08.equation_8_35_finrank`:
  $\dim \mathbb{P}_k(T) = (k+1)(k+2)/2$ for a set $T$ with nonempty interior.
* (8.38), `QuarteroniSaccoSaleri.Chapter08.equation_8_38_comp`: $(\Pi_T^k f) \circ F_T = \hat\Pi^k
  (f \circ F_T)$.
* (8.39), `QuarteroniSaccoSaleri.Chapter08.equation_8_39`: $|f(x) - \Pi_T^k f(x)| \le C h_T^{k+1}
  \|f^{(k+1)}\|_{\infty,T}$ on $T$, with $C = (\sum_m \|\hat l_m\|_{\infty,\hat T} + 1)/(k+1)!$.
* (8.39) for $k = 1$, `QuarteroniSaccoSaleri.Chapter08.equation_8_39_linear`: $|f(x) - \Pi_T^1 f(x)|
  \le 2 h_T^2 \|f''\|_{\infty,T}$ on $T$.
* (8.40), `QuarteroniSaccoSaleri.Chapter08.equation_8_40`: $|f(x) - \Pi_h^k f(x)| \le C h^{k+1}
  \|f^{(k+1)}\|_{\infty,\Omega}$ on $\bar\Omega$ for every conforming triangulation.

## Proof outline

For (8.39), let $P$ be the Taylor polynomial of degree $k$ of $f$ at the vertex $a_1$. Read through
$F_T$, $P$ is a polynomial of total degree at most $k$, so the interpolant reproduces it, and
$f - \Pi_T^k f = (f - P) - \Pi_T^k (f - P)$. The triangle $T$ is star-shaped with respect to $a_1$,
so Taylor's theorem along the segments from $a_1$ gives $|f - P| \le M h_T^{k+1}/(k+1)!$ on $T$. The
bound (8.40) is (8.39) on the element that contains the point.

## Conventions

* Points of the plane are elements of `ℝ × ℝ`, which carries the sup norm
  $\|(x, y)\| = \max\{|x|, |y|\}$. The exception is (8.40): its triangulation lives on
  `EuclideanSpace ℝ (Fin 2)`, and the reference data are read through the coordinate equivalence
  `QuarteroniSaccoSaleri.Chapter08.planeEquiv`.
* The norm $\|f^{(k+1)}(x)\|$ is the operator norm of the $(k+1)$-linear map
  `iteratedFDeriv ℝ (k + 1) f x`.
* A polynomial space on a set $D \subseteq \mathbb{R}^2$ is `Approximation.mvPolyLE` on
  `D : Set (Fin 2 → ℝ)`.

## Implementation notes

* The admissibility of a triangulation, which makes the piecewise interpolant (8.37) continuous, is
  `Triangulation.IsConformingElement`. The piecewise interpolant $\Pi_h^k f$ is
  `Triangulation.globalInterp`, and its restriction to an element is the element interpolant
  `Triangulation.localInterp`.
* The space $\mathbb{P}_k^c(\Omega)$ of (8.36) is `Triangulation.polySpace` of
  `Numlib.Analysis.Sobolev.Triangulation`.

## Deviations from the source

* **Generalization.** The tensor-product formulas work on the plane with injective node arrays in
  arbitrary order. See `QuarteroniSaccoSaleri.Chapter08.tensorProductInterp`,
  `QuarteroniSaccoSaleri.Chapter08.tensorProductInterp_isNodalBasis`,
  `QuarteroniSaccoSaleri.Chapter08.tensorProductInterp_apply_node`,
  `QuarteroniSaccoSaleri.Chapter08.tensorProductInterp_mem_span`.
* **Generalization.** The affine formula is defined for degenerate triangles, and bijectivity is
  equivalent to nonzero determinant. See `QuarteroniSaccoSaleri.Chapter08.equation_8_34`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_34_matrix`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_34_apply`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_34_vertex`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_34_bijective`.
* **Generalization.** The polynomial dimension formula holds on any set with nonempty interior. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_35_finrank`.
* **Generalization.** Affine transport works for arbitrary finite node and shape data with a left
  inverse. See `QuarteroniSaccoSaleri.Chapter08.equation_8_38_comp`.
* **Generalization.** The local estimate takes a nodal spanning family as input, gives an explicit
  constant, and proves the linear case with constant two. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_39`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_39_linear`.
* **Generalization.** The global sup-norm estimate uses a conforming nodal family and does not
  require shape regularity. See `QuarteroniSaccoSaleri.Chapter08.equation_8_40`.
* **(8.39)** (generalization). The reference Lagrange basis of $\mathbb{P}_k(\hat T)$ is a
  hypothesis: any nodal basis with nodes in $\hat T$ that spans $\mathbb{P}_k(\hat T)$, and $h_T$ is
  any bound on the two edges at $a_1$. The constant is explicit. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_39`.
* **(8.40)** (generalization). The regularity hypothesis $\max_T h_T/\rho_T \le \sigma$ of the
  source is not needed in the sup norm. See `QuarteroniSaccoSaleri.Chapter08.equation_8_40`.

## Not formalized

* **Example 8.7**, a table.
* **The existence of the reference Lagrange basis** on the principal lattice of Figure 8.8 (the
  $\mathbb{P}_k$-unisolvence of Ciarlet, Theorem 2.2.1), which (8.39) takes as a hypothesis.
-/

open Polynomial Set
open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter08

variable {n m : ℕ}

/-! ### Section 8.5.1: tensor-product interpolation -/

/-- **Section 8.5.1** of [quarteroni2000numerical], the tensor-product interpolant. Let
$x_0, \ldots, x_n$ and $y_0, \ldots, y_m$ be real numbers, and let
$f : \mathbb{R}^2 \to \mathbb{R}$. The **tensor-product interpolant** of $f$ on the grid
$(x_i, y_j)$ is
$$\Pi_{n,m} f(x, y) = \sum_{i=0}^n \sum_{j=0}^m f(x_i, y_j) l_i(x) l_j(y),$$
where $l_i \in \mathbb{P}_n$ and $l_j \in \mathbb{P}_m$ are the characteristic Lagrange
polynomials of the nodes $x_0, \ldots, x_n$ and $y_0, \ldots, y_m$.

The polynomial $l_i$ is `Lagrange.basis Finset.univ x i`. The interpolant is the nodal
interpolation operator `Approximation.nodalInterp` with the nodes $(x_i, y_j)$ and the product
shape functions.

**Generalization.** The function is defined on the whole plane. The grid nodes need not be ordered,
while nodal and span theorems use injective node arrays separately along each axis.
-/
noncomputable def tensorProductInterp (x : Fin (n + 1) → ℝ) (y : Fin (m + 1) → ℝ)
    (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  Approximation.nodalInterp (fun p : Fin (n + 1) × Fin (m + 1) => (x p.1, y p.2))
    (fun p q => (Lagrange.basis Finset.univ x p.1).eval q.1
      * (Lagrange.basis Finset.univ y p.2).eval q.2) f

/-- **Section 8.5.1** of [quarteroni2000numerical], nodal property. Let $x_0, \ldots, x_n$ be
distinct real numbers and let $y_0, \ldots, y_m$ be distinct real numbers. Then the product
shape functions $l_i(x) l_j(y)$ form a nodal basis for the grid nodes $(x_i, y_j)$: the function
with index $(i, j)$ takes the value $1$ at $(x_i, y_j)$ and the value $0$ at every other grid
node.

This is (8.3) in each variable. The nodal property is `Approximation.IsNodalBasis`.

**Generalization.** The function is defined on the whole plane. The grid nodes need not be ordered,
while nodal and span theorems use injective node arrays separately along each axis.
-/
theorem tensorProductInterp_isNodalBasis {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {y : Fin (m + 1) → ℝ} (hy : Function.Injective y) :
    Approximation.IsNodalBasis (fun p : Fin (n + 1) × Fin (m + 1) => (x p.1, y p.2))
      fun p q => (Lagrange.basis Finset.univ x p.1).eval q.1
        * (Lagrange.basis Finset.univ y p.2).eval q.2 where
  eval_self p := by simp [equation_8_3 hx, equation_8_3 hy]
  eval_of_ne p q hpq := by
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      simp [equation_8_3 hx, equation_8_3 hy, h2]
    · simp [equation_8_3 hx, equation_8_3 hy, h1]

/-- **Section 8.5.1** of [quarteroni2000numerical], interpolation at the nodes. Let
$x_0, \ldots, x_n$ be distinct real numbers, let $y_0, \ldots, y_m$ be distinct real numbers,
and let $f : \mathbb{R}^2 \to \mathbb{R}$. Then for all $i$ and $j$,
$$\Pi_{n,m} f(x_i, y_j) = f(x_i, y_j).$$

The proof is `Approximation.IsNodalBasis.nodalInterp_apply_node`.

**Generalization.** The function is defined on the whole plane. The grid nodes need not be ordered,
while nodal and span theorems use injective node arrays separately along each axis.
-/
theorem tensorProductInterp_apply_node {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {y : Fin (m + 1) → ℝ} (hy : Function.Injective y) (f : ℝ × ℝ → ℝ) (i : Fin (n + 1))
    (j : Fin (m + 1)) : tensorProductInterp x y f (x i, y j) = f (x i, y j) :=
  (tensorProductInterp_isNodalBasis hx hy).nodalInterp_apply_node f (i, j)

/-- A polynomial function of degree at most $n$ lies in the span of the monomials $s \mapsto s^p$,
$p \le n$. -/
private theorem eval_mem_span_monomials {P : ℝ[X]} (hP : P.natDegree ≤ n) :
    (fun s : ℝ => P.eval s)
      ∈ Submodule.span ℝ (Set.range fun p : Fin (n + 1) => fun s : ℝ => s ^ (p : ℕ)) := by
  have : (fun s : ℝ => P.eval s)
      = ∑ p : Fin (n + 1), P.coeff p • fun s : ℝ => s ^ (p : ℕ) := by
    funext s
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_apply,
      ← Fin.sum_univ_eq_sum_range (fun p => P.coeff p * s ^ p)]
    simp
  rw [this]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- **Section 8.5.1** of [quarteroni2000numerical], polynomial degree. Let $x_0, \ldots, x_n$ be
distinct real numbers, let $y_0, \ldots, y_m$ be distinct real numbers, and let
$f : \mathbb{R}^2 \to \mathbb{R}$. Then $\Pi_{n,m} f$ is a polynomial of degree at most $n$ in
$x$ and at most $m$ in $y$: it lies in the span of the monomials $x^p y^q$ with $p \le n$ and
$q \le m$.

**Generalization.** The function is defined on the whole plane. The grid nodes need not be ordered,
while nodal and span theorems use injective node arrays separately along each axis.
-/
theorem tensorProductInterp_mem_span {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {y : Fin (m + 1) → ℝ} (hy : Function.Injective y) (f : ℝ × ℝ → ℝ) :
    tensorProductInterp x y f ∈ Submodule.span ℝ
      (Set.range fun pq : Fin (n + 1) × Fin (m + 1) =>
        fun q : ℝ × ℝ => q.1 ^ (pq.1 : ℕ) * q.2 ^ (pq.2 : ℕ)) := by
  classical
  have hcard : ∀ k, (Finset.univ : Finset (Fin (k + 1))).card = k + 1 := fun k => by simp
  -- the shape functions lie in the span
  have hshape : ∀ p : Fin (n + 1) × Fin (m + 1),
      (fun q : ℝ × ℝ => (Lagrange.basis Finset.univ x p.1).eval q.1
        * (Lagrange.basis Finset.univ y p.2).eval q.2) ∈ Submodule.span ℝ
          (Set.range fun pq : Fin (n + 1) × Fin (m + 1) =>
            fun q : ℝ × ℝ => q.1 ^ (pq.1 : ℕ) * q.2 ^ (pq.2 : ℕ)) := by
    intro p
    have hdx : (Lagrange.basis Finset.univ x p.1).natDegree ≤ n := by
      rw [Lagrange.natDegree_basis hx.injOn (Finset.mem_univ _), hcard]
      simp
    have hdy : (Lagrange.basis Finset.univ y p.2).natDegree ≤ m := by
      rw [Lagrange.natDegree_basis hy.injOn (Finset.mem_univ _), hcard]
      simp
    have hx' : (fun q : ℝ × ℝ => (Lagrange.basis Finset.univ x p.1).eval q.1)
        = ∑ a : Fin (n + 1), (Lagrange.basis Finset.univ x p.1).coeff a •
            fun q : ℝ × ℝ => q.1 ^ (a : ℕ) := by
      funext q
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdx), Finset.sum_apply,
        ← Fin.sum_univ_eq_sum_range (fun a => (Lagrange.basis Finset.univ x p.1).coeff a * q.1 ^ a)]
      simp
    have hy' : (fun q : ℝ × ℝ => (Lagrange.basis Finset.univ y p.2).eval q.2)
        = ∑ b : Fin (m + 1), (Lagrange.basis Finset.univ y p.2).coeff b •
            fun q : ℝ × ℝ => q.2 ^ (b : ℕ) := by
      funext q
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdy), Finset.sum_apply,
        ← Fin.sum_univ_eq_sum_range (fun b => (Lagrange.basis Finset.univ y p.2).coeff b * q.2 ^ b)]
      simp
    have : (fun q : ℝ × ℝ => (Lagrange.basis Finset.univ x p.1).eval q.1
        * (Lagrange.basis Finset.univ y p.2).eval q.2)
        = ∑ a : Fin (n + 1), ∑ b : Fin (m + 1),
            ((Lagrange.basis Finset.univ x p.1).coeff a
                * (Lagrange.basis Finset.univ y p.2).coeff b)
              • fun q : ℝ × ℝ => q.1 ^ (a : ℕ) * q.2 ^ (b : ℕ) := by
      funext q
      have h1 := congrFun hx' q
      have h2 := congrFun hy' q
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
      rw [h1, h2, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)
  unfold tensorProductInterp Approximation.nodalInterp
  have : (fun q : ℝ × ℝ => ∑ p : Fin (n + 1) × Fin (m + 1),
      ((Lagrange.basis Finset.univ x p.1).eval q.1 * (Lagrange.basis Finset.univ y p.2).eval q.2)
        • f (x p.1, y p.2))
      = ∑ p : Fin (n + 1) × Fin (m + 1), f (x p.1, y p.2) •
          fun q : ℝ × ℝ => (Lagrange.basis Finset.univ x p.1).eval q.1
            * (Lagrange.basis Finset.univ y p.2).eval q.2 := by
    funext q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  rw [this]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hshape p)

/-! ### Remark 8.1: the bilinear problem at four nodes -/

/-- **Remark 8.1** of [quarteroni2000numerical], the square. The square $[-1, 1]^2$, as the product
of two closed intervals. -/
abbrev remark_8_1_square : Type := Icc (-1 : ℝ) 1 × Icc (-1 : ℝ) 1

/-- **Remark 8.1** of [quarteroni2000numerical], the coordinates. The coordinate functions
$(x, y) \mapsto x$ and $(x, y) \mapsto y$ on the square $[-1, 1]^2$, as continuous functions. -/
noncomputable def remark_8_1_coord : Fin 2 → C(remark_8_1_square, ℝ) :=
  ![⟨fun q => (q.1 : ℝ), by fun_prop⟩, ⟨fun q => (q.2 : ℝ), by fun_prop⟩]

/-- **Remark 8.1** of [quarteroni2000numerical], the space. The space of the polynomials
$$p(x, y) = a_3 xy + a_2 x + a_1 y + a_0,$$
which have degree $1$ in each of $x$ and $y$, as continuous functions on the square $[-1, 1]^2$.

The space is the span of $1$, $x$, $y$ and $xy$ in $C([-1, 1]^2)$. -/
noncomputable def remark_8_1_space : Submodule ℝ C(remark_8_1_square, ℝ) :=
  Submodule.span ℝ {1, remark_8_1_coord 0, remark_8_1_coord 1,
    remark_8_1_coord 0 * remark_8_1_coord 1}

/-- **Remark 8.1** of [quarteroni2000numerical], the nodes. The four nodes $(-1, 0)$, $(0, -1)$,
$(1, 0)$ and $(0, 1)$ of the square $[-1, 1]^2$. -/
noncomputable def remark_8_1_node : Fin 4 → remark_8_1_square :=
  ![(⟨-1, by norm_num⟩, ⟨0, by norm_num⟩), (⟨0, by norm_num⟩, ⟨-1, by norm_num⟩),
    (⟨1, by norm_num⟩, ⟨0, by norm_num⟩), (⟨0, by norm_num⟩, ⟨1, by norm_num⟩)]

/-- **Remark 8.1** of [quarteroni2000numerical], the mechanism. The product $xy$ vanishes at each of
the four nodes $(-1, 0)$, $(0, -1)$, $(1, 0)$, $(0, 1)$. -/
theorem remark_8_1_apply_node (k : Fin 4) :
    (remark_8_1_coord 0 * remark_8_1_coord 1) (remark_8_1_node k) = 0 := by
  fin_cases k <;> simp [remark_8_1_coord, remark_8_1_node]

/-- **Remark 8.1** of [quarteroni2000numerical]. Interpolation by the polynomials
$p(x, y) = a_3 xy + a_2 x + a_1 y + a_0$ at the four distinct nodes $(-1, 0)$, $(0, -1)$,
$(1, 0)$, $(0, 1)$ is not unisolvent: it is not true that for every choice of four values there
is exactly one such $p$ that takes these values at the nodes.

The reason is that $xy$ is a nonzero element of the space that vanishes at the four nodes, so
the interpolation conditions do not fix the coefficient $a_3$. Unisolvence is
`Approximation.IsUnisolvent`, with the point evaluations at the nodes as the functionals. -/
theorem remark_8_1 :
    ¬ Approximation.IsUnisolvent remark_8_1_space
      fun k => ContinuousMap.evalCLM ℝ (remark_8_1_node k) := by
  intro h
  obtain ⟨u, -, huniq⟩ := h 0
  have hmem : remark_8_1_coord 0 * remark_8_1_coord 1 ∈ remark_8_1_space :=
    Submodule.subset_span (by simp)
  have h1 := huniq ⟨_, hmem⟩ fun k => by simpa using remark_8_1_apply_node k
  have h2 := huniq 0 fun k => by simp
  have h3 : remark_8_1_coord 0 * remark_8_1_coord 1 = 0 := by
    have := h1.trans h2.symm
    simpa using congrArg Subtype.val this
  have := congrArg (fun g : C(remark_8_1_square, ℝ) =>
    g (⟨1 / 2, by norm_num⟩, ⟨1 / 2, by norm_num⟩)) h3
  norm_num [remark_8_1_coord] at this

/-! ### Section 8.5.2: the affine map from the reference triangle, and the space $\mathbb{P}_k$ -/

/-- **Equation (8.34)** of [quarteroni2000numerical], the affine map. Let
$a_1, a_2, a_3 \in \mathbb{R}^2$. The **affine map** $F_T(\hat x) = B_T \hat x + b_T$ from the
reference triangle with vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ onto the triangle $T$ with
vertices $a_1, a_2, a_3$ has $B_T = [a_2 - a_1 \mid a_3 - a_1]$ and $b_T = a_1$, that is,
$$F_T(\hat x, \hat y) = a_1 + \hat x (a_2 - a_1) + \hat y (a_3 - a_1).$$

The map is defined for any three points, also for collinear ones.

**Generalization.** The affine map and its vertex identities also hold for collinear or repeated
image vertices. The theorem isolates precisely the nonzero determinant condition needed for
bijectivity.
-/
noncomputable def equation_8_34 (a₁ a₂ a₃ : ℝ × ℝ) : ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ :=
  ((LinearMap.fst ℝ ℝ ℝ).smulRight (a₂ - a₁)
    + (LinearMap.snd ℝ ℝ ℝ).smulRight (a₃ - a₁)).toAffineMap + AffineMap.const ℝ (ℝ × ℝ) a₁

/-- **Equation (8.34)** of [quarteroni2000numerical], the matrix. Let
$a_i = (x_i, y_i) \in \mathbb{R}^2$ for $i = 1, 2, 3$. The matrix of the affine map $F_T$ is
$$B_T = \begin{bmatrix} x_2 - x_1 & x_3 - x_1 \\ y_2 - y_1 & y_3 - y_1 \end{bmatrix}.$$

**Generalization.** The affine map and its vertex identities also hold for collinear or repeated
image vertices. The theorem isolates precisely the nonzero determinant condition needed for
bijectivity.
-/
def equation_8_34_matrix (a₁ a₂ a₃ : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a₂.1 - a₁.1, a₃.1 - a₁.1; a₂.2 - a₁.2, a₃.2 - a₁.2]

/-- **Equation (8.34)** of [quarteroni2000numerical], the value. Let
$a_1, a_2, a_3, p \in \mathbb{R}^2$. Then
$$F_T(p) = p_1 (a_2 - a_1) + p_2 (a_3 - a_1) + a_1.$$

**Generalization.** The affine map and its vertex identities also hold for collinear or repeated
image vertices. The theorem isolates precisely the nonzero determinant condition needed for
bijectivity.
-/
theorem equation_8_34_apply (a₁ a₂ a₃ : ℝ × ℝ) (p : ℝ × ℝ) :
    equation_8_34 a₁ a₂ a₃ p = p.1 • (a₂ - a₁) + p.2 • (a₃ - a₁) + a₁ := by
  simp [equation_8_34]

/-- **Equation (8.34)** of [quarteroni2000numerical], the vertices. Let
$a_1, a_2, a_3 \in \mathbb{R}^2$. Then $F_T(0, 0) = a_1$, $F_T(1, 0) = a_2$ and
$F_T(0, 1) = a_3$.

**Generalization.** The affine map and its vertex identities also hold for collinear or repeated
image vertices. The theorem isolates precisely the nonzero determinant condition needed for
bijectivity.
-/
theorem equation_8_34_vertex (a₁ a₂ a₃ : ℝ × ℝ) :
    equation_8_34 a₁ a₂ a₃ (0, 0) = a₁ ∧ equation_8_34 a₁ a₂ a₃ (1, 0) = a₂ ∧
      equation_8_34 a₁ a₂ a₃ (0, 1) = a₃ := by
  simp [equation_8_34_apply]

/-- **Equation (8.34)** of [quarteroni2000numerical], the linear part. Let
$a_1, a_2, a_3 \in \mathbb{R}^2$. The matrix of the linear part of $F_T$ in the standard basis
of $\mathbb{R}^2$ is $B_T$. -/
theorem toMatrix_equation_8_34_linear (a₁ a₂ a₃ : ℝ × ℝ) :
    LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (equation_8_34 a₁ a₂ a₃).linear = equation_8_34_matrix a₁ a₂ a₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, equation_8_34, equation_8_34_matrix,
      Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]

/-- **Equation (8.34)** of [quarteroni2000numerical], invertibility. Let
$a_1, a_2, a_3 \in \mathbb{R}^2$. The affine map $F_T$ is a bijection of the plane if and only
if $\det B_T \neq 0$, that is, if and only if the three vertices are not collinear.

**Generalization.** The affine map and its vertex identities also hold for collinear or repeated
image vertices. The theorem isolates precisely the nonzero determinant condition needed for
bijectivity.
-/
theorem equation_8_34_bijective (a₁ a₂ a₃ : ℝ × ℝ) :
    Function.Bijective (equation_8_34 a₁ a₂ a₃) ↔ (equation_8_34_matrix a₁ a₂ a₃).det ≠ 0 := by
  set L := (equation_8_34 a₁ a₂ a₃).linear with hL
  have hF : ⇑(equation_8_34 a₁ a₂ a₃) = (fun v => v + a₁) ∘ ⇑L := by
    funext p
    simp [hL, equation_8_34]
  have hdet : L.det = (equation_8_34_matrix a₁ a₂ a₃).det := by
    rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), toMatrix_equation_8_34_linear]
  rw [hF, Function.Bijective.of_comp_iff' (AddGroup.addRight_bijective a₁), ← hdet,
    Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, LinearMap.injective_iff_surjective.mp h⟩⟩

/-- **Equation (8.35)** of [quarteroni2000numerical]. Let $T \subseteq \mathbb{R}^2$ be a set with
nonempty interior, such as a triangle, and let $k \in \mathbb{N}$. The space $\mathbb{P}_k(T)$
of the restrictions to $T$ of the polynomials of total degree at most $k$ in two variables has
dimension
$$d_k = \dim \mathbb{P}_k(T) = \frac{(k+1)(k+2)}{2}.$$

The space is `Approximation.mvPolyLE T k`, and the proof specializes
`Approximation.finrank_mvPolyLE`. The division in Lean is division of natural numbers, which is
exact here.

**Generalization.** The dimension statement works for restrictions to any planar set with nonempty
interior, with total degree bounded by k.
-/
theorem equation_8_35_finrank {T : Set (Fin 2 → ℝ)} (hT : (interior T).Nonempty) (k : ℕ) :
    Module.finrank ℝ (Approximation.mvPolyLE T k) = (k + 1) * (k + 2) / 2 := by
  rw [Approximation.finrank_mvPolyLE hT, Fintype.card_fin, Nat.choose_two_right,
    show k + 2 - 1 = k + 1 from rfl, mul_comm]

/-- **Equation (8.38)** of [quarteroni2000numerical], the reference-element identity. Let
$a_1, a_2, a_3 \in \mathbb{R}^2$, and let $G$ be a left inverse of $F_T$. Let
$\hat z_m \in \mathbb{R}^2$ be local nodes and $\hat l_m : \mathbb{R}^2 \to \mathbb{R}$
functions on the reference triangle, for $m$ in a finite set, and let
$f : \mathbb{R}^2 \to \mathbb{R}$. Define the element interpolant $\Pi_T^k f = \sum_m f(F_T \hat
z_m) (\hat l_m \circ G)$ and the reference interpolant
$\hat\Pi^k g = \sum_m g(\hat z_m) \hat l_m$. Then
$$(\Pi_T^k f) \circ F_T = \hat\Pi^k (f \circ F_T).$$

This is the identity behind $l_{j,T} = \hat l_j \circ F_T^{-1}$ in (8.38), with $G$ in the role
of $F_T^{-1}$. The proof is `Approximation.nodalInterp_comp`.

**Generalization.** The transport identity applies to arbitrary finite nodes and shape functions and
needs only a left inverse of the affine map. The source uses the local Lagrange nodal basis.
-/
theorem equation_8_38_comp {ι : Type*} [Fintype ι] (a₁ a₂ a₃ : ℝ × ℝ) {G : ℝ × ℝ → ℝ × ℝ}
    (hG : Function.LeftInverse G (equation_8_34 a₁ a₂ a₃)) (zhat : ι → ℝ × ℝ)
    (lhat : ι → ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℝ) :
    Approximation.nodalInterp (equation_8_34 a₁ a₂ a₃ ∘ zhat) (fun m => lhat m ∘ G) f
        ∘ equation_8_34 a₁ a₂ a₃
      = Approximation.nodalInterp zhat lhat (f ∘ equation_8_34 a₁ a₂ a₃) :=
  Approximation.nodalInterp_comp zhat lhat f hG

/-! ### Equation (8.39): the interpolation error on a triangle -/

/-- **Section 8.5.2** of [quarteroni2000numerical], the reference triangle. The **reference
triangle** $\hat T$ with vertices $(0, 0)$, $(1, 0)$ and $(0, 1)$ is the closed set
$$\hat T = \{(\hat x, \hat y) \in \mathbb{R}^2 : \hat x \ge 0, \ \hat y \ge 0, \ \hat x + \hat y
  \le 1\}.$$

It is a subset of `ℝ × ℝ`, the plane on which the affine map (8.34) acts. -/
def referenceTriangle : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1}

section Triangle

variable {a₁ a₂ a₃ : ℝ × ℝ}

local notation "F_T" => equation_8_34 a₁ a₂ a₃

/-- Let $a_1, a_2, a_3 \in \mathbb{R}^2$. For every
$\hat x = (\hat x_1, \hat x_2) \in \mathbb{R}^2$, the affine map (8.34) satisfies $F_T \hat x -
a_1 = \hat x_1 (a_2 - a_1) + \hat x_2 (a_3 - a_1)$. This supports (8.39). -/
theorem equation_8_34_sub_vertex (x : ℝ × ℝ) :
    F_T x - a₁ = x.1 • (a₂ - a₁) + x.2 • (a₃ - a₁) := by
  rw [equation_8_34_apply, add_sub_cancel_right]

/-- Let $a_1, a_2, a_3 \in \mathbb{R}^2$. The triangle $T = F_T(\hat T)$ is star-shaped with respect
to its vertex $a_1$: for $\hat x \in \hat T$ and $s \in [0, 1]$,
$$a_1 + s (F_T \hat x - a_1) \in F_T(\hat T).$$

This supports (8.39). The segment from $a_1$ to $F_T \hat x$ is the image under $F_T$ of the
segment from $(0, 0)$ to $\hat x$, which stays in $\hat T$. -/
theorem equation_8_34_segment_mem {x : ℝ × ℝ} (hx : x ∈ referenceTriangle) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : a₁ + s • (F_T x - a₁) ∈ F_T '' referenceTriangle := by
  refine ⟨s • x, ⟨mul_nonneg hs.1 hx.1, mul_nonneg hs.1 hx.2.1, ?_⟩, ?_⟩
  · calc s * x.1 + s * x.2 = s * (x.1 + x.2) := by ring
      _ ≤ 1 * 1 := mul_le_mul hs.2 hx.2.2 (add_nonneg hx.1 hx.2.1) zero_le_one
      _ = 1 := one_mul 1
  · rw [equation_8_34_apply, equation_8_34_sub_vertex]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_add, smul_smul]
    abel

/-- Let $a_1, a_2, a_3 \in \mathbb{R}^2$ and $h \in \mathbb{R}$ with $\|a_2 - a_1\| \le h$ and
$\|a_3 - a_1\| \le h$. Then every point of the triangle $T = F_T(\hat T)$ has distance at most
$h$ from the vertex $a_1$: $\|F_T \hat x - a_1\| \le h$ for all $\hat x \in \hat T$. This
supports (8.39). -/
theorem norm_equation_8_34_sub_vertex_le {h : ℝ} (hh₂ : ‖a₂ - a₁‖ ≤ h) (hh₃ : ‖a₃ - a₁‖ ≤ h)
    {x : ℝ × ℝ} (hx : x ∈ referenceTriangle) : ‖F_T x - a₁‖ ≤ h := by
  rw [equation_8_34_sub_vertex]
  calc ‖x.1 • (a₂ - a₁) + x.2 • (a₃ - a₁)‖ ≤ ‖x.1 • (a₂ - a₁)‖ + ‖x.2 • (a₃ - a₁)‖ :=
        norm_add_le _ _
    _ = x.1 * ‖a₂ - a₁‖ + x.2 * ‖a₃ - a₁‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hx.1, Real.norm_of_nonneg hx.2.1]
    _ ≤ x.1 * h + x.2 * h :=
        add_le_add (mul_le_mul_of_nonneg_left hh₂ hx.1) (mul_le_mul_of_nonneg_left hh₃ hx.2.1)
    _ = (x.1 + x.2) * h := by ring
    _ ≤ 1 * h := mul_le_mul_of_nonneg_right hx.2.2 ((norm_nonneg _).trans hh₂)
    _ = h := one_mul h

/-- Let $a_1, a_2, a_3 \in \mathbb{R}^2$, $f : \mathbb{R}^2 \to \mathbb{R}$ and $k \in \mathbb{N}$.
The Taylor polynomial of degree $k$ of $f$ at the vertex $a_1$, read through $F_T$, is a
polynomial of total degree at most $k$: there is a polynomial $q$ in two variables of total
degree at most $k$ such that for all $\hat x = (\hat x_1, \hat x_2) \in \mathbb{R}^2$,
$$\sum_{j=0}^k \frac{1}{j!} D^j f(a_1)[F_T \hat x - a_1, \ldots, F_T \hat x - a_1] = q(\hat x_1,
  \hat x_2).$$

This supports (8.39). The statement needs no smoothness of $f$, because `iteratedFDeriv` is
defined for every function. The proof uses `exists_mvPolynomial_taylorSum` and the formula for
$F_T \hat x - a_1$. -/
theorem exists_mvPolynomial_taylor_equation_8_34 (f : ℝ × ℝ → ℝ) (k : ℕ) :
    ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k ∧ ∀ x : ℝ × ℝ,
      ∑ j ∈ Finset.range (k + 1), ((j ! : ℝ)⁻¹) • iteratedFDeriv ℝ j f a₁ (fun _ => F_T x - a₁)
        = MvPolynomial.eval ![x.1, x.2] q := by
  obtain ⟨q, hqdeg, hq⟩ := exists_mvPolynomial_taylorSum (f := f) a₁ k ![a₂ - a₁, a₃ - a₁]
  refine ⟨q, hqdeg, fun x => ?_⟩
  rw [← hq ![x.1, x.2]]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    equation_8_34_sub_vertex]

/-- **Equation (8.39)** of [quarteroni2000numerical]. Let $a_1, a_2, a_3 \in \mathbb{R}^2$, let
$F_T$ be the affine map (8.34), let $G$ be a left inverse of $F_T$, and let $T = F_T(\hat T)$.
Let $k \in \mathbb{N}$. Let $\hat z_m \in \hat T$ and $\hat l_m : \mathbb{R}^2 \to \mathbb{R}$,
for $m$ in a finite set, satisfy:
* $\hat l_m(\hat z_j) = \delta_{mj}$ for all $m$ and $j$;
* every polynomial of total degree at most $k$ in two variables equals a linear combination of
  the $\hat l_m$ on $\hat T$;
* $|\hat l_m| \le L_m$ on $\hat T$ for all $m$.

Let $\Pi_T^k f = \sum_m f(F_T \hat z_m) (\hat l_m \circ G)$ be the element interpolant (8.38).
Let $h \in \mathbb{R}$ with $\|a_2 - a_1\| \le h$ and $\|a_3 - a_1\| \le h$. Let
$f : \mathbb{R}^2 \to \mathbb{R}$ be $C^{k+1}$ at every point of $T$, and let
$\|f^{(k+1)}(x)\| \le M$ for all $x \in T$. Then for every $x \in T$,
$$|f(x) - \Pi_T^k f(x)| \le \frac{\sum_m L_m + 1}{(k+1)!} \, h^{k+1} M.$$

**Generalization.** The source states $\|f - \Pi_T^k f\|_{\infty,T} \le C h_T^{k+1}
\|f^{(k+1)}\|_{\infty,T}$ for the Lagrange basis on the principal lattice of Figure 8.8, with
$h_T$ the diameter of $T$ and a constant $C$ independent of $h_T$ and $f$, and quotes the
theorem of Ciarlet and Lions (Theorem 16.1), whose proof goes through the Bramble–Hilbert lemma
in $W^{k+1,\infty}$. Here the reference basis is any nodal basis that spans
$\mathbb{P}_k(\hat T)$, $h$ is any bound on the two edges at $a_1$, and the constant is
explicit. The maximum edge length of $T$, in any norm that dominates the sup norm, is such a
bound. No shape regularity of $T$ enters. The existence of the basis on the principal lattice is
the $\mathbb{P}_k$-unisolvence of Ciarlet, Theorem 2.2.1, which is not formalized.

The plane `ℝ × ℝ` carries the sup norm, and $\|f^{(k+1)}(x)\|$ is the operator norm of the
$(k+1)$-linear map `iteratedFDeriv ℝ (k + 1) f x`. The left inverse $G$ exists only if $F_T$ is
injective, that is, only if $T$ is nondegenerate. The proof is elementary: with $P$ the Taylor
polynomial of $f$ of degree $k$ at $a_1$, $f - \Pi_T^k f = (f - P) - \Pi_T^k (f - P)$ because
$\Pi_T^k$ reproduces $P$
(`QuarteroniSaccoSaleri.Chapter08.exists_mvPolynomial_taylor_equation_8_34`), and
$|f - P| \le M h^{k+1}/(k+1)!$ on $T$ by `norm_sub_taylorSum_segment_le` along the segments from
$a_1$ (`QuarteroniSaccoSaleri.Chapter08.equation_8_34_segment_mem`).

**Generalization.** The reference shape functions are assumed nodal and spanning, and their
individual bounds enter an explicit constant. Any bound on the two emanating edges suffices. The
linear case supplies concrete reference functions and constant two.
-/
theorem equation_8_39 {ι : Type*} [Fintype ι] {k : ℕ} {G : ℝ × ℝ → ℝ × ℝ}
    (hG : Function.LeftInverse G F_T)
    {zhat : ι → ℝ × ℝ} (hz : ∀ m, zhat m ∈ referenceTriangle) {lhat : ι → ℝ × ℝ → ℝ}
    (hnodal : Approximation.IsNodalBasis zhat lhat)
    (hspan : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k → ∃ c : ι → ℝ,
      ∀ x ∈ referenceTriangle, MvPolynomial.eval ![x.1, x.2] q = ∑ m, c m * lhat m x)
    {L : ι → ℝ} (hL : ∀ m, ∀ x ∈ referenceTriangle, |lhat m x| ≤ L m)
    {h : ℝ} (hh₂ : ‖a₂ - a₁‖ ≤ h) (hh₃ : ‖a₃ - a₁‖ ≤ h) {f : ℝ × ℝ → ℝ}
    (hf : ∀ x ∈ F_T '' referenceTriangle, ContDiffAt ℝ (k + 1) f x) {M : ℝ}
    (hM : ∀ x ∈ F_T '' referenceTriangle, ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ M) :
    ∀ x ∈ F_T '' referenceTriangle,
      |f x - Approximation.nodalInterp (F_T ∘ zhat) (fun m => lhat m ∘ G) f x|
        ≤ (∑ m, L m + 1) / (k + 1)! * h ^ (k + 1) * M := by
  rintro _ ⟨x, hx, rfl⟩
  -- the Taylor polynomial of `f` at the vertex `a₁`
  set P : ℝ × ℝ → ℝ := fun y =>
    ∑ j ∈ Finset.range (k + 1), ((j ! : ℝ)⁻¹) • iteratedFDeriv ℝ j f a₁ (fun _ => y - a₁) with hP
  -- (1) Taylor's theorem along the segments from `a₁`
  have htaylor : ∀ y ∈ referenceTriangle,
      |f (F_T y) - P (F_T y)| ≤ M * h ^ (k + 1) / (k + 1)! := by
    intro y hy
    have key := norm_sub_taylorSum_segment_le (f := f) (n := k) (a := a₁) (w := F_T y - a₁)
      (M := M) (fun s hs => hf _ (equation_8_34_segment_mem hy hs))
      (fun s hs => hM _ (equation_8_34_segment_mem hy hs))
    rw [add_sub_cancel, Real.norm_eq_abs] at key
    refine key.trans ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨y, hy, rfl⟩)
    gcongr
    exact norm_equation_8_34_sub_vertex_le hh₂ hh₃ hy
  -- (2) the interpolant reproduces `P`, a polynomial of degree `≤ k`
  obtain ⟨q, hqdeg, hq⟩ := exists_mvPolynomial_taylor_equation_8_34 (a₂ := a₂) (a₃ := a₃) f k
  have hPF : ∀ y : ℝ × ℝ, P (F_T y) = MvPolynomial.eval ![y.1, y.2] q := hq
  obtain ⟨c, hc⟩ := hspan q hqdeg
  have hcm : ∀ m, c m = P (F_T (zhat m)) := by
    intro m
    rw [hPF, hc _ (hz m), Finset.sum_eq_single m]
    · rw [hnodal.eval_self, mul_one]
    · intro m' _ hm'
      rw [hnodal.eval_of_ne m' m hm', mul_zero]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  have hrepr : ∑ m, lhat m x * P (F_T (zhat m)) = P (F_T x) := by
    rw [hPF, hc x hx]
    exact Finset.sum_congr rfl fun m _ => by rw [hcm, mul_comm]
  -- (3) assemble
  have hinterp : Approximation.nodalInterp (F_T ∘ zhat) (fun m => lhat m ∘ G) f (F_T x)
      = ∑ m, lhat m x * f (F_T (zhat m)) := by
    simp only [Approximation.nodalInterp_apply, Function.comp, hG x, smul_eq_mul]
  have hsplit : f (F_T x) - ∑ m, lhat m x * f (F_T (zhat m))
      = (f (F_T x) - P (F_T x)) + ∑ m, lhat m x * (P (F_T (zhat m)) - f (F_T (zhat m))) := by
    simp only [mul_sub, Finset.sum_sub_distrib, hrepr]
    ring
  rw [hinterp, hsplit]
  calc |(f (F_T x) - P (F_T x)) + ∑ m, lhat m x * (P (F_T (zhat m)) - f (F_T (zhat m)))|
      ≤ |f (F_T x) - P (F_T x)| + |∑ m, lhat m x * (P (F_T (zhat m)) - f (F_T (zhat m)))| :=
        abs_add_le _ _
    _ ≤ M * h ^ (k + 1) / (k + 1)! + ∑ m, L m * (M * h ^ (k + 1) / (k + 1)!) := by
        gcongr
        · exact htaylor x hx
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
          rw [abs_mul, abs_sub_comm]
          exact mul_le_mul (hL m x hx) (htaylor _ (hz m)) (abs_nonneg _)
            ((abs_nonneg _).trans (hL m x hx))
    _ = (∑ m, L m + 1) / (k + 1)! * h ^ (k + 1) * M := by
        rw [← Finset.sum_mul]
        ring

end Triangle

/-! ### The case $k = 1$: nodes at the vertices -/

/-- **Section 8.5.2** of [quarteroni2000numerical], the local nodes for $k = 1$ (Figure 8.8). The
three vertices $(0, 0)$, $(1, 0)$ and $(0, 1)$ of the reference triangle. -/
def linearNodes : Fin 3 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (0, 1)]

/-- **Section 8.5.2** of [quarteroni2000numerical], the reference basis for $k = 1$. The Lagrange
basis of $\mathbb{P}_1(\hat T)$ at the vertices is given by the barycentric coordinates
$$\lambda_0(\hat x, \hat y) = 1 - \hat x - \hat y, \qquad \lambda_1(\hat x, \hat y) = \hat x,
  \qquad \lambda_2(\hat x, \hat y) = \hat y.$$
-/
def linearShape : Fin 3 → ℝ × ℝ → ℝ :=
  ![fun x => 1 - x.1 - x.2, fun x => x.1, fun x => x.2]

/-- **Section 8.5.2** of [quarteroni2000numerical], for $k = 1$. The three vertices lie in the
reference triangle $\hat T$. -/
theorem linearNodes_mem (m : Fin 3) : linearNodes m ∈ referenceTriangle := by
  fin_cases m <;> simp [linearNodes, referenceTriangle]

/-- **Section 8.5.2** of [quarteroni2000numerical], for $k = 1$. The barycentric coordinates are a
nodal basis for the vertices: $\lambda_m(\hat z_j) = \delta_{mj}$. -/
theorem linearShape_isNodalBasis : Approximation.IsNodalBasis linearNodes linearShape where
  eval_self m := by fin_cases m <;> simp [linearNodes, linearShape]
  eval_of_ne m j hmj := by
    fin_cases m <;> fin_cases j <;> simp_all [linearNodes, linearShape]

/-- **Section 8.5.2** of [quarteroni2000numerical], for $k = 1$. The barycentric coordinates satisfy
$|\lambda_m(\hat x)| \le 1$ for every $\hat x \in \hat T$. -/
theorem abs_linearShape_le (m : Fin 3) {x : ℝ × ℝ} (hx : x ∈ referenceTriangle) :
    |linearShape m x| ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := hx
  rw [abs_le]
  fin_cases m <;> simp [linearShape] <;> constructor <;> linarith

/-- **Section 8.5.2** of [quarteroni2000numerical], for $k = 1$. The barycentric coordinates span
$\mathbb{P}_1(\hat T)$: for every polynomial $q$ in two variables of total degree at most $1$
there are coefficients $c_0, c_1, c_2$ with $q = c_0 \lambda_0 + c_1 \lambda_1 + c_2 \lambda_2$
on $\hat T$.

The coefficients are $q(0, 0)$, $q(1, 0)$ and $q(0, 1)$. -/
theorem linearShape_span (q : MvPolynomial (Fin 2) ℝ) (hq : q.totalDegree ≤ 1) :
    ∃ c : Fin 3 → ℝ, ∀ x ∈ referenceTriangle,
      MvPolynomial.eval ![x.1, x.2] q = ∑ m, c m * linearShape m x := by
  refine ⟨fun m => MvPolynomial.eval ![(linearNodes m).1, (linearNodes m).2] q, fun x _ => ?_⟩
  -- monomial by monomial
  have hmono : ∀ v ∈ q.support, ∏ i, ![x.1, x.2] i ^ v i
      = ∑ m, (∏ i, ![(linearNodes m).1, (linearNodes m).2] i ^ v i) * linearShape m x := by
    intro v hv
    have hdeg : v 0 + v 1 ≤ 1 := by
      have := MvPolynomial.le_totalDegree hv
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
      exact this.trans hq
    simp only [Fin.prod_univ_two, Fin.sum_univ_three, linearNodes, linearShape,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_fin_one]
    rcases Nat.eq_zero_or_pos (v 0) with h0 | h0 <;> rcases Nat.eq_zero_or_pos (v 1) with h1 | h1
    · rw [h0, h1]; ring
    · obtain h1' : v 1 = 1 := by omega
      rw [h0, h1']; ring
    · obtain h0' : v 0 = 1 := by omega
      rw [h0', h1]; ring
    · omega
  simp only [MvPolynomial.eval_eq', Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hmono v hv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

section Triangle

variable {a₁ a₂ a₃ : ℝ × ℝ}

local notation "F_T" => equation_8_34 a₁ a₂ a₃

/-- **Equation (8.39)** of [quarteroni2000numerical], for $k = 1$. Let
$a_1, a_2, a_3 \in \mathbb{R}^2$, let $G$ be a left inverse of the affine map $F_T$ of (8.34),
and let $T = F_T(\hat T)$. Let $\Pi_T^1 f = \sum_{m=0}^2 f(F_T \hat z_m) (\lambda_m \circ G)$ be
the element interpolant with the nodes at the vertices $\hat z_m$ of $\hat T$ and the
barycentric coordinates $\lambda_m$. Let $h \in \mathbb{R}$ with $\|a_2 - a_1\| \le h$ and
$\|a_3 - a_1\| \le h$. Let $f : \mathbb{R}^2 \to \mathbb{R}$ be $C^2$ at every point of $T$,
with $\|f''(x)\| \le M$ for all $x \in T$. Then for every $x \in T$,
$$|f(x) - \Pi_T^1 f(x)| \le 2 h^2 M.$$

This is `QuarteroniSaccoSaleri.Chapter08.equation_8_39` with the barycentric coordinates as the
reference basis. Since $\|\lambda_m\|_{\infty,\hat T} \le 1$, the constant is $(3 + 1)/2! = 2$.

**Generalization.** The reference shape functions are assumed nodal and spanning, and their
individual bounds enter an explicit constant. Any bound on the two emanating edges suffices. The
linear case supplies concrete reference functions and constant two.
-/
theorem equation_8_39_linear {G : ℝ × ℝ → ℝ × ℝ} (hG : Function.LeftInverse G F_T)
    {h : ℝ} (hh₂ : ‖a₂ - a₁‖ ≤ h) (hh₃ : ‖a₃ - a₁‖ ≤ h) {f : ℝ × ℝ → ℝ}
    (hf : ∀ x ∈ F_T '' referenceTriangle, ContDiffAt ℝ 2 f x) {M : ℝ}
    (hM : ∀ x ∈ F_T '' referenceTriangle, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M) :
    ∀ x ∈ F_T '' referenceTriangle,
      |f x - Approximation.nodalInterp (F_T ∘ linearNodes) (fun m => linearShape m ∘ G) f x|
        ≤ 2 * h ^ 2 * M := by
  intro x hx
  refine (equation_8_39 (k := 1) hG linearNodes_mem linearShape_isNodalBasis linearShape_span
    (L := fun _ => 1) (fun m x hx => abs_linearShape_le m hx) hh₂ hh₃ hf hM x hx).trans_eq ?_
  simp only [Fin.sum_univ_three, Nat.factorial]
  norm_num

end Triangle


/-!
### Equation (8.40): the interpolation error on a triangulation

The global estimate is (8.39) on each element, together with the maximum over the elements. The
triangulation is a `Triangulation` on the plane `EuclideanSpace ℝ (Fin 2)`, and the global
interpolant $\Pi_h^k f$ of (8.37) is `Triangulation.globalInterp`. The element estimate (8.39) is
stated on the plane `ℝ × ℝ` of the affine map (8.34). Therefore it is transported along the
coordinate equivalence `QuarteroniSaccoSaleri.Chapter08.planeEquiv` from the Euclidean plane to
`ℝ × ℝ`. This changes the norms by the factor $\|\mathtt{planeEquiv}^{-1}\|^{k+1}$, which goes into
the constant.
-/

section Equation840

open EuclideanSpace TopologicalSpace

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The coordinate equivalence $x \mapsto (x_0, x_1)$ from the Euclidean plane
`EuclideanSpace ℝ (Fin 2)` of the triangulations to the plane `ℝ × ℝ` of the affine map (8.34).
It supports (8.40). -/
noncomputable def planeEquiv : 𝔼₂ ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

/-- For $x$ in the Euclidean plane, `planeEquiv x` $= (x_0, x_1)$. -/
theorem planeEquiv_apply (x : 𝔼₂) : planeEquiv x = (x 0, x 1) := rfl

/-- For $p \in$ `ℝ × ℝ`, the first coordinate of `planeEquiv.symm p` is $p_1$. -/
theorem planeEquiv_symm_apply_zero (p : ℝ × ℝ) : planeEquiv.symm p 0 = p.1 := rfl

/-- For $p \in$ `ℝ × ℝ`, the second coordinate of `planeEquiv.symm p` is $p_2$. -/
theorem planeEquiv_symm_apply_one (p : ℝ × ℝ) : planeEquiv.symm p 1 = p.2 := rfl

/-- For $x$ in the Euclidean plane, the sup norm of `planeEquiv x` is at most the Euclidean norm of
$x$. -/
theorem norm_planeEquiv_apply_le (x : 𝔼₂) : ‖planeEquiv x‖ ≤ ‖x‖ := by
  rw [planeEquiv_apply, Prod.norm_def]
  exact max_le (PiLp.norm_apply_le x 0) (PiLp.norm_apply_le x 1)

/-- Let $f$ be a real function on the Euclidean plane, $y \in$ `ℝ × ℝ` and $i \in \mathbb{N}$. The
$i$-th derivative of $f \circ \mathtt{planeEquiv}^{-1}$ at $y$ is the $i$-th derivative of $f$
at $\mathtt{planeEquiv}^{-1}(y)$, composed with $\mathtt{planeEquiv}^{-1}$ in each argument. -/
theorem iteratedFDeriv_comp_planeEquiv_symm (f : 𝔼₂ → ℝ) (y : ℝ × ℝ) (i : ℕ) :
    iteratedFDeriv ℝ i (f ∘ planeEquiv.symm) y
      = (iteratedFDeriv ℝ i f (planeEquiv.symm y)).compContinuousLinearMap
        fun _ ↦ (planeEquiv.symm : ℝ × ℝ →L[ℝ] 𝔼₂) := by
  have := planeEquiv.symm.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (mem_univ (planeEquiv.symm y)) i
  rwa [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at this

/-- Let $f$ be a real function on the Euclidean plane, $y \in$ `ℝ × ℝ` and $i \in \mathbb{N}$. Then
$$\|D^i (f \circ \mathtt{planeEquiv}^{-1})(y)\| \le \|D^i f(\mathtt{planeEquiv}^{-1}(y))\| \,
  \|\mathtt{planeEquiv}^{-1}\|^i.$$
-/
theorem norm_iteratedFDeriv_comp_planeEquiv_symm_le (f : 𝔼₂ → ℝ) (y : ℝ × ℝ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (f ∘ planeEquiv.symm) y‖
      ≤ ‖iteratedFDeriv ℝ i f (planeEquiv.symm y)‖
        * ‖(planeEquiv.symm : ℝ × ℝ →L[ℝ] 𝔼₂)‖ ^ i := by
  rw [iteratedFDeriv_comp_planeEquiv_symm]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A point of the closed reference triangle `EuclideanSpace.referenceTriangle` of the
triangulations, read in `ℝ × ℝ` through `planeEquiv`, lies in the reference triangle $\hat T$ of
(8.34). -/
theorem planeEquiv_mem_referenceTriangle {x : 𝔼₂}
    (hx : x ∈ closure (EuclideanSpace.referenceTriangle : Set 𝔼₂)) :
    planeEquiv x ∈ referenceTriangle := by
  rw [closure_referenceTriangle_eq] at hx
  exact hx

/-- A point of the reference triangle $\hat T$ of (8.34), read in the Euclidean plane through
`planeEquiv.symm`, lies in the closure of `EuclideanSpace.referenceTriangle`. -/
theorem planeEquiv_symm_mem_closure_referenceTriangle {y : ℝ × ℝ} (hy : y ∈ referenceTriangle) :
    planeEquiv.symm y ∈ closure (EuclideanSpace.referenceTriangle : Set 𝔼₂) := by
  rw [closure_referenceTriangle_eq]
  exact hy

/-- Let $\mathcal{T}$ be a triangulation of a domain $\Omega$ in the Euclidean plane, and let $T$ be
an element with vertices $v_0, v_1, v_2$. Let $F_K(z) = L_K z + v_0$ be the affine map of the
element, with $L_K$ = `Triangulation.linearPart`. Then the affine map (8.34) of the vertices
$\mathtt{planeEquiv}(v_0)$, $\mathtt{planeEquiv}(v_1)$, $\mathtt{planeEquiv}(v_2)$ satisfies,
for every $y \in$ `ℝ × ℝ`,
$$F_T(y) = \mathtt{planeEquiv}(F_K(\mathtt{planeEquiv}^{-1}(y))).$$
-/
theorem equation_8_34_planeEquiv {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (T : 𝒯.elems)
    (y : ℝ × ℝ) :
    equation_8_34 (planeEquiv (T.1 0)) (planeEquiv (T.1 1)) (planeEquiv (T.1 2)) y
      = planeEquiv (𝒯.linearPart T (planeEquiv.symm y) + T.1 0) := by
  rw [show 𝒯.linearPart T (planeEquiv.symm y) + T.1 0
      = triangleAffine (T.1 0) (T.1 1) (T.1 2) (planeEquiv.symm y) from
    congrFun (𝒯.affine_eq_triangleAffine T) _, equation_8_34_apply]
  simp only [triangleAffine, map_add, map_smul, map_sub, planeEquiv_symm_apply_zero,
    planeEquiv_symm_apply_one]
  abel

/-- **Equation (8.40)** of [quarteroni2000numerical]. Let $k \in \mathbb{N}$. Let $\hat x_i$ and
$\hat\varphi_i$, $i = 1, \ldots, I$, be nodes and shape functions on the reference triangle
$\hat T$ with these properties:
* each $\hat x_i$ lies in the closed reference triangle;
* $\hat\varphi_i(\hat x_j) = \delta_{ij}$ for all $i$ and $j$;
* every polynomial of total degree at most $k$ in two variables equals a linear combination of
  the $\hat\varphi_i$ on the closed reference triangle;
* $|\hat\varphi_i| \le L_i$ on the closed reference triangle for all $i$.

Then there is a constant $C$, which depends only on $k$ and on these data, with the following
property. Let $\mathcal{T}_h$ be a triangulation of an open set $\Omega$ of the Euclidean plane
on which the element is conforming. Let $f$ be $C^{k+1}$ at every point of $\bar\Omega$, with
$\|f^{(k+1)}(x)\| \le M$ for all $x \in \bar\Omega$. Then for every $x \in \bar\Omega$,
$$|f(x) - \Pi_h^k f(x)| \le C h^{k+1} M,$$
where $h = \max_T h_T$ is the mesh size of $\mathcal{T}_h$ and $\Pi_h^k f$ is the piecewise
interpolant (8.37).

**Generalization.** The source assumes that the family of triangulations is regular,
$\max_T h_T/\rho_T \le \sigma$. This hypothesis is not needed in the sup norm. It comes from the
Sobolev-norm version of the theorem that the source cites, Remark 3.4.2 of
[quarteroni1994numerical].

The conformity of the element, which makes the piecewise interpolant continuous, is
`Triangulation.IsConformingElement`. The interpolant is `Triangulation.globalInterp`, and the
mesh size `Triangulation.meshSize` is the largest Euclidean diameter of an element. The proof
applies (8.39) on the element that contains $x$, with $h_T \le h$, transported from `ℝ × ℝ` to
the Euclidean plane along `QuarteroniSaccoSaleri.Chapter08.planeEquiv`; the factor
$\|\mathtt{planeEquiv}^{-1}\|^{k+1}$ goes into $C$, and $\Pi_h^k f = \Pi_T^k f$ on $T$. The
$\mathbb{P}_k$ Lagrange element on the principal lattice satisfies the hypotheses on the
reference data, by `LagrangeElement.isNodalBasis`, `LagrangeElement.nodalInterp_eval` and
`LagrangeElement.isConformingElement`.

**Generalization.** The uniform error estimate on the closure uses a conforming nodal family on a
reference triangle and a derivative bound. No shape-regularity bound on diameter divided by inradius
is needed for this sup-norm estimate.
-/
theorem equation_8_40 {I : ℕ} {k : ℕ} {xhat : Fin I → 𝔼₂}
    (hx : ∀ i, xhat i ∈ closure (EuclideanSpace.referenceTriangle : Set 𝔼₂))
    {φhat : Fin I → 𝔼₂ → ℝ} (hnodal : Approximation.IsNodalBasis xhat φhat)
    (hspan : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k → ∃ c : Fin I → ℝ,
      ∀ x ∈ closure (EuclideanSpace.referenceTriangle : Set 𝔼₂),
        MvPolynomial.eval (fun j ↦ x j) q = ∑ m, c m * φhat m x)
    {L : Fin I → ℝ}
    (hL : ∀ m, ∀ x ∈ closure (EuclideanSpace.referenceTriangle : Set 𝔼₂), |φhat m x| ≤ L m) :
    ∃ C : ℝ, ∀ {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω), 𝒯.IsConformingElement xhat φhat →
      ∀ {f : 𝔼₂ → ℝ}, (∀ x ∈ closure (Ω : Set 𝔼₂), ContDiffAt ℝ (k + 1) f x) →
      ∀ {M : ℝ}, (∀ x ∈ closure (Ω : Set 𝔼₂), ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ M) →
      ∀ x ∈ closure (Ω : Set 𝔼₂),
        |f x - 𝒯.globalInterp xhat φhat f x| ≤ C * 𝒯.meshSize ^ (k + 1) * M := by
  set N : ℝ := ‖(planeEquiv.symm : ℝ × ℝ →L[ℝ] 𝔼₂)‖ with hN
  refine ⟨(∑ m, L m + 1) / (k + 1)! * N ^ (k + 1), fun {Ω} 𝒯 hconf {f} hf {M} hM x hx' ↦ ?_⟩
  -- the element containing `x`
  rw [𝒯.closure_eq_iUnion_closedK, mem_iUnion] at hx'
  obtain ⟨T, hxT⟩ := hx'
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (𝒯.closedK_subset_closure T hxT))
  -- the data of (8.39) on `ℝ × ℝ`
  have hFe : ∀ y : ℝ × ℝ, equation_8_34 (planeEquiv (T.1 0)) (planeEquiv (T.1 1))
      (planeEquiv (T.1 2)) y = planeEquiv (𝒯.linearPart T (planeEquiv.symm y) + T.1 0) :=
    fun y ↦ equation_8_34_planeEquiv 𝒯 T y
  have hG : Function.LeftInverse
      (fun p ↦ planeEquiv ((𝒯.linearPart T).symm (planeEquiv.symm p - T.1 0)))
      (equation_8_34 (planeEquiv (T.1 0)) (planeEquiv (T.1 1)) (planeEquiv (T.1 2))) := by
    intro y
    simp only [hFe, ContinuousLinearEquiv.symm_apply_apply, 𝒯.affine_symm,
      ContinuousLinearEquiv.apply_symm_apply]
  have hz : ∀ m, planeEquiv (xhat m) ∈ referenceTriangle := fun m ↦
    planeEquiv_mem_referenceTriangle (hx m)
  have hnodal' : Approximation.IsNodalBasis (planeEquiv ∘ xhat) fun m ↦ φhat m ∘ planeEquiv.symm :=
    hnodal.comp planeEquiv.symm_apply_apply
  have hspan' : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k → ∃ c : Fin I → ℝ,
      ∀ y ∈ referenceTriangle,
        MvPolynomial.eval ![y.1, y.2] q = ∑ m, c m * (φhat m ∘ planeEquiv.symm) y := by
    intro q hq
    obtain ⟨c, hc⟩ := hspan q hq
    refine ⟨c, fun y hy ↦ ?_⟩
    have h := hc _ (planeEquiv_symm_mem_closure_referenceTriangle hy)
    have hy' : (![y.1, y.2] : Fin 2 → ℝ) = fun j ↦ planeEquiv.symm y j := by
      funext j
      fin_cases j <;> rfl
    rw [hy']
    exact h
  have hL' : ∀ m, ∀ y ∈ referenceTriangle, |(φhat m ∘ planeEquiv.symm) y| ≤ L m :=
    fun m y hy ↦ hL m _ (planeEquiv_symm_mem_closure_referenceTriangle hy)
  -- the element's edges at the first vertex are bounded by the mesh size
  have hedge : ∀ a : Fin 3, ‖planeEquiv (T.1 a) - planeEquiv (T.1 0)‖ ≤ 𝒯.meshSize := fun a ↦ by
    rw [← map_sub]
    refine (norm_planeEquiv_apply_le _).trans ?_
    rw [← dist_eq_norm]
    refine (Metric.dist_le_diam_of_mem (𝒯.isCompact_closedK T).isBounded
      (𝒯.vertex_mem_closedK T a) (𝒯.vertex_mem_closedK T 0)).trans ?_
    rw [← 𝒯.closure_K, Metric.diam_closure]
    exact 𝒯.diam_le_meshSize T
  -- the image of `T̂` under `F_T` is the element, read in `ℝ × ℝ`
  have himage : ∀ y ∈ equation_8_34 (planeEquiv (T.1 0)) (planeEquiv (T.1 1))
      (planeEquiv (T.1 2)) '' referenceTriangle, planeEquiv.symm y ∈ 𝒯.closedK T := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hFe, ContinuousLinearEquiv.symm_apply_apply, ← 𝒯.image_closedReferenceTriangle,
      ← closure_referenceTriangle_eq]
    exact ⟨_, planeEquiv_symm_mem_closure_referenceTriangle hy, rfl⟩
  have hf' : ∀ y ∈ equation_8_34 (planeEquiv (T.1 0)) (planeEquiv (T.1 1))
      (planeEquiv (T.1 2)) '' referenceTriangle, ContDiffAt ℝ (k + 1) (f ∘ planeEquiv.symm) y :=
    fun y hy ↦ (hf _ (𝒯.closedK_subset_closure T (himage y hy))).comp y
      planeEquiv.symm.contDiff.contDiffAt
  have hM' : ∀ y ∈ equation_8_34 (planeEquiv (T.1 0)) (planeEquiv (T.1 1))
      (planeEquiv (T.1 2)) '' referenceTriangle,
      ‖iteratedFDeriv ℝ (k + 1) (f ∘ planeEquiv.symm) y‖ ≤ M * N ^ (k + 1) := fun y hy ↦
    (norm_iteratedFDeriv_comp_planeEquiv_symm_le f y (k + 1)).trans
      (mul_le_mul_of_nonneg_right (hM _ (𝒯.closedK_subset_closure T (himage y hy)))
        (by positivity))
  -- (8.39) on the element, at the point `e x = F_T (e (F_K⁻¹ x))`
  have hx'' : planeEquiv x ∈ equation_8_34 (planeEquiv (T.1 0)) (planeEquiv (T.1 1))
      (planeEquiv (T.1 2)) '' referenceTriangle := by
    rw [← 𝒯.image_closedReferenceTriangle] at hxT
    obtain ⟨z, hz', rfl⟩ := hxT
    refine ⟨planeEquiv z, planeEquiv_mem_referenceTriangle (by rwa [closure_referenceTriangle_eq]),
      ?_⟩
    rw [hFe, ContinuousLinearEquiv.symm_apply_apply]
  have h839 := equation_8_39 hG hz hnodal' hspan' hL' (hedge 1) (hedge 2) hf' hM'
    (planeEquiv x) hx''
  -- identify the two sides with `f x` and `Π_h^k f (x)`
  simp only [Approximation.nodalInterp_apply, Function.comp_apply, hFe,
    ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul] at h839
  rw [𝒯.globalInterp_eq_of_mem_closedK xhat φhat hconf T f hxT, Triangulation.localInterp_apply]
  refine h839.trans (le_of_eq ?_)
  ring

end Equation840

end QuarteroniSaccoSaleri.Chapter08
