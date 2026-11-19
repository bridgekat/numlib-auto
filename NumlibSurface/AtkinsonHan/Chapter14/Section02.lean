/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.RidgePolynomial
import NumlibSurface.AtkinsonHan.Chapter14.Section01

/-!
# Atkinson and Han, Section 14.2: Orthogonal polynomials in several variables

This module formalizes Section 14.2 of [han2009theoretical]. The section works in $L^2$ of the unit
ball $\mathbb{B}_d = \{x \in \mathbb{R}^d : \|x\| \le 1\}$, with the inner product
$(f, g) = \int_{\mathbb{B}_d} f g \, dx$ or the weighted inner product (14.2.11). The space
$\mathcal{V}_n^d$ consists of the polynomials in $\Pi_n^d$ that are orthogonal to $\Pi_{n-1}^d$.
Lemma 14.2.1 gives the orthogonal decomposition $\Pi_n^d = \mathcal{V}_0^d \oplus \cdots \oplus
\mathcal{V}_n^d$, and $\dim \mathcal{V}_n^d = \binom{n + d - 1}{d - 1}$. Theorem 14.2.3 is the
triple recursion relation: multiplication by a coordinate $x_j$ maps $\mathcal{V}_n^d$ into
$\mathcal{V}_{n-1}^d \oplus \mathcal{V}_n^d \oplus \mathcal{V}_{n+1}^d$. The orthogonal projection
$P_n$ onto $\Pi_n^d$ is the sum of the projections onto the components (14.2.12), and a bounded
projection of $C(\mathbb{B}_d)$ onto $\Pi_n^d$ satisfies the Lebesgue bound (14.2.13). Example
14.2.2 gives the Logan–Shepp ridge polynomials as an orthonormal basis of $\mathcal{V}_n^2$.

The orthogonal decomposition is the backbone `Numlib.Approximation.OrthogonalDecomposition` applied
to the chain $\Pi_0^d \subseteq \Pi_1^d \subseteq \cdots$ inside $L^2(\mu)$, and the integrals of
the ridge polynomials come from `Numlib.Approximation.RidgePolynomial`.

## Main definitions

* `AtkinsonHan.Chapter14.unitBall`: the closed unit ball $\mathbb{B}_d$.
* `AtkinsonHan.Chapter14.orthPolySpace`: the space $\mathcal{V}_n^d$ of orthogonal polynomials of
  degree $n$.
* Example 14.2.2, `AtkinsonHan.Chapter14.ridgeL2`: the ridge polynomials $\varphi_{n,k}(x, y) =
  \pi^{-1/2} U_n(x \cos(k h) + y \sin(k h))$, $h = \pi/(n + 1)$, in $L^2(\mathbb{B}_2)$.

## Main results

* Lemma 14.2.1, `AtkinsonHan.Chapter14.lemma_14_2_1`: $\Pi_n^d = \mathcal{V}_0^d + \cdots +
  \mathcal{V}_n^d$, with `AtkinsonHan.Chapter14.lemma_14_2_1_isOrtho` and
  `AtkinsonHan.Chapter14.lemma_14_2_1_iSupIndep` for the orthogonality and the directness of the
  sum.
* `AtkinsonHan.Chapter14.finrank_orthPolySpace`: $\dim \mathcal{V}_n^d = \binom{n + d - 1}{d - 1}$
  for $n \ge 1$.
* `AtkinsonHan.Chapter14.finrank_orthPolySpace_two`: $\dim \mathcal{V}_n^2 = n + 1$.
* Theorem 14.2.3, `AtkinsonHan.Chapter14.theorem_14_2_3`: $x_j \mathcal{V}_n^d \subseteq
  \mathcal{V}_{n-1}^d + \mathcal{V}_n^d + \mathcal{V}_{n+1}^d$.
* Theorem 14.2.3, `AtkinsonHan.Chapter14.theorem_14_2_3_unique`: the decomposition into the three
  components is unique.
* (14.2.10) and Exercise 14.2.1, `AtkinsonHan.Chapter14.exercise_14_2_1`: $(x_j p, q) = (p, x_j q)$.
* (14.2.11), `AtkinsonHan.Chapter14.isMvWeight_ballVolume`: the volume of $\mathbb{B}_d$ is a weight
  for the $L^2$ theory of polynomials.
* (14.2.12), `AtkinsonHan.Chapter14.equation_14_2_12`: $P_n$ is the sum of the orthogonal
  projections onto $\mathcal{V}_0^d, \dots, \mathcal{V}_n^d$.
* (14.2.12), `AtkinsonHan.Chapter14.equation_14_2_12_isBestApprox`: $P_n f$ is the best $L^2$
  approximation to $f$ from $\Pi_n^d$.
* (14.2.13), `AtkinsonHan.Chapter14.equation_14_2_13`: a bounded projection $P$ onto $\Pi_n^d$
  satisfies $\|f - P f\|_\infty \le (1 + \|P\|) E_n(f)$.
* Example 14.2.2, `AtkinsonHan.Chapter14.example_14_2_2`: the ridge polynomials
  $\varphi_{n,0}, \dots, \varphi_{n,n}$ are an orthonormal basis of $\mathcal{V}_n^2$.
* Example 14.2.2, `AtkinsonHan.Chapter14.example_14_2_2_polyLE`: the ridge polynomials of degree at
  most $N$ span $\Pi_N^2$.

## Proof outline

The book gives no proof of Example 14.2.2 and cites Logan and Shepp. Polar coordinates do not prove
it: $U_n(r \cos \beta)$ has no closed form for $r < 1$, so the angular integral does not separate.
The proof here uses the chord (Radon) decomposition of the integral over the disk, from the backbone
`Numlib.Approximation.RidgePolynomial`. It gives $$\int_{\mathbb{B}_2} U_n(x \cdot u_\theta) \,
U_m(x \cdot u_\psi) \, dx = \delta_{nm} \frac{\pi \, U_n(\cos(\theta - \psi))}{n + 1},$$ hence
$\varphi_{n,j} \perp \varphi_{m,k}$ for $n \neq m$, and also within a degree at the equispaced
directions $k \pi / (n + 1)$. The family of degree $n$ is orthonormal. It lies in $\mathcal{V}_n^2$
because it is orthogonal to the ridge polynomials of every lower degree, which span $\Pi_{n-1}^2$ by
induction. It spans $\mathcal{V}_n^2$ because $\dim \mathcal{V}_n^2 = n + 1$.

## Implementation notes

* The results are stated for a measure $\mu$ on $\mathbb{R}^d$ that satisfies
  `Approximation.IsMvWeight`: every polynomial is square integrable, and no nonzero polynomial
  vanishes almost everywhere. The volume of the unit ball is such a measure
  (`AtkinsonHan.Chapter14.isMvWeight_ballVolume`), and so is $w \, dx$ for a positive weight $w$, so
  the weighted inner product (14.2.11) needs no separate treatment.
* The space $\mathcal{V}_n^d$ is the $n$-th orthogonal component `Approximation.orthogonalComponent`
  of the chain `hw.polyLE n` of copies of $\Pi_n^d$ in $L^2(\mu)$.
* The matrices $A_{n,j}$, $B_{n,j}$ and $C_{n,j}$ of Theorem 14.2.3 are the expansions of the three
  components in a basis of each component, and they are not written. The theorem is stated
  coordinate-free.

## Deviations from the source

* **Section 14.2, the measure** (generalization). The book works with the volume of $\mathbb{B}_d$
  and with the weight of (14.2.11). The results hold for every measure that satisfies
  `Approximation.IsMvWeight`. See `AtkinsonHan.Chapter14.isMvWeight_ballVolume`.
* **Theorem 14.2.3** (reading). The book asserts that there are unique matrices $A_{n,j}$,
  $B_{n,j}$, $C_{n,j}$ in the recursion. The theorem states the membership of $x_j \varphi$ in
  $\mathcal{V}_{n-1}^d + \mathcal{V}_n^d + \mathcal{V}_{n+1}^d$ and the uniqueness of the three
  components. See `AtkinsonHan.Chapter14.theorem_14_2_3`.
* **Exercise 14.2.1** (partial translation). The formalized identity moves coordinate
  multiplication between the two arguments of the inner product. The exercise asks for the
  resulting matrix formulas (14.2.8)–(14.2.10).
* **(14.2.13)** (generalization). The book states the bound on $C(\mathbb{B}_d)$. It holds on $C(D)$
  for every compact $D \subseteq \mathbb{R}^d$. See `AtkinsonHan.Chapter14.equation_14_2_13`.

## Not formalized

* **(14.2.8) and (14.2.9)**, the defining relations of the matrices $A_{n,j}$ and $B_{n,j}$, asked
  for in Exercise 14.2.1. The matrices are not written.
* **(14.2.14)–(14.2.15)**, the closed form of the reproducing kernel: $P_n f(x) =
  \int_{\mathbb{B}_2} G_n(x, y) f(y) \, dy$ with $G_n(x, y) = c_n \int_0^\pi P_n^{(3/2, 1/2)}(x
  \cdot y + \sqrt{1 - \|x\|^2} \sqrt{1 - \|y\|^2} \cos \psi) \, d\psi$ and $c_n = \sqrt{\pi} \,
  \Gamma(n + 3) / (4 \Gamma(n + 3/2))$, where $P_n^{(3/2, 1/2)}$ is the Jacobi polynomial for the
  weight $(1 - t)^{3/2} (1 + t)^{1/2}$. Mathlib has neither Jacobi nor Gegenbauer polynomials, and
  `Numlib.Approximation.OrthogonalPolynomial` has only the one-variable families with the Legendre
  and Chebyshev normalizations. The kernel as the sum $\sum \varphi_{m,\ell}(x) \varphi_{m,\ell}(y)$
  over an orthonormal basis exists, because $\Pi_n^2$ is finite-dimensional. The book proves neither
  (14.2.15) nor (14.2.16), and calls both a special case of results of Yuan Xu.
* **Theorem 14.2.4**, $\|P_n\|_{C(\mathbb{B}_2) \to C(\mathbb{B}_2)} = O(n)$ (14.2.16). The book
  quotes it from Yuan Xu without proof. The reduction $\|P_n\| = \sup_x \int_{\mathbb{B}_2} |G_n(x,
  y)| \, dy$, (2.2.8) of the book, is available as `IntegralOperator.norm_kernelCLM`; the $O(n)$
  bound on this integral needs asymptotic estimates of the Jacobi polynomials through the closed
  form (14.2.14)–(14.2.15).
* **Theorem 14.2.5**: for $f \in C^k(\mathbb{B}_2)$ with $k \ge 1$, $\|f - P_n f\|_\infty \le
  (c_1(k) / n^{k-1}) [\|f\|_{*,k} / n + \omega_k(f, 1/n)]$ (14.2.17), so $P_n f \to f$ uniformly for
  $f \in C^1(\mathbb{B}_2)$; and there is $f \in C(\mathbb{B}_2)$ for which $P_n f$ does not
  converge uniformly. It follows from (14.2.13), which is `AtkinsonHan.Chapter14.equation_14_2_13`,
  together with Theorem 14.2.4 and Theorem 14.1.1, which are not formalized. The second part also
  needs the Banach–Steinhaus theorem, Mathlib's `banach_steinhaus`.
* **Exercise 14.2.4**, the integral identity between the sphere and the disk. It needs the surface
  measure on $S^2$.
-/

open Approximation MeasureTheory Module

namespace AtkinsonHan.Chapter14

section Ball

variable (d : ℕ)

/-- For $d \in \mathbb{N}$, the **closed unit ball** $\mathbb{B}_d = \{x \in \mathbb{R}^d : \sum_i
x_i^2 \le 1\}$.

It is written as a set of coordinate vectors `Fin d → ℝ`, so that `MvPolynomial.eval` applies to
its elements directly. -/
def unitBall : Set (Fin d → ℝ) := {x | ∑ i, x i ^ 2 ≤ 1}

/-- A point $x \in \mathbb{R}^d$ is in $\mathbb{B}_d$ if and only if $\sum_i x_i^2 \le 1$. -/
theorem mem_unitBall_iff {x : Fin d → ℝ} : x ∈ unitBall d ↔ ∑ i, x i ^ 2 ≤ 1 := Iff.rfl

/-- The unit ball $\mathbb{B}_d$ is closed. -/
theorem isClosed_unitBall : IsClosed (unitBall d) :=
  isClosed_le (by fun_prop) continuous_const

/-- The unit ball $\mathbb{B}_d$ is contained in the cube $[-1, 1]^d$, which is the closed unit ball
of the maximum norm of `Fin d → ℝ`. -/
theorem unitBall_subset_closedBall : unitBall d ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h : x i ^ 2 ≤ 1 :=
    le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)) hx
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (x i), sq_abs (x i)]

/-- The unit ball $\mathbb{B}_d$ is compact, because it is closed and contained in the cube
$[-1, 1]^d$. -/
theorem isCompact_unitBall : IsCompact (unitBall d) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_unitBall d)
    (Metric.isBounded_closedBall.subset (unitBall_subset_closedBall d))

/-- The origin is an interior point of the unit ball $\mathbb{B}_d$. This makes the $L^2$ inner
product of Section 14.2 definite on polynomials. -/
theorem zero_mem_interior_unitBall : (0 : Fin d → ℝ) ∈ interior (unitBall d) := by
  have hopen : IsOpen {x : Fin d → ℝ | ∑ i, x i ^ 2 < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hsub : {x : Fin d → ℝ | ∑ i, x i ^ 2 < 1} ⊆ interior (unitBall d) :=
    interior_maximal (fun _ hx => le_of_lt (Set.mem_ofPred_eq ▸ hx)) hopen
  exact hsub (by simp)

/-- **Equation (14.2.11)** of [han2009theoretical], for the standard weight $w = 1$. For every $d$,
the Lebesgue measure restricted to $\mathbb{B}_d$ is a weight for polynomials
(`Approximation.IsMvWeight`): every polynomial is square integrable on $\mathbb{B}_d$, and no
nonzero polynomial vanishes almost everywhere on $\mathbb{B}_d$. So the inner product
$(f, g) = \int_{\mathbb{B}_d} f g \, dx$ is definite on $\Pi_n^d$.

**Generalization.** The weighted inner product $(f, g)_w = \int_{\mathbb{B}_d} w f g \, dx$ of
(14.2.11) is the same statement for the measure $w \, dx$. Every result below is stated for an
arbitrary measure that satisfies `Approximation.IsMvWeight`, and this theorem gives the standard
case. -/
theorem isMvWeight_ballVolume : IsMvWeight (volume.restrict (unitBall d)) :=
  isMvWeight_restrict (isCompact_unitBall d) (isClosed_unitBall d).measurableSet
    (isCompact_unitBall d).measure_lt_top.ne ⟨0, zero_mem_interior_unitBall d⟩

end Ball

variable {d : ℕ} {μ : Measure (Fin d → ℝ)}

/-- Let $\mu$ be a weight for polynomials on $\mathbb{R}^d$. The space $\mathcal{V}_n^d$ consists of
the polynomials of degree at most $n$ that are orthogonal in $L^2(\mu)$ to all polynomials of
degree at most $n - 1$, with $\mathcal{V}_0^d$ the constants. It is the $n$-th orthogonal
component of the chain $\Pi_0^d \subseteq \Pi_1^d \subseteq \cdots$ inside $L^2(\mu)$.

The definition is `Approximation.orthogonalComponent` of the chain `hw.polyLE`.

**Reading.** Uses L² classes for any admissible polynomial weight measure.
-/
noncomputable abbrev orthPolySpace (hw : IsMvWeight μ) (n : ℕ) : Submodule ℝ (Lp ℝ 2 μ) :=
  orthogonalComponent hw.polyLE n

variable (hw : IsMvWeight μ)

/-- The space $\mathcal{V}_0^d$ is $\Pi_0^d$, the space of constants.

**Reading.** Constants as L² classes for any admissible weight.
-/
theorem orthPolySpace_zero : orthPolySpace hw 0 = hw.polyLE 0 := rfl

/-- For every $n \in \mathbb{N}$, an element $f \in L^2(\mu)$ is in $\mathcal{V}_{n+1}^d$ if and
only if $f \in \Pi_{n+1}^d$ and $(g, f) = 0$ for every $g \in \Pi_n^d$. This is the defining
property of $\mathcal{V}_{n+1}^d$ in the book.

**Reading.** Orthogonality to the previous degree space for general weight measures.
-/
theorem mem_orthPolySpace_succ_iff {n : ℕ} {f : Lp ℝ 2 μ} :
    f ∈ orthPolySpace hw (n + 1) ↔ f ∈ hw.polyLE (n + 1) ∧ ∀ g ∈ hw.polyLE n, inner ℝ g f = 0 := by
  rw [orthPolySpace, orthogonalComponent_succ, Submodule.mem_inf, and_comm,
    Submodule.mem_orthogonal]

/-- For every $n$, the space $\mathcal{V}_n^d$ is contained in $\Pi_n^d$.

**Reading.** Degree inclusion for the weighted L² classes.
-/
theorem orthPolySpace_le (n : ℕ) : orthPolySpace hw n ≤ hw.polyLE n :=
  orthogonalComponent_le _ n

/-- **Lemma 14.2.1** of [han2009theoretical], the spanning part. Let $\mu$ be a weight for
polynomials on $\mathbb{R}^d$. For every $n \in \mathbb{N}$, $$\Pi_n^d = \mathcal{V}_0^d +
\mathcal{V}_1^d + \cdots + \mathcal{V}_n^d$$ in $L^2(\mu)$.

The book writes the sum as a direct sum, $\Pi_n^d = \mathcal{V}_0^d \oplus \cdots \oplus
\mathcal{V}_n^d$. The orthogonality and the directness are
`AtkinsonHan.Chapter14.lemma_14_2_1_isOrtho` and `AtkinsonHan.Chapter14.lemma_14_2_1_iSupIndep`.

**Reading.** Spanning orthogonal decomposition for any admissible weight measure.
-/
theorem lemma_14_2_1 (n : ℕ) :
    (Finset.range (n + 1)).sup (orthPolySpace hw) = hw.polyLE n :=
  finsetSup_orthogonalComponent hw.monotone_polyLE (fun _ => inferInstance) n

/-- **Lemma 14.2.1** of [han2009theoretical], the orthogonality part. For $m \neq n$, the spaces
$\mathcal{V}_m^d$ and $\mathcal{V}_n^d$ are orthogonal in $L^2(\mu)$.

**Reading.** Orthogonality of the degree layers for any admissible weight.
-/
theorem lemma_14_2_1_isOrtho {m n : ℕ} (h : m ≠ n) : orthPolySpace hw m ⟂ orthPolySpace hw n :=
  orthogonalComponent_isOrtho hw.monotone_polyLE h

/-- **Lemma 14.2.1** of [han2009theoretical], the directness part. The spaces
$\mathcal{V}_0^d, \mathcal{V}_1^d, \dots$ are independent: each $\mathcal{V}_n^d$ meets the sum
of the others only in $0$.

**Reading.** Independence of all the weight-space degree components.
-/
theorem lemma_14_2_1_iSupIndep : iSupIndep (orthPolySpace hw) :=
  iSupIndep_orthogonalComponent hw.monotone_polyLE

/-- **Section 14.2** of [han2009theoretical], the dimension of $\mathcal{V}_n^d$. Let $d \ge 1$ and
let $\mu$ be a weight for polynomials on $\mathbb{R}^d$. For every $n \in \mathbb{N}$, $$\dim
\mathcal{V}_{n+1}^d = \binom{n + d}{d - 1},$$ which is $\dim \mathcal{P}_{n+1}^d$, the dimension
of the space of homogeneous polynomials of degree $n + 1$ in $d$ variables.

The theorem is stated for the indices $n + 1 \ge 1$; the case $n = 0$ is
$\dim \mathcal{V}_0^d = \dim \Pi_0^d = 1$. The proof uses Lemma 14.2.1, the dimension of
$\Pi_n^d$ and Pascal's rule, without a basis.

**Reading.** Same degree-layer dimension on arbitrary weight measure in positive dimension.
-/
theorem finrank_orthPolySpace (hd : 1 ≤ d) (n : ℕ) :
    finrank ℝ (orthPolySpace hw (n + 1)) = (n + d).choose (d - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hadd : finrank ℝ (orthPolySpace hw (n + 1)) +
      (n + Fintype.card (Fin (e + 1))).choose (Fintype.card (Fin (e + 1))) =
      (n + 1 + Fintype.card (Fin (e + 1))).choose (Fintype.card (Fin (e + 1))) :=
    hw.finrank_orthogonalComponent_add n
  have hpascal : (n + e + 1 + 1).choose (e + 1)
      = (n + e + 1).choose e + (n + e + 1).choose (e + 1) := Nat.choose_succ_succ (n + e + 1) e
  simp only [Fintype.card_fin] at hadd
  rw [show n + 1 + (e + 1) = n + e + 1 + 1 by omega, show n + (e + 1) = n + e + 1 by omega] at hadd
  rw [show n + (e + 1) = n + e + 1 by omega, Nat.add_sub_cancel]
  omega

/-- **Section 14.2** of [han2009theoretical], the dimension in the plane. Let $\mu$ be a weight for
polynomials on $\mathbb{R}^2$. For every $n \in \mathbb{N}$, $\dim \mathcal{V}_n^2 = n + 1$.

**Reading.** Planar formula n+1 for arbitrary admissible planar weights.
-/
theorem finrank_orthPolySpace_two {μ : Measure (Fin 2 → ℝ)} (hw : IsMvWeight μ) (n : ℕ) :
    finrank ℝ (orthPolySpace hw n) = n + 1 := by
  cases n with
  | zero =>
    rw [show orthPolySpace hw 0 = hw.polyLE 0 from rfl, hw.finrank_polyLE 0]
    simp
  | succ n => simpa using finrank_orthPolySpace hw one_le_two n

/-- **Equation (14.2.10)** of [han2009theoretical], part of **Exercise 14.2.1**, in coordinate-free
form. Let $\mu$ be a weight for polynomials on $\mathbb{R}^d$. For every coordinate index $j$
and all polynomials $p, q$, $$(x_j p, q) = (p, x_j q)$$ in $L^2(\mu)$.

For $p \in \mathcal{V}_n^d$ and $q \in \mathcal{V}_{n+1}^d$, the expansion of both sides in a
basis of each space gives $A_{n,j} H_{n+1} = H_n C_{n+1,j}^T$, which is (14.2.10); for an
orthonormal basis it reads $C_{n+1,j} = A_{n,j}^T$. Exercise 14.2.1 also asks for (14.2.8) and
(14.2.9), the defining relations of the matrices $A_{n,j}$ and $B_{n,j}$. These matrices are not
written, so only (14.2.10) is formalized.

**Reading.** Only the inner-product identity underlying the matrix formulas, for general weights.
-/
theorem exercise_14_2_1 (j : Fin d) (p q : MvPolynomial (Fin d) ℝ) :
    inner ℝ (hw.toL2 (MvPolynomial.X j * p)) (hw.toL2 q) =
      inner ℝ (hw.toL2 p) (hw.toL2 (MvPolynomial.X j * q)) :=
  hw.inner_toL2_mul_left _ p q

/-- **Theorem 14.2.3** of [han2009theoretical] (triple recursion relation), in membership form. Let
$\mu$ be a weight for polynomials on $\mathbb{R}^d$, let $n \in \mathbb{N}$ and let $j$ be a
coordinate index. If $p$ is a polynomial whose class in $L^2(\mu)$ lies in $\mathcal{V}_n^d$,
then $$x_j p \in \mathcal{V}_{n-1}^d + \mathcal{V}_n^d + \mathcal{V}_{n+1}^d.$$

**Reading.** The book states that there are unique matrices $A_{n,j}$, $B_{n,j}$ and $C_{n,j}$
that express $x_j$ times a basis of $\mathcal{V}_n^d$ through bases of $\mathcal{V}_{n+1}^d$,
$\mathcal{V}_n^d$ and $\mathcal{V}_{n-1}^d$. The theorem states the membership, and
`AtkinsonHan.Chapter14.theorem_14_2_3_unique` states the uniqueness of the three components; the
matrices are the expansions of these components in the bases.

For $n = 0$ the index $n - 1$ is $0$ in Lean's natural subtraction, so the conclusion is
$x_j p \in \mathcal{V}_0^d + \mathcal{V}_1^d$. The proof uses only
`AtkinsonHan.Chapter14.exercise_14_2_1`: for $q$ of degree at most $n - 2$,
$(x_j p, q) = (p, x_j q) = 0$, because $x_j q$ has degree at most $n - 1$. This is the
multivariate form of the three-term recursion for orthogonal polynomials in one variable. -/
theorem theorem_14_2_3 {n : ℕ} {j : Fin d} {p : MvPolynomial (Fin d) ℝ}
    (hp : hw.toL2 p ∈ orthPolySpace hw n) :
    hw.toL2 (MvPolynomial.X j * p) ∈ (Finset.Icc (n - 1) (n + 1)).sup (orthPolySpace hw) := by
  have hdeg : p.totalDegree ≤ n := by
    obtain ⟨r, hr, hre⟩ := hw.mem_polyLE_iff.1 (orthPolySpace_le hw n hp)
    rwa [hw.toL2_injective hre] at hr
  have hmul : ∀ r : MvPolynomial (Fin d) ℝ,
      (MvPolynomial.X j * r).totalDegree ≤ 1 + r.totalDegree :=
    fun r => le_trans (MvPolynomial.totalDegree_mul _ _) (by simp)
  refine mem_finsetSup_Icc_of_mem hw.monotone_polyLE (fun _ => inferInstance)
    (hw.toL2_mem_polyLE ((hmul p).trans (by omega))) fun k hk g hg => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨q, hq, rfl⟩ := hw.mem_polyLE_iff.1 hg
  rw [← exercise_14_2_1 hw j q p]
  exact ((mem_orthPolySpace_succ_iff hw).1 hp).2 _
    (hw.toL2_mem_polyLE ((hmul q).trans (by omega)))

/-- **Theorem 14.2.3** of [han2009theoretical], uniqueness. Let $\mu$ be a weight for polynomials on
$\mathbb{R}^d$ and $m \in \mathbb{N}$. If $a, a' \in \mathcal{V}_m^d$,
$b, b' \in \mathcal{V}_{m+1}^d$, $c, c' \in \mathcal{V}_{m+2}^d$ and $a + b + c = a' + b' + c'$,
then $a = a'$, $b = b'$ and $c = c'$.

This is the coordinate-free content of the uniqueness of the matrices $A_{n,j}$, $B_{n,j}$ and
$C_{n,j}$. It follows from the orthogonality of distinct components.

**Reading.** Uniqueness of the adjacent three components instead of uniqueness of the explicit
matrices.
-/
theorem theorem_14_2_3_unique {m : ℕ} {a b c a' b' c' : Lp ℝ 2 μ}
    (ha : a ∈ orthPolySpace hw m) (hb : b ∈ orthPolySpace hw (m + 1))
    (hc : c ∈ orthPolySpace hw (m + 2)) (ha' : a' ∈ orthPolySpace hw m)
    (hb' : b' ∈ orthPolySpace hw (m + 1)) (hc' : c' ∈ orthPolySpace hw (m + 2))
    (h : a + b + c = a' + b' + c') : a = a' ∧ b = b' ∧ c = c' := by
  have hz : (a - a') + (b - b') + (c - c') = 0 := by
    rw [show a - a' + (b - b') + (c - c') = a + b + c - (a' + b' + c') by abel, h, sub_self]
  have key : ∀ {i k : ℕ} {u v : Lp ℝ 2 μ}, i ≠ k → u ∈ orthPolySpace hw i →
      v ∈ orthPolySpace hw k → inner ℝ u v = 0 := fun hik hu hv =>
    (Submodule.mem_orthogonal' _ _).1 (Submodule.isOrtho_iff_le.1 (lemma_14_2_1_isOrtho hw hik) hu)
      _ hv
  have hsub : ∀ {i : ℕ} {u v : Lp ℝ 2 μ}, u ∈ orthPolySpace hw i → v ∈ orthPolySpace hw i →
      u - v ∈ orthPolySpace hw i := fun hu hv => Submodule.sub_mem _ hu hv
  have hda := hsub ha ha'
  have hdb := hsub hb hb'
  have hdc := hsub hc hc'
  refine ⟨sub_eq_zero.1 ?_, sub_eq_zero.1 ?_, sub_eq_zero.1 ?_⟩ <;>
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
  · have := congrArg (fun v => inner ℝ (a - a') v) hz
    simpa [inner_add_right, key (by omega) hda hdb, key (by omega) hda hdc] using this
  · have := congrArg (fun v => inner ℝ (b - b') v) hz
    simpa [inner_add_right, key (by omega) hdb hda, key (by omega) hdb hdc] using this
  · have := congrArg (fun v => inner ℝ (c - c') v) hz
    simpa [inner_add_right, key (by omega) hdc hda, key (by omega) hdc hdb] using this

/-- **Equation (14.2.12)** of [han2009theoretical]. Let $\mu$ be a weight for polynomials on
$\mathbb{R}^d$. For every $n \in \mathbb{N}$ and $f \in L^2(\mu)$, the orthogonal projection
$P_n$ onto $\Pi_n^d$ satisfies $$P_n f = \sum_{m=0}^{n} Q_m f,$$ where $Q_m$ is the orthogonal
projection onto $\mathcal{V}_m^d$.

In an orthonormal basis $\{\varphi_{m,\ell}\}_\ell$ of each $\mathcal{V}_m^d$, the $m$-th
summand is $\sum_\ell (f, \varphi_{m,\ell}) \varphi_{m,\ell}$, so this is the expansion of the
book without a choice of basis.

**Reading.** Basis-free sum of degree-layer projections for general weight measures.
-/
theorem equation_14_2_12 (n : ℕ) (f : Lp ℝ 2 μ) :
    (hw.polyLE n).starProjection f =
      ∑ m ∈ Finset.range (n + 1), (orthPolySpace hw m).starProjection f :=
  starProjection_eq_sum_orthogonalComponent hw.monotone_polyLE n f

/-- **Equation (14.2.12)** of [han2009theoretical], best approximation. Let $\mu$ be a weight for
polynomials on $\mathbb{R}^d$. For every $n \in \mathbb{N}$ and $f \in L^2(\mu)$, the orthogonal
projection $P_n f$ is a best approximation to $f$ from $\Pi_n^d$ in $L^2(\mu)$:
$\|f - P_n f\| \le \|f - p\|$ for every $p \in \Pi_n^d$.

**Reading.** Best L² approximation in any admissible weight space.
-/
theorem equation_14_2_12_isBestApprox (n : ℕ) (f : Lp ℝ 2 μ) :
    IsBestApprox (hw.polyLE n : Set (Lp ℝ 2 μ)) f ((hw.polyLE n).starProjection f) :=
  isBestApprox_starProjection _ f

/-- **Equation (14.2.13)** of [han2009theoretical] (Lebesgue lemma). Let $D \subseteq \mathbb{R}^d$
be compact, let $n \in \mathbb{N}$, and let $P$ be a bounded projection on $C(D)$ whose range is
the space of the restrictions to $D$ of the polynomials in $\Pi_n^d$. Then for every
$f \in C(D)$, $$\|f - P f\|_\infty \le (1 + \|P\|) \, E_n(f).$$ So $P f$ is a quasi-best
approximation, with the constant $1 + \|P\|$.

**Generalization.** The book states this for $D = \mathbb{B}_d$. It holds for every compact $D$.

The proof is the backbone `norm_sub_apply_le_of_isIdempotentElem`, with the subspace
`Approximation.mvPolyLE D n`. Together with Theorem 14.2.4, which is not formalized, it gives
Theorem 14.2.5. -/
theorem equation_14_2_13 {D : Set (Fin d → ℝ)} [CompactSpace D] (n : ℕ) (P : C(D, ℝ) →L[ℝ] C(D, ℝ))
    (hP : IsIdempotentElem P)
    (hr : LinearMap.range (P : C(D, ℝ) →ₗ[ℝ] C(D, ℝ)) = mvPolyLE D n) (f : C(D, ℝ)) :
    ‖f - P f‖ ≤ (1 + ‖P‖) * minimaxError n f := by
  rw [minimaxError, ← hr]
  exact norm_sub_apply_le_of_isIdempotentElem P hP f

/-! ### Example 14.2.2: the Logan–Shepp ridge polynomials -/

section Ridge

open scoped Real

/-- The closed unit ball $\mathbb{B}_2$ of the plane is the closed unit disk `Quadrature.unitDisk`
of `Numlib.Approximation.DiskQuadrature`, on which the chord decomposition of the integral is
proved. -/
theorem unitBall_two_eq_unitDisk : unitBall 2 = Quadrature.unitDisk := by
  ext x
  simp [unitBall, Quadrature.unitDisk, Fin.sum_univ_two]

/-- **Example 14.2.2** of [han2009theoretical], the ridge polynomials. For $n, k \in \mathbb{N}$ and
$h = \pi / (n + 1)$, the **ridge polynomial** $\varphi_{n,k}$ is the class in
$L^2(\mathbb{B}_2)$ of $$\varphi_{n,k}(x, y) = \frac{1}{\sqrt{\pi}} \, U_n\bigl(x \cos(k h) + y
\sin(k h)\bigr),$$ where $U_n$ is the Chebyshev polynomial of the second kind.

The polynomial is the backbone `Approximation.ridgePoly`. -/
noncomputable def ridgeL2 (n k : ℕ) : Lp ℝ 2 (volume.restrict (unitBall 2)) :=
  (isMvWeight_ballVolume 2).toL2 (ridgePoly n (k * (π / (n + 1))))

/-- **Example 14.2.2** of [han2009theoretical], the inner products. For $j \le n$ and $k \le m$,
$$(\varphi_{n,j}, \varphi_{m,k}) = \delta_{nm} \delta_{jk}$$ in $L^2(\mathbb{B}_2)$.

Both cases come from the chord decomposition of the integral over the disk in the backbone: for
$n \neq m$ the integral vanishes, and within a degree the equispaced directions
$k \pi / (n + 1)$ are the zeros of $U_n(\cos \cdot)$ off the diagonal. -/
theorem inner_ridgeL2 {n m j k : ℕ} (hj : j ≤ n) (hk : k ≤ m) :
    inner ℝ (ridgeL2 n j) (ridgeL2 m k) = if n = m then (if j = k then 1 else 0) else 0 := by
  rw [ridgeL2, ridgeL2, IsMvWeight.inner_toL2, unitBall_two_eq_unitDisk]
  rcases eq_or_ne n m with rfl | h
  · rw [ite_eq_left rfl]
    exact integral_unitDisk_ridgePoly_mul_angle hj hk
  · rw [integral_unitDisk_ridgePoly_mul, ite_eq_right h, ite_eq_right h]

/-- For all $n, k \in \mathbb{N}$, the ridge polynomial $\varphi_{n,k}$ lies in $\Pi_n^2$. It
supports Example 14.2.2. -/
theorem ridgeL2_mem_polyLE (n k : ℕ) : ridgeL2 n k ∈ (isMvWeight_ballVolume 2).polyLE n :=
  IsMvWeight.toL2_mem_polyLE _ (totalDegree_ridgePoly_le _ _)

/-- **Example 14.2.2** of [han2009theoretical], the orthonormality. For every $n \in \mathbb{N}$,
the $n + 1$ ridge polynomials $\varphi_{n,0}, \dots, \varphi_{n,n}$ are an orthonormal family in
$L^2(\mathbb{B}_2)$. -/
theorem orthonormal_ridgeL2 (n : ℕ) : Orthonormal ℝ fun k : Fin (n + 1) => ridgeL2 n k := by
  rw [orthonormal_iff_ite]
  intro j k
  rw [inner_ridgeL2 (Nat.lt_succ_iff.1 j.isLt) (Nat.lt_succ_iff.1 k.isLt), ite_eq_left rfl]
  simp [Fin.ext_iff]

/-- **Example 14.2.2** of [han2009theoretical], the spanning part. For every $n \in \mathbb{N}$, the
ridge polynomials $\varphi_{n,0}, \dots, \varphi_{n,n}$ span $\mathcal{V}_n^2$ for the volume of
$\mathbb{B}_2$.

The proof is by induction on $n$. A ridge polynomial of degree $n$ lies in $\Pi_n^2$ and is
orthogonal to every ridge polynomial of lower degree; by the induction hypothesis and Lemma
14.2.1 these span $\Pi_{n-1}^2$, so it lies in $\mathcal{V}_n^2$. The $n + 1$ ridge polynomials
of degree $n$ are orthonormal, hence independent, and $\dim \mathcal{V}_n^2 = n + 1$, so they
span $\mathcal{V}_n^2$. -/
theorem span_ridgeL2 (n : ℕ) :
    Submodule.span ℝ (Set.range fun k : Fin (n + 1) => ridgeL2 n k)
      = orthPolySpace (isMvWeight_ballVolume 2) n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    have hmem : ∀ k : Fin (n + 1), ridgeL2 n k ∈ orthPolySpace (isMvWeight_ballVolume 2) n := by
      intro k
      match n with
      | 0 => rw [orthPolySpace_zero]; exact ridgeL2_mem_polyLE 0 k
      | m + 1 =>
        rw [mem_orthPolySpace_succ_iff]
        refine ⟨ridgeL2_mem_polyLE _ _, fun g hg => ?_⟩
        have hsub : (isMvWeight_ballVolume 2).polyLE m
            ≤ (Submodule.span ℝ {ridgeL2 (m + 1) (k : ℕ)})ᗮ := by
          rw [← lemma_14_2_1 (isMvWeight_ballVolume 2) m]
          refine Finset.sup_le fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [← IH i (by omega), Submodule.span_le]
          rintro _ ⟨l, rfl⟩
          rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
            inner_ridgeL2 (Nat.lt_succ_iff.1 k.isLt) (Nat.lt_succ_iff.1 l.isLt),
            ite_eq_right (by omega)]
        rw [real_inner_comm]
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hsub hg)
    have hle : Submodule.span ℝ (Set.range fun k : Fin (n + 1) => ridgeL2 n k)
        ≤ orthPolySpace (isMvWeight_ballVolume 2) n := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hmem k
    have hfd : FiniteDimensional ℝ (orthPolySpace (isMvWeight_ballVolume 2) n) :=
      Submodule.finiteDimensional_of_le (orthPolySpace_le (isMvWeight_ballVolume 2) n)
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [finrank_orthPolySpace_two (isMvWeight_ballVolume 2) n,
      finrank_span_eq_card (orthonormal_ridgeL2 n).linearIndependent]
    simp

/-- **Example 14.2.2** of [han2009theoretical]. For every $n \in \mathbb{N}$, with
$h = \pi / (n + 1)$, the ridge polynomials $$\varphi_{n,k}(x, y) = \frac{1}{\sqrt{\pi}} \,
U_n\bigl(x \cos(k h) + y \sin(k h)\bigr), \qquad k = 0, \dots, n,$$ are an orthonormal basis of
$\mathcal{V}_n^2$ for the inner product $(f, g) = \int_{\mathbb{B}_2} f g \, dx$.

The basis property is stated as orthonormality together with the equality of the span with
$\mathcal{V}_n^2$. -/
theorem example_14_2_2 (n : ℕ) :
    (Orthonormal ℝ fun k : Fin (n + 1) => ridgeL2 n k) ∧
      Submodule.span ℝ (Set.range fun k : Fin (n + 1) => ridgeL2 n k)
        = orthPolySpace (isMvWeight_ballVolume 2) n :=
  ⟨orthonormal_ridgeL2 n, span_ridgeL2 n⟩

/-- **Example 14.2.2** of [han2009theoretical], the consequence for $\Pi_N^2$. For every
$N \in \mathbb{N}$, the ridge polynomials $\{\varphi_{m,k} : 0 \le k \le m \le N\}$ span
$\Pi_N^2$ in $L^2(\mathbb{B}_2)$. By `AtkinsonHan.Chapter14.inner_ridgeL2` they are orthonormal,
so they are an orthonormal basis of $\Pi_N^2$. -/
theorem example_14_2_2_polyLE (N : ℕ) :
    Submodule.span ℝ {f | ∃ m ≤ N, ∃ k ≤ m, f = ridgeL2 m k}
      = (isMvWeight_ballVolume 2).polyLE N := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro f ⟨m, hm, k, -, rfl⟩
    exact (isMvWeight_ballVolume 2).monotone_polyLE hm (ridgeL2_mem_polyLE m k)
  · rw [← lemma_14_2_1 (isMvWeight_ballVolume 2) N]
    refine Finset.sup_le fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [← span_ridgeL2 m]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨m, by omega, (k : ℕ), Nat.lt_succ_iff.1 k.isLt, rfl⟩

end Ridge

end AtkinsonHan.Chapter14
