/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.Taylor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Conn, Gould and Toint, Section 9.4: Newton interpolation models

This module formalizes the Newton interpolation models of Section 9.4 of [conn2000trust], which give
conditional models without derivatives. The interpolation points are grouped into blocks
$y_{l,1}, \dots, y_{l,n_l}$, for $l = 0, 1, \dots$, and each point $y_{l,i}$ has a fundamental
function $N_{l,i}$. The family is a **Newton fundamental family** up to degree $d$ (9.4.4) if
$N_{l,i}(y_{l,j}) = \delta_{ij}$ and $N_{l,i}$ vanishes on all points of earlier blocks. The
generalized finite differences are $\lambda_0 = f$ and
$$\lambda_{l+1}(x) = \lambda_l(x) - \sum_i \lambda_l(y_{l,i}) N_{l,i}(x) \qquad (9.4.8),$$
and the Newton model (9.4.9) is $m(x) = \sum_{l=0}^{d} \sum_i \lambda_l(y_{l,i}) N_{l,i}(x)$. The
model interpolates $f$ at all points (Theorem 9.4.1), and Algorithm 9.4.2 computes its coefficients
from the function values. The module also formalizes the interpolation matrix (9.4.3), the
elimination with pivots of Algorithm 9.4.1 (Theorem 9.4.2), a bounded graded Newton family on a
Euclidean ball (Theorem 9.4.3), and a model error bound for Theorem 9.4.4.

## Main definitions

* Equation (9.4.4), `ConnGouldToint.Chapter09.IsNewtonFundamentalFamily`: the Newton conditions on
  the blocks up to degree $d$.
* Equation (9.4.8), `ConnGouldToint.Chapter09.generalizedFiniteDifference`: the generalized finite
  differences $\lambda_l$.
* Equation (9.4.13), `ConnGouldToint.Chapter09.newtonInterpolationCoefficient`: the coefficient
  $\lambda_l(y_{l,i})$.
* Algorithm 9.4.2, `ConnGouldToint.Chapter09.newtonDifferenceTable`: the table of values after $k$
  passes of the algorithm.
* Algorithm 9.4.2, `ConnGouldToint.Chapter09.algorithm_9_4_2`: the table after $d$ passes on the
  blocks $0, \dots, d$.
* Equation (9.4.9), `ConnGouldToint.Chapter09.newtonInterpolationModel`: the Newton interpolation
  model of degree $d$.
* Equation (9.4.3), `ConnGouldToint.Chapter09.interpolationMatrix`: the matrix of the interpolation
  equations.
* Equation (9.4.3), `ConnGouldToint.Chapter09.IsPoised`: the interpolation matrix has nonzero
  determinant.
* Algorithm 9.4.1, `ConnGouldToint.Chapter09.interpolationPivots`: the list of pivots of the
  elimination with a given row selector.
* Equation (9.4.7), `ConnGouldToint.Chapter09.HasPivotThreshold`: every pivot has absolute value at
  least $\theta > 0$.

## Main results

* Algorithm 9.4.2, `ConnGouldToint.Chapter09.newtonDifferenceTable_eq_finiteDifference`: after $k$
  passes, the table holds the finite differences of order $\min\{k, l\}$.
* Algorithm 9.4.2, `ConnGouldToint.Chapter09.algorithm_9_4_2_eq_coefficient`: the algorithm returns
  the coefficients (9.4.13).
* Equation (9.4.11), `ConnGouldToint.Chapter09.generalizedFiniteDifference_eq_sub_sum`: $\lambda_j$
  is $f$ minus the partial Newton model.
* Theorem 9.4.1, `ConnGouldToint.Chapter09.theorem_9_4_1`: the Newton model interpolates $f$ at all
  points of the blocks up to degree $d$.
* Algorithm 9.4.2, `ConnGouldToint.Chapter09.algorithm_9_4_2_interpolates`: the model with the
  computed coefficients interpolates $f$.
* `ConnGouldToint.Chapter09.generalizedFiniteDifference_sub`: the finite differences are linear in
  $f$.
* `ConnGouldToint.Chapter09.abs_generalizedFiniteDifference_le`: uniform bounds on $f$ and on the
  fundamental functions bound the finite differences.
* Theorem 9.4.4, `ConnGouldToint.Chapter09.theorem_9_4_4_of_uniform_newton_bound`: a model that
  reproduces affine functions, with uniformly bounded fundamental functions on the ball, has error
  of order $\delta^2$.
* Equation (9.4.5), `ConnGouldToint.Chapter09.signedPivotNormalization_at_pivot`: division by the
  signed pivot gives the value $1$ at the pivot point.
* Equation (9.4.5), `ConnGouldToint.Chapter09.absolutePivotNormalization_counterexample`: division
  by the absolute value of a negative pivot does not give $1$.
* Equation (9.4.6), `ConnGouldToint.Chapter09.newtonElimination_at_pivot`: the update makes the
  other functions vanish at the pivot point.
* Theorem 9.4.2, `ConnGouldToint.Chapter09.theorem_9_4_2`: the interpolation set is poised if and
  only if all pivots are nonzero.
* Algorithm 9.4.1, `ConnGouldToint.Chapter09.exists_maxMagnitudePivotSelector`: a row selector of
  maximal magnitude exists.
* Theorem 9.4.3, `ConnGouldToint.Chapter09.theorem_9_4_3`: a lattice in a Euclidean ball carries a
  graded Newton family of polynomials with a uniform bound.
* Theorem 9.4.3, `ConnGouldToint.Chapter09.theorem_9_4_3_basis`: this family is a basis of the
  polynomials of total degree at most $d$.

## Implementation notes

* The fundamental functions $N_{l,i}$ are arbitrary functions $E \to \mathbb{R}$. Theorem 9.4.1 and
  Algorithm 9.4.2 use only the evaluation identities (9.4.4), so they also apply to basis functions
  that are not polynomials.
* Block $l$ has $n_l$ points, indexed by `Fin (n l)`, and the blocks are indexed by all of
  $\mathbb{N}$. The degree $d$ selects the blocks $0, \dots, d$.
* Theorem 9.4.3 is proved by an explicit construction. The points are the multi-indices of total
  degree at most $d$, scaled by $\delta / (d + 1)$ and shifted to the center, and the polynomials
  are products of one-dimensional Lagrange factors.

## Deviations from the source

* **Theorem 9.4.1** (reading). The interpolation result uses the defining nodal identities
  for abstract functions on a type. It does not construct the polynomial family.
* **Theorems 9.4.2 and 9.4.3** (reading). The poisedness criterion is stated for matrix pivots
  with a maximum-magnitude row selector. The complete Newton family is built from a simplex
  of lattice points, with a uniform bound from the product of one-dimensional Lagrange
  factors. The book constructs the points by maximizing the successive pivot polynomials.
* **Equation (9.4.5)** (correction). The normalization divides by the signed pivot, so that the
  diagonal value is $1$. Division by the absolute value fails for a negative pivot. See
  `ConnGouldToint.Chapter09.absolutePivotNormalization_counterexample`.
* **Equation (9.4.6)** (correction). The update is applied after the normalization (9.4.5), so that
  it makes the other functions vanish at the pivot point. See
  `ConnGouldToint.Chapter09.newtonElimination_at_pivot`.
* **Theorem 9.4.4** (correction). The model error bound uses affine reproduction and uniform bounds
  on all Newton blocks on the ball. The bounds on adjacent blocks and on the last block do not
  suffice: an incomplete quadratic example with five points violates (9.4.21) for every uniform
  constant. See `ConnGouldToint.Chapter09.theorem_9_4_4_of_uniform_newton_bound` and
  `ConnGouldToint.Chapter09.theorem_9_4_4_incompleteQuadratic_counterexample`.
-/

namespace ConnGouldToint.Chapter09

variable {E : Type*} {n : ℕ → ℕ}

/-- **Equation (9.4.4)** of [conn2000trust]. Let blocks of points $y_{l,i} \in E$ and functions
$N_{l,i} : E \to \mathbb{R}$ be given, for $l \in \mathbb{N}$ and $1 \le i \le n_l$, and let
$d \in \mathbb{N}$. They form a **Newton fundamental family** up to degree $d$ if for all
$l \le d$:

* $N_{l,i}(y_{l,j}) = 1$ if $i = j$ and $0$ otherwise, and
* $N_{l,i}(y_{j,k}) = 0$ for every earlier block $j < l$ and all $i, k$.

**Reading.** Nodal conditions for abstract function families, without polynomial-degree constraints.
-/
def IsNewtonFundamentalFamily (y : (l : ℕ) → Fin (n l) → E)
    (N : (l : ℕ) → Fin (n l) → E → ℝ) (d : ℕ) : Prop :=
  (∀ l ≤ d, ∀ i j, N l i (y l j) = if i = j then 1 else 0) ∧
  ∀ l ≤ d, ∀ j < l, ∀ i k, N l i (y j k) = 0

/-- **Equation (9.4.8)** of [conn2000trust]. Given $f : E \to \mathbb{R}$, points $y_{l,i}$ and
functions $N_{l,i}$, the **generalized finite differences** are $\lambda_0 = f$ and
$$\lambda_{l+1}(x) = \lambda_l(x) - \sum_{i=1}^{n_l} \lambda_l(y_{l,i}) N_{l,i}(x).$$
-/
noncomputable def generalizedFiniteDifference (f : E → ℝ) (y : (l : ℕ) → Fin (n l) → E)
    (N : (l : ℕ) → Fin (n l) → E → ℝ) : ℕ → E → ℝ
  | 0 => f
  | l + 1 => fun x ↦ generalizedFiniteDifference f y N l x -
      ∑ i, generalizedFiniteDifference f y N l (y l i) * N l i x

/-- **Equation (9.4.13)** of [conn2000trust]. The **Newton coefficient** at the point $y_{l,i}$ is
the generalized finite difference $\lambda_l(y_{l,i})$ (9.4.8). -/
noncomputable def newtonInterpolationCoefficient (f : E → ℝ)
    (y : (l : ℕ) → Fin (n l) → E) (N : (l : ℕ) → Fin (n l) → E → ℝ)
    (l : ℕ) (i : Fin (n l)) : ℝ :=
  generalizedFiniteDifference f y N l (y l i)

/-- **Algorithm 9.4.2** of [conn2000trust], Steps 0–1. Given values $v_{l,i} \in \mathbb{R}$, points
$y_{l,i}$ and functions $N_{l,i}$, the **difference table** after $k$ passes is defined by
$T_0(l, i) = v_{l,i}$ and
$$T_{k+1}(l, i) = \begin{cases} T_k(l, i) - \sum_j T_k(k, j) N_{k,j}(y_{l,i}) & \text{if } k <
  l, \\ T_k(l, i) & \text{otherwise.} \end{cases}$$

Pass $k + 1$ uses the finished block $k$ to update every later block, and leaves the finished
blocks unchanged. The table uses only the values at the given points. -/
noncomputable def newtonDifferenceTable
    (values : (l : ℕ) → Fin (n l) → ℝ) (y : (l : ℕ) → Fin (n l) → E)
    (N : (l : ℕ) → Fin (n l) → E → ℝ) :
    ℕ → (l : ℕ) → Fin (n l) → ℝ
  | 0 => values
  | k + 1 => fun l i ↦
      if k < l then
        newtonDifferenceTable values y N k l i -
          ∑ j, newtonDifferenceTable values y N k k j * N k j (y l i)
      else newtonDifferenceTable values y N k l i

/-- **Algorithm 9.4.2** of [conn2000trust], loop invariant. If the input values are
$v_{l,i} = f(y_{l,i})$, then after $k$ passes
$$T_k(l, i) = \lambda_{\min\{k, l\}}(y_{l,i}).$$
So the later blocks hold the residuals of order $k$, and the finished blocks keep their
generalized finite differences. -/
theorem newtonDifferenceTable_eq_finiteDifference (f : E → ℝ)
    (y : (l : ℕ) → Fin (n l) → E) (N : (l : ℕ) → Fin (n l) → E → ℝ)
    (k l : ℕ) (i : Fin (n l)) :
    newtonDifferenceTable (fun j a ↦ f (y j a)) y N k l i =
      generalizedFiniteDifference f y N (min k l) (y l i) := by
  induction k generalizing l with
  | zero => simp [newtonDifferenceTable, generalizedFiniteDifference]
  | succ k ih =>
    by_cases h : k < l
    · have hkl : k + 1 ≤ l := Nat.succ_le_of_lt h
      simp only [newtonDifferenceTable, ite_eq_left h, ih,
        min_eq_left h.le, min_self, min_eq_left hkl, generalizedFiniteDifference]
    · have hle : l ≤ k := le_of_not_gt h
      simp only [newtonDifferenceTable, ite_eq_right h, ih,
        min_eq_right hle, min_eq_right (hle.trans (Nat.le_succ _))]

/-- **Algorithm 9.4.2** of [conn2000trust]. Given values $v_{l,i}$, points $y_{l,i}$, functions
$N_{l,i}$ and a degree $d$, the algorithm returns the difference table $T_d(l, i)$ after $d$
passes, on the blocks $l = 0, \dots, d$. -/
noncomputable def algorithm_9_4_2 (values : (l : ℕ) → Fin (n l) → ℝ)
    (y : (l : ℕ) → Fin (n l) → E) (N : (l : ℕ) → Fin (n l) → E → ℝ)
    (d : ℕ) (l : Fin (d + 1)) (i : Fin (n l)) : ℝ :=
  newtonDifferenceTable values y N d l i

/-- **Algorithm 9.4.2** of [conn2000trust], output. If the input values are $f(y_{l,i})$, the
algorithm returns the Newton coefficients (9.4.13): $T_d(l, i) = \lambda_l(y_{l,i})$ for all
$l \le d$ and all $i$.

The identity holds for every $f$, points and functions, without the Newton conditions (9.4.4). -/
theorem algorithm_9_4_2_eq_coefficient (f : E → ℝ) (y : (l : ℕ) → Fin (n l) → E)
    (N : (l : ℕ) → Fin (n l) → E → ℝ) (d : ℕ) (l : Fin (d + 1)) (i : Fin (n l)) :
    algorithm_9_4_2 (fun j a ↦ f (y j a)) y N d l i =
      newtonInterpolationCoefficient f y N l i := by
  rw [algorithm_9_4_2, newtonDifferenceTable_eq_finiteDifference,
    min_eq_right (Nat.le_of_lt_succ l.isLt), newtonInterpolationCoefficient]

/-- **Equation (9.4.9)** of [conn2000trust]. The **Newton interpolation model** of degree $d$ for
$f$ is
$$m(x) = \sum_{l=0}^{d} \sum_{i=1}^{n_l} \lambda_l(y_{l,i}) N_{l,i}(x),$$
with the Newton coefficients (9.4.13) and the given functions $N_{l,i}$. -/
noncomputable def newtonInterpolationModel (f : E → ℝ)
    (y : (l : ℕ) → Fin (n l) → E) (N : (l : ℕ) → Fin (n l) → E → ℝ) (d : ℕ) (x : E) : ℝ :=
  ∑ l ∈ Finset.range (d + 1), ∑ i, newtonInterpolationCoefficient f y N l i * N l i x

/-- **Equation (9.4.11)** of [conn2000trust]. For every $x \in E$ and $j \in \mathbb{N}$,
$$\lambda_j(x) = f(x) - \sum_{l=0}^{j-1} \sum_{i=1}^{n_l} \lambda_l(y_{l,i}) N_{l,i}(x).$$
This follows from the recursion (9.4.8) by telescoping. -/
theorem generalizedFiniteDifference_eq_sub_sum (f : E → ℝ) (y : (l : ℕ) → Fin (n l) → E)
    (N : (l : ℕ) → Fin (n l) → E → ℝ) (x : E) (j : ℕ) :
    generalizedFiniteDifference f y N j x =
      f x - ∑ l ∈ Finset.range j, ∑ i, generalizedFiniteDifference f y N l (y l i) * N l i x := by
  induction j with
  | zero => simp [generalizedFiniteDifference]
  | succ j ih =>
    simp only [generalizedFiniteDifference, Finset.sum_range_succ, sub_add_eq_sub_sub]
    rw [ih]

/-- **Theorem 9.4.1** of [conn2000trust]. If the points $y_{l,i}$ and the functions $N_{l,i}$ form a
Newton fundamental family up to degree $d$ (9.4.4), then the Newton model (9.4.9) interpolates
$f$: $m(y_{j,k}) = f(y_{j,k})$ for all $j \le d$ and all $k$.

The proof uses only the evaluation identities (9.4.4), so it applies to any functions $N_{l,i}$
with these identities.

**Reading.** Interpolation identity for abstract nodal functions without polynomial assumptions.
-/
theorem theorem_9_4_1 (f : E → ℝ) (y : (l : ℕ) → Fin (n l) → E)
    (N : (l : ℕ) → Fin (n l) → E → ℝ) {d : ℕ} (hN : IsNewtonFundamentalFamily y N d) :
    ∀ j ≤ d, ∀ k, newtonInterpolationModel f y N d (y j k) = f (y j k) := by
  intro j hj k
  let diff := generalizedFiniteDifference f y N
  have hdiag : (∑ i, diff j (y j i) * N j i (y j k)) = diff j (y j k) := by
    rw [Finset.sum_eq_single k]
    · rw [hN.1 j hj, ite_eq_left rfl, mul_one]
    · intro i _ hik
      rw [hN.1 j hj, ite_eq_right hik, mul_zero]
    · simp
  have htruncate (r : ℕ) (hjr : j ≤ r) (hr : r ≤ d) :
      newtonInterpolationModel f y N r (y j k) = newtonInterpolationModel f y N j (y j k) := by
    induction r, hjr using Nat.le_induction with
    | base => rfl
    | succ r hjr ih =>
      unfold newtonInterpolationModel
      rw [Finset.sum_range_succ]
      have hz (i : Fin (n (r + 1))) : N (r + 1) i (y j k) = 0 :=
        hN.2 _ hr _ (Nat.lt_succ_of_le hjr) i k
      simp only [hz, mul_zero, Finset.sum_const_zero, add_zero]
      exact ih (Nat.le_of_succ_le hr)
  rw [htruncate d hj le_rfl, newtonInterpolationModel, Finset.sum_range_succ]
  change (∑ l ∈ Finset.range j, ∑ i, diff l (y l i) * N l i (y j k)) +
    (∑ i, diff j (y j i) * N j i (y j k)) = f (y j k)
  rw [hdiag]
  dsimp only [diff]
  rw [generalizedFiniteDifference_eq_sub_sum f y N (y j k) j]
  ring

/-- **Algorithm 9.4.2** of [conn2000trust], interpolation. If the points and functions form a Newton
fundamental family up to degree $d$, the coefficients $T_d(j, a)$ returned for the values
$f(y_{j,a})$ give an interpolating model:
$$\sum_{j=0}^{d} \sum_a T_d(j, a) N_{j,a}(y_{l,i}) = f(y_{l,i}) \quad \text{for all } l \le d
  \text{ and all } i.$$

**Reading.** Assembled result interpolates under abstract nodal identities.
-/
theorem algorithm_9_4_2_interpolates (f : E → ℝ) (y : (l : ℕ) → Fin (n l) → E)
    (N : (l : ℕ) → Fin (n l) → E → ℝ) {d : ℕ} (hN : IsNewtonFundamentalFamily y N d)
    (l : Fin (d + 1)) (i : Fin (n l)) :
    (∑ j : Fin (d + 1), ∑ a,
      algorithm_9_4_2 (fun j a ↦ f (y j a)) y N d j a * N j a (y l i)) = f (y l i) := by
  simp_rw [algorithm_9_4_2_eq_coefficient]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ ∑ a, newtonInterpolationCoefficient f y N j a * N j a (y l i))]
  exact theorem_9_4_1 f y N hN l (Nat.le_of_lt_succ l.isLt) i

/-- The generalized finite differences (9.4.8) are linear in the function: for
$f, g : E \to \mathbb{R}$, the difference of order $j$ of $f - g$ is the difference of order $j$
of $f$ minus that of $g$. -/
theorem generalizedFiniteDifference_sub (f g : E → ℝ)
    (y : (l : ℕ) → Fin (n l) → E) (N : (l : ℕ) → Fin (n l) → E → ℝ)
    (j : ℕ) (x : E) :
    generalizedFiniteDifference (fun z ↦ f z - g z) y N j x =
      generalizedFiniteDifference f y N j x - generalizedFiniteDifference g y N j x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    simp only [generalizedFiniteDifference, ih, sub_mul, Finset.sum_sub_distrib]
    ring

/-- Let $S \subseteq E$, $B \ge 0$ and $K \ge 0$, with $|f(z)| \le B$ for all $z \in S$. Suppose
that for all $l < j$ the points $y_{l,i}$ lie in $S$ and $|N_{l,i}(z)| \le K$ for all $z \in S$.
Then for every $x \in S$,
$$|\lambda_j(x)| \le B \prod_{l=0}^{j-1} (1 + n_l K).$$

**Correction.** Uses uniform bounds on all block functions in the corrected error analysis.
-/
theorem abs_generalizedFiniteDifference_le {f : E → ℝ}
    {y : (l : ℕ) → Fin (n l) → E} {N : (l : ℕ) → Fin (n l) → E → ℝ}
    {S : Set E} {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hf : ∀ z ∈ S, |f z| ≤ B) {j : ℕ}
    (hy : ∀ l < j, ∀ i, y l i ∈ S)
    (hN : ∀ l < j, ∀ i, ∀ z ∈ S, |N l i z| ≤ K) {x : E} (hx : x ∈ S) :
    |generalizedFiniteDifference f y N j x| ≤
      B * ∏ l ∈ Finset.range j, (1 + (n l : ℝ) * K) := by
  induction j generalizing x with
  | zero => simpa [generalizedFiniteDifference] using hf x hx
  | succ j ih =>
    let P := B * ∏ l ∈ Finset.range j, (1 + (n l : ℝ) * K)
    have hP : 0 ≤ P := by
      exact mul_nonneg hB (Finset.prod_nonneg fun _ _ ↦ by positivity)
    have hb (z : E) (hz : z ∈ S) : |generalizedFiniteDifference f y N j z| ≤ P :=
      ih (fun l hl ↦ hy l (Nat.lt_succ_of_lt hl))
        (fun l hl ↦ hN l (Nat.lt_succ_of_lt hl)) hz
    let v (i : Fin (n j)) := generalizedFiniteDifference f y N j (y j i) * N j i x
    have hsum : |∑ i, v i| ≤ (n j : ℝ) * (P * K) := by
      calc
        _ ≤ ∑ i, |v i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (n j), P * K := by
          apply Finset.sum_le_sum
          intro i _
          rw [show v i = generalizedFiniteDifference f y N j (y j i) * N j i x from rfl, abs_mul]
          exact mul_le_mul (hb _ (hy j (Nat.lt_succ_self j) i))
            (hN j (Nat.lt_succ_self j) i x hx) (abs_nonneg _) hP
        _ = _ := by simp
    change |generalizedFiniteDifference f y N j x - ∑ i, v i| ≤ _
    calc
      _ ≤ |generalizedFiniteDifference f y N j x| + |∑ i, v i| := abs_sub _ _
      _ ≤ P + (n j : ℝ) * (P * K) := add_le_add (hb x hx) hsum
      _ = _ := by rw [Finset.prod_range_succ]; dsimp [P]; ring

/-- **Theorem 9.4.4** of [conn2000trust], form with uniform bounds on all blocks. Let $F$ be a real
normed space and let $f : F \to \mathbb{R}$ be twice continuously differentiable. Let $x \in F$,
$\delta \ge 0$, $B \ge 0$ and $K \ge 0$, with $\|\nabla^2 f(z)\| \le B$ on the ball
$B(x, \delta)$. Suppose that for all $l \le d$ the points $y_{l,i}$ lie in the ball and
$|N_{l,i}(z)| \le K$ for all $z$ in the ball. Suppose also that the Newton model of degree $d$
reproduces affine functions: for every $a \in \mathbb{R}$ and continuous linear
$A : F \to \mathbb{R}$, the model of $w \mapsto a + A(w - x)$ is the same function. Then for all
$z$ in the ball
$$|f(z) - m(z)| \le \left(\frac{B}{2} \prod_{l=0}^{d} (1 + n_l K)\right) \delta^2.$$

**Correction.** This form uses uniform bounds on all Newton blocks on the ball. The printed
bounds on adjacent blocks and on the last block do not control the model error. An incomplete
quadratic example with five points satisfies them and violates (9.4.21) for every uniform
constant; see `ConnGouldToint.Chapter09.theorem_9_4_4_incompleteQuadratic_counterexample`.

Affine reproduction is the condition that the model is fully linear. The proof subtracts the
affine Taylor polynomial at $x$, which makes the error quadratic in the radius without a bound
on the gradient of $f$. -/
theorem theorem_9_4_4_of_uniform_newton_bound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ}
    (hf : ContDiff ℝ 2 f) {x : F} {δ B K : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z ∈ Metric.closedBall x δ, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B)
    {y : (l : ℕ) → Fin (n l) → F} {N : (l : ℕ) → Fin (n l) → F → ℝ} {d : ℕ}
    (hy : ∀ l ≤ d, ∀ i, y l i ∈ Metric.closedBall x δ)
    (hN : ∀ l ≤ d, ∀ i, ∀ z ∈ Metric.closedBall x δ, |N l i z| ≤ K)
    (haffine : ∀ a : ℝ, ∀ A : F →L[ℝ] ℝ, ∀ z,
      newtonInterpolationModel (fun w ↦ a + A (w - x)) y N d z = a + A (z - x)) :
    ∀ z ∈ Metric.closedBall x δ,
      |f z - newtonInterpolationModel f y N d z| ≤
        (B / 2 * ∏ l ∈ Finset.range (d + 1), (1 + (n l : ℝ) * K)) * δ ^ 2 := by
  intro z hz
  let a (w : F) := f x + fderiv ℝ f x (w - x)
  have hres (w : F) (hw : w ∈ Metric.closedBall x δ) :
      |f w - a w| ≤ (B / 2) * δ ^ 2 := by
    have hd := hf.fderiv_right (m := 1) (by norm_num)
    have ht := norm_sub_firstOrder_le_of_hessian_bound (f := f) (s := w - x)
      (convex_closedBall x δ) (Metric.mem_closedBall_self hδ)
      (by simpa only [add_comm x, sub_add_cancel] using hw)
      (fun w _ ↦ hf.differentiable (by norm_num) w)
      (fun w _ ↦ hd.differentiable (by norm_num) w) hH
    rw [Real.norm_eq_abs, add_comm x (w - x), sub_add_cancel] at ht
    have hn : ‖w - x‖ ≤ δ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    calc
      |f w - a w| ≤ (1 / 2 : ℝ) * B * ‖w - x‖ ^ 2 := ht
      _ ≤ (1 / 2 : ℝ) * B * δ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity)
      _ = _ := by ring
  have hb := abs_generalizedFiniteDifference_le (j := d + 1) (by positivity) hK hres
    (fun l hl ↦ hy l (Nat.le_of_lt_succ hl))
    (fun l hl ↦ hN l (Nat.le_of_lt_succ hl)) hz
  rw [generalizedFiniteDifference_sub] at hb
  have he (g : F → ℝ) : generalizedFiniteDifference g y N (d + 1) z =
      g z - newtonInterpolationModel g y N d z :=
    generalizedFiniteDifference_eq_sub_sum g y N z (d + 1)
  rw [he f, he a, haffine (f x) (fderiv ℝ f x) z, sub_self, sub_zero] at hb
  exact hb.trans_eq (by ring)

/-- **Equation (9.4.3)** of [conn2000trust]. For points $y_1, \dots, y_d \in E$ and functions
$P_1, \dots, P_d : E \to \mathbb{R}$, the **interpolation matrix** is the $d \times d$ matrix
with entries $P_j(y_i)$. -/
def interpolationMatrix {d : ℕ} (y : Fin d → E) (P : Fin d → E → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun i j ↦ P j (y i)

/-- **Equation (9.4.3)** of [conn2000trust], poisedness. A square interpolation set
$y_1, \dots, y_d$ is **poised** for $P_1, \dots, P_d$ if its interpolation matrix has nonzero
determinant. -/
def IsPoised {d : ℕ} (y : Fin d → E) (P : Fin d → E → ℝ) : Prop :=
  (interpolationMatrix y P).det ≠ 0

/-- **Equation (9.4.5)** of [conn2000trust]. Let $N : E \to \mathbb{R}$ and $y \in E$ with
$N(y) \neq 0$. The normalized function $x \mapsto N(x) / N(y)$ takes the value $1$ at $y$.

**Correction.** The source divides by the absolute value of the pivot $N(y)$. This gives $-1$ at
$y$ when $N(y) < 0$; see `ConnGouldToint.Chapter09.absolutePivotNormalization_counterexample`.
Division by the signed pivot gives the unit diagonal of the Newton conditions (9.4.4). -/
theorem signedPivotNormalization_at_pivot {N : E → ℝ} {y : E} (h : N y ≠ 0) :
    (fun x ↦ N x / N y) y = 1 :=
  div_self h

/-- **Equation (9.4.6)** of [conn2000trust]. Let $N, P : E \to \mathbb{R}$ and $y \in E$ with
$N(y) = 1$. The updated function $x \mapsto P(x) - P(y) N(x)$ vanishes at $y$.

**Correction.** The update is applied with the pivot function after its normalization (9.4.5),
so that $N(y) = 1$. -/
theorem newtonElimination_at_pivot {N P : E → ℝ} {y : E} (h : N y = 1) :
    (fun x ↦ P x - P y * N x) y = 0 := by
  simp [h]

/-- **Equation (9.4.5)** of [conn2000trust], counterexample to the normalization by the absolute
value: $(-1) / |-1| \neq 1$. A negative pivot normalized by its absolute value does not give the
value $1$ at the pivot point.

**Reading.** Negative pivot disproves unit normalization by its absolute value.
-/
theorem absolutePivotNormalization_counterexample : (-1 : ℝ) / |(-1 : ℝ)| ≠ 1 := by
  norm_num

private noncomputable def pivotRemainder {d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ A i.succ j.succ - A i.succ 0 / A 0 0 * A 0 j.succ

private theorem det_eq_pivot_mul_det_remainder {d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hA : A 0 0 ≠ 0) :
    A.det = A 0 0 * (pivotRemainder A).det := by
  let L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    fun i j ↦ if i = j then 1 else if j = 0 then -(A i 0 / A 0 0) else 0
  have hL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L]
    · simp [L]
    · intro i j hij
      have hne : i ≠ j := ne_of_lt hij
      have hj : j ≠ 0 := ne_of_gt (Fin.zero_le i |>.trans_lt hij)
      simp [L, hne, hj]
  have h0 (j : Fin (d + 1)) : (L * A) 0 j = A 0 j := by
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    have hz (i : Fin d) : (0 : Fin (d + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simp [L, hz]
  have hs (i : Fin d) (j : Fin (d + 1)) :
      (L * A) i.succ j = A i.succ j - A i.succ 0 / A 0 0 * A 0 j := by
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [L, Fin.succ_inj, sub_eq_add_neg, add_comm]
  have hc (i : Fin d) : (L * A) i.succ 0 = 0 := by
    rw [hs, div_mul_cancel₀ _ hA, sub_self]
  have hR : (L * A).submatrix Fin.succ Fin.succ = pivotRemainder A := by
    ext i j
    exact hs i j.succ
  have hdet := Matrix.det_succ_column_zero (L * A)
  rw [Fin.sum_univ_succ] at hdet
  simp only [hc, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero,
    pow_zero, one_mul, Fin.succAbove_zero, h0, hR] at hdet
  simpa only [Matrix.det_mul, hL, one_mul] using hdet

/-- **Algorithm 9.4.1** of [conn2000trust], the list of pivots. Let a row selector choose a row of
every square matrix of order $r + 1$. The pivots of a $d \times d$ matrix $A$ are defined
recursively. For $d = 0$ the list is empty. For a matrix of order $d + 1$, swap row $0$ with the
selected row to get $B$. The first pivot is $B_{00}$, and the remaining pivots are those of the
$d \times d$ matrix with entries
$$B_{i+1, j+1} - \frac{B_{i+1, 0}}{B_{00}} B_{0, j+1}.$$

The row selector is applied again to each remaining matrix. The entries of the remaining matrix
are $B_{i+1, j+1}$ when $B_{00} = 0$, because division by zero gives $0$ in Lean.

**Reading.** Matrix elimination computes pivots with a supplied row selector.
-/
noncomputable def interpolationPivots
    (chooseRow : (d : ℕ) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ → Fin (d + 1)) :
    (d : ℕ) → Matrix (Fin d) (Fin d) ℝ → List ℝ
  | 0, _ => []
  | d + 1, A =>
    let B := A.submatrix (Equiv.swap 0 (chooseRow d A)) id
    B 0 0 :: interpolationPivots chooseRow d (pivotRemainder B)

/-- **Equation (9.4.7)** of [conn2000trust]. A list of pivots **meets the threshold** $\theta$ if
$\theta > 0$ and $|p| \ge \theta$ for every pivot $p$ in the list.

This is the condition that the interpolation set is well poised at threshold $\theta$. -/
def HasPivotThreshold (θ : ℝ) (pivots : List ℝ) : Prop :=
  0 < θ ∧ ∀ p ∈ pivots, θ ≤ |p|

/-- **Theorem 9.4.2** of [conn2000trust]. Let $y_1, \dots, y_d \in E$, let
$P_1, \dots, P_d : E \to \mathbb{R}$, and let a row selector be given that picks a row with a
nonzero entry in the first column whenever such a row exists. Then the interpolation set is
poised if and only if every pivot of Algorithm 9.4.1 applied to the interpolation matrix is
nonzero.

Each elimination step takes the Schur complement of the normalized Newton column. Updating the
columns already processed within a block does not change the remaining pivots.

**Reading.** Determinant criterion stated for matrix pivots generated by a maximizing row selector.
-/
theorem theorem_9_4_2 {d : ℕ} (y : Fin d → E) (P : Fin d → E → ℝ)
    (chooseRow : (r : ℕ) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → Fin (r + 1))
    (hchoose : ∀ (r : ℕ) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
      A (chooseRow r A) 0 = 0 → ∀ i, A i 0 = 0) :
    IsPoised y P ↔ ∀ p ∈ interpolationPivots chooseRow d (interpolationMatrix y P), p ≠ 0 := by
  suffices ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ),
      A.det ≠ 0 ↔ ∀ p ∈ interpolationPivots chooseRow r A, p ≠ 0 by
    exact this d (interpolationMatrix y P)
  intro r
  induction r with
  | zero =>
    intro A
    simp [interpolationPivots]
  | succ r ih =>
    intro A
    let B := A.submatrix (Equiv.swap 0 (chooseRow r A)) id
    have hperm : B.det ≠ 0 ↔ A.det ≠ 0 := by
      change (A.submatrix (Equiv.swap 0 (chooseRow r A)) id).det ≠ 0 ↔ _
      rw [Matrix.det_permute, mul_ne_zero_iff]
      have hs : (↑(Equiv.Perm.sign (Equiv.swap 0 (chooseRow r A))) : ℝ) ≠ 0 := by
        exact_mod_cast Units.ne_zero _
      exact and_iff_right hs
    change A.det ≠ 0 ↔ ∀ p ∈ B 0 0 :: interpolationPivots chooseRow r (pivotRemainder B), p ≠ 0
    simp only [List.forall_mem_cons]
    rw [← hperm, ← ih]
    by_cases hp : B 0 0 = 0
    · have hB : B 0 0 = A (chooseRow r A) 0 := by simp [B]
      have hA0 := hchoose r A (hB.symm.trans hp)
      have hdet : B.det = 0 := by
        by_contra hb
        exact (hperm.mp hb) (Matrix.det_eq_zero_of_column_eq_zero 0 hA0)
      simp [hp, hdet]
    · rw [det_eq_pivot_mul_det_remainder B hp, mul_ne_zero_iff]

/-- **Algorithm 9.4.1** of [conn2000trust], pivot choice. There is a row selector that picks, for
every square matrix $A$, a row $r$ with $|A_{i0}| \le |A_{r0}|$ for all rows $i$. This selector
satisfies the hypothesis of `ConnGouldToint.Chapter09.theorem_9_4_2`. -/
theorem exists_maxMagnitudePivotSelector :
    ∃ chooseRow : (r : ℕ) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → Fin (r + 1),
      ∀ (r : ℕ) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (i : Fin (r + 1)),
        |A i 0| ≤ |A (chooseRow r A) 0| := by
  have h (r : ℕ) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :
      ∃ j : Fin (r + 1), ∀ i, |A i 0| ≤ |A j 0| := by
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
      (fun i : Fin (r + 1) ↦ |A i 0|) Finset.univ_nonempty
    exact ⟨j, fun i ↦ hj i (Finset.mem_univ _)⟩
  choose row hrow using h
  exact ⟨row, hrow⟩

private theorem mvPolynomial_totalDegree_prod {ι J : Type*} (s : Finset J)
    (F : J → MvPolynomial ι ℝ) (hne : ∀ j ∈ s, F j ≠ 0) :
    (∏ j ∈ s, F j).totalDegree = ∑ j ∈ s, (F j).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hn₁ := hne j (Finset.mem_insert_self _ _)
    have hn₂ (k : J) (hk : k ∈ s) : F k ≠ 0 := hne k (Finset.mem_insert_of_mem hk)
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      MvPolynomial.totalDegree_mul_of_isDomain hn₁ (Finset.prod_ne_zero_iff.mpr hn₂), ih hn₂]

/-- **Theorem 9.4.3** of [conn2000trust], graded Newton family on a Euclidean ball. Let $\iota$ be a
finite index set, let $x \in \mathbb{R}^\iota$ with the Euclidean norm, let $\delta > 0$ and
$d \in \mathbb{N}$. For a multi-index $a \in \mathbb{N}^\iota$, write $|a| = \sum_i a_i$. Then
there are points $y_a \in \mathbb{R}^\iota$ and real polynomials $P_a$ in the variables $\iota$,
for $a \in \mathbb{N}^\iota$, such that

* $y_0 = x$;
* for $|a| \le d$, $y_a \in B(x, \delta)$ and $P_a$ has total degree $|a|$;
* for all $a, b$ with $|b| \le |a|$, $P_a(y_b) = 1$ if $a = b$ and $0$ otherwise;
* for $|a| \le d$ and all $z \in B(x, \delta)$, $|P_a(z)| \le (2(d + 1))^d$.

Grouping the multi-indices by total degree gives the blocks of (9.4.4). The points form a
simplex of coordinate lattice points with spacing $\delta / (d + 1)$, and each $P_a$ is a
product of one-dimensional Lagrange factors.

**Reading.** Constructive simplex lattice with an explicit bound instead of the greedy maximization
proof.
-/
theorem theorem_9_4_3 {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι)
    {δ : ℝ} (hδ : 0 < δ) (d : ℕ) :
    let w (a : ι → ℕ) := ∑ i, a i
    ∃ (y : (ι → ℕ) → EuclideanSpace ℝ ι) (P : (ι → ℕ) → MvPolynomial ι ℝ),
      y 0 = x ∧
      (∀ a, w a ≤ d → y a ∈ Metric.closedBall x δ ∧ (P a).totalDegree = w a) ∧
      (∀ a b, w b ≤ w a → MvPolynomial.eval (fun i ↦ y b i) (P a) =
        if a = b then 1 else 0) ∧
      ∀ a, w a ≤ d → ∀ z ∈ Metric.closedBall x δ,
        |MvPolynomial.eval (fun i ↦ z i) (P a)| ≤ (2 * ((d : ℝ) + 1)) ^ d := by
  classical
  dsimp only
  let w (a : ι → ℕ) := ∑ i, a i
  let h := δ / ((d : ℝ) + 1)
  let q (i : ι) (r : ℕ) := x i + (r : ℝ) * h
  let y (a : ι → ℕ) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i ↦ q i (a i))
  let Q (a : ι → ℕ) (i : ι) (r : ℕ) : MvPolynomial ι ℝ :=
    MvPolynomial.C ((q i (a i) - q i r)⁻¹) *
      (MvPolynomial.X i - MvPolynomial.C (q i r))
  let P (a : ι → ℕ) := ∏ i, ∏ r ∈ Finset.range (a i), Q a i r
  have hh : 0 < h := by dsimp [h]; positivity
  have hden (i : ι) (l r : ℕ) (hlr : l < r) : h ≤ q i r - q i l := by
    have hlr' : (l : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlr
    dsimp [q]
    nlinarith only [mul_le_mul_of_nonneg_right hlr' hh.le]
  have hball (a : ι → ℕ) (ha : w a ≤ d) : y a ∈ Metric.closedBall x δ := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) hδ.le,
      EuclideanSpace.real_norm_sq_eq]
    have hcoord (i : ι) : (y a - x) i = (a i : ℝ) * h := by
      change x i + (a i : ℝ) * h - x i = _
      ring
    simp only [hcoord]
    refine (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ by positivity)).trans ?_
    rw [← Finset.sum_mul]
    have hsum : (∑ i, (a i : ℝ)) * h ≤ δ := by
      dsimp [h]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (show 0 < (d : ℝ) + 1 by positivity)).mpr
      have hcast : (∑ i, (a i : ℝ)) ≤ (d : ℝ) := by exact_mod_cast ha
      nlinarith only [mul_le_mul_of_nonneg_right hcast hδ.le, hδ]
    exact pow_le_pow_left₀ (by positivity) hsum 2
  have heval (a : ι → ℕ) (z : EuclideanSpace ℝ ι) :
      MvPolynomial.eval (fun i ↦ z i) (P a) =
        ∏ i, ∏ r ∈ Finset.range (a i), (z i - q i r) / (q i (a i) - q i r) := by
    simp [P, Q, div_eq_inv_mul]
  have hfactorDegree (a : ι → ℕ) (i : ι) {r : ℕ} (hr : r < a i) :
      (Q a i r).totalDegree = 1 := by
    have hs : (MvPolynomial.X i - MvPolynomial.C (q i r) : MvPolynomial ι ℝ).totalDegree = 1 := by
      rw [sub_eq_add_neg, MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
      · exact MvPolynomial.totalDegree_X i
      · rw [← map_neg, MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
        decide
    have hn : (MvPolynomial.X i - MvPolynomial.C (q i r) : MvPolynomial ι ℝ) ≠ 0 := by
      intro he
      rw [he, MvPolynomial.totalDegree_zero] at hs
      omega
    have hc : (MvPolynomial.C ((q i (a i) - q i r)⁻¹) : MvPolynomial ι ℝ) ≠ 0 :=
      MvPolynomial.C_ne_zero.mpr (inv_ne_zero (hh.trans_le (hden i r (a i) hr)).ne')
    dsimp [Q]
    rw [MvPolynomial.totalDegree_mul_of_isDomain hc hn, MvPolynomial.totalDegree_C, hs, zero_add]
  have hrowDegree (a : ι → ℕ) (i : ι) :
      (∏ r ∈ Finset.range (a i), Q a i r).totalDegree = a i := by
    have hne (r : ℕ) (hr : r ∈ Finset.range (a i)) : Q a i r ≠ 0 := by
      intro he
      have h := hfactorDegree a i (Finset.mem_range.mp hr)
      rw [he, MvPolynomial.totalDegree_zero] at h
      omega
    rw [mvPolynomial_totalDegree_prod _ _ hne]
    calc
      _ = ∑ _r ∈ Finset.range (a i), 1 :=
        Finset.sum_congr rfl (fun _ hr ↦ hfactorDegree a i (Finset.mem_range.mp hr))
      _ = _ := by simp
  have hdiag (a : ι → ℕ) : MvPolynomial.eval (fun i ↦ y a i) (P a) = 1 := by
    rw [heval]
    apply Finset.prod_eq_one
    intro i _
    apply Finset.prod_eq_one
    intro r hr
    change (q i (a i) - q i r) / _ = 1
    exact div_self (hh.trans_le (hden i r (a i) (Finset.mem_range.mp hr))).ne'
  refine ⟨y, P, ?_, ?_, ?_, ?_⟩
  · ext i
    simp [y, q]
  · intro a ha
    refine ⟨hball a ha, ?_⟩
    have hne (i : ι) (_ : i ∈ (Finset.univ : Finset ι)) :
        (∏ r ∈ Finset.range (a i), Q a i r) ≠ 0 := by
      intro he
      have h := hrowDegree a i
      rw [he, MvPolynomial.totalDegree_zero] at h
      simp [← h] at he
    dsimp [P, w]
    rw [mvPolynomial_totalDegree_prod _ _ hne]
    exact Finset.sum_congr rfl (fun i _ ↦ hrowDegree a i)
  · intro a b hab
    by_cases he : a = b
    · subst b
      simpa using hdiag a
    rw [ite_eq_right he, heval]
    have hex : ∃ i, b i < a i := by
      by_contra! hn
      apply he
      funext i
      apply le_antisymm (hn i)
      by_contra! hlt
      exact (not_lt_of_ge hab)
        (Finset.sum_lt_sum (fun j _ ↦ hn j) ⟨i, Finset.mem_univ _, hlt⟩)
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    change (q i (b i) - q i (b i)) / _ = 0
    rw [sub_self, zero_div]
  · intro a ha z hz
    let C := 2 * ((d : ℝ) + 1)
    have hC : 1 ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) d]
    have hfactor (i : ι) (r : ℕ) (hr : r < a i) :
        |(z i - q i r) / (q i (a i) - q i r)| ≤ C := by
      have hia : a i ≤ w a := Finset.single_le_sum
        (fun j _ ↦ Nat.zero_le (a j)) (Finset.mem_univ i)
      have hra : r ≤ d := hr.le.trans (hia.trans ha)
      have hz₁ : |z i - x i| ≤ δ := by
        have hn : ‖z - x‖ ≤ δ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
        have hcoord : |z i - x i| ≤ ‖z - x‖ := by
          simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (z - x) i
        exact hcoord.trans hn
      have hr₁ : |q i r - x i| ≤ δ := by
        dsimp [q, h]
        rw [add_sub_cancel_left, abs_of_nonneg (by positivity), ← mul_div_assoc]
        apply (div_le_iff₀ (show 0 < (d : ℝ) + 1 by positivity)).mpr
        have hcast : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast hra
        nlinarith only [mul_le_mul_of_nonneg_right hcast hδ.le, hδ]
      have hnum : |z i - q i r| ≤ 2 * δ := by
        calc
          _ = |(z i - x i) - (q i r - x i)| := by congr 1; ring
          _ ≤ |z i - x i| + |q i r - x i| := abs_sub _ _
          _ ≤ _ := by linarith
      rw [abs_div, abs_of_pos (hh.trans_le (hden i r (a i) hr))]
      apply (div_le_iff₀ (hh.trans_le (hden i r (a i) hr))).mpr
      calc
        _ ≤ 2 * δ := hnum
        _ = C * h := by dsimp [C, h]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hden i r (a i) hr) (zero_le_one.trans hC)
    rw [heval, Finset.abs_prod]
    calc
      _ ≤ ∏ i, C ^ (a i) := by
        apply Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _)
        intro i _
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏ _r ∈ Finset.range (a i), C :=
            Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _)
              (fun r hr ↦ hfactor i r (Finset.mem_range.mp hr))
          _ = _ := by simp
      _ = C ^ w a := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ _ := pow_le_pow_right₀ hC ha

open Module in
/-- **Theorem 9.4.3** of [conn2000trust], complete polynomial basis. Let $\iota$ be a finite index
set, let $x \in \mathbb{R}^\iota$ with the Euclidean norm, let $\delta > 0$ and
$d \in \mathbb{N}$, and let $I$ be the set of multi-indices $a$ with $|a| \le d$. Then there are
points $y_a \in B(x, \delta)$, for $a \in I$, and a basis $(B_a)_{a \in I}$ of the space of real
polynomials of total degree at most $d$, such that $y_0 = x$, $B_a$ has total degree $|a|$,
$B_a(y_b) = 1$ if $a = b$ and $0$ otherwise whenever $|b| \le |a|$, and
$|B_a(z)| \le (2(d + 1))^d$ for all $z \in B(x, \delta)$.

The space is `MvPolynomial.restrictTotalDegree ι ℝ d`, and the multi-indices are finitely
supported functions `ι →₀ ℕ`. The basis is the family of
`ConnGouldToint.Chapter09.theorem_9_4_3`.

**Reading.** Complete basis from the simplex lattice construction and its uniform bound.
-/
theorem theorem_9_4_3_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (x : EuclideanSpace ℝ ι)
    {δ : ℝ} (hδ : 0 < δ) (d : ℕ) :
    let I := {a : ι →₀ ℕ // a.sum (fun _ n ↦ n) ≤ d}
    ∃ (y : I → EuclideanSpace ℝ ι)
      (B : Basis I ℝ (MvPolynomial.restrictTotalDegree ι ℝ d)),
      y ⟨0, by simp⟩ = x ∧ (∀ a, y a ∈ Metric.closedBall x δ) ∧
      (∀ a, (B a : MvPolynomial ι ℝ).totalDegree = a.1.sum (fun _ n ↦ n)) ∧
      (∀ a b, b.1.sum (fun _ n ↦ n) ≤ a.1.sum (fun _ n ↦ n) →
        MvPolynomial.eval (fun i ↦ y b i) (B a : MvPolynomial ι ℝ) = if a = b then 1 else 0) ∧
      ∀ a z, z ∈ Metric.closedBall x δ →
        |MvPolynomial.eval (fun i ↦ z i) (B a : MvPolynomial ι ℝ)| ≤ (2 * ((d : ℝ) + 1)) ^ d := by
  classical
  dsimp only
  let I := {a : ι →₀ ℕ // a.sum (fun _ n ↦ n) ≤ d}
  let V := MvPolynomial.restrictTotalDegree ι ℝ d
  let w (a : I) := a.1.sum (fun _ n ↦ n)
  have hw (a : I) : (∑ i, a.1 i) = w a := by
    dsimp [w]
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
  have hcoord (a : I) (i : ι) : a.1 i ≤ d := by
    have h := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (a.1 j)) (Finset.mem_univ i)
    exact h.trans ((hw a).le.trans a.2)
  let enc (a : I) (i : ι) : Fin (d + 1) := ⟨a.1 i, Nat.lt_succ_of_le (hcoord a i)⟩
  have he : Function.Injective enc := by
    intro a b h
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun h i)
  let : Finite I := Finite.of_injective enc he
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨y, P, hcenter, hball, htri, hbound⟩ := theorem_9_4_3 x hδ d
  let N (a : I) : V := ⟨P a.1, (MvPolynomial.mem_restrictTotalDegree ι d (P a.1)).mpr
    ((hball a.1 ((hw a).le.trans a.2)).2.trans_le ((hw a).le.trans a.2))⟩
  have hentry (a b : I) (hab : w b ≤ w a) :
      MvPolynomial.eval (fun i ↦ y b.1 i) (N a : MvPolynomial ι ℝ) =
        if a = b then 1 else 0 := by
    have hc : ((a.1 : ι → ℕ) = b.1) ↔ a = b :=
      ⟨fun h ↦ Subtype.ext (Finsupp.ext (congrFun h)), fun h ↦ by subst b; rfl⟩
    have ht := htri (a.1 : ι → ℕ) (b.1 : ι → ℕ)
      ((hw b).le.trans (hab.trans (hw a).symm.le))
    simpa only [N, hc] using ht
  have hind : LinearIndependent ℝ N := by
    rw [linearIndependent_iff']
    intro s c hs a ha
    by_contra! hca
    let T := s.filter fun b ↦ c b ≠ 0
    have hT : T.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hca⟩⟩
    obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image T w hT
    have hb' := Finset.mem_filter.mp hb
    have hval := congrArg (fun p : V ↦ MvPolynomial.eval (fun i ↦ y b.1 i)
      (p : MvPolynomial ι ℝ)) hs
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
      map_sum, Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, MvPolynomial.eval_C,
      map_zero] at hval
    rw [Finset.sum_eq_single b] at hval
    · rw [hentry b b le_rfl, ite_eq_left rfl, mul_one] at hval
      exact hb'.2 hval
    · intro j hj hjb
      by_cases hc : c j = 0
      · simp [hc]
      rw [hentry j b (hbmin j (Finset.mem_filter.mpr ⟨hj, hc⟩)),
        ite_eq_right hjb, mul_zero]
    · exact fun h ↦ (h hb'.1).elim
  have hcard : Fintype.card I = Module.finrank ℝ V :=
    (Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℝ
      {a : ι →₀ ℕ | a.sum (fun _ n ↦ n) ≤ d})).symm
  let B := basisOfLinearIndependentOfCardEqFinrank' N hind hcard
  have hBN (a : I) : B a = N a :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' N hind hcard) a
  refine ⟨fun a ↦ y a.1, B, hcenter, ?_, ?_, ?_, ?_⟩
  · intro a
    exact (hball a.1 ((hw a).le.trans a.2)).1
  · intro a
    rw [hBN]
    exact (hball a.1 ((hw a).le.trans a.2)).2.trans (hw a)
  · intro a b h
    rw [hBN]
    exact hentry a b h
  · intro a z hz
    rw [hBN]
    exact hbound a.1 ((hw a).le.trans a.2) z hz

end ConnGouldToint.Chapter09
