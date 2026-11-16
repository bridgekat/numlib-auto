/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Approximation.Hermite
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Atkinson and Han, Section 10.1: One-dimensional finite element examples

This module formalizes the finite-dimensional algebra of Section 10.1 of [han2009theoretical]. The
section solves the two-point boundary value problem $-u'' + u = f$ on $(0, 1)$ with piecewise linear
and piecewise quadratic elements, and it introduces the cubic Hermite element for the beam problem
(10.1.16). For the piecewise linear element with $N$ uniform elements of length $h = 1/N$, the
stiffness matrix is $A = h^{-1} \operatorname{tridiag}(-1, 2, -1)$ of order $N - 1$, and its
spectral condition number (10.1.9) is $$\operatorname{Cond}_2(A) = \frac{1 + \cos \pi h}{1 - \cos
\pi h} = O(h^{-2}).$$ Static condensation eliminates the interior unknowns of an element, and the
condensed system (10.1.15) has a symmetric positive definite matrix (Exercise 10.1.2). The cubic
Hermite shape functions on $[0, 1]$ are $$\Phi_0 = (1 + 2x)(1 - x)^2, \quad \Phi_1 = (3 - 2x) x^2,
\quad \Psi_0 = x (1 - x)^2, \quad \Psi_1 = -(1 - x) x^2,$$ and they form a basis of the cubic
polynomials $\mathbb{P}_3$ dual to the values and the slopes at the two ends. A conforming method
for the beam problem needs this degree, because a $C^1$ piecewise quadratic function cannot be
supported on two neighbouring elements (Exercise 10.1.3). The condition number uses
`Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff` and `Matrix.IsHermitian.l2_opNorm_eq`, and the
Hermite element uses `Numlib.Approximation.Hermite`.

## Main definitions

* Equation (10.1.9), `AtkinsonHan.Chapter10.stiffnessMatrix`: the matrix
  $h^{-1} \operatorname{tridiag}(-1, 2, -1)$ of the piecewise linear element.
* Section 10.1.3, `AtkinsonHan.Chapter10.hermiteShape`: the four cubic Hermite shape functions on
  $[0, 1]$.
* Section 10.1.3, `AtkinsonHan.Chapter10.hermiteShapeBasis`: the four shape functions as a basis of
  $\mathbb{P}_3$.

## Main results

* Equation (10.1.9), `AtkinsonHan.Chapter10.equation_10_1_9`: $\operatorname{Cond}_2(A) = (1 + \cos
  \pi h) / (1 - \cos \pi h)$.
* Section 10.1.3, `AtkinsonHan.Chapter10.eval_iterate_derivative_hermiteShape`: the sixteen
  interpolation conditions of the Hermite shape functions.
* Section 10.1.3, `AtkinsonHan.Chapter10.hermiteShape_mem_degreeLT`: the Hermite shape functions are
  cubic polynomials.
* Section 10.1.3, `AtkinsonHan.Chapter10.eq_hermiteShape_combination`: every cubic is
  $p = \sum_i p(i) \Phi_i + \sum_i p'(i) \Psi_i$.
* Exercise 10.1.2, `AtkinsonHan.Chapter10.exercise_10_1_2`: the Schur complement of a symmetric
  positive definite block matrix is symmetric positive definite.
* Exercise 10.1.3, `AtkinsonHan.Chapter10.exercise_10_1_3`: two quadratics on neighbouring intervals
  that form a $C^1$ function vanishing to first order at the outer ends are both zero.

## Implementation notes

* The stiffness matrix is indexed by its order $n = N - 1$, so that $h = 1 / (n + 1)$. The condition
  number is `NormedRing.condNumber` for the operator norm induced by the Euclidean vector norm.
* The shape function of `AtkinsonHan.Chapter10.hermiteShape` with index $(i, j)$ is dual to the
  functional "$j$-th derivative at the node $i$", for $i, j \in \{0, 1\}$. So the index $(i, 0)$
  gives $\Phi_i$ and the index $(i, 1)$ gives $\Psi_i$.
* Over $\mathbb{R}$ the conjugate transpose `ᴴ` of the block matrix lemmas of Mathlib is the
  transpose, and Exercise 10.1.2 is stated with it.

## Deviations from the source

* **Exercise 10.1.2** (generalization). The statement is for any symmetric positive definite block
  matrix over any pair of index types, not only for the matrix of the finite element system. See
  `AtkinsonHan.Chapter10.exercise_10_1_2`.
* **Exercise 10.1.3** (reading). The claim on a space of piecewise quadratic functions is stated as
  the fact about two neighbouring elements on which its proof rests. See
  `AtkinsonHan.Chapter10.exercise_10_1_3`.

## Not formalized

* **The finite element systems (10.1.1)–(10.1.6) and (10.1.13)–(10.1.15), and Exercise 10.1.1.**
  They are posed on the space $V = \{v \in H^1(0, 1) : v(0) = 0\}$.
* **The dimension count $\dim V_h = (p - 1) N - 2$ of Exercise 10.1.3.** It is a statement about a
  space of piecewise polynomial functions.
-/

open Polynomial Real
open scoped Matrix Matrix.Norms.L2Operator NormedRing

namespace AtkinsonHan.Chapter10

/-! ### Exercise 10.1.2: static condensation -/

/-- **Exercise 10.1.2** of [han2009theoretical] (static condensation). Let
$M_{11} \in \mathbb{R}^{m \times m}$, $M_{12} \in \mathbb{R}^{m \times n}$ and
$D_{22} \in \mathbb{R}^{n \times n}$, with $D_{22}$ invertible. If the block matrix
$$\begin{bmatrix} M_{11} & M_{12} \\ M_{12}^T & D_{22} \end{bmatrix}$$ is symmetric positive
definite, then so is its Schur complement $M_{11} - M_{12} D_{22}^{-1} M_{12}^T$. This is the
coefficient matrix of the condensed system (10.1.15) that remains after the interior unknowns
are eliminated.

**Generalization.** The source states the exercise for the matrix of the finite element system.
Neither the origin of the blocks nor their size plays a part, so the statement is for any
symmetric positive definite block matrix over any finite index types. The source writes the
lower left block as $M_{21} = M_{12}^T$; over $\mathbb{R}$ the conjugate transpose `ᴴ` of the
statement is the transpose.

The proof evaluates the identity `Matrix.schur_complement_eq₂₂` at
$y = -D_{22}^{-1} M_{12}^T x$. This leaves the quadratic form of the Schur complement at $x$,
and $(x, y) \ne 0$ when $x \ne 0$. Mathlib's `Matrix.PosSemidef.fromBlocks₂₂` is the analogous
statement for positive semidefinite matrices. -/
theorem exercise_10_1_2 {m n : Type*} [Finite m] [Fintype n] [DecidableEq n]
    {M₁₁ : Matrix m m ℝ} {M₁₂ : Matrix m n ℝ} {D₂₂ : Matrix n n ℝ} [Invertible D₂₂]
    (h : (Matrix.fromBlocks M₁₁ M₁₂ M₁₂ᴴ D₂₂).PosDef) :
    (M₁₁ - M₁₂ * D₂₂⁻¹ * M₁₂ᴴ).PosDef := by
  have : Fintype m := Fintype.ofFinite m
  have hblocks := Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian
  have hD : D₂₂.IsHermitian := hblocks.2.2.2
  have hherm : (M₁₁ - M₁₂ * D₂₂⁻¹ * M₁₂ᴴ).IsHermitian :=
    hblocks.1.sub (Matrix.isHermitian_mul_mul_conjTranspose _ hD.inv)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
  set y : n → ℝ := -((D₂₂⁻¹ * M₁₂ᴴ) *ᵥ x) with hy
  have hkey := Matrix.schur_complement_eq₂₂ M₁₁ M₁₂ x y hD
  have hzero : (D₂₂⁻¹ * M₁₂ᴴ) *ᵥ x + y = 0 := by rw [hy]; abel
  rw [hzero] at hkey
  simp only [dotProduct_zero, zero_add, star_zero, Matrix.zero_vecMul] at hkey
  have hne : (Sum.elim x y) ≠ 0 := fun hc => hx (funext fun i => by
    simpa using congrFun hc (Sum.inl i))
  have hpos := h.dotProduct_mulVec_pos hne
  rw [Matrix.dotProduct_mulVec, hkey] at hpos
  rwa [Matrix.dotProduct_mulVec]

/-! ### The cubic Hermite element of Section 10.1.3 -/

/-- **Section 10.1.3** of [han2009theoretical], the cubic Hermite shape functions. On the reference
interval $[0, 1]$ they are $$\Phi_0 = (1 + 2x)(1 - x)^2, \quad \Phi_1 = (3 - 2x) x^2, \quad
\Psi_0 = x (1 - x)^2, \quad \Psi_1 = -(1 - x) x^2.$$

The shape function with index $(i, j)$ is dual to the functional "$j$-th derivative at the node
$i$". So the index $(i, 0)$ gives $\Phi_i$ and the index $(i, 1)$ gives $\Psi_i$, for $i = 0, 1$. -/
noncomputable def hermiteShape (i j : Fin 2) : ℝ[X] :=
  ![![(1 + 2 * X) * (1 - X) ^ 2, X * (1 - X) ^ 2],
    ![(3 - 2 * X) * X ^ 2, -((1 - X) * X ^ 2)]] i j

/-- **Section 10.1.3** of [han2009theoretical], the interpolation conditions. For
$i, j, i', j' \in \{0, 1\}$, the $j'$-th derivative of the shape function with index $(i, j)$ at
the node $i'$ is $1$ if $(i', j') = (i, j)$ and $0$ otherwise. For example, for $j = j' = 0$
this gives $\Phi_0(0) = 1$, $\Phi_0(1) = 0$, $\Phi_1(0) = 0$ and $\Phi_1(1) = 1$. -/
theorem eval_iterate_derivative_hermiteShape (i j i' j' : Fin 2) :
    (derivative^[(j' : ℕ)] (hermiteShape i j)).eval ((i' : ℕ) : ℝ)
      = if i = i' ∧ j = j' then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [hermiteShape, derivative_pow] <;> ring_nf

/-- **Section 10.1.3** of [han2009theoretical]. Each cubic Hermite shape function is a polynomial of
degree at most $3$, that is, an element of $\mathbb{P}_3$ (`Polynomial.degreeLT ℝ 4`). -/
theorem hermiteShape_mem_degreeLT (i j : Fin 2) : hermiteShape i j ∈ degreeLT ℝ 4 := by
  rw [mem_degreeLT]
  have h : (hermiteShape i j).degree < 4 := by
    fin_cases i <;> fin_cases j <;>
      · simp only [hermiteShape, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
          Fin.zero_eta, Fin.mk_one]
        compute_degree!
  exact_mod_cast h

/-- The two nodes `0` and `1` of the reference interval are distinct. -/
private theorem injective_node : Function.Injective (fun i : Fin 2 => ((i : ℕ) : ℝ)) := by
  intro i i'
  fin_cases i <;> fin_cases i' <;> simp_all

/-- **Section 10.1.3** of [han2009theoretical], the Hermite representation of a cubic. Every
polynomial $p$ of degree at most $3$ is determined by its values and slopes at the two ends of
$[0, 1]$: $$p = \sum_{i=0}^{1} p(i) \, \Phi_i + \sum_{i=0}^{1} p'(i) \, \Psi_i.$$

This is the unisolvence of two-point Hermite interpolation on $[0, 1]$. The difference of the
two sides is a cubic whose four Hermite data vanish, and a nonzero cubic cannot have four roots
counted with multiplicity (`Hermite.eq_zero_of_forall_eval_iterate_derivative_eq_zero`). -/
theorem eq_hermiteShape_combination {p : ℝ[X]} (hp : p ∈ degreeLT ℝ 4) :
    p = ∑ i : Fin 2, ∑ j : Fin 2,
      C ((derivative^[(j : ℕ)] p).eval ((i : ℕ) : ℝ)) * hermiteShape i j := by
  set r : ℝ[X] := ∑ i : Fin 2, ∑ j : Fin 2,
    C ((derivative^[(j : ℕ)] p).eval ((i : ℕ) : ℝ)) * hermiteShape i j with hr
  have hmem : r ∈ degreeLT ℝ 4 := by
    rw [hr]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hermiteShape_mem_degreeLT i j)
  have hdata : ∀ i' : Fin 2, ∀ j' : Fin 2,
      (derivative^[(j' : ℕ)] r).eval ((i' : ℕ) : ℝ)
        = (derivative^[(j' : ℕ)] p).eval ((i' : ℕ) : ℝ) := by
    intro i' j'
    rw [hr]
    simp only [iterate_derivative_sum, eval_finsetSum, iterate_derivative_C_mul, eval_mul, eval_C,
      eval_iterate_derivative_hermiteShape]
    rw [Finset.sum_eq_single i']
    · rw [Finset.sum_eq_single j']
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ => by simp [hi]
    · simp
  have hzero : p - r = 0 := by
    refine Hermite.eq_zero_of_forall_eval_iterate_derivative_eq_zero (n := 2) (M := 4)
      (x := fun i : Fin 2 => ((i : ℕ) : ℝ)) injective_node (m := fun _ => 1) (by decide) ?_ ?_
    · exact lt_of_le_of_lt (degree_sub_le _ _)
        (max_lt (mem_degreeLT.mp hp) (mem_degreeLT.mp hmem))
    · intro i j hj
      rw [iterate_derivative_sub, eval_sub, sub_eq_zero]
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simpa using (hdata i 0).symm
      · simpa using (hdata i 1).symm
  exact sub_eq_zero.mp hzero

/-- **Section 10.1.3** of [han2009theoretical]. The four cubic Hermite shape functions
$\Phi_0, \Psi_0, \Phi_1, \Psi_1$ form a basis of $\mathbb{P}_3$.

They span $\mathbb{P}_3$ by `AtkinsonHan.Chapter10.eq_hermiteShape_combination`. They are
linearly independent by the interpolation conditions: the functional "$j$-th derivative at $i$"
takes a combination of the shape functions to its coefficient with index $(i, j)$. -/
noncomputable def hermiteShapeBasis : Module.Basis (Fin 2 × Fin 2) ℝ (degreeLT ℝ 4) :=
  Module.Basis.mk (v := fun k => ⟨hermiteShape k.1 k.2, hermiteShape_mem_degreeLT k.1 k.2⟩)
    (by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have hc' : ∑ k' : Fin 2 × Fin 2, c k' • hermiteShape k'.1 k'.2 = 0 := by
        simpa [Submodule.coe_sum] using congrArg Subtype.val hc
      have h := congrArg (fun q : ℝ[X] => (derivative^[(k.2 : ℕ)] q).eval ((k.1 : ℕ) : ℝ)) hc'
      simpa [smul_eq_C_mul, iterate_derivative_sum, eval_finsetSum, iterate_derivative_C_mul,
        eval_iterate_derivative_hermiteShape, ← Prod.ext_iff, Finset.sum_ite_eq'] using h)
    (by
      rintro ⟨p, hp⟩ -
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun k => (derivative^[(k.2 : ℕ)] p).eval ((k.1 : ℕ) : ℝ), Subtype.ext ?_⟩
      simp only [Submodule.coe_sum, SetLike.val_smul, smul_eq_C_mul, Fintype.sum_prod_type]
      exact (eq_hermiteShape_combination hp).symm)

/-! ### Exercise 10.1.3: a $C^1$ piecewise quadratic function has no support on two elements -/

/-- A polynomial $p$ of degree at most $2$ with $p(a) = p'(a) = 0$ is $\alpha (x - a)^2$ for some
$\alpha \in \mathbb{R}$. -/
private theorem exists_eq_C_mul_sq {p : ℝ[X]} (hp : p ∈ degreeLT ℝ 3) {a : ℝ}
    (h0 : p.eval a = 0) (h1 : (derivative p).eval a = 0) :
    ∃ α : ℝ, p = C α * (X - C a) ^ 2 := by
  refine ⟨p.coeff 2, ?_⟩
  set q : ℝ[X] := p - C (p.coeff 2) * (X - C a) ^ 2 with hq
  have hcoeff2 : ((X - C a) ^ 2 : ℝ[X]).coeff 2 = 1 := by
    have h := ((monic_X_sub_C a).pow 2).coeff_natDegree
    rwa [natDegree_pow, natDegree_X_sub_C] at h
  have hqdeg : q ∈ degreeLT ℝ 2 := by
    rw [mem_degreeLT, degree_lt_iff_coeff_zero]
    intro m hm
    rw [hq, coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le (show (2 : ℕ) ≤ m by exact_mod_cast hm) with rfl | hm2
    · rw [hcoeff2, mul_one, sub_self]
    · have hp2 : p.coeff m = 0 := by
        have h := mem_degreeLT.mp hp
        rw [degree_lt_iff_coeff_zero] at h
        exact h m (by exact_mod_cast (by omega : 3 ≤ m))
      rw [hp2, coeff_eq_zero_of_natDegree_lt (n := m) (by simp; omega), mul_zero, sub_zero]
  have hq0 : q.eval a = 0 := by simp [hq, h0]
  have hq1 : (derivative q).eval a = 0 := by simp [hq, derivative_pow, h1]
  have hqz : q = 0 := by
    refine Hermite.eq_zero_of_forall_eval_iterate_derivative_eq_zero (n := 1) (M := 2)
      (x := fun _ : Fin 1 => a) (fun i j _ => Subsingleton.elim i j) (m := fun _ => 1)
      (by decide) (mem_degreeLT.mp hqdeg) fun i j hj => ?_
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · simpa using hq0
    · simpa using hq1
  rw [hq] at hqz
  exact sub_eq_zero.mp hqz

/-- **Exercise 10.1.3** of [han2009theoretical]. Let $a < b < c$, and let $p$ and $q$ be polynomials
of degree at most $2$ with $$p(a) = p'(a) = 0, \qquad q(c) = q'(c) = 0, \qquad p(b) = q(b),
\qquad p'(b) = q'(b).$$ Then $p = 0$ and $q = 0$. So a $C^1$ piecewise quadratic function on a
partition of $[0, 1]$ cannot have a basis function whose support is exactly two neighbouring
elements.

**Reading.** The source states the exercise for a space of $C^1$ piecewise quadratic functions.
The formal statement is the fact about two neighbouring elements on which the proof rests. The
count $\dim V_h = (p - 1) N - 2$ of the source is a statement about a space of functions and is
not formalized.

The consequence is that a conforming finite element method for the beam problem (10.1.16), whose
space lies in $H^2(0, 1)$ and so needs $C^1$ elements, needs polynomials of degree at least $3$.
The cubic Hermite element `AtkinsonHan.Chapter10.hermiteShape` supplies them. The proof writes
$p = \alpha (x - a)^2$ and $q = \beta (x - c)^2$. The values at $b$ give
$\alpha (b - a)^2 = \beta (b - c)^2$, and the slopes give $\alpha (b - a) = \beta (b - c)$. Then
$\beta (b - c)(c - a) = 0$, and since $b - c \ne 0$ and $c - a \ne 0$, $\beta = 0$. -/
theorem exercise_10_1_3 {a b c : ℝ} (hab : a < b) (hbc : b < c) {p q : ℝ[X]}
    (hp : p ∈ degreeLT ℝ 3) (hq : q ∈ degreeLT ℝ 3)
    (hpa : p.eval a = 0) (hpa' : (derivative p).eval a = 0)
    (hqc : q.eval c = 0) (hqc' : (derivative q).eval c = 0)
    (hval : p.eval b = q.eval b) (hslope : (derivative p).eval b = (derivative q).eval b) :
    p = 0 ∧ q = 0 := by
  obtain ⟨α, rfl⟩ := exists_eq_C_mul_sq hp hpa hpa'
  obtain ⟨β, rfl⟩ := exists_eq_C_mul_sq hq hqc hqc'
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, derivative_mul, derivative_C,
    derivative_pow, derivative_sub, derivative_X, zero_mul, zero_add, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, sub_zero, mul_one] at hval hslope
  -- matching the slopes at `b`, with the common factor `2` cancelled
  have h1 : α * (b - a) = β * (b - c) := by linarith
  -- eliminating `α` between the two matching conditions
  have h2 : β * (b - c) * (c - a) = 0 := by linear_combination (-(b - a)) * h1 + hval
  have hβ : β = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h (sub_ne_zero.mpr hbc.ne)
    · exact absurd h (sub_ne_zero.mpr (by linarith : c ≠ a))
  have hα : α = 0 := by
    rw [hβ, zero_mul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (sub_ne_zero.mpr hab.ne')
  rw [hα, hβ]
  simp

/-! ### Equation (10.1.9): the condition number of the stiffness matrix -/

/-- **Equation (10.1.9)** of [han2009theoretical], the stiffness matrix of the piecewise linear
element. For the two-point boundary value problem on $(0, 1)$ with $N$ uniform elements of
length $h = 1/N$, it is the matrix $$A = h^{-1} \operatorname{tridiag}(-1, 2, -1)$$ of order
$N - 1$.

The matrix is indexed by its order $n = N - 1$, so that $h = 1 / (n + 1)$ and $h^{-1} = n + 1$.
It is `Matrix.symmTridiagonalToeplitz n (-1) 2` multiplied by $n + 1$. -/
noncomputable def stiffnessMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) + 1) • Matrix.symmTridiagonalToeplitz n (-1) 2

/-- **Equation (10.1.9)** of [han2009theoretical]. Let $n \ge 1$ and $h = 1 / (n + 1)$. The spectral
condition number of the stiffness matrix $A = h^{-1} \operatorname{tridiag}(-1, 2, -1)$ of order
$n$ is $$\operatorname{Cond}_2(A) = \|A\|_2 \|A^{-1}\|_2 = \frac{1 + \cos \pi h}{1 - \cos \pi
h},$$ which is $O(h^{-2})$ as $h \to 0$.

The condition number is `NormedRing.condNumber` for the operator norm induced by the Euclidean
vector norm. The eigenvalues of $\operatorname{tridiag}(-1, 2, -1)$ are $2 - 2 \cos(k \pi h)$
for $1 \le k \le n$. The extreme ones are at $k = 1$ and $k = n$, so the spectrum lies in
$[2 - 2 \cos \pi h, 2 + 2 \cos \pi h]$ and contains both ends. `Matrix.IsHermitian.l2_opNorm_eq`
and `Matrix.IsHermitian.l2_opNorm_inv_eq` give the two norms, and the factor $h^{-1}$ cancels by
`NormedRing.condNumber_smul`. -/
theorem equation_10_1_9 (n : ℕ) (hn : 0 < n) :
    κ (stiffnessMatrix n)
      = (1 + Real.cos (π / ((n : ℝ) + 1))) / (1 - Real.cos (π / ((n : ℝ) + 1))) := by
  rw [stiffnessMatrix]
  set c : ℝ := Real.cos (π / ((n : ℝ) + 1)) with hc
  set B : Matrix (Fin n) (Fin n) ℝ := Matrix.symmTridiagonalToeplitz n (-1) 2 with hB
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hhalf : 0 < Real.sin (π / (2 * ((n : ℝ) + 1))) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hcos : c = 1 - 2 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
    rw [hc, ← Real.cos_two_mul_eq_one_sub]
    congr 1
    field_simp
  have hclt : c < 1 := by rw [hcos]; nlinarith
  have hcpos : 0 ≤ c := by
    rw [hc]
    have hpi := Real.pi_pos
    refine Real.cos_nonneg_of_mem_Icc ⟨by linarith [div_pos hpi hn1], ?_⟩
    rw [div_le_iff₀ hn1]
    nlinarith [Nat.one_le_cast (α := ℝ) |>.2 hn]
  have hm : (0 : ℝ) < 2 - 2 * c := by linarith
  have hbdd := Matrix.isSymmetricBoundedBy_symmTridiagonalToeplitz n (-1) 2
  simp only [abs_neg, abs_one, mul_one] at hbdd
  rw [← hc, ← hB] at hbdd
  have hHerm : B.IsHermitian := Matrix.symmTridiagonalToeplitz_isHermitian (-1) 2
  have hIcc : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin B) μ →
      μ ∈ Set.Icc (2 - 2 * c) (2 + 2 * c) := fun μ hμ => by
    simpa using hbdd.re_mem_Icc_of_hasEigenvalue hμ
  have hmin : Module.End.HasEigenvalue (Matrix.toEuclideanLin B) (2 - 2 * c) := by
    rw [hB, Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff]
    refine ⟨⟨0, hn⟩, ?_⟩
    push_cast
    rw [hc]
    ring_nf
  have hmax : Module.End.HasEigenvalue (Matrix.toEuclideanLin B) (2 + 2 * c) := by
    rw [hB, Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff]
    refine ⟨⟨n - 1, Nat.sub_lt hn one_pos⟩, ?_⟩
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have h1 : (1 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h1]
      ring
    have hsub : (n : ℝ) * π / ((n : ℝ) + 1) = π - π / ((n : ℝ) + 1) := by field_simp; ring
    rw [hcast, hc, hsub, Real.cos_pi_sub]
    ring
  have hnormB : ‖B‖ = 2 + 2 * c := by
    refine hHerm.l2_opNorm_eq (fun μ hμ => ?_) ⟨2 + 2 * c, hmax, by
      rw [RCLike.re_to_real, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 + 2 * c)]⟩
    obtain ⟨h1, h2⟩ := hIcc μ hμ
    rw [RCLike.re_to_real, abs_le]
    constructor <;> linarith
  have hnormBinv : ‖B⁻¹‖ = (2 - 2 * c)⁻¹ := by
    refine hHerm.l2_opNorm_inv_eq hm (fun μ hμ => ?_)
      ⟨2 - 2 * c, hmin, by
        rw [RCLike.re_to_real, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - 2 * c)]⟩
    obtain ⟨h1, h2⟩ := hIcc μ hμ
    rw [RCLike.re_to_real, abs_of_nonneg (by linarith)]
    linarith
  rw [NormedRing.condNumber_smul hn1.ne' B, NormedRing.condNumber,
    ← Matrix.nonsing_inv_eq_ringInverse, hnormB, hnormBinv]
  have h2 : (2 : ℝ) - 2 * c ≠ 0 := by linarith
  have h1 : (1 : ℝ) - c ≠ 0 := by linarith
  field_simp

end AtkinsonHan.Chapter10
