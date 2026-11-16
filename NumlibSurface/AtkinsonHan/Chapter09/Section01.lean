/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.ZetaValues
import Numlib.Analysis.Fourier.CosineBasis
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.InnerProductSpace.WeakCompactness
import Numlib.Projection.Basic
import Numlib.Projection.Optimality
import Numlib.Variational.Forms
import Numlib.Variational.EllipticInterval
import Numlib.Variational.Galerkin
import NumlibSurface.AtkinsonHan.Chapter08.Section03

/-!
# Atkinson and Han, Section 9.1: The Galerkin method

This module formalizes Section 9.1 of [han2009theoretical]. Let $V$ be a real inner product space,
$a$ a bilinear form on $V$, $\ell \in V'$ and $V_N \subseteq V$ a subspace. The form $a$ is bounded
with constant $M$ if $|a(u, v)| \le M \|u\| \|v\|$, and $V$-elliptic with constant $c_0$ if
$a(v, v) \ge c_0 \|v\|^2$, for all $u, v \in V$. The problem (9.1.1) asks for $u \in V$ with
$a(u, v) = \ell(v)$ for all $v \in V$. The Galerkin method (9.1.4) replaces it by the problem of
finding $u_N \in V_N$ with $a(u_N, v) = \ell(v)$ for all $v \in V_N$. In a basis $\{\phi_i\}$ of
$V_N$ this is a linear system with the stiffness matrix and the load vector (9.1.5). For a symmetric
form it is equivalent to the minimization of the energy $E(v) = \frac12 a(v, v) - \ell(v)$ over
$V_N$ (the Ritz formulation (9.1.6)–(9.1.8)). Céa's inequality (Proposition 9.1.3) bounds the error
by $\|u - u_N\| \le (M / c_0) \inf_{v \in V_N} \|u - v\|$, and Corollary 9.1.4 gives convergence for
an increasing sequence of trial spaces with dense union. The abstract results specialize
`IsGalerkinSolution` of `Numlib.Variational.Galerkin`.

Examples 9.1.1 and 9.1.2 apply the method to $-u'' = f$ on $(0, 1)$ with $u(0) = u(1) = 0$, posed
weakly on $H_0^1(0, 1)$ with $a(u, v) = \int_0^1 u' v' \, dx$ and $\ell(v) = \int_0^1 f v \, dx$.
Example 9.1.1 uses the trial space $V_N = \operatorname{span}\{x^i (1 - x) : 1 \le i \le N\}$, and
Example 9.1.2 uses $V_N = \operatorname{span}\{\sin(i \pi x) : 1 \le i \le N\}$, whose basis is
orthogonal for $a$, so that the Galerkin solution is the kernel approximation (9.1.10). The examples
use `SobolevIntervalZero` of `Numlib.Analysis.Sobolev.Interval` and `EllipticInterval.form` of
`Numlib.Variational.EllipticInterval`. The exercises give the stiffness matrix properties (Exercise
9.1.2), the sine expansion of the Green kernel (Exercise 9.1.3), and a second existence proof for
(9.1.1) through the Galerkin method (Exercise 9.1.4).

## Main definitions

* Equation (9.1.4), `AtkinsonHan.GalerkinProblem`: $u_N \in V_N$ and $a(u_N, v) = \ell(v)$ for all
  $v \in V_N$.
* Equation (9.1.5), `AtkinsonHan.stiffnessMatrix`: the matrix $A = (a(\phi_j, \phi_i))_{i,j}$.
* Equation (9.1.5), `AtkinsonHan.loadVector`: the vector $b = (\ell(\phi_i))_i$.
* Example 9.1.1, `AtkinsonHan.Chapter09.dirichletForm`: the form $a(u, v) = \int_0^1 u' v' \, dx$ on
  $H^1(0, 1)$.
* Example 9.1.1, `AtkinsonHan.Chapter09.polySpace`: the trial space $\operatorname{span}\{x^i (1 -
  x) : 1 \le i \le N\}$.
* Example 9.1.2, `AtkinsonHan.Chapter09.sineSpace`: the trial space $\operatorname{span}\{\sin(i \pi
  x) : 1 \le i \le N\}$.
* Example 9.1.2, `AtkinsonHan.Chapter09.sineGalerkin`: the Galerkin solution
  $u_N = \sum_{j=1}^N \xi_j \sin(j \pi x)$.

## Main results

* Equation (9.1.5), `AtkinsonHan.Chapter09.galerkinProblem_iff_mulVec`: the Galerkin problem for
  $u_N = \sum_j \xi_j \phi_j$ is the linear system $A \xi = b$.
* Equation (9.1.8), `AtkinsonHan.Chapter09.galerkinProblem_iff_isMinOn`: for a symmetric
  $V$-elliptic form, $u_N$ solves the Galerkin problem if and only if it minimizes the energy over
  $V_N$.
* Example 9.1.1, `AtkinsonHan.Chapter09.example_9_1_1`: unique solvability of the weak problem and
  of its Galerkin approximation, and the entries of the stiffness matrix and the load vector.
* Example 9.1.2, `AtkinsonHan.Chapter09.example_9_1_2`: the sine basis is $a$-orthogonal, the
  Galerkin solution has explicit coefficients, and it is the kernel approximation (9.1.10).
* Equation (9.1.12), `AtkinsonHan.Chapter09.galerkin_orthogonality`: $a(u - u_N, v) = 0$ for all
  $v \in V_N$.
* Proposition 9.1.3, `AtkinsonHan.Chapter09.proposition_9_1_3_le`:
  $\|u - u_N\| \le (M / c_0) \|u - v\|$ for every $v \in V_N$.
* Proposition 9.1.3, `AtkinsonHan.Chapter09.proposition_9_1_3`: Céa's inequality $\|u - u_N\| \le (M
  / c_0) \inf_{v \in V_N} \|u - v\|$.
* Remark after Proposition 9.1.3, `AtkinsonHan.Chapter09.galerkin_eq_energyProjection`: for a
  symmetric form, $u_N$ is the orthogonal projection of $u$ onto $V_N$ in the energy inner product.
* Remark after Proposition 9.1.3, `AtkinsonHan.Chapter09.proposition_9_1_3_sqrt`: for a symmetric
  form, the constant $M / c_0$ improves to $\sqrt{M / c_0}$.
* Corollary 9.1.4, `AtkinsonHan.Chapter09.corollary_9_1_4`: if the trial spaces increase and their
  union is dense, then $u_N \to u$.
* Exercise 9.1.2, `AtkinsonHan.Chapter09.stiffnessMatrix_isSymm`: a symmetric form has a symmetric
  stiffness matrix.
* Exercise 9.1.3, `AtkinsonHan.Chapter09.exercise_9_1_3`: $\min(x, t) (1 - \max(x, t)) =
  \frac{2}{\pi^2} \sum_{j \ge 1} \sin(j \pi x) \sin(j \pi t) / j^2$ on $[0, 1]^2$.
* Exercise 9.1.4(a), `AtkinsonHan.Chapter09.eq_zero_of_galerkinProblem_zero`: for $\ell = 0$ the
  only Galerkin solution is $0$.
* Exercise 9.1.4(a), `AtkinsonHan.Chapter09.exercise_9_1_4_a`: the Galerkin problem on a
  finite-dimensional $V_N$ has a unique solution, without the boundedness of $a$.
* Exercise 9.1.4(b)–(e), `AtkinsonHan.Chapter09.exercise_9_1_4`: the Galerkin solutions converge to
  a solution of (9.1.1).
* Exercise 9.1.4, `AtkinsonHan.Chapter09.existsUnique_solution_of_galerkin`: an increasing sequence
  of finite-dimensional subspaces with dense union makes (9.1.1) uniquely solvable.

## Implementation notes

* The form is `AtkinsonHan.BilinForm V` with the predicates `AtkinsonHan.BilinForm.IsBoundedWith`
  and `AtkinsonHan.BilinForm.IsEllipticWith`. The space $V$ is a real inner product space, and it is
  complete only where a statement assumes `CompleteSpace V`.
* The unique solvability of (9.1.1) itself is the Lax–Milgram lemma
  `AtkinsonHan.Chapter08.theorem_8_3_4`, and it is not restated here. The proof of
  `AtkinsonHan.Chapter09.existsUnique_solution_of_galerkin` does not use it, so that Exercise 9.1.4
  is a second proof of the Lax–Milgram lemma.
* In Examples 9.1.1 and 9.1.2 the basis functions are indexed from $0$: the function with index $k$
  is $x^{k+1} (1 - x)$ in `AtkinsonHan.Chapter09.polyBasis` and $\sin((k+1) \pi x)$ in
  `AtkinsonHan.Chapter09.sineBasis`.

## Deviations from the source

* **Example 9.1.1** (correction). With the indexing of the source, the displayed formula for the
  stiffness matrix entries is off by one; it holds for the basis indexed from $0$. See
  `AtkinsonHan.Chapter09.example_9_1_1`.

## Not formalized

* **Table 9.1.** The condition numbers of the stiffness matrix of Example 9.1.1 are numerical
  output.
-/

open Filter Topology
open scoped InnerProductSpace Real

namespace AtkinsonHan

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Equation (9.1.4)** of [han2009theoretical]. Let $a$ be a bilinear form on a real inner product
space $V$, let $\ell \in V'$, and let $V_N \subseteq V$ be a subspace. An element $u_N \in V$
**solves the Galerkin problem** if $u_N \in V_N$ and $$a(u_N, v) = \ell(v) \quad \text{for all }
v \in V_N.$$
-/
def GalerkinProblem (a : BilinForm V) (ℓ : StrongDual ℝ V) (VN : Submodule ℝ V) (uN : V) : Prop :=
  uN ∈ VN ∧ ∀ v ∈ VN, a uN v = ℓ v

/-- **Equation (9.1.5)** of [han2009theoretical], the stiffness matrix. For a bilinear form $a$ on
$V$ and elements $\phi_1, \dots, \phi_N \in V$, the **stiffness matrix** is the $N \times N$
matrix $A$ with entries $A_{ij} = a(\phi_j, \phi_i)$.

The indices run over `Fin N`, that is, from $0$ to $N - 1$. -/
def stiffnessMatrix (a : BilinForm V) {N : ℕ} (φ : Fin N → V) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => a (φ j) (φ i)

/-- **Equation (9.1.5)** of [han2009theoretical], the load vector. For $\ell \in V'$ and elements
$\phi_1, \dots, \phi_N \in V$, the **load vector** is the vector $b \in \mathbb{R}^N$ with
entries $b_i = \ell(\phi_i)$. -/
def loadVector (ℓ : StrongDual ℝ V) {N : ℕ} (φ : Fin N → V) : Fin N → ℝ := fun i => ℓ (φ i)

namespace Chapter09

variable {a : BilinForm V} {M α c₀ : ℝ} {ℓ : StrongDual ℝ V} {VN : Submodule ℝ V} {u uN : V}

/-- Let $a$ be bounded with constant $M$. Then $u_N$ solves the Galerkin problem
`AtkinsonHan.GalerkinProblem` if and only if it is a Galerkin solution in the sense of the
backbone predicate `IsGalerkinSolution` for the bundled form `AtkinsonHan.BilinForm.toCLM a hM`. -/
theorem galerkinProblem_iff (hM : a.IsBoundedWith M) :
    GalerkinProblem a ℓ VN uN ↔ IsGalerkinSolution (a.toCLM hM) ℓ VN uN := Iff.rfl

/-!
### Well-posedness

The unique solvability of (9.1.1) under the conditions (9.1.2) and (9.1.3) on $a$ is the Lax–Milgram
lemma `AtkinsonHan.Chapter08.theorem_8_3_4`, and it is not restated here.
-/

/-- Let $a$ be bounded with constant $M$ and $V$-elliptic with constant $c_0 > 0$, let
$\ell \in V'$, and let $V_N \subseteq V$ be a finite-dimensional subspace. Then the Galerkin
problem (9.1.4) has exactly one solution $u_N$.

The restriction of $a$ to $V_N$ is bounded and $V_N$-elliptic with the same constants, and the
proof applies the Lax–Milgram lemma on $V_N$. The space $V$ need not be complete, because $V_N$
is finite-dimensional. -/
theorem existsUnique_galerkinProblem (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
    (ha : a.IsEllipticWith c₀) (ℓ : StrongDual ℝ V) (VN : Submodule ℝ V)
    [FiniteDimensional ℝ VN] : ∃! uN, GalerkinProblem a ℓ VN uN :=
  IsGalerkinSolution.existsUnique (a := a.toCLM hM) (ℓ := ℓ) (K := VN) hc₀ ha

/-! ### The linear system (9.1.5) -/

/-- **Equation (9.1.5)** of [han2009theoretical]. Let $a$ be bounded with constant $M$, let
$\ell \in V'$, and let $\phi_1, \dots, \phi_N$ be a basis of the subspace $V_N$. Then
$u_N = \sum_j \xi_j \phi_j$ solves the Galerkin problem (9.1.4) if and only if $$A \xi = b,$$
where $A$ is the stiffness matrix `AtkinsonHan.stiffnessMatrix` and $b$ is the load vector
`AtkinsonHan.loadVector` of the basis. -/
theorem galerkinProblem_iff_mulVec (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V)
    (VN : Submodule ℝ V) {N : ℕ} (φ : Module.Basis (Fin N) ℝ VN) (ξ : Fin N → ℝ) :
    GalerkinProblem a ℓ VN (∑ j, ξ j • (φ j : V)) ↔
      (stiffnessMatrix a fun i => (φ i : V)).mulVec ξ = loadVector ℓ fun i => (φ i : V) := by
  have hstar : star ξ = ξ := funext fun i => star_trivial (ξ i)
  rw [galerkinProblem_iff hM, IsGalerkinSolution.iff_mulVec φ ξ, hstar]
  rfl

/-! ### Exercise 9.1.2: symmetry and positive definiteness of the stiffness matrix -/

/-- The entries of the stiffness matrix are $A_{ij} = a(\phi_j, \phi_i)$. -/
theorem stiffnessMatrix_apply (a : BilinForm V) {N : ℕ} (φ : Fin N → V) (i j : Fin N) :
    stiffnessMatrix a φ i j = a (φ j) (φ i) := rfl

/-- **Exercise 9.1.2** of [han2009theoretical], symmetry. Let $a$ be a symmetric bilinear form on
$V$, and let $\phi_1, \dots, \phi_N \in V$. Then the stiffness matrix $A = (a(\phi_j, \phi_i))$
is symmetric: $A^T = A$. -/
theorem stiffnessMatrix_isSymm (hs : LinearMap.BilinForm.IsSymm a) {N : ℕ} (φ : Fin N → V) :
    (stiffnessMatrix a φ).IsSymm := by
  ext i j
  exact BilinForm.isSymm_iff.mp hs (φ i) (φ j)

/-- Exercise 9.1.2 in the form of Mathlib: if $a$ is symmetric, then the real stiffness matrix of
any $\phi_1, \dots, \phi_N$ is Hermitian (`Matrix.IsHermitian`). -/
theorem stiffnessMatrix_isHermitian (hs : LinearMap.BilinForm.IsSymm a) {N : ℕ} (φ : Fin N → V) :
    (stiffnessMatrix a φ).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.2 (stiffnessMatrix_isSymm hs φ)

/-- For any bilinear form $a$, elements $\phi_1, \dots, \phi_N \in V$ and vectors
$\xi, \eta \in \mathbb{R}^N$, the stiffness matrix $A$ satisfies $$\eta^T A \xi = a\Big(\sum_j
\xi_j \phi_j, \sum_i \eta_i \phi_i\Big).$$
-/
theorem dotProduct_stiffnessMatrix_mulVec (a : BilinForm V) {N : ℕ} (φ : Fin N → V)
    (ξ η : Fin N → ℝ) :
    η ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ = a (∑ j, ξ j • φ j) (∑ i, η i • φ i) := by
  have hL : η ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ
      = ∑ i, ∑ j, η i * ξ j * a (φ j) (φ i) := by
    simp only [dotProduct, Matrix.mulVec, stiffnessMatrix, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hR : a (∑ j, ξ j • φ j) (∑ i, η i • φ i)
      = ∑ i, ∑ j, η i * ξ j * a (φ j) (φ i) := by
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hL, hR]

/-- Exercise 9.1.2, positivity. Let $a$ be $V$-elliptic with constant $\alpha > 0$, and let
$\phi_1, \dots, \phi_N \in V$ be linearly independent. Then $\xi^T A \xi > 0$ for every
$\xi \in \mathbb{R}^N$ with $\xi \neq 0$.

This half of the exercise does not need the symmetry of $a$. -/
theorem stiffnessMatrix_dotProduct_pos (hα : 0 < α) (ha : a.IsEllipticWith α) {N : ℕ}
    {φ : Fin N → V} (hφ : LinearIndependent ℝ φ) {ξ : Fin N → ℝ} (hξ : ξ ≠ 0) :
    0 < ξ ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ := by
  rw [dotProduct_stiffnessMatrix_mulVec]
  have hne : (∑ j, ξ j • φ j) ≠ 0 := fun h =>
    hξ (funext fun i => Fintype.linearIndependent_iff.mp hφ ξ h i)
  have hnorm : 0 < ‖(∑ j, ξ j • φ j : V)‖ := norm_pos_iff.mpr hne
  exact lt_of_lt_of_le (mul_pos hα (pow_pos hnorm 2)) (ha _)

/-- Exercise 9.1.2 in the form of Mathlib: if $a$ is symmetric and $V$-elliptic with constant
$\alpha > 0$, and $\phi_1, \dots, \phi_N \in V$ are linearly independent, then the stiffness
matrix is positive definite (`Matrix.PosDef`). -/
theorem stiffnessMatrix_posDef (hs : LinearMap.BilinForm.IsSymm a) (hα : 0 < α)
    (ha : a.IsEllipticWith α) {N : ℕ} {φ : Fin N → V} (hφ : LinearIndependent ℝ φ) :
    (stiffnessMatrix a φ).PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos (stiffnessMatrix_isHermitian hs φ) fun _ hx => by
    rw [show star _ = _ from funext fun i => star_trivial _]
    exact stiffnessMatrix_dotProduct_pos hα ha hφ hx

/-! ### The Ritz formulation (9.1.6)–(9.1.8) and Exercise 9.1.1 -/

/-- **Equation (9.1.8)** of [han2009theoretical] and **Exercise 9.1.1**. Let $V$ be a real Hilbert
space, let $a$ be symmetric, bounded with constant $M$ and $V$-elliptic with constant $c_0 > 0$,
let $\ell \in V'$, and let $V_N \subseteq V$ be a subspace. Then $u_N$ solves the Galerkin
problem (9.1.4) if and only if $u_N \in V_N$ and $u_N$ minimizes the energy (9.1.7) $$E(v) =
\tfrac12 a(v, v) - \ell(v)$$ over $V_N$.

For $V_N = V$ this is the equivalence (9.1.6) of the variational problem with the minimization
of $E$ over $V$. The energy is `AtkinsonHan.BilinForm.energy`. -/
theorem galerkinProblem_iff_isMinOn [CompleteSpace V] (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
    (ha : a.IsEllipticWith c₀) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    (VN : Submodule ℝ V) (uN : V) :
    GalerkinProblem a ℓ VN uN ↔ uN ∈ VN ∧ IsMinOn (a.energy ℓ) (VN : Set V) uN := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Chapter08.theorem_8_3_3_subspace hM hc₀ ha hs ℓ VN h1).mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Chapter08.theorem_8_3_3_subspace hM hc₀ ha hs ℓ VN h1).mp h2⟩

/-! ### Céa's inequality (Proposition 9.1.3) -/

/-- **Equation (9.1.12)** of [han2009theoretical] (Galerkin orthogonality). Let $a$ be bounded with
constant $M$, let $u \in V$ satisfy $a(u, v) = \ell(v)$ for all $v \in V$, and let $u_N$ solve
the Galerkin problem (9.1.4) on $V_N$. Then $$a(u - u_N, v) = 0 \quad \text{for all } v \in
V_N.$$
-/
theorem galerkin_orthogonality (hM : a.IsBoundedWith M) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) : a (u - uN) v = 0 :=
  IsGalerkinSolution.apply_sub_eq_zero (a := a.toCLM hM) huN hu hv

/-- **Proposition 9.1.3** of [han2009theoretical] (Céa's inequality), pointwise form. Let $a$ be
bounded with constant $M$ and $V$-elliptic with constant $c_0 > 0$. Let $u \in V$ satisfy
$a(u, v) = \ell(v)$ for all $v \in V$, and let $u_N$ solve the Galerkin problem (9.1.4) on
$V_N$. Then $$\|u - u_N\| \le \frac{M}{c_0} \|u - v\| \quad \text{for every } v \in V_N.$$
-/
theorem proposition_9_1_3_le (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hu : ∀ v, a u v = ℓ v) (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    ‖u - uN‖ ≤ M / c₀ * ‖u - v‖ :=
  IsGalerkinSolution.norm_sub_le hc₀ (BilinForm.isBoundedWith_toCLM hM) ha huN hu hv

/-- For $u \in V$ and a subspace $K \subseteq V$, the infimum $\inf_{v \in K} \|u - v\|$ equals the
distance from $u$ to $K$ (`Metric.infDist`).

This connects the infimum of (9.1.11) with the distance in which the backbone states its
quasi-optimality bounds. Section 10.4 uses it again for (10.4.5). -/
theorem iInf_norm_sub_eq_infDist (u : V) (K : Submodule ℝ V) :
    (⨅ v : K, ‖u - (v : V)‖) = Metric.infDist u (K : Set V) := by
  simp [Metric.infDist_eq_iInf, dist_eq_norm]

/-- **Proposition 9.1.3** of [han2009theoretical] (Céa's inequality). Let $a$ be bounded with
constant $M$ and $V$-elliptic with constant $c_0 > 0$. Let $u \in V$ satisfy $a(u, v) = \ell(v)$
for all $v \in V$, and let $u_N$ solve the Galerkin problem (9.1.4) on a subspace $V_N$. Then
(9.1.11) holds: $$\|u - u_N\| \le \frac{M}{c_0} \inf_{v \in V_N} \|u - v\|.$$

The proof uses neither that $V_N$ is finite-dimensional nor that $V$ is complete. -/
theorem proposition_9_1_3 (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hu : ∀ v, a u v = ℓ v) (huN : GalerkinProblem a ℓ VN uN) :
    ‖u - uN‖ ≤ M / c₀ * ⨅ v : VN, ‖u - (v : V)‖ := by
  rw [iInf_norm_sub_eq_infDist]
  exact IsGalerkinSolution.norm_sub_le_infDist hc₀ (BilinForm.isBoundedWith_toCLM hM) ha huN hu

/-! ### The symmetric case: best approximation in the energy norm -/

/-- **Section 9.1** of [han2009theoretical], remark after Proposition 9.1.3. Let $a$ be symmetric,
bounded with constant $M$ and $V$-elliptic with constant $c_0 > 0$. Let $u \in V$ satisfy
$a(u, v) = \ell(v)$ for all $v \in V$, and let $u_N$ solve the Galerkin problem (9.1.4) on
$V_N$. Then, in the energy norm $\|w\|_a = \sqrt{a(w, w)}$, $$\|u - u_N\|_a \le \|u - v\|_a
\quad \text{for every } v \in V_N.$$

The energy norm is `AtkinsonHan.BilinForm.energyNorm`. -/
theorem energyNorm_sub_le (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hs : LinearMap.BilinForm.IsSymm a) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    a.energyNorm (u - uN) ≤ a.energyNorm (u - v) :=
  IsGalerkinSolution.energyNorm_sub_le ((BilinForm.isSymm_iff_isHermitian hM).mp hs)
    (SesqForm.IsCoerciveWith.mono (a.toCLM hM) ha hc₀.le) huN hu hv

/-- Under the hypotheses of `AtkinsonHan.Chapter09.energyNorm_sub_le`, the Galerkin error is the
best approximation error in the energy norm: $\|u - u_N\|_a = \inf_{v \in V_N} \|u - v\|_a$. -/
theorem energyNorm_sub_eq_iInf (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
    (ha : a.IsEllipticWith c₀) (hs : LinearMap.BilinForm.IsSymm a) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) :
    a.energyNorm (u - uN) = ⨅ v : VN, a.energyNorm (u - (v : V)) := by
  have hbdd : BddBelow (Set.range fun v : VN => a.energyNorm (u - (v : V))) :=
    ⟨0, Set.forall_mem_range.2 fun v => BilinForm.energyNorm_nonneg a _⟩
  have : Nonempty VN := ⟨⟨uN, huN.1⟩⟩
  refine le_antisymm (le_ciInf fun v => energyNorm_sub_le hM hc₀ ha hs hu huN v.2) ?_
  exact ciInf_le hbdd ⟨uN, huN.1⟩

/-- **Section 9.1** of [han2009theoretical], remark after Proposition 9.1.3. Let $V$ be a real
Hilbert space, let $a$ be bounded with constant $M$, and let the operator $A : V \to V$ with
$(Au, v) = a(u, v)$ be symmetric and coercive. Let $V_N \subseteq V$ be finite-dimensional, let
$u \in V$ satisfy $a(u, v) = \ell(v)$ for all $v \in V$, and let $u_N$ solve the Galerkin
problem (9.1.4) on $V_N$. Then $u_N$ is the orthogonal projection of $u$ onto $V_N$ for the
energy inner product $(v, w)_a = a(v, w)$.

The operator $A$ is `AtkinsonHan.BilinForm.toOperator a hM`, and the hypothesis on it is
`LinearMap.IsSymmetricCoercive`, which `AtkinsonHan.Chapter09.isSymmetricBoundedBy_toOperator`
of Section 9.4 derives from the boundedness, the symmetry and the $V$-ellipticity of $a$. The
space $V$ with the energy inner product is `WithEnergy`, and the conclusion is stated with
`WithEnergy.equiv` and the projection onto `WithEnergy.submoduleMap`. This result makes
`AtkinsonHan.Chapter09.energyNorm_sub_eq_iInf` a statement on best approximation. -/
theorem galerkin_eq_energyProjection [CompleteSpace V] (hM : a.IsBoundedWith M)
    (hA : (BilinForm.toOperator a hM : V →ₗ[ℝ] V).IsSymmetricCoercive) [FiniteDimensional ℝ VN]
    (hu : ∀ v, a u v = ℓ v) (huN : GalerkinProblem a ℓ VN uN) :
    WithEnergy.equiv _ hA uN
      = (WithEnergy.submoduleMap _ hA VN).starProjection (WithEnergy.equiv _ hA u) := by
  have hstar : (BilinForm.toOperator a hM : V →ₗ[ℝ] V) u = SesqForm.rieszRep ℓ :=
    (BilinForm.toOperator_eq_rieszRep_iff hM ℓ u).mpr hu
  have hx : IsGalerkin (BilinForm.toOperator a hM : V →ₗ[ℝ] V) (SesqForm.rieszRep ℓ) 0 VN uN :=
    IsGalerkinSolution.iff_isGalerkin.mp ((galerkinProblem_iff hM).mp huN)
  have herr := IsGalerkin.error_eq_starProjection hA hx hstar
  have hsplit := (WithEnergy.submoduleMap _ hA VN).starProjection_add_starProjection_orthogonal
    (WithEnergy.equiv _ hA u)
  rw [sub_zero] at herr
  have hlin : WithEnergy.equiv _ hA (u - uN)
      = WithEnergy.equiv _ hA u - WithEnergy.equiv _ hA uN := map_sub _ _ _
  rw [hlin] at herr
  rw [eq_sub_of_add_eq hsplit, ← herr]
  abel

/-- **Section 9.1** of [han2009theoretical], the symmetric case of Proposition 9.1.3. Let $a$ be
symmetric, bounded with constant $M$ and $V$-elliptic with constant $c_0 > 0$. Let $u \in V$
satisfy $a(u, v) = \ell(v)$ for all $v \in V$, and let $u_N$ solve the Galerkin problem (9.1.4)
on $V_N$. Then $$\|u - u_N\| \le \sqrt{M / c_0} \, \|u - v\| \quad \text{for every } v \in
V_N.$$
-/
theorem proposition_9_1_3_sqrt (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hs : LinearMap.BilinForm.IsSymm a) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    ‖u - uN‖ ≤ Real.sqrt (M / c₀) * ‖u - v‖ :=
  IsGalerkinSolution.norm_sub_le_sqrt hc₀ (BilinForm.isBoundedWith_toCLM hM) ha
    ((BilinForm.isSymm_iff_isHermitian hM).mp hs) huN hu hv

/-! ### Corollary 9.1.4 -/

/-- **Corollary 9.1.4** of [han2009theoretical]. Let $a$ be bounded with constant $M$ and
$V$-elliptic with constant $c_0 > 0$, and let $\ell \in V'$. Let
$V_1 \subseteq V_2 \subseteq \cdots$ be subspaces of $V$ whose union is dense in $V$ (9.1.13).
Let $u \in V$ satisfy $a(u, v) = \ell(v)$ for all $v \in V$, and let $u_n$ solve the Galerkin
problem (9.1.4) on $V_n$ for each $n$. Then (9.1.14) holds: $$\|u - u_n\| \to 0 \quad \text{as }
n \to \infty.$$

The sequence of subspaces is indexed by $n \in \mathbb{N}$, starting at $0$. -/
theorem corollary_9_1_4 (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (ℓ : StrongDual ℝ V) (VN : ℕ → Submodule ℝ V) (hmono : Monotone VN)
    (hdense : Dense (⋃ n, (VN n : Set V))) (hu : ∀ v, a u v = ℓ v) (uN : ℕ → V)
    (huN : ∀ n, GalerkinProblem a ℓ (VN n) (uN n)) :
    Tendsto (fun n => ‖u - uN n‖) atTop (𝓝 0) := by
  have h := IsGalerkinSolution.tendsto (a := a.toCLM hM) (ℓ := ℓ) hc₀
    (BilinForm.isBoundedWith_toCLM hM) ha hmono hdense huN hu
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  simpa only [norm_sub_rev] using h

/-! ### Exercise 9.1.3: the Fourier expansion of the Green kernel -/

/-- The second Bernoulli polynomial, mapped to $\mathbb{R}$, is $B_2(x) = x^2 - x + 1/6$. -/
private theorem bernoulli_two_eval (x : ℝ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)).eval x = x ^ 2 - x + 1 / 6 := by
  simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_eq_bernoulli'_of_ne_one]
  ring

/-- For $\theta \in [0, 2\pi]$, $\sum_{n \ge 1} \cos(n \theta) / n^2 = \pi^2 / 6 - \pi \theta / 2 +
\theta^2 / 4$, with the sum over all $n \in \mathbb{N}$ and the term $n = 0$ equal to
$\cos 0 / 0 = 0$. -/
private theorem hasSum_cos_div_sq {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * π)) :
    HasSum (fun n : ℕ => Real.cos (n * θ) / n ^ 2) (π ^ 2 / 6 - π * θ / 2 + θ ^ 2 / 4) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hx : θ / (2 * π) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hθ.1 (by positivity), (div_le_one (by positivity)).2 hθ.2⟩
  convert hasSum_one_div_nat_pow_mul_cos one_ne_zero hx using 1
  · ext1 n
    have harg : 2 * π * (n : ℝ) * (θ / (2 * π)) = n * θ := by field_simp
    rw [harg]
    norm_num
    ring
  · rw [show (2 * 1 : ℕ) = 2 from rfl, bernoulli_two_eval]
    norm_num [Nat.factorial]
    field_simp
    ring

/-- For $0 \le x \le t \le 1$, $\frac{2}{\pi^2} \sum_{n} \sin(n \pi x) \sin(n \pi t) / n^2 = x (1 -
t)$, with the sum over all $n \in \mathbb{N}$. -/
private theorem hasSum_kernel_aux {x t : ℝ} (hx0 : 0 ≤ x) (hxt : x ≤ t) (ht1 : t ≤ 1) :
    HasSum (fun n : ℕ => 2 / π ^ 2 * (Real.sin (n * π * x) * Real.sin (n * π * t) / n ^ 2))
      (x * (1 - t)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h1 := hasSum_cos_div_sq (θ := π * (t - x)) ⟨by nlinarith, by nlinarith⟩
  have h2 := hasSum_cos_div_sq (θ := π * (t + x)) ⟨by nlinarith, by nlinarith⟩
  have hfun : ∀ n : ℕ, 2 / π ^ 2 * (Real.sin (n * π * x) * Real.sin (n * π * t) / n ^ 2)
      = 1 / π ^ 2 * (Real.cos ((n : ℝ) * (π * (t - x))) / (n : ℝ) ^ 2
        - Real.cos ((n : ℝ) * (π * (t + x))) / (n : ℝ) ^ 2) := by
    intro n
    have ha : (n : ℝ) * (π * (t - x)) = n * π * t - n * π * x := by ring
    have hb : (n : ℝ) * (π * (t + x)) = n * π * t + n * π * x := by ring
    rw [ha, hb, Real.cos_sub, Real.cos_add]
    ring
  have hval : x * (1 - t) = 1 / π ^ 2 *
      ((π ^ 2 / 6 - π * (π * (t - x)) / 2 + (π * (t - x)) ^ 2 / 4)
        - (π ^ 2 / 6 - π * (π * (t + x)) / 2 + (π * (t + x)) ^ 2 / 4)) := by
    field_simp
    ring
  rw [funext hfun, hval]
  exact (h1.sub h2).mul_left _

/-- For $x, t \in [0, 1]$, $\frac{2}{\pi^2} \sum_{n} \sin(n \pi x) \sin(n \pi t) / n^2 = \min(x, t)
(1 - \max(x, t))$, with the sum over all $n \in \mathbb{N}$. -/
private theorem hasSum_kernel {x t : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 2 / π ^ 2 * (Real.sin (n * π * x) * Real.sin (n * π * t) / n ^ 2))
      (min x t * (1 - max x t)) := by
  rcases le_total x t with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact hasSum_kernel_aux hx.1 h ht.2
  · rw [min_eq_right h, max_eq_left h]
    have hcomm : ∀ n : ℕ, 2 / π ^ 2 * (Real.sin (n * π * x) * Real.sin (n * π * t) / n ^ 2)
        = 2 / π ^ 2 * (Real.sin (n * π * t) * Real.sin (n * π * x) / n ^ 2) := fun n => by ring
    rw [funext hcomm]
    exact hasSum_kernel_aux ht.1 h hx.2

/-- **Exercise 9.1.3** of [han2009theoretical]. For $x, t \in [0, 1]$, the Green kernel
$K(x, t) = \min(x, t) (1 - \max(x, t))$ of $-u'' = f$ on $(0, 1)$ with $u(0) = u(1) = 0$, which
is the kernel of the solution formula (9.1.15), has the expansion $$K(x, t) = \frac{2}{\pi^2}
\sum_{j=1}^{\infty} \frac{\sin(j \pi x) \sin(j \pi t)}{j^2}.$$

The statement is pointwise, as a `HasSum` at each pair $(x, t)$, and the summation index is
shifted to start at $0$. The series converges absolutely, since its terms are bounded by
$1 / j^2$. The kernel $K_N$ of (9.1.10) is the $N$-th partial sum of this series. That the
Galerkin solution of Example 9.1.2 is $u_N(x) = \int_0^1 f(t) K_N(x, t) \, dt$ is
`AtkinsonHan.Chapter09.rep_sineGalerkin`. -/
theorem exercise_9_1_3 {x t : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun j : ℕ => 2 / π ^ 2 *
        (Real.sin (((j : ℝ) + 1) * π * x) * Real.sin (((j : ℝ) + 1) * π * t) / ((j : ℝ) + 1) ^ 2))
      (min x t * (1 - max x t)) := by
  have h0 : HasSum (fun n : ℕ => 2 / π ^ 2 *
      (Real.sin (n * π * x) * Real.sin (n * π * t) / (n : ℝ) ^ 2))
      (min x t * (1 - max x t) + ∑ i ∈ Finset.range 1, 2 / π ^ 2 *
        (Real.sin (i * π * x) * Real.sin (i * π * t) / (i : ℝ) ^ 2)) := by
    simpa using hasSum_kernel hx ht
  have hshift : ∀ n : ℕ, 2 / π ^ 2 *
      (Real.sin (((n : ℝ) + 1) * π * x) * Real.sin (((n : ℝ) + 1) * π * t) / ((n : ℝ) + 1) ^ 2)
      = 2 / π ^ 2 * (Real.sin ((↑(n + 1) : ℝ) * π * x) * Real.sin ((↑(n + 1) : ℝ) * π * t)
        / (↑(n + 1) : ℝ) ^ 2) := by
    intro n
    push_cast
    ring
  rw [funext hshift]
  exact (hasSum_nat_add_iff 1).2 h0

/-! ### Exercise 9.1.4: the Galerkin method as a second existence proof -/

/-- **Exercise 9.1.4(a)** of [han2009theoretical], uniqueness. Let $a$ be $V$-elliptic with constant
$c_0 > 0$. If $u_N$ solves the Galerkin problem (9.1.4) on $V_N$ with $\ell = 0$, then
$u_N = 0$.

The proof tests the equation with $u_N$ itself. It needs neither the boundedness of $a$, nor the
completeness of $V$, nor that $V_N$ is finite-dimensional. -/
theorem eq_zero_of_galerkinProblem_zero (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (h : GalerkinProblem a (0 : StrongDual ℝ V) VN uN) : uN = 0 := by
  have h0 : a uN uN = 0 := by simpa using h.2 uN h.1
  have hle : c₀ * ‖uN‖ ^ 2 ≤ 0 := h0 ▸ ha uN
  have hsq : ‖uN‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

/-- **Exercise 9.1.4(a)** of [han2009theoretical]. Let $a$ be $V$-elliptic with constant $c_0 > 0$,
let $\ell \in V'$, and let $V_N \subseteq V$ be finite-dimensional. Then the Galerkin problem
(9.1.4) has exactly one solution.

The proof is the argument of the source: the square linear system is injective by
`AtkinsonHan.Chapter09.eq_zero_of_galerkinProblem_zero`, hence surjective. It does not use the
Lax–Milgram lemma on $V_N$, as `AtkinsonHan.Chapter09.existsUnique_galerkinProblem` does.
Therefore it assumes neither the boundedness of $a$ nor the completeness of $V$, and the rest of
Exercise 9.1.4 does not depend on the Lax–Milgram lemma. -/
theorem exercise_9_1_4_a (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) (ℓ : StrongDual ℝ V)
    (VN : Submodule ℝ V) [FiniteDimensional ℝ VN] : ∃! uN, GalerkinProblem a ℓ VN uN := by
  obtain ⟨b, hb⟩ : ∃ b : VN →ₗ[ℝ] Module.Dual ℝ VN, ∀ w v : VN, b w v = a (w : V) (v : V) :=
    ⟨LinearMap.BilinForm.restrict a VN, fun _ _ => rfl⟩
  have hinj : Function.Injective b := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun z hz => ?_)
    refine Subtype.ext (eq_zero_of_galerkinProblem_zero hc₀ ha ⟨z.2, fun v hv => ?_⟩)
    have := congrArg (fun φ : Module.Dual ℝ VN => φ ⟨v, hv⟩) hz
    simpa [hb] using this
  have hsurj : Function.Surjective b :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).1 hinj
  obtain ⟨z, hz⟩ := hsurj ((ℓ : V →ₗ[ℝ] ℝ).domRestrict VN)
  have hsol : ∀ v ∈ VN, a (z : V) v = ℓ v := by
    intro v hv
    have := congrArg (fun φ : Module.Dual ℝ VN => φ ⟨v, hv⟩) hz
    simpa [hb] using this
  refine ⟨(z : V), ⟨z.2, hsol⟩, fun y hy => ?_⟩
  refine sub_eq_zero.mp (eq_zero_of_galerkinProblem_zero hc₀ ha
    ⟨VN.sub_mem hy.1 z.2, fun v hv => ?_⟩)
  simp [map_sub, LinearMap.sub_apply, hy.2 v hv, hsol v hv]

/-- **Exercise 9.1.4(b)–(e)** of [han2009theoretical]. Let $V$ be a real Hilbert space, let $a$ be
bounded with constant $M$ and $V$-elliptic with constant $c_0 > 0$, and let $\ell \in V'$. Let
$V_1 \subseteq V_2 \subseteq \cdots$ be subspaces of $V$ with dense union, and let $u_n$ solve
the Galerkin problem (9.1.4) on $V_n$ for each $n$. Then there is $u \in V$ with
$a(u, v) = \ell(v)$ for all $v \in V$ and $$\|u - u_n\| \to 0 \quad \text{as } n \to \infty.$$

The proof follows the steps of the exercise. (b) The $V$-ellipticity gives
$\|u_n\| \le \|\ell\| / c_0$, so a subsequence converges weakly to some $u \in V$. (c) For fixed
$N$, $a(u_n, v) = \ell(v)$ holds for $v \in V_N$ and $n \ge N$, and the weak limit gives
$a(u, v) = \ell(v)$ for $v \in V_N$. (d) The union of the $V_N$ is dense and
$v \mapsto a(u, v) - \ell(v)$ is continuous, so $u$ solves (9.1.1). (e) Corollary 9.1.4 makes
the whole sequence converge to $u$ in norm.

As in the source, the increasing sequence of subspaces is given data. Its existence forces $V$
to be separable, a hypothesis that the source mentions but does not state. The subspaces need
not be finite-dimensional here; this enters only in the existence of the $u_n$, which is
Exercise 9.1.4(a). -/
theorem exercise_9_1_4 [CompleteSpace V] (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
    (ha : a.IsEllipticWith c₀) (ℓ : StrongDual ℝ V) (VN : ℕ → Submodule ℝ V)
    (hmono : Monotone VN) (hdense : Dense (⋃ n, (VN n : Set V))) (uN : ℕ → V)
    (huN : ∀ n, GalerkinProblem a ℓ (VN n) (uN n)) :
    ∃ u, (∀ v, a u v = ℓ v) ∧ Tendsto (fun n => ‖u - uN n‖) atTop (𝓝 0) := by
  -- (b) the discrete solutions are bounded by `‖ℓ‖ / c₀`.
  have hbdd : ∀ n, ‖uN n‖ ≤ ‖ℓ‖ / c₀ := by
    intro n
    have h1 : c₀ * ‖uN n‖ ^ 2 ≤ a (uN n) (uN n) := ha _
    have h2 : a (uN n) (uN n) = ℓ (uN n) := (huN n).2 _ (huN n).1
    have h3 : ℓ (uN n) ≤ ‖ℓ‖ * ‖uN n‖ := (Real.le_norm_self _).trans (ℓ.le_opNorm _)
    rcases eq_or_lt_of_le (norm_nonneg (uN n)) with h | h
    · rw [← h]
      exact div_nonneg (norm_nonneg ℓ) hc₀.le
    · rw [le_div_iff₀ hc₀]
      nlinarith
  obtain ⟨σ, w, hσ, hweak⟩ := exists_subseq_weak_tendsto (𝕜 := ℝ) hbdd
  -- the same weak convergence, in the form the functionals see it
  have hfun : ∀ f : StrongDual ℝ V, Tendsto (fun k => f (uN (σ k))) atTop (𝓝 (f w)) := by
    intro f
    have hval : ∀ z : V, ⟪z, (InnerProductSpace.toDual ℝ V).symm f⟫_ℝ = f z := fun z => by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    simpa only [hval] using hweak ((InnerProductSpace.toDual ℝ V).symm f)
  -- (c) the weak limit solves the variational equation on every `V_N`.
  have hcv : ∀ N : ℕ, ∀ v ∈ VN N, a w v = ℓ v := by
    intro N v hv
    have hlim1 : Tendsto (fun k => a (uN (σ k)) v) atTop (𝓝 (a w v)) :=
      hfun ((a.toCLM hM).flip v)
    have hlim2 : Tendsto (fun k => a (uN (σ k)) v) atTop (𝓝 (ℓ v)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop N] with k hk
      exact ((huN (σ k)).2 v (hmono (hk.trans hσ.le_apply) hv)).symm
    exact tendsto_nhds_unique hlim1 hlim2
  -- (d) the density (9.1.13) upgrades that to all of `V`.
  have hsol : ∀ v, a w v = ℓ v := by
    have hclosed : IsClosed {v : V | a.toCLM hM w v = ℓ v} :=
      isClosed_eq (a.toCLM hM w).continuous ℓ.continuous
    have hsub : (⋃ n, (VN n : Set V)) ⊆ {v : V | a.toCLM hM w v = ℓ v} := by
      rintro v hv
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hv
      exact hcv N v hN
    exact fun v => closure_minimal hsub hclosed (hdense v)
  -- (e) with a solution in hand, Corollary 9.1.4 moves the whole sequence.
  exact ⟨w, hsol, corollary_9_1_4 hM hc₀ ha ℓ VN hmono hdense hsol uN huN⟩

/-- **Exercise 9.1.4** of [han2009theoretical], conclusion. Let $V$ be a real Hilbert space, let $a$
be bounded with constant $M$ and $V$-elliptic with constant $c_0 > 0$, and let $\ell \in V'$. If
there are finite-dimensional subspaces $V_1 \subseteq V_2 \subseteq \cdots$ of $V$ with dense
union, then there is exactly one $u \in V$ with $a(u, v) = \ell(v)$ for all $v \in V$.

This is the Lax–Milgram lemma, proved through the Galerkin method: the finite-dimensional
problems of `AtkinsonHan.Chapter09.exercise_9_1_4_a`, a weakly convergent subsequence, and the
density (9.1.13). The proof does not use `AtkinsonHan.Chapter08.theorem_8_3_4`. Uniqueness is
`AtkinsonHan.Chapter09.eq_zero_of_galerkinProblem_zero` for $\ell = 0$ and $V_N = V$. -/
theorem existsUnique_solution_of_galerkin [CompleteSpace V] (hM : a.IsBoundedWith M)
    (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) (ℓ : StrongDual ℝ V) (VN : ℕ → Submodule ℝ V)
    [∀ n, FiniteDimensional ℝ (VN n)] (hmono : Monotone VN)
    (hdense : Dense (⋃ n, (VN n : Set V))) : ∃! u, ∀ v, a u v = ℓ v := by
  choose uN huN using fun n => (exercise_9_1_4_a hc₀ ha ℓ (VN n)).exists
  obtain ⟨u, hu, -⟩ := exercise_9_1_4 hM hc₀ ha ℓ VN hmono hdense uN huN
  refine ⟨u, hu, fun y hy => ?_⟩
  refine sub_eq_zero.mp (eq_zero_of_galerkinProblem_zero hc₀ ha
    ⟨Submodule.mem_top, fun v _ => ?_⟩)
  simp [map_sub, LinearMap.sub_apply, hy v, hu v]

/-!
### Example 9.1.1: the Galerkin method for $-u'' = f$ with the basis $x^i (1 - x)$

The weak problem asks for $u \in H_0^1(0, 1)$ with $\int_0^1 u' v' \, dx = \int_0^1 f v \, dx$ for
all $v \in H_0^1(0, 1)$, and the trial space is $V_N = \operatorname{span}\{x^i (1 - x) : 1 \le i
\le N\}$. The exponents are indexed from $0$ here: `AtkinsonHan.Chapter09.polyBasis k` is
$x^{k+1} (1 - x)$, and the family `AtkinsonHan.Chapter09.polyBasis` over `Fin N` spans $V_N$.
-/

section Example911

open MeasureTheory Set SobolevInterval
open scoped ContDiff

noncomputable section

/-- The basis function $x \mapsto x^{k+1} (1 - x)$ of Example 9.1.1. -/
def polyBasisFun (k : ℕ) : ℝ → ℝ := fun x => x ^ (k + 1) * (1 - x)

/-- The function $x^{k+1} (1 - x)$ is real analytic on $\mathbb{R}$. -/
theorem contDiff_polyBasisFun (k : ℕ) : ContDiff ℝ ω (polyBasisFun k) := by
  unfold polyBasisFun; fun_prop

/-- The function $x^{k+1} (1 - x)$ is continuously differentiable on $[0, 1]$. -/
theorem contDiffOn_polyBasisFun (k : ℕ) :
    ContDiffOn ℝ ((1 : ℕ) : ℕ∞ω) (polyBasisFun k) (Icc (0 : ℝ) 1) :=
  ((contDiff_polyBasisFun k).of_le le_top).contDiffOn

/-- The derivative of $x^{k+1} (1 - x)$ is $(k+1) x^k - (k+2) x^{k+1}$. -/
theorem deriv_polyBasisFun (k : ℕ) (x : ℝ) :
    _root_.deriv (polyBasisFun k) x = ((k : ℝ) + 1) * x ^ k - ((k : ℝ) + 2) * x ^ (k + 1) := by
  unfold polyBasisFun
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := (hasDerivAt_id x).const_sub 1
  have h : HasDerivAt (fun x : ℝ => x ^ (k + 1) * (1 - x))
      ((k + 1 : ℕ) * x ^ (k + 1 - 1) * (1 - x) + x ^ (k + 1) * (-1)) x :=
    (hasDerivAt_pow (k + 1) x).mul h1
  rw [h.deriv]
  push_cast
  ring

/-- The basis function $x^{k+1} (1 - x)$ as an element of $H^1(0, 1)$. -/
def polyBasis (k : ℕ) : SobolevInterval 1 0 1 :=
  ContDiffMapIcc.toSobolevInterval zero_le_one zero_lt_one 1
    (ContDiffMapIcc.ofContDiffOn zero_le_one zero_lt_one (contDiffOn_polyBasisFun k))

/-- The element `AtkinsonHan.Chapter09.polyBasis k` of $H^1(0, 1)$ agrees almost everywhere on
$(0, 1)$ with the function $x^{k+1} (1 - x)$. -/
theorem coeFn_deriv_polyBasis_zero (k : ℕ) :
    (SobolevInterval.deriv (polyBasis k) 0 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] polyBasisFun k := by
  refine (ContDiffMapIcc.coeFn_derivLp _ 0).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [IccExtend_of_mem zero_le_one _ (Ioo_subset_Icc_self hx)]
  rfl

/-- The weak derivative of `AtkinsonHan.Chapter09.polyBasis k` agrees almost everywhere on $(0, 1)$
with $(k+1) x^k - (k+2) x^{k+1}$. -/
theorem coeFn_deriv_polyBasis_one (k : ℕ) :
    (SobolevInterval.deriv (polyBasis k) 1 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => ((k : ℝ) + 1) * x ^ k - ((k : ℝ) + 2) * x ^ (k + 1) := by
  refine (ContDiffMapIcc.coeFn_derivLp _ 1).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  rw [IccExtend_of_mem zero_le_one _ hx',
    ContDiffMapIcc.deriv_ofContDiffOn zero_le_one zero_lt_one (contDiffOn_polyBasisFun k) 1
      ⟨x, hx'⟩,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((contDiff_polyBasisFun k).contDiffAt.of_le le_top) hx']
  simpa using deriv_polyBasisFun k x

/-- The function $x^{k+1} (1 - x)$ vanishes at $0$ and at $1$, so it lies in $H_0^1(0, 1)$. -/
theorem polyBasis_mem (k : ℕ) : polyBasis k ∈ SobolevIntervalZero 0 1 := by
  have hc : ContinuousOn (polyBasisFun k) (Icc (0 : ℝ) 1) :=
    (contDiff_polyBasisFun k).continuous.continuousOn
  rw [mem_sobolevIntervalZero_iff zero_lt_one]
  refine ⟨?_, ?_⟩ <;>
    rw [toContinuousMap_eq_of_continuousOn zero_lt_one _ hc (coeFn_deriv_polyBasis_zero k)] <;>
    simp [polyBasisFun]

/-- The constant coefficient $1$ as an element of $L^\infty(0, 1)$. -/
def oneLinf : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (ContinuousOn.memLp_top_restrict_Ioo (g := fun _ => (1 : ℝ)) continuousOn_const).toLp _

/-- The element `AtkinsonHan.Chapter09.oneLinf` of $L^\infty(0, 1)$ is equal to $1$ almost
everywhere on $(0, 1)$. -/
theorem coeFn_oneLinf : (oneLinf : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun _ => (1 : ℝ) :=
  MemLp.coeFn_toLp _

/-- The coefficient `AtkinsonHan.Chapter09.oneLinf` is at least $1$ almost everywhere on $(0, 1)$.
-/
theorem one_le_oneLinf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), (1 : ℝ) ≤ oneLinf x := by
  filter_upwards [coeFn_oneLinf] with x hx
  rw [hx]

/-- The zero element of $L^\infty(0, 1)$ is nonnegative almost everywhere on $(0, 1)$. -/
theorem zero_le_zeroLinf :
    ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      (0 : ℝ) ≤ (0 : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) x := by
  filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))] with x hx
  rw [hx]
  rfl

/-- The bilinear form of (9.1.9), $a(u, v) = \int_0^1 u' v' \, dx$ on $H^1(0, 1)$.

It is `EllipticInterval.form` with the coefficients $\alpha = 1$ and $\beta = \gamma = 0$. -/
def dirichletForm : SesqForm ℝ (SobolevInterval 1 0 1) := EllipticInterval.form 0 1 oneLinf 0 0

/-- For $u, v \in H^1(0, 1)$, the form of (9.1.9) is $a(u, v) = \int_0^1 u'(x) v'(x) \, dx$, with
the weak derivatives. -/
theorem dirichletForm_apply (u v : SobolevInterval 1 0 1) :
    dirichletForm u v = ∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv u 1 x *
      SobolevInterval.deriv v 1 x := by
  rw [dirichletForm, EllipticInterval.form_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_oneLinf, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))] with x h1 h0
  rw [h1, h0]
  simp

/-- The trial space of Example 9.1.1, $V_N = \operatorname{span}\{x^i (1 - x) : 1 \le i \le N\}$, as
a subspace of $H^1(0, 1)$. -/
def polySpace (N : ℕ) : Submodule ℝ (SobolevInterval 1 0 1) :=
  Submodule.span ℝ (Set.range fun i : Fin N => polyBasis i)

/-- The trial space $V_N$ of Example 9.1.1 is contained in $H_0^1(0, 1)$. -/
theorem polySpace_le (N : ℕ) : polySpace N ≤ SobolevIntervalZero 0 1 :=
  Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact polyBasis_mem i)

instance (N : ℕ) : FiniteDimensional ℝ (polySpace N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- For $n \in \mathbb{N}$, $\int_0^1 x^n \, dx = 1 / (n + 1)$. -/
theorem integral_pow_unit (n : ℕ) : ∫ x in (0 : ℝ)..1, x ^ n = 1 / (n + 1) := by
  rw [integral_pow]; simp

/-- Let $K$ be a complete subspace of $H^1(0, 1)$ with $K \subseteq H_0^1(0, 1)$, and let
$f \in L^2(0, 1)$. Then there is exactly one $u \in K$ with
$\int_0^1 u' v' \, dx = \int_0^1 f v \, dx$ for all $v \in K$.

The proof is the Lax–Milgram lemma; the form is coercive on $H_0^1(0, 1)$ by the Poincaré
inequality. For $K = H_0^1(0, 1)$ this is the weak problem of Example 9.1.1, and for $K = V_N$
it is its Galerkin approximation. The load $v \mapsto \int_0^1 f v \, dx$ is
`EllipticInterval.load`. -/
theorem existsUnique_dirichletGalerkin {K : Submodule ℝ (SobolevInterval 1 0 1)}
    (hK : K ≤ SobolevIntervalZero 0 1) [CompleteSpace K]
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f) K u := by
  have hc : (0 : ℝ) < 1 / (1 + ((1 : ℝ) - 0) ^ 2 / 2) := by norm_num
  have hcoer : (dirichletForm.restrict K).IsCoerciveWith (1 / (1 + ((1 : ℝ) - 0) ^ 2 / 2)) := by
    intro v
    have h := EllipticInterval.form_isCoerciveWith_restrict (a := 0) (b := 1) zero_lt_one oneLinf 0
      one_le_oneLinf zero_le_zeroLinf zero_le_one ⟨(v : SobolevInterval 1 0 1), hK v.2⟩
    rw [SesqForm.restrict_apply] at h
    rw [SesqForm.restrict_apply]
    simpa [dirichletForm] using h
  obtain ⟨w, hw, hwu⟩ := SesqForm.laxMilgram (dirichletForm.restrict K)
    ((EllipticInterval.load 0 1 f).comp K.subtypeL) hc hcoer
  refine ⟨(w : SobolevInterval 1 0 1), ⟨w.2, fun v hv => hw ⟨v, hv⟩⟩, ?_⟩
  rintro y ⟨hyK, hy⟩
  exact congrArg Subtype.val (hwu ⟨y, hyK⟩ fun z => hy (z : SobolevInterval 1 0 1) z.2)

/-- For $i, j \in \mathbb{N}$, the stiffness matrix entry of Example 9.1.1 is $$\int_0^1 [x^{j+1}
(1 - x)]' [x^{i+1} (1 - x)]' \, dx = \frac{(i+1)(j+1)}{i+j+1} + \frac{(i+2)(j+2)}{i+j+3} -
\frac{(i+1)(j+2) + (i+2)(j+1)}{i+j+2}.$$
-/
theorem dirichletForm_polyBasis (i j : ℕ) :
    dirichletForm (polyBasis j) (polyBasis i)
      = ((i : ℝ) + 1) * ((j : ℝ) + 1) / ((i : ℝ) + (j : ℝ) + 1)
        + ((i : ℝ) + 2) * ((j : ℝ) + 2) / ((i : ℝ) + (j : ℝ) + 3)
        - (((i : ℝ) + 1) * ((j : ℝ) + 2) + ((i : ℝ) + 2) * ((j : ℝ) + 1))
            / ((i : ℝ) + (j : ℝ) + 2) := by
  rw [dirichletForm_apply,
    show (∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv (polyBasis j) 1 x *
          SobolevInterval.deriv (polyBasis i) 1 x)
        = ∫ x in Ioo (0 : ℝ) 1,
          (((j : ℝ) + 1) * x ^ j - ((j : ℝ) + 2) * x ^ (j + 1)) *
            (((i : ℝ) + 1) * x ^ i - ((i : ℝ) + 2) * x ^ (i + 1)) from ?_]
  · rw [← intervalIntegral.integral_eq_setIntegral_Ioo zero_le_one]
    have hexp : ∀ x : ℝ,
        (((j : ℝ) + 1) * x ^ j - ((j : ℝ) + 2) * x ^ (j + 1)) *
          (((i : ℝ) + 1) * x ^ i - ((i : ℝ) + 2) * x ^ (i + 1))
        = (((j : ℝ) + 1) * ((i : ℝ) + 1)) * x ^ (i + j)
          + (-(((j : ℝ) + 1) * ((i : ℝ) + 2)) - ((j : ℝ) + 2) * ((i : ℝ) + 1)) * x ^ (i + j + 1)
          + (((j : ℝ) + 2) * ((i : ℝ) + 2)) * x ^ (i + j + 2) := fun x => by ring
    simp only [hexp]
    have hint : ∀ (c : ℝ) (n : ℕ), IntervalIntegrable (fun x : ℝ => c * x ^ n) volume 0 1 :=
      fun c n => (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add ((hint _ _).add (hint _ _)) (hint _ _),
      intervalIntegral.integral_add (hint _ _) (hint _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow_unit, integral_pow_unit,
      integral_pow_unit]
    have h1 : ((i : ℝ) + (j : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((i : ℝ) + (j : ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((i : ℝ) + (j : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_deriv_polyBasis_one j, coeFn_deriv_polyBasis_one i] with x hj hi
    rw [hj, hi]

/-- For $f \in L^2(0, 1)$ and $i \in \mathbb{N}$, the load vector entry of Example 9.1.1 is
$b_i = \int_0^1 f(x) x^{i+1} (1 - x) \, dx$. -/
theorem load_polyBasis (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (i : ℕ) :
    EllipticInterval.load 0 1 f (polyBasis i) = ∫ x in Ioo (0 : ℝ) 1, f x * polyBasisFun i x := by
  rw [EllipticInterval.load_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_deriv_polyBasis_zero i] with x hx
  rw [hx]

/-- **Example 9.1.1** of [han2009theoretical]. Consider $-u'' = f$ on $(0, 1)$ with
$u(0) = u(1) = 0$ and $f \in L^2(0, 1)$, posed weakly on $V = H_0^1(0, 1)$ with
$a(u, v) = \int_0^1 u' v' \, dx$ and $\ell(v) = \int_0^1 f v \, dx$. Let $N \in \mathbb{N}$, and
let $V_N$ be spanned by $\phi_i(x) = x^{i+1} (1 - x)$, $0 \le i \le N - 1$. Then:

* the weak problem has exactly one solution $u \in H_0^1(0, 1)$;
* the Galerkin problem on $V_N$ has exactly one solution $u_N$;
* for $0 \le i, j \le N - 1$ the stiffness matrix entries are $$A_{ij} =
  \frac{(i+1)(j+1)}{i+j+1} + \frac{(i+2)(j+2)}{i+j+3} - \frac{(i+1)(j+2) + (i+2)(j+1)}{i+j+2};$$
* the load vector entries are $b_i = \int_0^1 f(x) x^{i+1} (1 - x) \, dx$.

**Correction.** The source indexes the basis as $x^i (1 - x)$ for $i = 1, \dots, N$, with
$A_{ij} = \int_0^1 [x^j (1 - x)]' [x^i (1 - x)]' \, dx$, and prints the formula above for this
$A_{ij}$. With this indexing the formula is off by one: at $i = j = 1$ it gives $2/15$, while
the integral is $1/3$. The printed formula is the entry for the exponents $i + 1$ and $j + 1$.
With the basis indexed from $0$, as here, the formula of the source holds without change.

The weak problem and the Galerkin problem are stated with `IsGalerkinSolution` for
`AtkinsonHan.Chapter09.dirichletForm` and `EllipticInterval.load`, on `SobolevIntervalZero 0 1`
and on `AtkinsonHan.Chapter09.polySpace N`. The stiffness matrix is that of
`AtkinsonHan.BilinForm.ofCLM` of the form. -/
theorem example_9_1_1 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) :
    (∃! u, IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f)
        (SobolevIntervalZero 0 1) u) ∧
      (∃! uN, IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f) (polySpace N) uN) ∧
      (∀ i j : Fin N,
        stiffnessMatrix (BilinForm.ofCLM dirichletForm) (fun i : Fin N => polyBasis i) i j =
          ((i : ℝ) + 1) * ((j : ℝ) + 1) / ((i : ℝ) + (j : ℝ) + 1)
            + ((i : ℝ) + 2) * ((j : ℝ) + 2) / ((i : ℝ) + (j : ℝ) + 3)
            - (((i : ℝ) + 1) * ((j : ℝ) + 2) + ((i : ℝ) + 2) * ((j : ℝ) + 1))
                / ((i : ℝ) + (j : ℝ) + 2)) ∧
      (∀ i : Fin N, loadVector (EllipticInterval.load 0 1 f) (fun i : Fin N => polyBasis i) i
        = ∫ x in Ioo (0 : ℝ) 1, f x * polyBasisFun i x) := by
  refine ⟨existsUnique_dirichletGalerkin le_rfl f,
    existsUnique_dirichletGalerkin (polySpace_le N) f, fun i j => ?_, fun i => load_polyBasis f i⟩
  rw [stiffnessMatrix_apply, BilinForm.ofCLM_apply]
  exact dirichletForm_polyBasis i j

end

end Example911

/-!
### Example 9.1.2: the same problem with the basis $\sin(i \pi x)$

The trial space is $V_N = \operatorname{span}\{\sin(i \pi x) : 1 \le i \le N\}$. As in Example 9.1.1
the index starts at $0$ here, so `AtkinsonHan.Chapter09.sineBasis k` is $\sin((k+1) \pi x)$. The
basis is orthogonal for $a(u, v) = \int_0^1 u' v' \, dx$, the Galerkin system is diagonal, and the
Galerkin solution is the kernel approximation (9.1.10), whose kernel is the $N$-th partial sum of
the series of Exercise 9.1.3.
-/

section Example912

open MeasureTheory Set SobolevInterval
open scoped ContDiff

noncomputable section

/-- The basis function $x \mapsto \sin((k+1) \pi x)$ of Example 9.1.2. -/
def sineBasisFun (k : ℕ) : ℝ → ℝ := fun x => Real.sin (((k : ℝ) + 1) * π * x)

/-- The function $\sin((k+1) \pi x)$ is real analytic on $\mathbb{R}$. -/
theorem contDiff_sineBasisFun (k : ℕ) : ContDiff ℝ ω (sineBasisFun k) := by
  unfold sineBasisFun; fun_prop

/-- The function $\sin((k+1) \pi x)$ is continuously differentiable on $[0, 1]$. -/
theorem contDiffOn_sineBasisFun (k : ℕ) :
    ContDiffOn ℝ ((1 : ℕ) : ℕ∞ω) (sineBasisFun k) (Icc (0 : ℝ) 1) :=
  ((contDiff_sineBasisFun k).of_le le_top).contDiffOn

/-- The derivative of $\sin((k+1) \pi x)$ is $(k+1) \pi \cos((k+1) \pi x)$. -/
theorem deriv_sineBasisFun (k : ℕ) (x : ℝ) :
    _root_.deriv (sineBasisFun k) x
      = ((k : ℝ) + 1) * π * Real.cos (((k : ℝ) + 1) * π * x) := by
  unfold sineBasisFun
  have h1 : HasDerivAt (fun y : ℝ => ((k : ℝ) + 1) * π * y) (((k : ℝ) + 1) * π) x := by
    simpa using (hasDerivAt_id x).const_mul (((k : ℝ) + 1) * π)
  have h2 : HasDerivAt (fun y : ℝ => Real.sin (((k : ℝ) + 1) * π * y))
      (Real.cos (((k : ℝ) + 1) * π * x) * (((k : ℝ) + 1) * π)) x :=
    (Real.hasDerivAt_sin _).comp x h1
  rw [h2.deriv]
  ring

/-- The basis function $\sin((k+1) \pi x)$ as an element of $H^1(0, 1)$. -/
def sineBasis (k : ℕ) : SobolevInterval 1 0 1 :=
  ContDiffMapIcc.toSobolevInterval zero_le_one zero_lt_one 1
    (ContDiffMapIcc.ofContDiffOn zero_le_one zero_lt_one (contDiffOn_sineBasisFun k))

/-- The element `AtkinsonHan.Chapter09.sineBasis k` of $H^1(0, 1)$ agrees almost everywhere on
$(0, 1)$ with the function $\sin((k+1) \pi x)$. -/
theorem coeFn_deriv_sineBasis_zero (k : ℕ) :
    (SobolevInterval.deriv (sineBasis k) 0 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] sineBasisFun k := by
  refine (ContDiffMapIcc.coeFn_derivLp _ 0).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [IccExtend_of_mem zero_le_one _ (Ioo_subset_Icc_self hx)]
  rfl

/-- The weak derivative of `AtkinsonHan.Chapter09.sineBasis k` agrees almost everywhere on $(0, 1)$
with $(k+1) \pi \cos((k+1) \pi x)$. -/
theorem coeFn_deriv_sineBasis_one (k : ℕ) :
    (SobolevInterval.deriv (sineBasis k) 1 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => ((k : ℝ) + 1) * π * Real.cos (((k : ℝ) + 1) * π * x) := by
  refine (ContDiffMapIcc.coeFn_derivLp _ 1).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  rw [IccExtend_of_mem zero_le_one _ hx',
    ContDiffMapIcc.deriv_ofContDiffOn zero_le_one zero_lt_one (contDiffOn_sineBasisFun k) 1
      ⟨x, hx'⟩,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((contDiff_sineBasisFun k).contDiffAt.of_le le_top) hx']
  simpa using deriv_sineBasisFun k x

/-- The continuous representative of `AtkinsonHan.Chapter09.sineBasis k` is $\sin((k+1) \pi x)$ at
every $x \in [0, 1]$. -/
theorem rep_sineBasis (k : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    SobolevInterval.rep (sineBasis k) x = sineBasisFun k x :=
  rep_eq_of_continuousOn zero_lt_one _ (contDiff_sineBasisFun k).continuous.continuousOn
    (coeFn_deriv_sineBasis_zero k) hx

/-- The function $\sin((k+1) \pi x)$ lies in $H_0^1(0, 1)$. -/
theorem sineBasis_mem (k : ℕ) : sineBasis k ∈ SobolevIntervalZero 0 1 := by
  have hc : ContinuousOn (sineBasisFun k) (Icc (0 : ℝ) 1) :=
    (contDiff_sineBasisFun k).continuous.continuousOn
  rw [mem_sobolevIntervalZero_iff zero_lt_one]
  refine ⟨?_, ?_⟩ <;>
    rw [toContinuousMap_eq_of_continuousOn zero_lt_one _ hc (coeFn_deriv_sineBasis_zero k)]
  · simp [sineBasisFun]
  · have hone : ((k : ℝ) + 1) * π * 1 = ((k + 1 : ℕ) : ℝ) * π := by push_cast; ring
    simp only [sineBasisFun, hone, Real.sin_nat_mul_pi]

/-- The orthogonality relation of Example 9.1.2. For $i, j \in \mathbb{N}$, $$\int_0^1 [\sin((j+1)
\pi x)]' [\sin((i+1) \pi x)]' \, dx = \begin{cases} (i+1)(j+1) \pi^2 / 2 & \text{if } i = j, \\
0 & \text{otherwise.} \end{cases}$$
-/
theorem dirichletForm_sineBasis (i j : ℕ) :
    dirichletForm (sineBasis j) (sineBasis i)
      = if i = j then ((i : ℝ) + 1) * ((j : ℝ) + 1) * π ^ 2 / 2 else 0 := by
  rw [dirichletForm_apply,
    show (∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv (sineBasis j) 1 x *
          SobolevInterval.deriv (sineBasis i) 1 x)
        = ∫ x in Ioo (0 : ℝ) 1,
          (((j : ℝ) + 1) * π * Real.cos (((j : ℝ) + 1) * π * x)) *
            (((i : ℝ) + 1) * π * Real.cos (((i : ℝ) + 1) * π * x)) from ?_]
  · rw [← intervalIntegral.integral_eq_setIntegral_Ioo zero_le_one]
    have hre : ∀ x : ℝ,
        (((j : ℝ) + 1) * π * Real.cos (((j : ℝ) + 1) * π * x)) *
          (((i : ℝ) + 1) * π * Real.cos (((i : ℝ) + 1) * π * x))
        = (((j : ℝ) + 1) * π * (((i : ℝ) + 1) * π)) *
            (Real.cos (((j + 1 : ℕ) : ℝ) * π * x) * Real.cos (((i + 1 : ℕ) : ℝ) * π * x)) := by
      intro x
      push_cast
      ring
    simp only [hre]
    rw [intervalIntegral.integral_const_mul,
      integral_cos_mul_cos_unit (Nat.succ_pos j) (Nat.succ_pos i)]
    rcases eq_or_ne i j with rfl | hij
    · rw [ite_eq_left (rfl : i = i), ite_eq_left (rfl : i + 1 = i + 1)]
      ring
    · rw [ite_eq_right hij, ite_eq_right (by simpa using fun h => hij (by omega))]
      ring
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_deriv_sineBasis_one j, coeFn_deriv_sineBasis_one i] with x hj hi
    rw [hj, hi]

/-- The trial space of Example 9.1.2, $V_N = \operatorname{span}\{\sin(i \pi x) : 1 \le i \le N\}$,
as a subspace of $H^1(0, 1)$. -/
def sineSpace (N : ℕ) : Submodule ℝ (SobolevInterval 1 0 1) :=
  Submodule.span ℝ (Set.range fun i : Fin N => sineBasis i)

/-- The trial space $V_N$ of Example 9.1.2 is contained in $H_0^1(0, 1)$. -/
theorem sineSpace_le (N : ℕ) : sineSpace N ≤ SobolevIntervalZero 0 1 :=
  Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact sineBasis_mem i)

instance (N : ℕ) : FiniteDimensional ℝ (sineSpace N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- The Galerkin coefficient of Example 9.1.2, $\xi_i = \frac{2}{\pi^2 i^2} \int_0^1 f(x) \sin(i \pi
x) \, dx$, here for $i = k + 1$. -/
def sineCoeff (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (k : ℕ) : ℝ :=
  2 / (π ^ 2 * ((k : ℝ) + 1) ^ 2) * ∫ x in Ioo (0 : ℝ) 1, f x * sineBasisFun k x

/-- The Galerkin solution of Example 9.1.2, $u_N = \sum_{j=1}^N \xi_j \sin(j \pi x)$ with the
coefficients `AtkinsonHan.Chapter09.sineCoeff`. -/
def sineGalerkin (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) : SobolevInterval 1 0 1 :=
  ∑ j : Fin N, sineCoeff f j • sineBasis j

/-- For $f \in L^2(0, 1)$ and $i \in \mathbb{N}$, the load vector entry of Example 9.1.2 is
$\int_0^1 f(x) \sin((i+1) \pi x) \, dx$. -/
theorem load_sineBasis (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (i : ℕ) :
    EllipticInterval.load 0 1 f (sineBasis i) = ∫ x in Ioo (0 : ℝ) 1, f x * sineBasisFun i x := by
  rw [EllipticInterval.load_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_deriv_sineBasis_zero i] with x hx
  rw [hx]

/-- For $f \in L^2(0, 1)$, the function $u_N = \sum_{j=1}^N \xi_j \sin(j \pi x)$ with $\xi_i =
\frac{2}{\pi^2 i^2} \int_0^1 f(x) \sin(i \pi x) \, dx$ solves the Galerkin problem of Example
9.1.2 on $V_N$. -/
theorem isGalerkinSolution_sineGalerkin (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) :
    IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f) (sineSpace N)
      (sineGalerkin f N) := by
  classical
  refine ⟨Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩), ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hsum : dirichletForm (sineGalerkin f N) (sineBasis i)
          = ∑ j : Fin N, sineCoeff f j * dirichletForm (sineBasis j) (sineBasis i) := by
        rw [sineGalerkin, map_sum]
        simp only [FunLike.coe_sum, Finset.sum_apply, map_smul, FunLike.coe_smul, Pi.smul_apply,
          smul_eq_mul]
      rw [hsum]
      simp only [dirichletForm_sineBasis, mul_ite, mul_zero]
      have hfin : ∀ j : Fin N, ((i : ℕ) = (j : ℕ)) = (i = j) := fun j => by simp [Fin.val_inj]
      simp only [hfin]
      rw [Finset.sum_ite_eq Finset.univ i
        (fun j : Fin N => sineCoeff f j * (((i : ℝ) + 1) * ((j : ℝ) + 1) * π ^ 2 / 2)),
        ite_eq_left (Finset.mem_univ i), load_sineBasis, sineCoeff]
      have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      have hik : ((i : ℝ) + 1) ≠ 0 := by positivity
      field_simp
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy]
  | smul c x _ ih => rw [map_smul, map_smul, ih]

/-- The kernel form (9.1.10) of the Galerkin solution of Example 9.1.2. For $f \in L^2(0, 1)$ and
$x \in [0, 1]$, the continuous representative of $u_N$ satisfies $$u_N(x) = \int_0^1 f(t) K_N(x,
t) \, dt, \qquad K_N(x, t) = \frac{2}{\pi^2} \sum_{j=1}^N \frac{\sin(j \pi x) \sin(j \pi
t)}{j^2}.$$

The kernel $K_N$ is the $N$-th partial sum of the expansion of the Green kernel in
`AtkinsonHan.Chapter09.exercise_9_1_3`. -/
theorem rep_sineGalerkin (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    SobolevInterval.rep (sineGalerkin f N) x
      = ∫ t in Ioo (0 : ℝ) 1, f t * (2 / π ^ 2 *
          ∑ j : Fin N, sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2) := by
  have hintg : ∀ j : Fin N, IntegrableOn
      (fun t => f t * (2 / π ^ 2 * (sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2)))
      (Ioo (0 : ℝ) 1) := by
    intro j
    have hg : ContinuousOn
        (fun t => 2 / π ^ 2 * (sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2))
        (Icc (0 : ℝ) 1) := by
      have hcont : Continuous (sineBasisFun (j : ℕ)) := (contDiff_sineBasisFun j).continuous
      fun_prop
    exact (MeasureTheory.integrableOn_continuousOn_mul hg f).congr_fun
      (fun t _ => mul_comm _ _) measurableSet_Ioo
  rw [sineGalerkin, rep_finset_sum zero_lt_one _ _ _ hx]
  have hterm : ∀ j : Fin N, sineCoeff f j * SobolevInterval.rep (sineBasis j) x
      = ∫ t in Ioo (0 : ℝ) 1,
        f t * (2 / π ^ 2 * (sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2)) := by
    intro j
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hjk : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hre : ∀ t : ℝ,
        (f : ℝ → ℝ) t * (2 / π ^ 2 * (sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2))
        = (2 / (π ^ 2 * ((j : ℝ) + 1) ^ 2) * sineBasisFun j x) *
            ((f : ℝ → ℝ) t * sineBasisFun j t) := by
      intro t
      field_simp
    rw [rep_sineBasis j hx, sineCoeff]
    simp only [hre]
    rw [integral_const_mul]
    ring
  simp only [hterm]
  rw [← integral_finsetSum _ fun j _ => hintg j]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [Finset.mul_sum, Finset.mul_sum]

/-- **Example 9.1.2** of [han2009theoretical]. Consider the boundary value problem (9.1.9),
$-u'' = f$ on $(0, 1)$ with $u(0) = u(1) = 0$ and $f \in L^2(0, 1)$, with the trial space $V_N =
\operatorname{span}\{\sin(i \pi x) : 1 \le i \le N\}$. Then:

* the basis is orthogonal for the energy inner product, $\int_0^1 [\sin(j \pi x)]' [\sin(i \pi
  x)]' \, dx = i j \pi^2 \delta_{ij} / 2$ for all $i, j \ge 1$, so the Galerkin system is
  diagonal;
* an element $u_N$ solves the Galerkin problem on $V_N$ if and only if
  $u_N = \sum_{j=1}^N \xi_j \sin(j \pi x)$ with $\xi_i = \frac{2}{\pi^2 i^2} \int_0^1 f(x)
  \sin(i \pi x) \, dx$;
* for $x \in [0, 1]$, $u_N(x) = \int_0^1 f(t) K_N(x, t) \, dt$ with $K_N(x, t) = \frac{2}{\pi^2}
  \sum_{j=1}^N \sin(j \pi x) \sin(j \pi t) / j^2$, which is the kernel approximation (9.1.10).

The indices are shifted to start at $0$: `AtkinsonHan.Chapter09.sineBasis k` is
$\sin((k+1) \pi x)$. The value $u_N(x)$ is that of the continuous representative
`SobolevIntervalLp.rep`. The kernel $K_N$ is the $N$-th partial sum of the expansion of
`AtkinsonHan.Chapter09.exercise_9_1_3`. -/
theorem example_9_1_2 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) :
    (∀ i j : ℕ, dirichletForm (sineBasis j) (sineBasis i)
        = if i = j then ((i : ℝ) + 1) * ((j : ℝ) + 1) * π ^ 2 / 2 else 0) ∧
      (∀ uN, IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f) (sineSpace N) uN ↔
        uN = ∑ j : Fin N, (2 / (π ^ 2 * ((j : ℝ) + 1) ^ 2) *
          ∫ x in Ioo (0 : ℝ) 1, f x * sineBasisFun j x) • sineBasis j) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, SobolevInterval.rep (sineGalerkin f N) x
        = ∫ t in Ioo (0 : ℝ) 1, f t * (2 / π ^ 2 *
            ∑ j : Fin N, sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2)) := by
  refine ⟨dirichletForm_sineBasis, fun uN => ⟨fun h => ?_, fun h => ?_⟩,
    fun x hx => rep_sineGalerkin f N hx⟩
  · obtain ⟨w, -, huniq⟩ := existsUnique_dirichletGalerkin (sineSpace_le N) f
    exact (huniq uN h).trans (huniq _ (isGalerkinSolution_sineGalerkin f N)).symm
  · rw [h]
    exact isGalerkinSolution_sineGalerkin f N

end

end Example912

end Chapter09

end AtkinsonHan
