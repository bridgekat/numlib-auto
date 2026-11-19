/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.ODE.LinearSystem
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 11.9: Systems of ODEs

This module formalizes Section 11.9 of [quarteroni2000numerical], on the Cauchy problem for a system
$y' = F(t, y)$, $y(t_0) = y_0$ in $\mathbb{R}^n$ (11.78)–(11.79). Property 11.5 gives global
existence and uniqueness when $F$ is continuous and Lipschitz in $y$ (11.80). For the linear system
$y' = Ay$ (11.81) with a diagonalizable matrix $A \in \mathbb{R}^{n \times n}$, the solutions are
$y(t) = \sum_j C_j e^{\lambda_j t} v_j$ (11.82), they decay to $0$ when every eigenvalue has
negative real part (11.83)–(11.84), and the change of variables $z = Q^{-1} y$ turns the system into
the diagonal system $z' = \Lambda z$ (11.85).

The vector Cauchy problem is `ODE.IsSolutionOn` on `EuclideanSpace ℝ (Fin n)`, and Property 11.5
specializes `ODE.existsUnique_isSolutionOn_of_lipschitz` from `Numlib.Analysis.ODE.Cauchy`. The
linear system specializes `Numlib.Analysis.ODE.LinearSystem`.

## Main definitions

* Equations (11.78)–(11.79), `QuarteroniSaccoSaleri.Chapter11.equation_11_78`: $y$ solves the vector
  Cauchy problem on an interval.

## Main results

* Property 11.5, `QuarteroniSaccoSaleri.Chapter11.property_11_5`: existence and uniqueness of the
  solution for a continuous field that is Lipschitz in $y$.
* Equation (11.82), `QuarteroniSaccoSaleri.Chapter11.equation_11_82`: every solution of $y' = Ay$ is
  $\sum_j C_j e^{\lambda_j t} v_j$.
* Equations (11.83)–(11.84), `QuarteroniSaccoSaleri.Chapter11.equation_11_83`: the solutions tend to
  $0$ when every eigenvalue has negative real part.
* Equation (11.85), `QuarteroniSaccoSaleri.Chapter11.equation_11_85`: $z = Q^{-1} y$ solves
  $z' = \Lambda z$.

## Implementation notes

* The linear system is read on `Fin n → ℝ`, where a matrix acts by `Matrix.mulVec`. The results on
  it pass to the complexified matrix `A.map ((↑) : ℝ → ℂ)` on `Fin n → ℂ`, which is the setting of
  `Numlib.Analysis.ODE.LinearSystem`; `QuarteroniSaccoSaleri.Chapter11.linearSystem_complexify`
  makes this step.
* The diagonalization is $A = Q \Lambda Q^{-1}$ over $\mathbb{C}$, with $\Lambda =
  \operatorname{diag}(\lambda_1, \dots, \lambda_n)$ and the columns $v_j$ of $Q$ the eigenvectors.
  The eigenvalues are `μ : Fin n → ℂ` in Lean.

## Deviations from the source

* **Equations (11.78)–(11.79) and Property 11.5** (reading). The solution predicate uses within-
  set derivatives. The existence theorem works on a closed time interval and fixes a common
  constant extension off the interval for uniqueness as total functions.
* **Equations (11.82)–(11.84)** (reading). `equation_11_82` computes the expansion coefficients
  from time zero. `equation_11_83` gives decay directly from negative real parts. The printed
  trigonometric expansion in (11.84) omits the time factor in the imaginary arguments, which
  does not affect the stated decay conclusion.
* **Equations (11.82)–(11.85)** (generalization). The source assumes that $A$ has $n$ distinct
  eigenvalues; the results assume only that $A$ is diagonalizable over $\mathbb{C}$. See
  `QuarteroniSaccoSaleri.Chapter11.equation_11_82`.
-/

open Set Filter Topology Matrix

namespace QuarteroniSaccoSaleri.Chapter11

variable {n : ℕ}

/-- **Equations (11.78)–(11.79)** of [quarteroni2000numerical]. Let $F : \mathbb{R} \times
\mathbb{R}^n \to \mathbb{R}^n$, $t_0 \in \mathbb{R}$, $y_0 \in \mathbb{R}^n$ and
$I \subseteq \mathbb{R}$. A function $y : \mathbb{R} \to \mathbb{R}^n$ **solves the vector
Cauchy problem** on $I$ if $y(t_0) = y_0$ and $y'(t) = F(t, y(t))$ for every $t \in I$, the
derivative taken within $I$.

The definition is `ODE.IsSolutionOn` on `EuclideanSpace ℝ (Fin n)`.

**Generalization.** Uses within-set derivatives on arbitrary time sets, with the initial value
condition separate. -/
def equation_11_78 (F : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (t₀ : ℝ)
    (y₀ : EuclideanSpace ℝ (Fin n)) (I : Set ℝ) (y : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ODE.IsSolutionOn F t₀ y₀ I y

/-- **Property 11.5** of [quarteroni2000numerical]. Let $t_0 \le T$ and $L \ge 0$, and let $F :
\mathbb{R} \times \mathbb{R}^n \to \mathbb{R}^n$ be continuous on
$D = [t_0, T] \times \mathbb{R}^n$ with
$$\|F(t, y) - F(t, \bar{y})\| \le L \|y - \bar{y}\| \qquad \text{for all } t \in [t_0, T] \text{
  and } y, \bar{y} \in \mathbb{R}^n \quad (11.80).$$
Then for every $y_0 \in \mathbb{R}^n$ there is exactly one function
$y : \mathbb{R} \to \mathbb{R}^n$ that solves the Cauchy problem (11.78)–(11.79) on $[t_0, T]$
and satisfies $y(t) = y_0$ for $t \notin [t_0, T]$.

The values off $[t_0, T]$ are fixed so that uniqueness of a function on $\mathbb{R}$ makes
sense. The norm is the Euclidean norm. The proof specializes
`ODE.existsUnique_isSolutionOn_of_lipschitz`.

**Reading.** Allows $L=0$, explicitly orders the interval endpoints, and assigns the same
constant value outside the interval to obtain uniqueness of total functions. -/
theorem property_11_5 {F : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {t₀ T L : ℝ}
    (hT : t₀ ≤ T) (hL : 0 ≤ L) (hF : ContinuousOn (Function.uncurry F) (Icc t₀ T ×ˢ univ))
    (hlip : ∀ t ∈ Icc t₀ T, ∀ y w : EuclideanSpace ℝ (Fin n), ‖F t y - F t w‖ ≤ L * ‖y - w‖)
    (y₀ : EuclideanSpace ℝ (Fin n)) :
    ∃! y : ℝ → EuclideanSpace ℝ (Fin n), equation_11_78 F t₀ y₀ (Icc t₀ T) y ∧
      ∀ t ∉ Icc t₀ T, y t = y₀ := by
  have e : Icc t₀ T = Icc t₀ (t₀ + (T - t₀)) := by rw [add_sub_cancel]
  simp only [equation_11_78, e]
  rw [e] at hF hlip
  exact ODE.existsUnique_isSolutionOn_of_lipschitz (K := ⟨L, hL⟩) (by linarith) hF
    (fun t ht => LipschitzWith.of_dist_le_mul fun v₁ v₂ => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip t ht v₁ v₂) y₀

/-! ### The linear system $y' = Ay$ -/

variable {A : Matrix (Fin n) (Fin n) ℝ} {y₀ : Fin n → ℝ} {y : ℝ → Fin n → ℝ}

/-- A real solution of the linear system (11.81) is a complex solution of the complexified system.
Let $A \in \mathbb{R}^{n \times n}$, $I \subseteq \mathbb{R}$, and let $y$ solve $y' = Ay$,
$y(t_0) = y_0$ on $I$. Then $t \mapsto y(t)$, read in $\mathbb{C}^n$ componentwise, solves
$z' = Az$, $z(t_0) = y_0$ on $I$, where $A$ acts on $\mathbb{C}^n$. -/
theorem linearSystem_complexify {t₀ : ℝ} {I : Set ℝ}
    (hy : ODE.IsSolutionOn (fun _ v => A *ᵥ v) t₀ y₀ I y) :
    ODE.IsSolutionOn (fun _ v => A.map ((↑) : ℝ → ℂ) *ᵥ v) t₀ (fun i => (y₀ i : ℂ)) I
      fun t i => (y t i : ℂ) := by
  refine ⟨by simp [hy.1], fun t ht => ?_⟩
  rw [hasDerivWithinAt_pi]
  intro i
  have := (hasDerivWithinAt_pi.1 (hy.2 t ht) i).ofReal_comp
  refine this.congr_deriv ?_
  change ((A *ᵥ y t) i : ℂ) = (A.map ((↑) : ℝ → ℂ) *ᵥ fun i => (y t i : ℂ)) i
  exact RingHom.map_mulVec Complex.ofRealHom A (y t) i

/-- **Equation (11.82)** of [quarteroni2000numerical], the solutions of $y' = Ay$ (11.81). Let
$A \in \mathbb{R}^{n \times n}$, and let $Q \in \mathbb{C}^{n \times n}$ be invertible with
$A = Q \Lambda Q^{-1}$ over $\mathbb{C}$, where $\Lambda = \operatorname{diag}(\lambda_1, \dots,
\lambda_n)$. Let $T \in \mathbb{R}$, and let $y$ solve $y' = Ay$, $y(0) = y_0$ on $[0, T]$. Then
for every $t \in [0, T]$
$$y(t) = \sum_{j=1}^n C_j e^{\lambda_j t} v_j, \qquad C = Q^{-1} y_0,$$
where $v_j$ is the $j$-th column of $Q$, and the identity holds in $\mathbb{C}^n$.

**Generalization.** The source assumes that $A$ has $n$ distinct eigenvalues $\lambda_j$ with
eigenvectors $v_j$. The statement assumes only the diagonalization $A = Q \Lambda Q^{-1}$, which
is how the assumption is used.

The proof specializes `ODE.linear_solution_eq_sum_exp_smul`.

**Generalization.** A complex diagonalization suffices even when eigenvalues repeat. The
solution is initialized at time zero and its coefficients are the coordinates of the initial
vector in the eigenbasis. -/
theorem equation_11_82 {Q : Matrix (Fin n) (Fin n) ℂ} {μ : Fin n → ℂ}
    (hA : A.map ((↑) : ℝ → ℂ) = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q) {T : ℝ}
    (hy : ODE.IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Icc 0 T) y) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun i => (y t i : ℂ)) =
      ∑ j, ((Q⁻¹ *ᵥ fun i => (y₀ i : ℂ)) j * Complex.exp (μ j * t)) • fun i => Q i j :=
  ODE.linear_solution_eq_sum_exp_smul hA hQ (linearSystem_complexify hy) ht

/-- **Equations (11.83)–(11.84)** of [quarteroni2000numerical], decay of the solutions. Let
$A \in \mathbb{R}^{n \times n}$, and let $Q \in \mathbb{C}^{n \times n}$ be invertible with
$A = Q \Lambda Q^{-1}$ over $\mathbb{C}$, where $\Lambda = \operatorname{diag}(\lambda_1, \dots,
\lambda_n)$ and $\operatorname{Re} \lambda_j < 0$ for every $j$. If $y$ solves $y' = Ay$,
$y(0) = y_0$ on $[0, \infty)$, then $\|y(t)\| \to 0$ as $t \to \infty$.

**Generalization.** The source assumes that $A$ has $n$ distinct eigenvalues. The statement
assumes only that $A$ is diagonalizable over $\mathbb{C}$.

The decay comes from $e^{\lambda_j t} = e^{\operatorname{Re}(\lambda_j) t}
(\cos(\operatorname{Im}(\lambda_j) t) + i \sin(\operatorname{Im}(\lambda_j) t)) \to 0$. The norm
is the supremum norm of `Fin n → ℝ`. The proof specializes
`ODE.linear_tendsto_zero_of_re_lt_zero`.

**Reading.** Decay uses a complex diagonalization and negative real parts. The printed equality
(11.84) omits $t$ in the sine and cosine arguments. The theorem states the resulting norm
limit. -/
theorem equation_11_83 {Q : Matrix (Fin n) (Fin n) ℂ} {μ : Fin n → ℂ}
    (hA : A.map ((↑) : ℝ → ℂ) = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q) (hμ : ∀ j, (μ j).re < 0)
    (hy : ODE.IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Ici 0) y) :
    Tendsto (fun t => ‖y t‖) atTop (𝓝 0) := by
  have := ODE.linear_tendsto_zero_of_re_lt_zero hA hQ hμ (linearSystem_complexify hy)
  refine this.congr fun t => ?_
  simp only [Pi.norm_def, Complex.nnnorm_real]

/-- **Equation (11.85)** of [quarteroni2000numerical], the diagonalized system. Let
$A \in \mathbb{R}^{n \times n}$, and let $Q \in \mathbb{C}^{n \times n}$ be invertible with
$A = Q \Lambda Q^{-1}$ over $\mathbb{C}$, where $\Lambda = \operatorname{diag}(\lambda_1, \dots,
\lambda_n)$. Let $I \subseteq \mathbb{R}$, and let $y$ solve $y' = Ay$, $y(t_0) = y_0$ on $I$.
Then $z = Q^{-1} y$ solves $z' = \Lambda z$, $z(t_0) = Q^{-1} y_0$ on $I$, and each component
solves the scalar test equation $z_j' = \lambda_j z_j$, $z_j(t_0) = (Q^{-1} y_0)_j$ on $I$.

**Generalization.** The source assumes that $A$ has $n$ distinct eigenvalues. The statement
assumes only that $A$ is diagonalizable over $\mathbb{C}$.

The proof specializes `ODE.linear_diagonalized_isSolutionOn` and
`ODE.isSolutionOn_diagonal_iff`.

**Generalization.** A complex diagonalization suffices, and the change of coordinates applies
to arbitrary time sets and initial times. -/
theorem equation_11_85 {Q : Matrix (Fin n) (Fin n) ℂ} {μ : Fin n → ℂ}
    (hA : A.map ((↑) : ℝ → ℂ) = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q) {t₀ : ℝ} {I : Set ℝ}
    (hy : ODE.IsSolutionOn (fun _ v => A *ᵥ v) t₀ y₀ I y) :
    ODE.IsSolutionOn (fun _ v => diagonal μ *ᵥ v) t₀ (Q⁻¹ *ᵥ fun i => (y₀ i : ℂ)) I
        (fun t => Q⁻¹ *ᵥ fun i => (y t i : ℂ)) ∧
      ∀ j, ODE.IsSolutionOn (fun _ w => μ j * w) t₀ ((Q⁻¹ *ᵥ fun i => (y₀ i : ℂ)) j) I
        fun t => (Q⁻¹ *ᵥ fun i => (y t i : ℂ)) j := by
  have h := ODE.linear_diagonalized_isSolutionOn hA hQ (linearSystem_complexify hy)
  exact ⟨h, ODE.isSolutionOn_diagonal_iff.1 h⟩

end QuarteroniSaccoSaleri.Chapter11
