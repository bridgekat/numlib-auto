/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Numlib.Analysis.ODE.Cauchy

/-!
# Linear systems with constant coefficients

This file studies the system $y' = Ay$ for a constant matrix $A \in \mathbb{C}^{n \times n}$, as in
the discussion of absolute stability and stiffness in §11.9–11.10 of [quarteroni2000numerical]. The
solution with $y(0) = y_0$ is $y(t) = e^{tA} y_0$, and it is unique. When $A = Q \Lambda Q^{-1}$ is
diagonalizable, with $\Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$ and the columns
$v_j$ of $Q$ an eigenvector basis, every solution has the expansion
$$y(t) = \sum_j C_j e^{\lambda_j t} v_j, \qquad C = Q^{-1} y_0,$$
which is (11.82) of the book. If every eigenvalue has negative real part, then $\|y(t)\| \to 0$ as
$t \to \infty$ ((11.83)–(11.84)). The change of variables $z = Q^{-1} y$ gives $z' = \Lambda z$
((11.85)), that is, $n$ scalar test equations $z_j' = \lambda_j z_j$. The file ends with the
stiffness quotient $r_s = \sigma / \tau$ of (11.86), with
$\sigma = \min_j \operatorname{Re} \lambda_j$ and $\tau = \max_j \operatorname{Re} \lambda_j$.

## Main definitions

* `ODE.stiffnessQuotient`: the stiffness quotient $\sigma / \tau$ of a matrix.

## Main results

* `ODE.linear_isSolutionOn_exp_smul`: $t \mapsto e^{tA} y_0$ solves $y' = Ay$, $y(0) = y_0$.
* `ODE.linear_isSolutionOn_unique`: every solution on $[0, T]$ is $t \mapsto e^{tA} y_0$.
* `ODE.linear_solution_eq_sum_exp_smul`: the expansion $y(t) = \sum_j C_j e^{\lambda_j t} v_j$ of a
  solution of a diagonalizable system.
* `ODE.linear_tendsto_zero_of_re_lt_zero`: the solutions of a diagonalizable system whose
  eigenvalues have negative real parts tend to zero.
* `ODE.linear_diagonalized_isSolutionOn`: if $y$ solves $y' = Ay$, then $z = Q^{-1} y$ solves
  $z' = \Lambda z$.
* `ODE.isSolutionOn_diagonal_iff`: a diagonal system is equivalent to $n$ scalar test equations.
* `ODE.one_le_stiffnessQuotient`: if the spectrum is nonempty and all eigenvalues have negative real
  part, the stiffness quotient is at least $1$.

## Implementation notes

* The matrix exponential is Mathlib's `NormedSpace.exp` on `Matrix n n ℂ`, with `Matrix.exp_conj`
  and `Matrix.exp_diagonal`. The derivative comes from `hasDerivAt_exp_smul_const'`, and the
  solution is one composition with the linear map $M \mapsto M y_0$. Uniqueness is
  `ODE.isSolutionOn_unique_of_lipschitz` for the Lipschitz field $v \mapsto Av$.
* Everything is over $\mathbb{C}$ on `n → ℂ`, because the eigenvalues of a real matrix are complex.
  A real system is read through the complexified matrix `A.map ofReal`.
* Diagonalizability is the hypothesis `A = Q * diagonal μ * Q⁻¹` with `IsUnit Q`: the columns of $Q$
  are the eigenvectors $v_j$, and $\mu_j = \lambda_j$ are the eigenvalues. The book assumes instead
  that $A$ has $n$ distinct eigenvalues, which implies this hypothesis, and uses only this
  hypothesis.
* For $t \in \mathbb{R}$, `t • A` is the real multiple of the complex matrix, `(t : ℂ) • A`. The
  book's $e^{\lambda_j t}$ is `Complex.exp (μ j * t)`. Time starts at $t_0 = 0$, and the initial
  value is $y_0$.
* The stiffness quotient is a definition on the spectrum. The book's statement that the system is
  stiff when $r_s \gg 1$, and its Definition 11.14, are informal and are not formalized.
-/

open Set Filter Topology Matrix NormedSpace

namespace ODE

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Derivatives of matrix-vector products -/

omit [DecidableEq n] in
/-- Let $M \in \mathbb{C}^{m \times n}$, and let $y : \mathbb{R} \to \mathbb{C}^n$ have the
derivative $y'$ within $I \subseteq \mathbb{R}$ at $t$. Then $t \mapsto M y(t)$ has the
derivative $M y'$ within $I$ at $t$, because $v \mapsto Mv$ is linear. -/
theorem hasDerivWithinAt_mulVec {m : Type*} [Finite m] (M : Matrix m n ℂ) {y : ℝ → n → ℂ}
    {y' : n → ℂ} {I : Set ℝ} {t : ℝ} (hy : HasDerivWithinAt y y' I t) :
    HasDerivWithinAt (fun t => M *ᵥ y t) (M *ᵥ y') I t := by
  cases nonempty_fintype m
  exact ((LinearMap.toContinuousLinearMap
    M.mulVecLin).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hy

/-- The map $M \mapsto Mv$ from $\mathbb{C}^{n \times n}$ to $\mathbb{C}^n$, for a fixed
$v \in \mathbb{C}^n$, as a continuous real-linear map. -/
noncomputable def mulVecRightCLM (v : n → ℂ) : Matrix n n ℂ →L[ℝ] (n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => Matrix.smul_mulVec c M v }

omit [DecidableEq n] in
/-- The map `ODE.mulVecRightCLM v` sends $M$ to $Mv$. -/
@[simp] theorem mulVecRightCLM_apply (v : n → ℂ) (M : Matrix n n ℂ) :
    mulVecRightCLM v M = M *ᵥ v :=
  rfl

/-- For $A \in \mathbb{C}^{n \times n}$, $y_0 \in \mathbb{C}^n$ and $t \in \mathbb{R}$, the function
$t \mapsto e^{tA} y_0$ has the derivative $A (e^{tA} y_0)$ at $t$.

The proof uses `hasDerivAt_exp_smul_const'` in the normed algebra `Matrix n n ℂ` with the
$L^\infty$ operator norm. -/
theorem hasDerivAt_exp_smul_mulVec (A : Matrix n n ℂ) (y₀ : n → ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => exp (t • A) *ᵥ y₀) (A *ᵥ (exp (t • A) *ᵥ y₀)) t := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have h := (mulVecRightCLM y₀).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' A t)
  exact h.congr_deriv (by simp only [Matrix.mulVec_mulVec]; rfl)

/-! ### The exponential solution -/

/-- **The exponential solution.** For $A \in \mathbb{C}^{n \times n}$ and $y_0 \in \mathbb{C}^n$,
the function $t \mapsto e^{tA} y_0$ solves the Cauchy problem $y' = Ay$, $y(0) = y_0$ at every
time $t \in \mathbb{R}$ (§11.9 of [quarteroni2000numerical]).

The solution concept is `ODE.IsSolutionOn` with the field `fun _ v => A *ᵥ v` and the set of
times `univ`. -/
theorem linear_isSolutionOn_exp_smul (A : Matrix n n ℂ) (y₀ : n → ℂ) :
    IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ univ fun t : ℝ => exp (t • A) *ᵥ y₀ :=
  ⟨by simp, fun t _ => (hasDerivAt_exp_smul_mulVec A y₀ t).hasDerivWithinAt⟩

omit [DecidableEq n] in
/-- The linear field $v \mapsto Av$ on $\mathbb{C}^n$ is Lipschitz with some constant $L \ge 0$. -/
theorem exists_lipschitzWith_mulVec (A : Matrix n n ℂ) :
    ∃ L : NNReal, LipschitzWith L fun v : n → ℂ => A *ᵥ v :=
  ⟨_, (LinearMap.toContinuousLinearMap A.mulVecLin).lipschitzWith⟩

/-- **Uniqueness.** Let $A \in \mathbb{C}^{n \times n}$, $y_0 \in \mathbb{C}^n$ and
$T \in \mathbb{R}$. Every solution $y$ of $y' = Ay$, $y(0) = y_0$ on $[0, T]$ satisfies
$y(t) = e^{tA} y_0$ for all $t \in [0, T]$. -/
theorem linear_isSolutionOn_unique {A : Matrix n n ℂ} {y₀ : n → ℂ} {T : ℝ} {y : ℝ → n → ℂ}
    (hy : IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Icc 0 T) y) :
    EqOn y (fun t : ℝ => exp (t • A) *ᵥ y₀) (Icc 0 T) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_mulVec A
  have h := (linear_isSolutionOn_exp_smul A y₀).mono (subset_univ (Icc 0 T))
  have := isSolutionOn_unique_of_lipschitz (t₀ := 0) (T := T) (fun _ _ => hL) (by simpa using hy)
    (by simpa using h)
  simpa using this

/-! ### Diagonalizable systems -/

variable {A Q : Matrix n n ℂ} {μ : n → ℂ}

/-- Let $A = Q \Lambda Q^{-1}$ with $\Lambda = \operatorname{diag}(\mu)$ and
$Q \in \mathbb{C}^{n \times n}$ invertible. Then for every $t \in \mathbb{R}$,
$$e^{tA} = Q \operatorname{diag}(e^{\mu_1 t}, \dots, e^{\mu_n t}) Q^{-1}.$$
-/
theorem exp_smul_eq_of_eq_mul_diagonal (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q) (t : ℝ) :
    exp (t • A) = Q * diagonal (fun j => Complex.exp (μ j * t)) * Q⁻¹ := by
  have e : t • A = Q * diagonal (fun j => μ j * t) * Q⁻¹ := by
    rw [hA, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    ext j
    simp [mul_comm]
  rw [e, Matrix.exp_conj _ _ hQ, Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]

omit [DecidableEq n] in
/-- For $Q \in \mathbb{C}^{n \times n}$ and $w \in \mathbb{C}^n$, the product $Qw$ is the
combination $\sum_j w_j q_j$ of the columns $q_j$ of $Q$. -/
theorem mulVec_eq_sum_smul_col (Q : Matrix n n ℂ) (w : n → ℂ) :
    Q *ᵥ w = ∑ j, w j • fun i => Q i j := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- **The eigenvector expansion of the solution.** Let $A = Q \Lambda Q^{-1}$ with
$\Lambda = \operatorname{diag}(\mu)$ and $Q \in \mathbb{C}^{n \times n}$ invertible, so that the
columns $v_j$ of $Q$ are an eigenvector basis and $\mu_j = \lambda_j$ are the eigenvalues. Let
$y$ solve $y' = Ay$, $y(0) = y_0$ on $[0, T]$. Then for every $t \in [0, T]$,
$$y(t) = \sum_j C_j e^{\lambda_j t} v_j, \qquad C = Q^{-1} y_0.$$
This is (11.82) of [quarteroni2000numerical]. -/
theorem linear_solution_eq_sum_exp_smul (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q)
    {y₀ : n → ℂ} {T : ℝ} {y : ℝ → n → ℂ} (hy : IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Icc 0 T) y)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    y t = ∑ j, ((Q⁻¹ *ᵥ y₀) j * Complex.exp (μ j * t)) • fun i => Q i j := by
  rw [show y t = exp (t • A) *ᵥ y₀ from linear_isSolutionOn_unique hy ht,
    exp_smul_eq_of_eq_mul_diagonal hA hQ, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_eq_sum_smul_col]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_diagonal, mul_comm]

/-- **Decay of the solutions.** Let $A = Q \Lambda Q^{-1}$ with $\Lambda = \operatorname{diag}(\mu)$
and $Q \in \mathbb{C}^{n \times n}$ invertible, and assume $\operatorname{Re} \mu_j < 0$ for
every $j$. If $y$ solves $y' = Ay$, $y(0) = y_0$ on $[0, \infty)$, then $\|y(t)\| \to 0$ as
$t \to \infty$. This is (11.83)–(11.84) of [quarteroni2000numerical].

The reason is that $e^{\lambda_j t} = e^{\operatorname{Re} \lambda_j t} (\cos(\operatorname{Im}
\lambda_j t) + i \sin(\operatorname{Im} \lambda_j t))$ has the norm
$e^{\operatorname{Re} \lambda_j t} \to 0$. -/
theorem linear_tendsto_zero_of_re_lt_zero (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q)
    (hμ : ∀ j, (μ j).re < 0) {y₀ : n → ℂ} {y : ℝ → n → ℂ}
    (hy : IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Ici 0) y) :
    Tendsto (fun t => ‖y t‖) atTop (𝓝 0) := by
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have hterm : ∀ j, Tendsto (fun t : ℝ => ((Q⁻¹ *ᵥ y₀) j * Complex.exp (μ j * t)) • fun i => Q i j)
      atTop (𝓝 0) := by
    intro j
    have h1 : Tendsto (fun t : ℝ => Complex.exp (μ j * t)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (hμ j))
    simpa using (h1.const_mul ((Q⁻¹ *ᵥ y₀) j)).smul_const (fun i => Q i j)
  have hsum := tendsto_finsetSum Finset.univ fun j _ => hterm j
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (linear_solution_eq_sum_exp_smul hA hQ (hy.mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0))
    (right_mem_Icc.2 ht)).symm

/-- **The diagonalizing change of variables.** Let $A = Q \Lambda Q^{-1}$ with
$\Lambda = \operatorname{diag}(\mu)$ and $Q \in \mathbb{C}^{n \times n}$ invertible. If $y$
solves $y' = Ay$, $y(t_0) = y_0$ on a set of times $I$, then $z = Q^{-1} y$ solves
$z' = \Lambda z$, $z(t_0) = Q^{-1} y_0$ on $I$. This is (11.85) of [quarteroni2000numerical]. -/
theorem linear_diagonalized_isSolutionOn (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q)
    {t₀ : ℝ} {y₀ : n → ℂ} {I : Set ℝ} {y : ℝ → n → ℂ}
    (hy : IsSolutionOn (fun _ v => A *ᵥ v) t₀ y₀ I y) :
    IsSolutionOn (fun _ v => diagonal μ *ᵥ v) t₀ (Q⁻¹ *ᵥ y₀) I fun t => Q⁻¹ *ᵥ y t := by
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  refine ⟨by simp [hy.1], fun t ht => ?_⟩
  have h := hasDerivWithinAt_mulVec Q⁻¹ (hy.2 t ht)
  have e : diagonal μ *ᵥ (Q⁻¹ *ᵥ y t) = Q⁻¹ *ᵥ (A *ᵥ y t) := by
    rw [mulVec_mulVec, mulVec_mulVec, hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  change HasDerivWithinAt _ (diagonal μ *ᵥ (Q⁻¹ *ᵥ y t)) I t
  rw [e]
  exact h

/-- The converse of `ODE.linear_diagonalized_isSolutionOn`. Let $A = Q \Lambda Q^{-1}$ with
$\Lambda = \operatorname{diag}(\mu)$ and $Q \in \mathbb{C}^{n \times n}$ invertible. If $z$
solves $z' = \Lambda z$, $z(t_0) = z_0$ on a set of times $I$, then $y = Qz$ solves $y' = Ay$,
$y(t_0) = Q z_0$ on $I$. -/
theorem linear_isSolutionOn_of_diagonalized (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q)
    {t₀ : ℝ} {z₀ : n → ℂ} {I : Set ℝ} {z : ℝ → n → ℂ}
    (hz : IsSolutionOn (fun _ v => diagonal μ *ᵥ v) t₀ z₀ I z) :
    IsSolutionOn (fun _ v => A *ᵥ v) t₀ (Q *ᵥ z₀) I fun t => Q *ᵥ z t := by
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  refine ⟨by simp [hz.1], fun t ht => ?_⟩
  have h := hasDerivWithinAt_mulVec Q (hz.2 t ht)
  have e : A *ᵥ (Q *ᵥ z t) = Q *ᵥ (diagonal μ *ᵥ z t) := by
    rw [mulVec_mulVec, mulVec_mulVec, hA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
      Matrix.mul_one]
  change HasDerivWithinAt _ (A *ᵥ (Q *ᵥ z t)) I t
  rw [e]
  exact h

/-- **A diagonal system is $n$ scalar test equations.** A function $z : \mathbb{R} \to \mathbb{C}^n$
solves $z' = \operatorname{diag}(\mu) z$, $z(t_0) = z_0$ on a set of times $I$ if and only if,
for every $j$, the component $z_j$ solves the scalar equation $z_j' = \mu_j z_j$,
$z_j(t_0) = (z_0)_j$ on $I$. -/
theorem isSolutionOn_diagonal_iff {t₀ : ℝ} {z₀ : n → ℂ} {I : Set ℝ} {z : ℝ → n → ℂ} :
    IsSolutionOn (fun _ v => diagonal μ *ᵥ v) t₀ z₀ I z ↔
      ∀ j, IsSolutionOn (fun _ w => μ j * w) t₀ (z₀ j) I fun t => z t j := by
  simp only [IsSolutionOn, funext_iff, forall_and, forall_comm (α := n)]
  refine and_congr Iff.rfl (forall_congr' fun t => forall_congr' fun _ => ?_)
  rw [hasDerivWithinAt_pi]
  simp only [mulVec_diagonal]

/-! ### The stiffness quotient -/

/-- **The stiffness quotient** of $A \in \mathbb{C}^{n \times n}$:
$$r_s = \frac{\sigma}{\tau}, \qquad \sigma = \inf_{\lambda \in \operatorname{spec}(A)}
  \operatorname{Re} \lambda, \quad \tau = \sup_{\lambda \in \operatorname{spec}(A)}
  \operatorname{Re} \lambda,$$
where $\operatorname{spec}(A)$ is the spectrum of $A$. This is (11.86) of
[quarteroni2000numerical]. The spectrum is the finite set of eigenvalues, so $\sigma$ and $\tau$
are the minimum and the maximum of their real parts. When the spectrum is nonempty and all
eigenvalues have negative real part, $\sigma \le \tau < 0$ and $r_s \ge 1$.

The book calls the system stiff when $r_s \gg 1$, which is not a definition. The definition uses
`sInf` and `sSup` of `Complex.re '' spectrum ℂ A`. For $n = 0$ the spectrum is empty, both are
$0$, and $r_s = 0$. -/
noncomputable def stiffnessQuotient (A : Matrix n n ℂ) : ℝ :=
  sInf (Complex.re '' spectrum ℂ A) / sSup (Complex.re '' spectrum ℂ A)

/-- Let $A \in \mathbb{C}^{n \times n}$ have a nonempty spectrum, and let every eigenvalue $\lambda$
of $A$ satisfy $\operatorname{Re} \lambda < 0$. Then the stiffness quotient satisfies
$r_s \ge 1$, because $\sigma \le \tau < 0$ gives $\sigma / \tau \ge 1$. -/
theorem one_le_stiffnessQuotient (A : Matrix n n ℂ) (hne : (spectrum ℂ A).Nonempty)
    (hneg : ∀ μ ∈ spectrum ℂ A, μ.re < 0) : 1 ≤ stiffnessQuotient A := by
  have hfin : (Complex.re '' spectrum ℂ A).Finite := A.finite_spectrum.image _
  have hne' : (Complex.re '' spectrum ℂ A).Nonempty := hne.image _
  have hτ : sSup (Complex.re '' spectrum ℂ A) < 0 := by
    obtain ⟨μ, hμ, hμ'⟩ := hne'.csSup_mem hfin
    rw [← hμ']
    exact hneg μ hμ
  have hστ : sInf (Complex.re '' spectrum ℂ A) ≤ sSup (Complex.re '' spectrum ℂ A) :=
    csInf_le_csSup hne' hfin.bddBelow hfin.bddAbove
  rw [stiffnessQuotient, le_div_iff_of_neg hτ, one_mul]
  exact hστ

end ODE
