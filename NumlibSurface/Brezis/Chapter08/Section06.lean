/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Variational.EllipticInterval.SturmLiouville
import NumlibSurface.Brezis.Chapter08.Section05

/-!
# Brezis, Section 8.6: Eigenfunctions and spectral decomposition

This module formalizes Section 8.6 of [brezis2011functional]. Let $I = (0, 1)$ and
$\bar I = [0, 1]$, let $p \in C^1(\bar I)$ with $p \ge \alpha > 0$ on $\bar I$, and let
$q \in C(\bar I)$. Theorem 8.22 says that the Sturm–Liouville operator $Au = -(pu')' + qu$ with
Dirichlet conditions has a sequence of eigenvalues $\lambda_n \to +\infty$ and a Hilbert basis
$(e_n)$ of $L^2(I)$ of eigenfunctions, with $e_n \in C^2(\bar I)$ and (37):
$$-(pe_n')' + qe_n = \lambda_n e_n \text{ on } I, \qquad e_n(0) = e_n(1) = 0.$$
The proof reduces to $q \ge 0$ and applies the spectral theorem for compact self-adjoint operators
(Theorem 6.11) to the solution operator $T : f \mapsto u$ of the problem (38), $-(pu')' + qu = f$,
$u(0) = u(1) = 0$. In the Example of the section, $p \equiv 1$ and $q \equiv 0$, the eigenfunctions
are $e_n(x) = \sqrt2 \sin(n\pi x)$ with $\lambda_n = n^2\pi^2$, $n \ge 1$. Remark 30 says that the
solution operator of the problem on $\mathbb{R}$ of Example 8 is bounded and self-adjoint but not
compact.

The proofs specialize the backbone module `Numlib.Variational.EllipticInterval.SturmLiouville` and
the spectral theorem `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` of chapter 6.

## Main results

* Theorem 8.22, `Brezis.Chapter08.theorem_8_22`: for $p \in C^1(\bar I)$ with $p \ge \alpha > 0$ and
  $q \in C(\bar I)$ there are real numbers $\lambda_n \to +\infty$ and a Hilbert basis $(e_n)$ of
  $L^2(I)$ of $C^2$ solutions of (37).
* Theorem 8.22, the Hilbert basis, `Brezis.Chapter08.theorem_8_22_basis`: for $q \ge 0$, the
  eigenfunctions are eigenvectors of $T$ with $Te_n = \lambda_n^{-1} e_n$ and $\lambda_n > 0$.
* Theorem 8.22, the eigenfunction equation, `Brezis.Chapter08.theorem_8_22_eigen`: for $q \ge 0$,
  each $e_n$ is a $C^2$ solution of (37).
* Theorem 8.22, the eigenvalues, `Brezis.Chapter08.theorem_8_22_tendsto`: for $q \ge 0$,
  $\lambda_n \to +\infty$.
* Theorem 8.22, the solution operator, `Brezis.Chapter08.theorem_8_22_operator`: for $q \ge 0$, $T$
  is compact, self-adjoint, positive and injective.
* Section 8.6, the Example, `Brezis.Chapter08.sineEigenfunctions_eigen`: $\sqrt2 \sin(n\pi x)$ is a
  $C^2$ solution of $-e'' = n^2\pi^2 e$, $e(0) = e(1) = 0$.
* Section 8.6, the Example, `Brezis.Chapter08.sineEigenfunctions_hilbertBasis`: these functions form
  a Hilbert basis of $L^2(0, 1)$ of eigenvectors of $T$.
* Section 8.6, the Example, `Brezis.Chapter08.sineEigenfunctions_eigenvalue`: the eigenvalues of
  Theorem 8.22 for $p \equiv 1$, $q \equiv 0$ are exactly the numbers $n^2\pi^2$, each simple.
* Section 8.6, the Example, `Brezis.Chapter08.sineEigenfunctions_classical`: every nonzero $C^2$
  Dirichlet eigenfunction of $-u''$ on $[0, 1]$ is a multiple of some $\sin(n\pi x)$.
* Section 8.6, the Example, `Brezis.Chapter08.sineEigenfunctions`: the first three statements of the
  Example together.
* Remark 30, `Brezis.Chapter08.remark_8_30_bounded_selfAdjoint`: the solution operator of Example 8
  on $L^2(\mathbb{R})$ is bounded and self-adjoint.
* Remark 30, `Brezis.Chapter08.remark_8_30_not_compact`: this operator is not compact.

## Conventions

* The hypotheses $p \in C^1(\bar I)$, $p \ge \alpha > 0$, $q \in C(\bar I)$ and $q \ge 0$ are the
  backbone's `EllipticInterval.SturmLiouville.Hypotheses 0 1 p q α`. The eigenfunctions, the
  eigenvalues and the solution operator for these hypotheses are
  `EllipticInterval.SturmLiouville.eigenfunction`, `EllipticInterval.SturmLiouville.eigenvalue` and
  `EllipticInterval.SturmLiouville.solutionOperator`.
* $L^2(I)$ is `Lp ℝ 2 (volume.restrict (Ioo 0 1))`, and a Hilbert basis $(e_n)$ of $L^2(I)$ is a
  `HilbertBasis ℕ ℝ` of this space.
* "$e_n \in C^2(\bar I)$" is an element `v` of `ContDiffMapIcc zero_le_one 2` that is equal to $e_n$
  almost everywhere. Equation (37) is stated on $(0, 1)$, with the derivative of the extension of
  $v'$ to $\mathbb{R}$ (`v.shift.extend`), as in Section 8.4.
* The sines of the Example are indexed from $0$: $\sqrt2 \sin(n\pi x)$ for $n \ge 1$ is
  `sinUnitFun (n - 1)`, and the Hilbert basis is `sinBasisUnit`, of the module
  `Numlib.Analysis.Fourier.SineBasis`.

## Implementation notes

* Theorem 8.22 is stated for every continuous $q$. The reduction of the source, which replaces $q$
  by $q + C$ and so $\lambda_n$ by $\lambda_n + C$, is carried out in the proof. The parts
  `Brezis.Chapter08.theorem_8_22_basis`, `Brezis.Chapter08.theorem_8_22_eigen`,
  `Brezis.Chapter08.theorem_8_22_tendsto` and `Brezis.Chapter08.theorem_8_22_operator` are stated
  for $q \ge 0$, the normalization of the backbone.

## Not formalized

* **Remark 29.** The eigenvalues of $-u''$ under the boundary conditions of Examples 3, 5, 6 and 7
  of Section 8.4. The source leaves them as an exercise.
* **Remark 30, the spectrum.** The eigenvalues and the spectrum of the operator $T$ on
  $L^2(\mathbb{R})$, which the source leaves to Exercise 8.38.
-/

open Filter MeasureTheory Set TopologicalSpace EllipticInterval EllipticInterval.SturmLiouville
open scoped InnerProductSpace Topology

noncomputable section

namespace Brezis.Chapter08

/-! ### Theorem 8.22 -/

/-- The hypotheses of Theorem 8.22 hold for $q + C$, for a constant $C \ge 0$ that bounds $-q$ on
$[0, 1]$: the reduction of the source to $q \ge 0$. -/
private theorem hypotheses_add_const {p q : ℝ → ℝ} {α : ℝ} (hp : ContDiffOn ℝ 1 p (Icc 0 1))
    (hα : 0 < α) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α ≤ p x) (hq : ContinuousOn q (Icc 0 1)) :
    ∃ C : ℝ, Hypotheses 0 1 p (fun x ↦ q x + C) α := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hq
  refine ⟨max 0 (-q x₀), ⟨zero_lt_one, hp, hα, hpα, hq.add continuousOn_const, fun x hx ↦ ?_⟩⟩
  have := isMinOn_iff.1 hmin x hx
  have := le_max_right 0 (-q x₀)
  linarith

/-- **Theorem 8.22** of [brezis2011functional]. Let $I = (0, 1)$ and $\alpha > 0$, let
$p \in C^1([0, 1])$ satisfy $p \ge \alpha$ on $[0, 1]$, and let $q$ be continuous on $[0, 1]$.
Then there are a sequence $(\lambda_n)$ of real numbers and a Hilbert basis $(e_n)$ of $L^2(I)$
with the following properties:
* each $e_n$ is equal almost everywhere on $I$ to some $e \in C^2([0, 1])$ that satisfies (37),
  $-(pe')' + qe = \lambda_n e$ on $I$ and $e(0) = e(1) = 0$;
* $\lambda_n \to +\infty$ as $n \to \infty$.

The proof follows the source: it replaces $q$ by $q + C$, which replaces $\lambda_n$ by
$\lambda_n + C$, and uses the backbone's `EllipticInterval.SturmLiouville.eigenfunction`,
`EllipticInterval.SturmLiouville.eigenvalue`,
`EllipticInterval.SturmLiouville.exists_contDiffMapIcc_eigenfunction` and
`EllipticInterval.SturmLiouville.tendsto_eigenvalue_atTop`. These come from the spectral theorem
for the compact self-adjoint solution operator, Theorem 6.11. -/
theorem theorem_8_22 {p q : ℝ → ℝ} {α : ℝ} (hp : ContDiffOn ℝ 1 p (Icc 0 1)) (hα : 0 < α)
    (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α ≤ p x) (hq : ContinuousOn q (Icc 0 1)) :
    ∃ (l : ℕ → ℝ) (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))),
      (∀ n, ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
        ((e n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v.extend) ∧
        v.extend 0 = 0 ∧ v.extend 1 = 0 ∧
        ∀ x ∈ Ioo (0 : ℝ) 1,
          -deriv (fun t ↦ p t * v.shift.extend t) x + q x * v.extend x = l n * v.extend x) ∧
      Tendsto l atTop atTop := by
  obtain ⟨C, h⟩ := hypotheses_add_const hp hα hpα hq
  refine ⟨fun n ↦ eigenvalue h n - C, eigenfunction h, fun n ↦ ?_, ?_⟩
  · obtain ⟨v, hv, hv0, hv1, hode⟩ := exists_contDiffMapIcc_eigenfunction h n
    refine ⟨v, hv, hv0, hv1, fun x hx ↦ ?_⟩
    have := hode x hx
    linarith
  · exact tendsto_atTop_add_const_right _ (-C) (tendsto_eigenvalue_atTop h)

/-- **Theorem 8.22** of [brezis2011functional], the Hilbert basis. Let $p \in C^1([0, 1])$ with
$p \ge \alpha > 0$ on $[0, 1]$, and let $q \in C([0, 1])$ with $q \ge 0$ on $[0, 1]$. Let $T$ be
the solution operator of (38), let $(e_n)$ be the Hilbert basis
`EllipticInterval.SturmLiouville.eigenfunction h` of $L^2(0, 1)$, and let $\lambda_n$ be the
eigenvalues. Then for every $n$,
$$Te_n = \lambda_n^{-1} e_n \qquad \text{and} \qquad \lambda_n > 0.$$

The eigenvalues $\lambda_n = 1/\mu_n$ are the reciprocals of the eigenvalues $\mu_n$ of $T$. -/
theorem theorem_8_22_basis {p q : ℝ → ℝ} {α : ℝ} (h : Hypotheses 0 1 p q α) (n : ℕ) :
    solutionOperator h (eigenfunction h n) = (eigenvalue h n)⁻¹ • eigenfunction h n ∧
      0 < eigenvalue h n := by
  refine ⟨?_, eigenvalue_pos h n⟩
  rw [eigenvalue, inv_inv]
  exact solutionOperator_eigenfunction h n

/-- **Theorem 8.22** of [brezis2011functional], the eigenfunction equation (37). Let
$p \in C^1([0, 1])$ with $p \ge \alpha > 0$ on $[0, 1]$, and let $q \in C([0, 1])$ with
$q \ge 0$ on $[0, 1]$. For every $n$, the eigenfunction $e_n$ is equal almost everywhere on
$(0, 1)$ to some $e \in C^2([0, 1])$ with
$$-(pe')' + qe = \lambda_n e \text{ on } (0, 1), \qquad e(0) = e(1) = 0.$$

The proof specializes `EllipticInterval.SturmLiouville.exists_contDiffMapIcc_eigenfunction`. -/
theorem theorem_8_22_eigen {p q : ℝ → ℝ} {α : ℝ} (h : Hypotheses 0 1 p q α) (n : ℕ) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ((eigenfunction h n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v.extend) ∧
      v.extend 0 = 0 ∧ v.extend 1 = 0 ∧
      ∀ x ∈ Ioo (0 : ℝ) 1,
        -deriv (fun t ↦ p t * v.shift.extend t) x + q x * v.extend x
          = eigenvalue h n * v.extend x :=
  exists_contDiffMapIcc_eigenfunction h n

/-- **Theorem 8.22** of [brezis2011functional], the eigenvalues tend to $+\infty$. Let
$p \in C^1([0, 1])$ with $p \ge \alpha > 0$ on $[0, 1]$, and let $q \in C([0, 1])$ with
$q \ge 0$ on $[0, 1]$. Then $\lambda_n \to +\infty$ as $n \to \infty$.

This holds because $\lambda_n = 1/\mu_n$, where the eigenvalues $\mu_n > 0$ of the compact
operator $T$ tend to $0$. -/
theorem theorem_8_22_tendsto {p q : ℝ → ℝ} {α : ℝ} (h : Hypotheses 0 1 p q α) :
    Tendsto (eigenvalue h) atTop atTop :=
  tendsto_eigenvalue_atTop h

/-- **Theorem 8.22** of [brezis2011functional], the solution operator of the proof. Let
$p \in C^1([0, 1])$ with $p \ge \alpha > 0$ on $[0, 1]$, and let $q \in C([0, 1])$ with
$q \ge 0$ on $[0, 1]$. Let $T : L^2(I) \to L^2(I)$ be the bounded operator $f \mapsto u$, where
$u \in H^2(I) \cap H_0^1(I)$ is the unique solution of (38), $-(pu')' + qu = f$,
$u(0) = u(1) = 0$. Then:
* $Tf$ is the function of the weak solution `EllipticInterval.SturmLiouville.solution h f`, as
  an element of $L^2(I)$;
* $T$ is compact;
* $T$ is self-adjoint: $\int (Tf)g = \int f(Tg)$ for all $f, g \in L^2(I)$;
* $T$ is positive: $\int (Tf)f \ge 0$ for all $f \in L^2(I)$;
* $N(T) = \{0\}$.

The operator is `EllipticInterval.SturmLiouville.solutionOperator`, which is bounded by its
type; the estimate $\|Tf\|_{H^1} \le C\|f\|_{L^2}$ is
`EllipticInterval.SturmLiouville.norm_solution_le`. $T$ is compact because the injection
$H^1(I) \subset L^2(I)$ is compact for bounded $I$. Theorem 6.11 then applies. -/
theorem theorem_8_22_operator {p q : ℝ → ℝ} {α : ℝ} (h : Hypotheses 0 1 p q α) :
    (∀ f, solutionOperator h f = SobolevInterval.deriv (solution h f) 0) ∧
    IsCompactOperator (solutionOperator h) ∧
    (∀ f g, ⟪solutionOperator h f, g⟫_ℝ = ⟪f, solutionOperator h g⟫_ℝ) ∧
    (∀ f, 0 ≤ ⟪solutionOperator h f, f⟫_ℝ) ∧
    LinearMap.ker (solutionOperator h : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) = ⊥ :=
  ⟨solutionOperator_apply h, isCompactOperator_solutionOperator h,
    fun f g ↦ isSymmetric_solutionOperator h f g, inner_solutionOperator_nonneg h,
    ker_solutionOperator h⟩

/-! ### The Example: $p \equiv 1$, $q \equiv 0$ -/

/-- **Section 8.6** of [brezis2011functional], the Example, the functions. For $p \equiv 1$ and
$q \equiv 0$ the source gives $e_n(x) = \sqrt2 \sin(n\pi x)$ and $\lambda_n = n^2\pi^2$,
$n = 1, 2, \dots$. For every $n \ge 0$, the function $s_n(x) = \sqrt2 \sin((n + 1)\pi x)$ is in
$C^2(\mathbb{R})$, satisfies $s_n(0) = s_n(1) = 0$, and
$$-s_n'' = (n + 1)^2\pi^2 s_n \text{ on } \mathbb{R}.$$

The function $s_n$ is `sinUnitFun n`. -/
theorem sineEigenfunctions_eigen (n : ℕ) :
    ContDiff ℝ 2 (sinUnitFun n) ∧ sinUnitFun n 0 = 0 ∧ sinUnitFun n 1 = 0 ∧
      ∀ x, -deriv (deriv (sinUnitFun n)) x = ((n + 1) * Real.pi) ^ 2 * sinUnitFun n x :=
  ⟨(contDiff_sinUnitFun n).of_le (by simp), sinUnitFun_zero n, sinUnitFun_one n, fun x ↦ by
    rw [deriv_deriv_sinUnitFun]; ring⟩

/-- **Section 8.6** of [brezis2011functional], the Example, the Hilbert basis. The functions
$s_n(x) = \sqrt2 \sin((n + 1)\pi x)$, $n \ge 0$, form a Hilbert basis of $L^2(0, 1)$, and they
are eigenvectors of the solution operator $T$ of $-u''$ with Dirichlet conditions:
$$Ts_n = \frac{1}{(n + 1)^2\pi^2} s_n.$$

The Hilbert basis is `sinBasisUnit`. It is obtained from the cosine basis of
`Numlib.Analysis.Fourier.CosineBasis` by multiplication with a sine, not from the abstract
spectral theorem. The operator $T$ is `EllipticInterval.SturmLiouville.solutionOperator` for
`EllipticInterval.SturmLiouville.hypotheses_one_zero`. -/
theorem sineEigenfunctions_hilbertBasis :
    (∀ n, (sinBasisUnit n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ √2 * Real.sin ((n + 1) * Real.pi * x)) ∧
    ∀ n, solutionOperator hypotheses_one_zero (sinBasisUnit n)
      = (((n + 1) * Real.pi) ^ 2)⁻¹ • sinBasisUnit n :=
  ⟨coeFn_sinBasisUnit, solutionOperator_sinBasisUnit⟩

/-- **Section 8.6** of [brezis2011functional], the Example, the eigenvalues. For $p \equiv 1$ and
$q \equiv 0$, the eigenvalues $\lambda_n$ of Theorem 8.22 are exactly the numbers $n^2\pi^2$,
$n = 1, 2, \dots$, and each is simple: the set of values of $n \mapsto \lambda_n$ is
$\{(n + 1)^2\pi^2 : n \in \mathbb{N}\}$, and $n \mapsto \lambda_n$ is injective.

The eigenvalues are `EllipticInterval.SturmLiouville.eigenvalue hypotheses_one_zero`. The proof
specializes `EllipticInterval.SturmLiouville.eigenvalue_eq_sq_pi_sq`, which expands an
eigenvector of $T$ in the sine basis. -/
theorem sineEigenfunctions_eigenvalue :
    range (eigenvalue hypotheses_one_zero) = range (fun n : ℕ ↦ ((n + 1) * Real.pi) ^ 2) ∧
      Function.Injective (eigenvalue hypotheses_one_zero) :=
  eigenvalue_eq_sq_pi_sq

/-- **Section 8.6** of [brezis2011functional], the Example in classical form. Let
$e \in C^2([0, 1])$ be nonzero and $\lambda \in \mathbb{R}$, with
$$-e'' = \lambda e \text{ on } [0, 1], \qquad e(0) = e(1) = 0.$$
Then there is $n \ge 0$ with $\lambda = (n + 1)^2\pi^2$, and there is $c \neq 0$ with
$e(x) = c \sin((n + 1)\pi x)$ for all $x \in [0, 1]$.

The proof specializes `EllipticInterval.SturmLiouville.eq_smul_sin_of_dirichlet`. -/
theorem sineEigenfunctions_classical (e : ContDiffMapIcc (zero_le_one' ℝ) 2) {l : ℝ}
    (hode : ∀ x : Icc (0 : ℝ) 1, -e.deriv 2 x = l * e x)
    (h0 : e ⟨0, left_mem_Icc.2 zero_le_one⟩ = 0) (h1 : e ⟨1, right_mem_Icc.2 zero_le_one⟩ = 0)
    (hne : e ≠ 0) :
    ∃ n : ℕ, l = ((n + 1) * Real.pi) ^ 2 ∧
      ∃ c : ℝ, c ≠ 0 ∧ ∀ x ∈ Icc (0 : ℝ) 1, e.extend x = c * Real.sin ((n + 1) * Real.pi * x) :=
  eq_smul_sin_of_dirichlet e hode h0 h1 hne

/-- **Section 8.6** of [brezis2011functional], the Example. If $p \equiv 1$ and $q \equiv 0$, then
$e_n(x) = \sqrt2 \sin(n\pi x)$ and $\lambda_n = n^2\pi^2$, $n = 1, 2, \dots$. With the index
$n \ge 0$ and $s_n(x) = \sqrt2 \sin((n + 1)\pi x)$:
* each $s_n$ is in $C^2(\mathbb{R})$, satisfies $s_n(0) = s_n(1) = 0$, and
  $-s_n'' = (n + 1)^2\pi^2 s_n$ (`Brezis.Chapter08.sineEigenfunctions_eigen`);
* the Hilbert basis `sinBasisUnit` of $L^2(0, 1)$ consists of the functions $s_n$, and
  $Ts_n = ((n + 1)^2\pi^2)^{-1} s_n$ for the solution operator $T$
  (`Brezis.Chapter08.sineEigenfunctions_hilbertBasis`);
* the eigenvalues of Theorem 8.22 are exactly the numbers $(n + 1)^2\pi^2$, each simple
  (`Brezis.Chapter08.sineEigenfunctions_eigenvalue`). -/
theorem sineEigenfunctions :
    (∀ n : ℕ, ContDiff ℝ 2 (sinUnitFun n) ∧ sinUnitFun n 0 = 0 ∧ sinUnitFun n 1 = 0 ∧
      ∀ x, -deriv (deriv (sinUnitFun n)) x = ((n + 1) * Real.pi) ^ 2 * sinUnitFun n x) ∧
    (∀ n, (sinBasisUnit n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] sinUnitFun n) ∧
    (∀ n, solutionOperator hypotheses_one_zero (sinBasisUnit n)
      = (((n + 1) * Real.pi) ^ 2)⁻¹ • sinBasisUnit n) ∧
    range (eigenvalue hypotheses_one_zero) = range (fun n : ℕ ↦ ((n + 1) * Real.pi) ^ 2) ∧
    Function.Injective (eigenvalue hypotheses_one_zero) :=
  ⟨sineEigenfunctions_eigen, coeFn_sinBasisUnit, solutionOperator_sinBasisUnit,
    eigenvalue_eq_sq_pi_sq.1, eigenvalue_eq_sq_pi_sq.2⟩

/-! ### Remark 30 -/

/-- **Remark 30** in Chapter 8 of [brezis2011functional], boundedness and self-adjointness. There is
a bounded linear operator $T : L^2(\mathbb{R}) \to L^2(\mathbb{R})$ such that, for every
$f \in L^2(\mathbb{R})$, $Tf$ is the solution $u \in H^2(\mathbb{R})$ of problem (30) of Example
8, read in $L^2(\mathbb{R})$, and
$$\langle Tf, g \rangle = \langle f, Tg \rangle \quad \text{for all } f, g \in
  L^2(\mathbb{R}).$$

The solution is `EllipticInterval.Line.solution f`, read in $L^2(\mathbb{R})$ through the
inclusion $H^1(\mathbb{R}) \subset L^2(\mathbb{R})$. The symmetry holds because
$\langle Tf, g \rangle = (Tf, Tg)_{H^1}$, by the weak equation of $Tg$ tested against $Tf$. -/
theorem remark_8_30_bounded_selfAdjoint :
    ∃ T : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ]
        Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      (∀ f, T f = SobolevIntervalLp.deriv (Line.solution f) 0) ∧
      ∀ f g, ⟪T f, g⟫_ℝ = ⟪f, T g⟫_ℝ := by
  -- the weak solution depends linearly on `f`
  have hadd : ∀ f g, Line.solution (f + g) = Line.solution f + Line.solution g := fun f g ↦
    (Line.eq_solution_of_forall fun v ↦ by
      rw [map_add, add_apply, Line.form_solution, Line.form_solution,
        Line.load_apply_inner, Line.load_apply_inner, Line.load_apply_inner, inner_add_left]).symm
  have hsmul : ∀ (c : ℝ) f, Line.solution (c • f) = c • Line.solution f := fun c f ↦
    (Line.eq_solution_of_forall fun v ↦ by
      rw [map_smulₛₗ, smul_apply, Line.form_solution, Line.load_apply_inner,
        Line.load_apply_inner, real_inner_smul_left, RCLike.conj_to_real, smul_eq_mul]).symm
  -- and is bounded by `‖f‖`
  have hbound : ∀ f, ‖SobolevIntervalLp.deriv (Line.solution f) 0‖ ≤ 1 * ‖f‖ := fun f ↦ by
    rw [one_mul]
    refine (SobolevIntervalLp.norm_deriv_le _ 0).trans ?_
    rw [Line.solution, LinearIsometryEquiv.norm_map, Line.load]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [innerSL_apply_norm]
    exact mul_le_of_le_one_right (norm_nonneg _) (SobolevIntervalLp.norm_derivL_le _)
  let Tₗ : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    { toFun := fun f ↦ SobolevIntervalLp.deriv (Line.solution f) 0
      map_add' := fun f g ↦ by simp only [hadd, SobolevIntervalLp.deriv_add]
      map_smul' := fun c f ↦ by simp only [hsmul, SobolevIntervalLp.deriv_smul, RingHom.id_apply] }
  refine ⟨Tₗ.mkContinuous 1 hbound, fun f ↦ rfl, fun f g ↦ ?_⟩
  -- `⟪T f, g⟫ = (T f, T g)_{H¹} = ⟪f, T g⟫`
  have e1 : ⟪SobolevIntervalLp.deriv (Line.solution f) 0, g⟫_ℝ
      = ⟪Line.solution g, Line.solution f⟫_ℝ := by
    rw [real_inner_comm, ← Line.load_apply_inner, ← Line.form_solution, Line.form_apply]
  have e2 : ⟪f, SobolevIntervalLp.deriv (Line.solution g) 0⟫_ℝ
      = ⟪Line.solution f, Line.solution g⟫_ℝ := by
    rw [← Line.load_apply_inner, ← Line.form_solution, Line.form_apply]
  change ⟪SobolevIntervalLp.deriv (Line.solution f) 0, g⟫_ℝ
    = ⟪f, SobolevIntervalLp.deriv (Line.solution g) 0⟫_ℝ
  rw [e1, e2, real_inner_comm]

/-- **Remark 30** in Chapter 8 of [brezis2011functional], the operator is not compact. Let
$T : L^2(\mathbb{R}) \to L^2(\mathbb{R})$ be a bounded linear operator such that $Tf$ is the
solution of problem (30) of Example 8 for every $f \in L^2(\mathbb{R})$, as in
`Brezis.Chapter08.remark_8_30_bounded_selfAdjoint`. Then $T$ is not compact.

The operator $T$ commutes with the translations $\tau_n$
(`EllipticInterval.Line.solution_translateLp`). For $f \neq 0$, the translates $\tau_n f$ are
bounded in $L^2(\mathbb{R})$ by $\|f\|$, and $T$ maps them to the translates $\tau_n(Tf)$ of
$Tf \neq 0$ ($T$ is injective by `EllipticInterval.Line.solution_eq_zero_iff`). These have no
convergent subsequence (`EllipticInterval.Line.not_tendsto_translateLp`). This is the argument
of Remark 10(c). The eigenvalues and the spectrum of $T$, Exercise 8.38 of the source, are not
stated. -/
theorem remark_8_30_not_compact
    (T : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ]
      Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hT : ∀ f, T f = SobolevIntervalLp.deriv (Line.solution f) 0) : ¬ IsCompactOperator T := by
  intro hc
  -- a nonzero `f ∈ L²(ℝ)`: the indicator of `[0, 1]`
  obtain ⟨f, hf⟩ : ∃ f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), f ≠ 0 := by
    have hμs : volume.restrict ((⊤ : Opens ℝ) : Set ℝ) (Icc (0 : ℝ) 1) ≠ ⊤ := by
      rw [Measure.restrict_apply measurableSet_Icc]
      exact (measure_mono inter_subset_left).trans_lt measure_Icc_lt_top |>.ne
    refine ⟨indicatorConstLp 2 measurableSet_Icc hμs (1 : ℝ), fun h0 ↦ ?_⟩
    have := congrArg norm h0
    rw [norm_zero, norm_indicatorConstLp two_ne_zero (by simp), norm_one, one_mul,
      measureReal_def, Measure.restrict_apply measurableSet_Icc, Opens.coe_top, inter_univ,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal zero_le_one, Real.one_rpow] at this
    exact one_ne_zero this
  -- `T f ≠ 0`
  have hg : T f ≠ 0 := fun h0 ↦ by
    rw [hT] at h0
    refine hf ((Line.solution_eq_zero_iff f).1 (SobolevMultiIndex.ext_of_fn_ae_eq ?_))
    change ⇑(SobolevIntervalLp.deriv (Line.solution f) 0) =ᵐ[_] _
    rw [h0]
    exact (Lp.coeFn_zero ℝ 2 _).trans SobolevMultiIndex.fn_zero.symm
  -- `T` commutes with the translations
  have hTn : ∀ n : ℕ, T (Line.translateLp n f) = Line.translateLp n (T f) := fun n ↦ by
    rw [hT, hT, Line.solution_translateLp, Line.deriv_translate]
  -- the translates `τ_n (T f)` lie in a compact set, so a subsequence converges
  have hc' : IsCompactOperator (T : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) := by rwa [ContinuousLinearMap.coe_coe]
  have hK := hc'.isCompact_closure_image_closedBall ‖f‖
  have hmem : ∀ n : ℕ, Line.translateLp n (T f) ∈ closure ((T : Lp ℝ 2 (volume.restrict
      ((⊤ : Opens ℝ) : Set ℝ)) →ₗ[ℝ] Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) ''
        Metric.closedBall 0 ‖f‖) := fun n ↦
    subset_closure ⟨Line.translateLp n f, by simp, hTn n⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  exact Line.not_tendsto_translateLp hg hφ a hlim

end Brezis.Chapter08
