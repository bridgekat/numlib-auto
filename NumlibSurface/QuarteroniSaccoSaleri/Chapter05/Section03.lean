/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Similar
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 5.3: The Power Method

This module formalizes Section 5.3 of [quarteroni2000numerical]. The power method (5.17) starts from
a unit vector $q^{(0)}$ and sets $z^{(k)} = A q^{(k-1)}$ and $q^{(k)} = z^{(k)} / \|z^{(k)}\|_2$, so
that $q^{(k)} = A^k q^{(0)} / \|A^k q^{(0)}\|_2$ (5.18), and it approximates the dominant eigenvalue
by the Rayleigh quotient $\nu^{(k)} = (q^{(k)})^H A q^{(k)}$. Let $A$ be diagonalizable with
eigenvalues ordered as in (5.16), $|\lambda_1| > |\lambda_2| \ge |\lambda_i|$, and let
$q^{(0)} = \sum_i \alpha_i x_i$ with $\alpha_1 \neq 0$ (5.19). Then the iterates approach the
direction of $x_1$ at the rate $|\lambda_2 / \lambda_1|^k$ (Theorem 5.6), and
$\nu^{(k)} \to \lambda_1$. For a real symmetric matrix the Rayleigh quotients converge at the rate
$|\lambda_2 / \lambda_1|^{2k}$ (5.23). Each $\nu^{(k)}$ is an exact eigenvalue of a perturbed matrix
$A + \varepsilon E^{(k)}$ with $\varepsilon = \|r^{(k)}\|_2$ (5.24). Inverse iteration (5.28) is the
power method for $(A - \mu I)^{-1}$, and it converges to the eigenvalue closest to $\mu$. Section
5.3.3 treats two coincident dominant eigenvalues.

The proofs specialize the backbone modules `Numlib.Eigen.PowerMethod` (the power iteration in closed
form, its convergence and rate, the Rayleigh quotients, the symmetric rate, and inverse iteration)
and `Numlib.Eigen.Perturbation` (the backward error of an approximate eigenpair).

## Main definitions

* Equation (5.17), `QuarteroniSaccoSaleri.Chapter05.powerIterate`: the power method.
* Equation (5.17), `QuarteroniSaccoSaleri.Chapter05.rayleighQuotient`: the Rayleigh quotient
  $q^H A q$.
* Equation (5.28), `QuarteroniSaccoSaleri.Chapter05.inverseIterate`: inverse iteration with shift
  $\mu$.

## Main results

* Equation (5.17), `QuarteroniSaccoSaleri.Chapter05.powerIterate_eq_krylov`: the recursion of the
  book is the backbone's closed form.
* Equation (5.18), `QuarteroniSaccoSaleri.Chapter05.equation_5_18`:
  $q^{(k)} = A^k q^{(0)} / \|A^k q^{(0)}\|_2$.
* Theorem 5.6, `QuarteroniSaccoSaleri.Chapter05.theorem_5_6`: $\|\tilde q^{(k)} - x_1\|_2 \le C
  |\lambda_2 / \lambda_1|^k$.
* Theorem 5.6, `QuarteroniSaccoSaleri.Chapter05.theorem_5_6_rayleigh`: $\nu^{(k)} \to \lambda_1$.
* Equation (5.23), `QuarteroniSaccoSaleri.Chapter05.equation_5_23`: for a real symmetric $A$,
  $|\lambda_1 - \nu^{(k)}| \le (\lambda_{\max} - \lambda_{\min}) \tan^2 \theta_0 \, |\lambda_2 /
  \lambda_1|^{2k}$.
* Equation (5.24), `QuarteroniSaccoSaleri.Chapter05.equation_5_24`: $\nu^{(k)}$ is an eigenvalue of
  $A + \varepsilon E^{(k)}$, and $\varepsilon = \|r^{(k)}\|_2$ is the smallest such perturbation.
* Equation (5.28), `QuarteroniSaccoSaleri.Chapter05.inverseIterate_eq_krylov`: the recursion of the
  book is the backbone's inverse iteration.
* Section 5.3.2, `QuarteroniSaccoSaleri.Chapter05.inverseIterate_tendsto`: inverse iteration
  converges to the eigenvector and the eigenvalue closest to $\mu$.
* Section 5.3.3, `QuarteroniSaccoSaleri.Chapter05.powerIterate_of_eq`: if $\lambda_2 = \lambda_1$,
  the power method still converges.

## Conventions

* The matrix $A \in \mathbb{C}^{n \times n}$ is `Matrix (Fin n) (Fin n) ℂ`, which acts on
  `EuclideanSpace ℂ (Fin n)` through `Matrix.toEuclideanLin`. The iterations are stated over any
  `RCLike` field $\mathbb{K}$ ($\mathbb{R}$ or $\mathbb{C}$), so that the real symmetric estimate
  (5.23) is stated for `Matrix (Fin n) (Fin n) ℝ`.
* A diagonalizable $A$ with the matrix of eigenvectors $X = (x_1, \dots, x_n)$ is given by a basis
  `x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))` of eigenvectors with eigenvalues `lam`.
  The coefficients $\alpha_i$ of (5.19) are the coordinates `x.repr q₀ i`.
* The ordering (5.16) is given by two indices: `i₀` is the index $1$ of the dominant eigenvalue, and
  `i₁` is the index $2$. The hypotheses are $|\lambda_{i_1}| < |\lambda_{i_0}|$ and
  $|\lambda_i| \le |\lambda_{i_1}|$ for $i \neq i_0$.

## Implementation notes

* The power method (5.17) and inverse iteration (5.28) are written as the book writes them, as
  recursions that normalize after every step.
  `QuarteroniSaccoSaleri.Chapter05.powerIterate_eq_krylov` and
  `QuarteroniSaccoSaleri.Chapter05.inverseIterate_eq_krylov` identify them with the backbone's
  closed forms `Krylov.powerIterate` and `Krylov.inverseIterate`.
* The Rayleigh quotients $\nu^{(k)}$ and $\sigma^{(k)}$ are both
  `QuarteroniSaccoSaleri.Chapter05.rayleighQuotient`.

## Deviations from the source

* **Theorem 5.6** (correction). The book's constant $C = (\sum_{i \ge 2} (\alpha_i /
  \alpha_1)^2)^{1/2}$ needs orthonormal eigenvectors. For a diagonalizable $A$ the statement has
  $C = \sum_{i \ge 2} |\alpha_i / \alpha_1|$. See `QuarteroniSaccoSaleri.Chapter05.theorem_5_6`.
* **Equation (5.23)** (correction). The book prints the factor $|\lambda_1 - \lambda_n|$, which is
  false under the ordering (5.16) by modulus. The statement has the spread
  $\lambda_{\max} - \lambda_{\min}$ of the spectrum. See
  `QuarteroniSaccoSaleri.Chapter05.equation_5_23`.

## Not formalized

* **The a posteriori estimates (5.25), (5.26) and (5.29).** They are heuristic ($\simeq$).
* **Example 5.3.** It is numerical.
-/

open Filter Finset Matrix Topology
open scoped Matrix.Norms.L2Operator

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Bridges to the backbone -/

/-- Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $A \in \mathbb{K}^{n \times n}$ and
$\mu \in \mathbb{K}$. If $\mu \notin \sigma(A)$, then the shifted matrix $A - \mu I$ is
nonsingular. -/
theorem isUnit_sub_smul_one_of_notMem_spectrum {A : Matrix (Fin n) (Fin n) 𝕜} {μ : 𝕜}
    (hμ : μ ∉ spectrum 𝕜 A) : IsUnit (A - μ • (1 : Matrix (Fin n) (Fin n) 𝕜)) := by
  have h := (spectrum.notMem_iff.mp hμ).neg
  rwa [Algebra.algebraMap_eq_smul_one, neg_sub] at h

/-! ### Equation (5.17): the power method -/

/-- **Equation (5.17)** of [quarteroni2000numerical], the power method. Let
$A \in \mathbb{K}^{n \times n}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and let
$q^{(0)} \in \mathbb{K}^n$. For $k = 1, 2, \dots$, the method sets
$$z^{(k)} = A q^{(k-1)}, \qquad q^{(k)} = \frac{z^{(k)}}{\|z^{(k)}\|_2}.$$
The approximation of the eigenvalue is the Rayleigh quotient
$\nu^{(k)} = (q^{(k)})^H A q^{(k)}$, which is
`QuarteroniSaccoSaleri.Chapter05.rayleighQuotient`.

The book takes $\|q^{(0)}\|_2 = 1$; the definition takes any $q^{(0)}$. Lean divides by zero to
zero, so $z^{(k)} = 0$ gives $q^{(k)} = 0$, and the recursion is defined for every $k$. -/
noncomputable def powerIterate (A : Matrix (Fin n) (Fin n) 𝕜) (q₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → EuclideanSpace 𝕜 (Fin n)
  | 0 => q₀
  | k + 1 =>
    (‖toEuclideanLin A (powerIterate A q₀ k)‖ : 𝕜)⁻¹ • toEuclideanLin A (powerIterate A q₀ k)

/-- The **Rayleigh quotient** $q^H A q$ of a vector $q \in \mathbb{K}^n$ for
$A \in \mathbb{K}^{n \times n}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. At
$q = q^{(k)}$ it is the $\nu^{(k)}$ of (5.17) for the power method, and the $\sigma^{(k)}$ of
(5.28) for inverse iteration. There is no division by $q^H q$. -/
noncomputable def rayleighQuotient (A : Matrix (Fin n) (Fin n) 𝕜) (q : EuclideanSpace 𝕜 (Fin n)) :
    𝕜 :=
  inner 𝕜 q (toEuclideanLin A q)

/-- The recursion (5.17) of [quarteroni2000numerical] is the backbone's closed form. Let
$A \in \mathbb{K}^{n \times n}$ and $q^{(0)} \in \mathbb{K}^n$ with $\|q^{(0)}\|_2 = 1$. Then
for every $k$, the iterate $q^{(k)}$ is `Krylov.powerIterate (toEuclideanLin A) q₀ k`.

The proof specializes the backbone's `Krylov.eq_powerIterate_of_recurrence`. -/
theorem powerIterate_eq_krylov (A : Matrix (Fin n) (Fin n) 𝕜) {q₀ : EuclideanSpace 𝕜 (Fin n)}
    (hq₀ : ‖q₀‖ = 1) (k : ℕ) : powerIterate A q₀ k = Krylov.powerIterate (toEuclideanLin A) q₀ k :=
  Krylov.eq_powerIterate_of_recurrence (toEuclideanLin A) q₀ (y := powerIterate A q₀)
    (by simp [powerIterate, hq₀]) (fun _ => rfl) k

/-- **Equation (5.18)** of [quarteroni2000numerical]. Let $A \in \mathbb{K}^{n \times n}$ and
$q^{(0)} \in \mathbb{K}^n$ with $\|q^{(0)}\|_2 = 1$. Then for every $k$,
$$q^{(k)} = \frac{A^k q^{(0)}}{\|A^k q^{(0)}\|_2}.$$

If $A^k q^{(0)} = 0$, both sides are $0$. The proof specializes the backbone's
`Krylov.powerIterate_eq_smul`. -/
theorem equation_5_18 (A : Matrix (Fin n) (Fin n) 𝕜) {q₀ : EuclideanSpace 𝕜 (Fin n)}
    (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    powerIterate A q₀ k =
      (‖toEuclideanLin (A ^ k) q₀‖ : 𝕜)⁻¹ • toEuclideanLin (A ^ k) q₀ := by
  rw [powerIterate_eq_krylov A hq₀, Krylov.powerIterate_eq_smul, toEuclideanLin_pow]

/-- Let $A \in \mathbb{K}^{n \times n}$ and $q^{(0)} \in \mathbb{K}^n$ with $\|q^{(0)}\|_2 = 1$.
Then for every $k$, $\|A^k q^{(0)}\|_2 \, q^{(k)} = A^k q^{(0)}$. This identity turns the
rescaled iterate $\tilde q^{(k)} = q^{(k)} \|A^k q^{(0)}\|_2 / (\alpha_1 \lambda_1^k)$ of (5.22)
into $A^k q^{(0)} / (\alpha_1 \lambda_1^k)$. -/
theorem norm_smul_powerIterate (A : Matrix (Fin n) (Fin n) 𝕜) {q₀ : EuclideanSpace 𝕜 (Fin n)}
    (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    (‖toEuclideanLin (A ^ k) q₀‖ : 𝕜) • powerIterate A q₀ k = toEuclideanLin (A ^ k) q₀ := by
  rw [equation_5_18 A hq₀, smul_smul]
  rcases eq_or_ne (toEuclideanLin (A ^ k) q₀) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)), one_smul]

/-! ### Theorem 5.6 -/

/-- **Theorem 5.6** of [quarteroni2000numerical], (5.21)–(5.22). Let $A \in \mathbb{C}^{n \times n}$
be diagonalizable, with a basis of unit eigenvectors $x_1, \dots, x_n$ (the columns of $X$) and
eigenvalues ordered as in (5.16):
$$|\lambda_1| > |\lambda_2| \ge |\lambda_i|, \qquad i \neq 1.$$
Let $q^{(0)} \in \mathbb{C}^n$ with $\|q^{(0)}\|_2 = 1$, write $q^{(0)} = \sum_i \alpha_i x_i$
(5.19), and assume $\alpha_1 \neq 0$. Let $\tilde q^{(k)} = q^{(k)} \|A^k q^{(0)}\|_2 /
(\alpha_1 \lambda_1^k)$ be the rescaled iterate of (5.22). Then for every $k$,
$$\|\tilde q^{(k)} - x_1\|_2 \le C \left| \frac{\lambda_2}{\lambda_1} \right|^k, \qquad C =
  \sum_{i \neq 1} \left| \frac{\alpha_i}{\alpha_1} \right|.$$

**Correction.** The book's constant is $C = (\sum_{i \ge 2} (\alpha_i / \alpha_1)^2)^{1/2}$. It
comes from the step $\|\sum_i c_i x_i\|_2 \le (\sum_i c_i^2)^{1/2}$, which needs orthonormal
eigenvectors, that is, a normal $A$. For a diagonalizable $A$, the triangle inequality gives the
constant $C = \sum_{i \neq 1} |\alpha_i / \alpha_1|$, and this is what is proved.

The indices $1$ and $2$ are `i₀` and `i₁`. The proof specializes the backbone's
`Krylov.norm_inv_pow_smul_pow_apply_sub_le_of_eigenbasis`, after
`QuarteroniSaccoSaleri.Chapter05.norm_smul_powerIterate`. -/
theorem theorem_5_6 {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) (hx1 : ∀ i, ‖x i‖ = 1) {i₀ i₁ : Fin n}
    (hgap : ‖lam i₁‖ < ‖lam i₀‖) (hdom : ∀ i, i ≠ i₀ → ‖lam i‖ ≤ ‖lam i₁‖)
    {q₀ : EuclideanSpace ℂ (Fin n)} (hq₀ : ‖q₀‖ = 1) (hα : x.repr q₀ i₀ ≠ 0) (k : ℕ) :
    ‖(x.repr q₀ i₀ * lam i₀ ^ k)⁻¹ •
        ((‖toEuclideanLin (A ^ k) q₀‖ : ℂ) • powerIterate A q₀ k) - x i₀‖ ≤
      (∑ i ∈ univ.erase i₀, ‖x.repr q₀ i / x.repr q₀ i₀‖) * (‖lam i₁‖ / ‖lam i₀‖) ^ k := by
  have hl₀ : lam i₀ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hgap)
  rw [show ((‖toEuclideanLin (A ^ k) q₀‖ : ℝ) : ℂ) • powerIterate A q₀ k =
      toEuclideanLin (A ^ k) q₀ from norm_smul_powerIterate A hq₀ k, toEuclideanLin_pow]
  exact Krylov.norm_inv_pow_smul_pow_apply_sub_le_of_eigenbasis hx hx1 hl₀ hdom hα
    (x.sum_repr q₀).symm k

/-- Let $A \in \mathbb{C}^{n \times n}$ have a basis of eigenvectors $x_i$ with eigenvalues
$\lambda_i$, let $q^{(0)} = \sum_i \alpha_i x_i$, and let $s$ be a set of indices and
$l \in \mathbb{C}$ with $\lambda_i \neq l$ for every $i \notin s$. Then
$\sum_{i \notin s} \alpha_i x_i$ lies in the span of the generalized eigenspaces of $A$ for the
eigenvalues $\mu \neq l$.

This splits $q^{(0)}$ into its $l$-component and the rest, for
`QuarteroniSaccoSaleri.Chapter05.theorem_5_6_rayleigh`,
`QuarteroniSaccoSaleri.Chapter05.inverseIterate_tendsto` and
`QuarteroniSaccoSaleri.Chapter05.powerIterate_of_eq`. -/
theorem sum_repr_erase_mem_iSup_maxGenEigenspace {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) (q₀ : EuclideanSpace ℂ (Fin n))
    (s : Finset (Fin n)) {l : ℂ} (hs : ∀ i ∉ s, lam i ≠ l) :
    ∑ i ∈ univ \ s, x.repr q₀ i • x i ∈
      ⨆ μ, ⨆ _ : μ ≠ l, Module.End.maxGenEigenspace (toEuclideanLin A) μ := by
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ∉ s := (Finset.mem_sdiff.mp hi).2
  exact Submodule.mem_iSup_of_mem (lam i) (Submodule.mem_iSup_of_mem (hs i hi')
    (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr (hx i))))

/-- **Theorem 5.6** of [quarteroni2000numerical], the consequence that the book draws after it. Let
$A \in \mathbb{C}^{n \times n}$ have a basis of eigenvectors $x_1, \dots, x_n$ with eigenvalues
ordered as in (5.16), $|\lambda_1| > |\lambda_2| \ge |\lambda_i|$ for $i \neq 1$. Let
$q^{(0)} = \sum_i \alpha_i x_i$ with $\|q^{(0)}\|_2 = 1$ and $\alpha_1 \neq 0$. Then the
Rayleigh quotients converge to the dominant eigenvalue:
$$\lim_{k \to \infty} \nu^{(k)} = \lambda_1.$$

The eigenvectors need not be unit vectors here. The proof specializes the backbone's
`Krylov.tendsto_inner_powerIterate`, with the splitting $q^{(0)} = \alpha_1 x_1 + \sum_{i \neq
1} \alpha_i x_i$ of the starting vector along the dominant eigenvector and the other generalized
eigenspaces. -/
theorem theorem_5_6_rayleigh {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) {i₀ i₁ : Fin n}
    (hgap : ‖lam i₁‖ < ‖lam i₀‖) (hdom : ∀ i, i ≠ i₀ → ‖lam i‖ ≤ ‖lam i₁‖)
    {q₀ : EuclideanSpace ℂ (Fin n)} (hq₀ : ‖q₀‖ = 1) (hα : x.repr q₀ i₀ ≠ 0) :
    Tendsto (fun k => rayleighQuotient A (powerIterate A q₀ k)) atTop (𝓝 (lam i₀)) := by
  have hl₀ : lam i₀ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hgap)
  have hlt : ∀ i, i ≠ i₀ → ‖lam i‖ < ‖lam i₀‖ := fun i hi => (hdom i hi).trans_lt hgap
  have hne : ∀ i ∉ ({i₀} : Finset (Fin n)), lam i ≠ lam i₀ := fun i hi h =>
    (hlt i (by simpa using hi)).ne (congrArg norm h)
  have hu : toEuclideanLin A (x.repr q₀ i₀ • x i₀) = lam i₀ • (x.repr q₀ i₀ • x i₀) := by
    rw [map_smul, hx, smul_comm]
  simp only [rayleighQuotient, powerIterate_eq_krylov A hq₀]
  refine Krylov.tendsto_inner_powerIterate (LinearMap.continuous_of_finiteDimensional _) hl₀
    hu (smul_ne_zero hα (x.ne_zero i₀))
    (sum_repr_erase_mem_iSup_maxGenEigenspace x hx q₀ {i₀} hne) (fun μ hμ hev => ?_) ?_
  · have hμ' : μ ∈ Set.range lam := by
      rw [← Module.End.spectrum_eq_range_of_basis x hx]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hev
    obtain ⟨i, rfl⟩ := hμ'
    exact hlt i fun h => hμ (h ▸ rfl)
  · conv_lhs => rw [← x.sum_repr q₀]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), Finset.sdiff_singleton_eq_erase]

/-! ### Equation (5.23): the symmetric case -/

/-- **Equation (5.23)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, with orthonormal eigenvectors $x_i$ and eigenvalues $\lambda_i$ ordered as in (5.16),
$|\lambda_1| > |\lambda_2| \ge |\lambda_i|$ for $i \neq 1$. Let $q^{(0)} \in \mathbb{R}^n$ with
$\|q^{(0)}\|_2 = 1$ and $\cos \theta_0 = |x_1^T q^{(0)}| \neq 0$. Then for every $k$,
$$|\lambda_1 - \nu^{(k)}| \le (\lambda_{\max} - \lambda_{\min}) \tan^2 \theta_0 \left|
  \frac{\lambda_2}{\lambda_1} \right|^{2k}.$$
So the convergence of $\nu^{(k)}$ is quadratic in the ratio $|\lambda_2 / \lambda_1|$.

**Correction.** The book prints the factor $|\lambda_1 - \lambda_n|$ for the spread of the
spectrum. Under the ordering (5.16) by modulus this is false:
$A = \operatorname{diag}(3, -2, 1)$ has $|\lambda_1 - \lambda_3| = 2$, while the error constant
is $5$. The statement has $\lambda_{\max} - \lambda_{\min}$.

The eigenvectors and eigenvalues are `LinearMap.IsSymmetric.eigenvectorBasis` and
`LinearMap.IsSymmetric.eigenvalues` of `Matrix.toEuclideanLin A`, and $\lambda_{\max}$ and
$\lambda_{\min}$ are their supremum and infimum. The angle is
$\theta_0 = \arccos |x_1^T q^{(0)}|$. The proof specializes the backbone's
`LinearMap.IsSymmetric.abs_sub_rayleigh_powerIterate_le`, with $\tan^2 \theta_0 = (1 - \cos^2
\theta_0) / \cos^2 \theta_0$. -/
theorem equation_5_23 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {i₀ i₁ : Fin n}
    (hgap : |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₁| <
      |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₀|)
    (hdom : ∀ i, i ≠ i₀ →
      |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i| ≤
        |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₁|)
    {q₀ : EuclideanSpace ℝ (Fin n)} (hq₀ : ‖q₀‖ = 1)
    (hc : inner ℝ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin i₀)
      q₀ ≠ 0) (k : ℕ) :
    |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₀ -
        rayleighQuotient A (powerIterate A q₀ k)| ≤
      ((⨆ i, (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i) -
          ⨅ i, (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i) *
        Real.tan (Real.arccos |inner ℝ
          ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin i₀) q₀|)
          ^ 2 *
        (|(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₁| /
          |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₀|) ^ (2 * k) :=
    by
  set hA' := hA.isSymmetric_toEuclideanLin
  set lam := hA'.eigenvalues finrank_euclideanSpace_fin
  set c := inner ℝ (hA'.eigenvectorBasis finrank_euclideanSpace_fin i₀) q₀
  have hl₀ : lam i₀ ≠ 0 := fun h => by
    rw [h, abs_zero] at hgap
    exact absurd hgap (not_lt.mpr (abs_nonneg _))
  have hab : ∀ i, lam i ∈ Set.Icc (⨅ i, lam i) (⨆ i, lam i) := fun i =>
    ⟨ciInf_le (Set.finite_range _).bddBelow i, le_ciSup (Set.finite_range _).bddAbove i⟩
  have hc1 : |c| ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (hA'.eigenvectorBasis finrank_euclideanSpace_fin i₀) q₀
    rwa [(hA'.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one, hq₀, one_mul,
      Real.norm_eq_abs] at h
  have htan : Real.tan (Real.arccos |c|) ^ 2 = (1 - ‖c‖ ^ 2) / ‖c‖ ^ 2 := by
    rw [Real.tan_arccos, div_pow, Real.sq_sqrt (by nlinarith [abs_nonneg c, sq_abs c]), sq_abs,
      Real.norm_eq_abs, sq_abs]
  have h := hA'.abs_sub_rayleigh_powerIterate_le finrank_euclideanSpace_fin hl₀ hdom hab hq₀ hc k
  rw [htan, rayleighQuotient, powerIterate_eq_krylov A hq₀]
  simpa using h

/-! ### Equation (5.24): the backward error of the iterate -/

/-- **Equation (5.24)** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$ and
$q^{(0)} \in \mathbb{C}^n$ with $\|q^{(0)}\|_2 = 1$, and let $k \in \mathbb{N}$ with
$A^k q^{(0)} \neq 0$, so that $\|q^{(k)}\|_2 = 1$. Let $r^{(k)} = A q^{(k)} - \nu^{(k)} q^{(k)}$
be the residual at step $k$, and let $\varepsilon E^{(k)} = -r^{(k)} (q^{(k)})^H \in
\mathbb{C}^{n \times n}$. Then:

1. $\varepsilon E^{(k)} q^{(k)} = -r^{(k)}$, so $(A + \varepsilon E^{(k)}) q^{(k)} = \nu^{(k)}
   q^{(k)}$: at each step of the power method, $\nu^{(k)}$ is an eigenvalue of the perturbed
   matrix $A + \varepsilon E^{(k)}$;
2. $\|\varepsilon E^{(k)}\|_2 = \|r^{(k)}\|_2$;
3. every $\Delta A \in \mathbb{C}^{n \times n}$ with
   $(A + \Delta A) q^{(k)} = \nu^{(k)} q^{(k)}$ satisfies $\|r^{(k)}\|_2 \le \|\Delta A\|_2$.

The product $\varepsilon E^{(k)}$ is one matrix in the statement, so
$\varepsilon = \|r^{(k)}\|_2$ and $\|E^{(k)}\|_2 = 1$ are read from part 2. The rank-one matrix
$r q^H$ is `Matrix.vecMulVec r (star q)`. The proof specializes the backbone's
`isLeast_eigen_backwardError`. -/
theorem equation_5_24 (A : Matrix (Fin n) (Fin n) ℂ) {q₀ : EuclideanSpace ℂ (Fin n)}
    (hq₀ : ‖q₀‖ = 1) {k : ℕ} (hz : toEuclideanLin (A ^ k) q₀ ≠ 0) :
    let q := powerIterate A q₀ k
    let r := toEuclideanLin A q - rayleighQuotient A q • q
    let εE : Matrix (Fin n) (Fin n) ℂ := -vecMulVec (WithLp.ofLp r) (star (WithLp.ofLp q))
    toEuclideanLin εE q = -r ∧ toEuclideanLin (A + εE) q = rayleighQuotient A q • q ∧
      ‖εE‖ = ‖r‖ ∧
      ∀ ΔA : Matrix (Fin n) (Fin n) ℂ,
        toEuclideanLin (A + ΔA) q = rayleighQuotient A q • q → ‖r‖ ≤ ‖ΔA‖ := by
  intro q r εE
  have hq : ‖q‖ = 1 := by
    change ‖powerIterate A q₀ k‖ = 1
    rw [powerIterate_eq_krylov A hq₀]
    exact Krylov.norm_powerIterate_of_ne_zero _ _ _ (by rwa [← toEuclideanLin_pow])
  have hqq : inner ℂ q q = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hq]; norm_num
  set R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    InnerProductSpace.rankOne ℂ r q with hR
  -- the rank-one matrix `r qᴴ` is the rank-one operator
  have hlin : toEuclideanLin εE =
      -(R : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
    simp only [εE, map_neg]
    congr 1
    rw [hR, ← InnerProductSpace.symm_toEuclideanLin_rankOne r q, LinearEquiv.apply_symm_apply]
  have hrank : toEuclideanCLM (n := Fin n) (𝕜 := ℂ) εE = -R :=
    ContinuousLinearMap.coe_injective (by rw [coe_toEuclideanCLM_eq_toEuclideanLin, hlin]; rfl)
  have hεEq : toEuclideanLin εE q = -r := by
    rw [hlin, LinearMap.neg_apply, ContinuousLinearMap.coe_coe, hR, InnerProductSpace.rankOne_apply,
      hqq, one_smul]
  refine ⟨hεEq, ?_, ?_, fun ΔA hΔ => ?_⟩
  · rw [map_add, LinearMap.add_apply, hεEq]
    simp [r]
  · rw [← l2_opNorm_toEuclideanCLM, hrank, norm_neg, hR, InnerProductSpace.norm_rankOne, hq,
      mul_one]
  · have hleast := (isLeast_eigen_backwardError (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) hq
      (rayleighQuotient A q)).2
    have h := hleast ⟨-toEuclideanCLM (n := Fin n) (𝕜 := ℂ) ΔA, ?_, rfl⟩
    · rwa [norm_neg, l2_opNorm_toEuclideanCLM] at h
    · rw [sub_neg_eq_add, _root_.add_apply]
      rw [map_add, LinearMap.add_apply] at hΔ
      exact hΔ

/-! ### Equation (5.28): inverse iteration -/

/-- **Equation (5.28)** of [quarteroni2000numerical], inverse iteration with shift $\mu$. Let
$A \in \mathbb{K}^{n \times n}$, $\mu \in \mathbb{K}$ and $q^{(0)} \in \mathbb{K}^n$. For
$k = 1, 2, \dots$, the method solves $(A - \mu I) z^{(k)} = q^{(k-1)}$ and sets
$q^{(k)} = z^{(k)} / \|z^{(k)}\|_2$. The approximation of the eigenvalue is the Rayleigh
quotient $\sigma^{(k)} = (q^{(k)})^H A q^{(k)}$ of $A$ itself.

The book takes $\|q^{(0)}\|_2 = 1$. The solution is $z^{(k)} = (A - \mu I)^{-1} q^{(k-1)}$ with
Mathlib's inverse, which is $0$ when $A - \mu I$ is singular. Lean divides by zero to zero. -/
noncomputable def inverseIterate (A : Matrix (Fin n) (Fin n) 𝕜) (μ : 𝕜)
    (q₀ : EuclideanSpace 𝕜 (Fin n)) : ℕ → EuclideanSpace 𝕜 (Fin n)
  | 0 => q₀
  | k + 1 =>
    (‖toEuclideanLin (A - μ • 1)⁻¹ (inverseIterate A μ q₀ k)‖ : 𝕜)⁻¹ •
      toEuclideanLin (A - μ • 1)⁻¹ (inverseIterate A μ q₀ k)

/-- The recursion (5.28) of [quarteroni2000numerical] is the backbone's inverse iteration. Let
$A \in \mathbb{K}^{n \times n}$, $\mu \notin \sigma(A)$, and $q^{(0)} \in \mathbb{K}^n$ with
$\|q^{(0)}\|_2 = 1$. Then for every $k$, the iterate $q^{(k)}$ is `Krylov.inverseIterate
(toEuclideanLin A) μ q₀ k`, the power method for $(A - \mu I)^{-1}$.

The proof specializes the backbone's `Krylov.inverseIterate_eq_powerIterate`. -/
theorem inverseIterate_eq_krylov {A : Matrix (Fin n) (Fin n) 𝕜} {μ : 𝕜} (hμ : μ ∉ spectrum 𝕜 A)
    {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    inverseIterate A μ q₀ k = Krylov.inverseIterate (toEuclideanLin A) μ q₀ k := by
  have hinv := (ringInverse_toEuclideanLin (isUnit_sub_smul_one_of_notMem_spectrum hμ)).2
  rw [map_sub, map_smul, toEuclideanLin_one, ← Module.End.one_eq_id] at hinv
  rw [Krylov.inverseIterate_eq_powerIterate]
  refine Krylov.eq_powerIterate_of_recurrence _ q₀ (y := inverseIterate A μ q₀)
    (by simp [inverseIterate, hq₀]) (fun j => ?_) k
  rw [hinv]
  rfl

/-- **Section 5.3.2** of [quarteroni2000numerical], the convergence of inverse iteration, after
(5.28). Let $A \in \mathbb{C}^{n \times n}$ be diagonalizable, with a basis of unit eigenvectors
$x_i$ and eigenvalues $\lambda_i$, and let $\mu \notin \sigma(A)$. Let $\lambda_m$ be the
eigenvalue closest to $\mu$ in the sense of (5.27),
$$|\lambda_m - \mu| < |\lambda_i - \mu|, \qquad i \neq m,$$
so that $\lambda_m$ is simple. Let $q^{(0)} = \sum_i \alpha_i x_i$ with $\|q^{(0)}\|_2 = 1$ and
$\alpha_m \neq 0$. Then
$$c_k q^{(k)} \to x_m, \qquad c_k = \left( \frac{\lambda_m - \mu}{|\lambda_m - \mu|} \right)^k
  \frac{|\alpha_m|}{\alpha_m},$$
and $\sigma^{(k)} \to \lambda_m$.

The scalars $c_k$ have modulus $1$, so the iterates converge to $x_m$ up to a unimodular factor.
This is the book's $\tilde q^{(k)} \to x_m$. The proof specializes the backbone's
`Krylov.tendsto_smul_inverseIterate` and `Krylov.tendsto_inner_inverseIterate`. -/
theorem inverseIterate_tendsto {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) (hx1 : ∀ i, ‖x i‖ = 1) {μ : ℂ}
    (hμ : μ ∉ spectrum ℂ A) {m : Fin n} (hclose : ∀ i, i ≠ m → ‖lam m - μ‖ < ‖lam i - μ‖)
    {q₀ : EuclideanSpace ℂ (Fin n)} (hq₀ : ‖q₀‖ = 1) (hα : x.repr q₀ m ≠ 0) :
    Tendsto (fun k => (((lam m - μ) / (‖lam m - μ‖ : ℂ)) ^ k * (‖x.repr q₀ m‖ / x.repr q₀ m)) •
        inverseIterate A μ q₀ k) atTop (𝓝 (x m)) ∧
      Tendsto (fun k => rayleighQuotient A (inverseIterate A μ q₀ k)) atTop (𝓝 (lam m)) := by
  have hne : ∀ i ∉ ({m} : Finset (Fin n)), lam i ≠ lam m := fun i hi h =>
    (hclose i (by simpa using hi)).ne (by rw [h])
  have hσ : IsUnit (toEuclideanLin A - μ • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin n)))) := by
    have h := (ringInverse_toEuclideanLin (isUnit_sub_smul_one_of_notMem_spectrum hμ)).1
    rwa [map_sub, map_smul, toEuclideanLin_one, ← Module.End.one_eq_id] at h
  have hdom : ∀ ν, ν ≠ lam m → Module.End.HasEigenvalue (toEuclideanLin A) ν →
      ‖lam m - μ‖ < ‖ν - μ‖ := fun ν hν hev => by
    have hν' : ν ∈ Set.range lam := by
      rw [← Module.End.spectrum_eq_range_of_basis x hx]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hev
    obtain ⟨i, rfl⟩ := hν'
    exact hclose i fun h => hν (h ▸ rfl)
  have hsplit : q₀ = x.repr q₀ m • x m + ∑ i ∈ univ \ {m}, x.repr q₀ i • x i := by
    conv_lhs => rw [← x.sum_repr q₀]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), Finset.sdiff_singleton_eq_erase]
  have hu0 : x.repr q₀ m • x m ≠ 0 := smul_ne_zero hα (x.ne_zero m)
  have hu : toEuclideanLin A (x.repr q₀ m • x m) = lam m • (x.repr q₀ m • x m) := by
    rw [map_smul, hx, smul_comm]
  have hw := sum_repr_erase_mem_iSup_maxGenEigenspace x hx q₀ {m} hne
  simp only [inverseIterate_eq_krylov hμ hq₀, rayleighQuotient]
  refine ⟨?_, Krylov.tendsto_inner_inverseIterate (LinearMap.continuous_of_finiteDimensional _) hσ
    hu hu0 hw hdom hsplit⟩
  have hlim := Krylov.tendsto_smul_inverseIterate hσ hu hu0 hw hdom hsplit
  have hcoe : ∀ r : ℝ, (RCLike.ofReal r : ℂ) = (r : ℂ) := fun r => rfl
  simp only [hcoe] at hlim
  have hαn : (‖x.repr q₀ m‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hα)
  have hval : (‖x.repr q₀ m‖ / x.repr q₀ m : ℂ) • ((‖x.repr q₀ m • x m‖ : ℂ)⁻¹ •
      x.repr q₀ m • x m) = x m := by
    rw [norm_smul, hx1, mul_one, smul_smul, smul_smul]
    rw [show (‖x.repr q₀ m‖ : ℂ) / x.repr q₀ m * (‖x.repr q₀ m‖ : ℂ)⁻¹ * x.repr q₀ m = 1 by
      field_simp, one_smul]
  have h := hlim.const_smul ((‖x.repr q₀ m‖ : ℂ) / x.repr q₀ m)
  rw [hval] at h
  refine h.congr fun k => ?_
  rw [smul_smul, mul_comm]

/-! ### Section 5.3.3: coincident dominant eigenvalues -/

/-- **Section 5.3.3** of [quarteroni2000numerical], case 1: $\lambda_2 = \lambda_1$. Let
$A \in \mathbb{C}^{n \times n}$ have a basis of eigenvectors $x_i$ with eigenvalues $\lambda_i$.
Suppose that the two dominant eigenvalues coincide, $\lambda_2 = \lambda_1 \neq 0$ for two
distinct indices, and that $|\lambda_i| < |\lambda_1|$ for the other indices. Let
$q^{(0)} = \sum_i \alpha_i x_i$ with $\|q^{(0)}\|_2 = 1$ and $\alpha_1 \neq 0$, and let
$u = \alpha_1 x_1 + \alpha_2 x_2$. Then:

1. $u$ lies in the subspace spanned by $x_1$ and $x_2$;
2. there are scalars $c_k$ with $|c_k| = 1$ such that $c_k q^{(k)} \to u / \|u\|_2$;
3. $\nu^{(k)} \to \lambda_1$.

So the power method is still convergent, and the iterates converge, up to a unimodular factor,
to the unit vector in the direction of $u$.

The indices $1$ and $2$ are `i₀` and `i₁`. The proof specializes the backbone's
`Krylov.exists_norm_eq_one_tendsto_smul_powerIterate` and `Krylov.tendsto_inner_powerIterate`,
for which the $\lambda_1$-component $u$ of $q^{(0)}$ is an eigenvector. The backbone does not
assume that $\lambda_1$ is simple. -/
theorem powerIterate_of_eq {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) {i₀ i₁ : Fin n} (hi : i₁ ≠ i₀)
    (heq : lam i₁ = lam i₀) (hdom : ∀ i, i ≠ i₀ → i ≠ i₁ → ‖lam i‖ < ‖lam i₀‖) (hl₀ : lam i₀ ≠ 0)
    {q₀ : EuclideanSpace ℂ (Fin n)} (hq₀ : ‖q₀‖ = 1) (hα : x.repr q₀ i₀ ≠ 0) :
    let u := x.repr q₀ i₀ • x i₀ + x.repr q₀ i₁ • x i₁
    u ∈ Submodule.span ℂ {x i₀, x i₁} ∧
      (∃ c : ℕ → ℂ, (∀ k, ‖c k‖ = 1) ∧
        Tendsto (fun k => c k • powerIterate A q₀ k) atTop (𝓝 ((‖u‖ : ℂ)⁻¹ • u))) ∧
      Tendsto (fun k => rayleighQuotient A (powerIterate A q₀ k)) atTop (𝓝 (lam i₀)) := by
  intro u
  have hu : toEuclideanLin A u = lam i₀ • u := by
    simp only [u, map_add, map_smul, hx, heq, smul_add, smul_comm (lam i₀)]
  have hu0 : u ≠ 0 := fun h => by
    have := congrArg (fun z => x.repr z i₀) h
    simp only [u, map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne' hi, smul_eq_mul, mul_one, mul_zero,
      add_zero, map_zero, Finsupp.zero_apply] at this
    exact hα this
  have hne : ∀ i ∉ ({i₀, i₁} : Finset (Fin n)), lam i ≠ lam i₀ := fun i hi' h => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi'
    exact (hdom i hi'.1 hi'.2).ne (congrArg norm h)
  have hw := sum_repr_erase_mem_iSup_maxGenEigenspace x hx q₀ {i₀, i₁} hne
  have hsplit : q₀ = u + ∑ i ∈ univ \ {i₀, i₁}, x.repr q₀ i • x i := by
    conv_lhs => rw [← x.sum_repr q₀]
    rw [← Finset.sum_sdiff (Finset.subset_univ {i₀, i₁}), Finset.sum_pair hi.symm, add_comm]
  have hdom' : ∀ μ, μ ≠ lam i₀ → Module.End.HasEigenvalue (toEuclideanLin A) μ →
      ‖μ‖ < ‖lam i₀‖ := fun μ hμ hev => by
    have hμ' : μ ∈ Set.range lam := by
      rw [← Module.End.spectrum_eq_range_of_basis x hx]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hev
    obtain ⟨i, rfl⟩ := hμ'
    exact hdom i (fun h => hμ (h ▸ rfl)) (fun h => hμ (h ▸ heq))
  refine ⟨?_, ?_, ?_⟩
  · exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · simp only [powerIterate_eq_krylov A hq₀]
    exact Krylov.exists_norm_eq_one_tendsto_smul_powerIterate hl₀ hu hu0 hw hdom' hsplit
  · simp only [rayleighQuotient, powerIterate_eq_krylov A hq₀]
    exact Krylov.tendsto_inner_powerIterate (LinearMap.continuous_of_finiteDimensional _) hl₀ hu
      hu0 hw hdom' hsplit

end QuarteroniSaccoSaleri.Chapter05
