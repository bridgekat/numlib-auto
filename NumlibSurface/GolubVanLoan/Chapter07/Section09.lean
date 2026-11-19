/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Eigen.Pseudospectrum
import NumlibSurface.GolubVanLoan.Chapter07.Section03

/-!
# Golub and Van Loan, Section 7.9: Pseudospectra

This module formalizes §7.9 of [golub2013matrix]. For $A \in \mathbb{C}^{n \times n}$ and
$\varepsilon \ge 0$, the $\varepsilon$-pseudospectrum is $$\Lambda_\varepsilon(A) = \{z \in
\mathbb{C} : \sigma_{\min}(A - zI) \le \varepsilon\}$$ (7.9.5), and its elements are the
$\varepsilon$-pseudoeigenvalues of $A$. The section starts from the powers of a matrix: $\|A^k\|_2$
behaves like $\rho(A)^k$ for large $k$ (7.9.1), but the example $\begin{bmatrix} \lambda_1 & M \\ 0
& \lambda_2 \end{bmatrix}$ ((7.9.2), (7.9.3)) shows that the powers can grow for a long time before
they decay. It then gives two other forms of $\Lambda_\varepsilon(A)$: the resolvent form
$\|(zI - A)^{-1}\|_2 \ge 1/\varepsilon$ (7.9.6) and the perturbation form $z \in \lambda(A + E)$
with $\|E\|_2 \le \varepsilon$ (7.9.7).

The elementary properties are Theorems 7.9.1–7.9.8 and Corollaries 7.9.3, 7.9.5 and 7.9.7: the
behaviour of $\Lambda_\varepsilon$ under shifts, scalings and similarities, the pseudospectra of
diagonal, normal and block triangular matrices, and a lower bound on the distance of a point from
$\Lambda_\varepsilon(A)$. The module also states the reduction of $\sigma_{\min}(zI - A)$ to a Schur
form (§7.9.5), the pseudospectral abscissa and radius ((7.9.8), (7.9.9)), the matrix (7.9.10) whose
imaginary eigenvalues locate the crossings of a ray with the boundary of $\Lambda_\varepsilon(A)$,
and the lower bound (7.9.11) on transient growth. The proofs specialize the backbone module
`Numlib.Eigen.Pseudospectrum`.

## Main definitions

* (7.9.5), `GolubVanLoan.Chapter07.pseudospectrum`: $\Lambda_\varepsilon(A) = \{z :
  \sigma_{\min}(A - zI) \le \varepsilon\}$.
* (7.9.8), `GolubVanLoan.Chapter07.pseudospectralAbscissa`: $\alpha_\varepsilon(A) =
  \max\{\operatorname{Re} z : z \in \Lambda_\varepsilon(A)\}$.
* (7.9.9), `GolubVanLoan.Chapter07.pseudospectralRadius`: $\rho_\varepsilon(A) = \max\{|z| : z \in
  \Lambda_\varepsilon(A)\}$.
* (7.9.10), `GolubVanLoan.Chapter07.rayCrossingMatrix`: the matrix $\begin{bmatrix} i e^{i\theta}
  A^H & -\varepsilon I \\ \varepsilon I & i e^{-i\theta} A \end{bmatrix}$.

## Main results

* (7.9.1), `GolubVanLoan.Chapter07.equation_7_9_1`: $\|A^k\|_2^{1/k} \to \rho(A)$, and
  $\|A^k\|_2 \le C(\rho(A) + \varepsilon)^k$ for every $\varepsilon > 0$.
* (7.9.2), `GolubVanLoan.Chapter07.equation_7_9_2`: the diagonalization of $\begin{bmatrix}
  \lambda_1 & M \\ 0 & \lambda_2 \end{bmatrix}$ for $\lambda_1 \neq \lambda_2$.
* (7.9.3), `GolubVanLoan.Chapter07.equation_7_9_3`: the powers of $\begin{bmatrix} \lambda_1 & M \\
  0 & \lambda_2 \end{bmatrix}$.
* §7.9.1, `GolubVanLoan.Chapter07.two_by_two_power_bound`: when the powers of the $2 \times 2$
  example tend to $0$, and a bound on their norms.
* §7.9.2–7.9.3, `GolubVanLoan.Chapter07.pseudospectrum_zero`: $\Lambda_0(A) = \lambda(A)$, and
  $\Lambda_\varepsilon(A)$ grows with $\varepsilon$.
* (7.9.6), `GolubVanLoan.Chapter07.equation_7_9_6`: the resolvent form of $\Lambda_\varepsilon(A)$.
* (7.9.7), `GolubVanLoan.Chapter07.equation_7_9_7`: the perturbation form of
  $\Lambda_\varepsilon(A)$.
* §7.9.3, `GolubVanLoan.Chapter07.pseudospectrum_component`: each connected component of
  $\Lambda_\varepsilon(A)$ contains an eigenvalue of $A$.
* Theorem 7.9.1, `GolubVanLoan.Chapter07.theorem_7_9_1`: $\Lambda_{\varepsilon|\beta|}(\alpha I +
  \beta A) = \alpha + \beta \Lambda_\varepsilon(A)$.
* Theorem 7.9.2, `GolubVanLoan.Chapter07.theorem_7_9_2`: $\Lambda_\varepsilon(X^{-1} A X) \subseteq
  \Lambda_{\varepsilon \kappa_2(X)}(A)$.
* Corollary 7.9.3, `GolubVanLoan.Chapter07.corollary_7_9_3`: a unitary similarity preserves
  $\Lambda_\varepsilon$.
* Theorem 7.9.4, `GolubVanLoan.Chapter07.theorem_7_9_4`: the pseudospectrum of a diagonal matrix is
  the union of the closed discs of radius $\varepsilon$ about its diagonal entries.
* Corollary 7.9.5, `GolubVanLoan.Chapter07.corollary_7_9_5`: the same holds for a normal matrix and
  its eigenvalues.
* Theorem 7.9.6, `GolubVanLoan.Chapter07.theorem_7_9_6`: $\Lambda_\varepsilon(T_{11}) \cup
  \Lambda_\varepsilon(T_{22}) \subseteq \Lambda_\varepsilon(T)$ for a block upper triangular $T$.
* Corollary 7.9.7, `GolubVanLoan.Chapter07.corollary_7_9_7`: equality for a block diagonal $T$.
* Theorem 7.9.8, `GolubVanLoan.Chapter07.theorem_7_9_8`: $\operatorname{dist}(z_0,
  \Lambda_\varepsilon(A)) \ge 1/\|(z_0 I - A)^{-1}\|_2 - \varepsilon$.
* §7.9.5, `GolubVanLoan.Chapter07.sigmaMin_schur`: $\sigma_{\min}(zI - A) = \sigma_{\min}(zI - T)$
  for a Schur form $T$ of $A$, and an upper bound from one linear solve.
* (7.9.10), `GolubVanLoan.Chapter07.equation_7_9_10`: the imaginary eigenvalues $ir$ of the matrix
  (7.9.10) are the $r$ for which $\varepsilon$ is a singular value of $A - re^{i\theta} I$.
* §7.9.6, `GolubVanLoan.Chapter07.equation_7_9_10_max`: at the largest such $r$, $\varepsilon =
  \sigma_{\min}(A - re^{i\theta} I)$.
* (7.9.11), `GolubVanLoan.Chapter07.equation_7_9_11`: $\sup_{k \ge 0} \|A^k\|_2 \ge
  (\rho_\varepsilon(A) - 1)/\varepsilon$.

## Conventions

* The matrices are complex. The 2-norm is the operator norm of the scoped instance
  `Matrix.Norms.L2Operator`.
* The least singular value is $\sigma_{\min}(M) = $ `⨅ i, M.colSingularValues i`, the infimum of the
  backbone's column-indexed `Matrix.colSingularValues`.
* `GolubVanLoan.Chapter07.pseudospectrum` is defined for a square matrix over any finite index type:
  the source's $n \times n$, and the block matrices of Theorem 7.9.6 on `Fin p ⊕ Fin q`.

## Implementation notes

* For a nonempty index type, `GolubVanLoan.Chapter07.pseudospectrum` is the backbone's closed
  pseudospectrum `ContinuousLinearMap.closedPseudospectrum` of the Euclidean operator of $A$, the
  set of $z$ with a unit vector $w$ such that $\|Aw - zw\|_2 \le \varepsilon$
  (`GolubVanLoan.Chapter07.pseudospectrum_eq`).
* Lean's matrix inverse is $0$ at a singular matrix. The resolvent norm $\|(zI - A)^{-1}\|_2$ is
  therefore $0$ at an eigenvalue, and the statements that use it name the eigenvalues explicitly.

## Deviations from the source

* **Equation (7.9.5), closed level set** (reading). `GolubVanLoan.Chapter07.pseudospectrum`
  takes the nonstrict inequality. With a positive tolerance the two conventions can differ at
  boundary points, even for the scalar zero matrix.
* **Equation (7.9.7)** (reading). `GolubVanLoan.Chapter07.equation_7_9_7` makes the source’s
  implicit existential perturbation quantifier explicit.
* **Theorem 7.9.2, proof** (typo). The rightmost factor of the resolvent similarity is $X$, not
  the printed $X^{-1}$. See `GolubVanLoan.Chapter07.theorem_7_9_2`.
* **Theorem 7.9.8 and §7.9.5** (reading). `GolubVanLoan.Chapter07.theorem_7_9_8` uses the least
  singular value everywhere and the reciprocal resolvent only off the spectrum.
  `GolubVanLoan.Chapter07.sigmaMin_schur` does not require a triangular transformed matrix for
  the stated identities.
* **Equations (7.9.8)–(7.9.9)** (reading). `GolubVanLoan.Chapter07.pseudospectralAbscissa` and
  `GolubVanLoan.Chapter07.pseudospectralRadius` use real suprema. Attainment is proved for
  nonempty matrices and nonnegative tolerance.
* **Equations (7.9.10)–(7.9.11)** (reading). The ray eigenvalue and singular value
  correspondence is bidirectional for positive tolerance. The transient growth estimate uses
  arbitrary real uniform upper bounds in place of a supremum.
* **(7.9.5)** (typo). The source writes $\lambda$ for $z$ inside the set-builder. See
  `GolubVanLoan.Chapter07.pseudospectrum`.
* **(7.9.6)** (reading). The resolvent form is stated for $\varepsilon > 0$ with
  $\lambda(A) \subseteq \Lambda_\varepsilon(A)$ explicit, since
  $\|(zI - A)^{-1}\|_2 \ge 1/\varepsilon$ has no meaning at an eigenvalue. See
  `GolubVanLoan.Chapter07.equation_7_9_6`.
* **(7.9.1)** (reading). The source says that $A^k$ decays "like $\rho(A)^k$"; the theorem states
  Gelfand's formula and a bound $C(\rho(A) + \varepsilon)^k$. See
  `GolubVanLoan.Chapter07.equation_7_9_1`.
* **(7.9.3)** (generalization). The source derives the formula from (7.9.2) under
  $\lambda_1 \neq \lambda_2$; it holds without this hypothesis. See
  `GolubVanLoan.Chapter07.equation_7_9_3`.
* **§7.9.1, the power bound of the $2 \times 2$ example** (correction). The source states the bound
  for any $\varepsilon > 0$; at $k = 0$ it reads $1 \le M/\varepsilon$, so $\varepsilon \le M$ is
  needed. See `GolubVanLoan.Chapter07.two_by_two_power_bound`.

## Not formalized

* **Display (7.9.4).** It repeats (7.9.1) and illustrates transient growth.
* **The Eigtool plots and the Kahan, Demmel and `Gallery(5)` matrices.**
* **The strategies of §7.9.5 for computing pseudospectra, and the Burke–Lewis–Overton and
  Mengi–Overton algorithms.**
* **The estimate $\sigma_{\min}(zI - T) \approx 1/\|y\|_2$.** It is a heuristic; the rigorous upper
  bound is `GolubVanLoan.Chapter07.sigmaMin_schur`.
-/

open Matrix Filter Topology Metric

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.9.1 Motivation: matrix powers -/

section L2

open scoped Matrix.Norms.L2Operator

/-- **Equation (7.9.1)** of [golub2013matrix], in a rigorous form. Let
$A \in \mathbb{C}^{n \times n}$ and let $\rho(A)$ be its spectral radius. Then $$\lim_{k \to
\infty} \|A^k\|_2^{1/k} = \rho(A)$$ (Gelfand's formula), and for every $\varepsilon > 0$ there
is $C$ such that $\|A^k\|_2 \le C (\rho(A) + \varepsilon)^k$ for all $k \ge 0$.

**Reading.** The source says that if $\rho(A) < 1$ then $A^k \to 0$ and the decay is "like
$\rho(A)^k$". The theorem makes this precise in the two forms above.

The spectral radius is `GolubVanLoan.Chapter07.spectralRadius` of (7.1.1). -/
theorem equation_7_9_1 (A : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop (𝓝 (spectralRadius A)) ∧
      ∀ ε > 0, ∃ C : ℝ, ∀ k : ℕ, ‖A ^ k‖ ≤ C * (spectralRadius A + ε) ^ k := by
  have := FiniteDimensional.complete ℂ (Matrix (Fin n) (Fin n) ℂ)
  have hfin : _root_.spectralRadius ℂ A ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm A)
  have hlim : Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop (𝓝 (spectralRadius A)) := by
    have h := (ENNReal.tendsto_toReal hfin).comp
      (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius A)
    rw [spectralRadius_eq]
    refine h.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [← ENNReal.toReal_rpow, ENNReal.coe_toReal, coe_nnnorm]
  refine ⟨hlim, fun ε hε => ?_⟩
  have hρ0 : 0 ≤ spectralRadius A := by rw [spectralRadius_eq]; exact ENNReal.toReal_nonneg
  have hpos : 0 < spectralRadius A + ε := by linarith
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((hlim.eventually (gt_mem_nhds (by linarith :
    spectralRadius A < spectralRadius A + ε))).and (eventually_ge_atTop 1))
  refine ⟨1 + ∑ k ∈ Finset.range K, ‖A ^ k‖ / (spectralRadius A + ε) ^ k, fun k => ?_⟩
  have hsum : 0 ≤ ∑ k ∈ Finset.range K, ‖A ^ k‖ / (spectralRadius A + ε) ^ k :=
    Finset.sum_nonneg fun _ _ => by positivity
  rcases lt_or_ge k K with hk | hk
  · have hle : ‖A ^ k‖ / (spectralRadius A + ε) ^ k ≤
        1 + ∑ k ∈ Finset.range K, ‖A ^ k‖ / (spectralRadius A + ε) ^ k := by
      have := Finset.single_le_sum (f := fun k => ‖A ^ k‖ / (spectralRadius A + ε) ^ k)
        (fun _ _ => by positivity) (Finset.mem_range.2 hk)
      linarith
    calc ‖A ^ k‖ = ‖A ^ k‖ / (spectralRadius A + ε) ^ k * (spectralRadius A + ε) ^ k := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)
  · obtain ⟨hlt, hk1⟩ := hK k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have h1 : ‖A ^ k‖ ≤ (spectralRadius A + ε) ^ k := by
      have h2 := Real.rpow_le_rpow (by positivity) hlt.le (Nat.cast_nonneg k)
      rwa [← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hk0, Real.rpow_one,
        Real.rpow_natCast] at h2
    calc ‖A ^ k‖ ≤ 1 * (spectralRadius A + ε) ^ k := by rw [one_mul]; exact h1
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end L2

/-- **Equation (7.9.2)** of [golub2013matrix]. Let $\lambda_1, \lambda_2, M \in \mathbb{C}$ with
$\lambda_1 \neq \lambda_2$. Then $$\begin{bmatrix} \lambda_1 & M \\ 0 & \lambda_2
\end{bmatrix} = X \begin{bmatrix} \lambda_1 & 0 \\ 0 & \lambda_2 \end{bmatrix} X^{-1}, \qquad
X = \begin{bmatrix} 1 & M/(\lambda_2 - \lambda_1) \\ 0 & 1 \end{bmatrix}.$$
-/
theorem equation_7_9_2 {l₁ l₂ M : ℂ} (hl : l₁ ≠ l₂) :
    !![l₁, M; 0, l₂] = !![1, M / (l₂ - l₁); 0, 1] * diagonal ![l₁, l₂] *
      (!![1, M / (l₂ - l₁); 0, 1])⁻¹ := by
  have hsub : l₂ - l₁ ≠ 0 := sub_ne_zero.2 hl.symm
  set X : Matrix (Fin 2) (Fin 2) ℂ := !![1, M / (l₂ - l₁); 0, 1] with hX
  have hXd : IsUnit X.det := by
    rw [hX, det_fin_two]
    simp
  have hAX : !![l₁, M; 0, l₂] * X = X * diagonal ![l₁, l₂] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [X, Matrix.mul_apply, Fin.sum_univ_two]
    · simpa [X, Matrix.mul_apply, Fin.sum_univ_two] using
        (show l₁ * (M / (l₂ - l₁)) + M = M / (l₂ - l₁) * l₂ by field_simp; ring)
    · simp [X, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [X, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← hAX, Matrix.mul_assoc, mul_nonsing_inv _ hXd, Matrix.mul_one]

/-- **Equation (7.9.3)** of [golub2013matrix]. Let $\lambda_1, \lambda_2, M \in \mathbb{C}$ and
$k \ge 0$. Then $$\begin{bmatrix} \lambda_1 & M \\ 0 & \lambda_2 \end{bmatrix}^k =
\begin{bmatrix} \lambda_1^k & M \sum_{j=0}^{k-1} \lambda_1^{k-1-j} \lambda_2^j \\ 0 &
\lambda_2^k \end{bmatrix}.$$

**Generalization.** The source derives the formula from (7.9.2), which assumes
$\lambda_1 \neq \lambda_2$. The formula holds without this hypothesis. -/
theorem equation_7_9_3 (l₁ l₂ M : ℂ) (k : ℕ) :
    !![l₁, M; 0, l₂] ^ k =
      !![l₁ ^ k, M * ∑ j ∈ Finset.range k, l₂ ^ j * l₁ ^ (k - 1 - j); 0, l₂ ^ k] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ', ih, Nat.add_sub_cancel, geom_sum₂_succ_eq]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ']
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ']

/-- The strictly upper triangular part of $\begin{bmatrix} \lambda_1 & M \\ 0 & \lambda_2
\end{bmatrix}$ is $\begin{bmatrix} 0 & M \\ 0 & 0 \end{bmatrix}$. -/
private theorem strictUpper_two_by_two (l₁ l₂ M : ℂ) :
    strictUpper !![l₁, M; 0, l₂] = !![0, M; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [strictUpper_apply]

open scoped Matrix.Norms.Frobenius in
/-- For real $M \ge 0$, the Frobenius norm of the strictly upper triangular part of $\begin{bmatrix}
\lambda_1 & M \\ 0 & \lambda_2 \end{bmatrix}$ is $M$. -/
private theorem frobenius_norm_strictUpper_two_by_two (l₁ l₂ : ℂ) {M : ℝ} (hM : 0 ≤ M) :
    ‖strictUpper !![l₁, (M : ℂ); 0, l₂]‖ = M := by
  rw [strictUpper_two_by_two, frobenius_norm_def]
  simp only [of_apply, cons_val', cons_val_fin_one, Real.rpow_ofNat, Fin.sum_univ_two, Fin.isValue,
    cons_val_zero, cons_val_one, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, zero_add, add_zero, one_div]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
  norm_num

section L2

open scoped Matrix.Norms.L2Operator

/-- **§7.9.1** of [golub2013matrix], the powers of a $2 \times 2$ upper triangular matrix. Let
$\lambda_1, \lambda_2 \in \mathbb{C}$, let $M > 0$ be real, and let $A = \begin{bmatrix}
\lambda_1 & M \\ 0 & \lambda_2 \end{bmatrix}$. Then $\|A^k\|_2 \to 0$ as $k \to \infty$ if and
only if $|\lambda_1| < 1$ and $|\lambda_2| < 1$. Moreover, for every $\varepsilon$ with
$0 < \varepsilon \le M$ and every $k \ge 0$, $$\|A^k\|_2 \le \frac{M}{\varepsilon}
\bigl(\max\{|\lambda_1|, |\lambda_2|\} + \varepsilon\bigr)^k,$$ where
$\max\{|\lambda_1|, |\lambda_2|\} = \rho(A)$.

**Correction.** The source states the bound "for any $\varepsilon > 0$". At $k = 0$ the bound
reads $1 \le M/\varepsilon$, so the hypothesis $\varepsilon \le M$ is needed.

The bound is Lemma 7.3.2 with $n = 2$ and $1 + \mu = M/\varepsilon$; the source cites it as
"Lemma 7.3.1". -/
theorem two_by_two_power_bound {l₁ l₂ : ℂ} {M : ℝ} (hM : 0 < M) :
    (Tendsto (fun k : ℕ => ‖!![l₁, (M : ℂ); 0, l₂] ^ k‖) atTop (𝓝 0) ↔
        ‖l₁‖ < 1 ∧ ‖l₂‖ < 1) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ M → ∀ k : ℕ,
        ‖!![l₁, (M : ℂ); 0, l₂] ^ k‖ ≤ M / ε * (max ‖l₁‖ ‖l₂‖ + ε) ^ k := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![l₁, (M : ℂ); 0, l₂] with hA
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ M → ∀ k : ℕ,
      ‖A ^ k‖ ≤ M / ε * (max ‖l₁‖ ‖l₂‖ + ε) ^ k := by
    intro ε hε hεM k
    have hQ : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitaryGroup (Fin 2) ℂ := one_mem _
    have hT : star (1 : Matrix (Fin 2) (Fin 2) ℂ) * A * 1 = A := by simp
    have hTu : A.IsUpperTriangular := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [A]
    have hμ : 0 ≤ M / ε - 1 := by
      rw [sub_nonneg, le_div_iff₀ hε, one_mul]
      exact hεM
    have h := (lemma_7_3_2 hQ hT hTu hμ).1 k
    have hsup : ⨆ i, ‖A i i‖ = max ‖l₁‖ ‖l₂‖ := by
      refine le_antisymm (ciSup_le fun i => ?_) (max_le ?_ ?_)
      · fin_cases i <;> simp [A]
      · exact le_ciSup_of_le (Set.finite_range _).bddAbove 0 (by simp [A])
      · exact le_ciSup_of_le (Set.finite_range _).bddAbove 1 (by simp [A])
    rw [lpOpNorm_two, hsup, frobenius_norm_strictUpper_two_by_two l₁ l₂ hM.le] at h
    have h1 : 1 + (M / ε - 1) = M / ε := by ring
    have h2 : M / (M / ε) = ε := by field_simp
    rwa [h1, h2, show 2 - 1 = 1 from rfl, pow_one] at h
  refine ⟨⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩, hbound⟩
  · have hpow : ∀ k : ℕ, A ^ k = !![l₁ ^ k,
        (M : ℂ) * ∑ j ∈ Finset.range k, l₂ ^ j * l₁ ^ (k - 1 - j); 0, l₂ ^ k] :=
      equation_7_9_3 l₁ l₂ M
    have hlim : ∀ i : Fin 2, Tendsto (fun k : ℕ => ‖(A ^ k) i i‖) atTop (𝓝 0) := fun i =>
      squeeze_zero (fun _ => norm_nonneg _) (fun k => norm_entry_le_l2_opNorm _ i i) h
    have e₁ := hlim 0
    have e₂ := hlim 1
    simp only [hpow, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, norm_pow] at e₁ e₂
    refine ⟨?_, ?_⟩
    · have := tendsto_pow_atTop_nhds_zero_iff.1 e₁
      rwa [abs_norm] at this
    · have := tendsto_pow_atTop_nhds_zero_iff.1 e₂
      rwa [abs_norm] at this
  · set ρ := max ‖l₁‖ ‖l₂‖ with hρ
    have hρ1 : ρ < 1 := max_lt h₁ h₂
    have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
    set ε := min M ((1 - ρ) / 2) with hε
    have hε0 : 0 < ε := lt_min hM (by linarith)
    have hεM : ε ≤ M := min_le_left _ _
    have hlt : ρ + ε < 1 := by
      have : ε ≤ (1 - ρ) / 2 := min_le_right _ _
      linarith
    have hgeo : Tendsto (fun k : ℕ => M / ε * (ρ + ε) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) hlt).const_mul (M / ε)
    exact squeeze_zero (fun _ => norm_nonneg _) (hbound ε hε0 hεM) hgeo

end L2

/-! ### §7.9.2 Definitions -/

section Pseudospectrum

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Equation (7.9.5)** of [golub2013matrix], the $\varepsilon$-pseudospectrum. Let $A$ be a square
complex matrix and $\varepsilon \in \mathbb{R}$. The **$\varepsilon$-pseudospectrum** of $A$ is
$$\Lambda_\varepsilon(A) = \{z \in \mathbb{C} : \sigma_{\min}(A - zI) \le \varepsilon\},$$ and
its elements are the **$\varepsilon$-pseudoeigenvalues** of $A$.

**Typo.** The source writes $\lambda$ for $z$ inside the set-builder.

The least singular value is `⨅ i, (A - z • 1).colSingularValues i`. For an empty index type this
infimum is $0$, so that $\Lambda_\varepsilon(A) = \mathbb{C}$ for $\varepsilon \ge 0$. For a
nonempty index type, $\Lambda_\varepsilon(A)$ is the backbone's closed pseudospectrum of the
Euclidean operator of $A$ (`GolubVanLoan.Chapter07.pseudospectrum_eq`).

**Reading.** The source discusses strict and nonstrict inequalities as interchangeable. They
define different point sets at the boundary: for a $1\times1$ zero matrix and positive
tolerance, the strict version is the open disk and the Lean definition is the closed disk. -/
noncomputable def pseudospectrum (ε : ℝ) (A : Matrix m m ℂ) : Set ℂ :=
  {z | ⨅ i, (A - z • 1).colSingularValues i ≤ ε}

/-- The Euclidean operator of $A - zI$ maps $w$ to the residual $Aw - zw$. -/
private theorem toEuclideanLin_sub_smul (A : Matrix m m ℂ) (z : ℂ) (w : EuclideanSpace ℂ m) :
    toEuclideanLin (A - z • 1) w = toEuclideanCLM (n := m) (𝕜 := ℂ) A w - z • w := by
  rw [map_sub, map_smul, toLpLin_one, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  rfl

/-- The least singular value of $A - zI$ is the least residual $\|Aw - zw\|_2$ over the unit vectors
$w$. -/
private theorem iInf_colSingularValues_sub_smul (A : Matrix m m ℂ) (z : ℂ) :
    ⨅ i, (A - z • 1).colSingularValues i =
      ⨅ w : {w : EuclideanSpace ℂ m // ‖w‖ = 1},
        ‖toEuclideanCLM (n := m) (𝕜 := ℂ) A w - z • (w : EuclideanSpace ℂ m)‖ := by
  rw [iInf_colSingularValues_eq_iInf_norm]
  simp only [toEuclideanLin_sub_smul]

/-- Let $A$ be a square complex matrix over a nonempty index type, and $\varepsilon \in \mathbb{R}$.
The pseudospectrum (7.9.5) is the set of $z \in \mathbb{C}$ for which some unit vector $w$
satisfies $\|Aw - zw\|_2 \le \varepsilon$, because $\sigma_{\min}(A - zI) = \min_{\|w\|_2 = 1}
\|(A - zI) w\|_2$.

The right side is `ContinuousLinearMap.closedPseudospectrum` of `Matrix.toEuclideanCLM A`. -/
theorem pseudospectrum_eq [Nonempty m] (ε : ℝ) (A : Matrix m m ℂ) :
    pseudospectrum ε A = (toEuclideanCLM (n := m) (𝕜 := ℂ) A).closedPseudospectrum ε := by
  ext z
  rw [ContinuousLinearMap.mem_closedPseudospectrum_iff_iInf, ← iInf_colSingularValues_sub_smul]
  rfl

/-- The spectrum of the Euclidean operator of a matrix is the spectrum of the matrix. -/
private theorem spectrum_toEuclideanCLM (A : Matrix m m ℂ) :
    spectrum ℂ (toEuclideanCLM (n := m) (𝕜 := ℂ) A) = spectrum ℂ A :=
  AlgEquiv.spectrum_eq (toEuclideanCLM (n := m) (𝕜 := ℂ)) A

/-- **§7.9.2–7.9.3** of [golub2013matrix]. Let $A$ be a square complex matrix over a nonempty index
type. Then $\Lambda_0(A) = \lambda(A)$, and $\Lambda_{\varepsilon_1}(A) \subseteq
\Lambda_{\varepsilon_2}(A)$ for all real $\varepsilon_1 \le \varepsilon_2$. -/
theorem pseudospectrum_zero [Nonempty m] (A : Matrix m m ℂ) :
    pseudospectrum 0 A = spectrum ℂ A ∧
      ∀ ε₁ ε₂ : ℝ, ε₁ ≤ ε₂ → pseudospectrum ε₁ A ⊆ pseudospectrum ε₂ A := by
  refine ⟨?_, fun ε₁ ε₂ h => ?_⟩
  · rw [pseudospectrum_eq, ContinuousLinearMap.closedPseudospectrum_zero, spectrum_toEuclideanCLM]
  · rw [pseudospectrum_eq, pseudospectrum_eq]
    exact ContinuousLinearMap.closedPseudospectrum_mono h

section L2

open scoped Matrix.Norms.L2Operator

/-- The Euclidean operator of the matrix inverse $M^{-1}$ is the ring inverse of the Euclidean
operator of $M$. -/
private theorem toEuclideanCLM_inv (M : Matrix m m ℂ) :
    toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹ = Ring.inverse (toEuclideanCLM (n := m) (𝕜 := ℂ) M) := by
  by_cases hM : IsUnit M.det
  · have h1 : toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹ * toEuclideanCLM (n := m) (𝕜 := ℂ) M = 1 := by
      rw [← map_mul, nonsing_inv_mul _ hM, map_one]
    have h2 : toEuclideanCLM (n := m) (𝕜 := ℂ) M * toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹ = 1 := by
      rw [← map_mul, mul_nonsing_inv _ hM, map_one]
    have hu : IsUnit (toEuclideanCLM (n := m) (𝕜 := ℂ) M) := ⟨⟨_, _, h2, h1⟩, rfl⟩
    symm
    calc Ring.inverse (toEuclideanCLM (n := m) (𝕜 := ℂ) M)
        = Ring.inverse (toEuclideanCLM (n := m) (𝕜 := ℂ) M) *
            (toEuclideanCLM (n := m) (𝕜 := ℂ) M * toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹) := by
          rw [h2, mul_one]
      _ = toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹ := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  · have hT : ¬ IsUnit (toEuclideanCLM (n := m) (𝕜 := ℂ) M) := fun h => by
      apply hM
      refine isUnit_det_of_right_inverse (B := (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm
        (Ring.inverse (toEuclideanCLM (n := m) (𝕜 := ℂ) M))) ?_
      have h3 := congrArg (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm (Ring.mul_inverse_cancel _ h)
      rwa [map_mul, StarAlgEquiv.symm_apply_apply, map_one] at h3
    rw [nonsing_inv_apply_not_isUnit _ hM, map_zero, Ring.inverse_non_unit _ hT]

/-- **Equation (7.9.6)** of [golub2013matrix], the resolvent form. Let $A$ be a square complex
matrix over a nonempty index type, let $\varepsilon > 0$ and $z \in \mathbb{C}$. Then
$z \in \Lambda_\varepsilon(A)$ if and only if $z \in \lambda(A)$ or $$\|(zI - A)^{-1}\|_2 \ge
\frac{1}{\varepsilon}.$$

**Reading.** The source writes the condition $\|(zI - A)^{-1}\|_2 \ge 1/\varepsilon$ alone. It
has no meaning at an eigenvalue, where Lean's inverse is $0$, so the theorem names the
eigenvalues explicitly and assumes $\varepsilon > 0$. -/
theorem equation_7_9_6 [Nonempty m] {ε : ℝ} (hε : 0 < ε) (A : Matrix m m ℂ) (z : ℂ) :
    z ∈ pseudospectrum ε A ↔ z ∈ spectrum ℂ A ∨ 1 / ε ≤ ‖(z • 1 - A)⁻¹‖ := by
  rw [pseudospectrum_eq, ContinuousLinearMap.mem_closedPseudospectrum_iff_resolvent hε,
    spectrum_toEuclideanCLM, ← l2_opNorm_toEuclideanCLM, toEuclideanCLM_inv, map_sub, map_smul,
    map_one]

/-- **Equation (7.9.7)** of [golub2013matrix]. Let $A$ be a square complex matrix over a nonempty
index type, $\varepsilon \in \mathbb{R}$ and $z \in \mathbb{C}$. Then
$z \in \Lambda_\varepsilon(A)$ if and only if there is a matrix $E$ with
$\|E\|_2 \le \varepsilon$ such that $z$ is an eigenvalue of $A + E$.

**Reading.** The source’s set display leaves the perturbation quantifier implicit. The Lean
theorem explicitly requires the existence of a matrix $E$ satisfying both conditions. -/
theorem equation_7_9_7 [Nonempty m] (ε : ℝ) (A : Matrix m m ℂ) (z : ℂ) :
    z ∈ pseudospectrum ε A ↔ ∃ E : Matrix m m ℂ, ‖E‖ ≤ ε ∧ z ∈ spectrum ℂ (A + E) := by
  rw [pseudospectrum_eq,
    ContinuousLinearMap.mem_closedPseudospectrum_iff_exists_mem_spectrum_add]
  constructor
  · rintro ⟨B, hB, hz⟩
    refine ⟨(toEuclideanCLM (n := m) (𝕜 := ℂ)).symm B, ?_, ?_⟩
    · rwa [← l2_opNorm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply]
    · rwa [← spectrum_toEuclideanCLM, map_add, StarAlgEquiv.apply_symm_apply]
  · rintro ⟨E, hE, hz⟩
    refine ⟨toEuclideanCLM (n := m) (𝕜 := ℂ) E, by rwa [l2_opNorm_toEuclideanCLM], ?_⟩
    rwa [← map_add, spectrum_toEuclideanCLM]

end L2

/-- **§7.9.3** of [golub2013matrix]: "each connected component of $\Lambda_\varepsilon(A)$ contains
at least one eigenvalue of $A$". Let $A$ be a square complex matrix over a nonempty index type
and $\varepsilon \in \mathbb{R}$. For every $z \in \Lambda_\varepsilon(A)$ there is an
eigenvalue $\mu$ of $A$ in the connected component of $\Lambda_\varepsilon(A)$ that contains
$z$. -/
theorem pseudospectrum_component [Nonempty m] {ε : ℝ} (A : Matrix m m ℂ) {z : ℂ}
    (hz : z ∈ pseudospectrum ε A) :
    ∃ μ ∈ spectrum ℂ A, μ ∈ connectedComponentIn (pseudospectrum ε A) z := by
  rw [pseudospectrum_eq] at hz ⊢
  obtain ⟨μ, hμ, hc⟩ := ContinuousLinearMap.exists_mem_spectrum_mem_connectedComponentIn _ hz
  exact ⟨μ, by rwa [spectrum_toEuclideanCLM] at hμ, hc⟩

/-! ### §7.9.4 Some elementary properties -/

/-- **Theorem 7.9.1** of [golub2013matrix]. Let $A$ be a square complex matrix over a nonempty index
type, let $\alpha, \beta \in \mathbb{C}$ and $\varepsilon \ge 0$. Then
$$\Lambda_{\varepsilon|\beta|}(\alpha I + \beta A) = \alpha + \beta \Lambda_\varepsilon(A) =
\{\alpha + \beta z : z \in \Lambda_\varepsilon(A)\}.$$

The theorem includes $\beta = 0$, where both sides are $\{\alpha\}$. In the source's proof, the
first chain ends in $= \Lambda_\varepsilon(A)$ where $\alpha + \Lambda_\varepsilon(A)$ is meant. -/
theorem theorem_7_9_1 [Nonempty m] (A : Matrix m m ℂ) (α β : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    pseudospectrum (ε * ‖β‖) (α • 1 + β • A) = (fun z => α + β * z) '' pseudospectrum ε A := by
  rcases eq_or_ne β 0 with rfl | hβ
  · have hspec : spectrum ℂ (α • (1 : Matrix m m ℂ)) = {α} := by
      rw [← Algebra.algebraMap_eq_smul_one, spectrum.scalar_eq]
    rw [norm_zero, mul_zero, zero_smul, add_zero, (pseudospectrum_zero _).1, hspec]
    have hne : (pseudospectrum ε A).Nonempty := by
      rw [pseudospectrum_eq]
      exact ContinuousLinearMap.closedPseudospectrum_nonempty hε _
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_image, zero_mul, add_zero]
    exact ⟨fun h => ⟨_, hne.some_mem, h.symm⟩, fun ⟨_, _, h⟩ => h.symm⟩
  · rw [pseudospectrum_eq, pseudospectrum_eq, map_add, map_smul, map_smul, map_one]
    exact ContinuousLinearMap.closedPseudospectrum_smul_add α hβ

section L2

open scoped Matrix.Norms.L2Operator

/-- **Theorem 7.9.2** of [golub2013matrix]. Let $A, X$ be square complex matrices over a nonempty
index type, with $X$ nonsingular, and let $\varepsilon \in \mathbb{R}$. Then
$$\Lambda_\varepsilon(X^{-1} A X) \subseteq \Lambda_{\varepsilon \kappa_2(X)}(A),$$ where
$\kappa_2(X) = \|X\|_2 \|X^{-1}\|_2$.

The condition number is `NormedRing.condNumber X` for the operator 2-norm. The source's proof
writes $X^{-1} (zI - A)^{-1} X^{-1}$ where $X^{-1} (zI - A)^{-1} X$ is meant.

**Typo.** The second similarity factor on the right of the resolvent identity in the source
proof is $X$, where it prints $X^{-1}$. -/
theorem theorem_7_9_2 [Nonempty m] {X : Matrix m m ℂ} (hX : IsUnit X) (A : Matrix m m ℂ)
    (ε : ℝ) :
    pseudospectrum ε (X⁻¹ * A * X) ⊆ pseudospectrum (ε * NormedRing.condNumber X) A := by
  rw [pseudospectrum_eq, pseudospectrum_eq]
  exact closedPseudospectrum_conj_subset hX A ε

end L2

/-- **Corollary 7.9.3** of [golub2013matrix]. Let $A, X$ be square complex matrices over a nonempty
index type, with $X$ unitary. Then $\Lambda_\varepsilon(X^{-1} A X) = \Lambda_\varepsilon(A)$
for every $\varepsilon \in \mathbb{R}$. -/
theorem corollary_7_9_3 [Nonempty m] {X : Matrix m m ℂ} (hX : X ∈ unitaryGroup m ℂ)
    (A : Matrix m m ℂ) (ε : ℝ) : pseudospectrum ε (X⁻¹ * A * X) = pseudospectrum ε A := by
  rw [Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 hX), pseudospectrum_eq, pseudospectrum_eq]
  exact closedPseudospectrum_unitary_conj hX A ε

/-- **Theorem 7.9.4** of [golub2013matrix]. Let $d$ be a vector over a nonempty index type and
$\varepsilon \in \mathbb{R}$. Then $$\Lambda_\varepsilon(\operatorname{diag}(d_1, \dots, d_n)) =
\{d_1, \dots, d_n\} + \Delta_\varepsilon = \bigcup_i \{z : |z - d_i| \le \varepsilon\},$$ the
union of the closed discs of radius $\varepsilon$ about the diagonal entries. -/
theorem theorem_7_9_4 [Nonempty m] (d : m → ℂ) (ε : ℝ) :
    pseudospectrum ε (diagonal d) = ⋃ i, closedBall (d i) ε := by
  rw [pseudospectrum_eq]
  exact closedPseudospectrum_diagonal d ε

/-- **Corollary 7.9.5** of [golub2013matrix]. Let $A$ be a normal complex matrix over a nonempty
index type and $\varepsilon \in \mathbb{R}$. Then $$\Lambda_\varepsilon(A) = \lambda(A) +
\Delta_\varepsilon = \bigcup_{\mu \in \lambda(A)} \{z : |z - \mu| \le \varepsilon\}.$$

Normality is `IsStarNormal A`. -/
theorem corollary_7_9_5 [Nonempty m] {A : Matrix m m ℂ} (hA : IsStarNormal A) (ε : ℝ) :
    pseudospectrum ε A = ⋃ μ ∈ spectrum ℂ A, closedBall μ ε := by
  rw [pseudospectrum_eq]
  exact closedPseudospectrum_of_isStarNormal hA ε

/-- **Theorem 7.9.6** of [golub2013matrix]. Let $p, q \ge 1$, let
$T_{11} \in \mathbb{C}^{p \times p}$, $T_{12} \in \mathbb{C}^{p \times q}$ and
$T_{22} \in \mathbb{C}^{q \times q}$, and let $T = \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22}
\end{bmatrix}$. Then for every $\varepsilon \in \mathbb{R}$, $$\Lambda_\varepsilon(T_{11}) \cup
\Lambda_\varepsilon(T_{22}) \subseteq \Lambda_\varepsilon(T).$$

The block matrix is `Matrix.fromBlocks T₁₁ T₁₂ 0 T₂₂`, indexed by `Fin p ⊕ Fin q`. -/
theorem theorem_7_9_6 {p q : ℕ} [NeZero p] [NeZero q] (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (T₁₂ : Matrix (Fin p) (Fin q) ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ) (ε : ℝ) :
    pseudospectrum ε T₁₁ ∪ pseudospectrum ε T₂₂ ⊆ pseudospectrum ε (fromBlocks T₁₁ T₁₂ 0 T₂₂) := by
  rw [pseudospectrum_eq, pseudospectrum_eq, pseudospectrum_eq]
  exact closedPseudospectrum_fromBlocks_zero₂₁_supset T₁₁ T₁₂ T₂₂ ε

/-- **Corollary 7.9.7** of [golub2013matrix]. Let $p, q \ge 1$, $T_{11} \in \mathbb{C}^{p \times p}$
and $T_{22} \in \mathbb{C}^{q \times q}$. Then for every $\varepsilon \in \mathbb{R}$,
$$\Lambda_\varepsilon(\operatorname{diag}(T_{11}, T_{22})) = \Lambda_\varepsilon(T_{11}) \cup
\Lambda_\varepsilon(T_{22}).$$
-/
theorem corollary_7_9_7 {p q : ℕ} [NeZero p] [NeZero q] (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (T₂₂ : Matrix (Fin q) (Fin q) ℂ) (ε : ℝ) :
    pseudospectrum ε (fromBlocks T₁₁ 0 0 T₂₂) = pseudospectrum ε T₁₁ ∪ pseudospectrum ε T₂₂ := by
  rw [pseudospectrum_eq, pseudospectrum_eq, pseudospectrum_eq]
  exact closedPseudospectrum_fromBlocks_diagonal T₁₁ T₂₂ ε

section L2

open scoped Matrix.Norms.L2Operator

/-- **Theorem 7.9.8** of [golub2013matrix]. Let $A$ be a square complex matrix over a nonempty index
type, let $\varepsilon \ge 0$ and $z_0 \in \mathbb{C}$. Then $$\operatorname{dist}(z_0,
\Lambda_\varepsilon(A)) \ge \sigma_{\min}(z_0 I - A) - \varepsilon,$$ and if
$z_0 \notin \lambda(A)$, then $$\operatorname{dist}(z_0, \Lambda_\varepsilon(A)) \ge
\frac{1}{\|(z_0 I - A)^{-1}\|_2} - \varepsilon.$$

The second inequality is the source's statement; it follows from the first, because
$\sigma_{\min}(z_0 I - A) = 1/\|(z_0 I - A)^{-1}\|_2$ when $z_0 \notin \lambda(A)$. The distance
is `Metric.infDist`.

**Reading.** The source gives a reciprocal resolvent expression at $z_0$. Lean makes the
condition $z_0\notin\Lambda(A)$ explicit for that expression and gives the least-singular-value
version for all $z_0$. -/
theorem theorem_7_9_8 [Nonempty m] {ε : ℝ} (hε : 0 ≤ ε) (A : Matrix m m ℂ) (z₀ : ℂ) :
    (⨅ i, (z₀ • 1 - A).colSingularValues i) - ε ≤ infDist z₀ (pseudospectrum ε A) ∧
      (z₀ ∉ spectrum ℂ A → 1 / ‖(z₀ • 1 - A)⁻¹‖ - ε ≤ infDist z₀ (pseudospectrum ε A)) := by
  have hσ : ⨅ i, (z₀ • 1 - A).colSingularValues i = ⨅ i, (A - z₀ • 1).colSingularValues i := by
    rw [iInf_colSingularValues_eq_iInf_norm, iInf_colSingularValues_eq_iInf_norm]
    congr 1
    ext w
    rw [← neg_sub A, map_neg, LinearMap.neg_apply, norm_neg]
  have h1 : (⨅ i, (z₀ • 1 - A).colSingularValues i) - ε ≤ infDist z₀ (pseudospectrum ε A) := by
    rw [hσ, iInf_colSingularValues_sub_smul, pseudospectrum_eq]
    exact ContinuousLinearMap.le_infDist_closedPseudospectrum
      (ContinuousLinearMap.closedPseudospectrum_nonempty hε _) z₀
  refine ⟨h1, fun hz => le_trans ?_ h1⟩
  have hunit : IsUnit (z₀ • (1 : Matrix m m ℂ) - A).det := by
    rw [← isUnit_iff_isUnit_det]
    rwa [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hz
  rw [l2_opNorm_inv_eq_inv_iInf_colSingularValues _ hunit, one_div, inv_inv]

end L2

/-! ### §7.9.5 Computing pseudospectra -/

/-- **§7.9.5** of [golub2013matrix], computing $\sigma_{\min}(zI - A)$ through a Schur form. Let
$n \ge 1$, let $A, Q, T \in \mathbb{C}^{n \times n}$ with $Q$ unitary and $Q^H A Q = T$, and let
$z \in \mathbb{C}$. Then $\sigma_{\min}(zI - A) = \sigma_{\min}(zI - T)$. Moreover, if
$d, y \in \mathbb{C}^n$ satisfy $\|d\|_2 = 1$ and $(zI - T) y = d$, then $$\sigma_{\min}(zI - T)
\le \frac{1}{\|y\|_2}.$$

**Generalization.** Triangularity of $T$ enables the source’s contemplated computation, while
these identities and the upper estimate need only unitary similarity and the indicated solve. -/
theorem sigmaMin_schur [NeZero n] {A Q T : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hT : star Q * A * Q = T) (z : ℂ) :
    ⨅ i, (z • 1 - A).colSingularValues i = ⨅ i, (z • 1 - T).colSingularValues i ∧
      ∀ d y : EuclideanSpace ℂ (Fin n), ‖d‖ = 1 → toEuclideanLin (z • 1 - T) y = d →
        ⨅ i, (z • 1 - T).colSingularValues i ≤ 1 / ‖y‖ := by
  refine ⟨?_, fun d y hd hy => ?_⟩
  · have h : z • 1 - T = star Q * (z • 1 - A) * Q := by
      rw [← hT, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        mem_unitaryGroup_iff'.1 hQ]
    rw [h, iInf_colSingularValues_unitary_mul_mul _ (Unitary.star_mem hQ) hQ]
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [map_zero] at hy
      rw [← hy, norm_zero] at hd
      exact absurd hd zero_ne_one
    · have h := (z • 1 - T).iInf_colSingularValues_mul_norm_le y
      rw [hy, hd] at h
      rw [le_div_iff₀ (norm_pos_iff.2 hy0)]
      exact h

/-! ### §7.9.6 Computing the $\varepsilon$-pseudospectral abscissa and radius -/

/-- **Equation (7.9.8)** of [golub2013matrix], the pseudospectral abscissa. For a square complex
matrix $A$ and $\varepsilon \in \mathbb{R}$, the **$\varepsilon$-pseudospectral abscissa** is
$$\alpha_\varepsilon(A) = \sup\{\operatorname{Re} z : z \in \Lambda_\varepsilon(A)\}.$$

The supremum is the real `sSup`, which is $0$ for an empty or an unbounded set. For a nonempty
index type and $\varepsilon \ge 0$ the supremum is a maximum, and the definition agrees with the
backbone's `Matrix.pseudospectralAbscissa`
(`GolubVanLoan.Chapter07.pseudospectralAbscissa_spec`).

**Reading.** The source uses a maximum. Lean uses a real supremum, and
`GolubVanLoan.Chapter07.pseudospectralAbscissa_spec` gives attainment for nonempty matrices and
nonnegative tolerance. -/
noncomputable def pseudospectralAbscissa (ε : ℝ) (A : Matrix m m ℂ) : ℝ :=
  sSup (Complex.re '' pseudospectrum ε A)

/-- **Equation (7.9.9)** of [golub2013matrix], the pseudospectral radius. For a square complex
matrix $A$ and $\varepsilon \in \mathbb{R}$, the **$\varepsilon$-pseudospectral radius** is
$$\rho_\varepsilon(A) = \sup\{|z| : z \in \Lambda_\varepsilon(A)\}.$$

The supremum is the real `sSup`, which is $0$ for an empty or an unbounded set. For a nonempty
index type and $\varepsilon \ge 0$ the supremum is a maximum, and the definition agrees with the
backbone's `Matrix.pseudospectralRadius` (`GolubVanLoan.Chapter07.pseudospectralAbscissa_spec`).

**Reading.** The source uses a maximum. Lean uses a real supremum, with attainment under the
hypotheses of `GolubVanLoan.Chapter07.pseudospectralAbscissa_spec`. -/
noncomputable def pseudospectralRadius (ε : ℝ) (A : Matrix m m ℂ) : ℝ :=
  sSup ((‖·‖) '' pseudospectrum ε A)

/-- Let $A$ be a square complex matrix over a nonempty index type and $\varepsilon \ge 0$. The
pseudospectral abscissa (7.9.8) and radius (7.9.9) equal the backbone's
`Matrix.pseudospectralAbscissa` and `Matrix.pseudospectralRadius`, and both suprema are
attained: there are $z, z' \in \Lambda_\varepsilon(A)$ with
$\operatorname{Re} z = \alpha_\varepsilon(A)$ and $|z'| = \rho_\varepsilon(A)$. -/
theorem pseudospectralAbscissa_spec [Nonempty m] {ε : ℝ} (hε : 0 ≤ ε) (A : Matrix m m ℂ) :
    pseudospectralAbscissa ε A = Matrix.pseudospectralAbscissa ε A ∧
      pseudospectralRadius ε A = Matrix.pseudospectralRadius ε A ∧
      (∃ z ∈ pseudospectrum ε A, z.re = pseudospectralAbscissa ε A) ∧
      ∃ z ∈ pseudospectrum ε A, ‖z‖ = pseudospectralRadius ε A := by
  have ha : pseudospectralAbscissa ε A = Matrix.pseudospectralAbscissa ε A := by
    rw [pseudospectralAbscissa, pseudospectrum_eq]
    rfl
  have hr : pseudospectralRadius ε A = Matrix.pseudospectralRadius ε A := by
    rw [pseudospectralRadius, pseudospectrum_eq]
    rfl
  obtain ⟨h1, h2⟩ := Matrix.exists_eq_pseudospectralAbscissa_radius hε A
  rw [ha, hr, pseudospectrum_eq]
  exact ⟨rfl, rfl, h1, h2⟩

/-- **Equation (7.9.10)** of [golub2013matrix], the matrix of §7.9.6. For a square complex matrix
$A$ and $\theta, \varepsilon \in \mathbb{R}$, $$M = \begin{bmatrix} i e^{i\theta} A^H &
-\varepsilon I \\ \varepsilon I & i e^{-i\theta} A \end{bmatrix}.$$ Its purely imaginary
eigenvalues $ir$ locate the points $re^{i\theta}$ on the ray of angle $\theta$ at which
$\varepsilon$ is a singular value of $A - re^{i\theta} I$
(`GolubVanLoan.Chapter07.equation_7_9_10`). The source attributes the method to Byers and to
Mengi and Overton. -/
noncomputable def rayCrossingMatrix (θ ε : ℝ) (A : Matrix m m ℂ) : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  fromBlocks ((Complex.I * Complex.exp (θ * Complex.I)) • Aᴴ) (-(ε : ℂ) • 1) ((ε : ℂ) • 1)
    ((Complex.I * Complex.exp (-(θ * Complex.I))) • A)

/-- $e^{i\theta} e^{-i\theta} = 1$ for real $\theta$. -/
private theorem exp_mul_exp_neg_mul_I (θ : ℝ) :
    Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- $(i e^{i\theta}) \cdot (-i e^{-i\theta}) = 1$ for real $\theta$. -/
private theorem I_exp_mul_neg_I_exp (θ : ℝ) :
    Complex.I * Complex.exp (θ * Complex.I) * -(Complex.I * Complex.exp (-(θ * Complex.I))) =
      1 := by
  linear_combination (-Complex.I ^ 2) * exp_mul_exp_neg_mul_I θ - Complex.I_sq

omit [Fintype m] in
/-- $(A - re^{i\theta} I)^H = A^H - re^{-i\theta} I$ for real $r$ and $\theta$. -/
private theorem conjTranspose_sub_ray (θ r : ℝ) (A : Matrix m m ℂ) :
    (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)ᴴ =
      Aᴴ - ((r : ℂ) * Complex.exp (-(θ * Complex.I))) • 1 := by
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, Complex.star_def, map_mul,
    Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    mul_neg]

/-- The eigenvalue equation $M \begin{bmatrix} f \\ g \end{bmatrix} = ir \begin{bmatrix} f \\ g
\end{bmatrix}$ for the matrix (7.9.10) holds if and only if
$i e^{i\theta} B^H f = \varepsilon g$ and $\varepsilon f = -i e^{-i\theta} B g$, where
$B = A - re^{i\theta} I$. -/
private theorem rayCrossingMatrix_mulVec_eq_iff (θ r ε : ℝ) (A : Matrix m m ℂ) (f g : m → ℂ) :
    rayCrossingMatrix θ ε A *ᵥ Sum.elim f g = (Complex.I * r) • Sum.elim f g ↔
      (Complex.I * Complex.exp (θ * Complex.I)) •
          ((A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)ᴴ *ᵥ f) = (ε : ℂ) • g ∧
        (ε : ℂ) • f = -(Complex.I * Complex.exp (-(θ * Complex.I))) •
          ((A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1) *ᵥ g) := by
  have hcc := exp_mul_exp_neg_mul_I θ
  rw [conjTranspose_sub_ray, rayCrossingMatrix, fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  generalize Complex.exp (θ * Complex.I) = c at hcc ⊢
  generalize Complex.exp (-(θ * Complex.I)) = c' at hcc ⊢
  have hs : (Complex.I * r) • Sum.elim f g =
      Sum.elim ((Complex.I * r) • f) ((Complex.I * r) • g) := by
    ext (i | i) <;> rfl
  rw [hs]
  simp only [smul_mulVec, one_mulVec, sub_mulVec]
  constructor
  · intro h
    have h1 := funext fun i => congrFun h (Sum.inl i)
    have h2 := funext fun i => congrFun h (Sum.inr i)
    simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2
    exact ⟨by linear_combination (norm := module) h1 - (Complex.I * r * hcc) • f,
      by linear_combination (norm := module) h2 - (Complex.I * r * hcc) • g⟩
  · rintro ⟨h1, h2⟩
    have e1 : (Complex.I * c) • (Aᴴ *ᵥ f) + (-(ε : ℂ)) • g = (Complex.I * r) • f := by
      linear_combination (norm := module) h1 + (Complex.I * r * hcc) • f
    have e2 : (ε : ℂ) • f + (Complex.I * c') • (A *ᵥ g) = (Complex.I * r) • g := by
      linear_combination (norm := module) h2 + (Complex.I * r * hcc) • g
    rw [e1, e2]

/-- **Equation (7.9.10)** of [golub2013matrix], the singular value property. Let $A$ be a square
complex matrix, let $\theta, r, \varepsilon \in \mathbb{R}$, let $M$ be the matrix (7.9.10), and
let $B = A - re^{i\theta} I$. The following hold.

1. If $M \begin{bmatrix} f \\ g \end{bmatrix} = ir \begin{bmatrix} f \\ g \end{bmatrix}$, then
   $B^H B g = \varepsilon^2 g$.
2. If $\varepsilon > 0$, then $ir$ is an eigenvalue of $M$ if and only if $\varepsilon$ is a
   singular value of $B$.

The source states: "if $i \cdot r$ is an eigenvalue of the matrix $M$, then $\varepsilon$ is a
singular value of $A - re^{i\theta} I$. To see this, observe that if
$M [f; g] = i \cdot r [f; g]$, then $(A - re^{i\theta} I)^H (A - re^{i\theta} I) g =
\varepsilon^2 g$". For $\varepsilon > 0$, $g = 0$ forces $f = 0$, so the eigenvector gives a
singular vector; the converse is built from a singular pair. The eigenvalue condition is the
existence of $v \neq 0$ with $Mv = irv$, and "$\varepsilon$ is a singular value of $B$" is
$\varepsilon = $ `B.colSingularValues i` for some `i`.

**Reading.** The source shows the implication from a crossing eigenvalue to a singular value.
Lean gives the two-way statement for positive tolerance and keeps the squared Gram identity for
every real tolerance. -/
theorem equation_7_9_10 (θ r ε : ℝ) (A : Matrix m m ℂ) :
    (∀ f g : m → ℂ, rayCrossingMatrix θ ε A *ᵥ Sum.elim f g = (Complex.I * r) • Sum.elim f g →
      ((A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)ᴴ *
          (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)) *ᵥ g = ((ε : ℂ) ^ 2) • g) ∧
      (0 < ε → ((∃ v : m ⊕ m → ℂ, v ≠ 0 ∧
          rayCrossingMatrix θ ε A *ᵥ v = (Complex.I * r) • v) ↔
        ∃ i, (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1).colSingularValues i = ε)) := by
  have hdd := I_exp_mul_neg_I_exp θ
  have hgram : ∀ f g : m → ℂ,
      rayCrossingMatrix θ ε A *ᵥ Sum.elim f g = (Complex.I * r) • Sum.elim f g →
      ((A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)ᴴ *
          (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)) *ᵥ g = ((ε : ℂ) ^ 2) • g := by
    intro f g h
    obtain ⟨h1, h2⟩ := (rayCrossingMatrix_mulVec_eq_iff θ r ε A f g).1 h
    rw [← mulVec_mulVec]
    generalize A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1 = B at h1 h2 ⊢
    have h3 := congrArg (Bᴴ *ᵥ ·) h2
    simp only [mulVec_smul] at h3
    linear_combination (norm := module) (ε : ℂ) • h1 - (Complex.I * Complex.exp (θ * Complex.I)) •
      h3 - hdd • (Bᴴ *ᵥ (B *ᵥ g))
  refine ⟨hgram, fun hε => ⟨?_, ?_⟩⟩
  · rintro ⟨v, hv0, hv⟩
    rw [← Sum.elim_comp_inl_inr v] at hv hv0
    have hg : v ∘ Sum.inr ≠ 0 := by
      intro hg
      obtain ⟨-, h2⟩ := (rayCrossingMatrix_mulVec_eq_iff θ r ε A _ _).1 hv
      rw [hg, mulVec_zero, smul_zero, smul_eq_zero] at h2
      refine hv0 ?_
      rw [hg, h2.resolve_left (by exact_mod_cast hε.ne')]
      ext (i | i) <;> rfl
    exact Matrix.exists_colSingularValues_eq_of_mulVec _ hg hε.le (hgram _ _ hv)
  · rintro ⟨i, hi⟩
    set B := A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1 with hB
    obtain ⟨g, hg0, hgB⟩ : ∃ g : m → ℂ, g ≠ 0 ∧ Bᴴ *ᵥ (B *ᵥ g) = ((ε : ℂ) ^ 2) • g := by
      have h := (isHermitian_conjTranspose_mul_self B).mulVec_eigenvectorBasis i
      have he : (isHermitian_conjTranspose_mul_self B).eigenvalues i = ε ^ 2 := by
        rw [← sq_colSingularValues, hi]
      rw [he, ← mulVec_mulVec, ← Complex.coe_smul] at h
      refine ⟨_, fun h0 =>
        (isHermitian_conjTranspose_mul_self B).eigenvectorBasis.orthonormal.ne_zero i
          (by ext j; simpa using congrFun h0 j), ?_⟩
      rw [h]
      push_cast
      rfl
    have hεinv : (ε : ℂ) * (ε : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hε.ne')
    set d := Complex.I * Complex.exp (θ * Complex.I) with hd
    set d' := -(Complex.I * Complex.exp (-(θ * Complex.I))) with hd'
    refine ⟨Sum.elim (((ε : ℂ)⁻¹ * d') • (B *ᵥ g)) g, fun h0 => hg0 (funext fun j => by
      simpa using congrFun h0 (Sum.inr j)), ?_⟩
    refine (rayCrossingMatrix_mulVec_eq_iff θ r ε A _ _).2 ⟨?_, ?_⟩
    · rw [← hB, mulVec_smul, ← hd]
      linear_combination (norm := module) (d * (ε : ℂ)⁻¹ * d') • hgB +
        ((ε : ℂ) * (d * d') * hεinv) • g + ((ε : ℂ) * hdd) • g
    · rw [← hB, ← hd']
      linear_combination (norm := module) (d' * hεinv) • (B *ᵥ g)

open scoped Matrix.Norms.L2Operator in
/-- **§7.9.6** of [golub2013matrix], the largest crossing. Let $A$ be a square complex matrix, let
$\theta \in \mathbb{R}$ and $\varepsilon > 0$, and let $M$ be the matrix (7.9.10). Suppose that
$ir_{\max}$ is an eigenvalue of $M$ and that no $ir$ with $r > r_{\max}$ is an eigenvalue of
$M$. Then $$\sigma_{\min}(A - r_{\max} e^{i\theta} I) = \varepsilon.$$ Therefore
$r_{\max} e^{i\theta}$ is the farthest point of the ray $\{re^{i\theta}\}$ on the boundary of
$\Lambda_\varepsilon(A)$.

The source states this with "It can be shown that". The inequality $\le$ follows from (7.9.10).
If it were strict, the continuous function $r \mapsto \sigma_{\min}(A - re^{i\theta} I)$, which
grows like $|r|$, would take the value $\varepsilon$ at some $r > r_{\max}$ by the intermediate
value theorem, and $ir$ would be an eigenvalue of $M$ by the converse in (7.9.10). -/
theorem equation_7_9_10_max {θ ε rmax : ℝ} (hε : 0 < ε) {A : Matrix m m ℂ}
    (hmax : ∃ v : m ⊕ m → ℂ, v ≠ 0 ∧ rayCrossingMatrix θ ε A *ᵥ v = (Complex.I * rmax) • v)
    (hnot : ∀ r : ℝ, rmax < r → ∀ v : m ⊕ m → ℂ,
      rayCrossingMatrix θ ε A *ᵥ v = (Complex.I * r) • v → v = 0) :
    ⨅ i, (A - ((rmax : ℂ) * Complex.exp (θ * Complex.I)) • 1).colSingularValues i = ε := by
  set s : ℝ → ℝ := fun r =>
    ⨅ i, (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1).colSingularValues i with hs
  obtain ⟨i₀, hi₀⟩ := ((equation_7_9_10 θ rmax ε A).2 hε).1 hmax
  have : Nonempty m := ⟨i₀⟩
  have hle : s rmax ≤ ε := hi₀ ▸ ciInf_le (Set.finite_range _).bddBelow i₀
  change s rmax = ε
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hcont : Continuous s := by
    have hlip : ∀ r r' : ℝ, dist (s r) (s r') ≤ (‖(1 : Matrix m m ℂ)‖₊ : ℝ) * dist r r' := by
      intro r r'
      rw [Real.dist_eq, Real.dist_eq, coe_nnnorm]
      refine (abs_iInf_colSingularValues_sub_le _ _).trans (le_of_eq ?_)
      have e : A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1 -
          (A - ((r' : ℂ) * Complex.exp (θ * Complex.I)) • 1) =
          (((r' - r : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) • 1 := by
        push_cast
        module
      rw [e, norm_smul, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
        Real.norm_eq_abs, abs_sub_comm]
      ring
    exact (LipschitzWith.of_dist_le_mul hlip).continuous
  have hgrow : ∀ r : ℝ, |r| - ‖A‖ ≤ s r := by
    intro r
    simp only [hs]
    rw [iInf_colSingularValues_eq_iInf_norm]
    have : Nonempty {x : EuclideanSpace ℂ m // ‖x‖ = 1} :=
      ⟨⟨EuclideanSpace.single i₀ 1, by simp⟩⟩
    refine le_ciInf fun x => ?_
    rw [toEuclideanLin_sub_smul]
    have h1 := norm_sub_norm_le (((r : ℂ) * Complex.exp (θ * Complex.I)) • (x : EuclideanSpace ℂ m))
      (toEuclideanCLM (n := m) (𝕜 := ℂ) A x)
    have h2 : ‖toEuclideanCLM (n := m) (𝕜 := ℂ) A x‖ ≤ ‖A‖ := by
      have := (toEuclideanCLM (n := m) (𝕜 := ℂ) A).le_opNorm x
      rwa [x.2, mul_one, l2_opNorm_toEuclideanCLM] at this
    rw [norm_smul, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, x.2,
      Real.norm_eq_abs, mul_one, mul_one, norm_sub_rev] at h1
    linarith
  set R := |rmax| + ‖A‖ + ε + 1 with hR
  have hRmax : rmax < R := by
    have := le_abs_self rmax
    have := norm_nonneg A
    linarith
  have hsR : ε ≤ s R := by
    have h := hgrow R
    rw [abs_of_pos (by have := abs_nonneg rmax; have := norm_nonneg A; linarith : 0 < R)] at h
    have := abs_nonneg rmax
    linarith
  obtain ⟨r, ⟨hr1, -⟩, hr⟩ :=
    intermediate_value_Icc hRmax.le hcont.continuousOn ⟨hlt.le, hsR⟩
  have hrr : rmax < r := lt_of_le_of_ne hr1 fun h => by rw [← h] at hr; linarith
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
    (f := fun i => (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1).colSingularValues i)
  obtain ⟨v, hv0, hv⟩ := ((equation_7_9_10 θ r ε A).2 hε).2 ⟨i, hi.trans hr⟩
  exact hv0 (hnot r hrr v hv)

section L2

open scoped Matrix.Norms.L2Operator

/-- **Equation (7.9.11)** of [golub2013matrix], transient growth. Let $A$ be a square complex matrix
over a nonempty index type and $\varepsilon > 0$. Then $$\sup_{k \ge 0} \|A^k\|_2 \ge
\frac{\rho_\varepsilon(A) - 1}{\varepsilon}.$$

The source takes the bound from Trefethen and Embree, pp. 160–161. The supremum is stated
through its upper bounds: if $\|A^k\|_2 \le M$ for all $k \ge 0$, then
$(\rho_\varepsilon(A) - 1)/\varepsilon \le M$.

**Reading.** The source writes the supremum of all power norms. Lean gives the bound for any
real uniform upper bound, also covering the case where the powers are unbounded through the
absence of such a bound. -/
theorem equation_7_9_11 [Nonempty m] {ε : ℝ} (hε : 0 < ε) (A : Matrix m m ℂ) {M : ℝ}
    (hM : ∀ k : ℕ, ‖A ^ k‖ ≤ M) : (pseudospectralRadius ε A - 1) / ε ≤ M := by
  rw [(pseudospectralAbscissa_spec hε.le A).2.1]
  exact Matrix.pseudospectralRadius_sub_one_div_le_norm_pow hε A hM

end L2

end Pseudospectrum

end GolubVanLoan.Chapter07
