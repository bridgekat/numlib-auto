/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The least curvature of a bilinear form

Let $E$ be a real normed space and let $A$ be a continuous bilinear form on $E$, typically a second
derivative $\nabla^2 f(x)$. Its **least curvature** is the infimum of the quadratic form on the unit
sphere,
$$\lambda_{\min}[A] = \inf_{\|d\| = 1} A[d, d],$$
and it satisfies the Rayleigh bound $\lambda_{\min}[A] \|d\|^2 \le A[d, d]$ for every $d$, which is
(A.3) of [cartis2022evaluation]. On a nonzero finite-dimensional inner product space, for a
symmetric form $A[v, w] = \langle v, T w \rangle$, the number $\lambda_{\min}[A]$ is the leftmost
eigenvalue of the symmetric operator $T$, as in Section A.5 of [cartis2022evaluation], and it is
attained at a unit eigenvector.

In infinite dimension, $\lambda_{\min}[A]$ is only the infimum of the quadratic form on the unit
sphere, and it need not be an eigenvalue. On the zero space the unit sphere is empty and
$\lambda_{\min}[A] = 0$; the characterizations that need a unit vector assume that $E$ is nonzero.

## Main definitions

* `minCurvature`: the least curvature $\lambda_{\min}[A] = \inf_{\|d\| = 1} A[d, d]$.
* `minCurvatureOn`: the least curvature of $A$ restricted to a subspace $V$, which is
  $\lambda_{\min}[Q^T A Q]$ for a matrix $Q$ with orthonormal columns that span $V$ ((3.4.32) of
  [cartis2022evaluation]).
* `innerForm`: the inner product $(v, w) \mapsto \langle v, w \rangle$ as a bilinear form, the
  identity matrix $I$ of [cartis2022evaluation].

## Main results

* `minCurvature_le_apply`, `minCurvature_mul_norm_sq_le`: the Rayleigh bound (A.3) of
  [cartis2022evaluation].
* `le_minCurvature_iff`: on a nonzero space, $c \le \lambda_{\min}[A]$ if and only if
  $c \|d\|^2 \le A[d, d]$ for all $d$. So $-\varepsilon \le \lambda_{\min}[A]$ is the approximate
  second-order condition (3.2.6) of [cartis2022evaluation].
* `abs_minCurvature_le_norm`, `abs_minCurvature_sub_le`: $|\lambda_{\min}[A]| \le \|A\|$ and
  $|\lambda_{\min}[A] - \lambda_{\min}[B]| \le \|A - B\|$, the bounds (A.4) and (A.5) of
  [cartis2022evaluation].
* `minCurvature_add_smul_inner`: $\lambda_{\min}[A + \lambda I] = \lambda_{\min}[A] + \lambda$,
  which is (3.4.33) of [cartis2022evaluation].
* `minCurvature_ge_of_add_smul`: $\lambda_{\min}[A] \ge \lambda_{\min}[T + c N] - \|A - T\| - c K$
  when $N[d, d] \le K \|d\|^2$; this is the step in the bounds (4.1.27) and (5.5.15) of
  [cartis2022evaluation].
* `exists_eq_minCurvature`, `apply_eq_minCurvature_mul_inner`, `exists_eigenvector_minCurvature`: in
  finite dimension $\lambda_{\min}[A]$ is attained at a unit vector $u$; for a symmetric form $u$ is
  an eigenvector, and it can be chosen with $\langle u, g \rangle \le 0$ for a given $g$, as in
  (3.2.3) of [cartis2022evaluation].
* `minCurvature_eq_iInf_eigenvalues`, `hasEigenvalue_minCurvature`,
  `minCurvature_le_of_hasEigenvalue`: for $A[v, w] = \langle v, T w \rangle$ with $T$ symmetric,
  $\lambda_{\min}[A]$ is the least eigenvalue of $T$.
* `minCurvature_eq_iInf_rayleigh`: $\lambda_{\min}[A]$ is the least Rayleigh quotient of $H$ when
  $A[v, w] = \langle v, H w \rangle$.
* `minCurvature_eq_iInf_isHermitian_eigenvalues`: $\lambda_{\min}[A]$ is the least eigenvalue of a
  real symmetric matrix $M$ when $A[v, w] = \langle v, M w \rangle$.

## Notation

* $A[v, w]$: the value `A ![v, w]` of the bilinear form `A : ContinuousMultilinearMap ℝ (fun _ : Fin
  2 => E) ℝ`.
* $A[d, d]$: the diagonal value `A (fun _ => d)`.
* $\lambda_{\min}[A]$: `minCurvature A`.

## Implementation notes

* A bilinear form is a continuous multilinear map on `Fin 2`, the type of `iteratedFDeriv ℝ 2 f x`.
  The norm $\|A\|$ is its operator norm.
* The relation to the leftmost eigenvalue `Subproblem.leftmost` of the trust-region subproblem
  theory is in the module `Numlib.Optimization.Subproblem.MinCurvature`.
-/

open Metric Set
open scoped RealInnerProductSpace

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **least curvature** of a continuous bilinear form $A$ on $E$ is
$$\lambda_{\min}[A] = \inf_{\|d\| = 1} A[d, d].$$
It is $0$ on the zero space, where the unit sphere is empty.

For a symmetric matrix $A$ this is the leftmost eigenvalue of Section A.5 of
[cartis2022evaluation]. The infimum is the infimum in `ℝ` over the unit sphere
`Metric.sphere 0 1`. -/
noncomputable def minCurvature (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) : ℝ :=
  ⨅ d : sphere (0 : E) 1, A (fun _ => (d : E))

variable (A B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)

/-- The defining formula $\lambda_{\min}[A] = \inf_{\|d\| = 1} A[d, d]$. -/
theorem minCurvature_def : minCurvature A = ⨅ d : sphere (0 : E) 1, A (fun _ => (d : E)) := rfl

/-- For every $d \in E$, $|A[d, d]| \le \|A\| \|d\|^2$. -/
theorem abs_apply_diag_le (d : E) : |A (fun _ => d)| ≤ ‖A‖ * ‖d‖ ^ 2 := by
  simpa [Fin.prod_univ_two, sq] using A.le_opNorm (fun _ => d)

/-- The values $A[d, d]$ on the unit sphere are bounded below. -/
theorem bddBelow_apply_sphere :
    BddBelow (range fun d : sphere (0 : E) 1 => A (fun _ => (d : E))) := by
  refine ⟨-‖A‖, ?_⟩
  rintro _ ⟨d, rfl⟩
  have h := neg_abs_le (A (fun _ => (d : E)))
  have hd : ‖(d : E)‖ = 1 := by simp
  have := abs_apply_diag_le A d
  rw [hd] at this
  linarith

/-- If $\|d\| = 1$, then $\lambda_{\min}[A] \le A[d, d]$. This is the Rayleigh bound (A.3) of
[cartis2022evaluation] on the unit sphere. -/
theorem minCurvature_le_apply {d : E} (hd : ‖d‖ = 1) : minCurvature A ≤ A (fun _ => d) :=
  ciInf_le (bddBelow_apply_sphere A) (⟨d, by simpa using hd⟩ : sphere (0 : E) 1)

/-- For every $d \in E$,
$$\lambda_{\min}[A] \|d\|^2 \le A[d, d].$$
This is the Rayleigh bound (A.3) of [cartis2022evaluation]. -/
theorem minCurvature_mul_norm_sq_le (d : E) : minCurvature A * ‖d‖ ^ 2 ≤ A (fun _ => d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [A.map_coord_zero (m := fun _ => (0 : E)) 0 rfl]
  have hn : 0 < ‖d‖ := norm_pos_iff.2 hd
  have h := minCurvature_le_apply A (d := ‖d‖⁻¹ • d) (by simp [norm_smul, hn.ne'])
  have hs : A (fun _ => ‖d‖⁻¹ • d) = (‖d‖⁻¹) ^ 2 * A (fun _ => d) := by
    simpa [Fin.prod_univ_two, sq] using A.map_smul_univ (fun _ => ‖d‖⁻¹) (fun _ => d)
  rw [hs] at h
  have h2 : 0 < ‖d‖ ^ 2 := by positivity
  calc minCurvature A * ‖d‖ ^ 2 ≤ (‖d‖⁻¹) ^ 2 * A (fun _ => d) * ‖d‖ ^ 2 := by gcongr
    _ = A (fun _ => d) := by field_simp

/-- If $E$ is the zero space, then $\lambda_{\min}[A] = 0$, because the unit sphere is empty. -/
theorem minCurvature_of_subsingleton [Subsingleton E] : minCurvature A = 0 := by
  have : IsEmpty (sphere (0 : E) 1) := ⟨fun d => by
    have := d.2
    simp [Subsingleton.elim (d : E) 0] at this⟩
  rw [minCurvature_def, Real.iInf_of_isEmpty]

variable {A B}

/-- Let $E$ be a nonzero real normed space and let $c \in \mathbb{R}$. Then
$$c \le \lambda_{\min}[A] \iff c \|d\|^2 \le A[d, d] \text{ for all } d \in E.$$

With $c = -\varepsilon$, the right-hand side is the approximate second-order condition (3.2.6)
of [cartis2022evaluation]. -/
theorem le_minCurvature_iff [Nontrivial E] {c : ℝ} :
    c ≤ minCurvature A ↔ ∀ d, c * ‖d‖ ^ 2 ≤ A (fun _ => d) := by
  constructor
  · intro hc d
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (minCurvature_mul_norm_sq_le A d)
  · intro h
    have : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
    refine le_ciInf fun d => ?_
    have hd : ‖(d : E)‖ = 1 := by simp
    simpa [hd] using h d

/-- $\lambda_{\min}[A] \ge 0$ if and only if $A$ is positive semidefinite: $A[d, d] \ge 0$ for all
$d$. -/
theorem minCurvature_nonneg_iff : 0 ≤ minCurvature A ↔ ∀ d, 0 ≤ A (fun _ => d) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [minCurvature_of_subsingleton, le_refl, true_iff]
    intro d
    rw [Subsingleton.elim d 0, A.map_coord_zero (m := fun _ => (0 : E)) 0 rfl]
  · simp [le_minCurvature_iff]

/-- On a nonzero space, for every $c > \lambda_{\min}[A]$ there is a unit vector $d$ with
$A[d, d] < c$. -/
theorem exists_apply_lt_of_minCurvature_lt [Nontrivial E] {c : ℝ} (hc : minCurvature A < c) :
    ∃ d, ‖d‖ = 1 ∧ A (fun _ => d) < c := by
  have : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨d, hd⟩ := exists_lt_of_ciInf_lt hc
  exact ⟨d, by simp, hd⟩

/-- For every continuous bilinear form $A$,
$$-\|A\| \le \lambda_{\min}[A] \le \|A\|.$$
This is (A.4) of [cartis2022evaluation]. -/
theorem abs_minCurvature_le_norm : |minCurvature A| ≤ ‖A‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [minCurvature_of_subsingleton]
  rw [abs_le]
  constructor
  · refine le_minCurvature_iff.2 fun d => ?_
    have := neg_abs_le (A (fun _ => d))
    have := abs_apply_diag_le A d
    linarith
  · obtain ⟨d, hd⟩ := exists_norm_eq E zero_le_one
    have h1 := minCurvature_le_apply A hd
    have h2 := le_abs_self (A (fun _ => d))
    have h3 := abs_apply_diag_le A d
    rw [hd] at h3
    linarith

/-- For continuous bilinear forms $A$ and $B$,
$$|\lambda_{\min}[A] - \lambda_{\min}[B]| \le \|A - B\|,$$
so $\lambda_{\min}$ is $1$-Lipschitz. This is (A.5) of [cartis2022evaluation]. -/
theorem abs_minCurvature_sub_le : |minCurvature A - minCurvature B| ≤ ‖A - B‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [minCurvature_of_subsingleton]
  have key : ∀ A B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ,
      minCurvature B - ‖A - B‖ ≤ minCurvature A := by
    intro A B
    refine le_minCurvature_iff.2 fun d => ?_
    have h1 := minCurvature_mul_norm_sq_le B d
    have h2 := neg_abs_le ((A - B) (fun _ => d))
    have h3 := abs_apply_diag_le (A - B) d
    have h4 : (A - B) (fun _ => d) = A (fun _ => d) - B (fun _ => d) := rfl
    nlinarith
  rw [abs_sub_le_iff]
  have := key A B
  have := key B A
  rw [norm_sub_rev] at this
  constructor <;> linarith

variable (A)

/-- Let $E$ be a nonzero finite-dimensional real normed space. Then for every continuous bilinear
form $A$ there is a unit vector $u$ with $A[u, u] = \lambda_{\min}[A]$. -/
theorem exists_eq_minCurvature [FiniteDimensional ℝ E] [Nontrivial E]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) :
    ∃ u, ‖u‖ = 1 ∧ A (fun _ => u) = minCurvature A := by
  have := FiniteDimensional.proper_real E
  have hcont : Continuous fun d : E => A (fun _ => d) :=
    A.coe_continuous.comp (continuous_pi fun _ => continuous_id)
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hcont.continuousOn
  have hu1 : ‖u‖ = 1 := by simpa using hu
  refine ⟨u, hu1, le_antisymm ?_ (minCurvature_le_apply A hu1)⟩
  have : Nonempty (sphere (0 : E) 1) := ⟨⟨u, hu⟩⟩
  exact le_ciInf fun d => hmin d.2

/-! ### Bilinear-form calculus on pairs of vectors -/

/-- The diagonal value $A[d, d]$, written `A (fun _ => d)`, equals `A ![d, d]`. -/
theorem apply_diag_eq_vec (d : E) : A (fun _ => d) = A ![d, d] := by
  congr 1
  funext i
  fin_cases i <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem update_vec_zero (x z v : E) : Function.update ![x, z] 0 v = ![v, z] := by
  ext i
  fin_cases i <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem update_vec_one (x z v : E) : Function.update ![z, x] 1 v = ![z, v] := by
  ext i
  fin_cases i <;> rfl

/-- $A[x + y, z] = A[x, z] + A[y, z]$. -/
theorem apply_vec_add_left (x y z : E) : A ![x + y, z] = A ![x, z] + A ![y, z] := by
  simpa only [update_vec_zero] using A.map_update_add ![x, z] 0 x y

/-- $A[c x, z] = c A[x, z]$. -/
theorem apply_vec_smul_left (c : ℝ) (x z : E) : A ![c • x, z] = c * A ![x, z] := by
  simpa only [update_vec_zero, smul_eq_mul] using A.map_update_smul ![x, z] 0 c x

/-- $A[z, x + y] = A[z, x] + A[z, y]$. -/
theorem apply_vec_add_right (x y z : E) : A ![z, x + y] = A ![z, x] + A ![z, y] := by
  simpa only [update_vec_one] using A.map_update_add ![z, x] 1 x y

/-- $A[z, c x] = c A[z, x]$. -/
theorem apply_vec_smul_right (c : ℝ) (x z : E) : A ![z, c • x] = c * A ![z, x] := by
  simpa only [update_vec_one, smul_eq_mul] using A.map_update_smul ![z, x] 1 c x

variable {A}

/-- Let $A$, $T$ and $N$ be continuous bilinear forms on $E$, and let $c \ge 0$ and $K \ge 0$ be
real numbers with $N[d, d] \le K \|d\|^2$ for all $d \in E$. Then
$$\lambda_{\min}[T + c N] - \|A - T\| - c K \le \lambda_{\min}[A].$$

In [cartis2022evaluation], $T + c N$ is a model of $A$, and this is the computation
(4.1.27)–(4.1.29) and (5.5.15)–(5.5.17), based on $\min(a + b) \ge \min a + \min b$. -/
theorem minCurvature_ge_of_add_smul
    (A T N : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) {c K : ℝ} (hc : 0 ≤ c)
    (hK : 0 ≤ K) (hN : ∀ d, N (fun _ => d) ≤ K * ‖d‖ ^ 2) :
    minCurvature (T + c • N) - ‖A - T‖ - c * K ≤ minCurvature A := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [minCurvature_of_subsingleton]
    have := norm_nonneg (A - T)
    nlinarith [mul_nonneg hc hK]
  refine le_minCurvature_iff.2 fun d => ?_
  have h1 := minCurvature_mul_norm_sq_le (T + c • N) d
  have h2 : -(‖A - T‖ * ‖d‖ ^ 2) ≤ (A - T) (fun _ => d) :=
    neg_le_of_abs_le (abs_apply_diag_le (A - T) d)
  have h3 : c * N (fun _ => d) ≤ c * (K * ‖d‖ ^ 2) := mul_le_mul_of_nonneg_left (hN d) hc
  have hsplit : A (fun _ => d) = (A - T) (fun _ => d) + (T + c • N) (fun _ => d) -
      c * N (fun _ => d) := by
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hsplit]
  nlinarith

/-! ### Least curvature on a subspace -/

/-- The **least curvature of $A$ on a subspace** $V$ of $E$ is the least curvature of the
restriction of $A$ to $V$:
$$\lambda_{\min}[A|_V] = \inf_{d \in V,\ \|d\| = 1} A[d, d].$$
It is $\lambda_{\min}[Q^T A Q]$ for a matrix $Q$ with orthonormal columns that span $V$, as in
(3.4.32) of [cartis2022evaluation]. For $V = E$, which is $Q = I$, it is $\lambda_{\min}[A]$
(`minCurvatureOn_top`).

The restriction is the composition of $A$ with the inclusion of $V$ in both arguments. On
$V = 0$ the value is $0$. -/
noncomputable def minCurvatureOn (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (V : Submodule ℝ E) : ℝ :=
  minCurvature (A.compContinuousLinearMap fun _ => V.subtypeL)

/-- The defining formula: `minCurvatureOn A V` is the least curvature of the restriction of $A$ to
$V$. -/
theorem minCurvatureOn_def (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (V : Submodule ℝ E) :
    minCurvatureOn A V = minCurvature (A.compContinuousLinearMap fun _ => V.subtypeL) := rfl

section MinCurvatureOn

variable {V : Submodule ℝ E}

/-- For every $d \in V$, $\lambda_{\min}[A|_V] \|d\|^2 \le A[d, d]$. -/
theorem minCurvatureOn_mul_norm_sq_le {d : E} (hd : d ∈ V) :
    minCurvatureOn A V * ‖d‖ ^ 2 ≤ A (fun _ => d) := by
  have := minCurvature_mul_norm_sq_le (A.compContinuousLinearMap fun _ => V.subtypeL)
    (⟨d, hd⟩ : V)
  rw [minCurvatureOn]
  simpa using this

/-- Let $V$ be a nonzero subspace of $E$ and let $c \in \mathbb{R}$. Then
$$c \le \lambda_{\min}[A|_V] \iff c \|d\|^2 \le A[d, d] \text{ for all } d \in V.$$
-/
theorem le_minCurvatureOn_iff [Nontrivial V] {c : ℝ} :
    c ≤ minCurvatureOn A V ↔ ∀ d ∈ V, c * ‖d‖ ^ 2 ≤ A (fun _ => d) := by
  refine ⟨fun hc d hd => (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans
    (minCurvatureOn_mul_norm_sq_le hd), fun h => ?_⟩
  refine le_minCurvature_iff.2 fun d => ?_
  simpa using h d d.2

/-- If $c \le 0$ and $c \|d\|^2 \le A[d, d]$ for all $d \in V$, then $c \le \lambda_{\min}[A|_V]$.
The hypothesis $c \le 0$ covers the case $V = 0$, where $\lambda_{\min}[A|_V] = 0$. -/
theorem le_minCurvatureOn {c : ℝ} (hc : c ≤ 0) (h : ∀ d ∈ V, c * ‖d‖ ^ 2 ≤ A (fun _ => d)) :
    c ≤ minCurvatureOn A V := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [minCurvatureOn, minCurvature_of_subsingleton]; exact hc
  · exact le_minCurvatureOn_iff.2 h

/-- On the whole space, the least curvature of $A$ on $V = E$ is $\lambda_{\min}[A]$; in matrix
terms, $\lambda_{\min}[I^T A I] = \lambda_{\min}[A]$. -/
@[simp]
theorem minCurvatureOn_top : minCurvatureOn A ⊤ = minCurvature A := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : Subsingleton (⊤ : Submodule ℝ E) := inferInstance
    rw [minCurvatureOn, minCurvature_of_subsingleton, minCurvature_of_subsingleton]
  · have : Nontrivial (⊤ : Submodule ℝ E) := Submodule.topEquiv.toEquiv.nontrivial
    refine le_antisymm (le_minCurvature_iff.2 fun d =>
      minCurvatureOn_mul_norm_sq_le (Submodule.mem_top (x := d))) ?_
    exact le_minCurvatureOn_iff.2 fun d _ => minCurvature_mul_norm_sq_le A d

end MinCurvatureOn

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let $E$ be a real inner product space. The inner product as a continuous bilinear form,
$I[v, w] = \langle v, w \rangle$. It is the identity matrix $I$ of [cartis2022evaluation]. -/
noncomputable def innerForm : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  @ContinuousLinearMap.uncurryLeft ℝ 1 (fun _ => E) ℝ _ _ _ _ _ <|
    (↑(continuousMultilinearCurryFin1 ℝ E ℝ).symm : (E →L[ℝ] ℝ) →L[ℝ] _).comp (innerSL ℝ)

/-- The inner product form takes the value $I[v, w] = \langle v, w \rangle$, written
`innerForm v = ⟪v 0, v 1⟫` for a pair `v : Fin 2 → E`. -/
@[simp]
theorem innerForm_apply (v : Fin 2 → E) : innerForm v = ⟪v 0, v 1⟫ := rfl

/-- The diagonal of the inner product form is the squared norm: $I[d, d] = \|d\|^2$. -/
theorem innerForm_apply_diag (d : E) : innerForm (fun _ => d) = ‖d‖ ^ 2 := by
  simp

/-- On a nonzero real inner product space, $\lambda_{\min}[I] = 1$. -/
theorem minCurvature_innerForm [Nontrivial E] : minCurvature (innerForm : E [×2]→L[ℝ] ℝ) = 1 := by
  refine le_antisymm ?_ (le_minCurvature_iff.2 fun d => by simp)
  obtain ⟨d, hd⟩ := exists_norm_eq E zero_le_one
  simpa [innerForm_apply_diag, hd] using minCurvature_le_apply innerForm hd

/-- Let $E$ be a nonzero real inner product space, let $A$ be a continuous bilinear form on $E$ and
let $\lambda \in \mathbb{R}$. Then
$$\lambda_{\min}[A + \lambda I] = \lambda_{\min}[A] + \lambda.$$
This is (3.4.33) of [cartis2022evaluation]. -/
theorem minCurvature_add_smul_inner [Nontrivial E]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) (lam : ℝ) :
    minCurvature (A + lam • innerForm) = minCurvature A + lam := by
  have happ : ∀ d : E, (A + lam • (innerForm : E [×2]→L[ℝ] ℝ)) (fun _ => d) =
      A (fun _ => d) + lam * ‖d‖ ^ 2 :=
    fun d => by simp
  refine le_antisymm ?_ ?_
  · have h : minCurvature (A + lam • innerForm) - lam ≤ minCurvature A := by
      refine le_minCurvature_iff.2 fun d => ?_
      have := minCurvature_mul_norm_sq_le (A + lam • innerForm) d
      rw [happ] at this
      linarith
    linarith
  · refine le_minCurvature_iff.2 fun d => ?_
    have := minCurvature_mul_norm_sq_le A d
    rw [happ]
    linarith

variable {A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ}

/-- If $A$ is symmetric, $A[v, w] = A[w, v]$ for all $v, w$, then for all $x, y \in E$ and
$t \in \mathbb{R}$,
$$A[x + t y, x + t y] = A[x, x] + 2 t A[x, y] + t^2 A[y, y].$$
-/
theorem apply_diag_add_smul (hA : ∀ v w, A ![v, w] = A ![w, v]) (x y : E) (t : ℝ) :
    A (fun _ => x + t • y) = A (fun _ => x) + 2 * t * A ![x, y] + t ^ 2 * A (fun _ => y) := by
  rw [apply_diag_eq_vec, apply_diag_eq_vec, apply_diag_eq_vec, apply_vec_add_left,
    apply_vec_add_right, apply_vec_add_right, apply_vec_smul_left, apply_vec_smul_left,
    apply_vec_smul_right, apply_vec_smul_right, hA y x]
  ring

/-- Let $E$ be a real inner product space and let $A$ be a symmetric continuous bilinear form on
$E$: $A[v, w] = A[w, v]$ for all $v, w$. If a unit vector $u$ satisfies
$A[u, u] = \lambda_{\min}[A]$, then for all $w \in E$,
$$A[u, w] = \lambda_{\min}[A] \langle u, w \rangle.$$
So a minimizer is an eigenvector, as in (3.2.3) of [cartis2022evaluation].

This is the bilinear-form version of Mathlib's `IsSelfAdjoint.hasEigenvector_of_isMinOn`. It
needs neither completeness of $E$ nor an operator that represents $A$. -/
theorem apply_eq_minCurvature_mul_inner (hA : ∀ v w, A ![v, w] = A ![w, v]) {u : E}
    (hu : ‖u‖ = 1) (hmin : A (fun _ => u) = minCurvature A) (w : E) :
    A ![u, w] = minCurvature A * ⟪u, w⟫ := by
  set μ := minCurvature A
  set a := A ![u, w] - μ * ⟪u, w⟫
  set b := A (fun _ => w) - μ * ‖w‖ ^ 2
  have hb : 0 ≤ b := by have := minCurvature_mul_norm_sq_le A w; simp only [b]; linarith
  have key : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b := by
    intro t
    have h := minCurvature_mul_norm_sq_le A (u + t • w)
    rw [apply_diag_add_smul hA, hmin, norm_add_sq_real, norm_smul, inner_smul_right, hu,
      Real.norm_eq_abs, mul_pow, sq_abs] at h
    simp only [a, b]
    nlinarith
  have h := key (-a / (b + 1))
  have hb1 : 0 < b + 1 := by linarith
  have h2 : 0 ≤ -a ^ 2 * (b + 2) := by
    have := mul_nonneg h (sq_nonneg (b + 1))
    field_simp at this
    nlinarith
  have : a ^ 2 = 0 := by nlinarith [sq_nonneg a]
  have : a = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  simp only [a] at this
  linarith

/-- Let $E$ be a nonzero finite-dimensional real inner product space, let $A$ be a symmetric
continuous bilinear form on $E$, and let $g \in E$. Then there is a unit vector $u$ with
$$A[u, u] = \lambda_{\min}[A], \qquad A[u, w] = \lambda_{\min}[A] \langle u, w \rangle \text{
  for all } w \in E, \qquad \langle u, g \rangle \le 0.$$
So $u$ is an eigenvector for $\lambda_{\min}[A]$, as in (3.2.3) of [cartis2022evaluation].

The sign condition comes from replacing $u$ by $-u$ if necessary. -/
theorem exists_eigenvector_minCurvature [FiniteDimensional ℝ E] [Nontrivial E]
    (hA : ∀ v w, A ![v, w] = A ![w, v]) (g : E) :
    ∃ u, ‖u‖ = 1 ∧ A (fun _ => u) = minCurvature A ∧
      (∀ w, A ![u, w] = minCurvature A * ⟪u, w⟫) ∧ ⟪u, g⟫ ≤ 0 := by
  obtain ⟨u, hu, hmin⟩ := exists_eq_minCurvature A
  by_cases hg : ⟪u, g⟫ ≤ 0
  · exact ⟨u, hu, hmin, apply_eq_minCurvature_mul_inner hA hu hmin, hg⟩
  · have hu' : ‖-u‖ = 1 := by rw [norm_neg, hu]
    have hmin' : A (fun _ => -u) = minCurvature A := by
      rw [← hmin, apply_diag_eq_vec, apply_diag_eq_vec, ← neg_one_smul ℝ u, apply_vec_smul_left,
        apply_vec_smul_right]
      ring
    refine ⟨-u, hu', hmin', apply_eq_minCurvature_mul_inner hA hu' hmin', ?_⟩
    rw [inner_neg_left]
    linarith

section Operator

variable {T : E →ₗ[ℝ] E}

/-- Let $T$ be a linear operator on $E$ with $A[v, w] = \langle v, T w \rangle$ for all $v, w$. Then
$\lambda_{\min}[A] \le \mu$ for every eigenvalue $\mu$ of $T$. -/
theorem minCurvature_le_of_hasEigenvalue (hAT : ∀ v w, A ![v, w] = ⟪v, T w⟫) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue T μ) : minCurvature A ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hTv : T v = μ • v := hv.apply_eq_smul
  have hv0 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 hv.2; positivity
  have h := minCurvature_mul_norm_sq_le A v
  rw [apply_diag_eq_vec, hAT, hTv, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  exact le_of_mul_le_mul_right h hv0

/-- If $T$ is a symmetric linear operator on $E$ and $A[v, w] = \langle v, T w \rangle$ for all
$v, w$, then $A$ is symmetric: $A[v, w] = A[w, v]$. -/
theorem apply_vec_comm_of_isSymmetric (hT : T.IsSymmetric) (hAT : ∀ v w, A ![v, w] = ⟪v, T w⟫)
    (v w : E) : A ![v, w] = A ![w, v] := by
  rw [hAT, hAT, ← hT, real_inner_comm]

/-- Let $E$ be a nonzero finite-dimensional real inner product space and let $T$ be a symmetric
linear operator on $E$ with $A[v, w] = \langle v, T w \rangle$ for all $v, w$. Then
$\lambda_{\min}[A]$ is an eigenvalue of $T$. -/
theorem hasEigenvalue_minCurvature [FiniteDimensional ℝ E] [Nontrivial E] (hT : T.IsSymmetric)
    (hAT : ∀ v w, A ![v, w] = ⟪v, T w⟫) : Module.End.HasEigenvalue T (minCurvature A) := by
  obtain ⟨u, hu, -, heig, -⟩ :=
    exists_eigenvector_minCurvature (apply_vec_comm_of_isSymmetric hT hAT) (0 : E)
  have hTu : T u = minCurvature A • u := ext_inner_right ℝ fun w => by
    rw [hT, ← hAT, heig, real_inner_smul_left]
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 hTu, hu0⟩

/-- Let $E$ be a finite-dimensional real inner product space of dimension $n$, and let $T$ be a
symmetric linear operator on $E$ with $A[v, w] = \langle v, T w \rangle$ for all $v, w$. Then
$\lambda_{\min}[A]$ is the least eigenvalue of $T$:
$$\lambda_{\min}[A] = \min_{1 \le i \le n} \lambda_i(T).$$
This is the leftmost eigenvalue of Section A.5 of [cartis2022evaluation].

The eigenvalues are Mathlib's `LinearMap.IsSymmetric.eigenvalues`, indexed by `Fin n`, and the
minimum is an infimum in `ℝ`. For $n = 0$ both sides are $0$. -/
theorem minCurvature_eq_iInf_eigenvalues [FiniteDimensional ℝ E] (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hAT : ∀ v w, A ![v, w] = ⟪v, T w⟫) :
    minCurvature A = ⨅ i, hT.eigenvalues hn i := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h2 : IsEmpty (Fin n) := by
      rw [← hn, Module.finrank_zero_of_subsingleton]; infer_instance
    rw [minCurvature_of_subsingleton, Real.iInf_of_isEmpty]
  have : Nonempty (Fin n) := ⟨⟨0, hn ▸ Module.finrank_pos⟩⟩
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq hn (hasEigenvalue_minCurvature hT hAT)
  refine le_antisymm (le_ciInf fun j => minCurvature_le_of_hasEigenvalue hAT
    (hT.hasEigenvalue_eigenvalues hn j)) ?_
  rw [← hi]
  exact ciInf_le (Set.finite_range _).bddBelow i

/-- Let $E$ be a nonzero finite-dimensional real inner product space and let $H$ be a continuous
linear operator on $E$ with $A[v, w] = \langle v, H w \rangle$ for all $v, w$. Then
$\lambda_{\min}[A]$ is the least Rayleigh quotient of $H$:
$$\lambda_{\min}[A] = \inf_{x \ne 0} \frac{\langle H x, x \rangle}{\|x\|^2}.$$
This combines (A.2) and (A.3) of [cartis2022evaluation].

The Rayleigh quotient is Mathlib's `ContinuousLinearMap.rayleighQuotient`. No symmetry of $H$ is
assumed. Compare Mathlib's `IsSelfAdjoint.hasEigenvalue_iInf_of_finiteDimensional`. -/
theorem minCurvature_eq_iInf_rayleigh [FiniteDimensional ℝ E] [Nontrivial E] {H : E →L[ℝ] E}
    (hAH : ∀ v w, A ![v, w] = ⟪v, H w⟫) :
    minCurvature A = ⨅ x : {x : E // x ≠ 0}, H.rayleighQuotient x := by
  have hR : ∀ x : E, H.rayleighQuotient x = ⟪H x, x⟫ / ‖x‖ ^ 2 := fun x => by
    rfl
  simp_rw [hR]
  have hq : ∀ x : {x : E // x ≠ 0}, minCurvature A ≤ ⟪H x, x⟫ / ‖(x : E)‖ ^ 2 := by
    intro x
    have hx : 0 < ‖(x : E)‖ ^ 2 := by have := norm_pos_iff.2 x.2; positivity
    rw [le_div_iff₀ hx, real_inner_comm, ← hAH, ← apply_diag_eq_vec]
    exact minCurvature_mul_norm_sq_le A x
  obtain ⟨u, hu, hmin⟩ := exists_eq_minCurvature A
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have : Nonempty {x : E // x ≠ 0} := ⟨⟨u, hu0⟩⟩
  refine le_antisymm (le_ciInf hq) ?_
  refine (ciInf_le ⟨minCurvature A, ?_⟩ (⟨u, hu0⟩ : {x : E // x ≠ 0})).trans ?_
  · rintro _ ⟨x, rfl⟩
    exact hq x
  · simp only [hu, one_pow, div_one]
    rw [real_inner_comm, ← hAH, ← apply_diag_eq_vec, hmin]

end Operator

/-- Let $\iota$ be a finite type, let $M \in \mathbb{R}^{\iota \times \iota}$ be a symmetric matrix,
and let $A$ be a continuous bilinear form on $\mathbb{R}^\iota$ with the Euclidean inner
product, such that $A[v, w] = \langle v, M w \rangle$ for all $v, w$. Then $\lambda_{\min}[A]$
is the least eigenvalue of $M$:
$$\lambda_{\min}[A] = \min_i \lambda_i(M).$$
This is the leftmost eigenvalue of Section A.5 of [cartis2022evaluation].

The space is `EuclideanSpace ℝ ι`, $M w$ is `Matrix.toEuclideanLin M w`, and the eigenvalues are
`Matrix.IsHermitian.eigenvalues`. The minimum is an infimum in `ℝ`, which is $0$ for an empty
$\iota$. -/
theorem minCurvature_eq_iInf_isHermitian_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    {A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ ι) ℝ}
    (hAM : ∀ v w, A ![v, w] = ⟪v, Matrix.toEuclideanLin M w⟫) :
    minCurvature A = ⨅ i, hM.eigenvalues i := by
  rw [minCurvature_eq_iInf_eigenvalues (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM)
    finrank_euclideanSpace hAM]
  exact (Equiv.iInf_comp (g := fun j => (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM).eigenvalues
    finrank_euclideanSpace j) (Fintype.equivOfCardEq (Fintype.card_fin _)).symm).symm

end Inner
