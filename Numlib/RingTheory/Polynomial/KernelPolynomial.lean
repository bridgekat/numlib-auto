/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Basic` for the affine-hyperplane lemma and a
new `Mathlib.RingTheory.Polynomial.KernelPolynomial` for the rest.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact

/-!
# Kernel polynomials

Let $B$ be a bilinear form on $\mathbb{R}[X]$, let $\gamma \in \mathbb{R}$ and $k \in \mathbb{N}$,
and let $q_0, q_1, \dots$ be polynomials with $\deg q_i = i$ that are orthonormal for $B$, so that
$q_0, \dots, q_k$ is a basis of the polynomials of degree at most $k$. The **kernel polynomial**
$$K_k(\gamma) = \Bigl(\sum_{i=0}^{k} q_i(\gamma)^2\Bigr)^{-1} \sum_{i=0}^{k} q_i(\gamma)\, q_i$$
minimizes $B(p, p)$ over the polynomials $p$ with $\deg p \le k$ and $p(\gamma) = 1$, and the
minimum value is $\bigl(\sum_{i \le k} q_i(\gamma)^2\bigr)^{-1}$. This is the least-squares
counterpart of the Chebyshev min–max problem of `Numlib.RingTheory.Polynomial.ChebyshevMinimax`:
both problems minimize over the same set of polynomials, but the Chebyshev problem minimizes the
supremum norm on an interval. The presentation follows [saad2003iterative], §12.3.3.

The mathematical content is the Cauchy–Schwarz inequality. In an inner product space, the least norm
of a point $x$ on the affine hyperplane $\langle y, x \rangle = 1$ is $1 / \|y\|$, attained at
$x = \|y\|^{-2} y$. With $y$ the vector of values $q_i(\gamma)$, this is the kernel polynomial
formula. The module also proves the normal equations of the problem at $\gamma = 0$, and a geometric
decay of the minimum value for a form supported on an interval $[\alpha, \beta]$ with
$0 < \alpha < \beta$.

## Main definitions

* `LinearMap.BilinForm.IsOrthonormal`: a family $(v_i)$ with $B(v_i, v_j) = 1$ for $i = j$ and $0$
  otherwise.
* `Polynomial.kernelPolynomial`: the kernel polynomial $K_k(\gamma)$ of a family $(q_i)$.

## Main results

* `isLeast_of_inner_eq_one`: the least norm on the affine hyperplane $\langle y, x \rangle = 1$ is
  $1 / \|y\|$.
* `LinearMap.BilinForm.IsOrthonormal.apply_sum_smul_sum_smul`: on the span of an orthonormal family,
  $B$ is the dot product of the coefficients.
* `Polynomial.bilinForm_kernelPolynomial_le`: the kernel polynomial minimizes $B(p, p)$ over the
  polynomials of degree at most $k$ with value $1$ at $\gamma$, with minimum value
  $\bigl(\sum_{i \le k} q_i(\gamma)^2\bigr)^{-1}$.
* `Polynomial.bilinForm_kernelPolynomial_mul_X`: for symmetric $B$, $B(X p, K_k(0)) = 0$ for every
  $p$ of degree less than $k$.
* `Polynomial.bilinForm_kernelPolynomial_le_pow`: for a form supported on $[\alpha, \beta]$ with
  $0 < \alpha < \beta$, $B(K_k(0), K_k(0)) \le \bigl((\beta - \alpha)/(\beta + \alpha)\bigr)^{2k}
  B(1, 1)$.

## Implementation notes

* No measure theory appears. The weighted form $B(p, r) = \int p r w$ is one instance, but the
  proofs do not use the integral, so the discrete forms that come from a spectral measure are
  covered by the same statements.
* Positive semidefiniteness of $B$ is not assumed. On the polynomials of degree at most $k$, it
  follows from the orthonormality of $(q_i)$ (`Polynomial.bilinForm_self_nonneg_of_degree_le`).
* The explicit formula of [saad2003iterative] for Jacobi weights and the evaluation of the minimum
  by the Gamma function are not here, because they need Jacobi polynomials.
-/

open Polynomial

/-- The **least norm on an affine hyperplane**. Let $E$ be an inner product space over $\mathbb{R}$
or $\mathbb{C}$ and let $y \in E$ be nonzero. Then $1 / \|y\|$ is the least element of the set
of norms $\|x\|$ of the points $x \in E$ with $\langle y, x \rangle = 1$.

The Cauchy–Schwarz inequality gives the lower bound, and the point $x = \|y\|^{-2} y$ attains
it. -/
theorem isLeast_of_inner_eq_one {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {y : E} (hy : y ≠ 0) :
    IsLeast {r : ℝ | ∃ x : E, inner 𝕜 y x = 1 ∧ ‖x‖ = r} (1 / ‖y‖) := by
  have hy0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hyK : ((‖y‖ : 𝕜)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (RCLike.ofReal_ne_zero.mpr hy0.ne')
  refine ⟨⟨(((‖y‖ : 𝕜)) ^ 2)⁻¹ • y, ?_, ?_⟩, ?_⟩
  · rw [inner_smul_right, inner_self_eq_norm_sq_to_K, inv_mul_cancel₀ hyK]
  · rw [norm_smul, norm_inv, norm_pow, RCLike.norm_ofReal, abs_of_pos hy0, pow_two, mul_inv,
      mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one, one_div]
  · rintro r ⟨x, hx, rfl⟩
    rw [div_le_iff₀ hy0]
    calc (1 : ℝ) = ‖inner 𝕜 y x‖ := by rw [hx, norm_one]
      _ ≤ ‖y‖ * ‖x‖ := norm_inner_le_norm y x
      _ = ‖x‖ * ‖y‖ := mul_comm _ _

namespace LinearMap.BilinForm

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]

/-- A family $(v_i)_{i \in \iota}$ in a module $M$ is **orthonormal** for a bilinear form $B$ on $M$
if $B(v_i, v_j) = 1$ for $i = j$ and $B(v_i, v_j) = 0$ for $i \neq j$.

For the inner product of a real inner product space, this is Mathlib's `Orthonormal` (see
`orthonormal_iff_ite`). Here $B$ need not be positive or symmetric. -/
def IsOrthonormal (B : LinearMap.BilinForm R M) (v : ι → M) : Prop :=
  ∀ i j, B (v i) (v j) = if i = j then 1 else 0

/-- A family $(v_i)$ is orthonormal for $B$ if and only if $B(v_i, v_j)$ is $1$ for $i = j$ and $0$
otherwise, for all $i$, $j$. -/
theorem isOrthonormal_iff {B : LinearMap.BilinForm R M} {v : ι → M} :
    B.IsOrthonormal v ↔ ∀ i j, B (v i) (v j) = if i = j then 1 else 0 :=
  Iff.rfl

namespace IsOrthonormal

variable {B : LinearMap.BilinForm R M} {v : ι → M}

/-- If $(v_i)$ is orthonormal for $B$, then $B(v_i, v_j)$ is $1$ for $i = j$ and $0$ otherwise. -/
theorem apply (h : B.IsOrthonormal v) (i j : ι) : B (v i) (v j) = if i = j then 1 else 0 :=
  h i j

/-- On the span of an orthonormal family, the form is the dot product of the coefficients: if
$(v_i)$ is orthonormal for $B$, then for every finite set $s$ of indices and all coefficients
$c_i$, $d_i$,
$$B\Bigl(\sum_{i \in s} c_i v_i, \sum_{j \in s} d_j v_j\Bigr) = \sum_{i \in s} c_i d_i.$$
-/
theorem apply_sum_smul_sum_smul (h : B.IsOrthonormal v) (s : Finset ι) (c d : ι → R) :
    B (∑ i ∈ s, c i • v i) (∑ j ∈ s, d j • v j) = ∑ i ∈ s, c i * d i := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, h.apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  exact Finset.sum_congr rfl fun i hi => by simp [hi, mul_comm]

end IsOrthonormal

end LinearMap.BilinForm

namespace Polynomial

/-! ### Spanning by a family with one polynomial of each degree -/

/-- Let $K$ be a field and let $q_0, q_1, \dots \in K[X]$ satisfy $\deg q_i = i$ for every $i$. Then
for every $k \in \mathbb{N}$, every polynomial $p$ of degree at most $k$ is a linear combination
$p = \sum_{i=0}^{k} c_i q_i$.

Thus an orthonormal family with $\deg q_i = i$ is a basis of the competitors in the minimization
problems below. -/
theorem exists_sum_smul_of_degree_le {K : Type*} [Field K] {q : ℕ → K[X]}
    (hdeg : ∀ i, (q i).degree = i) :
    ∀ (k : ℕ) {p : K[X]}, p.degree ≤ k →
      ∃ c : ℕ → K, p = ∑ i ∈ Finset.range (k + 1), c i • q i := by
  have hne : ∀ i : ℕ, q i ≠ 0 := fun i h => by
    have := hdeg i
    rw [h, degree_zero] at this
    exact absurd this (by simp)
  have hcoeff : ∀ i : ℕ, (q i).coeff i ≠ 0 := fun i => by
    have hlc : (q i).leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp (hne i)
    rwa [leadingCoeff, natDegree_eq_of_degree_eq_some (hdeg i)] at hlc
  intro k
  induction k with
  | zero =>
    intro p hp
    refine ⟨fun _ => p.coeff 0 / (q 0).coeff 0, ?_⟩
    rw [Finset.sum_range_one]
    refine Polynomial.ext fun m => ?_
    rw [coeff_smul, smul_eq_mul]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [div_mul_cancel₀ _ (hcoeff 0)]
    · have hm' : (0 : WithBot ℕ) < (m : WithBot ℕ) := by exact_mod_cast hm
      rw [coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hp hm'),
        coeff_eq_zero_of_degree_lt (lt_of_le_of_lt (hdeg 0).le hm'), mul_zero]
  | succ k ih =>
    intro p hp
    have hrdeg : (p - (p.coeff (k + 1) / (q (k + 1)).coeff (k + 1)) • q (k + 1)).degree ≤
        (k : WithBot ℕ) := by
      refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
      have hm0 : k < m := by exact_mod_cast hm
      have hm' : k + 1 ≤ m := hm0
      rw [coeff_sub, coeff_smul, smul_eq_mul]
      rcases eq_or_lt_of_le hm' with rfl | hlt
      · rw [div_mul_cancel₀ _ (hcoeff (k + 1)), sub_self]
      · have hlt' : ((k + 1 : ℕ) : WithBot ℕ) < (m : WithBot ℕ) := by exact_mod_cast hlt
        rw [coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hp hlt'),
          coeff_eq_zero_of_degree_lt (lt_of_le_of_lt (hdeg (k + 1)).le hlt'), mul_zero, sub_self]
    obtain ⟨c, hc⟩ := ih hrdeg
    refine ⟨Function.update c (k + 1) (p.coeff (k + 1) / (q (k + 1)).coeff (k + 1)), ?_⟩
    have hsum : ∑ i ∈ Finset.range (k + 1),
        Function.update c (k + 1) (p.coeff (k + 1) / (q (k + 1)).coeff (k + 1)) i • q i =
          ∑ i ∈ Finset.range (k + 1), c i • q i :=
      Finset.sum_congr rfl fun i hi => by
        rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hi))]
    rw [Finset.sum_range_succ, hsum, Function.update_self, ← hc]
    abel

/-! ### The kernel polynomial -/

/-- The **kernel polynomial** of a family $q_0, q_1, \dots \in \mathbb{R}[X]$ at
$\gamma \in \mathbb{R}$ and of degree $k$:
$$K_k(\gamma) = \Bigl(\sum_{i=0}^{k} q_i(\gamma)^2\Bigr)^{-1} \sum_{i=0}^{k} q_i(\gamma)\,
  q_i.$$
If the normalizing sum $\sum_{i \le k} q_i(\gamma)^2$ is $0$, the inverse is $0$ and
$K_k(\gamma) = 0$.

For a family that is orthonormal for a bilinear form, $K_k(\gamma)$ is normalized to the value
$1$ at $\gamma$ (`Polynomial.kernelPolynomial_eval`). It is the least-squares analogue of the
shifted Chebyshev polynomial `Polynomial.Chebyshev.shifted`. -/
noncomputable def kernelPolynomial (q : ℕ → ℝ[X]) (γ : ℝ) (k : ℕ) : ℝ[X] :=
  (∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2)⁻¹ •
    ∑ i ∈ Finset.range (k + 1), (q i).eval γ • q i

section Bilin

variable {B : LinearMap.BilinForm ℝ ℝ[X]} {q : ℕ → ℝ[X]}

/-- A combination $\sum_{i \le k} c_i q_i$ takes the value $\sum_{i \le k} c_i q_i(\gamma)$ at
$\gamma$. -/
private theorem eval_sum_smul (γ : ℝ) (k : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (k + 1), c i • q i).eval γ =
      ∑ i ∈ Finset.range (k + 1), c i * (q i).eval γ := by
  simp [eval_finsetSum]

/-- If $(q_i)$ is orthonormal for $B$ and $\deg q_i = i$ for every $i$, then $B(p, p) \ge 0$ for
every polynomial $p$ of degree at most $k$.

The quadratic form on these polynomials is a sum of squares of coefficients. For this reason no
positivity hypothesis on $B$ appears in this module. -/
theorem bilinForm_self_nonneg_of_degree_le
    (horth : B.IsOrthonormal q) (hdeg : ∀ i, (q i).degree = i)
    {k : ℕ} {p : ℝ[X]} (hp : p.degree ≤ k) : 0 ≤ B p p := by
  obtain ⟨c, rfl⟩ := exists_sum_smul_of_degree_le hdeg k hp
  rw [horth.apply_sum_smul_sum_smul]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (c i)

/-- The kernel polynomial $K_k(\gamma)$ is the combination of $q_0, \dots, q_k$ with coefficients
$\bigl(\sum_{j \le k} q_j(\gamma)^2\bigr)^{-1} q_i(\gamma)$. -/
private theorem kernelPolynomial_eq (q : ℕ → ℝ[X]) (γ : ℝ) (k : ℕ) :
    kernelPolynomial q γ k =
      ∑ i ∈ Finset.range (k + 1),
        ((∑ j ∈ Finset.range (k + 1), (q j).eval γ ^ 2)⁻¹ * (q i).eval γ) • q i := by
  rw [kernelPolynomial, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _

private theorem sum_inv_mul_mul {S : ℝ} {k : ℕ} {y : ℕ → ℝ}
    (hy : ∑ i ∈ Finset.range (k + 1), y i ^ 2 = S) (hS : S ≠ 0) :
    ∑ i ∈ Finset.range (k + 1), S⁻¹ * y i * (S⁻¹ * y i) = S⁻¹ := by
  rw [Finset.sum_congr rfl fun i _ => (by ring :
      S⁻¹ * y i * (S⁻¹ * y i) = S⁻¹ * S⁻¹ * y i ^ 2), ← Finset.mul_sum, hy, mul_assoc,
    inv_mul_cancel₀ hS, mul_one]

private theorem sum_inv_mul_self {S : ℝ} {k : ℕ} {y : ℕ → ℝ}
    (hy : ∑ i ∈ Finset.range (k + 1), y i ^ 2 = S) (hS : S ≠ 0) :
    ∑ i ∈ Finset.range (k + 1), S⁻¹ * y i * y i = 1 := by
  rw [Finset.sum_congr rfl fun i _ => (by ring : S⁻¹ * y i * y i = S⁻¹ * y i ^ 2),
    ← Finset.mul_sum, hy, inv_mul_cancel₀ hS]

/-- If $\deg q_i = i$ for every $i$, then the kernel polynomial $K_k(\gamma)$ has degree at most
$k$. This is one of the two conditions that make it an admissible competitor. -/
theorem kernelPolynomial_degree_le (hdeg : ∀ i, (q i).degree = i) (γ : ℝ) (k : ℕ) :
    (kernelPolynomial q γ k).degree ≤ k := by
  refine (degree_smul_le _ _).trans ((degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_))
  refine (degree_smul_le _ _).trans ?_
  rw [hdeg i]
  exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

/-- If $\sum_{i \le k} q_i(\gamma)^2 \neq 0$, then the kernel polynomial satisfies
$K_k(\gamma)(\gamma) = 1$. This is the other condition that makes it admissible. The hypothesis
says that $q_i(\gamma) \neq 0$ for some $i \le k$. -/
theorem kernelPolynomial_eval {γ : ℝ} {k : ℕ}
    (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2 ≠ 0) :
    (kernelPolynomial q γ k).eval γ = 1 := by
  rw [kernelPolynomial_eq, eval_sum_smul]
  exact sum_inv_mul_self rfl hS

/-- If $(q_i)$ is orthonormal for $B$ and $S = \sum_{i \le k} q_i(\gamma)^2 \neq 0$, then the kernel
polynomial satisfies $B(K_k(\gamma), K_k(\gamma)) = S^{-1}$. This is the minimum value in
[saad2003iterative], §12.3.3. -/
theorem bilinForm_kernelPolynomial_self
    (horth : B.IsOrthonormal q) {γ : ℝ} {k : ℕ}
    (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2 ≠ 0) :
    B (kernelPolynomial q γ k) (kernelPolynomial q γ k) =
      (∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2)⁻¹ := by
  rw [kernelPolynomial_eq, horth.apply_sum_smul_sum_smul]
  exact sum_inv_mul_mul rfl hS

/-! ### The minimization -/

private theorem norm_sq_toLp {n : ℕ} (f : ℕ → ℝ) :
    ‖(WithLp.toLp 2 (fun i : Fin n => f i) : EuclideanSpace ℝ (Fin n))‖ ^ 2 =
      ∑ i ∈ Finset.range n, f i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, ← Fin.sum_univ_eq_sum_range (fun i => f i ^ 2) n]

private theorem inner_toLp {n : ℕ} (f g : ℕ → ℝ) :
    inner ℝ (WithLp.toLp 2 (fun i : Fin n => f i) : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (fun i : Fin n => g i)) = ∑ i ∈ Finset.range n, g i * f i := by
  rw [PiLp.inner_apply, ← Fin.sum_univ_eq_sum_range (fun i => g i * f i) n]
  exact Finset.sum_congr rfl fun i _ => by simp [RCLike.inner_apply]

/-- The **optimality of the kernel polynomial**. Let $B$ be a bilinear form on $\mathbb{R}[X]$, let
$(q_i)$ be orthonormal for $B$ with $\deg q_i = i$ for every $i$, let $\gamma \in \mathbb{R}$
and $k \in \mathbb{N}$, and suppose that $S = \sum_{i=0}^{k} q_i(\gamma)^2 \neq 0$. Then
$S^{-1}$ is the least value of $B(p, p)$ over the polynomials $p$ with $\deg p \le k$ and
$p(\gamma) = 1$:
$$\min \{ B(p, p) : \deg p \le k,\ p(\gamma) = 1 \} = \Bigl(\sum_{i=0}^{k}
  q_i(\gamma)^2\Bigr)^{-1}.$$

This is the optimality claim of [saad2003iterative], §12.3.3. The minimum is attained at
`Polynomial.kernelPolynomial q γ k` (see `Polynomial.bilinForm_kernelPolynomial_self`). The
proof expands a competitor in the orthonormal family and applies `isLeast_of_inner_eq_one` to
the vector of values $q_i(\gamma)$. -/
theorem bilinForm_kernelPolynomial_le
    (horth : B.IsOrthonormal q) (hdeg : ∀ i, (q i).degree = i)
    {γ : ℝ} {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2 ≠ 0) :
    IsLeast {r : ℝ | ∃ p : ℝ[X], p.degree ≤ k ∧ p.eval γ = 1 ∧ B p p = r}
      (∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2)⁻¹ := by
  have hynorm := norm_sq_toLp (n := k + 1) (fun i => (q i).eval γ)
  have hy0 : (WithLp.toLp 2 (fun i : Fin (k + 1) => (q i).eval γ) :
      EuclideanSpace ℝ (Fin (k + 1))) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hynorm
    exact hS (by simpa using hynorm.symm)
  refine ⟨⟨kernelPolynomial q γ k, kernelPolynomial_degree_le hdeg γ k,
    kernelPolynomial_eval hS, bilinForm_kernelPolynomial_self horth hS⟩, ?_⟩
  rintro r ⟨p, hpdeg, hpγ, rfl⟩
  obtain ⟨c, rfl⟩ := exists_sum_smul_of_degree_le hdeg k hpdeg
  have hxnorm := norm_sq_toLp (n := k + 1) c
  have hinner := (inner_toLp (n := k + 1) (fun i => (q i).eval γ) c).trans
    ((eval_sum_smul (q := q) γ k c).symm.trans hpγ)
  have hle := (isLeast_of_inner_eq_one hy0).2 ⟨_, hinner, rfl⟩
  rw [horth.apply_sum_smul_sum_smul]
  have hsq : ∑ i ∈ Finset.range (k + 1), c i * c i = ∑ i ∈ Finset.range (k + 1), c i ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq (c i) ▸ rfl
  rw [hsq, ← hxnorm, ← hynorm]
  calc (‖(WithLp.toLp 2 (fun i : Fin (k + 1) => (q i).eval γ) :
        EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2)⁻¹
      = (1 / ‖(WithLp.toLp 2 (fun i : Fin (k + 1) => (q i).eval γ) :
        EuclideanSpace ℝ (Fin (k + 1)))‖) ^ 2 := by rw [div_pow, one_pow, one_div]
    _ ≤ ‖(WithLp.toLp 2 (fun i : Fin (k + 1) => c i) :
        EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2 := by gcongr

/-! ### The normal equations -/

/-- The **normal equations of the least-squares problem**. Let $B$ be a symmetric bilinear form on
$\mathbb{R}[X]$, let $(q_i)$ be orthonormal for $B$ with $\deg q_i = i$ for every $i$, let
$k \in \mathbb{N}$ with $\sum_{i=0}^{k} q_i(0)^2 \neq 0$, and let $R = K_k(0)$ be the kernel
polynomial at $0$. Then
$$B(X p, R) = 0$$
for every polynomial $p$ of degree less than $k$.

Thus the residual polynomials are orthogonal for the shifted form $(p, r) \mapsto B(X p, r)$.
The proof varies $R$ along the directions $X p$, which are the directions that keep both the
bound $\deg \le k$ and the value $1$ at $0$. -/
theorem bilinForm_kernelPolynomial_mul_X (hsymm : B.IsSymm)
    (horth : B.IsOrthonormal q) (hdeg : ∀ i, (q i).degree = i)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0)
    {p : ℝ[X]} (hp : p.degree < (k : WithBot ℕ)) :
    B (X * p) (kernelPolynomial q 0 k) = 0 := by
  have hddeg : (X * p).degree ≤ (k : WithBot ℕ) := by
    rcases eq_or_ne p 0 with rfl | h0
    · simp
    rw [degree_eq_natDegree h0] at hp
    have hn : p.natDegree < k := by exact_mod_cast hp
    rw [degree_mul, degree_X, degree_eq_natDegree h0,
      show (1 : WithBot ℕ) + (p.natDegree : WithBot ℕ) = ((1 + p.natDegree : ℕ) : WithBot ℕ) by
        push_cast; ring]
    exact_mod_cast (by omega : 1 + p.natDegree ≤ k)
  have hdeval : (X * p).eval 0 = 0 := by rw [eval_mul, eval_X, zero_mul]
  have hmin := (bilinForm_kernelPolynomial_le horth hdeg hS).2
  -- the quadratic `t ↦ B (R + t X p) (R + t X p) - B R R` is nonnegative, so its discriminant
  -- `(2 B (X p) R) ^ 2` is nonpositive
  suffices h : ∀ t : ℝ,
      0 ≤ B (X * p) (X * p) * (t * t) + 2 * B (X * p) (kernelPolynomial q 0 k) * t + 0 by
    have hd := discrim_le_zero h
    rw [discrim] at hd
    nlinarith [sq_nonneg (B (X * p) (kernelPolynomial q 0 k))]
  intro t
  have hadm : (kernelPolynomial q 0 k + t • (X * p)).degree ≤ (k : WithBot ℕ) :=
    (degree_add_le _ _).trans
      (max_le (kernelPolynomial_degree_le hdeg 0 k) ((degree_smul_le _ _).trans hddeg))
  have hev : (kernelPolynomial q 0 k + t • (X * p)).eval 0 = 1 := by
    rw [eval_add, eval_smul, kernelPolynomial_eval hS, hdeval, smul_zero, add_zero]
  have hexp : B (kernelPolynomial q 0 k + t • (X * p)) (kernelPolynomial q 0 k + t • (X * p)) =
      B (kernelPolynomial q 0 k) (kernelPolynomial q 0 k) +
        (2 * t * B (X * p) (kernelPolynomial q 0 k) + t ^ 2 * B (X * p) (X * p)) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsymm.eq (kernelPolynomial q 0 k) (X * p)]
    ring
  have hle := hmin ⟨kernelPolynomial q 0 k + t • (X * p), hadm, hev, rfl⟩
  rw [hexp, bilinForm_kernelPolynomial_self horth hS] at hle
  linarith

/-! ### The geometric bound -/

/-- The **geometric bound for the kernel polynomial**. Let $B$ be a bilinear form on
$\mathbb{R}[X]$, let $(q_i)$ be orthonormal for $B$ with $\deg q_i = i$ for every $i$, and let
$0 < \alpha < \beta$. Suppose that $B$ is supported on $[\alpha, \beta]$ in the sense that
$$B(p, p) \le \Bigl(\sup_{t \in [\alpha, \beta]} |p(t)|\Bigr)^2 B(1, 1) \quad \text{for every }
  p \in \mathbb{R}[X].$$
Let $k \in \mathbb{N}$ with $\sum_{i=0}^{k} q_i(0)^2 \neq 0$, and let $R = K_k(0)$ be the kernel
polynomial at $0$. Then
$$B(R, R) \le \Bigl(\frac{\beta - \alpha}{\beta + \alpha}\Bigr)^{2k} B(1, 1).$$

This is the geometric bound of [saad2003iterative], §12.3.3. The weighted form
$B(p, r) = \int_\alpha^\beta p r w$ with $w \ge 0$ satisfies the hypothesis by monotonicity of
the integral. The proof compares $R$ with the admissible competitor $(1 - X/\theta)^k$,
$\theta = (\alpha + \beta)/2$, whose supremum on $[\alpha, \beta]$ is at most $\bigl((\beta -
\alpha)/(\beta + \alpha)\bigr)^k$. -/
theorem bilinForm_kernelPolynomial_le_pow
    (horth : B.IsOrthonormal q) (hdeg : ∀ i, (q i).degree = i)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hB : ∀ p : ℝ[X], B p p ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * B 1 1)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0) :
    B (kernelPolynomial q 0 k) (kernelPolynomial q 0 k) ≤
      ((β - α) / (β + α)) ^ (2 * k) * B 1 1 := by
  have hθpos : (0 : ℝ) < (α + β) / 2 := by linarith
  have hsum : (0 : ℝ) < β + α := by linarith
  set P : ℝ[X] := (1 - C ((α + β) / 2)⁻¹ * X) ^ k with hP
  have hPdeg : P.degree ≤ (k : WithBot ℕ) := by
    refine degree_le_of_natDegree_le (natDegree_pow_le.trans ?_)
    have h1 : (1 - C ((α + β) / 2)⁻¹ * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
    simpa using Nat.mul_le_mul_left k h1
  have hPeval : ∀ t : ℝ, P.eval t = (1 - ((α + β) / 2)⁻¹ * t) ^ k := by
    intro t; rw [hP]; simp
  have hP0 : P.eval 0 = 1 := by rw [hPeval]; simp
  have hsuple : sSup ((fun t => |P.eval t|) '' Set.Icc α β) ≤ ((β - α) / (β + α)) ^ k := by
    refine csSup_le ((Set.nonempty_Icc.mpr hαβ.le).image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    dsimp only
    rw [hPeval, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ k
    have hform : 1 - ((α + β) / 2)⁻¹ * t = ((α + β) / 2 - t) / ((α + β) / 2) := by
      rw [sub_div, div_self hθpos.ne', inv_mul_eq_div]
    have hprod : (β - α) / (β + α) * ((α + β) / 2) = (β - α) / 2 := by
      field_simp; ring
    rw [hform, abs_div, abs_of_pos hθpos, div_le_iff₀ hθpos, hprod, abs_le]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsupnonneg : 0 ≤ sSup ((fun t => |P.eval t|) '' Set.Icc α β) :=
    le_csSup_of_le (isCompact_Icc.image P.continuous.abs).bddAbove
      ⟨α, Set.left_mem_Icc.mpr hαβ.le, rfl⟩ (abs_nonneg _)
  have hB11 : 0 ≤ B 1 1 :=
    bilinForm_self_nonneg_of_degree_le horth hdeg
      (degree_one_le.trans (by exact_mod_cast Nat.zero_le k))
  have hmin := (bilinForm_kernelPolynomial_le horth hdeg hS).2 ⟨P, hPdeg, hP0, rfl⟩
  rw [bilinForm_kernelPolynomial_self horth hS]
  calc (∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2)⁻¹ ≤ B P P := hmin
    _ ≤ sSup ((fun t => |P.eval t|) '' Set.Icc α β) ^ 2 * B 1 1 := hB P
    _ ≤ (((β - α) / (β + α)) ^ k) ^ 2 * B 1 1 := by gcongr
    _ = ((β - α) / (β + α)) ^ (2 * k) * B 1 1 := by rw [← pow_mul, mul_comm k 2]

end Bilin

end Polynomial
