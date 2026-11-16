/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Numlib.Algebra.Order.BigOperators.Ring.Finset
import Numlib.Analysis.InnerProductSpace.GramDeterminant
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Analysis.SpecialFunctions.Exp
import Numlib.Approximation.OrthogonalPolynomial
import Numlib.LinearAlgebra.Matrix.Cauchy

/-!
# The Müntz–Szász theorem in $L^2(0, 1)$

Let $0 < \lambda_0 < \lambda_1 < \cdots$ be real exponents with $\lambda_j \to \infty$. The
**Müntz–Szász theorem** says that the span of the powers $t \mapsto t^{\lambda_j}$ is dense in
$L^2(0, 1)$ if and only if $\sum_j 1/\lambda_j = \infty$. This is Theorem 3.1.5 of
[han2009theoretical]. Mathlib has neither the Müntz–Szász theorem nor a theory of Hardy spaces, and
the proof here is the classical one through Gram determinants.

The key formula is the distance in $L^2(0, 1)$ from a power $t^a$ to the span of finitely many
distinct powers $t^{l_0}, \dots, t^{l_{n-1}}$, with all exponents greater than $-1/2$:
$$d^2 = \frac{1}{2a + 1} \prod_{i < n} \Bigl(\frac{a - l_i}{a + l_i + 1}\Bigr)^2.$$

## Main definitions

* `Muntz.powerL2`: the power $t \mapsto t^l$ as an element of $L^2(0, 1)$, and $0$ when
  $l \le -1/2$, where the power is not square integrable.

## Main results

* `Muntz.inner_powerL2`: $\langle t^a, t^b \rangle = 1/(a + b + 1)$ for $a, b > -1/2$.
* `Muntz.linearIndependent_powerL2`: distinct powers are linearly independent.
* `Muntz.dist_sq_powerL2`: the squared distance from $t^a$ to the span of
  $t^{l_0}, \dots, t^{l_{n-1}}$ is $(2a + 1)^{-1} \prod_i ((a - l_i)/(a + l_i + 1))^2$.
* `Muntz.dense_span_powerL2_natCast`: the monomials $t^m$, $m \in \mathbb{N}$, span a dense subspace
  of $L^2(0, 1)$.
* `Muntz.dense_span_powerL2_iff`: the Müntz–Szász theorem.

## Proof outline

By `Muntz.inner_powerL2`, the Gram matrix of a finite family of powers is a Cauchy matrix
(`Matrix.cauchy`), whose determinant is given by `Matrix.det_cauchy`. Gram's formula for the
distance to a span, `Submodule.norm_sub_starProjection_sq_eq_det_gram_div_real`, writes the squared
best approximation error as a quotient of two such determinants, and the quotient simplifies to the
product above.

The rest is real analysis of that product. Since $1 - (\lambda_i - a)/(\lambda_i + a + 1) = (2a +
1)/(\lambda_i + a + 1)$ is comparable to $1/\lambda_i$, the product tends to $0$ exactly when
$\sum_i 1/\lambda_i$ diverges. The inequality $1 - x \le e^{-x}$ gives the vanishing, and the
Weierstrass product inequality $1 - \sum_i b_i \le \prod_i (1 - b_i)$ gives the lower bound. For the
direction "divergence implies density", the vanishing is applied at every natural number $a = m$,
and the density of the polynomials in $L^2(0, 1)$ finishes the proof. That density is
`OrthogonalPolynomial.IsWeight.denseRange_toLpₗ` for Lebesgue measure on $(0, 1)$. For the converse
direction, the lower bound is applied at one exponent $a$ strictly between $\lambda_0$ and
$\lambda_1$.

## Implementation notes

* $L^2(0, 1)$ is `Lp ℝ 2 (volume.restrict (Set.Ioo 0 1))`, the real space $L^2$ of Lebesgue measure
  on the open interval $(0, 1)$.
* The divergence of $\sum_j 1/\lambda_j$ is stated as `¬ Summable fun j ↦ (lam j)⁻¹`. The terms are
  positive, so the two conditions agree.
-/

open Filter MeasureTheory Set Submodule

open scoped Topology

namespace Muntz

/-- The measure of $L^2(0, 1)$: Lebesgue measure restricted to the open interval $(0, 1)$. -/
local notation "μ₁" => MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)

private theorem aestronglyMeasurable_rpow (l : ℝ) :
    AEStronglyMeasurable (fun t : ℝ ↦ t ^ l) μ₁ :=
  (ContinuousOn.rpow_const continuousOn_id fun _ (hx : _ ∈ Set.Ioo (0 : ℝ) 1) ↦
    Or.inl (ne_of_gt hx.1)).aestronglyMeasurable measurableSet_Ioo

/-- For real $a, b$ with $a + b > -1$, $\int_0^1 t^a t^b \, dt = 1/(a + b + 1)$. -/
private theorem integral_rpow_mul_rpow {a b : ℝ} (h : -1 < a + b) :
    ∫ t in Ioo (0:ℝ) 1, t ^ a * t ^ b = 1 / (a + b + 1) := by
  have hc : ∀ t ∈ Ioo (0:ℝ) 1, t ^ a * t ^ b = t ^ (a + b) :=
    fun t ht ↦ (Real.rpow_add ht.1 a b).symm
  rw [setIntegral_congr_fun measurableSet_Ioo hc, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl h), Real.one_rpow,
    Real.zero_rpow (by linarith), sub_zero]

/-- For real $l > -1/2$, the power function $t \mapsto t^l$ is square integrable on $(0, 1)$. -/
theorem memLp_rpow {l : ℝ} (hl : -(1 / 2 : ℝ) < l) : MemLp (fun t : ℝ ↦ t ^ l) 2 μ₁ := by
  rw [memLp_two_iff_integrable_sq (aestronglyMeasurable_rpow l)]
  have hc : ∀ t ∈ Ioo (0:ℝ) 1, (t ^ l) ^ 2 = t ^ (2 * l) := by
    intro t ht
    rw [← Real.rpow_natCast (t ^ l) 2, ← Real.rpow_mul ht.1.le]
    norm_num
    ring_nf
  rw [← IntegrableOn, integrableOn_congr_fun hc measurableSet_Ioo]
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)

/-- For real $l$, `Muntz.powerL2 l` is the **power function** $t \mapsto t^l$ as an element of
$L^2(0, 1)$ if $l > -1/2$.

For $l \le -1/2$ the power is not square integrable, and the definition gives $0$. Every use in
this module has $l > -1/2$. -/
noncomputable def powerL2 (l : ℝ) : Lp ℝ 2 μ₁ :=
  if h : -(1 / 2 : ℝ) < l then (memLp_rpow h).toLp _ else 0

/-- For real $l > -1/2$, the element `Muntz.powerL2 l` of $L^2(0, 1)$ is represented almost
everywhere by the function $t \mapsto t^l$. -/
theorem coeFn_powerL2 {l : ℝ} (hl : -(1 / 2 : ℝ) < l) : powerL2 l =ᵐ[μ₁] fun t ↦ t ^ l := by
  have h : powerL2 l = (memLp_rpow hl).toLp _ := dite_eq_iff.2 (Or.inl ⟨hl, rfl⟩)
  rw [h]
  exact MemLp.coeFn_toLp _

/-- For real $a, b > -1/2$, the inner product of two powers in $L^2(0, 1)$ is
$$\langle t^a, t^b \rangle = \int_0^1 t^a t^b \, dt = \frac{1}{a + b + 1}.$$
-/
theorem inner_powerL2 {a b : ℝ} (ha : -(1 / 2 : ℝ) < a) (hb : -(1 / 2 : ℝ) < b) :
    inner ℝ (powerL2 a) (powerL2 b) = 1 / (a + b + 1) := by
  rw [L2.inner_def, ← integral_rpow_mul_rpow (a := a) (b := b) (by linarith)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_powerL2 ha, coeFn_powerL2 hb] with t h1 h2
  rw [h1, h2, RCLike.inner_apply]
  simp [mul_comm]

/-- For exponents $m_i > -1/2$, the Gram matrix of the powers $t^{m_i}$ in $L^2(0, 1)$ is the Cauchy
matrix $((m_i + 1/2) + (m_j + 1/2))^{-1}$. -/
private theorem gram_powerL2 {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, -(1 / 2 : ℝ) < m i) :
    Matrix.gram ℝ (fun i ↦ powerL2 (m i))
      = Matrix.cauchy (fun i ↦ m i + 1 / 2) (fun i ↦ m i + 1 / 2) := by
  ext i j
  rw [Matrix.gram_apply, inner_powerL2 (hm i) (hm j), Matrix.cauchy_apply, one_div]
  congr 1
  ring

/-- For exponents $m_i > -1/2$, the Gram determinant of the powers $t^{m_i}$ is $\prod_{i < j}
(m_j - m_i)^2 / \prod_{i, j} (m_i + m_j + 1)$. -/
private theorem det_gram_powerL2 {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, -(1 / 2 : ℝ) < m i) :
    (Matrix.gram ℝ fun i ↦ powerL2 (m i)).det
      = (∏ i, ∏ j ∈ Finset.Ioi i, ((m j - m i) * (m j - m i)))
        / ∏ i, ∏ j, (m i + m j + 1) := by
  rw [gram_powerL2 m hm,
    Matrix.det_cauchy _ _ fun i j ↦ ne_of_gt (by have := hm i; have := hm j; linarith)]
  congr 1
  · exact Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr rfl fun j _ ↦ by ring
  · exact Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr rfl fun j _ ↦ by ring

/-- Let $m_0, \dots, m_{n-1}$ be distinct real numbers with $m_i > -1/2$ for all $i$. Then the
powers $t^{m_0}, \dots, t^{m_{n-1}}$ are linearly independent in $L^2(0, 1)$.

The proof uses that their Gram matrix is a Cauchy matrix with distinct nodes, so its determinant
is not zero. -/
theorem linearIndependent_powerL2 {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, -(1 / 2 : ℝ) < m i)
    (hinj : Function.Injective m) : LinearIndependent ℝ (fun i ↦ powerL2 (m i)) := by
  refine Matrix.det_gram_ne_zero_iff_linearIndependent.1 ?_
  rw [gram_powerL2 m hm]
  exact Matrix.det_cauchy_ne_zero (fun i j ↦ ne_of_gt (by have := hm i; have := hm j; linarith))
    (fun i j h ↦ hinj (by simpa using h)) (fun i j h ↦ hinj (by simpa using h))

/-- A product over the pairs $i < j$ in `Fin (n + 1)`, for the family `Fin.cons a l`, splits into
the factors with $i = 0$ and a product over the pairs $i < j$ for $l$. -/
private theorem prod_Ioi_cons {M : Type*} [CommMonoid M] {n : ℕ} (g : ℝ → ℝ → M) (a : ℝ)
    (l : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
        g ((Fin.cons a l : Fin (n + 1) → ℝ) i) ((Fin.cons a l : Fin (n + 1) → ℝ) j))
      = (∏ j, g a (l j)) * ∏ i, ∏ j ∈ Finset.Ioi i, g (l i) (l j) := by
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_Ioi_zero]; simp
  · exact Finset.prod_congr rfl fun i _ ↦ by rw [Fin.prod_Ioi_succ]; simp

/-- A double product over `Fin (n + 1)`, for the family `Fin.cons a l`, splits into the factors that
involve $a$ and a double product for $l$. -/
private theorem prod_prod_cons {M : Type*} [CommMonoid M] {n : ℕ} (g : ℝ → ℝ → M) (a : ℝ)
    (l : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j : Fin (n + 1),
        g ((Fin.cons a l : Fin (n + 1) → ℝ) i) ((Fin.cons a l : Fin (n + 1) → ℝ) j))
      = (g a a * ∏ j, g a (l j)) * ∏ i, (g (l i) a * ∏ j, g (l i) (l j)) := by
  simp [Fin.prod_univ_succ]

/-- An algebraic identity that turns the quotient of the two Cauchy determinants into the Müntz
product. -/
private theorem ratio_algebra {A N P Q D a : ℝ} (hN : N ≠ 0) (hD : D ≠ 0) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (ha : 2 * a + 1 ≠ 0) :
    ((A * N) / (((a + a + 1) * P) * (Q * D))) / (N / D) = (2 * a + 1)⁻¹ * (A / (P * Q)) := by
  rw [show a + a + 1 = 2 * a + 1 by ring]
  field_simp

/-- Let $l_0, \dots, l_{n-1}$ be distinct real numbers with $l_i > -1/2$ for all $i$, and let
$a > -1/2$. Then the squared distance in $L^2(0, 1)$ from $t^a$ to the span $V$ of
$t^{l_0}, \dots, t^{l_{n-1}}$ is
$$\|t^a - P_V t^a\|^2 = \frac{1}{2a + 1} \prod_{i < n} \Bigl(\frac{a - l_i}{a + l_i +
  1}\Bigr)^2,$$
where $P_V$ is the orthogonal projection onto $V$.

The projection $P_V$ is `Submodule.starProjection`. The proof evaluates Gram's determinant
formula `Submodule.norm_sub_starProjection_sq_eq_det_gram_div_real` with the Cauchy determinant
`Matrix.det_cauchy`. -/
theorem dist_sq_powerL2 {n : ℕ} (l : Fin n → ℝ) (a : ℝ) (hl : ∀ i, -(1 / 2 : ℝ) < l i)
    (ha : -(1 / 2 : ℝ) < a) (hinj : Function.Injective l) :
    ‖powerL2 a
        - (Submodule.span ℝ (Set.range fun i ↦ powerL2 (l i))).starProjection (powerL2 a)‖ ^ 2
      = (2 * a + 1)⁻¹ * ∏ i, ((a - l i) / (a + l i + 1)) ^ 2 := by
  have hm : ∀ i, -(1 / 2 : ℝ) < (Fin.cons a l : Fin (n + 1) → ℝ) i := by
    intro i
    induction i using Fin.cases with
    | zero => simpa using ha
    | succ i => simpa using hl i
  have hcons : (Fin.cons (powerL2 a) fun i ↦ powerL2 (l i))
      = fun i ↦ powerL2 ((Fin.cons a l : Fin (n + 1) → ℝ) i) := by
    funext i; induction i using Fin.cases <;> simp
  have hN0 : (∏ i, ∏ j ∈ Finset.Ioi i, ((l j - l i) * (l j - l i))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ ↦ Finset.prod_ne_zero_iff.2 fun j hj ↦ ?_
    have h : l j ≠ l i := fun h ↦ absurd (hinj h) (Finset.mem_Ioi.1 hj).ne'
    exact mul_ne_zero (sub_ne_zero.2 h) (sub_ne_zero.2 h)
  have hD0 : (∏ i, ∏ j : Fin n, (l i + l j + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ Finset.prod_ne_zero_iff.2 fun j _ ↦
      ne_of_gt (by have := hl i; have := hl j; linarith)
  have hS : ∀ i, (a + l i + 1) ≠ 0 := fun i ↦ ne_of_gt (by have := hl i; linarith)
  have ha2 : (2 * a + 1) ≠ 0 := ne_of_gt (by linarith)
  rw [Submodule.norm_sub_starProjection_sq_eq_det_gram_div_real
    (linearIndependent_powerL2 l hl hinj), Matrix.det_gram_sumElim_eq_det_gram_cons, hcons,
    det_gram_powerL2 _ hm, det_gram_powerL2 l hl,
    prod_Ioi_cons (fun x y ↦ (y - x) * (y - x)) a l,
    prod_prod_cons (fun x y ↦ x + y + 1) a l]
  have hsplit : (∏ i, ((l i + a + 1) * ∏ j : Fin n, (l i + l j + 1)))
      = (∏ i, (l i + a + 1)) * ∏ i, ∏ j : Fin n, (l i + l j + 1) := Finset.prod_mul_distrib
  rw [hsplit]
  have hR : (∏ i, ((a - l i) / (a + l i + 1)) ^ 2)
      = (∏ i, ((l i - a) * (l i - a))) / ((∏ j, (a + l j + 1)) * ∏ i, (l i + a + 1)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [div_pow]; congr 1 <;> ring
  rw [hR]
  have hP : (∏ j : Fin n, (a + l j + 1)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hS i
  have hQ : (∏ i : Fin n, (l i + a + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ ne_of_gt (by have := hl i; linarith)
  exact ratio_algebra hN0 hD0 hP hQ ha2

/-! ### The Müntz products -/

section Products

variable {a : ℝ} {l : ℕ → ℝ} {i : ℕ}

/-- For $a \ge 0$ and $l_i > 0$, the $i$-th factor $((a - l_i)/(a + l_i + 1))^2$ of the Müntz
product is at most $1$. -/
private theorem muntzFactor_le_one (ha : 0 ≤ a) (hl : 0 < l i) :
    ((a - l i) / (a + l i + 1)) ^ 2 ≤ 1 := by
  rw [div_pow, div_le_one (by positivity)]
  nlinarith [abs_nonneg (a - l i)]

/-- For $a \ge 0$ and $l_i > 0$, the $i$-th factor of the Müntz product is $(1 - b_i)^2$ with
$b_i = (2a + 1)/(l_i + a + 1)$, a quantity comparable to $1/l_i$. -/
private theorem muntzFactor_eq (ha : 0 ≤ a) (hl : 0 < l i) :
    ((a - l i) / (a + l i + 1)) ^ 2 = (1 - (2 * a + 1) / (l i + a + 1)) ^ 2 := by
  have h : l i + a + 1 ≠ 0 := by positivity
  rw [show (1 : ℝ) - (2 * a + 1) / (l i + a + 1) = (l i - a) / (l i + a + 1) by field_simp; ring,
    div_pow, div_pow]
  congr 1 <;> ring

/-- If $a \ge 0$, all $l_j > 0$, $l_j \to \infty$ and $\sum_j 1/l_j$ diverges, then the Müntz
products $\prod_{i < n} ((a - l_i)/(a + l_i + 1))^2$ tend to $0$ as $n \to \infty$. -/
private theorem tendsto_muntzProd (ha : 0 ≤ a) (hl : ∀ j, 0 < l j)
    (htop : Tendsto l atTop atTop) (hns : ¬ Summable fun j ↦ (l j)⁻¹) :
    Tendsto (fun n ↦ ∏ i ∈ Finset.range n, ((a - l i) / (a + l i + 1)) ^ 2) atTop (𝓝 0) := by
  obtain ⟨I, hI⟩ := (tendsto_atTop.1 htop (a + 1)).exists_forall_of_atTop
  set b : ℕ → ℝ := fun k ↦ (2 * a + 1) / (l (k + I) + a + 1) with hbdef
  have hlI : ∀ k, a + 1 ≤ l (k + I) := fun k ↦ hI (k + I) (Nat.le_add_left _ _)
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦ by
    have := hl (k + I); positivity
  have hb1 : ∀ k, b k ≤ 1 := fun k ↦ by
    rw [hbdef, div_le_one (by have := hl (k + I); positivity)]
    linarith [hlI k]
  have hdiv : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, b k) atTop atTop := by
    refine (not_summable_iff_tendsto_nat_atTop_of_nonneg hb0).1 fun hsum ↦ hns ?_
    refine (summable_nat_add_iff I).1 (Summable.of_nonneg_of_le (fun k ↦ by
      have := hl (k + I); positivity) (fun k ↦ ?_) (hsum.mul_left (2 / (2 * a + 1))))
    have h1 : (0:ℝ) < l (k + I) := hl (k + I)
    have key : (2 / (2 * a + 1)) * b k = 2 / (l (k + I) + a + 1) := by
      rw [hbdef]; field_simp
    rw [key, inv_eq_one_div, ← sub_nonneg,
      show 2 / (l (k + I) + a + 1) - 1 / l (k + I)
        = (l (k + I) - a - 1) / (l (k + I) * (l (k + I) + a + 1)) by field_simp; ring]
    exact div_nonneg (by linarith [hlI k]) (by positivity)
  have hprod : Tendsto (fun n ↦ ∏ k ∈ Finset.range n, (1 - b k)) atTop (𝓝 0) :=
    Real.tendsto_prod_one_sub_of_tendsto_sum hb1 hdiv
  have hshift : ∀ n, (∏ i ∈ Finset.range (n + I), ((a - l i) / (a + l i + 1)) ^ 2)
      = (∏ i ∈ Finset.range I, ((a - l i) / (a + l i + 1)) ^ 2)
        * (∏ k ∈ Finset.range n, (1 - b k)) ^ 2 := by
    intro n
    rw [add_comm n I, Finset.prod_range_add, ← Finset.prod_pow]
    refine congrArg _ (Finset.prod_congr rfl fun k _ ↦ ?_)
    rw [show I + k = k + I from Nat.add_comm I k]
    exact muntzFactor_eq ha (hl (k + I))
  rw [← tendsto_add_atTop_iff_nat I]
  refine Filter.Tendsto.congr (fun n ↦ (hshift n).symm) ?_
  simpa using (hprod.pow 2).const_mul
    (∏ i ∈ Finset.range I, ((a - l i) / (a + l i + 1)) ^ 2)

/-- If $a \ge 0$ and all $l_j > 0$, then the Müntz products
$\prod_{i < n} ((a - l_i)/(a + l_i + 1))^2$ decrease in $n$. -/
private theorem muntzProd_antitone (ha : 0 ≤ a) (hl : ∀ j, 0 < l j) :
    Antitone fun n ↦ ∏ i ∈ Finset.range n, ((a - l i) / (a + l i + 1)) ^ 2 := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [Finset.prod_range_succ]
  nlinarith [Finset.prod_nonneg (fun i (_ : i ∈ Finset.range n) ↦
      sq_nonneg ((a - l i) / (a + l i + 1))),
    muntzFactor_le_one (i := n) ha (hl n), sq_nonneg ((a - l n) / (a + l n + 1))]

/-- If $a \ge 0$, all $l_j > 0$, $l_j \to \infty$, $l_j \ne a$ for all $j$, and $\sum_j 1/l_j$
converges, then the Müntz products have a positive lower bound $\varepsilon$ that does not
depend on $n$. -/
private theorem muntzProd_bddBelow (ha : 0 ≤ a) (hl : ∀ j, 0 < l j)
    (htop : Tendsto l atTop atTop) (hne : ∀ j, l j ≠ a) (hsum : Summable fun j ↦ (l j)⁻¹) :
    ∃ ε > 0, ∀ n, ε ≤ ∏ i ∈ Finset.range n, ((a - l i) / (a + l i + 1)) ^ 2 := by
  set b : ℕ → ℝ := fun j ↦ (2 * a + 1) / (l j + a + 1) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j ↦ by have := hl j; positivity
  have hbsum : Summable b := by
    refine Summable.of_nonneg_of_le hb0 (fun j ↦ ?_) (hsum.mul_left (2 * a + 1))
    have h1 : (0:ℝ) < l j := hl j
    rw [hbdef, inv_eq_one_div, mul_one_div]
    exact div_le_div_of_nonneg_left (by linarith) h1 (by linarith)
  obtain ⟨I, hI⟩ := (tendsto_atTop.1 htop (a + 1)).exists_forall_of_atTop
  obtain ⟨J, hJI, hJ⟩ : ∃ J, I ≤ J ∧ ∑' k, b (k + J) ≤ 1 / 2 := by
    have h := (tendsto_sum_nat_add b).eventually
      (eventually_le_nhds (show (0:ℝ) < 1 / 2 by norm_num))
    obtain ⟨J, hJ⟩ := (h.and (eventually_ge_atTop I)).exists
    exact ⟨J, hJ.2, hJ.1⟩
  have hQJpos : 0 < ∏ i ∈ Finset.range J, ((a - l i) / (a + l i + 1)) ^ 2 := by
    refine Finset.prod_pos fun i _ ↦ ?_
    have h1 : (a - l i) / (a + l i + 1) ≠ 0 :=
      div_ne_zero (sub_ne_zero.2 fun h ↦ hne i h.symm) (by have := hl i; positivity)
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h1))
  refine ⟨(∏ i ∈ Finset.range J, ((a - l i) / (a + l i + 1)) ^ 2) / 4, by linarith, fun n ↦ ?_⟩
  rcases le_total n J with hn | hn
  · linarith [muntzProd_antitone ha hl hn]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hkey : (∏ i ∈ Finset.range (J + m), ((a - l i) / (a + l i + 1)) ^ 2)
        = (∏ i ∈ Finset.range J, ((a - l i) / (a + l i + 1)) ^ 2)
          * (∏ k ∈ Finset.range m, (1 - b (k + J))) ^ 2 := by
      rw [Finset.prod_range_add, ← Finset.prod_pow]
      refine congrArg _ (Finset.prod_congr rfl fun k _ ↦ ?_)
      rw [show J + k = k + J from Nat.add_comm J k]
      exact muntzFactor_eq ha (hl (k + J))
    have hlow : (1:ℝ) / 2 ≤ ∏ k ∈ Finset.range m, (1 - b (k + J)) := by
      have h1 : ∑ k ∈ Finset.range m, b (k + J) ≤ 1 / 2 :=
        le_trans (((summable_nat_add_iff J).2 hbsum).sum_le_tsum (Finset.range m)
          (fun k _ ↦ hb0 _)) hJ
      have h2 := Finset.one_sub_sum_le_prod_one_sub (Finset.range m) (fun k ↦ b (k + J))
        (fun k _ ↦ hb0 _) (fun k _ ↦ by
          rw [hbdef, div_le_one (by have := hl (k + J); positivity)]
          linarith [hI (k + J) (le_trans hJI (Nat.le_add_left _ _))])
      linarith
    rw [hkey]
    have hB : (1:ℝ) / 4 ≤ (∏ k ∈ Finset.range m, (1 - b (k + J))) ^ 2 := by nlinarith [hlow]
    nlinarith [hQJpos, hB]

end Products

/-! ### The polynomials are dense in $L^2(0, 1)$ -/

/-- Lebesgue measure on $(0, 1)$ is a weight in the sense of `OrthogonalPolynomial.IsWeight`, so the
polynomials lie in $L^2(0, 1)$ and are dense there. -/
private theorem isWeight_unit : OrthogonalPolynomial.IsWeight μ₁ :=
  OrthogonalPolynomial.isWeight_volume_restrict_Ioo zero_lt_one

/-- For $m \in \mathbb{N}$, the class in $L^2(0, 1)$ of the monomial $X^m$ is `Muntz.powerL2 m`. -/
private theorem toLpₗ_X_pow (m : ℕ) :
    isWeight_unit.toLpₗ (Polynomial.X ^ m) = powerL2 (m : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [isWeight_unit.coeFn_toLpₗ (Polynomial.X ^ m),
    coeFn_powerL2 (l := (m : ℝ)) (by linarith)]
    with t h1 h2
  rw [h1, h2, Polynomial.eval_pow, Polynomial.eval_X, Real.rpow_natCast]

/-- The monomials $t^m$, $m \in \mathbb{N}$, span a dense subspace of $L^2(0, 1)$.

The polynomials are dense in $L^2$ of a weight that is carried by a compact interval
(`OrthogonalPolynomial.IsWeight.denseRange_toLpₗ`). That result rests on Theorem 3.1.1 of
[han2009theoretical] and on the density of the bounded continuous functions in $L^2$. Every
polynomial is a linear combination of the monomials. -/
theorem dense_span_powerL2_natCast :
    Dense ((Submodule.span ℝ (Set.range fun m : ℕ ↦ powerL2 (m : ℝ)) :
      Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) := by
  have hsupp : μ₁ (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Icc.compl]
    exact measure_mono_null (fun x hx ↦ (hx.1 (Set.Ioo_subset_Icc_self hx.2)).elim) measure_empty
  refine (isWeight_unit.denseRange_toLpₗ hsupp).mono ?_
  rintro _ ⟨p, rfl⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | monomial n a =>
    rw [← Polynomial.smul_X_eq_monomial, map_smul, toLpₗ_X_pow]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-! ### The theorem -/

section Main

variable {lam : ℕ → ℝ}

/-- For $n \le n'$, the span of the first $n$ powers $t^{\lambda_i}$ is contained in the span of the
first $n'$ powers. -/
private theorem muntzFin_le {n n' : ℕ} (hn : n ≤ n') :
    Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))
      ≤ Submodule.span ℝ (Set.range fun i : Fin n' ↦ powerL2 (lam i)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, lt_of_lt_of_le i.2 hn⟩, rfl⟩

/-- For every $n$, the span of the first $n$ powers $t^{\lambda_i}$ is contained in the span of all
the powers $t^{\lambda_j}$. -/
private theorem muntzFin_le_span (n : ℕ) :
    Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))
      ≤ Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨i, rfl⟩

/-- Every element of the span of all the powers $t^{\lambda_j}$ lies in the span of the first $n$
powers for some $n$. -/
private theorem exists_mem_muntzFin {x : Lp ℝ 2 μ₁}
    (hx : x ∈ Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j))) :
    ∃ n, x ∈ Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i)) := by
  have hsub : Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j))
      ≤ ⨆ n, Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (j + 1)
      (Submodule.subset_span ⟨⟨j, Nat.lt_succ_self j⟩, rfl⟩)
  have hdir : Directed (· ≤ ·)
      fun n ↦ Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i)) :=
    fun n n' ↦ ⟨max n n', muntzFin_le (le_max_left n n'), muntzFin_le (le_max_right n n')⟩
  exact (Submodule.mem_iSup_of_directed _ hdir).1 (hsub hx)

/-- If all $\lambda_j > 0$, $\lambda$ is strictly increasing and $a \ge 0$, then the squared
distance from $t^a$ to the span of the first $n$ powers $t^{\lambda_i}$ is $(2a + 1)^{-1}
\prod_{i < n} ((a - \lambda_i)/(a + \lambda_i + 1))^2$. -/
private theorem norm_sub_starProjection_muntz (hlam : ∀ j, 0 < lam j) (hmono : StrictMono lam)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection
        (powerL2 a)‖ ^ 2
      = (2 * a + 1)⁻¹ * ∏ i ∈ Finset.range n, ((a - lam i) / (a + lam i + 1)) ^ 2 := by
  rw [dist_sq_powerL2 (fun i : Fin n ↦ lam i) a (fun i ↦ by linarith [hlam i]) (by linarith)
    (fun i j h ↦ Fin.val_injective (hmono.injective h))]
  exact congrArg _ (Fin.prod_univ_eq_prod_range (fun i ↦ ((a - lam i) / (a + lam i + 1)) ^ 2) n)

/-- If all $\lambda_j > 0$, $\lambda$ is strictly increasing, $\lambda_j \to \infty$ and
$\sum_j 1/\lambda_j$ diverges, then every power $t^a$ with $a \ge 0$ lies in the closure of the
span of the powers $t^{\lambda_j}$. -/
private theorem mem_closure_muntzSpan (hlam : ∀ j, 0 < lam j) (hmono : StrictMono lam)
    (htop : Tendsto lam atTop atTop) (hns : ¬ Summable fun j ↦ (lam j)⁻¹) {a : ℝ} (ha : 0 ≤ a) :
    powerL2 a ∈ closure ((Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j)) :
      Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) := by
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  have hsq : Tendsto (fun n ↦ ‖powerL2 a - (Submodule.span ℝ
      (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection (powerL2 a)‖ ^ 2)
      atTop (𝓝 0) := by
    simp_rw [norm_sub_starProjection_muntz hlam hmono ha]
    simpa using (tendsto_muntzProd ha hlam htop hns).const_mul (2 * a + 1)⁻¹
  obtain ⟨n, hn⟩ := (hsq.eventually (gt_mem_nhds (show (0:ℝ) < ε ^ 2 by positivity))).exists
  refine ⟨(Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection
    (powerL2 a), muntzFin_le_span n (Submodule.starProjection_apply_mem _ _), ?_⟩
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hn

/-- If all $\lambda_j > 0$, $\lambda$ is strictly increasing, $\lambda_j \to \infty$ and
$\sum_j 1/\lambda_j$ converges, then the span of the powers $t^{\lambda_j}$ is not dense in
$L^2(0, 1)$: its closure does not contain $t^a$ for $a$ strictly between $\lambda_0$ and
$\lambda_1$. -/
private theorem not_dense_muntzSpan (hlam : ∀ j, 0 < lam j) (hmono : StrictMono lam)
    (htop : Tendsto lam atTop atTop) (hs : Summable fun j ↦ (lam j)⁻¹) :
    ¬ Dense ((Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j)) :
      Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) := by
  have h01 : lam 0 < lam 1 := hmono (by norm_num)
  set a := (lam 0 + lam 1) / 2 with hadef
  have ha0 : 0 < a := by have := hlam 0; simp only [hadef]; linarith
  have hane : ∀ j, lam j ≠ a := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [hadef]; intro h; linarith
    · have h1 : lam 1 ≤ lam j := hmono.monotone hj
      simp only [hadef]; intro h; linarith
  obtain ⟨ε, hε, hbd⟩ := muntzProd_bddBelow ha0.le hlam htop hane hs
  intro hdense
  obtain ⟨y, hy, hlt⟩ := Metric.mem_closure_iff.1 (hdense (powerL2 a))
    (Real.sqrt ((2 * a + 1)⁻¹ * ε)) (Real.sqrt_pos.2 (by positivity))
  obtain ⟨n, hn⟩ := exists_mem_muntzFin hy
  have hmin := (isBestApprox_starProjection
    (Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))) (powerL2 a)).2 y hn
  have hge : (2 * a + 1)⁻¹ * ε
      ≤ ‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection
        (powerL2 a)‖ ^ 2 := by
    rw [norm_sub_starProjection_muntz hlam hmono ha0.le]
    exact mul_le_mul_of_nonneg_left (hbd n) (by positivity)
  have hsqrt : Real.sqrt ((2 * a + 1)⁻¹ * ε)
      ≤ ‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection
        (powerL2 a)‖ := by
    rw [show ‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦
        powerL2 (lam i))).starProjection (powerL2 a)‖
        = Real.sqrt (‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦
          powerL2 (lam i))).starProjection (powerL2 a)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hge
  rw [dist_eq_norm] at hlt
  linarith

/-- The **Müntz–Szász theorem**. Let $\lambda_0, \lambda_1, \dots$ be real numbers with
$0 < \lambda_0 < \lambda_1 < \cdots$ and $\lambda_j \to \infty$. Then the span of the powers
$t \mapsto t^{\lambda_j}$ is dense in $L^2(0, 1)$ if and only if
$$\sum_{j = 0}^{\infty} \frac{1}{\lambda_j} = \infty.$$
This is Theorem 3.1.5 of [han2009theoretical].

The divergence of the series is stated as `¬ Summable fun j ↦ (lam j)⁻¹`; the terms are
positive, so the two conditions agree. The hypothesis $0 < \lambda_0 < \lambda_1 < \cdots$ is
`0 < lam 0` together with `StrictMono lam`. -/
theorem dense_span_powerL2_iff (lam : ℕ → ℝ) (hpos : 0 < lam 0) (hmono : StrictMono lam)
    (htop : Tendsto lam atTop atTop) :
    Dense ((Submodule.span ℝ (Set.range fun j ↦ powerL2 (lam j)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁))
      ↔ ¬ Summable fun j ↦ (lam j)⁻¹ := by
  have hlam : ∀ j, 0 < lam j := fun j ↦ lt_of_lt_of_le hpos (hmono.monotone (Nat.zero_le j))
  refine ⟨fun hdense hs ↦ not_dense_muntzSpan hlam hmono htop hs hdense, fun hns ↦ ?_⟩
  have hmem : ∀ m : ℕ, powerL2 (m : ℝ) ∈
      closure ((Submodule.span ℝ (Set.range fun j ↦ powerL2 (lam j)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) :=
    fun m ↦ mem_closure_muntzSpan hlam hmono htop hns (Nat.cast_nonneg m)
  have hsub : ((Submodule.span ℝ (Set.range fun m : ℕ ↦ powerL2 (m : ℝ)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁))
      ⊆ closure ((Submodule.span ℝ (Set.range fun j ↦ powerL2 (lam j)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) := by
    rw [← Submodule.topologicalClosure_coe, SetLike.coe_subset_coe, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.topologicalClosure_coe] at *
    exact hmem m
  refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
  rw [← dense_span_powerL2_natCast.closure_eq]
  exact closure_minimal hsub isClosed_closure

end Main

end Muntz
