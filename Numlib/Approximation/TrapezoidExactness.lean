/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Integrals`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import Numlib.Analysis.Fourier.TrigonometricPolynomial

/-!
# The periodic trapezoidal rule is exact on trigonometric polynomials

Let $N \ge 1$, and let $\theta_m = 2\pi m / N$, $m = 0, \dots, N - 1$, be $N$ equispaced nodes in
one period. The trapezoidal rule with these nodes and the equal weights $2\pi / N$ integrates every
trigonometric polynomial $f$ of degree less than $N$ exactly:
$$\frac{2\pi}{N} \sum_{m=0}^{N-1} f(\theta_m) = \int_0^{2\pi} f(\theta) \, d\theta.$$

The reason is the pair of orthogonality relations for the character $\theta \mapsto e^{ip\theta}$,
$p \in \mathbb{Z}$. Its integral over a period vanishes unless $p = 0$, and its sum over the nodes
vanishes unless $N \mid p$. For $|p| < N$ the two conditions coincide, so the rule sees exactly the
constant term of $f$, which is what the integral sees.

## Main definitions

* `Quadrature.angleNode`: the node $\theta_m = 2\pi m / N$.

## Main results

* `Quadrature.sum_exp_angleNode`: the discrete orthogonality relation,
  $\sum_{m=0}^{N-1} e^{ip\theta_m}$ is $N$ if $N \mid p$ and $0$ otherwise. The continuous relation
  is `integral_exp_I_int_mul`.
* `Quadrature.trapezoid_eq_integral_of_expSum`: the rule is exact on every finite combination of
  characters $e^{ip\theta}$ with $|p| < N$.
* `Complex.cos_pow_mul_sin_pow_eq_expSum`: the expansion of $\cos^a z \sin^b z$ in characters
  $e^{ipz}$ with $|p| \le a + b$.
* `Quadrature.trapezoid_eq_integral_cos_pow_mul_sin_pow`: the rule is exact on
  $\cos^a \theta \sin^b \theta$ when $a + b < N$, the form that a product quadrature rule on a disk
  needs.

## Implementation notes

* The characters are indexed by $\mathbb{Z}$, and the degree bound is $|p| < N$ rather than $p < N$,
  so that $N \mid p$ is equivalent to $p = 0$ on the range that occurs.
* The character $e^{ip\theta}$ is written `Complex.exp (p * θ * I)`.
-/

open Complex Finset intervalIntegral MeasureTheory

open scoped Real

namespace Quadrature

/-- The $m$-th of the $N$ equispaced angles of one period, $\theta_m = 2\pi m / N$. For $N = 0$ the
value is $0$, because division by zero gives $0$. -/
noncomputable def angleNode (N m : ℕ) : ℝ := 2 * π * m / N

/-- The **discrete orthogonality of the characters**: let $N \ge 1$ and $p \in \mathbb{Z}$. Then
$$\sum_{m=0}^{N-1} e^{ip\theta_m} = \begin{cases} N & \text{if } N \mid p, \\ 0 &
  \text{otherwise,} \end{cases}$$
where $\theta_m = 2\pi m / N$.

The terms $e^{ip\theta_m}$ are the powers of the $N$-th root of unity $e^{2\pi i p / N}$. The
divisibility $N \mid p$ is divisibility in $\mathbb{Z}$. -/
theorem sum_exp_angleNode {N : ℕ} (hN : 0 < N) (p : ℤ) :
    ∑ m ∈ range N, Complex.exp (p * (angleNode N m : ℝ) * I)
      = if (N : ℤ) ∣ p then (N : ℂ) else 0 := by
  have hN' : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set ζ : ℂ := Complex.exp (2 * π * I / N) with hζ
  have hprim : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  set z : ℂ := ζ ^ (p : ℤ) with hz
  have hterm : ∀ m : ℕ, Complex.exp (p * (angleNode N m : ℝ) * I) = z ^ m := by
    intro m
    rw [hz, hζ, ← Complex.exp_int_mul, ← Complex.exp_nat_mul, angleNode]
    congr 1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun m _ => hterm m]
  have hzN : z ^ N = 1 := by
    rw [hz, ← zpow_natCast (ζ ^ (p : ℤ)) N, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hprim.pow_eq_one, one_zpow]
  by_cases hdvd : (N : ℤ) ∣ p
  · have hz1 : z = 1 := (hprim.zpow_eq_one_iff_dvd p).2 hdvd
    rw [ite_eq_left hdvd, hz1]
    simp
  · have hz1 : z ≠ 1 := fun h => hdvd ((hprim.zpow_eq_one_iff_dvd p).1 h)
    rw [ite_eq_right hdvd, geom_sum_eq hz1, hzN, sub_self, zero_div]

/-- The **exactness of the trapezoidal rule on trigonometric polynomials**: let $N \ge 1$, let $S$
be a finite index set, and let $c_j \in \mathbb{C}$ and $p_j \in \mathbb{Z}$ with $|p_j| < N$
for all $j \in S$. Then $f(\theta) = \sum_{j \in S} c_j e^{i p_j \theta}$ satisfies
$$\frac{2\pi}{N} \sum_{m=0}^{N-1} f(\theta_m) = \int_0^{2\pi} f(\theta) \, d\theta,$$
where $\theta_m = 2\pi m / N$.

The proof compares the two sides term by term with the discrete relation
`Quadrature.sum_exp_angleNode` and the continuous relation `integral_exp_I_int_mul`. -/
theorem trapezoid_eq_integral_of_expSum {ι : Type*} {N : ℕ} (hN : 0 < N) {s : Finset ι}
    {c : ι → ℂ} {p : ι → ℤ} (hp : ∀ i ∈ s, |p i| < (N : ℤ)) :
    ((2 * π / N : ℝ) : ℂ) * ∑ m ∈ range N, ∑ i ∈ s, c i * Complex.exp (p i * (angleNode N m) * I)
      = ∫ θ in (0 : ℝ)..(2 * π), ∑ i ∈ s, c i * Complex.exp (p i * θ * I) := by
  have hN' : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hdvd : ∀ i ∈ s, ((N : ℤ) ∣ p i ↔ p i = 0) := by
    intro i hi
    refine ⟨fun h => ?_, fun h => h ▸ dvd_zero _⟩
    exact Int.eq_zero_of_abs_lt_dvd h (hp i hi)
  rw [Finset.sum_comm]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.mul_sum, sum_exp_angleNode hN, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_congr (g := fun θ : ℝ => Complex.exp (I * p i * θ))
      fun θ _ => by simp only []; congr 1; ring,
    integral_exp_I_int_mul]
  by_cases h0 : p i = 0
  · rw [ite_eq_left h0, ite_eq_left ((hdvd i hi).2 h0)]
    push_cast
    field_simp
  · rw [ite_eq_right h0, ite_eq_right (fun hh => h0 ((hdvd i hi).1 hh))]
    simp

end Quadrature

namespace Complex

open Finset

/-- The expansion of $\cos^a z$ in characters: for $a \in \mathbb{N}$ and $z \in \mathbb{C}$,
$$\cos^a z = 2^{-a} \sum_{j=0}^{a} \binom{a}{j} e^{i(2j - a) z}.$$
-/
theorem cos_pow_eq_expSum (a : ℕ) (z : ℂ) :
    cos z ^ a = ∑ j ∈ range (a + 1),
      (a.choose j : ℂ) * (2 : ℂ)⁻¹ ^ a * Complex.exp (((2 * j - a : ℤ) : ℂ) * z * I) := by
  have hcos : cos z = (2 : ℂ)⁻¹ * Complex.exp (z * I) + (2 : ℂ)⁻¹ * Complex.exp (-z * I) := by
    rw [Complex.cos]
    ring
  rw [hcos, add_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  rw [mul_mul_mul_comm, ← pow_add, Nat.add_sub_cancel' hj', ← Complex.exp_add]
  rw [mul_comm ((2 : ℂ)⁻¹ ^ a) _, mul_assoc, mul_comm _ ((2 : ℂ)⁻¹ ^ a)]
  rw [show ((j : ℂ) * (z * I) + ((a - j : ℕ) : ℂ) * (-z * I))
      = ((2 * j - a : ℤ) : ℂ) * z * I by rw [Nat.cast_sub hj']; push_cast; ring]
  ring

/-- The expansion of $\sin^b z$ in characters: for $b \in \mathbb{N}$ and $z \in \mathbb{C}$,
$$\sin^b z = \sum_{k=0}^{b} \binom{b}{k} \left(\frac{i}{2}\right)^k
  \left(-\frac{i}{2}\right)^{b-k} e^{i(b - 2k) z}.$$
-/
theorem sin_pow_eq_expSum (b : ℕ) (z : ℂ) :
    sin z ^ b = ∑ k ∈ range (b + 1),
      ((b.choose k : ℂ) * (I / 2) ^ k * (-I / 2) ^ (b - k))
        * Complex.exp (((b - 2 * k : ℤ) : ℂ) * z * I) := by
  have hsin : sin z = I / 2 * Complex.exp (-z * I) + (-I / 2) * Complex.exp (z * I) := by
    rw [Complex.sin]
    ring
  rw [hsin, add_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  rw [show ((k : ℂ) * (-z * I) + ((b - k : ℕ) : ℂ) * (z * I))
      = ((b - 2 * k : ℤ) : ℂ) * z * I by rw [Nat.cast_sub hk']; push_cast; ring]
  ring

/-- The expansion of $\cos^a z \sin^b z$ in characters: for $a, b \in \mathbb{N}$ and
$z \in \mathbb{C}$,
$$\cos^a z \sin^b z = \sum_{j=0}^{a} \sum_{k=0}^{b} 2^{-a} \binom{a}{j} \binom{b}{k}
  \left(\frac{i}{2}\right)^k \left(-\frac{i}{2}\right)^{b-k} e^{i p_{jk} z}, \qquad p_{jk} =
  (2j - a) + (b - 2k).$$
Every exponent satisfies $|p_{jk}| \le a + b$.

The double sum is a sum over the product `range (a + 1) ×ˢ range (b + 1)`. -/
theorem cos_pow_mul_sin_pow_eq_expSum (a b : ℕ) (z : ℂ) :
    cos z ^ a * sin z ^ b
      = ∑ q ∈ range (a + 1) ×ˢ range (b + 1),
          ((a.choose q.1 : ℂ) * (2 : ℂ)⁻¹ ^ a
              * ((b.choose q.2 : ℂ) * (I / 2) ^ q.2 * (-I / 2) ^ (b - q.2)))
            * Complex.exp (((2 * q.1 - a + (b - 2 * q.2) : ℤ) : ℂ) * z * I) := by
  rw [cos_pow_eq_expSum, sin_pow_eq_expSum, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Complex

namespace Quadrature

open Finset

/-- The **exactness of the periodic trapezoidal rule on $\cos^a \theta \sin^b \theta$**: let
$a, b, N \in \mathbb{N}$ with $a + b < N$. Then
$$\frac{2\pi}{N} \sum_{m=0}^{N-1} \cos^a \theta_m \sin^b \theta_m = \int_0^{2\pi} \cos^a \theta
  \sin^b \theta \, d\theta,$$
where $\theta_m = 2\pi m / N$.

This is the angular half of a product quadrature rule on a disk: the $N$ equispaced angles with
the equal weights $2\pi / N$ integrate every such product exactly. The statement is over the
reals. The expansion behind it is `Complex.cos_pow_mul_sin_pow_eq_expSum`. -/
theorem trapezoid_eq_integral_cos_pow_mul_sin_pow {N a b : ℕ} (hN : a + b < N) :
    (2 * π / N) * ∑ m ∈ range N, Real.cos (angleNode N m) ^ a * Real.sin (angleNode N m) ^ b
      = ∫ θ in (0 : ℝ)..(2 * π), Real.cos θ ^ a * Real.sin θ ^ b := by
  have hN0 : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hN
  have hbound : ∀ q ∈ range (a + 1) ×ˢ range (b + 1),
      |(2 * (q.1 : ℤ) - a + (b - 2 * q.2) : ℤ)| < (N : ℤ) := by
    intro q hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hq
    have h1 : (q.1 : ℤ) ≤ a := by exact_mod_cast Nat.lt_succ_iff.mp hq.1
    have h2 : (q.2 : ℤ) ≤ b := by exact_mod_cast Nat.lt_succ_iff.mp hq.2
    have h5 : (a : ℤ) + b < N := by exact_mod_cast hN
    rw [abs_lt]
    constructor <;> omega
  have key := trapezoid_eq_integral_of_expSum (ι := ℕ × ℕ) hN0
    (s := range (a + 1) ×ˢ range (b + 1))
    (c := fun q => (a.choose q.1 : ℂ) * (2 : ℂ)⁻¹ ^ a
      * ((b.choose q.2 : ℂ) * (I / 2) ^ q.2 * (-I / 2) ^ (b - q.2)))
    (p := fun q => (2 * (q.1 : ℤ) - a + (b - 2 * q.2) : ℤ)) hbound
  have hsum : ((∑ m ∈ range N,
        Real.cos (angleNode N m) ^ a * Real.sin (angleNode N m) ^ b : ℝ) : ℂ)
      = ∑ m ∈ range N, ∑ q ∈ range (a + 1) ×ˢ range (b + 1),
          ((a.choose q.1 : ℂ) * (2 : ℂ)⁻¹ ^ a
              * ((b.choose q.2 : ℂ) * (I / 2) ^ q.2 * (-I / 2) ^ (b - q.2)))
            * Complex.exp (((2 * (q.1 : ℤ) - a + (b - 2 * q.2) : ℤ) : ℂ)
                * ((angleNode N m : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Complex.cos_pow_mul_sin_pow_eq_expSum a b ((angleNode N m : ℝ) : ℂ)]
    push_cast
    ring
  have hint : ((∫ θ in (0 : ℝ)..(2 * π), Real.cos θ ^ a * Real.sin θ ^ b : ℝ) : ℂ)
      = ∫ θ in (0 : ℝ)..(2 * π), ∑ q ∈ range (a + 1) ×ˢ range (b + 1),
          ((a.choose q.1 : ℂ) * (2 : ℂ)⁻¹ ^ a
              * ((b.choose q.2 : ℂ) * (I / 2) ^ q.2 * (-I / 2) ^ (b - q.2)))
            * Complex.exp (((2 * (q.1 : ℤ) - a + (b - 2 * q.2) : ℤ) : ℂ) * ((θ : ℝ) : ℂ) * I) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [← Complex.cos_pow_mul_sin_pow_eq_expSum a b ((θ : ℝ) : ℂ)]
    push_cast
    ring
  rw [← Complex.ofReal_inj, Complex.ofReal_mul, hsum, hint]
  exact key

end Quadrature
