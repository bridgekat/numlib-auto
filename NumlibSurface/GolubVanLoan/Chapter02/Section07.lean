/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Rat.Floor
import Numlib.FloatingPoint.InnerProduct
import Numlib.FloatingPoint.System
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter02.Section06

/-!
# Golub and Van Loan, Section 2.7: Finite precision matrix computations

This module formalizes §2.7 of [golub2013matrix] on floating point arithmetic and the rounding
errors of basic matrix computations. It describes two concrete number systems: a 3-digit decimal
calculator (§2.7.1) and the IEEE double format (2.7.2)–(2.7.3), with its machine epsilon $2^{-52}$
and the relative error bound $2^{-53}$ of rounding to nearest. It proves the model of floating point
arithmetic: $\operatorname{fl}(x) = x(1 + \delta)$ with $|\delta| \le u$ (2.7.4), $u$ is half the
gap between $1$ and the next floating point number (2.7.5), and $\operatorname{fl}(x \mathbin{op}
y) = (x \mathbin{op} y)(1 + \delta)$ (2.7.6). It shows that floating point addition is not
associative (Maxim 1), and bounds the error of storing a matrix (2.7.7). For the dot product it
proves the error recursion (2.7.9)–(2.7.10), Lemma 2.7.1, and the bounds $|\operatorname{fl}(x^T
y) - x^T y| \le 1.01 n u |x|^T |y|$ (2.7.11) and $\le \gamma_n |x|^T |y|$ (2.7.12), with
$\gamma_n = nu/(1 - nu)$. It then bounds the errors of scaling and addition (2.7.15)–(2.7.16), of
the saxpy and the outer product update (2.7.17)–(2.7.18), and of matrix multiplication
(2.7.19)–(2.7.20), proves the backward error form of the $2 \times 2$ triangular product of §2.7.9,
and analyses the ideal equation solver (2.7.21)–(2.7.22).

The proofs specialize the backbone modules `Numlib.FloatingPoint.Model`,
`Numlib.FloatingPoint.System` and `Numlib.FloatingPoint.InnerProduct`, and
`Numlib.Analysis.Matrix.OperatorNorm` for the bounds in norms.

## Main definitions

* §2.7.1, `GolubVanLoan.Chapter02.calculator3`: the 3-digit calculator as the number system
  $\mathbb{F}(10, 3, -8, 10)$.

## Main results

* §2.7.1, `GolubVanLoan.Chapter02.calculator3_card`: the calculator has $34201$ floating point
  numbers.
* §2.7.1, `GolubVanLoan.Chapter02.calculator3_range`: the smallest and the largest positive numbers
  of the calculator, and the spacing of its numbers.
* Equation (2.7.2), `GolubVanLoan.Chapter02.equation_2_7_2`: the normalized doubles
  $\pm (1.b_1 \dots b_{52})_2 \times 2^{E - 1023}$ are the nonzero numbers of the double system.
* Equation (2.7.3), `GolubVanLoan.Chapter02.equation_2_7_3`: the values
  $\pm (0.b_1 \dots b_{52})_2 \times 2^{-1022}$ are $0$ and the subnormal doubles.
* §2.7.2, `GolubVanLoan.Chapter02.ieeeDouble_constants`: the machine epsilon $2^{-52}$ and the
  extreme positive normalized doubles $2^{-1022}$ and $(2 - 2^{-52}) 2^{1023}$.
* §2.7.2, `GolubVanLoan.Chapter02.ieeeDouble_round_nearest`: rounding to nearest has relative error
  at most $2^{-53}$.
* Equation (2.7.4), `GolubVanLoan.Chapter02.equation_2_7_4` and
  `GolubVanLoan.Chapter02.equation_2_7_4_system`: $\operatorname{fl}(x) = x(1 + \delta)$ with
  $|\delta| \le u$.
* Equation (2.7.5), `GolubVanLoan.Chapter02.equation_2_7_5`: $u$ is half the gap between $1$ and the
  next floating point number, and its values for the IEEE formats.
* Equation (2.7.6), `GolubVanLoan.Chapter02.equation_2_7_6`: the fundamental axiom of floating point
  arithmetic.
* §2.7.4, Maxim 1, `GolubVanLoan.Chapter02.calculator3_add_not_assoc`: floating point addition is
  not associative.
* Equation (2.7.7), `GolubVanLoan.Chapter02.equation_2_7_7`: $|\operatorname{fl}(A) - A| \le u |A|$
  and $\|\operatorname{fl}(A) - A\|_1 \le u \|A\|_1$.
* Equation (2.7.9), `GolubVanLoan.Chapter02.equation_2_7_9`: the recursion of the rounding errors in
  the partial sums of a dot product.
* Equation (2.7.10), `GolubVanLoan.Chapter02.equation_2_7_10`: $\operatorname{fl}(x^T y) = \sum_k
  x_k y_k (1 + \gamma_k)$.
* Lemma 2.7.1, `GolubVanLoan.Chapter02.lemma_2_7_1`: if $1 + \alpha = \prod_{k=1}^n (1 + \alpha_k)$
  with $|\alpha_k| \le u$ and $nu \le 0.01$, then $|\alpha| \le 1.01 nu$.
* Equation (2.7.11), `GolubVanLoan.Chapter02.equation_2_7_11`: $|\operatorname{fl}(x^T y) - x^T y|
  \le 1.01 nu |x|^T |y|$.
* Equation (2.7.12), `GolubVanLoan.Chapter02.equation_2_7_12`: $|\operatorname{fl}(x^T y) - x^T y|
  \le \gamma_n |x|^T |y|$.
* Equations (2.7.15)–(2.7.16), `GolubVanLoan.Chapter02.equation_2_7_15` and
  `GolubVanLoan.Chapter02.equation_2_7_16`: the errors of $\operatorname{fl}(\alpha A)$ and
  $\operatorname{fl}(A + B)$.
* Equations (2.7.17)–(2.7.18), `GolubVanLoan.Chapter02.equation_2_7_17` and
  `GolubVanLoan.Chapter02.equation_2_7_18`: the errors of the saxpy and of the outer product update.
* Equation (2.7.19), `GolubVanLoan.Chapter02.equation_2_7_19`,
  `GolubVanLoan.Chapter02.equation_2_7_19_saxpy` and `GolubVanLoan.Chapter02.equation_2_7_19_outer`:
  $|\operatorname{fl}(AB) - AB| \le \gamma_r |A| |B|$ for the dot product, saxpy and outer product
  forms of matrix multiplication.
* Equation (2.7.20), `GolubVanLoan.Chapter02.equation_2_7_20`: $\|\operatorname{fl}(AB) - AB\|_1 \le
  \gamma_r \|A\|_1 \|B\|_1$.
* §2.7.9, `GolubVanLoan.Chapter02.triangular_mul_two_backward` and
  `GolubVanLoan.Chapter02.triangular_mul_two_backward_run`: the computed product of two $2 \times 2$
  upper triangular matrices is the exact product of slightly perturbed factors.
* §2.7.10, `GolubVanLoan.Chapter02.abs_sub_le_gamma_mul_abs_of_nonneg`: for $A, B \ge 0$, the
  computed product has small componentwise relative error.
* Equation (2.7.21), `GolubVanLoan.Chapter02.equation_2_7_21`: storing $A$ and $b$ gives
  $\|E\|_\infty \le u \|A\|_\infty$ and $\|e\|_\infty \le u \|b\|_\infty$.
* Equation (2.7.22), `GolubVanLoan.Chapter02.equation_2_7_22`: the ideal equation solver has
  relative error at most $4 u \kappa_\infty(A)$.

## Conventions

* `fp : FloatingPoint.RoundingModel ℝ` is the floating point arithmetic of the source, and `fp.u` is
  its unit roundoff $u$. A stored or computed value $\operatorname{fl}(x)$ is any $y$ with
  `fp.Rounds x y`, entrywise for matrices and vectors.
* Concrete arithmetic is a `FloatingPoint.System`, the number system $\mathbb{F}(\beta, t, L, U)$.
  Its rounding is `FloatingPoint.System.round`, and its machine operations are
  `FloatingPoint.System.op` and `FloatingPoint.System.add`.
* The source states first-order bounds with a term $O(u^2)$. The theorems state rigorous bounds with
  `FloatingPoint.gamma`, $\gamma_n = nu/(1 - nu) = nu + O(u^2)$, or with the $u^2$ term written out.
* The statements about the dot product (2.7.8)–(2.7.12), the saxpy and the outer product update
  (2.7.17)–(2.7.18), the matrix products (2.7.19)–(2.7.20), the remark on nonnegative factors of
  §2.7.10 and the $2 \times 2$ triangular product of §2.7.9 are about every run
  `s ∈ (alg fp.round …).run` of Algorithms 1.1.1, 1.1.2, 1.1.6–1.1.8 and 1.2.1 of Chapter 1, in the
  namespace `GolubVanLoan.Chapter01`.
* The source uses that the first addition $\operatorname{fl}(0 + p) = p$ of an accumulation is
  exact. This is the hypothesis `fp.IsIdempotent`. The rounding bridges of Chapter 1
  (`GolubVanLoan.Chapter01.algorithm_1_1_1_rounds`, `GolubVanLoan.Chapter01.algorithm_1_1_6_rounds`
  and the corresponding theorems for Algorithms 1.1.7 and 1.1.8, and the run characterizations
  `…_mem_run`) turn runs into the backbone relations `FloatingPoint.RoundsDot` and
  `FloatingPoint.RoundsMul`.

## Not formalized

* **The IEEE bit layout (2.7.1).** It is notation.
* **The sample roundings of §2.7.1.**
* **The values $\pm\infty$ and NaN, the exceptions, and the directed rounding modes of §2.7.2.** The
  tie rule of rounding to nearest is covered by allowing any nearest element.
* **Maxims 2 and 3 of §2.7.4.**
* **The styles of error analysis (2.7.13)–(2.7.14).**
* **The quotation of Wilkinson.**
* **The claims about the Strassen method in §2.7.10.** They have no stated constant.
-/

open Finset Matrix FloatingPoint WithLp
open scoped ENNReal

namespace GolubVanLoan.Chapter02

variable {m n : ℕ}

/-! ### §2.7.1 A 3-digit calculator -/

/-- **Section 2.7.1** of [golub2013matrix], the 3-digit calculator. The calculator represents the
numbers $\pm d_0.d_1 d_2 \times 10^e$ with digits $d_i$, $1 \le d_0 \le 9$ and $-9 \le e \le 9$,
together with $0$. It is the number system $\mathbb{F}(10, 3, -8, 10)$.

The backbone writes the numbers as $\pm 0.d_0 d_1 d_2 \times 10^{e+1}$, which shifts the
exponent range by one. -/
def calculator3 : System :=
  ⟨10, 3, -8, 10, by norm_num, by norm_num, by norm_num⟩

/-- **Section 2.7.1** of [golub2013matrix]. The 3-digit calculator has
$$2 \times 9 \times 10 \times 10 \times 19 + 1 = 34201$$
floating point numbers. -/
theorem calculator3_card : ((calculator3.finset ℝ).card : ℤ) = 34201 := by
  rw [System.card_finset]
  norm_num [calculator3]

/-- **Section 2.7.1** of [golub2013matrix]. The smallest and the largest positive numbers of the
3-digit calculator are $N_{\min} = 1.00 \times 10^{-9}$ and $N_{\max} = 9.99 \times 10^9$. For
$-9 \le e \le 9$, the numbers of the calculator in $[10^e, 10^{e+1})$ are exactly the numbers
$m \times 10^{e-2}$ with $100 \le m \le 999$, so their spacing is $10^{e-2}$. -/
theorem calculator3_range :
    calculator3.xmin ℝ = 10 ^ (-9 : ℤ) ∧ calculator3.xmax ℝ = 999 / 100 * 10 ^ 9 ∧
      ∀ e : ℤ, -9 ≤ e → e ≤ 9 →
        calculator3.numbers ℝ ∩ Set.Ico ((10 : ℝ) ^ e) (10 ^ (e + 1)) =
          (fun m : ℕ => (m : ℝ) * 10 ^ (e - 2)) '' Set.Icc 100 999 := by
  refine ⟨by norm_num [System.xmin, calculator3], by norm_num [System.xmax, calculator3], ?_⟩
  intro e he1 he2
  have h := calculator3.numbers_inter_Ico (K := ℝ) (e := e + 1)
    (show (-8 : ℤ) ≤ e + 1 by omega) (show e + 1 ≤ (10 : ℤ) by omega)
  have hβ : ((calculator3.β : ℕ) : ℝ) = 10 := by norm_num [calculator3]
  have hβ' : calculator3.β = 10 := rfl
  have ht : calculator3.t = 3 := rfl
  rw [hβ, hβ', ht, add_sub_cancel_right] at h
  rw [h, show (fun m : ℕ => (m : ℝ) * 10 ^ (e - 2)) =
      fun m : ℕ => (m : ℝ) * 10 ^ (e + 1 - ((3 : ℕ) : ℤ)) from
        funext fun m => by congr 2; push_cast; ring]
  norm_num

/-! ### §2.7.2 IEEE floating point arithmetic -/

/-- The 52 mantissa bits $b_1, \dots, b_{52}$ read as the integer $\sum_i b_i 2^{52-i}$ (with
0-based exponent $51 - i$) are `finFunctionFinEquiv` of the reversed bit string. -/
private theorem bits_eq (b : Fin 52 → Fin 2) :
    ∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)) = (finFunctionFinEquiv (b ∘ Fin.rev) : ℕ) := by
  rw [finFunctionFinEquiv_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Function.comp_apply, Fin.rev_rev, Fin.val_rev]
  rw [show 52 - ((i : ℕ) + 1) = 51 - (i : ℕ) by omega]

/-- The integer encoded by 52 mantissa bits is less than $2^{52}$. -/
private theorem bits_lt (b : Fin 52 → Fin 2) :
    ∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)) < 2 ^ 52 := by
  rw [bits_eq]
  exact (finFunctionFinEquiv (b ∘ Fin.rev)).isLt

/-- Every natural number less than $2^{52}$ is encoded by some 52 mantissa bits. -/
private theorem exists_bits {r : ℕ} (hr : r < 2 ^ 52) :
    ∃ b : Fin 52 → Fin 2, ∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)) = r := by
  refine ⟨finFunctionFinEquiv.symm ⟨r, hr⟩ ∘ Fin.rev, ?_⟩
  have h : (finFunctionFinEquiv.symm ⟨r, hr⟩ ∘ Fin.rev) ∘ Fin.rev =
      (finFunctionFinEquiv.symm ⟨r, hr⟩ : Fin 52 → Fin 2) := by
    funext i
    simp
  rw [bits_eq, h, Equiv.apply_symm_apply]

/-- The binary fraction $(0.b_1 \dots b_{52})_2$ is the integer encoded by the bits times $2^{-52}$.
-/
private theorem bits_real (b : Fin 52 → Fin 2) :
    ∑ i : Fin 52, ((b i : ℕ) : ℝ) * (2 : ℝ) ^ (-((i : ℤ) + 1)) =
      ((∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)) : ℕ) : ℝ) * 2 ^ (-52 : ℤ) := by
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
  congr 2
  have := i.isLt
  omega

/-- $2^{52} \cdot 2^{-52} = 1$. -/
private theorem two_pow_mul_zpow_neg : (2 : ℝ) ^ (52 : ℕ) * 2 ^ (-52 : ℤ) = 1 := by
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
  norm_num

/-- The base of the double system is $2$. -/
private theorem ieeeDouble_β_cast : ((System.ieeeDouble.β : ℕ) : ℝ) = 2 := by
  norm_num [System.ieeeDouble]

/-- **Equation (2.7.2)** of [golub2013matrix], the normalized doubles. The real numbers
$$\pm (1.b_1 b_2 \dots b_{52})_2 \times 2^{E - 1023}$$
with bits $b_i \in \{0, 1\}$ and a biased exponent $1 \le E \le 2046$, that is, with exponent
bits neither all $0$ nor all $1$, are exactly the nonzero numbers of the double system
$\mathbb{F}(2, 53, -1021, 1024)$.

The double system is `FloatingPoint.System.ieeeDouble`. A number
$\pm (1.b_1 \dots b_{52})_2 \times 2^{E - 1023}$ has the mantissa
$m = 2^{52} + \sum_i b_i 2^{52-i}$ and the exponent $e = E - 1022$ of that system. The bits are
elements of `Fin 2`, and the sign is a unit of `ℤ`. -/
theorem equation_2_7_2 :
    {x : ℝ | ∃ (σ : ℤˣ) (b : Fin 52 → Fin 2) (E : ℕ), 1 ≤ E ∧ E ≤ 2046 ∧
        x = ((σ : ℤ) : ℝ) * (1 + ∑ i : Fin 52, ((b i : ℕ) : ℝ) * 2 ^ (-((i : ℤ) + 1))) *
          2 ^ ((E : ℤ) - 1023)} =
      System.ieeeDouble.numbers ℝ \ {0} := by
  have ht : (System.ieeeDouble.t : ℤ) = 53 := rfl
  ext x
  constructor
  · rintro ⟨σ, b, E, hE1, hE2, rfl⟩
    have hr := bits_lt b
    norm_num at hr
    have h1 : (0 : ℝ) < 1 + ∑ i : Fin 52, ((b i : ℕ) : ℝ) * 2 ^ (-((i : ℤ) + 1)) :=
      add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => by positivity)
    refine ⟨Or.inr ⟨σ, 2 ^ 52 + ∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)), (E : ℤ) - 1022,
      ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · norm_num [System.ieeeDouble]
    · norm_num [System.ieeeDouble]
      omega
    · change (-1021 : ℤ) ≤ _
      omega
    · change _ ≤ (1024 : ℤ)
      omega
    · rw [ieeeDouble_β_cast, ht, show (2 : ℝ) ^ ((E : ℤ) - 1022 - 53) =
          2 ^ ((E : ℤ) - 1023) * 2 ^ (-52 : ℤ) by rw [← zpow_add₀ two_ne_zero]; ring_nf, bits_real]
      push_cast
      linear_combination (-(((σ : ℤ) : ℝ)) * (2 : ℝ) ^ ((E : ℤ) - 1023)) * two_pow_mul_zpow_neg
    · rw [Set.mem_singleton_iff]
      exact mul_ne_zero (mul_ne_zero (Int.cast_ne_zero.2 σ.ne_zero) h1.ne') (by positivity)
  · rintro ⟨hx | ⟨σ, m, e, hm1, hm2, he1, he2, rfl⟩, hx0⟩
    · exact absurd hx hx0
    norm_num [System.ieeeDouble] at hm1 hm2
    change (-1021 : ℤ) ≤ e at he1
    change e ≤ (1024 : ℤ) at he2
    obtain ⟨b, hb⟩ := exists_bits (r := m - 2 ^ 52) (by norm_num; omega)
    refine ⟨σ, b, (e + 1022).toNat, by omega, by omega, ?_⟩
    rw [ieeeDouble_β_cast, ht, bits_real, hb, Nat.cast_sub (by norm_num; omega),
      Int.toNat_of_nonneg (by omega), show (2 : ℝ) ^ (e - 53) =
        2 ^ (e + 1022 - 1023) * 2 ^ (-52 : ℤ) by rw [← zpow_add₀ two_ne_zero]; ring_nf]
    push_cast
    linear_combination (((σ : ℤ) : ℝ)) * (2 : ℝ) ^ (e + 1022 - 1023) * two_pow_mul_zpow_neg

/-- **Equation (2.7.3)** of [golub2013matrix], zero and the subnormal doubles. The real numbers
$$\pm (0.b_1 b_2 \dots b_{52})_2 \times 2^{-1022},$$
whose exponent bits are all $0$, are exactly $0$ and the de-normalized numbers
$\pm m \, 2^{L - t} = \pm m \, 2^{-1074}$, $1 \le m < 2^{52}$, of the double system. Every
de-normalized double $x$ satisfies $|x| < N_{\min}$.

So the subnormal doubles lie strictly between $-N_{\min}$ and $N_{\min}$, with the uniform
spacing $2^{-1074}$. The de-normalized numbers are `FloatingPoint.System.denormalized`, and
$N_{\min}$ is `FloatingPoint.System.xmin`. -/
theorem equation_2_7_3 :
    {x : ℝ | ∃ (σ : ℤˣ) (b : Fin 52 → Fin 2),
        x = ((σ : ℤ) : ℝ) * (∑ i : Fin 52, ((b i : ℕ) : ℝ) * 2 ^ (-((i : ℤ) + 1))) *
          2 ^ (-1022 : ℤ)} =
      System.ieeeDouble.denormalized ℝ ∪ {0} ∧
      ∀ x ∈ System.ieeeDouble.denormalized ℝ, |x| < System.ieeeDouble.xmin ℝ := by
  refine ⟨?_, fun x hx => System.ieeeDouble.abs_lt_xmin_of_mem_denormalized hx⟩
  have ht : (System.ieeeDouble.t : ℤ) = 53 := rfl
  have hL : System.ieeeDouble.L = -1021 := rfl
  have hexp : ∀ r : ℝ, r * 2 ^ (-52 : ℤ) * 2 ^ (-1022 : ℤ) = r * 2 ^ ((-1021 : ℤ) - 53) := by
    intro r
    rw [mul_assoc, ← zpow_add₀ two_ne_zero]
    norm_num
  ext x
  constructor
  · rintro ⟨σ, b, rfl⟩
    have hr := bits_lt b
    norm_num at hr
    rw [bits_real]
    rcases Nat.eq_zero_or_pos (∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ))) with h0 | hpos
    · refine Set.mem_union_right _ ?_
      rw [h0, Set.mem_singleton_iff]
      simp
    · refine Set.mem_union_left _ ⟨σ, _, hpos, ?_, ?_⟩
      · norm_num [System.ieeeDouble]
        omega
      · rw [ieeeDouble_β_cast, hL, ht, ← hexp]
        ring
  · rintro (⟨σ, m, hm1, hm2, rfl⟩ | h0)
    · norm_num [System.ieeeDouble] at hm2
      obtain ⟨b, hb⟩ := exists_bits (r := m) (by norm_num; omega)
      refine ⟨σ, b, ?_⟩
      rw [bits_real, hb, ieeeDouble_β_cast, hL, ht, ← hexp]
      ring
    · rw [Set.mem_singleton_iff] at h0
      exact ⟨1, fun _ => 0, by simp [h0]⟩

/-- **Section 2.7.2** of [golub2013matrix], the constants of the double format. The machine epsilon
of the double system is $2^{-52}$, and it is the gap between $1$ and the next larger double: it
is the least $\delta > 0$ such that $1 + \delta$ is a double. The smallest and the largest
positive normalized doubles are
$$N_{\min} = 2^{-1022}, \qquad N_{\max} = (2 - 2^{-52}) \, 2^{1023}.$$
-/
theorem ieeeDouble_constants :
    System.ieeeDouble.machineEps ℝ = 2 ^ (-52 : ℤ) ∧
      IsLeast {δ : ℝ | 0 < δ ∧ 1 + δ ∈ System.ieeeDouble.numbers ℝ} (2 ^ (-52 : ℤ)) ∧
      System.ieeeDouble.xmin ℝ = 2 ^ (-1022 : ℤ) ∧
      System.ieeeDouble.xmax ℝ = (2 - 2 ^ (-52 : ℤ)) * 2 ^ (1023 : ℤ) := by
  refine ⟨System.ieeeDouble_machineEps, ?_, System.ieeeDouble_xmin, System.ieeeDouble_xmax⟩
  rw [← System.ieeeDouble_machineEps]
  exact System.ieeeDouble.isLeast_machineEps (by norm_num [System.ieeeDouble])
    (by norm_num [System.ieeeDouble]) (by norm_num [System.ieeeDouble])

/-- **Section 2.7.2** of [golub2013matrix], rounding to nearest. Let $x \in \mathbb{R}$ with
$N_{\min} \le |x| \le N_{\max}$, and let $y \in \mathbb{R}$ be at least as close to $x$ as every
double. Then
$$\frac{|y - x|}{|x|} \le 2^{-53},$$
so the relative error is at most half the machine epsilon.

A nearest double to $x$ is such a $y$. The tie rule of the source, round half to even, chooses
one nearest double. -/
theorem ieeeDouble_round_nearest {x y : ℝ} (h1 : System.ieeeDouble.xmin ℝ ≤ |x|)
    (h2 : |x| ≤ System.ieeeDouble.xmax ℝ) (hnear : ∀ z ∈ System.ieeeDouble.numbers ℝ,
      |y - x| ≤ |z - x|) :
    |y - x| / |x| ≤ 2 ^ (-53 : ℤ) := by
  have hx : 0 < |x| := (System.ieeeDouble.xmin_pos).trans_le h1
  rw [div_le_iff₀ hx, ← System.ieeeDouble_unitRoundoff (K := ℝ)]
  exact System.ieeeDouble.abs_sub_le_of_forall_abs_sub_le h1 h2 hnear

/-! ### §2.7.3 The `fl` notation -/

/-- **Equation (2.7.4)** of [golub2013matrix]. In a rounding model with unit roundoff $u$, every
admissible floating point representation $y = \operatorname{fl}(x)$ of $x \in \mathbb{R}$
satisfies
$$\operatorname{fl}(x) = x(1 + \delta), \qquad |\delta| \le u.$$

The representation $y$ is any value with `fp.Rounds x y`. -/
theorem equation_2_7_4 (fp : RoundingModel ℝ) {x y : ℝ} (h : fp.Rounds x y) :
    ∃ δ : ℝ, |δ| ≤ fp.u ∧ y = x * (1 + δ) :=
  h.exists_delta

/-- **Equation (2.7.4)** of [golub2013matrix], for a concrete number system. Let $\mathbb{F}$ be a
number system with unit roundoff $u$, and let $\operatorname{fl}$ be its rounding to nearest.
Then for every $z \in \mathbb{R}$,
$$\operatorname{fl}(z) = z(1 + \delta), \qquad |\delta| \le u.$$

The rounding `FloatingPoint.System.round` puts no bound on the exponent, so no range hypothesis
on $z$ is needed. -/
theorem equation_2_7_4_system (s : System) (z : ℝ) :
    ∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ s.round z = z * (1 + δ) :=
  s.exists_round_eq_mul_one_add z

/-- **Equation (2.7.5)** of [golub2013matrix]. Let $\mathbb{F}(\beta, t, L, U)$ be a number system
with $t \ge 2$ and $L \le 1 \le U$. Then its unit roundoff is
$$u = \tfrac12 \times (\text{gap between } 1 \text{ and the next larger floating point
  number}),$$
that is, $u$ is half the machine epsilon, and the machine epsilon is the least $\delta > 0$ such
that $1 + \delta$ is a floating point number. For the IEEE formats,
$u = 2^{-24} \approx 10^{-7}$ in single precision and $u = 2^{-53} \approx 10^{-16}$ in double
precision.

The hypotheses $t \ge 2$ and $L \le 1 \le U$ make sure that $1$ and the next larger number are
in the system. The IEEE formats are `FloatingPoint.System.ieeeSingle` and
`FloatingPoint.System.ieeeDouble`. -/
theorem equation_2_7_5 (s : System) (hL : s.L ≤ 1) (hU : 1 ≤ s.U) (ht : 2 ≤ s.t) :
    s.unitRoundoff ℝ = s.machineEps ℝ / 2 ∧
      IsLeast {δ : ℝ | 0 < δ ∧ 1 + δ ∈ s.numbers ℝ} (s.machineEps ℝ) ∧
      System.ieeeSingle.unitRoundoff ℝ = 2 ^ (-24 : ℤ) ∧
      System.ieeeDouble.unitRoundoff ℝ = 2 ^ (-53 : ℤ) :=
  ⟨s.unitRoundoff_eq_machineEps_div_two, s.isLeast_machineEps hL hU ht,
    System.ieeeSingle_unitRoundoff, System.ieeeDouble_unitRoundoff⟩

/-- **Equation (2.7.6)** of [golub2013matrix], the fundamental axiom of floating point arithmetic.
Let $\mathbb{F}$ be a number system with unit roundoff $u$, let $x, y \in \mathbb{F}$, and let
$\mathbin{op}$ be a binary operation on $\mathbb{R}$. Then
$$\operatorname{fl}(x \mathbin{op} y) = (x \mathbin{op} y)(1 + \delta), \qquad |\delta| \le u.$$
Equivalently, if $x \mathbin{op} y \neq 0$, the relative error $|\operatorname{fl}(x
\mathbin{op} y) - x \mathbin{op} y| / |x \mathbin{op} y|$ is at most $u$.

The source states the axiom for $+$, $-$, $\times$ and $/$; the theorem holds for every function
`f : ℝ → ℝ → ℝ`. The computed value is the machine operation `FloatingPoint.System.op`, which
rounds the arguments and the result. -/
theorem equation_2_7_6 (s : System) (f : ℝ → ℝ → ℝ) {x y : ℝ} (hx : x ∈ s.numbers ℝ)
    (hy : y ∈ s.numbers ℝ) :
    (∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ s.op f x y = f x y * (1 + δ)) ∧
      (f x y ≠ 0 → |s.op f x y - f x y| / |f x y| ≤ s.unitRoundoff ℝ) := by
  obtain ⟨δ, hδ, hop⟩ := s.exists_op_eq_mul_one_add f hx hy
  refine ⟨⟨δ, hδ, hop⟩, fun h0 => ?_⟩
  rw [hop, show f x y * (1 + δ) - f x y = f x y * δ by ring, abs_mul,
    mul_div_cancel_left₀ _ (abs_ne_zero.2 h0)]
  exact hδ

/-! ### §2.7.4 Become a floating point thinker -/

/-- The rounding of the 3-digit calculator at $x$ with $10^{e-1} \le |x| < 10^e$: the mantissa
$|x| \, 10^{3-e}$ is rounded to an integer, and the sign and the exponent are restored. -/
private theorem calculator3_round_eq {x : ℝ} (e : ℤ) (h1 : (10 : ℝ) ^ (e - 1) ≤ |x|)
    (h2 : |x| < 10 ^ e) :
    calculator3.round x =
      (SignType.sign x : ℝ) * (_root_.round (|x| * (10 : ℝ) ^ (3 - e)) : ℝ) * 10 ^ (e - 3) := by
  have h := calculator3.round_eq_of_le_of_lt (K := ℝ) (x := x) (e := e)
    (by simpa [calculator3] using h1) (by simpa [calculator3] using h2)
  simpa [calculator3] using h

/-- **Section 2.7.4** of [golub2013matrix], Maxim 1: order is important. Floating point addition is
not associative. In the 3-digit calculator, with $x = 1.24$, $y = -1.23$ and
$z = 1.00 \times 10^{-3}$,
$$\operatorname{fl}(\operatorname{fl}(x + y) + z) = 1.10 \times 10^{-2}, \qquad
  \operatorname{fl}(x + \operatorname{fl}(y + z)) = 1.00 \times 10^{-2}.$$

The machine addition is `FloatingPoint.System.add` of `GolubVanLoan.Chapter02.calculator3`. -/
theorem calculator3_add_not_assoc :
    calculator3.add (calculator3.add (124 / 100 : ℝ) (-123 / 100)) (1 / 1000) = 110 / 10000 ∧
      calculator3.add (124 / 100 : ℝ) (calculator3.add (-123 / 100) (1 / 1000)) = 100 / 10000 := by
  have hx : calculator3.round (124 / 100 : ℝ) = 124 / 100 := by
    rw [calculator3_round_eq 1 (by norm_num) (by norm_num)]; norm_num
  have hy : calculator3.round (-123 / 100 : ℝ) = -123 / 100 := by
    rw [calculator3_round_eq 1 (by norm_num) (by norm_num)]; norm_num
  have hz : calculator3.round (1 / 1000 : ℝ) = 1 / 1000 := by
    rw [calculator3_round_eq (-2) (by norm_num) (by norm_num)]; norm_num
  have hxy : calculator3.round (124 / 100 + -123 / 100 : ℝ) = 1 / 100 := by
    rw [calculator3_round_eq (-1) (by norm_num) (by norm_num)]; norm_num
  have h01 : calculator3.round (1 / 100 : ℝ) = 1 / 100 := by
    rw [calculator3_round_eq (-1) (by norm_num) (by norm_num)]; norm_num
  have hxyz : calculator3.round (1 / 100 + 1 / 1000 : ℝ) = 110 / 10000 := by
    rw [calculator3_round_eq (-1) (by norm_num) (by norm_num)]; norm_num
  have hyz : calculator3.round (-123 / 100 + 1 / 1000 : ℝ) = -123 / 100 := by
    rw [calculator3_round_eq 1 (by norm_num) (by norm_num)]; norm_num
  refine ⟨?_, ?_⟩
  · simp only [System.add, System.op]
    rw [hx, hy, hxy, h01, hz, hxyz]
  · simp only [System.add, System.op]
    rw [hy, hz, hyz, hx, hy, hxy]
    norm_num

/-! ### §2.7.5 Storing a real matrix -/

/-- **Equation (2.7.7)** of [golub2013matrix], storing a real matrix. Let
$A \in \mathbb{R}^{m \times n}$, and let $\operatorname{fl}(A)$ round each entry of $A$ in a
rounding model with unit roundoff $u$. Then $[\operatorname{fl}(A)]_{ij} = a_{ij}(1 +
\epsilon_{ij})$ with $|\epsilon_{ij}| \le u$, so
$$|\operatorname{fl}(A) - A| \le u |A|$$
entrywise, and $\|\operatorname{fl}(A) - A\|_1 \le u \|A\|_1$. -/
theorem equation_2_7_7 (fp : RoundingModel ℝ) {A Â : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, fp.Rounds (A i j) (Â i j)) :
    (∃ ε : Matrix (Fin m) (Fin n) ℝ, (∀ i j, |ε i j| ≤ fp.u) ∧ ∀ i j, Â i j = A i j * (1 + ε i j)) ∧
      (Â - A).abs ≤ₑ fp.u • A.abs ∧ lpOpNorm 1 (Â - A) ≤ fp.u * lpOpNorm 1 A := by
  have habs : (Â - A).abs ≤ₑ fp.u • A.abs := fun i j => by
    simpa using fp.abs_sub_le (h i j)
  refine ⟨⟨fun i j => (h i j).exists_delta.choose, fun i j => (h i j).exists_delta.choose_spec.1,
    fun i j => (h i j).exists_delta.choose_spec.2⟩, habs, ?_⟩
  rw [lpOpNorm_one_eq_linfty_opNorm_transpose, lpOpNorm_one_eq_linfty_opNorm_transpose]
  exact linfty_opNorm_le_mul_of_abs_entrywiseLE fp.u_nonneg fun i j => habs j i

/-! ### §2.7.6 Roundoff in dot products -/

/-- A run of the dot product (2.7.8) on $n + 1$ entries is a run on the first $n$ entries followed
by one rounded update $\operatorname{fl}(s + \operatorname{fl}(x_{n+1} y_{n+1}))$. -/
private theorem mem_run_algorithm_1_1_1_succ (fp : RoundingModel ℝ) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) (s : ℝ) :
    s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run ↔
      ∃ s' ∈ (Chapter01.algorithm_1_1_1 fp.round (fun k => x (Fin.castSucc k))
          (fun k => y (Fin.castSucc k))).run,
        ∃ p, fp.Rounds (x (Fin.last n) * y (Fin.last n)) p ∧ fp.Rounds (s' + p) s := by
  simp only [Chapter01.algorithm_1_1_1, List.finRange_succ_last, List.foldlM_append,
    List.foldlM_map, List.foldlM_cons, List.foldlM_nil, bind_pure, SetM.mem_run_bind,
    RoundingModel.mem_run_round]

/-- Splitting off the last factor: for $f$ on $n + 1$ indices and $q < n$, the product of
$f(j)$ over $j \ge q$ is the product of $f(j)$ over $q \le j < n$ times $f(n)$, with 0-based
indices. -/
private theorem prod_Ici_castSucc {n : ℕ} (f : Fin (n + 1) → ℝ) (q : Fin n) :
    ∏ j ∈ Finset.Ici (Fin.castSucc q), f j =
      (∏ j ∈ Finset.Ici q, f (Fin.castSucc j)) * f (Fin.last n) := by
  rw [← Finset.filter_le_eq_Ici, ← Finset.filter_le_eq_Ici, Finset.prod_filter,
    Finset.prod_filter, Fin.prod_univ_castSucc]
  simp [Fin.castSucc_le_castSucc_iff, Fin.le_last]

/-- The product of $f$ over the indices from the last index on is $f$ at the last index. -/
private theorem prod_Ici_last {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∏ j ∈ Finset.Ici (Fin.last n), f j = f (Fin.last n) := by
  rw [← Fin.top_eq_last, Finset.Ici_top, Finset.prod_singleton]

/-- The partial sums of a run of the dot product (2.7.8), and their closed form. Over an idempotent
rounding model, a run $s$ of Algorithm 1.1.1 has relative errors $\delta_k$ of the products and
$\epsilon_k$ of the additions, with $\epsilon_1 = 0$, such that $s_0 = 0$, $s_p = (s_{p-1} + x_p
y_p (1 + \delta_p))(1 + \epsilon_p)$, $s = s_n$ and $s = \sum_k x_k y_k (1 + \delta_k) \prod_{j
\ge k} (1 + \epsilon_j)$. -/
private theorem exists_partialSums_of_mem_run (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) :
    ∀ {n : ℕ} (x y : Fin n → ℝ) {s : ℝ}, s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run →
      ∃ δ ε : Fin n → ℝ, (∀ k, |δ k| ≤ fp.u) ∧ (∀ k, |ε k| ≤ fp.u) ∧
        (∀ k : Fin n, (k : ℕ) = 0 → ε k = 0) ∧
        (∃ S : ℕ → ℝ, S 0 = 0 ∧
          (∀ p : Fin n, S (p + 1) = (S p + x p * y p * (1 + δ p)) * (1 + ε p)) ∧ s = S n) ∧
        s = ∑ k, x k * y k * ((1 + δ k) * ∏ j ∈ Finset.Ici k, (1 + ε j))
  | 0, x, y, s, hs => by
    have hs0 : s = 0 := by simpa [Chapter01.algorithm_1_1_1] using hs
    refine ⟨0, 0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
      ⟨fun _ => 0, rfl, fun k => k.elim0, hs0⟩, ?_⟩
    simp [hs0]
  | n + 1, x, y, s, hs => by
    obtain ⟨s', hs', p, hp, hsp⟩ := (mem_run_algorithm_1_1_1_succ fp x y s).1 hs
    obtain ⟨δ', ε', hδ', hε', hε0', ⟨S', hS0, hSrec, hs'S⟩, hs'sum⟩ :=
      exists_partialSums_of_mem_run fp hfp (fun k => x (Fin.castSucc k))
        (fun k => y (Fin.castSucc k)) hs'
    obtain ⟨d, hd, hpd⟩ := hp.exists_delta
    obtain ⟨e, he, hse, he0⟩ : ∃ e, |e| ≤ fp.u ∧ s = (s' + p) * (1 + e) ∧ (n = 0 → e = 0) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hs'0 : s' = 0 := hs'S.trans hS0
        rw [hs'0, zero_add] at hsp
        refine ⟨0, by simp [fp.u_nonneg], ?_, fun _ => rfl⟩
        rw [hfp hp hsp, hs'0]
        ring
      · obtain ⟨e, he, hse⟩ := hsp.exists_delta
        exact ⟨e, he, hse, fun h => absurd h hn.ne'⟩
    refine ⟨Fin.snoc (α := fun _ => ℝ) δ' d, Fin.snoc (α := fun _ => ℝ) ε' e, fun k => ?_,
      fun k => ?_, fun k hk => ?_, ⟨fun k => if k ≤ n then S' k else s, by simp [hS0],
        fun q => ?_, by simp⟩, ?_⟩
    · induction k using Fin.lastCases with
      | last => simpa using hd
      | cast q => simpa using hδ' q
    · induction k using Fin.lastCases with
      | last => simpa using he
      | cast q => simpa using hε' q
    · induction k using Fin.lastCases with
      | last =>
        simp only [Fin.val_last] at hk
        simpa using he0 hk
      | cast q => simpa using hε0' q (by simpa using hk)
    · induction q using Fin.lastCases with
      | last =>
        simp only [Fin.val_last, Fin.snoc_last, le_refl, ↓reduceIte,
          show ¬ n + 1 ≤ n from Nat.not_succ_le_self n]
        rw [← hs'S, hse, hpd]
      | cast q =>
        have hq : (q : ℕ) + 1 ≤ n := q.isLt
        simp only [Fin.val_castSucc, Fin.snoc_castSucc, hq, q.isLt.le, ↓reduceIte]
        exact hSrec q
    · rw [Fin.sum_univ_castSucc, hse, hs'sum, hpd, add_mul, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun q _ => ?_
        simp only [Fin.snoc_castSucc, prod_Ici_castSucc, Fin.snoc_last]
        ring
      · simp only [Fin.snoc_last, prod_Ici_last]
        ring

/-- **Equation (2.7.9)** of [golub2013matrix], the rounding errors of the dot product (2.7.8). Let
the rounding model have unit roundoff $u$ and exact first additions,
$\operatorname{fl}(0 + p) = p$. Let $x, y \in \mathbb{R}^n$, and let $s$ be a computed value of
$\operatorname{fl}(x^T y)$ by Algorithm 1.1.1. Then there are $\delta_p, \epsilon_p$ with
$|\delta_p|, |\epsilon_p| \le u$ such that the partial sums $s_p = \operatorname{fl}(\sum_{k \le
p} x_k y_k)$ satisfy
$$s_1 = x_1 y_1 (1 + \delta_1), \qquad s_p = (s_{p-1} + x_p y_p (1 + \delta_p))(1 + \epsilon_p)
  \quad (p = 2, \dots, n),$$
and $s = s_n$.

The hypothesis $\operatorname{fl}(0 + p) = p$ is `fp.IsIdempotent`; it makes $s_1$ exact up to
$\delta_1$. The computed value is any `s ∈ (GolubVanLoan.Chapter01.algorithm_1_1_1 fp.round x
y).run`. The indices of $x$, $y$, $\delta$ and $\epsilon$ are 0-based, and the partial sums are
a function `S : ℕ → ℝ` with $s_p$ = `S p`. -/
theorem equation_2_7_9 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {n : ℕ} (x y : Fin n → ℝ)
    {s : ℝ} (hs : s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run) :
    ∃ (δ ε : Fin n → ℝ) (S : ℕ → ℝ), (∀ k, |δ k| ≤ fp.u) ∧ (∀ k, |ε k| ≤ fp.u) ∧
      (∀ p : Fin n, (p : ℕ) = 0 → S 1 = x p * y p * (1 + δ p)) ∧
      (∀ p : Fin n, (p : ℕ) ≠ 0 → S (p + 1) = (S p + x p * y p * (1 + δ p)) * (1 + ε p)) ∧
      s = S n := by
  obtain ⟨δ, ε, hδ, hε, hε0, ⟨S, hS0, hrec, hsS⟩, -⟩ := exists_partialSums_of_mem_run fp hfp x y hs
  refine ⟨δ, ε, S, hδ, hε, fun p hp => ?_, fun p _ => hrec p, hsS⟩
  simpa [hp, hS0, hε0 p hp] using hrec p

/-- **Equation (2.7.10)** of [golub2013matrix]. Let the rounding model have unit roundoff $u$ and
$\operatorname{fl}(0 + p) = p$, let $x, y \in \mathbb{R}^n$, and let $s$ be a computed value of
$\operatorname{fl}(x^T y)$ by Algorithm 1.1.1. Then there are $\delta_k, \epsilon_k$ with
$|\delta_k|, |\epsilon_k| \le u$ and $\epsilon_1 = 0$ such that
$$\operatorname{fl}(x^T y) = \sum_{k=1}^n x_k y_k (1 + \gamma_k), \qquad 1 + \gamma_k = (1 +
  \delta_k) \prod_{j=k}^n (1 + \epsilon_j),$$
and hence
$$|\operatorname{fl}(x^T y) - x^T y| \le \sum_{k=1}^n |x_k y_k| |\gamma_k|.$$

The $\gamma_k$ of the source are these local quantities, not `FloatingPoint.gamma`. The
hypothesis $\operatorname{fl}(0 + p) = p$ is `fp.IsIdempotent`. -/
theorem equation_2_7_10 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {n : ℕ}
    (x y : Fin n → ℝ) {s : ℝ} (hs : s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run) :
    ∃ δ ε : Fin n → ℝ, (∀ k, |δ k| ≤ fp.u) ∧ (∀ k, |ε k| ≤ fp.u) ∧
      (∀ k : Fin n, (k : ℕ) = 0 → ε k = 0) ∧
      s = ∑ k, x k * y k * (1 + ((1 + δ k) * ∏ j ∈ Finset.Ici k, (1 + ε j) - 1)) ∧
      |s - x ⬝ᵥ y| ≤ ∑ k, |x k * y k| * |(1 + δ k) * ∏ j ∈ Finset.Ici k, (1 + ε j) - 1| := by
  obtain ⟨δ, ε, hδ, hε, hε0, -, hsum⟩ := exists_partialSums_of_mem_run fp hfp x y hs
  refine ⟨δ, ε, hδ, hε, hε0, by simpa using hsum, ?_⟩
  rw [hsum, dotProduct, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← abs_mul]
  exact le_of_eq (congrArg _ (by ring))

/-- **Lemma 2.7.1** of [golub2013matrix]. Let $u \ge 0$, let $\alpha_1, \dots, \alpha_n$ satisfy
$|\alpha_k| \le u$, and let $nu \le 0.01$. If $1 + \alpha = \prod_{k=1}^n (1 + \alpha_k)$, then
$$|\alpha| \le 1.01 \, nu.$$
-/
theorem lemma_2_7_1 {u : ℝ} (hu : 0 ≤ u) (α : Fin n → ℝ) (hα : ∀ k, |α k| ≤ u)
    (hnu : (n : ℝ) * u ≤ 1 / 100) {a : ℝ} (ha : 1 + a = ∏ k, (1 + α k)) :
    |a| ≤ 101 / 100 * (n * u) := by
  have h := abs_prod_one_add_sub_one_le_of_mul_le hu hα hnu
  rwa [← ha, add_sub_cancel_left] at h

/-- **Equation (2.7.11)** of [golub2013matrix]. Let the rounding model have unit roundoff $u$ and
$\operatorname{fl}(0 + p) = p$, let $x, y \in \mathbb{R}^n$ with $nu \le 0.01$, and let $s$ be a
computed value of $\operatorname{fl}(x^T y)$ by Algorithm 1.1.1. Then
$$|\operatorname{fl}(x^T y) - x^T y| \le 1.01 \, nu \, |x|^T |y|.$$

The proof combines the bound $(1 + u)^n - 1$ of the product form,
`FloatingPoint.abs_sub_le_one_add_pow_sub_one_of_roundsDot`, with Lemma 2.7.1. The hypothesis
$\operatorname{fl}(0 + p) = p$ is `fp.IsIdempotent`. -/
theorem equation_2_7_11 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {n : ℕ}
    (x y : Fin n → ℝ) (hnu : (n : ℝ) * fp.u ≤ 1 / 100) {s : ℝ}
    (hs : s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run) :
    |s - x ⬝ᵥ y| ≤ 101 / 100 * (n * fp.u) * (|x| ⬝ᵥ |y|) := by
  have h := abs_sub_le_one_add_pow_sub_one_of_roundsDot
    (Chapter01.algorithm_1_1_1_rounds hfp x y s hs)
  rw [Fintype.card_fin] at h
  have hc : (1 + fp.u) ^ n - 1 ≤ 101 / 100 * (n * fp.u) := by
    have h1 := lemma_2_7_1 fp.u_nonneg (fun _ : Fin n => fp.u)
      (fun _ => (abs_of_nonneg fp.u_nonneg).le) hnu (a := (1 + fp.u) ^ n - 1) (by simp)
    exact (le_abs_self _).trans h1
  exact h.trans (mul_le_mul_of_nonneg_right hc
    (dotProduct_nonneg_of_nonneg (abs_nonneg x) (abs_nonneg y)))

/-- **Equation (2.7.12)** of [golub2013matrix], in rigorous form. Let the rounding model have unit
roundoff $u$, let $x, y \in \mathbb{R}^n$, and let $s$ be a computed value of
$\operatorname{fl}(x^T y)$ by Algorithm 1.1.1. If $\operatorname{fl}(0 + p) = p$ and $nu < 1$,
then
$$|\operatorname{fl}(x^T y) - x^T y| \le \gamma_n |x|^T |y|, \qquad \gamma_n = \frac{nu}{1 -
  nu}.$$
Without the hypothesis $\operatorname{fl}(0 + p) = p$, the first addition costs one more
rounding: if $(n + 1)u < 1$, then $|\operatorname{fl}(x^T y) - x^T y| \le \gamma_{n+1} |x|^T
|y|$.

The source states the first-order bound $nu |x|^T |y| + O(u^2)$, which follows because
$\gamma_n = nu + O(u^2)$. The hypothesis $\operatorname{fl}(0 + p) = p$ is `fp.IsIdempotent`,
and $\gamma_n$ is `FloatingPoint.gamma`. The second bound is
`FloatingPoint.abs_sub_le_of_mem_run_dotAccum`. -/
theorem equation_2_7_12 (fp : RoundingModel ℝ) {n : ℕ} (x y : Fin n → ℝ) {s : ℝ}
    (hs : s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run) :
    (fp.IsIdempotent → (n : ℝ) * fp.u < 1 → |s - x ⬝ᵥ y| ≤ gamma fp.u n * (|x| ⬝ᵥ |y|)) ∧
      (((n + 1 : ℕ) : ℝ) * fp.u < 1 →
        |s - x ⬝ᵥ y| ≤ gamma fp.u (n + 1) * (|x| ⬝ᵥ |y|)) := by
  refine ⟨fun hfp hnu => ?_, fun hnu => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hs0 : s = 0 := by simpa [Chapter01.algorithm_1_1_1] using hs
      simp [hs0, dotProduct]
    · have hu : fp.u < 1 := by
        have : fp.u ≤ n * fp.u :=
          le_mul_of_one_le_left fp.u_nonneg (by exact_mod_cast hn)
        linarith
      simpa using abs_sub_le_of_roundsDot hu (by simpa using hnu)
        (Chapter01.algorithm_1_1_1_rounds hfp x y s hs)
  · rw [Chapter01.algorithm_1_1_1_eq_dotAccum] at hs
    have h := abs_sub_le_of_mem_run_dotAccum (by simpa using hnu) hs
    simp only [List.length_finRange, zero_add, abs_zero] at h
    rw [← Fin.sum_univ_def, ← Fin.sum_univ_def] at h
    exact h

/-! ### §2.7.8 Roundoff in other basic matrix computations -/

/-- **Equation (2.7.15)** of [golub2013matrix]. Let $\alpha \in \mathbb{R}$ and
$A \in \mathbb{R}^{m \times n}$, and let $\operatorname{fl}(\alpha A)$ round each entry of
$\alpha A$ in a rounding model with unit roundoff $u$. Then
$$\operatorname{fl}(\alpha A) = \alpha A + E, \qquad |E| \le u |\alpha A|.$$
-/
theorem equation_2_7_15 (fp : RoundingModel ℝ) (α : ℝ) {A C : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, fp.Rounds (α * A i j) (C i j)) :
    ∃ E : Matrix (Fin m) (Fin n) ℝ, C = α • A + E ∧ E.abs ≤ₑ fp.u • (α • A).abs :=
  ⟨C - α • A, by abel, fun i j => by simpa using fp.abs_sub_le (h i j)⟩

/-- **Equation (2.7.16)** of [golub2013matrix]. Let $A, B \in \mathbb{R}^{m \times n}$, and let
$\operatorname{fl}(A + B)$ round each entry of $A + B$ in a rounding model with unit roundoff
$u$. Then
$$\operatorname{fl}(A + B) = (A + B) + E, \qquad |E| \le u |A + B|.$$
-/
theorem equation_2_7_16 (fp : RoundingModel ℝ) {A B C : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, fp.Rounds (A i j + B i j) (C i j)) :
    ∃ E : Matrix (Fin m) (Fin n) ℝ, C = (A + B) + E ∧ E.abs ≤ₑ fp.u • (A + B).abs :=
  ⟨C - (A + B), by abel, fun i j => by simpa using fp.abs_sub_le (h i j)⟩

/-- **Equation (2.7.17)** of [golub2013matrix], in rigorous form. Let $a \in \mathbb{R}$ and
$x, y \in \mathbb{R}^n$, and let $\hat y$ be a computed value of the saxpy $y + ax$ by Algorithm
1.1.2 in a rounding model with unit roundoff $u$. Then
$$\operatorname{fl}(y + ax) = y + ax + z, \qquad |z| \le u |y| + (2u + u^2) |ax|.$$

The source states the first-order bound $|z| \le u(|y| + 2|ax|) + O(u^2)$. Each entry is one
rounded update, `FloatingPoint.abs_sub_le_of_rounds_add_mul`. -/
theorem equation_2_7_17 (fp : RoundingModel ℝ) (a : ℝ) (x y : Fin n → ℝ) {ŷ : Fin n → ℝ}
    (hŷ : ŷ ∈ (Chapter01.algorithm_1_1_2 fp.round a x y).run) :
    ∃ z : Fin n → ℝ, ŷ = y + a • x + z ∧
      |z| ≤ fp.u • |y| + (2 * fp.u + fp.u ^ 2) • |a • x| := by
  refine ⟨ŷ - (y + a • x), by abel, fun i => ?_⟩
  obtain ⟨p, hp, hs⟩ := (Chapter01.algorithm_1_1_2_mem_run fp a x y ŷ).1 hŷ i
  simpa using abs_sub_le_of_rounds_add_mul hp hs

/-- **Equation (2.7.18)** of [golub2013matrix], in rigorous form. In this statement the unit
roundoff is written $\mathbf{u}$, because $u$ is a vector. Let $C \in \mathbb{R}^{m \times n}$,
$u \in \mathbb{R}^m$ and $v \in \mathbb{R}^n$, and let $\hat C$ be a computed value of the outer
product update $C + uv^T$, with each entry computed as $\operatorname{fl}(c_{ij} +
\operatorname{fl}(u_i v_j))$. Then
$$\operatorname{fl}(C + uv^T) = C + uv^T + E, \qquad |E| \le \mathbf{u} |C| + (2\mathbf{u} +
  \mathbf{u}^2) |uv^T|.$$

The source states the first-order bound $|E| \le \mathbf{u}(|C| + 2|uv^T|) + O(\mathbf{u}^2)$.
The computed value is a run of Algorithm 1.1.8 with inner dimension $1$, applied to the
$m \times 1$ matrix `replicateCol (Fin 1) u` and the $1 \times n$ matrix
`replicateRow (Fin 1) v`. -/
theorem equation_2_7_18 (fp : RoundingModel ℝ) (C : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ)
    (v : Fin n → ℝ) {Ĉ : Matrix (Fin m) (Fin n) ℝ}
    (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_8 fp.round (replicateCol (Fin 1) u)
      (replicateRow (Fin 1) v) C).run) :
    ∃ E : Matrix (Fin m) (Fin n) ℝ, Ĉ = C + vecMulVec u v + E ∧
      E.abs ≤ₑ fp.u • C.abs + (2 * fp.u + fp.u ^ 2) • (vecMulVec u v).abs := by
  refine ⟨Ĉ - (C + vecMulVec u v), by abel, fun i j => ?_⟩
  have h := (Chapter01.algorithm_1_1_8_mem_run fp _ _ C Ĉ).1 hĈ i j
  simp only [dotAccum, List.finRange_succ, List.finRange_zero, List.map_nil, List.foldlM_cons,
    List.foldlM_nil, bind_pure, SetM.mem_run_bind, RoundingModel.mem_run_round,
    replicateCol_apply, replicateRow_apply] at h
  obtain ⟨p, hp, hs⟩ := h
  simpa [vecMulVec_apply] using abs_sub_le_of_rounds_add_mul hp hs

/-- In a rounding model with unit roundoff $u$, if $\hat C$ is a computed product of
$A \in \mathbb{R}^{m \times r}$ and $B \in \mathbb{R}^{r \times n}$ in the relational sense
`FloatingPoint.RoundsMul` and $ru < 1$, then $|\hat C - AB| \le \gamma_r |A| |B|$; for $r = 0$
both sides vanish. -/
private theorem abs_sub_entrywiseLE_of_roundsMul_fin (fp : RoundingModel ℝ) {r : ℕ}
    {A : Matrix (Fin m) (Fin r) ℝ} {B : Matrix (Fin r) (Fin n) ℝ} {Ĉ : Matrix (Fin m) (Fin n) ℝ}
    (hr : (r : ℝ) * fp.u < 1) (h : RoundsMul fp A B Ĉ) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A.abs * B.abs) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · intro i j
    obtain ⟨o, p, -, -, -, hsum⟩ := h i j
    have ho : o = [] := List.eq_nil_iff_forall_not_mem.2 fun k => k.elim0
    subst ho
    have hC : Ĉ i j = 0 := hsum
    simp [hC]
  · have hu : fp.u < 1 := by
      have : fp.u ≤ r * fp.u := le_mul_of_one_le_left fp.u_nonneg (by exact_mod_cast hr0)
      linarith
    simpa using abs_sub_entrywiseLE_of_roundsMul hu (by simpa using hr) h

/-- **Equation (2.7.19)** of [golub2013matrix], in rigorous form. Let the rounding model have unit
roundoff $u$ and $\operatorname{fl}(0 + p) = p$, let $A \in \mathbb{R}^{m \times r}$ and
$B \in \mathbb{R}^{r \times n}$ with $ru < 1$, and let $\hat C$ be a computed value of $AB$ by
the dot product matrix multiplication, Algorithm 1.1.6 started at $C = 0$. Then
$$\operatorname{fl}(AB) = AB + E, \qquad |E| \le \gamma_r |A| |B|.$$

The source states $|E| \le nu |A| |B| + O(u^2)$, where its $n$ is the inner dimension, here $r$;
this follows because $\gamma_r = ru + O(u^2)$. The proof applies
`GolubVanLoan.Chapter01.algorithm_1_1_6_rounds` and
`FloatingPoint.abs_sub_entrywiseLE_of_roundsMul`. -/
theorem equation_2_7_19 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_6 fp.round A B 0).run) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A.abs * B.abs) :=
  abs_sub_entrywiseLE_of_roundsMul_fin fp hr (Chapter01.algorithm_1_1_6_rounds hfp A B Ĉ hĈ)

/-- **Equation (2.7.19)** of [golub2013matrix], the remark that "the same result applies if a gaxpy
… procedure is used". Let the rounding model have unit roundoff $u$ and
$\operatorname{fl}(0 + p) = p$, let $A \in \mathbb{R}^{m \times r}$ and
$B \in \mathbb{R}^{r \times n}$ with $ru < 1$, and let $\hat C$ be a computed value of $AB$ by
the saxpy matrix multiplication, Algorithm 1.1.7 started at $C = 0$. Then
$$|\hat C - AB| \le \gamma_r |A| |B|.$$

Each entry is accumulated over $k = 1, \dots, r$ in order. -/
theorem equation_2_7_19_saxpy (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_7 fp.round A B 0).run) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A.abs * B.abs) :=
  abs_sub_entrywiseLE_of_roundsMul_fin fp hr (Chapter01.algorithm_1_1_7_rounds hfp A B Ĉ hĈ)

/-- **Equation (2.7.19)** of [golub2013matrix], the remark that the same result applies to an "outer
product based procedure". Let the rounding model have unit roundoff $u$ and
$\operatorname{fl}(0 + p) = p$, let $A \in \mathbb{R}^{m \times r}$ and
$B \in \mathbb{R}^{r \times n}$ with $ru < 1$, and let $\hat C$ be a computed value of $AB$ by
the outer product matrix multiplication, Algorithm 1.1.8 started at $C = 0$. Then
$$|\hat C - AB| \le \gamma_r |A| |B|.$$
-/
theorem equation_2_7_19_outer (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_8 fp.round A B 0).run) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A.abs * B.abs) :=
  abs_sub_entrywiseLE_of_roundsMul_fin fp hr (Chapter01.algorithm_1_1_8_rounds hfp A B Ĉ hĈ)

/-- **Equation (2.7.20)** of [golub2013matrix], in rigorous form. Under the hypotheses of (2.7.19)
for Algorithm 1.1.6,
$$\|\operatorname{fl}(AB) - AB\|_1 \le \gamma_r \|A\|_1 \|B\|_1.$$

The source states $nu \|A\|_1 \|B\|_1 + O(u^2)$. The proof uses that the 1-norm is monotone in
$|\cdot|$ and submultiplicative, and that $\| |A| \|_1 = \|A\|_1$. -/
theorem equation_2_7_20 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_6 fp.round A B 0).run) :
    lpOpNorm 1 (Ĉ - A * B) ≤ gamma fp.u r * (lpOpNorm 1 A * lpOpNorm 1 B) := by
  have h := equation_2_7_19 fp hfp A B hr hĈ
  have hγ : 0 ≤ gamma fp.u r := gamma_nonneg fp.u_nonneg hr
  have habs : ∀ {p q : ℕ} (X : Matrix (Fin p) (Fin q) ℝ), lpOpNorm 1 X.abs = lpOpNorm 1 X :=
    fun X => by
      rw [lpOpNorm_one_eq_linfty_opNorm_transpose, lpOpNorm_one_eq_linfty_opNorm_transpose]
      exact linfty_opNorm_abs Xᵀ
  calc lpOpNorm 1 (Ĉ - A * B) ≤ gamma fp.u r * lpOpNorm 1 (A.abs * B.abs) := by
        rw [lpOpNorm_one_eq_linfty_opNorm_transpose, lpOpNorm_one_eq_linfty_opNorm_transpose]
        refine linfty_opNorm_le_mul_of_abs_entrywiseLE hγ fun i j => ?_
        simp only [Matrix.abs_apply, transpose_apply, Matrix.smul_apply, smul_eq_mul]
        exact (h j i).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hγ)
    _ ≤ gamma fp.u r * (lpOpNorm 1 A.abs * lpOpNorm 1 B.abs) :=
        mul_le_mul_of_nonneg_left (lpOpNorm_mul_le 1 A.abs B.abs) hγ
    _ = gamma fp.u r * (lpOpNorm 1 A * lpOpNorm 1 B) := by rw [habs, habs]

/-- **Section 2.7.10** of [golub2013matrix]: "if $A \ge 0$ and $B \ge 0$, then conventional matrix
multiplication produces a product $\hat C$ that has small componentwise relative error". Let the
rounding model have unit roundoff $u$ and $\operatorname{fl}(0 + p) = p$, let
$A \in \mathbb{R}^{m \times r}$ and $B \in \mathbb{R}^{r \times n}$ be entrywise nonnegative
with $ru < 1$, and let $\hat C$ be a computed value of $C = AB$ by Algorithm 1.1.6 started at
$0$. Then
$$|\hat C - C| \le \gamma_r |C|.$$

The proof is (2.7.19) together with $|A| |B| = AB$. -/
theorem abs_sub_le_gamma_mul_abs_of_nonneg (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent)
    {r : ℕ} {A : Matrix (Fin m) (Fin r) ℝ} {B : Matrix (Fin r) (Fin n) ℝ}
    (hA : A.EntrywiseNonneg) (hB : B.EntrywiseNonneg) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_6 fp.round A B 0).run) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A * B).abs := by
  have h := equation_2_7_19 fp hfp A B hr hĈ
  have hAabs : A.abs = A := by
    ext i j
    exact abs_of_nonneg (hA i j)
  have hBabs : B.abs = B := by
    ext i j
    exact abs_of_nonneg (hB i j)
  rw [hAabs, hBabs] at h
  intro i j
  refine (h i j).trans ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.abs_apply]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (gamma_nonneg fp.u_nonneg hr)

/-! ### §2.7.9 Forward and backward error analyses -/

/-- If $|c - 1| \le g$, then $|ac - a| \le g |a|$. -/
private theorem abs_mul_sub_self_le {a c g : ℝ} (h : |c - 1| ≤ g) : |a * c - a| ≤ g * |a| := by
  rw [show a * c - a = a * (c - 1) by ring, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg a)

/-- **Section 2.7.9** of [golub2013matrix], the backward error of the $2 \times 2$ triangular
product. Let $u \ge 0$ with $2u < 1$, let $a_{11}, a_{12}, a_{22}, b_{11}, b_{12}, b_{22} \in
\mathbb{R}$, let $A = \begin{bmatrix} a_{11} & a_{12} \\ 0 & a_{22} \end{bmatrix}$ and $B =
\begin{bmatrix} b_{11} & b_{12} \\ 0 & b_{22} \end{bmatrix}$, and let $|\epsilon_i| \le u$ for
$i = 1, \dots, 5$. Then
$$\begin{bmatrix} a_{11} b_{11} (1 + \epsilon_1) & (a_{11} b_{12} (1 + \epsilon_2) + a_{12}
  b_{22} (1 + \epsilon_3))(1 + \epsilon_4) \\ 0 & a_{22} b_{22} (1 + \epsilon_5) \end{bmatrix} =
  \hat A \hat B,$$
where
$$\hat A = \begin{bmatrix} a_{11} & a_{12} (1 + \epsilon_3)(1 + \epsilon_4) \\ 0 & a_{22} (1 +
  \epsilon_5) \end{bmatrix}, \qquad \hat B = \begin{bmatrix} b_{11} (1 + \epsilon_1) & b_{12}
  (1 + \epsilon_2)(1 + \epsilon_4) \\ 0 & b_{22} \end{bmatrix},$$
and $|\hat A - A| \le \gamma_2 |A|$ and $|\hat B - B| \le \gamma_2 |B|$. So the computed product
is the exact product of slightly perturbed factors.

The left side is the form of $\operatorname{fl}(AB)$ in the source;
`GolubVanLoan.Chapter02.triangular_mul_two_backward_run` shows that every computed product has
this form. The source states the first-order bounds $2u|A| + O(u^2)$ and $2u|B| + O(u^2)$. The
indices of $\epsilon$ are 0-based in Lean. -/
theorem triangular_mul_two_backward {u : ℝ} (hu : 0 ≤ u) (h2u : 2 * u < 1)
    (a₁₁ a₁₂ a₂₂ b₁₁ b₁₂ b₂₂ : ℝ) (ε : Fin 5 → ℝ) (hε : ∀ i, |ε i| ≤ u) :
    !![a₁₁ * b₁₁ * (1 + ε 0),
        (a₁₁ * b₁₂ * (1 + ε 1) + a₁₂ * b₂₂ * (1 + ε 2)) * (1 + ε 3);
        0, a₂₂ * b₂₂ * (1 + ε 4)] =
      !![a₁₁, a₁₂ * ((1 + ε 2) * (1 + ε 3)); 0, a₂₂ * (1 + ε 4)] *
        !![b₁₁ * (1 + ε 0), b₁₂ * ((1 + ε 1) * (1 + ε 3)); 0, b₂₂] ∧
      (!![a₁₁, a₁₂ * ((1 + ε 2) * (1 + ε 3)); 0, a₂₂ * (1 + ε 4)] - !![a₁₁, a₁₂; 0, a₂₂]).abs ≤ₑ
        gamma u 2 • (!![a₁₁, a₁₂; 0, a₂₂] : Matrix (Fin 2) (Fin 2) ℝ).abs ∧
      (!![b₁₁ * (1 + ε 0), b₁₂ * ((1 + ε 1) * (1 + ε 3)); 0, b₂₂] - !![b₁₁, b₁₂; 0, b₂₂]).abs ≤ₑ
        gamma u 2 • (!![b₁₁, b₁₂; 0, b₂₂] : Matrix (Fin 2) (Fin 2) ℝ).abs := by
  have h2 : ((2 : ℕ) : ℝ) * u < 1 := by exact_mod_cast h2u
  have hγ0 : 0 ≤ gamma u 2 := gamma_nonneg hu h2
  have hγ1 : u ≤ gamma u 2 :=
    (le_gamma_one hu (by linarith)).trans (gamma_mono hu (by norm_num) h2)
  have hpair : ∀ i j : Fin 5, |(1 + ε i) * (1 + ε j) - 1| ≤ gamma u 2 := fun i j => by
    have h := abs_prod_one_add_sub_one_le_gamma hu h2 (δ := ![ε i, ε j])
      (fun k => by fin_cases k <;> simp [hε]) (ρ := fun _ => 1) (fun _ => Or.inl rfl)
    simpa [Fin.prod_univ_two] using h
  have hone : ∀ i : Fin 5, |(1 + ε i) - 1| ≤ gamma u 2 := fun i => by
    rw [add_sub_cancel_left]; exact (hε i).trans hγ1
  refine ⟨?_, fun i j => ?_, fun i j => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · fin_cases i <;> fin_cases j
    · simpa using mul_nonneg hγ0 (abs_nonneg a₁₁)
    · simpa using abs_mul_sub_self_le (a := a₁₂) (hpair 2 3)
    · simp
    · simpa using abs_mul_sub_self_le (a := a₂₂) (hone 4)
  · fin_cases i <;> fin_cases j
    · simpa using abs_mul_sub_self_le (a := b₁₁) (hone 0)
    · simpa using abs_mul_sub_self_le (a := b₁₂) (hpair 1 3)
    · simp
    · simpa using mul_nonneg hγ0 (abs_nonneg b₂₂)

/-- **Section 2.7.9** of [golub2013matrix], the claim "it can be shown that". Let the rounding model
have unit roundoff $u$ and $\operatorname{fl}(0 + p) = p$, and let $\hat C$ be a computed value
of $AB$ by Algorithm 1.2.1 for the $2 \times 2$ upper triangular matrices $A = \begin{bmatrix}
a_{11} & a_{12} \\ 0 & a_{22} \end{bmatrix}$ and $B = \begin{bmatrix} b_{11} & b_{12} \\ 0 &
b_{22} \end{bmatrix}$, started at $C = 0$. Then there are $\epsilon_1, \dots, \epsilon_5$ with
$|\epsilon_i| \le u$ and
$$\hat C = \begin{bmatrix} a_{11} b_{11} (1 + \epsilon_1) & (a_{11} b_{12} (1 + \epsilon_2) +
  a_{12} b_{22} (1 + \epsilon_3))(1 + \epsilon_4) \\ 0 & a_{22} b_{22} (1 + \epsilon_5)
  \end{bmatrix}.$$

With `GolubVanLoan.Chapter02.triangular_mul_two_backward` this gives the backward error
statement $\operatorname{fl}(AB) = \hat A \hat B$. The indices of $\epsilon$ are 0-based in
Lean. -/
theorem triangular_mul_two_backward_run (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent)
    (a₁₁ a₁₂ a₂₂ b₁₁ b₁₂ b₂₂ : ℝ) {Ĉ : Matrix (Fin 2) (Fin 2) ℝ}
    (hĈ : Ĉ ∈ (Chapter01.algorithm_1_2_1 fp.round !![a₁₁, a₁₂; 0, a₂₂] !![b₁₁, b₁₂; 0, b₂₂]
      0).run) :
    ∃ ε : Fin 5 → ℝ, (∀ i, |ε i| ≤ fp.u) ∧
      Ĉ = !![a₁₁ * b₁₁ * (1 + ε 0),
        (a₁₁ * b₁₂ * (1 + ε 1) + a₁₂ * b₂₂ * (1 + ε 2)) * (1 + ε 3);
        0, a₂₂ * b₂₂ * (1 + ε 4)] := by
  have h' : ∃ p₁, fp.Rounds (a₁₁ * b₁₁) p₁ ∧ ∃ c₁, fp.Rounds p₁ c₁ ∧
      ∃ p₂, fp.Rounds (a₁₁ * b₁₂) p₂ ∧ ∃ c₂, fp.Rounds p₂ c₂ ∧
      ∃ p₃, fp.Rounds (a₁₂ * b₂₂) p₃ ∧ ∃ c₃, fp.Rounds (c₂ + p₃) c₃ ∧
      ∃ p₄, fp.Rounds (a₂₂ * b₂₂) p₄ ∧ ∃ c₄, fp.Rounds p₄ c₄ ∧
        ((0 : Matrix (Fin 2) (Fin 2) ℝ).updateRow 0
          (Function.update (Function.update ((0 : Matrix (Fin 2) (Fin 2) ℝ) 0) 0 c₁) 1
            c₃)).updateRow 1 (Function.update ((0 : Matrix (Fin 2) (Fin 2) ℝ) 1) 1 c₄) = Ĉ := by
    simpa (config := { decide := true }) [Chapter01.algorithm_1_2_1, List.finRange_succ,
      SetM.mem_run_bind, RoundingModel.mem_run_round] using hĈ
  obtain ⟨p₁, hp₁, c₁, hc₁, p₂, hp₂, c₂, hc₂, p₃, hp₃, c₃, hc₃, p₄, hp₄, c₄, hc₄, rfl⟩ := h'
  obtain rfl := hfp hp₁ hc₁
  obtain rfl := hfp hp₂ hc₂
  obtain rfl := hfp hp₄ hc₄
  obtain ⟨d₁, hd₁, rfl⟩ := hp₁.exists_delta
  obtain ⟨d₂, hd₂, rfl⟩ := hp₂.exists_delta
  obtain ⟨d₃, hd₃, rfl⟩ := hp₃.exists_delta
  obtain ⟨d₄, hd₄, rfl⟩ := hc₃.exists_delta
  obtain ⟨d₅, hd₅, rfl⟩ := hp₄.exists_delta
  refine ⟨![d₁, d₂, d₃, d₄, d₅], fun i => by fin_cases i <;> assumption, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [updateRow_apply]

/-! ### §2.7.11 Analysis of an ideal equation solver -/

/-- **Equation (2.7.21)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$, and let $\operatorname{fl}(A) = A + E$ and $\operatorname{fl}(b) = b + e$
round each entry of $A$ and $b$ in a rounding model with unit roundoff $u$. Then
$$\|E\|_\infty \le u \|A\|_\infty, \qquad \|e\|_\infty \le u \|b\|_\infty.$$
-/
theorem equation_2_7_21 (fp : RoundingModel ℝ) {A Â : Matrix (Fin n) (Fin n) ℝ}
    {b bh : Fin n → ℝ} (hA : ∀ i j, fp.Rounds (A i j) (Â i j)) (hb : ∀ i, fp.Rounds (b i) (bh i)) :
    lpOpNorm ∞ (Â - A) ≤ fp.u * lpOpNorm ∞ A ∧
      ‖WithLp.toLp ∞ (bh - b)‖ ≤ fp.u * ‖WithLp.toLp ∞ b‖ := by
  refine ⟨?_, ?_⟩
  · rw [lpOpNorm_top, lpOpNorm_top]
    exact linfty_opNorm_le_mul_of_abs_entrywiseLE fp.u_nonneg (equation_2_7_7 fp hA).2.1
  · rw [PiLp.norm_toLp, PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg fp.u_nonneg (norm_nonneg _))).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (fp.abs_sub_le (hb i)).trans
      (mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm b i))
        fp.u_nonneg)

/-- **Equation (2.7.22)** of [golub2013matrix], the ideal equation solver. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $b \in \mathbb{R}^n$ with $b \neq 0$, and
let $Ax = b$. Let $\hat x$ solve $(A + E) \hat x = b + e$, where
$\|E\|_\infty \le u \|A\|_\infty$ and $\|e\|_\infty \le u \|b\|_\infty$ as in (2.7.21). If
$u \kappa_\infty(A) \le 1/2$, then
$$\frac{\|x - \hat x\|_\infty}{\|x\|_\infty} \le 4 u \kappa_\infty(A).$$

The proof is Theorem 2.6.2 with $\epsilon = u$. The perturbations $E$ and $e$ need only satisfy
the norm bounds; they need not come from rounding. -/
theorem equation_2_7_22 (fp : RoundingModel ℝ) {A E : Matrix (Fin n) (Fin n) ℝ}
    {b e x xh : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hxh : (A + E) *ᵥ xh = b + e) (hE : lpOpNorm ∞ E ≤ fp.u * lpOpNorm ∞ A)
    (he : ‖WithLp.toLp ∞ e‖ ≤ fp.u * ‖WithLp.toLp ∞ b‖)
    (hκ : fp.u * condNumberLp ∞ A ≤ 1 / 2) :
    ‖WithLp.toLp ∞ (x - xh)‖ / ‖WithLp.toLp ∞ x‖ ≤ 4 * fp.u * condNumberLp ∞ A := by
  have h := theorem_2_6_2 ∞ hA hx hb hxh hE he (by linarith)
  rw [← norm_neg, ← WithLp.toLp_neg, neg_sub]
  refine h.trans ?_
  have hu := fp.u_nonneg
  have hκ0 : 0 ≤ condNumberLp ∞ A := mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hu hκ0]

end GolubVanLoan.Chapter02
