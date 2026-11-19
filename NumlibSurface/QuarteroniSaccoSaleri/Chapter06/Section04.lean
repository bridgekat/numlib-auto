/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Polynomial.CauchyBound
import Numlib.RingTheory.Polynomial.Horner
import Numlib.RingTheory.Polynomial.RuleOfSigns
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 6.4: Zeros of Algebraic Equations

This module formalizes Section 6.4 of [quarteroni2000numerical], on the zeros of a polynomial
$p_n(x) = \sum_{k=0}^n a_k x^k$ with real coefficients. Two results localize the zeros: Descartes'
rule of signs (Property 6.5) bounds the number of positive real zeros by the number of sign changes
in the coefficients, and Cauchy's theorem (Property 6.6) puts all complex zeros in the disc
$|z| \le 1 + \max_{k < n} |a_k / a_n|$. Horner's scheme (6.25)–(6.26) evaluates $p_n(z)$, and its
intermediate values $b_k$ are the coefficients of the associated polynomial $q_{n-1}(x; z)$ of
(6.27), the quotient of $p_n$ by $x - z$. This gives the division identity
$p_n(x) = b_0 + (x - z) q_{n-1}(x; z)$, the deflation of a known zero, and the identity
$p_n'(z) = q_{n-1}(z; z)$ behind the Newton–Horner method (6.29).

The module also states division with remainder (6.28), and Muller's method (6.30) with the order of
convergence that the source cites. The proofs specialize `Numlib.RingTheory.Polynomial.Horner`,
`Numlib.RingTheory.Polynomial.RuleOfSigns` and the Muller iteration in `Numlib.Nonlinear.Secant`,
over Mathlib's `Polynomial.divByMonic`, `Polynomial.signVariations` and `Polynomial.cauchyBound`.

## Main definitions

* Equation (6.27), `QuarteroniSaccoSaleri.Chapter06.equation_6_27`: the associated polynomial
  $q_{n-1}(x; z)$, the quotient of $p_n$ by $x - z$.
* Equation (6.29), `QuarteroniSaccoSaleri.Chapter06.equation_6_29`: the Newton–Horner method.
* Equation (6.30), `QuarteroniSaccoSaleri.Chapter06.equation_6_30`: Muller's method, in real
  arithmetic.

## Main results

* Property 6.5, `QuarteroniSaccoSaleri.Chapter06.property_6_5`: the number of positive real roots is
  at most the number of sign changes of the coefficients.
* Property 6.5, `QuarteroniSaccoSaleri.Chapter06.property_6_5_parity`: the difference of the two
  numbers is even.
* Property 6.6, `QuarteroniSaccoSaleri.Chapter06.property_6_6`: every complex zero $z$ satisfies
  $|z| \le 1 + \max_{k < n} |a_k / a_n|$.
* Equations (6.25)–(6.26), `QuarteroniSaccoSaleri.Chapter06.equation_6_26`: Horner's scheme
  evaluates $p_n(z)$, and synthetic division gives the coefficients of the quotient by $x - z$.
* Equation (6.27), `QuarteroniSaccoSaleri.Chapter06.equation_6_27_natDegree` and
  `QuarteroniSaccoSaleri.Chapter06.equation_6_27_coeff`: the associated polynomial has degree
  $n - 1$ and the coefficients $b_1, \dots, b_n$.
* Equation (6.28), `QuarteroniSaccoSaleri.Chapter06.equation_6_28`: division with remainder by a
  polynomial of degree $m \le n$ has a unique quotient and remainder.
* Section 6.4.1, `QuarteroniSaccoSaleri.Chapter06.hornerDivision`:
  $p_n(x) = p_n(z) + (x - z) q_{n-1}(x; z)$.
* Section 6.4.1, `QuarteroniSaccoSaleri.Chapter06.deflation`: at a zero $z$,
  $p_n(x) = (x - z) q_{n-1}(x; z)$, and the other roots of $p_n$ are the roots of $q_{n-1}$.
* Section 6.4.2, `QuarteroniSaccoSaleri.Chapter06.derivative_eq_associatedPolynomial`:
  $p_n'(z) = q_{n-1}(z; z)$.
* Section 6.4.2, `QuarteroniSaccoSaleri.Chapter06.equation_6_29_eq_newton`: the Newton–Horner method
  is Newton's method for $p_n$.
* Section 6.4.3, `QuarteroniSaccoSaleri.Chapter06.muller_order`: Muller's method converges near a
  simple real root with order $p \approx 1.84$ in the sense of Definition 6.1.

## Implementation notes

* Polynomials are Mathlib's `Polynomial` with real coefficients. The associated polynomial
  $q_{n-1}(\cdot; z)$ is `p /ₘ (X - C z)`.
* Coefficient lists are Mathlib's `Polynomial.coeffList`, with the leading coefficient first.
* Muller's method is formalized in real arithmetic only. The square root is `Real.sqrt`, whose value
  is $0$ for a negative radicand, so the formal method finds simple real roots only.

## Deviations from the source

* **Reading.** Descartes' rule skips zero coefficients and states parity for nonzero polynomials.
  See `QuarteroniSaccoSaleri.Chapter06.property_6_5`,
  `QuarteroniSaccoSaleri.Chapter06.property_6_5_parity`.
* **Representation.** Horner's scalar recurrence is packaged as a descending list scan and an
  evaluation identity. See `QuarteroniSaccoSaleri.Chapter06.equation_6_26`.
* **Representation.** The associated polynomial is defined by monic division, with separate degree
  and Horner coefficient identities. See `QuarteroniSaccoSaleri.Chapter06.equation_6_27`,
  `QuarteroniSaccoSaleri.Chapter06.equation_6_27_natDegree`,
  `QuarteroniSaccoSaleri.Chapter06.equation_6_27_coeff`.
* **Reading.** Polynomial division assumes exact degree for the divisor and allows an upper bound on
  the dividend degree. See `QuarteroniSaccoSaleri.Chapter06.equation_6_28`.
* **Specialization.** The deflation theorem is over the real polynomial ring and its multiset
  identity counts real roots. See `QuarteroniSaccoSaleri.Chapter06.deflation`.
* **Specialization.** Newton–Horner is formalized over the reals and uses totalized division. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_29`,
  `QuarteroniSaccoSaleri.Chapter06.equation_6_29_eq_newton`.
* **Specialization.** Muller's recurrence uses real square roots and totalized division. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_30`.
* **Specialization.** Muller's order is the tribonacci constant, with a local bound in place of the
  printed exact quotient limit. See `QuarteroniSaccoSaleri.Chapter06.muller_order`.
* **Property 6.5** (reading). The "number of sign changes" of the coefficients ignores the zero
  coefficients. See `QuarteroniSaccoSaleri.Chapter06.property_6_5`.
* **Property 6.6** (reading). The zeros are the complex zeros of the real polynomial. See
  `QuarteroniSaccoSaleri.Chapter06.property_6_6`.
* **Equation (6.28)** (reading). The divisor $g_m \in \mathbb{P}_m$ has degree exactly $m$, and the
  remainder $\rho \in \mathbb{P}_{m-1}$ has degree less than $m$. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_28`.
* **Section 6.4.3, order of Muller's method** (reading). The order $p \simeq 1.84$ is the real root
  of $p^3 = p^2 + p + 1$, in the sense of Definition 6.1. See
  `QuarteroniSaccoSaleri.Chapter06.muller_order`.

## Not formalized

* **Section 6.4.3, the limit form of the order of Muller's method**, $|e^{(k+1)}| / |e^{(k)}|^p \to
  |f'''(\alpha) / f'(\alpha)| / 6$. The source quotes it from Hildebrand without proof, and the
  backbone proves only two-sided bounds whose constants are not driven to this limit along a single
  orbit.
* **Muller's method in complex arithmetic**, for complex roots.
-/

open Filter Polynomial Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

/-! ### Localization of the zeros -/

section Localization

variable (p : ℝ[X])

/-- **Property 6.5** of [quarteroni2000numerical] (Descartes' rule of signs), first half. Let $p$ be
a real polynomial. The number $k$ of positive real roots of $p$, counted with multiplicity, is
at most the number $\nu$ of sign changes in the sequence of its coefficients.

**Reading.** The sign changes are counted after the zero coefficients are removed. This is
Mathlib's `Polynomial.signVariations`.

For $p = 0$ both numbers are $0$. The proof is Mathlib's
`Polynomial.roots_countP_pos_le_signVariations`.

**Reading.** Sign variations skip zero coefficients. The parity statement applies to nonzero
polynomials and counts positive real roots with multiplicity.
-/
theorem property_6_5 : p.roots.countP (0 < ·) ≤ p.signVariations :=
  roots_countP_pos_le_signVariations p

/-- **Property 6.5** of [quarteroni2000numerical] (Descartes' rule of signs), second half. Let
$p \neq 0$ be a real polynomial, let $k$ be the number of its positive real roots, counted with
multiplicity, and let $\nu$ be the number of sign changes in its coefficients. Then $\nu - k$ is
even.

The difference is the truncated difference of natural numbers; by the first half it is the true
difference. The proof is the backbone's `Polynomial.even_signVariations_sub_roots_countP_pos`.

**Reading.** Sign variations skip zero coefficients. The parity statement applies to nonzero
polynomials and counts positive real roots with multiplicity.
-/
theorem property_6_5_parity (hp : p ≠ 0) : Even (p.signVariations - p.roots.countP (0 < ·)) :=
  even_signVariations_sub_roots_countP_pos hp

/-- **Property 6.6** of [quarteroni2000numerical] (Cauchy's theorem). Let
$p_n(x) = \sum_{k=0}^n a_k x^k$ be a real polynomial of degree $n \ge 1$, and let
$z \in \mathbb{C}$ be a zero of $p_n$. Then
$$|z| \le 1 + \eta, \qquad \eta = \max_{0 \le k \le n-1} \left| \frac{a_k}{a_n} \right|.$$

**Reading.** The source says that all zeros of $p_n$ lie in the disc. The statement takes the
complex zeros of the real polynomial, as roots of `p.map Complex.ofRealHom`.

The proof uses Mathlib's `Polynomial.IsRoot.norm_lt_cauchyBound`, whose bound
$\max_k |a_k| / |a_n| + 1$ is $1 + \eta$ and whose inequality is strict. -/
theorem property_6_6 (hn : 0 < p.natDegree) {z : ℂ} (hz : (p.map Complex.ofRealHom).IsRoot z) :
    ‖z‖ ≤ 1 + (Finset.range p.natDegree).sup' (Finset.nonempty_range_iff.2 hn.ne')
      (fun k => |p.coeff k / p.leadingCoeff|) := by
  set η := (Finset.range p.natDegree).sup' (Finset.nonempty_range_iff.2 hn.ne')
    (fun k => |p.coeff k / p.leadingCoeff|) with hη
  have hp : p ≠ 0 := ne_zero_of_natDegree_gt hn
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp
  have hbound := hz.norm_lt_cauchyBound (map_ne_zero hp)
  have hη0 : 0 ≤ η :=
    (abs_nonneg _).trans (Finset.le_sup' (fun k => |p.coeff k / p.leadingCoeff|)
      (Finset.mem_range.2 hn))
  -- the Cauchy bound of the complexified polynomial is at most `1 + η`
  have hcb : (cauchyBound (p.map Complex.ofRealHom) : ℝ) ≤ 1 + η := by
    rw [cauchyBound, NNReal.coe_add, NNReal.coe_one, NNReal.coe_div, add_comm]
    gcongr
    rw [div_le_iff₀ (by simpa [leadingCoeff_map, Complex.nnnorm_real] using hlc),
      leadingCoeff_map, Complex.ofRealHom_eq_coe, Complex.nnnorm_real, coe_nnnorm,
      Real.norm_eq_abs]
    have hη0' : 0 ≤ η * |p.leadingCoeff| := mul_nonneg hη0 (abs_nonneg _)
    have hS : ((Finset.range (p.map Complex.ofRealHom).natDegree).sup
        fun k => ‖(p.map Complex.ofRealHom).coeff k‖₊) ≤ (η * |p.leadingCoeff|).toNNReal := by
      refine Finset.sup_le fun k hk => ?_
      rw [natDegree_map] at hk
      rw [Real.le_toNNReal_iff_coe_le hη0', coe_nnnorm, coeff_map, Complex.ofRealHom_eq_coe,
        Complex.norm_real, Real.norm_eq_abs]
      calc |p.coeff k| = |p.coeff k / p.leadingCoeff| * |p.leadingCoeff| := by
            rw [abs_div, div_mul_cancel₀ _ (abs_ne_zero.2 hlc)]
        _ ≤ η * |p.leadingCoeff| := by
            gcongr
            exact Finset.le_sup' (fun k => |p.coeff k / p.leadingCoeff|) hk
    have := NNReal.coe_le_coe.2 hS
    rwa [Real.coe_toNNReal _ hη0'] at this
  calc ‖z‖ = (‖z‖₊ : ℝ) := (coe_nnnorm z).symm
    _ ≤ (cauchyBound (p.map Complex.ofRealHom) : ℝ) := by exact_mod_cast hbound.le
    _ ≤ 1 + η := hcb

end Localization

/-! ### Section 6.4.1: The Horner method and deflation -/

section Horner

variable (p : ℝ[X]) (z : ℝ)

/-- **Equations (6.25)–(6.26)** of [quarteroni2000numerical], Horner's scheme and synthetic
division. Let $p_n(x) = \sum_{k=0}^n a_k x^k$ be a real polynomial and $z \in \mathbb{R}$. Then:

* the nested form $a_0 + z(a_1 + z(a_2 + \cdots + z a_n))$ is $p_n(z)$;
* if $p_n \neq 0$, the values $b_n = a_n$ and $b_k = a_k + b_{k+1} z$ for $k = n - 1, \dots, 0$
  of the synthetic division algorithm are the coefficients $b_n, \dots, b_1$ of the quotient of
  $p_n$ by $x - z$, followed by $b_0 = p_n(z)$.

The nested form is `Polynomial.hornerEval` and the list $[b_n, \dots, b_0]$ is
`Polynomial.hornerScan`, both applied to the coefficient list $[a_n, \dots, a_0]$. The proof
specializes `Polynomial.hornerEval_coeffList` and `Polynomial.hornerScan_coeffList`.

**Reading.** The Horner scan of the descending coefficient list is identified with the quotient's
coefficient list followed by the remainder, and evaluation is also supplied at the zero polynomial.
-/
theorem equation_6_26 :
    hornerEval p.coeffList z = p.eval z ∧
      (p ≠ 0 → hornerScan p.coeffList z = (p /ₘ (X - C z)).coeffList ++ [p.eval z]) :=
  ⟨hornerEval_coeffList p z, fun hp => hornerScan_coeffList hp z⟩

/-- **Equation (6.27)** of [quarteroni2000numerical]. The **associated polynomial** of the real
polynomial $p_n$ at $z \in \mathbb{R}$ is
$$q_{n-1}(x; z) = \sum_{k=1}^n b_k x^{k-1},$$
with $b_k$ the values of the synthetic division (6.26). It is defined as the quotient
`p /ₘ (X - C z)` of $p_n$ by $x - z$.

**Reading.** The associated polynomial is defined by monic division, with the degree and coefficient
formulas proved separately in their stated ranges. The quotient is defined even for zero or constant
input.
-/
noncomputable def equation_6_27 (p : ℝ[X]) (z : ℝ) : ℝ[X] := p /ₘ (X - C z)

/-- The associated polynomial $q_{n-1}(\cdot; z)$ of a real polynomial $p_n$ of degree $n \ge 1$ has
degree $n - 1$. The proof is `Polynomial.natDegree_divByMonic_X_sub_C`.

**Reading.** The associated polynomial is defined by monic division, with the degree and coefficient
formulas proved separately in their stated ranges. The quotient is defined even for zero or constant
input.
-/
theorem equation_6_27_natDegree (hn : 0 < p.natDegree) :
    (equation_6_27 p z).natDegree = p.natDegree - 1 :=
  (natDegree_divByMonic_X_sub_C hn z).2

/-- The coefficients of the associated polynomial $q_{n-1}(\cdot; z)$ are the values $b_k$,
$k \ge 1$, of (6.26). Let $p_n$ have degree $n$, and let $i < n$. Then the entry of index $i$ of
the list $[b_n, \dots, b_1, b_0]$ of synthetic division is the coefficient of $x^{n-1-i}$ in
$q_{n-1}(\cdot; z)$.

The list is `Polynomial.hornerScan` of the coefficient list, indexed from $0$. The proof uses
`Polynomial.hornerEval_take_coeffList`.

**Reading.** The associated polynomial is defined by monic division, with the degree and coefficient
formulas proved separately in their stated ranges. The quotient is defined even for zero or constant
input.
-/
theorem equation_6_27_coeff {i : ℕ} (hi : i < p.natDegree) :
    (hornerScan p.coeffList z)[i]'(by simp [coeffList,
      withBotSucc_degree_eq_natDegree_add_one (ne_zero_of_natDegree_gt hi)]; omega) =
      (equation_6_27 p z).coeff (p.natDegree - 1 - i) := by
  rw [getElem_hornerScan _ _ (by simp [coeffList,
    withBotSucc_degree_eq_natDegree_add_one (ne_zero_of_natDegree_gt hi)]; omega),
    hornerEval_take_coeffList p z hi]
  rfl

/-- **Equation (6.28)** of [quarteroni2000numerical], division of polynomials. Let $m \le n$, let
$h$ be a real polynomial of degree at most $n$, and let $g$ be a real polynomial of degree $m$.
Then there is exactly one pair $(\delta, \rho)$ of real polynomials with
$\deg \delta \le n - m$, $\deg \rho < m$ and
$$h = g \delta + \rho.$$

**Reading.** The source writes $h_n \in \mathbb{P}_n$, $g_m \in \mathbb{P}_m$,
$\delta \in \mathbb{P}_{n-m}$ and $\rho \in \mathbb{P}_{m-1}$. Here $g_m$ has degree exactly
$m$, because otherwise the remainder is not unique, and $\rho \in \mathbb{P}_{m-1}$ means
$\deg \rho < m$, which also covers $m = 0$.

The proof uses Mathlib's `Polynomial.divByMonic` and `Polynomial.modByMonic` by the monic
polynomial $g / \operatorname{lc}(g)$, with `Polynomial.div_modByMonic_unique` for the
uniqueness.

**Reading.** The divisor must have exact degree m, because otherwise the quotient degree bound and
uniqueness with remainders of degree below m fail. The dividend can have any degree at most n.
-/
theorem equation_6_28 {h g : ℝ[X]} {n m : ℕ} (hh : h.degree ≤ n) (hg : g.degree = m)
    (_hmn : m ≤ n) :
    ∃! δρ : ℝ[X] × ℝ[X], δρ.1.degree ≤ (n - m : ℕ) ∧ δρ.2.degree < m ∧ h = g * δρ.1 + δρ.2 := by
  have hg0 : g ≠ 0 := fun h0 => by simp [h0] at hg
  set g' : ℝ[X] := g * C g.leadingCoeff⁻¹ with hg'
  have hmonic : g'.Monic := monic_mul_leadingCoeff_inv hg0
  have hg'deg : g'.degree = m := by rw [hg', degree_mul_leadingCoeff_inv g hg0, hg]
  have hg'nat : g'.natDegree = m := natDegree_eq_of_degree_eq_some hg'deg
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hg0
  -- `g * (C lc⁻¹ * q) = g' * q`
  have hgq : ∀ q : ℝ[X], g * (C g.leadingCoeff⁻¹ * q) = g' * q := fun q => by
    rw [hg', mul_assoc]
  refine ⟨(C g.leadingCoeff⁻¹ * (h /ₘ g'), h %ₘ g'), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- the degree of the quotient
    refine (degree_mul_le _ _).trans ?_
    rw [degree_C (inv_ne_zero hlc), zero_add]
    refine degree_le_natDegree.trans ?_
    rw [natDegree_divByMonic _ hmonic, hg'nat]
    exact_mod_cast Nat.sub_le_sub_right (natDegree_le_of_degree_le hh) m
  · rw [← hg'deg]
    exact degree_modByMonic_lt h hmonic
  · rw [hgq]
    conv_lhs => rw [← h.modByMonic_add_div g']
    exact add_comm _ _
  · rintro ⟨δ, ρ⟩ ⟨-, hρ, heq⟩
    have hunique := div_modByMonic_unique (f := h) (g := g') (C g.leadingCoeff * δ) ρ hmonic
      ⟨by rw [hg', mul_assoc, ← mul_assoc (C _), ← C_mul, inv_mul_cancel₀ hlc, C_1, one_mul,
        add_comm, heq], by rwa [hg'deg]⟩
    refine Prod.ext ?_ hunique.2.symm
    simp only
    rw [hunique.1, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, one_mul]

/-- **Section 6.4.1** of [quarteroni2000numerical], the identity after (6.28) for synthetic
division. Let $p_n$ be a real polynomial and $z \in \mathbb{R}$. Division of $p_n$ by $x - z$
gives the quotient $q_{n-1}(\cdot; z)$ and the remainder $b_0 = p_n(z)$:
$$p_n(x) = p_n(z) + (x - z) q_{n-1}(x; z).$$

The proof is `Polynomial.eq_X_sub_C_mul_divByMonic_add_C_eval`. -/
theorem hornerDivision : p = C (p.eval z) + (X - C z) * equation_6_27 p z := by
  rw [add_comm]
  exact eq_X_sub_C_mul_divByMonic_add_C_eval p z

/-- **Section 6.4.1** of [quarteroni2000numerical], deflation. Let $p_n$ be a real polynomial and
let $z$ be a zero of $p_n$. Then $p_n(x) = (x - z) q_{n-1}(x; z)$. If moreover $p_n \neq 0$, the
roots of $p_n$, counted with multiplicity, are $z$ together with the roots of
$q_{n-1}(\cdot; z)$.

So the equation $q_{n-1}(x; z) = 0$ gives the remaining $n - 1$ roots of $p_n$. The proof uses
Mathlib's `Polynomial.mul_divByMonic_eq_iff_isRoot` and `Polynomial.roots_divByMonic_X_sub_C`.

**Reading.** The factorization divides out a real root, and the multiset identity deletes one copy
among the real roots of a nonzero polynomial. The source also applies deflation to complex roots.
-/
theorem deflation (hz : p.IsRoot z) :
    p = (X - C z) * equation_6_27 p z ∧
      (p ≠ 0 → p.roots = (equation_6_27 p z).roots + {z}) :=
  ⟨(mul_divByMonic_eq_iff_isRoot.2 hz).symm, fun hp => roots_divByMonic_X_sub_C hp hz⟩

end Horner

/-! ### Section 6.4.2: The Newton–Horner method -/

section NewtonHorner

variable (p : ℝ[X]) (z : ℝ)

/-- **Section 6.4.2** of [quarteroni2000numerical]. Let $p_n$ be a real polynomial and
$z \in \mathbb{R}$. Then
$$p_n'(z) = q_{n-1}(z; z).$$

Since $p_n(x) = p_n(z) + (x - z) q_{n-1}(x; z)$, the derivative is
$p_n' = q_{n-1} + (x - z) q_{n-1}'$, and its value at $z$ is $q_{n-1}(z; z)$. The proof is
`Polynomial.eval_divByMonic_X_sub_C_self`. -/
theorem derivative_eq_associatedPolynomial :
    p.derivative.eval z = (equation_6_27 p z).eval z :=
  (eval_divByMonic_X_sub_C_self p z).symm

/-- **Equation (6.29)** of [quarteroni2000numerical], the **Newton–Horner method** for a real
polynomial $p_n$:
$$r^{(k+1)} = r^{(k)} - \frac{p_n(r^{(k)})}{q_{n-1}(r^{(k)}; r^{(k)})},$$
where synthetic division supplies the derivative $p_n'(r^{(k)}) = q_{n-1}(r^{(k)}; r^{(k)})$.

The value at $k$ is the $k$-th iterate of the backbone's `NewtonHorner.step` from $r^{(0)}$. The
source recommends complex arithmetic for complex roots; `NewtonHorner.step` is defined over any
field, so that variant is the same definition over `ℂ[X]`.

**Reading.** The Newton–Horner formula is for real polynomials and iterates. The text also allows
complex arithmetic. Zero derivative is handled by totalized division.
-/
noncomputable def equation_6_29 (p : ℝ[X]) (r₀ : ℝ) (k : ℕ) : ℝ := (NewtonHorner.step p)^[k] r₀

/-- The Newton–Horner method (6.29) for a real polynomial $p_n$ is Newton's method (6.16) for
$f = p_n$ with $f' = p_n'$: for every $r^{(0)}$ and $k$ the two iterates agree.

So `QuarteroniSaccoSaleri.Chapter06.newton_order_two` and
`QuarteroniSaccoSaleri.Chapter06.equation_6_22`, with
`Polynomial.isRootOfMultiplicity_eval_iff`, describe its convergence. The proof uses
`NewtonHorner.step_eq`.

**Reading.** The Newton–Horner formula is for real polynomials and iterates. The text also allows
complex arithmetic. Zero derivative is handled by totalized division.
-/
theorem equation_6_29_eq_newton (r₀ : ℝ) (k : ℕ) :
    equation_6_29 p r₀ k = newton (fun x => p.eval x) (fun x => p.derivative.eval x) r₀ k := by
  rw [equation_6_29, newton]
  congr 1
  funext x
  rw [NewtonHorner.step_eq]
  rfl

end NewtonHorner

/-! ### Section 6.4.3: The Muller method -/

section Muller

/-- **Equation (6.30)** of [quarteroni2000numerical], **Muller's method**. From three distinct
starting values $x^{(0)}, x^{(1)}, x^{(2)}$, it computes
$$x^{(k+1)} = x^{(k)} - \frac{2 f(x^{(k)})}{w \mp \sqrt{w^2 - 4 f(x^{(k)}) f[x^{(k)}, x^{(k-1)},
  x^{(k-2)}]}},$$
with $w = f[x^{(k)}, x^{(k-1)}] + (x^{(k)} - x^{(k-1)}) f[x^{(k)}, x^{(k-1)}, x^{(k-2)}]$. This
is the zero of the quadratic interpolant of $f$ at the last three iterates, with the sign that
maximizes the modulus of the denominator.

The method is in real arithmetic only, as `Muller.iterate`, and the square root of a negative
radicand is $0$. The index is shifted: the value at $k$ is the iterate $x^{(k+2)}$ of the
source, so the value at $0$ is $x^{(2)}$.

**Reading.** The step uses real square roots and totalized division. The source allows complex
iterates when the interpolating quadratic gives a nonreal root.
-/
noncomputable def equation_6_30 (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) (k : ℕ) : ℝ :=
  Muller.iterate f x₀ x₁ x₂ k

/-- **Section 6.4.3** of [quarteroni2000numerical], the order of Muller's method. Let
$f(\alpha) = 0$, let $f$ be of class $C^3$ on a neighbourhood of $\alpha$, and let
$f'(\alpha) \neq 0$ and $f'''(\alpha) \neq 0$. Then there is $\varepsilon > 0$ such that for any
three distinct starting values $x^{(0)}, x^{(1)}, x^{(2)} \in (\alpha - \varepsilon, \alpha +
\varepsilon)$, none of them equal to $\alpha$, the sequence (6.30) converges to $\alpha$ with
order $p$ in the sense of Definition 6.1, where $p \approx 1.8393$ is the real root of
$p^3 = p^2 + p + 1$.

**Reading.** The source states the order $p \simeq 1.84$. Here $p$ is the exact root
`Real.tribonacci`, and the order is the one of Definition 6.1. The source also states the limit
$|e^{(k+1)}| / |e^{(k)}|^p \to |f'''(\alpha) / f'(\alpha)| / 6$, quoted from Hildebrand without
proof. This limit is not formalized: the backbone proves the two-sided bounds of
`Muller.LocalData.step_bounds`, whose constants tend to $|f'''(\alpha) / (6 f'(\alpha))|$ as the
ball and the tolerance shrink, but are not driven to it along a single orbit. Property 6.2 for
the secant method is treated in the same way.

The hypothesis $f'''(\alpha) \neq 0$ plays the role that $f''(\alpha) \neq 0$ plays for the
secant method in `QuarteroniSaccoSaleri.Chapter06.property_6_2`. The proof specializes
`Muller.exists_ball_convergesWithOrder`.

**Reading.** The theorem states a local convergence-order bound for distinct real starting points
avoiding the root and assumes a nonzero third derivative. It uses the exact tribonacci order and
leaves the displayed quotient limit and constant unstated.
-/
theorem muller_order {f : ℝ → ℝ} {α : ℝ} (hf : ContDiffAt ℝ 3 f α) (hα : f α = 0)
    (hf' : deriv f α ≠ 0) (hf3 : iteratedDeriv 3 f α ≠ 0) :
    ∃ ε > 0, ∀ x₀ ∈ Ioo (α - ε) (α + ε), ∀ x₁ ∈ Ioo (α - ε) (α + ε),
      ∀ x₂ ∈ Ioo (α - ε) (α + ε), x₀ ≠ x₁ → x₀ ≠ x₂ → x₁ ≠ x₂ → x₀ ≠ α → x₁ ≠ α → x₂ ≠ α →
      definition_6_1 (equation_6_30 f x₀ x₁ x₂) α Real.tribonacci := by
  obtain ⟨ε, hε, h⟩ := Muller.exists_ball_convergesWithOrder hα hf hf' hf3
  refine ⟨ε, hε, fun x₀ h0 x₁ h1 x₂ h2 n01 n02 n12 a0 a1 a2 => ?_⟩
  rw [← Real.ball_eq_Ioo] at h0 h1 h2
  exact definition_6_1_of_convergesWithOrder Real.one_lt_tribonacci.le
    (h x₀ h0 x₁ h1 x₂ h2 n01 n02 n12 a0 a1 a2)

end Muller

end QuarteroniSaccoSaleri.Chapter06
