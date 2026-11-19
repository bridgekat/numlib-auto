/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Numlib.Eigen.Sturm
import Numlib.RingTheory.Polynomial.Horner
import NumlibSurface.LiesenStrakos.Chapter03.Section02
import NumlibSurface.LiesenStrakos.Chapter03.Section03.SignChanges

/-!
# Orthogonal polynomials and continued fractions

The roots of consecutive monic orthogonal polynomials strictly interlace. Their recurrence
coefficients form a Jacobi continued fraction whose convergents represent the resolvent
quadratures of §3.3 of [liesen2013krylov].

## Main definitions

* `LiesenStrakos.Chapter03.stieltjesRationalConvergent` is the finite continued fraction as
  a rational function.
* `LiesenStrakos.Chapter03.secondKindPolynomial` integrates the polynomial divided
  difference of the monic orthogonal polynomial.

## Main results

* `LiesenStrakos.Chapter03.theorem_3_3_1` puts a higher-order node in each gap between
  roots of a lower-degree orthogonal polynomial, and beyond its two extreme roots.
* `LiesenStrakos.Chapter03.corollary_3_3_3` proves strict interlacing for consecutive orthogonal
  polynomials, including the terminal polynomial of a finite distribution.
* `LiesenStrakos.Chapter03.theorem_3_3_4` counts the sign changes in the difference of
  consecutive Gauss distribution functions.
* `LiesenStrakos.Chapter03.theorem_3_3_5` gives the numerator and denominator of a convergent.
* `LiesenStrakos.Chapter03.theorem_3_3_6` identifies its poles and residues with the Gauss rule.
* `LiesenStrakos.Chapter03.gaussResolvent_tendsto` proves convergence of the resolvent quadratures.

## Deviations from the source

* **Section 3.3** (reading). Interlacing and partial fractions use explicit support,
  integrability or exactness hypotheses. The continued fraction and second-kind definitions are
  total. The resolvent convergence theorem is stated for real parameters.
-/

open Filter MeasureTheory OrthogonalPolynomial Polynomial Topology
open scoped Polynomial

namespace LiesenStrakos.Chapter03

private noncomputable def continuedFractionTail (μ : Measure ℝ) : ℕ → ℕ → RatFunc ℝ
  | 0, _ => 0
  | m + 1, i =>
    (RatFunc.X - RatFunc.C (alpha μ i) -
      RatFunc.C (beta μ i) * continuedFractionTail μ m (i + 1))⁻¹

/-- The $n$th Stieltjes convergent is the finite Jacobi continued fraction with denominators
$X-\alpha_0,\ldots,X-\alpha_{n-1}$ and interior numerators $-\beta_0,\ldots,-\beta_{n-2}$.
This is (3.3.17)–(3.3.18) of [liesen2013krylov].

**Generalization.** The algebraic recursion is defined at every index, including zero and
indices beyond a finite support. -/
noncomputable def stieltjesRationalConvergent (μ : Measure ℝ) (n : ℕ) : RatFunc ℝ :=
  continuedFractionTail μ n 0

private noncomputable def shiftedContinuant (μ : Measure ℝ) : ℕ → ℕ → ℝ[X]
  | 0, _ => 1
  | 1, i => X - C (alpha μ i)
  | k + 2, i => (X - C (alpha μ i)) * shiftedContinuant μ (k + 1) (i + 1) -
      C (beta μ i) * shiftedContinuant μ k (i + 2)

private theorem shiftedContinuant_monic_degree (μ : Measure ℝ) :
    ∀ n i, (shiftedContinuant μ n i).Monic ∧ (shiftedContinuant μ n i).degree = n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro i; simp [shiftedContinuant]
  | one => intro i; exact ⟨monic_X_sub_C _, degree_X_sub_C _⟩
  | more n ih₀ ih₁ =>
    intro i
    have hmonic := (monic_X_sub_C (alpha μ i)).mul (ih₁ (i + 1)).1
    have hd₁ : ((X - C (alpha μ i)) * shiftedContinuant μ (n + 1) (i + 1)).degree = ↑(n + 2) := by
      rw [degree_mul, degree_X_sub_C, (ih₁ (i + 1)).2]
      norm_cast
      omega
    have hd₀ : (C (beta μ i) * shiftedContinuant μ n (i + 2)).degree ≤ (n : WithBot ℕ) := by
      simpa only [(ih₀ (i + 2)).2, zero_add] using
        degree_mul_le_of_le (degree_C_le (a := beta μ i)) ((ih₀ (i + 2)).2.le)
    have hlt : (C (beta μ i) * shiftedContinuant μ n (i + 2)).degree <
        ((X - C (alpha μ i)) * shiftedContinuant μ (n + 1) (i + 1)).degree := by
      rw [hd₁]
      exact hd₀.trans_lt (by exact_mod_cast (by omega : n < n + 2))
    rw [shiftedContinuant]
    exact ⟨by rw [sub_eq_add_neg]; exact hmonic.add_of_left (by simpa only [degree_neg]),
      (degree_sub_eq_left_of_degree_lt hlt).trans hd₁⟩

private theorem shiftedContinuant_append (μ : Measure ℝ) :
    ∀ n i, shiftedContinuant μ (n + 2) i =
      (X - C (alpha μ (i + n + 1))) * shiftedContinuant μ (n + 1) i -
        C (beta μ (i + n)) * shiftedContinuant μ n i := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro i; simp [shiftedContinuant]; ring
  | one => intro i; simp [shiftedContinuant, Nat.add_assoc]; ring
  | more n ih₀ ih₁ =>
    intro i
    have hbig : shiftedContinuant μ (n + 2 + 2) i =
        (X - C (alpha μ i)) * shiftedContinuant μ (n + 2 + 1) (i + 1) -
          C (beta μ i) * shiftedContinuant μ (n + 2) (i + 2) := by rw [shiftedContinuant]
    have hmid : shiftedContinuant μ (n + 2 + 1) i =
        (X - C (alpha μ i)) * shiftedContinuant μ (n + 2) (i + 1) -
          C (beta μ i) * shiftedContinuant μ (n + 1) (i + 2) := by rw [shiftedContinuant]
    have hsmall : shiftedContinuant μ (n + 2) i =
        (X - C (alpha μ i)) * shiftedContinuant μ (n + 1) (i + 1) -
          C (beta μ i) * shiftedContinuant μ n (i + 2) := by rw [shiftedContinuant]
    rw [hbig, ih₁ (i + 1), ih₀ (i + 2), hmid, hsmall]
    simp only [
      show i + 1 + (n + 1) = i + (n + 2) by omega,
      show i + 2 + n = i + (n + 2) by omega]
    ring

private theorem shiftedContinuant_eq_family {μ : Measure ℝ}
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) :
    ∀ n, (∀ j < n, normSq μ j ≠ 0) → shiftedContinuant μ n 0 = family μ n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro _; simp [shiftedContinuant]
  | one => intro _; rw [shiftedContinuant, family_one]
  | more n h₀ h₁ =>
    intro hnorm
    rw [shiftedContinuant_append, zero_add, h₀ (fun j hj => hnorm j (by omega)),
      h₁ (fun j hj => hnorm j (by omega)), three_term_recurrence_of_integrable hint hnorm]

private theorem continuedFractionTail_succ_eq (μ : Measure ℝ) :
    ∀ n i, continuedFractionTail μ (n + 1) i =
      algebraMap ℝ[X] (RatFunc ℝ) (shiftedContinuant μ n (i + 1)) /
        algebraMap ℝ[X] (RatFunc ℝ) (shiftedContinuant μ (n + 1) i) := by
  intro n
  induction n with
  | zero =>
    intro i
    simp [continuedFractionTail, shiftedContinuant, one_div]
  | succ n ih =>
    intro i
    let f := algebraMap ℝ[X] (RatFunc ℝ)
    have hne : f (shiftedContinuant μ (n + 1) (i + 1)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (shiftedContinuant_monic_degree μ _ _).1.ne_zero
    have hdiv :
        RatFunc.X - RatFunc.C (alpha μ i) -
          RatFunc.C (beta μ i) *
            (f (shiftedContinuant μ n (i + 2)) / f (shiftedContinuant μ (n + 1) (i + 1))) =
        f (shiftedContinuant μ (n + 2) i) / f (shiftedContinuant μ (n + 1) (i + 1)) := by
      rw [eq_div_iff hne]
      rw [sub_mul, mul_assoc (RatFunc.C _), div_mul_cancel₀ _ hne]
      simp only [shiftedContinuant, f, map_sub, map_mul, RatFunc.algebraMap_X,
        RatFunc.algebraMap_C]
    rw [continuedFractionTail, ih, hdiv, inv_div]
private noncomputable def quotientCoeff (p : ℝ[X]) (k : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.Icc (k + 1) p.natDegree, C (p.coeff i) * X ^ (i - (k + 1))

private theorem eval_quotientCoeff (p : ℝ[X]) (k : ℕ) (t : ℝ) :
    (quotientCoeff p k).eval t = (p /ₘ (X - C t)).coeff k := by
  simp only [quotientCoeff, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    coeff_divByMonic_X_sub_C, mul_comm (p.coeff _)]

private noncomputable def quotientEval (p : ℝ[X]) (z : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1), C (z ^ k) * quotientCoeff p k

private theorem eval_quotientEval (p : ℝ[X]) (z t : ℝ) :
    (quotientEval p z).eval t = (p /ₘ (X - C t)).eval z := by
  have hdeg : (p /ₘ (X - C t)).natDegree < p.natDegree + 1 := by
    rw [natDegree_divByMonic p (monic_X_sub_C t), natDegree_X_sub_C]
    omega
  rw [eval_eq_sum_range' hdeg]
  simp only [quotientEval, eval_finsetSum, eval_mul, eval_C, eval_quotientCoeff,
    mul_comm (z ^ _)]

private theorem degree_quotientCoeff_lt (p : ℝ[X]) (k : ℕ) :
    (quotientCoeff p k).degree < (p.natDegree : WithBot ℕ) := by
  unfold quotientCoeff
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  have hil := (Finset.mem_Icc.1 hi).1
  have hir := (Finset.mem_Icc.1 hi).2
  refine (degree_mul_le_of_le degree_C_le (degree_X_pow (i - (k + 1))).le).trans_lt ?_
  rw [zero_add]
  exact_mod_cast (show i - (k + 1) < p.natDegree by omega)

private theorem degree_quotientEval_lt (p : ℝ[X]) (z : ℝ) :
    (quotientEval p z).degree < (p.natDegree : WithBot ℕ) := by
  unfold quotientEval
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro k _
  refine (degree_mul_le_of_le degree_C_le le_rfl).trans_lt ?_
  rw [zero_add]
  exact degree_quotientCoeff_lt p k

private noncomputable def secondKindOf (μ : Measure ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1), C (∫ t, (quotientCoeff p k).eval t ∂μ) * X ^ k

/-- The second-kind polynomial is the coefficientwise integral of the polynomial divided
difference $(\psi_n(X)-\psi_n(t))/(X-t)$ against $\mu$. The monic quotient by $X-C(t)$
has this value, including at $X=t$ by polynomial evaluation. This is (3.3.20)
of [liesen2013krylov].

**Generalization.** This coefficientwise construction is defined for any measure and index
using total integration. -/
noncomputable def secondKindPolynomial (μ : Measure ℝ) (n : ℕ) : ℝ[X] :=
  secondKindOf μ (family μ n)

private theorem eval_secondKindOf {μ : Measure ℝ}
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) (p : ℝ[X]) (z : ℝ) :
    (secondKindOf μ p).eval z = ∫ t, (p /ₘ (X - C t)).eval z ∂μ := by
  simp_rw [← eval_quotientEval]
  simp only [secondKindOf, quotientEval, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [integral_finsetSum _ fun k _ => (hint (quotientCoeff p k)).const_mul (z ^ k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, mul_comm]

private theorem quotient_mul_affine (p : ℝ[X]) (a t : ℝ) :
    ((X - C a) * p) /ₘ (X - C t) =
      (X - C a) * (p /ₘ (X - C t)) + C (p.eval t) := by
  refine (div_modByMonic_unique _ (C (((X - C a) * p).eval t)) (monic_X_sub_C t)
    ⟨?_, degree_C_le.trans_lt (by rw [degree_X_sub_C]; decide)⟩).1
  calc
    C (((X - C a) * p).eval t) +
        (X - C t) * ((X - C a) * (p /ₘ (X - C t)) + C (p.eval t)) =
          (X - C a) * ((X - C t) * (p /ₘ (X - C t)) + C (p.eval t)) := by
      simp only [eval_mul, eval_sub, eval_X, eval_C, map_mul, map_sub]
      ring
    _ = (X - C a) * p := by rw [← eq_X_sub_C_mul_divByMonic_add_C_eval]

private theorem quotient_mul_C (p : ℝ[X]) (a t : ℝ) :
    (C a * p) /ₘ (X - C t) = C a * (p /ₘ (X - C t)) := by
  refine (div_modByMonic_unique _ (C ((C a * p).eval t)) (monic_X_sub_C t)
    ⟨?_, degree_C_le.trans_lt (by rw [degree_X_sub_C]; decide)⟩).1
  calc
    C ((C a * p).eval t) + (X - C t) * (C a * (p /ₘ (X - C t))) =
        C a * ((X - C t) * (p /ₘ (X - C t)) + C (p.eval t)) := by
      simp only [eval_mul, eval_C, map_mul]
      ring
    _ = C a * p := by rw [← eq_X_sub_C_mul_divByMonic_add_C_eval]

private theorem secondKindOf_recurrence {μ : Measure ℝ}
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ)
    (n : ℕ) (hnorm : ∀ j < n + 2, normSq μ j ≠ 0) :
    secondKindOf μ (family μ (n + 2)) =
      (X - C (alpha μ (n + 1))) * secondKindOf μ (family μ (n + 1)) -
        C (beta μ n) * secondKindOf μ (family μ n) := by
  apply Polynomial.funext
  intro z
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_secondKindOf hint]
  have hf (p : ℝ[X]) : Integrable (fun t => (p /ₘ (X - C t : ℝ[X])).eval z) μ := by
    simp_rw [← eval_quotientEval]
    exact hint _
  let p := family μ (n + 1)
  let q := family μ n
  let a := alpha μ (n + 1)
  let b := beta μ n
  have hp : ∫ t, p.eval t ∂μ = 0 := by
    have h := integral_family_mul_of_degree_lt_of_integrable hint (n := n + 1)
      (fun j hj => hnorm j (by omega)) (q := 1)
      (by rw [degree_one]; exact_mod_cast n.succ_pos)
    simpa [p] using h
  have heval (t : ℝ) : ((family μ (n + 2)) /ₘ (X - C t)).eval z =
      ((z - a) * (p /ₘ (X - C t)).eval z + p.eval t) -
        b * (q /ₘ (X - C t)).eval z := by
    rw [three_term_recurrence_of_integrable hint hnorm, sub_divByMonic, quotient_mul_affine,
      quotient_mul_C]
    simp [p, q, a, b]
  simp_rw [heval]
  let F : ℝ → ℝ := fun t => (z - a) * (p /ₘ (X - C t)).eval z
  let G : ℝ → ℝ := fun t => p.eval t
  let H : ℝ → ℝ := fun t => b * (q /ₘ (X - C t)).eval z
  have hF : Integrable F μ := (hf p).const_mul (z - a)
  have hG : Integrable G μ := hint p
  have hH : Integrable H μ := (hf q).const_mul b
  change (∫ t, (F + G) t - H t ∂μ) = _
  rw [integral_sub (hF.add hG) hH]
  change (∫ t, F t + G t ∂μ) - (∫ t, H t ∂μ) = _
  rw [integral_add hF hG]
  unfold F G H
  rw [integral_const_mul, integral_const_mul, hp, add_zero]

private theorem secondKindOf_family_zero {μ : Measure ℝ}
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) :
    secondKindOf μ (family μ 0) = 0 := by
  apply Polynomial.funext
  intro z
  rw [eval_secondKindOf hint, family_zero, eval_zero]
  have hd (t : ℝ) : (1 : ℝ[X]) /ₘ (X - C t) = 0 :=
    (divByMonic_eq_zero_iff (monic_X_sub_C t)).2 (by rw [degree_one, degree_X_sub_C]; decide)
  simp [hd]

private theorem secondKindOf_family_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) :
    secondKindOf μ (family μ 1) = 1 := by
  apply Polynomial.funext
  intro z
  rw [eval_secondKindOf hint, family_one, eval_one]
  have hd (t : ℝ) : (X - C (alpha μ 0)) /ₘ (X - C t) = 1 := by
    refine (div_modByMonic_unique 1 (C (t - alpha μ 0)) (monic_X_sub_C t)
      ⟨?_, degree_C_le.trans_lt (by rw [degree_X_sub_C]; decide)⟩).1
    rw [mul_one, map_sub]
    ring
  simp [hd]

private theorem secondKindOf_eval_div_eq_sum {μ : Measure ℝ}
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) {n : ℕ}
    {x w : Fin n → ℝ} {p : ℝ[X]} (hd : p.natDegree = n)
    (hprod : p = ∏ i, (X - C (x i)))
    (hexact : Quadrature.IsExactOnMeasure μ w x n) {z : ℝ} (hz : ∀ i, z ≠ x i) :
    (secondKindOf μ p).eval z / p.eval z = ∑ i, w i / (z - x i) := by
  have hpz : p.eval z ≠ 0 := by
    rw [hprod, eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by
      simpa only [eval_sub, eval_X, eval_C] using sub_ne_zero.2 (hz i)
  have hroot (i : Fin n) : p.eval (x i) = 0 := by
    rw [hprod, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hqdeg : (quotientEval p z).degree ≤ n := (degree_quotientEval_lt p z).le.trans (by rw [hd])
  rw [div_eq_iff hpz, eval_secondKindOf hint]
  simp_rw [← eval_quotientEval]
  rw [← hexact _ hqdeg, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_quotientEval, div_mul_eq_mul_div, mul_div_assoc]
  congr 1
  apply (eq_div_iff (sub_ne_zero.2 (hz i))).2
  have h := congrArg (fun q : ℝ[X] => q.eval z) (eq_X_sub_C_mul_divByMonic_add_C_eval p (x i))
  simpa only [eval_add, eval_mul, eval_sub, eval_X, eval_C, hroot, add_zero, mul_comm] using h.symm

private theorem secondKindOf_family_succ_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) :
    ∀ n, (∀ j < n + 1, normSq μ j ≠ 0) →
      secondKindOf μ (family μ (n + 1)) = shiftedContinuant μ n 1 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro _; simpa [shiftedContinuant] using secondKindOf_family_one hint
  | one =>
    intro hnorm
    rw [secondKindOf_recurrence hint 0 hnorm, secondKindOf_family_zero hint,
      secondKindOf_family_one hint]
    simp [shiftedContinuant]
  | more n ih₀ ih₁ =>
    intro hnorm
    rw [secondKindOf_recurrence hint (n + 1) hnorm, ih₀ (fun j hj => hnorm j (by omega)),
      ih₁ (fun j hj => hnorm j (by omega)), shiftedContinuant_append]
    simp [Nat.add_comm, Nat.add_left_comm]

/-- **Theorem 3.3.5** of [liesen2013krylov]. The denominator of the Stieltjes convergent is
the monic orthogonal polynomial. The numerator is the second-kind polynomial, which satisfies
the same three-term recurrence with initial values $0$ and $1$. Nonzero norms below order $N$
suffice through that order, including the final convergent of a distribution on $N$ points.

**Generalization.** Integrability of polynomials and nonzero earlier squared norms replace
compact support. The numerator and denominator are exhibited as a rational-function quotient. -/
theorem theorem_3_3_5 {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ)
    (N : ℕ) (hnorm : ∀ j < N, normSq μ j ≠ 0) :
    (∀ n, n + 1 ≤ N → stieltjesRationalConvergent μ (n + 1) =
      algebraMap ℝ[X] (RatFunc ℝ) (secondKindPolynomial μ (n + 1)) /
        algebraMap ℝ[X] (RatFunc ℝ) (family μ (n + 1))) ∧
    secondKindPolynomial μ 0 = 0 ∧ secondKindPolynomial μ 1 = 1 ∧
    ∀ n, n + 2 ≤ N → secondKindPolynomial μ (n + 2) =
      (X - C (alpha μ (n + 1))) * secondKindPolynomial μ (n + 1) -
        C (beta μ n) * secondKindPolynomial μ n := by
  refine ⟨fun n hn => ?_, secondKindOf_family_zero hint, secondKindOf_family_one hint,
    fun n hn => secondKindOf_recurrence hint n (fun j hj => hnorm j (hj.trans_le hn))⟩
  have h := fun j hj => hnorm j (Nat.lt_of_lt_of_le hj hn)
  change continuedFractionTail μ (n + 1) 0 = _
  rw [continuedFractionTail_succ_eq, shiftedContinuant_eq_family hint (n + 1) h,
    secondKindPolynomial, secondKindOf_family_succ_eq hint n h]

/-- **Theorem 3.3.6** of [liesen2013krylov]. For a Gauss rule of a probability measure,
the Stieltjes convergent is the sum of simple fractions with
poles at the nodes and residues equal to the quadrature weights.

**Generalization.** The identity follows from sufficiently high degree exactness at distinct
nodes and includes the terminal rule of a finite distribution. -/
theorem theorem_3_3_6 {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ)
    {n : ℕ} (hm : ∀ s : Finset ℝ, s.card < n + 1 → μ (↑s : Set ℝ)ᶜ ≠ 0)
    {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hexact : Quadrature.IsExactOnMeasure μ w x (2 * n + 1)) :
    stieltjesRationalConvergent μ (n + 1) =
      ∑ i, RatFunc.C (w i) / (RatFunc.X - RatFunc.C (x i)) := by
  let p := family μ (n + 1)
  let φ := algebraMap ℝ[X] (RatFunc ℝ)
  have hn : p.natDegree = n + 1 := natDegree_eq_of_degree_eq_some (degree_family μ _)
  have hpn : φ p ≠ 0 := RatFunc.algebraMap_ne_zero (family_ne_zero μ _)
  have hnodal : Lagrange.nodal Finset.univ x = p :=
    ((Quadrature.isExactOnMeasure_two_mul_add_one_iff_of_card_lt hint hm hx w).1 hexact).1
  have hroot (i : Fin (n + 1)) : p.eval (x i) = 0 := by
    rw [← hnodal]
    exact Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hpoly : secondKindOf μ p = ∑ i, C (w i) * (p /ₘ (X - C (x i))) := by
    apply Polynomial.funext
    intro z
    rw [eval_secondKindOf hint]
    simp_rw [← eval_quotientEval]
    have hd : (quotientEval p z).degree ≤ ↑(2 * n + 1) :=
      (degree_quotientEval_lt p z).le.trans
        (by rw [hn]; exact_mod_cast (by omega : n + 1 ≤ 2 * n + 1))
    rw [← hexact _ hd]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_quotientEval]
  rw [(theorem_3_3_5 hint (n + 1) (fun _ hj => normSq_ne_zero_of_card_lt hint hm hj)).1 n le_rfl]
  change φ (secondKindOf μ p) / φ p = _
  rw [div_eq_iff hpn, Finset.sum_mul, hpoly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfac : p = (X - C (x i)) * (p /ₘ (X - C (x i))) := by
    have h := eq_X_sub_C_mul_divByMonic_add_C_eval p (x i)
    rwa [hroot i, map_zero, add_zero] at h
  have hmap : RatFunc.X - RatFunc.C (x i) = φ (X - C (x i)) := by simp [φ]
  have hne : RatFunc.X - RatFunc.C (x i) ≠ 0 := hmap ▸ fun h =>
    (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero _)) h
  rw [map_mul, hmap, div_mul_eq_mul_div, mul_div_assoc,
    show φ (C (w i)) = RatFunc.C (w i) from RatFunc.algebraMap_C _]
  congr 1
  apply (eq_div_iff (hmap ▸ hne)).2
  rw [← map_mul, mul_comm, ← hfac]

/-- **Equation (3.3.20)** of [liesen2013krylov]. Evaluating the second-kind polynomial
at $z$ integrates the polynomial divided difference at $(z,t)$.

**Generalization.** The quotient by a monic linear factor gives the removable value at a
coinciding argument. Polynomial integrability suffices. -/
theorem secondKindPolynomial_eval {μ : Measure ℝ}
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) (n : ℕ) (z : ℝ) :
    (secondKindPolynomial μ n).eval z =
      ∫ t, (family μ n /ₘ (X - C t)).eval z ∂μ :=
  eval_secondKindOf hint _ z

/-- **Theorem 3.3.6** of [liesen2013krylov], evaluated away from the Gauss nodes.

**Generalization.** The evaluated quotient identity needs no normalization of the measure. -/
theorem theorem_3_3_6_eval {μ : Measure ℝ}
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ)
    {n : ℕ} (hm : ∀ s : Finset ℝ, s.card < n + 1 → μ (↑s : Set ℝ)ᶜ ≠ 0)
    {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hexact : Quadrature.IsExactOnMeasure μ w x (2 * n + 1)) {z : ℝ} (hz : ∀ i, z ≠ x i) :
    (secondKindPolynomial μ (n + 1)).eval z / (family μ (n + 1)).eval z =
      ∑ i, w i / (z - x i) := by
  have hprod : family μ (n + 1) = ∏ i, (X - C (x i)) :=
    ((Quadrature.isExactOnMeasure_two_mul_add_one_iff_of_card_lt hint hm hx w).1 hexact).1.symm
  exact secondKindOf_eval_div_eq_sum hint (natDegree_eq_of_degree_eq_some (degree_family μ _))
    hprod (hexact.mono (by omega)) hz

private theorem exists_opposite_signs_of_orthogonal_factor {μ : Measure ℝ} {n m : ℕ}
    (hnm : n < m) {y w : Fin m → ℝ} (hy : Function.Injective y) (hw : ∀ i, 0 < w i)
    (hexact : Quadrature.IsExactOnMeasure μ w y (2 * m - 1))
    {p q r : ℝ[X]} (hp : p.Monic) (hd : p.degree = n) (hfac : p = q * r)
    (hq : 0 < q.natDegree)
    (horth : ∀ s : ℝ[X], s.degree < n → (∫ t, p.eval t * s.eval t ∂μ) = 0) :
    (∃ i, q.eval (y i) < 0) ∧ (∃ i, 0 < q.eval (y i)) := by
  have hqr : q * r ≠ 0 := hfac ▸ hp.ne_zero
  have hr : r ≠ 0 := right_ne_zero_of_mul hqr
  have hqn : q ≠ 0 := left_ne_zero_of_mul hqr
  have hrdeg : r.natDegree < n := by
    have hn := natDegree_eq_of_degree_eq_some hd
    rw [hfac, natDegree_mul' (mul_ne_zero (leadingCoeff_ne_zero.mpr hqn)
      (leadingCoeff_ne_zero.mpr hr))] at hn
    omega
  have hpr : (p * r).degree ≤ ↑(2 * m - 1) := by
    rw [degree_mul, hd, degree_eq_natDegree hr, ← Nat.cast_add]
    exact_mod_cast (show n + r.natDegree ≤ 2 * m - 1 by omega)
  have hsum := hexact (p * r) hpr
  simp only [eval_mul, horth r (by rw [degree_eq_natDegree hr]; exact_mod_cast hrdeg)] at hsum
  have hz : ∃ i, p.eval (y i) ≠ 0 := by
    by_contra! hall
    apply hp.ne_zero
    exact Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hy.injOn
      (by rw [hd, Finset.card_univ, Fintype.card_fin]; exact_mod_cast hnm)
      (fun i _ => hall i)
  obtain ⟨i, hi⟩ := hz
  have hne : q.eval (y i) ≠ 0 ∧ r.eval (y i) ≠ 0 := by
    rw [hfac, eval_mul, mul_ne_zero_iff] at hi
    exact hi
  have heval (j : Fin m) : w j * (p.eval (y j) * r.eval (y j)) =
      w j * (q.eval (y j) * (r.eval (y j)) ^ 2) := by
    rw [hfac, eval_mul]
    ring
  simp only [heval] at hsum
  constructor
  · by_contra! h
    have hpos : 0 < ∑ j, w j * (q.eval (y j) * (r.eval (y j)) ^ 2) := Finset.sum_pos'
      (fun j _ => mul_nonneg (hw j).le (mul_nonneg (h j) (sq_nonneg _)))
      ⟨i, Finset.mem_univ i, mul_pos (hw i)
        (mul_pos (lt_of_le_of_ne (h i) hne.1.symm) (sq_pos_of_ne_zero hne.2))⟩
    exact hpos.ne' hsum
  · by_contra! h
    have hneg : (∑ j, w j * (q.eval (y j) * (r.eval (y j)) ^ 2)) < 0 := Finset.sum_neg'
      (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw j).le
        (mul_nonpos_of_nonpos_of_nonneg (h j) (sq_nonneg _)))
      ⟨i, Finset.mem_univ i, mul_neg_of_pos_of_neg (hw i)
        (mul_neg_of_neg_of_pos (lt_of_le_of_ne (h i) hne.1) (sq_pos_of_ne_zero hne.2))⟩
    exact hneg.ne hsum

/-- **Theorem 3.3.1** of [liesen2013krylov].
For a monic orthogonal polynomial $p$ of degree $n$, every gap between two distinct roots
contains a node of each higher-order Gauss rule, and there are nodes on either side of
every root. When the larger rule is the finite support itself, its exactness gives the same
conclusion. The two outer gaps use whatever endpoint inclusion holds for its nodes.

**Reading.** The larger node set comes from a given positive exact rule. The theorem gives
relative positions with respect to these nodes, without prescribing enclosing interval
endpoints. -/
theorem theorem_3_3_1 {μ : Measure ℝ} {n m : ℕ} (hnm : n < m)
    {x : Fin n → ℝ} {y w : Fin m → ℝ} (hy : Function.Injective y) (hw : ∀ i, 0 < w i)
    (hexact : Quadrature.IsExactOnMeasure μ w y (2 * m - 1))
    {p : ℝ[X]} (hp : p.Monic) (hd : p.degree = n) (hx : ∀ i, p.IsRoot (x i))
    (horth : ∀ s : ℝ[X], s.degree < n → (∫ t, p.eval t * s.eval t ∂μ) = 0) :
    (∀ i, ∃ j, y j < x i) ∧ (∀ i, ∃ j, x i < y j) ∧
      ∀ i j, x i < x j → ∃ k, y k ∈ Set.Ioo (x i) (x j) := by
  have hhalf (i : Fin n) : (∃ j, y j < x i) ∧ (∃ j, x i < y j) := by
    obtain ⟨r, hr⟩ := dvd_iff_isRoot.2 (hx i)
    have hsign := exists_opposite_signs_of_orthogonal_factor hnm hy hw hexact hp hd hr
      (by rw [natDegree_X_sub_C]; decide) horth
    simpa only [eval_sub, eval_X, eval_C, sub_lt_zero, sub_pos] using hsign
  refine ⟨fun i => (hhalf i).1, fun i => (hhalf i).2, ?_⟩
  intro i j hij
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.2 (hx i)
  have hrj : r.IsRoot (x j) := by
    have hz := hx j
    rw [IsRoot, hr, eval_mul, eval_sub, eval_X, eval_C] at hz
    exact (mul_eq_zero.1 hz).resolve_left (sub_ne_zero.2 hij.ne')
  obtain ⟨s, hs⟩ := dvd_iff_isRoot.2 hrj
  have hp' : p = ((X - C (x i)) * (X - C (x j))) * s := by
    rw [hr, hs, mul_assoc]
  have hdeg : 0 < ((X - C (x i)) * (X - C (x j))).natDegree := by
    have h := (monic_X_sub_C (x i)).natDegree_mul (monic_X_sub_C (x j))
    rw [h, natDegree_X_sub_C, natDegree_X_sub_C]
    decide
  obtain ⟨k, hk⟩ := (exists_opposite_signs_of_orthogonal_factor hnm hy hw hexact
    hp hd hp' hdeg horth).1
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hk
  rcases mul_neg_iff.mp hk with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨k, sub_pos.mp h₁, sub_lt_zero.mp h₂⟩
  · have hi : y k < x i := sub_lt_zero.mp h₁
    have hj : x j < y k := sub_pos.mp h₂
    exact False.elim (hi.not_ge (hij.trans hj).le)

/-- **Corollary 3.3.3** of [liesen2013krylov]. The roots of consecutive monic orthogonal
polynomials, listed in descending order, strictly interlace:
$x_{n+1,i+1}<x_{n,i}<x_{n+1,i}$. The smaller roots lie in $(a,b)$. The larger
roots also lie there unless the polynomial is terminal, in which case its roots are
the support points and may include the right endpoint.

**Reading.** Nodes are ordered from largest to smallest. The larger nodes are stated to lie in
$(a,b]$, which includes the terminal right endpoint. -/
theorem corollary_3_3_3 {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Ioc a b)ᶜ = 0) (n : ℕ)
    (hm : ∀ s : Finset ℝ, s.card ≤ n → μ (↑s : Set ℝ)ᶜ ≠ 0) :
    ∃ (x : Fin n → ℝ) (y : Fin (n + 1) → ℝ),
      StrictAnti x ∧ StrictAnti y ∧ (∀ i, x i ∈ Set.Ioo a b) ∧ (∀ j, y j ∈ Set.Ioc a b) ∧
      family μ n = (∏ i, (X - C (x i))) ∧
      family μ (n + 1) = (∏ j, (X - C (y j))) ∧
      ∀ i : Fin n, y i.succ < x i ∧ x i < y i.castSucc := by
  classical
  have hIcc : μ (Set.Icc a b)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.2 Set.Ioc_subset_Icc_self) hsupp
  let hint := integrable_eval_of_measure_compl_Icc_eq_zero hIcc
  have hpos (j : ℕ) (hj : j ≤ n) : 0 < normSq μ j :=
    integral_eval_sq_pos_of_degree_le hint (fun s hs => hm s (hs.trans hj))
      (family_ne_zero μ j) (degree_family μ j).le
  let d := alpha μ
  let e := fun i => Real.sqrt (beta μ i)
  have he (m : ℕ) (hm' : m ≤ n + 1) : Sturm.IsUnreduced e m := by
    intro j hj
    exact (Real.sqrt_pos.2 (div_pos (hpos (j + 1) (by omega)) (hpos j (by omega)))).ne'
  have hprod (m : ℕ) (hm' : m ≤ n + 1) :
      family μ m = ∏ i, (X - C (Sturm.eigenvalues d e m i)) := by
    have hM : Matrix.symmTridiagonalOf d e m = jacobiMatrix μ m := by
      ext i j
      simp [Matrix.symmTridiagonalOf_apply, jacobiMatrix_apply, d, e, eq_comm]
    rw [← charpoly_jacobiMatrix_of_integrable hint m (fun j hj => (hpos j (by omega)).ne'),
      ← hM, Sturm.charpoly_eq_prod]
  have hroot {m : ℕ} (hm' : m ≤ n + 1) (i : Fin m) :
      (family μ m).eval (Sturm.eigenvalues d e m i) = 0 := by
    rw [hprod m hm', eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hxmem (i : Fin n) : Sturm.eigenvalues d e n i ∈ Set.Ioo a b :=
    root_family_mem_Ioo_of_measure_compl_ne_zero hIcc hm (hroot (by omega) i)
  have hymem (i : Fin (n + 1)) : Sturm.eigenvalues d e (n + 1) i ∈ Set.Ioc a b := by
    by_cases hmore : ∀ s : Finset ℝ, s.card ≤ n + 1 → μ (↑s : Set ℝ)ᶜ ≠ 0
    · exact Set.Ioo_subset_Ioc_self
        (root_family_mem_Ioo_of_measure_compl_ne_zero hIcc hmore (hroot le_rfl i))
    push Not at hmore
    obtain ⟨s, hs, hzero⟩ := hmore
    have hsn : n < s.card := lt_of_not_ge (fun h => hm s h hzero)
    have hcard : s.card = n + 1 := by omega
    have hmem (z : ℝ) (hz : z ∈ s) : z ∈ Set.Ioc a b := by
      by_contra h
      have hae : ∀ᵐ t ∂μ, t ∈ (↑s : Set ℝ) := MeasureTheory.ae_iff.2 hzero
      have haI : ∀ᵐ t ∂μ, t ∈ Set.Ioc a b := MeasureTheory.ae_iff.2 hsupp
      have hnull : μ (↑(s.erase z) : Set ℝ)ᶜ = 0 := MeasureTheory.ae_iff.1 <| by
        filter_upwards [hae, haI] with t ht ht'
        exact Finset.mem_erase.2 ⟨fun he => h (he ▸ ht'), ht⟩
      exact hm (s.erase z) (by rw [Finset.card_erase_of_mem hz, hcard]; omega) hnull
    let roots := s.orderEmbOfFin hcard
    have hzero' : μ (Set.range roots)ᶜ = 0 := by
      rw [Finset.range_orderEmbOfFin]
      exact hzero
    have hp := lemma_3_2_4_terminal hIcc hzero'
      (fun s hs => hm s (Nat.lt_succ_iff.mp hs))
    change family μ (n + 1) = _ at hp
    have hr := hroot le_rfl i
    rw [hp, Lagrange.eval_nodal, Finset.prod_eq_zero_iff] at hr
    obtain ⟨j, -, hj⟩ := hr
    rw [sub_eq_zero.1 hj]
    exact hmem _ (Finset.orderEmbOfFin_mem _ hcard j)
  exact ⟨Sturm.eigenvalues d e n, Sturm.eigenvalues d e (n + 1),
    Sturm.strictAnti_eigenvalues d e n (he n (by omega)),
    Sturm.strictAnti_eigenvalues d e (n + 1) (he _ le_rfl),
    hxmem, hymem, hprod n (by omega), hprod (n + 1) le_rfl, fun i =>
      ⟨Sturm.eigenvalues_succ_lt d e n (he _ le_rfl) i,
        Sturm.eigenvalues_lt_castSucc d e n (he _ le_rfl) i⟩⟩

/-- At a real parameter outside the interval $[a,b]$, quadratures with nonnegative weights
and increasing degree of exactness converge to the Stieltjes integral
$\int(\lambda-t)^{-1}\,d\mu(t)$. This is the convergence of (3.2.22) of [liesen2013krylov].

**Generalization.** Any nonnegative exact rules of increasing degree give convergence for real
parameters outside the interval. -/
theorem gaussResolvent_tendsto {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {m d : ℕ → ℕ} {x w : ∀ k, Fin (m k) → ℝ}
    (hinj : ∀ k, Function.Injective (x k)) (hmem : ∀ k i, x k i ∈ Set.Icc a b)
    (hw : ∀ k i, 0 ≤ w k i) (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, Quadrature.IsExactOnMeasure μ (w k) (x k) (d k))
    {z : ℝ} (hz : z ∉ Set.Icc a b) :
    Tendsto (fun k => ∑ i, w k i / (z - x k i)) atTop (𝓝 (∫ t, (z - t)⁻¹ ∂μ)) := by
  have hf : ContinuousOn (fun t => (z - t)⁻¹) (Set.Icc a b) :=
    (continuous_const.sub continuous_id).continuousOn.inv₀ fun t ht => sub_ne_zero.mpr
      (fun he => by
        change z = t at he
        exact hz (he.symm ▸ ht))
  simpa only [mechanicalQuadrature, div_eq_mul_inv] using
    gaussChristoffel_tendsto_integral hsupp hinj hmem hw hd hexact hf

end LiesenStrakos.Chapter03
