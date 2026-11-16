/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Ring.Units`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Explicit Neumann-series and perturbation bounds

Let $R$ be a normed ring, and write $a^{-1}$ for `Ring.inverse a`, which is $0$ when $a$ is not a
unit. This file gives explicit forms of the classical geometric-series (Banach perturbation)
estimates for the inverse of a small perturbation of an invertible element. They are quantitative
versions of Mathlib's `Units.oneSub` and `Units.add`. In a complete normed ring with $\|1\| = 1$,
$$\|(1 - t)^{-1}\| \le \frac{1}{1 - \|t\|} \quad (\|t\| < 1), \qquad \|(x + t)^{-1}\| \le
  \frac{\|x^{-1}\|}{1 - \|x^{-1}\| \|t\|} \quad (\|x^{-1}\| \|t\| < 1),$$
and there is a version for isomorphisms between two normed spaces. These are (2.3.6), Theorem 2.3.5
and its displays (2.3.13) and (2.3.14) of [han2009theoretical].

The one-sided forms measure the perturbation by $r = \|a^{-1} t\| \le \|a^{-1}\| \|t\|$ instead, as
in Theorem 2.3.4 of [golub2013matrix]: if $r < 1$, then $a + t$ is a unit and $\|(a + t)^{-1} -
a^{-1}\| \le r \|a^{-1}\| / (1 - r)$. The right forms use $r = \|t a^{-1}\|$. As a contrapositive,
if $a$ is a unit and $a - b$ is not, then $\|a^{-1} b\| \ge 1$; this is the step used in eigenvalue
perturbation. The one-sided forms and the bound on $\|(1 - t)^{-1} - 1\|$ need neither $\|1\| = 1$
nor completeness, only that geometric series with ratio of norm less than $1$ are summable.

## Main results

* `NormedRing.norm_inverse_one_sub_le`: $\|(1 - t)^{-1}\| \le 1 / (1 - \|t\|)$ for $\|t\| < 1$.
* `NormedRing.norm_inverse_one_sub_sub_one_le`: $\|(1 - t)^{-1} - 1\| \le \|t\| / (1 - \|t\|)$ for
  $\|t\| < 1$.
* `NormedRing.isUnit_one_sub_of_norm_pow_lt_one` and
  `NormedRing.norm_inverse_one_sub_le_of_norm_pow_lt_one`: $\|t^m\| < 1$ for one $m$ makes $1 - t$ a
  unit, with $\|(1 - t)^{-1}\| \le \sum_{i < m} \|t^i\| / (1 - \|t^m\|)$.
* `NormedRing.isUnit_add_of_norm_inverse_mul_lt_one` and
  `NormedRing.norm_inverse_add_sub_le_of_norm_inverse_mul_lt_one`: the one-sided perturbation of a
  unit and of its inverse.
* `NormedRing.isUnit_add_of_norm_mul_inverse_lt_one` and
  `NormedRing.norm_inverse_add_sub_le_of_norm_mul_inverse_lt_one`: the right one-sided forms.
* `NormedRing.one_le_norm_inverse_mul_of_not_isUnit_sub`: if $a$ is a unit and $a - b$ is not, then
  $1 \le \|a^{-1} b\|$.
* `Units.isUnit_add_of_norm_lt`, `Units.norm_inverse_add_le` and `Units.norm_inverse_add_sub_le`:
  the perturbation of a unit $x$ by $t$ with $\|t\| < \|x^{-1}\|^{-1}$.
* `ContinuousLinearEquiv.exists_symm_norm_le_of_add`: the perturbation theorem for an isomorphism
  $e \colon E \to F$.
* `ContinuousLinearEquiv.norm_sub_le_of_apply_eq`: consistency and stability give convergence.
-/

/-- For real numbers $u \le v < 1$, $1/(1 - u) \le 1/(1 - v)$. -/
private theorem one_div_one_sub_le_one_div_one_sub {u v : ℝ} (huv : u ≤ v) (hv : v < 1) :
    1 / (1 - u) ≤ 1 / (1 - v) :=
  one_div_le_one_div_of_le (by linarith) (by linarith)

/-- For real numbers $u \le v < 1$, $u/(1 - u) \le v/(1 - v)$. -/
private theorem div_one_sub_le_div_one_sub {u v : ℝ} (huv : u ≤ v) (hv : v < 1) :
    u / (1 - u) ≤ v / (1 - v) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

namespace NormedRing

/-- Let $R$ be a normed ring in which geometric series with ratio of norm less than $1$ are
summable, and suppose that $\|1\| \le 1$. If $t \in R$ and $\|t\| < 1$, then
$$\|(1 - t)^{-1}\| \le \frac{1}{1 - \|t\|}.$$

This form needs only $\|1\| \le 1$, not $\|1\| = 1$. It applies to rings of bounded operators,
which are not `NormOneClass` when the space is trivial. -/
theorem norm_inverse_one_sub_le_of_norm_one_le {R : Type*} [NormedRing R]
    [HasSummableGeomSeries R] (h₁ : ‖(1 : R)‖ ≤ 1) {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ 1 / (1 - ‖t‖) := by
  rw [← geom_series_eq_inverse t h, one_div]
  have := tsum_geometric_le_of_norm_lt_one t h
  linarith

variable {R : Type*} [NormedRing R]

/-- Let $R$ be a normed ring in which geometric series with ratio of norm less than $1$ are
summable. If $t \in R$ and $\|t\| < 1$, then
$$\|(1 - t)^{-1} - 1\| \le \frac{\|t\|}{1 - \|t\|}.$$

No $\|1\| = 1$ is needed: $(1 - t)^{-1} - 1$ is the tail $\sum_{i \ge 0} t^{i+1}$ of the
geometric series, whose terms have norm at most $\|t\|^{i+1}$. -/
theorem norm_inverse_one_sub_sub_one_le [HasSummableGeomSeries R] {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t) - 1‖ ≤ ‖t‖ / (1 - ‖t‖) := by
  rw [← geom_series_eq_inverse t h, ← geom_series_succ t h]
  have hs : HasSum (fun i : ℕ => ‖t‖ ^ (i + 1)) (‖t‖ / (1 - ‖t‖)) := by
    simpa only [pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one (norm_nonneg t) h).mul_left ‖t‖
  exact tsum_of_norm_bounded hs fun i => norm_pow_le' t i.succ_pos

variable [NormOneClass R] [CompleteSpace R]

/-- The **geometric series theorem** with an explicit bound. Let $R$ be a complete normed ring with
$\|1\| = 1$. If $t \in R$ and $\|t\| < 1$, then
$$\|(1 - t)^{-1}\| \le \frac{1}{1 - \|t\|}.$$
-/
theorem norm_inverse_one_sub_le {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ 1 / (1 - ‖t‖) :=
  norm_inverse_one_sub_le_of_norm_one_le norm_one.le h

omit [NormOneClass R] [CompleteSpace R] in
private theorem commute_one_sub_geom_sum (t : R) (m : ℕ) :
    Commute (1 - t) (∑ i ∈ Finset.range m, t ^ i) :=
  Commute.sum_right _ _ _ fun i _ =>
    (Commute.one_left (t ^ i)).sub_left ((Commute.refl t).pow_right i)

omit [NormOneClass R] in
/-- Let $R$ be a complete normed ring, let $t \in R$, and let $m \in \mathbb{N}$ with $\|t^m\| < 1$.
Then $1 - t$ is a unit.

A single power of $t$ with norm less than $1$ suffices, and $\|1\| = 1$ is not needed. -/
theorem isUnit_one_sub_of_norm_pow_lt_one {t : R} {m : ℕ} (h : ‖t ^ m‖ < 1) : IsUnit (1 - t) := by
  have hprod : IsUnit ((1 - t) * ∑ i ∈ Finset.range m, t ^ i) := by
    rw [mul_neg_geom_sum]
    exact isUnit_one_sub_of_norm_lt_one h
  exact ((commute_one_sub_geom_sum t m).isUnit_mul_iff.mp hprod).1

/-- Let $R$ be a complete normed ring with $\|1\| = 1$, let $t \in R$, and let $m \in \mathbb{N}$
with $\|t^m\| < 1$. Then
$$\|(1 - t)^{-1}\| \le \frac{\sum_{i < m} \|t^i\|}{1 - \|t^m\|}.$$
This is (2.3.6) of [han2009theoretical].

This bound accompanies `NormedRing.isUnit_one_sub_of_norm_pow_lt_one`. -/
theorem norm_inverse_one_sub_le_of_norm_pow_lt_one {t : R} {m : ℕ} (h : ‖t ^ m‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ (∑ i ∈ Finset.range m, ‖t ^ i‖) / (1 - ‖t ^ m‖) := by
  have hunit : IsUnit (1 - t) := isUnit_one_sub_of_norm_pow_lt_one h
  have hpow : IsUnit (1 - t ^ m) := isUnit_one_sub_of_norm_lt_one h
  have h₁ : (1 - t) * ((∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m)) = 1 := by
    rw [← mul_assoc, mul_neg_geom_sum, Ring.mul_inverse_cancel _ hpow]
  have hkey : Ring.inverse (1 - t)
      = (∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m) := by
    calc Ring.inverse (1 - t)
        = Ring.inverse (1 - t) *
            ((1 - t) * ((∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m))) := by
          rw [h₁, mul_one]
      _ = (∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m) := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hunit, one_mul]
  rw [hkey]
  calc ‖(∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m)‖
      ≤ ‖∑ i ∈ Finset.range m, t ^ i‖ * ‖Ring.inverse (1 - t ^ m)‖ := norm_mul_le _ _
    _ ≤ (∑ i ∈ Finset.range m, ‖t ^ i‖) * (1 / (1 - ‖t ^ m‖)) :=
        mul_le_mul (norm_sum_le _ _) (norm_inverse_one_sub_le h) (norm_nonneg _)
          (Finset.sum_nonneg fun i _ => norm_nonneg _)
    _ = (∑ i ∈ Finset.range m, ‖t ^ i‖) / (1 - ‖t ^ m‖) := by ring

section OneSided

omit [NormOneClass R] [CompleteSpace R]

/-- For a unit $a$, $a + t = a (1 - (-(a^{-1} t)))$. -/
private theorem add_eq_mul_one_sub {a t : R} (ha : IsUnit a) :
    a + t = a * (1 - -(Ring.inverse a * t)) := by
  rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel _ ha, one_mul]

variable [HasSummableGeomSeries R] {a t : R}

/-- **Perturbation of a unit, one-sided form**. Let $R$ be a normed ring in which geometric series
with ratio of norm less than $1$ are summable. If $a \in R$ is a unit and $\|a^{-1} t\| < 1$,
then $a + t$ is a unit.

The proof writes $a + t = a (1 + a^{-1} t)$. The hypothesis is weaker than the hypothesis
$\|a^{-1}\| \|t\| < 1$ of `Units.isUnit_add_of_norm_lt`. -/
theorem isUnit_add_of_norm_inverse_mul_lt_one (ha : IsUnit a) (h : ‖Ring.inverse a * t‖ < 1) :
    IsUnit (a + t) := by
  rw [add_eq_mul_one_sub ha]
  exact ha.mul (isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg]))

/-- Let $R$ be a normed ring in which geometric series with ratio of norm less than $1$ are
summable. If $a \in R$ is a unit and $a - b$ is not a unit, then
$$1 \le \|a^{-1} b\|.$$

Otherwise $a - b = a (1 - a^{-1} b)$ would be a unit, by
`NormedRing.isUnit_add_of_norm_inverse_mul_lt_one`. This is the step shared by the
resolvent-based eigenvalue perturbation bounds, as in (7.2.1) of [golub2013matrix] through Lemma
2.3.3: an eigenvalue $\mu$ of $A + E$ that is not an eigenvalue of $A$ has
$\|(\mu I - A)^{-1} E\| \ge 1$. -/
theorem one_le_norm_inverse_mul_of_not_isUnit_sub {b : R} (ha : IsUnit a)
    (hab : ¬IsUnit (a - b)) : 1 ≤ ‖Ring.inverse a * b‖ := by
  by_contra hlt
  refine hab ?_
  rw [sub_eq_add_neg]
  exact isUnit_add_of_norm_inverse_mul_lt_one ha (by rwa [mul_neg, norm_neg, ← not_le])

/-- If $a$ is a unit and $\|a^{-1} t\| < 1$, then $(a + t)^{-1} = (1 + a^{-1} t)^{-1} a^{-1}$. -/
private theorem inverse_add_eq_mul (ha : IsUnit a) (h : ‖Ring.inverse a * t‖ < 1) :
    Ring.inverse (a + t) = Ring.inverse (1 - -(Ring.inverse a * t)) * Ring.inverse a := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, hv⟩ := isUnit_one_sub_of_norm_lt_one (x := -(Ring.inverse (u : R) * t))
    (by rwa [norm_neg])
  rw [add_eq_mul_one_sub u.isUnit, ← hv, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit,
    Ring.inverse_unit, mul_inv_rev, Units.val_mul]

/-- **Perturbation of the inverse, one-sided form**. Let $R$ be a normed ring in which geometric
series with ratio of norm less than $1$ are summable. Let $a \in R$ be a unit and let
$r = \|a^{-1} t\| < 1$. Then
$$\|(a + t)^{-1} - a^{-1}\| \le \frac{r \|a^{-1}\|}{1 - r} \quad \text{and} \quad \|(a +
  t)^{-1} - a^{-1}\| \le \frac{\|t\| \|a^{-1}\|^2}{1 - r}.$$
This is Theorem 2.3.4 of [golub2013matrix], which prints the second bound.

The proof writes $(a + t)^{-1} - a^{-1} = ((1 + a^{-1} t)^{-1} - 1) a^{-1}$ and bounds the first
factor by the tail of the geometric series (`NormedRing.norm_inverse_one_sub_sub_one_le`). No
$\|1\| = 1$ is needed. Since $r \le \|a^{-1}\| \|t\|$, this sharpens
`Units.norm_inverse_add_sub_le`. -/
theorem norm_inverse_add_sub_le_of_norm_inverse_mul_lt_one (ha : IsUnit a)
    (h : ‖Ring.inverse a * t‖ < 1) :
    ‖Ring.inverse (a + t) - Ring.inverse a‖
        ≤ ‖Ring.inverse a * t‖ * ‖Ring.inverse a‖ / (1 - ‖Ring.inverse a * t‖) ∧
      ‖Ring.inverse (a + t) - Ring.inverse a‖
        ≤ ‖t‖ * ‖Ring.inverse a‖ ^ 2 / (1 - ‖Ring.inverse a * t‖) := by
  have hr : 0 < 1 - ‖Ring.inverse a * t‖ := by linarith
  have h₁ : ‖Ring.inverse (a + t) - Ring.inverse a‖
      ≤ ‖Ring.inverse a * t‖ * ‖Ring.inverse a‖ / (1 - ‖Ring.inverse a * t‖) := by
    have hn : ‖-(Ring.inverse a * t)‖ < 1 := by rwa [norm_neg]
    rw [inverse_add_eq_mul ha h, ← sub_one_mul]
    refine (norm_mul_le _ _).trans ?_
    have := norm_inverse_one_sub_sub_one_le hn
    rw [norm_neg] at this
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  refine ⟨h₁, h₁.trans (div_le_div_of_nonneg_right ?_ hr.le)⟩
  calc ‖Ring.inverse a * t‖ * ‖Ring.inverse a‖ ≤ ‖Ring.inverse a‖ * ‖t‖ * ‖Ring.inverse a‖ := by
        gcongr; exact norm_mul_le _ _
    _ = ‖t‖ * ‖Ring.inverse a‖ ^ 2 := by ring

omit [HasSummableGeomSeries R] in
/-- For a unit $a$, $a + t = (1 - (-(t a^{-1}))) a$. -/
private theorem add_eq_one_sub_mul (ha : IsUnit a) : a + t = (1 - -(t * Ring.inverse a)) * a := by
  rw [sub_neg_eq_add, add_mul, one_mul, mul_assoc, Ring.inverse_mul_cancel _ ha, mul_one]

/-- **Perturbation of a unit, right one-sided form**. Let $R$ be a normed ring in which geometric
series with ratio of norm less than $1$ are summable. If $a \in R$ is a unit and
$\|t a^{-1}\| < 1$, then $a + t$ is a unit.

The proof writes $a + t = (1 + t a^{-1}) a$. This is the mirror image of
`NormedRing.isUnit_add_of_norm_inverse_mul_lt_one`. -/
theorem isUnit_add_of_norm_mul_inverse_lt_one (ha : IsUnit a) (h : ‖t * Ring.inverse a‖ < 1) :
    IsUnit (a + t) := by
  rw [add_eq_one_sub_mul ha]
  exact (isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])).mul ha

/-- If $a$ is a unit and $\|t a^{-1}\| < 1$, then $(a + t)^{-1} = a^{-1} (1 + t a^{-1})^{-1}$. -/
private theorem inverse_add_eq_mul' (ha : IsUnit a) (h : ‖t * Ring.inverse a‖ < 1) :
    Ring.inverse (a + t) = Ring.inverse a * Ring.inverse (1 - -(t * Ring.inverse a)) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, hv⟩ := isUnit_one_sub_of_norm_lt_one (x := -(t * Ring.inverse (u : R)))
    (by rwa [norm_neg])
  rw [add_eq_one_sub_mul u.isUnit, ← hv, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit,
    Ring.inverse_unit, mul_inv_rev, Units.val_mul]

/-- **Perturbation of the inverse, right one-sided form**. Let $R$ be a normed ring in which
geometric series with ratio of norm less than $1$ are summable. Let $a \in R$ be a unit and let
$r = \|t a^{-1}\| < 1$. Then
$$\|(a + t)^{-1} - a^{-1}\| \le \frac{r \|a^{-1}\|}{1 - r} \quad \text{and} \quad \|(a +
  t)^{-1} - a^{-1}\| \le \frac{\|t\| \|a^{-1}\|^2}{1 - r}.$$

This is the mirror image of `NormedRing.norm_inverse_add_sub_le_of_norm_inverse_mul_lt_one`,
through $(a + t)^{-1} - a^{-1} = a^{-1} ((1 + t a^{-1})^{-1} - 1)$. -/
theorem norm_inverse_add_sub_le_of_norm_mul_inverse_lt_one (ha : IsUnit a)
    (h : ‖t * Ring.inverse a‖ < 1) :
    ‖Ring.inverse (a + t) - Ring.inverse a‖
        ≤ ‖t * Ring.inverse a‖ * ‖Ring.inverse a‖ / (1 - ‖t * Ring.inverse a‖) ∧
      ‖Ring.inverse (a + t) - Ring.inverse a‖
        ≤ ‖t‖ * ‖Ring.inverse a‖ ^ 2 / (1 - ‖t * Ring.inverse a‖) := by
  have hr : 0 < 1 - ‖t * Ring.inverse a‖ := by linarith
  have h₁ : ‖Ring.inverse (a + t) - Ring.inverse a‖
      ≤ ‖t * Ring.inverse a‖ * ‖Ring.inverse a‖ / (1 - ‖t * Ring.inverse a‖) := by
    have hn : ‖-(t * Ring.inverse a)‖ < 1 := by rwa [norm_neg]
    rw [inverse_add_eq_mul' ha h, ← mul_sub_one]
    refine (norm_mul_le _ _).trans ?_
    have := norm_inverse_one_sub_sub_one_le hn
    rw [norm_neg] at this
    rw [mul_div_right_comm, mul_comm (‖t * Ring.inverse a‖ / (1 - ‖t * Ring.inverse a‖))]
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  refine ⟨h₁, h₁.trans (div_le_div_of_nonneg_right ?_ hr.le)⟩
  calc ‖t * Ring.inverse a‖ * ‖Ring.inverse a‖ ≤ ‖t‖ * ‖Ring.inverse a‖ * ‖Ring.inverse a‖ := by
        gcongr; exact norm_mul_le _ _
    _ = ‖t‖ * ‖Ring.inverse a‖ ^ 2 := by ring

end OneSided

end NormedRing

namespace Units

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

omit [NormOneClass R] in
/-- **Perturbation of a unit**. Let $R$ be a complete normed ring, let $x$ be a unit of $R$, and let
$t \in R$ with $\|t\| < \|x^{-1}\|^{-1}$. Then $x + t$ is a unit.

This is Mathlib's `Units.add`, stated with `IsUnit`. -/
theorem isUnit_add_of_norm_lt (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    IsUnit ((x : R) + t) :=
  ⟨x.add t h, rfl⟩

omit [CompleteSpace R] in
private theorem norm_inv_mul_lt_one {x : Rˣ} {t : R} (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖(↑x⁻¹ : R)‖ * ‖t‖ < 1 := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hpos : 0 < ‖(↑x⁻¹ : R)‖ := Units.norm_pos x⁻¹
  calc ‖(↑x⁻¹ : R)‖ * ‖t‖ < ‖(↑x⁻¹ : R)‖ * ‖(↑x⁻¹ : R)‖⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hpos.ne'

omit [CompleteSpace R] in
private theorem norm_neg_inv_mul_lt_one {x : Rˣ} {t : R} (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖(-((↑x⁻¹ : R) * t))‖ < 1 :=
  lt_of_le_of_lt (by rw [norm_neg]; exact norm_mul_le _ _) (norm_inv_mul_lt_one h)

/-- If $\|t\| < \|x^{-1}\|^{-1}$, then $(x + t)^{-1} = (1 + x^{-1} t)^{-1} x^{-1}$. -/
private theorem inverse_add_eq (x : Rˣ) {t : R} (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    Ring.inverse ((x : R) + t)
      = Ring.inverse (1 - -((↑x⁻¹ : R) * t)) * (↑x⁻¹ : R) := by
  have h' : ‖Ring.inverse (x : R) * t‖ < 1 := by
    rw [Ring.inverse_unit]
    exact (norm_mul_le _ _).trans_lt (norm_inv_mul_lt_one h)
  simpa only [Ring.inverse_unit] using NormedRing.inverse_add_eq_mul x.isUnit h'

/-- Let $R$ be a complete normed ring with $\|1\| = 1$, let $x$ be a unit of $R$, and let $t \in R$
with $\|t\| < \|x^{-1}\|^{-1}$. Then
$$\|(x + t)^{-1}\| \le \frac{\|x^{-1}\|}{1 - \|x^{-1}\| \|t\|}.$$
-/
theorem norm_inverse_add_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t)‖ ≤ ‖(↑x⁻¹ : R)‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by
  have hle : ‖(-((↑x⁻¹ : R) * t))‖ ≤ ‖(↑x⁻¹ : R)‖ * ‖t‖ := by
    rw [norm_neg]; exact norm_mul_le _ _
  rw [inverse_add_eq x h]
  calc ‖Ring.inverse (1 - -((↑x⁻¹ : R) * t)) * (↑x⁻¹ : R)‖
      ≤ ‖Ring.inverse (1 - -((↑x⁻¹ : R) * t))‖ * ‖(↑x⁻¹ : R)‖ := norm_mul_le _ _
    _ ≤ (1 / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖)) * ‖(↑x⁻¹ : R)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (NormedRing.norm_inverse_one_sub_le (norm_neg_inv_mul_lt_one h)).trans
          (one_div_one_sub_le_one_div_one_sub hle (norm_inv_mul_lt_one h))
    _ = ‖(↑x⁻¹ : R)‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by ring

/-- Let $R$ be a complete normed ring with $\|1\| = 1$, let $x$ be a unit of $R$, and let $t \in R$
with $\|t\| < \|x^{-1}\|^{-1}$. Then
$$\|(x + t)^{-1} - x^{-1}\| \le \frac{\|x^{-1}\|^2 \|t\|}{1 - \|x^{-1}\| \|t\|}.$$
-/
theorem norm_inverse_add_sub_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t) - ↑x⁻¹‖ ≤
      ‖(↑x⁻¹ : R)‖ ^ 2 * ‖t‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by
  have hle : ‖(-((↑x⁻¹ : R) * t))‖ ≤ ‖(↑x⁻¹ : R)‖ * ‖t‖ := by
    rw [norm_neg]; exact norm_mul_le _ _
  have hrw : Ring.inverse ((x : R) + t) - (↑x⁻¹ : R)
      = (Ring.inverse (1 - -((↑x⁻¹ : R) * t)) - 1) * (↑x⁻¹ : R) := by
    rw [inverse_add_eq x h, sub_mul, one_mul]
  rw [hrw]
  calc ‖(Ring.inverse (1 - -((↑x⁻¹ : R) * t)) - 1) * (↑x⁻¹ : R)‖
      ≤ ‖Ring.inverse (1 - -((↑x⁻¹ : R) * t)) - 1‖ * ‖(↑x⁻¹ : R)‖ := norm_mul_le _ _
    _ ≤ (‖(↑x⁻¹ : R)‖ * ‖t‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖)) * ‖(↑x⁻¹ : R)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (NormedRing.norm_inverse_one_sub_sub_one_le (norm_neg_inv_mul_lt_one h)).trans
          (div_one_sub_le_div_one_sub hle (norm_inv_mul_lt_one h))
    _ = ‖(↑x⁻¹ : R)‖ ^ 2 * ‖t‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by ring

end Units

namespace ContinuousLinearEquiv

section OfUnit

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- For a unit $u$ of the ring of bounded operators on $V$, the continuous linear equivalence
`ContinuousLinearEquiv.ofUnit u` has underlying operator $u$. -/
theorem coe_ofUnit (u : (V →L[𝕜] V)ˣ) :
    ((ContinuousLinearEquiv.ofUnit u : V ≃L[𝕜] V) : V →L[𝕜] V) = (u : V →L[𝕜] V) := by
  ext x; rfl

/-- For a unit $u$ of the ring of bounded operators on $V$, the inverse map of
`ContinuousLinearEquiv.ofUnit u` is `Ring.inverse u`, the inverse of $u$. -/
theorem coe_ofUnit_symm (u : (V →L[𝕜] V)ˣ) :
    ((ContinuousLinearEquiv.ofUnit u).symm : V →L[𝕜] V) = Ring.inverse (u : V →L[𝕜] V) := by
  rw [Ring.inverse_unit]
  ext x; rfl

end OfUnit

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace E]

/-- The **perturbation theorem for an isomorphism**. Let $E$ be a Banach space and $F$ a normed
space over a nontrivially normed field, let $e \colon E \to F$ be an isomorphism, and let
$t \colon E \to F$ be bounded with $\|e^{-1}\| \|t\| < 1$. Then $e + t$ is an isomorphism, and
$$\|(e + t)^{-1}\| \le \frac{\|e^{-1}\|}{1 - \|e^{-1}\| \|t\|}, \qquad \|(e + t)^{-1} - e^{-1}\|
  \le \frac{\|e^{-1}\|^2 \|t\|}{1 - \|e^{-1}\| \|t\|}.$$
This is Theorem 2.3.5 of [han2009theoretical], with the bounds (2.3.13) and (2.3.14).

The isomorphism $e + t$ is given as a continuous linear equivalence $e'$ whose underlying
operator is $e + t$. Theorem 2.3.5 of [han2009theoretical] assumes that one of the two spaces is
complete; here the completeness of $E$ is assumed. -/
theorem exists_symm_norm_le_of_add (e : E ≃L[𝕜] F) (t : E →L[𝕜] F)
    (h : ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖ < 1) :
    ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = (e : E →L[𝕜] F) + t ∧
      ‖(e'.symm : F →L[𝕜] E)‖ ≤
        ‖(e.symm : F →L[𝕜] E)‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) ∧
      ‖(e'.symm : F →L[𝕜] E) - (e.symm : F →L[𝕜] E)‖ ≤
        ‖(e.symm : F →L[𝕜] E)‖ ^ 2 * ‖t‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) := by
  have hnu : ‖(e.symm : F →L[𝕜] E).comp t‖ ≤ ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hnu1 : ‖(-((e.symm : F →L[𝕜] E).comp t) : E →L[𝕜] E)‖ < 1 := by
    rw [norm_neg]; linarith
  have hone : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  obtain ⟨v, hv⟩ : IsUnit (1 - -((e.symm : F →L[𝕜] E).comp t)) :=
    isUnit_one_sub_of_norm_lt_one hnu1
  refine ⟨(ContinuousLinearEquiv.ofUnit v).trans e, ?_, ?_, ?_⟩
  · ext x
    change e ((v : E →L[𝕜] E) x) = e x + t x
    rw [hv]
    simp
  all_goals
    have hvinv : ((↑v⁻¹ : E →L[𝕜] E)) = Ring.inverse (1 - -((e.symm : F →L[𝕜] E).comp t)) := by
      rw [← hv, Ring.inverse_unit]
    have hsymm : (((ContinuousLinearEquiv.ofUnit v).trans e).symm : F →L[𝕜] E)
        = (↑v⁻¹ : E →L[𝕜] E).comp (e.symm : F →L[𝕜] E) := by ext y; rfl
    rw [hsymm]
  · calc ‖(↑v⁻¹ : E →L[𝕜] E).comp (e.symm : F →L[𝕜] E)‖
        ≤ ‖(↑v⁻¹ : E →L[𝕜] E)‖ * ‖(e.symm : F →L[𝕜] E)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖)) * ‖(e.symm : F →L[𝕜] E)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [hvinv]
          exact (NormedRing.norm_inverse_one_sub_le_of_norm_one_le hone hnu1).trans
            (one_div_one_sub_le_one_div_one_sub (by rwa [norm_neg]) h)
      _ = ‖(e.symm : F →L[𝕜] E)‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) := by ring
  · have hsub : (↑v⁻¹ : E →L[𝕜] E).comp (e.symm : F →L[𝕜] E) - (e.symm : F →L[𝕜] E)
        = ((↑v⁻¹ : E →L[𝕜] E) - 1).comp (e.symm : F →L[𝕜] E) := by
      ext y
      simp
    rw [hsub]
    calc ‖((↑v⁻¹ : E →L[𝕜] E) - 1).comp (e.symm : F →L[𝕜] E)‖
        ≤ ‖(↑v⁻¹ : E →L[𝕜] E) - 1‖ * ‖(e.symm : F →L[𝕜] E)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖(e.symm : F →L[𝕜] E)‖ * ‖t‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖)) *
            ‖(e.symm : F →L[𝕜] E)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [hvinv]
          exact (NormedRing.norm_inverse_one_sub_sub_one_le hnu1).trans
            (div_one_sub_le_div_one_sub (by rwa [norm_neg]) h)
      _ = ‖(e.symm : F →L[𝕜] E)‖ ^ 2 * ‖t‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) := by ring

omit [CompleteSpace E] in
/-- **Consistency and stability give convergence**. Let $L \colon E \to F$ be bounded, let
$L_n \colon E \to F$ be an isomorphism, and let $v, v_n \in E$ with $Lv = L_n v_n$. Then
$$\|v - v_n\| \le \|L_n^{-1}\| \, \|(L - L_n) v\|.$$

So a uniform bound on $\|L_n^{-1}\|$ (stability) turns the consistency error
$\|(L - L_n) v\| \to 0$ into $v_n \to v$. -/
theorem norm_sub_le_of_apply_eq (L : E →L[𝕜] F) (Ln : E ≃L[𝕜] F) {v vn : E}
    (h : L v = Ln vn) : ‖v - vn‖ ≤ ‖(Ln.symm : F →L[𝕜] E)‖ * ‖(L - Ln) v‖ := by
  have hv : (Ln.symm : F →L[𝕜] E) ((L - (Ln : E →L[𝕜] F)) v) = vn - v := by simp [h]
  calc ‖v - vn‖ = ‖(Ln.symm : F →L[𝕜] E) ((L - (Ln : E →L[𝕜] F)) v)‖ := by
        rw [hv, norm_sub_rev]
    _ ≤ ‖(Ln.symm : F →L[𝕜] E)‖ * ‖(L - (Ln : E →L[𝕜] F)) v‖ := ContinuousLinearMap.le_opNorm _ _

end ContinuousLinearEquiv
