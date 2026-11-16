/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The standard model of floating-point arithmetic

Let $K$ be an ordered field. A rounding model on $K$ fixes a unit roundoff $u \ge 0$ and a relation
that says which values $y$ are admissible results of rounding an exact value $x$. Every admissible
pair satisfies $|y - x| \le u |x|$, or equivalently $y = x(1 + \delta)$ with $|\delta| \le u$. This
is the standard model of [higham2002accuracy], (2.4), stated as a relation and not as a function. A
theorem proved in the model therefore holds for every rounding rule that meets the bound, and, when
the theorem is about an algorithm, for every evaluation order that its statement allows. A concrete
number format is connected to the model by showing that its rounding relation is a rounding model.

The bookkeeping constants are those of [higham2002accuracy]: $\gamma_n = nu/(1 - nu)$, and a value
$y$ is a relative perturbation of order $n$ of $x$ if $y = x(1 + \theta)$ for some
$|\theta| \le \gamma_n$. Two facts drive every error analysis. A product of $n$ factors
$(1 + \delta_i)^{\pm 1}$ with $|\delta_i| \le u$ is $1 + \theta$ with $|\theta| \le \gamma_n$, and
relative perturbations compose by adding their orders. The sharp form of the first fact,
$|\prod_i (1 + \delta_i) - 1| \le (1 + u)^n - 1$, needs no hypothesis on $nu$. It gives Wilkinson's
classical constant $1.01\,nu$ for $nu \le 0.01$ (Lemma 2.7.1 of [golub2013matrix]), which $\gamma_n$
does not give. The module also contains the arithmetic of the constants $\gamma_n$ and the steps
that an algorithm takes one operation at a time: one more rounding as a multiplication or a
division, a sum of nonnegative terms, a square root, a common factor, and the passage between a
relative perturbation and an error bound.

## Main definitions

* `FloatingPoint.RoundingModel`: a unit roundoff $u \ge 0$ and a rounding relation whose admissible
  pairs satisfy $|y - x| \le u|x|$.
* `FloatingPoint.RoundingModel.exact`: the exact model, with $u = 0$ and the rounding relation
  $y = x$.
* `FloatingPoint.RoundingModel.IsIdempotent`: rounding fixes its own outputs.
* `FloatingPoint.RoundingModel.IsTotal`: every value has an admissible rounding.
* `FloatingPoint.gamma`: the constant $\gamma_n = nu/(1 - nu)$.
* `FloatingPoint.IsRelPert`: $y = x(1 + \theta)$ for some $|\theta| \le \gamma_n$.

## Main results

* `FloatingPoint.RoundingModel.Rounds.exists_delta`: an admissible rounding of $x$ is
  $x(1 + \delta)$ for some $|\delta| \le u$.
* `FloatingPoint.abs_prod_one_add_sub_one_le_gamma`: if $nu < 1$, then $|\prod_{i=1}^n (1 +
  \delta_i)^{\rho_i} - 1| \le \gamma_n$ for $|\delta_i| \le u$ and $\rho_i = \pm 1$.
* `FloatingPoint.abs_prod_one_add_sub_one_le_one_add_pow_sub_one`: $|\prod_{i=1}^n (1 + \delta_i) -
  1| \le (1 + u)^n - 1$ for $|\delta_i| \le u$.
* `FloatingPoint.abs_prod_one_add_sub_one_le_of_mul_le`: if $nu \le 0.01$, then $|\prod_{i=1}^n (1 +
  \delta_i) - 1| \le 1.01\,nu$.
* `FloatingPoint.gamma_add_gamma_add_mul_le`: $\gamma_j + \gamma_k + \gamma_j \gamma_k \le
  \gamma_{j+k}$.
* `FloatingPoint.IsRelPert.trans`, `FloatingPoint.IsRelPert.mul`, `FloatingPoint.IsRelPert.div`:
  relative perturbations compose, multiply and divide, with orders $k + j$, $k + j$ and $k + 2j$.
* `FloatingPoint.IsRelPert.rounds`: one more rounding raises the order of a relative perturbation by
  one.
* `FloatingPoint.IsRelPert.add_of_nonneg`: a sum of two nonnegative values perturbed to order $k$ is
  perturbed to order $k$.
* `FloatingPoint.IsRelPert.sqrt`: the square root of a relative perturbation of order $n$ is one of
  order $n$ when $\gamma_n \le 1$.

## Implementation notes

* The rounding relation need not be functional, total or deterministic. Two further properties are
  named for the program semantics of `Numlib.FloatingPoint.Program`. The exact model gives the exact
  specification of an algorithm from a theorem proved for every model, and its rounding step is
  `pure`. Idempotence makes the first addition $0 + fl(x_1 y_1)$ of an inner-product loop exact, so
  that the analysis gives the constant $\gamma_n$ of the textbooks and not $\gamma_{n+1}$. Totality
  makes the set of runs of a program nonempty, so that a theorem about every run is not vacuous.
* The constant `FloatingPoint.gamma u n` is defined for all $u$ and $n$ by the formula
  $nu/(1 - nu)$, with the convention $a / 0 = 0$ of Lean. It is meaningful only when $nu < 1$, and
  every statement about it carries a hypothesis of this kind.
* The square-root step `FloatingPoint.IsRelPert.sqrt` is stated over $\mathbb{R}$; all other results
  hold over any linearly ordered field.
-/

open Finset

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### The rounding relation -/

/-- **The standard model of floating-point arithmetic** ([higham2002accuracy], (2.4)). A rounding
model on an ordered field $K$ consists of a unit roundoff $u \ge 0$ and a relation
$\operatorname{Rounds}(x, y)$, read "$y$ is an admissible floating-point value of the exact
$x$", such that every admissible pair satisfies $$|y - x| \le u |x|.$$

The relation need not be functional, total or deterministic. So a theorem stated for a rounding
model holds for every rounding rule that obeys the bound, and this is the strength that an error
analysis needs. -/
structure RoundingModel (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The unit roundoff $u$. -/
  u : K
  /-- The unit roundoff is nonnegative: $u \ge 0$. -/
  u_nonneg : 0 ≤ u
  /-- The rounding relation: `Rounds x y` holds when $y$ is an admissible floating-point value of
  the exact value $x$. -/
  Rounds : K → K → Prop
  /-- Every admissible rounding has relative error at most the unit roundoff: if $y$ is an
  admissible rounding of $x$, then $|y - x| \le u|x|$. -/
  abs_sub_le : ∀ {x y : K}, Rounds x y → |y - x| ≤ u * |x|

/-- The form of the standard model in [higham2002accuracy], (2.4). Let $m$ be a rounding model with
unit roundoff $u$. If $y$ is an admissible rounding of $x$, then there is $\delta \in K$ with
$$|\delta| \le u, \qquad y = x(1 + \delta).$$
-/
theorem RoundingModel.Rounds.exists_delta {m : RoundingModel K} {x y : K} (h : m.Rounds x y) :
    ∃ δ : K, |δ| ≤ m.u ∧ y = x * (1 + δ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : |y - 0| ≤ m.u * |0| := m.abs_sub_le h
    rw [sub_zero, abs_zero, mul_zero] at hy
    exact ⟨0, by simpa using m.u_nonneg, by simp [abs_nonpos_iff.1 hy]⟩
  · refine ⟨(y - x) / x, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.2 hx)]
      simpa [mul_comm] using m.abs_sub_le h
    · field_simp
      ring

/-! ### The exact model, idempotence and totality -/

namespace RoundingModel

/-- **The exact model** on $K$: the unit roundoff is $u = 0$, and the only admissible rounding of
$x$ is $x$ itself.

Every theorem proved for all rounding models specializes here to exact arithmetic. In the
program semantics of `Numlib.FloatingPoint.Program`, the rounding step of this model is `pure`. -/
def exact (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : RoundingModel K where
  u := 0
  u_nonneg := le_rfl
  Rounds x y := y = x
  abs_sub_le := by rintro x y rfl; simp

/-- The unit roundoff of the exact model is $0$. -/
@[simp] theorem exact_u : (exact K).u = 0 := rfl

/-- In the exact model, $y$ is an admissible rounding of $x$ if and only if $y = x$. -/
@[simp] theorem exact_rounds_iff {x y : K} : (exact K).Rounds x y ↔ y = x := Iff.rfl

/-- A rounding model is **idempotent** if rounding fixes its own outputs: if $y$ is an admissible
rounding of some $x$, and $z$ is an admissible rounding of $y$, then $z = y$.

Every concrete floating-point format has this property, because a floating-point number rounds
to itself. The property does not follow from the relative-error bound of the model. It makes
exact the first addition $fl(0 + fl(x_1 y_1))$ of an inner-product loop that starts at $s = 0$.
The textbook analyses that start from $s = 0$ assume this without saying so ([golub2013matrix],
(2.7.9)). -/
def IsIdempotent (m : RoundingModel K) : Prop :=
  ∀ ⦃x y z : K⦄, m.Rounds x y → m.Rounds y z → z = y

/-- The exact model is idempotent. -/
theorem isIdempotent_exact : (exact K).IsIdempotent := by
  rintro x y z rfl rfl
  rfl

/-- A rounding model is **total** if every $x \in K$ has an admissible rounding $y$.

A statement about every run of a program in a model is vacuous when the set of runs is empty.
This happens exactly when some value that the program rounds has no admissible rounding. Over a
total model every set of runs is nonempty (see `Numlib.FloatingPoint.Program`). -/
def IsTotal (m : RoundingModel K) : Prop := ∀ x : K, ∃ y, m.Rounds x y

/-- The exact model is total. -/
theorem isTotal_exact : (exact K).IsTotal := fun x => ⟨x, rfl⟩

end RoundingModel

/-! ### The constants $\gamma_n$ -/

/-- The constant $$\gamma_n = \frac{nu}{1 - nu}$$ of [higham2002accuracy], Lemma 3.1, which bounds
the relative error that $n$ roundings with unit roundoff $u$ accumulate.

The constant is meaningful only when $nu < 1$, and every statement about it carries a hypothesis
of this kind. The definition uses the Lean convention $a / 0 = 0$, so $\gamma_n = 0$ when
$nu = 1$. -/
def gamma (u : K) (n : ℕ) : K := n * u / (1 - n * u)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- By definition, $\gamma_n = nu/(1 - nu)$, over any field $K$. -/
theorem gamma_def (u : K) (n : ℕ) : gamma u n = n * u / (1 - n * u) := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- With no roundings there is no error: $\gamma_0 = 0$, over any field $K$. -/
@[simp]
theorem gamma_zero (u : K) : gamma u 0 = 0 := by simp [gamma]

/-- If $u \ge 0$ and $nu < 1$, then $\gamma_n \ge 0$. -/
theorem gamma_nonneg {u : K} (hu : 0 ≤ u) {n : ℕ} (h : (n : K) * u < 1) : 0 ≤ gamma u n :=
  div_nonneg (mul_nonneg (by positivity) hu) (by linarith)

/-- If $u \ge 0$ and $2ku \le 1$, then $\gamma_k \le 2ku$. -/
theorem gamma_le_two_mul {u : K} (hu : 0 ≤ u) {k : ℕ} (h : 2 * ((k : K) * u) ≤ 1) :
    gamma u k ≤ 2 * (k * u) := by
  have hk0 : 0 ≤ (k : K) * u := by positivity
  rw [gamma_def, div_le_iff₀ (by linarith)]
  nlinarith

/-- If $nu < 1$, then $1 + \gamma_n = (1 - nu)^{-1}$. This identity is the basis of the arithmetic
of the constants $\gamma_n$. -/
theorem one_add_gamma {u : K} {n : ℕ} (h : (n : K) * u < 1) :
    1 + gamma u n = (1 - (n : K) * u)⁻¹ := by
  have hne : (1 : K) - (n : K) * u ≠ 0 := by linarith
  rw [gamma_def]
  field_simp
  ring

/-- The constant $\gamma_n$ increases with $n$: if $u \ge 0$, $m \le n$ and $nu < 1$, then
$\gamma_m \le \gamma_n$. -/
theorem gamma_mono {u : K} (hu : 0 ≤ u) {m n : ℕ} (hmn : m ≤ n) (h : (n : K) * u < 1) :
    gamma u m ≤ gamma u n := by
  have hcast : (m : K) * u ≤ (n : K) * u :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hmn) hu
  rw [gamma_def, gamma_def, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- One rounding is bounded by $\gamma_1$: if $0 \le u < 1$, then $u \le \gamma_1$. -/
theorem le_gamma_one {u : K} (hu : 0 ≤ u) (h : u < 1) : u ≤ gamma u 1 := by
  rw [gamma_def, Nat.cast_one, one_mul, le_div_iff₀ (by linarith)]
  nlinarith

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Over any field, $\gamma_1 = u/(1 - u)$. -/
theorem gamma_one_eq {u : K} : gamma u 1 = u / (1 - u) := by simp [gamma_def]

/-- If $2ku < 1$, then $\gamma_k < 1$. -/
theorem gamma_lt_one {u : K} {k : ℕ} (h : 2 * ((k : K) * u) < 1) : gamma u k < 1 := by
  rw [gamma_def, div_lt_one (by linarith)]
  linarith

/-- If $2ku < 1$, then $$\frac{\gamma_k}{1 - \gamma_k} = \frac{ku}{1 - 2ku}.$$
-/
theorem gamma_div_one_sub_gamma {u : K} {k : ℕ} (h : 2 * ((k : K) * u) < 1) :
    gamma u k / (1 - gamma u k) = k * u / (1 - 2 * (k * u)) := by
  have h1 : (1 : K) - k * u ≠ 0 := by linarith
  have : 1 - gamma u k = (1 - 2 * (k * u)) / (1 - k * u) := by
    rw [gamma_def]
    field_simp
    ring
  rw [this, gamma_def, div_div_div_cancel_right₀ h1]

/-! ### Products of rounding factors -/

/-- **Lemma 3.1** of [higham2002accuracy]. Let $u \ge 0$ and $nu < 1$, and let
$\delta_1, \dots, \delta_n \in K$ with $|\delta_i| \le u$ and
$\rho_1, \dots, \rho_n \in \{1, -1\}$. Then $$\Bigl|\prod_{i=1}^n (1 + \delta_i)^{\rho_i} -
1\Bigr| \le \gamma_n.$$

Every factor lies between $1 - u$ and $(1 - u)^{-1}$. So the product lies between $(1 - u)^n$
and $(1 - u)^{-n}$, and Bernoulli's inequality $1 - nu \le (1 - u)^n$ turns the upper bound into
$1 + \gamma_n$. The indices run over `Fin n`, and the exponents $\rho_i$ are integers. -/
theorem abs_prod_one_add_sub_one_le_gamma {u : K} (hu : 0 ≤ u) {n : ℕ} (hnu : (n : K) * u < 1)
    {δ : Fin n → K} (hδ : ∀ i, |δ i| ≤ u) {ρ : Fin n → ℤ} (hρ : ∀ i, ρ i = 1 ∨ ρ i = -1) :
    |∏ i, (1 + δ i) ^ (ρ i) - 1| ≤ gamma u n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- `u < 1`, because `u ≤ n u < 1`
  have hu1 : u < 1 := by
    have hle : (1 : K) * u ≤ (n : K) * u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hu
    rw [one_mul] at hle
    linarith
  have hpos : (0 : K) < 1 - u := by linarith
  -- every factor lies in `[1 - u, (1 - u)⁻¹]`
  have hfac : ∀ i, 1 - u ≤ (1 + δ i) ^ (ρ i) ∧ (1 + δ i) ^ (ρ i) ≤ (1 - u)⁻¹ := by
    intro i
    have h1 : -u ≤ δ i := neg_le_of_abs_le (hδ i)
    have h2 : δ i ≤ u := le_of_abs_le (hδ i)
    have hd : (0 : K) < 1 + δ i := by linarith
    have hub : (1 : K) + δ i ≤ (1 - u)⁻¹ := by
      rw [← sub_nonneg]
      have heq : (1 - u)⁻¹ - (1 + δ i) = (1 - (1 + δ i) * (1 - u)) / (1 - u) := by
        field_simp
      rw [heq]
      exact div_nonneg (by nlinarith) hpos.le
    have hlb : 1 - u ≤ (1 + δ i)⁻¹ := by
      rw [← sub_nonneg]
      have heq : (1 + δ i)⁻¹ - (1 - u) = (1 - (1 - u) * (1 + δ i)) / (1 + δ i) := by
        field_simp
      rw [heq]
      exact div_nonneg (by nlinarith) hd.le
    have hub' : (1 + δ i)⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ hpos (by linarith)
    rcases hρ i with hr | hr <;> rw [hr]
    · rw [zpow_one]; exact ⟨by linarith, hub⟩
    · rw [zpow_neg_one]; exact ⟨hlb, hub'⟩
  have hnn : ∀ i, (0 : K) ≤ (1 + δ i) ^ (ρ i) := fun i => hpos.le.trans (hfac i).1
  -- hence the product lies in `[(1 - u)^n, ((1 - u)^n)⁻¹]`
  have hppos : (0 : K) < (1 - u) ^ n := pow_pos hpos n
  have hlow : (1 - u) ^ n ≤ ∏ i, (1 + δ i) ^ (ρ i) := by
    calc (1 - u) ^ n = ∏ _i : Fin n, (1 - u) := by simp
      _ ≤ ∏ i, (1 + δ i) ^ (ρ i) :=
          Finset.prod_le_prod₀ (fun _ _ => hpos.le) fun i _ => (hfac i).1
  have hhigh : (∏ i, (1 + δ i) ^ (ρ i)) ≤ ((1 - u) ^ n)⁻¹ := by
    calc (∏ i, (1 + δ i) ^ (ρ i)) ≤ ∏ _i : Fin n, (1 - u)⁻¹ :=
          Finset.prod_le_prod₀ (fun i _ => hnn i) fun i _ => (hfac i).2
      _ = ((1 - u) ^ n)⁻¹ := by simp
  -- Bernoulli's inequality turns `((1 - u)^n)⁻¹ - 1` into `γ_n`
  have hbern : 1 - (n : K) * u ≤ (1 - u) ^ n := by
    have h := one_add_mul_le_pow (a := -u) (by linarith) n
    simpa [sub_eq_add_neg, mul_neg] using h
  have hgamma : ((1 - u) ^ n)⁻¹ - 1 ≤ gamma u n := by
    have h1 : ((1 - u) ^ n)⁻¹ ≤ (1 - (n : K) * u)⁻¹ := by
      rw [← sub_nonneg]
      have heq : (1 - (n : K) * u)⁻¹ - ((1 - u) ^ n)⁻¹
          = ((1 - u) ^ n - (1 - (n : K) * u)) / ((1 - (n : K) * u) * (1 - u) ^ n) := by
        field_simp
      rw [heq]
      exact div_nonneg (by linarith) (mul_pos (by linarith) hppos).le
    have h2 := one_add_gamma (u := u) (n := n) hnu
    linarith
  have hlow2 : 1 - (1 - u) ^ n ≤ ((1 - u) ^ n)⁻¹ - 1 := by
    rw [← sub_nonneg]
    have heq : ((1 - u) ^ n)⁻¹ - 1 - (1 - (1 - u) ^ n)
        = (1 - (1 - u) ^ n) ^ 2 / (1 - u) ^ n := by
      field_simp
    rw [heq]
    exact div_nonneg (sq_nonneg _) hppos.le
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- One more factor in the sharp product bound: if $|\alpha| \le (1 + u)^k - 1$ and
$|\delta| \le u$, then $$|(1 + \alpha)(1 + \delta) - 1| \le (1 + u)^{k+1} - 1.$$
-/
theorem abs_one_add_mul_one_add_sub_one_le_one_add_pow_sub_one {u : K} {k : ℕ} {α δ : K}
    (hα : |α| ≤ (1 + u) ^ k - 1) (hδ : |δ| ≤ u) :
    |(1 + α) * (1 + δ) - 1| ≤ (1 + u) ^ (k + 1) - 1 := by
  have h1 : |1 + δ| ≤ 1 + u := (abs_add_le 1 δ).trans (by rw [abs_one]; linarith)
  calc |(1 + α) * (1 + δ) - 1| = |α * (1 + δ) + δ| := by ring_nf
    _ ≤ |α| * |1 + δ| + |δ| := by rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ ((1 + u) ^ k - 1) * (1 + u) + u :=
        add_le_add (mul_le_mul hα h1 (abs_nonneg _) ((abs_nonneg _).trans hα)) hδ
    _ = (1 + u) ^ (k + 1) - 1 := by ring

/-- **The sharp product bound** (from the proof of Lemma 2.7.1 of [golub2013matrix]). Let
$\delta_1, \dots, \delta_n \in K$ with $|\delta_i| \le u$. Then $$\Bigl|\prod_{i=1}^n (1 +
\delta_i) - 1\Bigr| \le (1 + u)^n - 1.$$

No hypothesis on $nu$ is needed. The bound is smaller than the bound $\gamma_n$ of
`FloatingPoint.abs_prod_one_add_sub_one_le_gamma` (see
`FloatingPoint.one_add_pow_sub_one_le_gamma`). -/
theorem abs_prod_one_add_sub_one_le_one_add_pow_sub_one {u : K} {n : ℕ} {δ : Fin n → K}
    (hδ : ∀ i, |δ i| ≤ u) : |∏ i, (1 + δ i) - 1| ≤ (1 + u) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    have hα := ih (δ := fun i => δ (Fin.castSucc i)) fun i => hδ _
    have h := abs_one_add_mul_one_add_sub_one_le_one_add_pow_sub_one hα (hδ (Fin.last n))
    rwa [add_sub_cancel] at h

/-- The passage from the sharp constant to $\gamma_r$: if $u \ge 0$ and $ru < 1$, then $$(1 + u)^r -
1 \le \gamma_r = \frac{ru}{1 - ru}.$$ This is Lemma 3.1 of [higham2002accuracy] with all
$\delta_i$ equal to $u$. -/
theorem one_add_pow_sub_one_le_gamma {u : K} (hu : 0 ≤ u) {r : ℕ} (hr : (r : K) * u < 1) :
    (1 + u) ^ r - 1 ≤ gamma u r := by
  have h := abs_prod_one_add_sub_one_le_gamma (u := u) hu (n := r) hr (δ := fun _ => u)
    (fun _ => le_of_eq (abs_of_nonneg hu)) (ρ := fun _ => 1) (fun _ => Or.inl rfl)
  simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact (le_abs_self _).trans h

/-- If $u \ge 0$ and $nu \le 1$, then $(1 + u)^n - 1 \le nu + (nu)^2$.

The induction step from $n$ to $n + 1$ reduces to $n^2 u^3 \le nu^2 + u^2$, which holds when
$nu \le 1$. -/
theorem one_add_pow_sub_one_le_mul_add_sq {u : K} (hu : 0 ≤ u) {n : ℕ} (h : (n : K) * u ≤ 1) :
    (1 + u) ^ n - 1 ≤ n * u + (n * u) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast at h ⊢
    have hn0 : (0 : K) ≤ n := n.cast_nonneg
    have hnu0 : 0 ≤ (n : K) * u := mul_nonneg hn0 hu
    have hnu : (n : K) * u ≤ 1 := by nlinarith
    have ih := ih hnu
    -- `(1 + u)^(n+1) - 1 = (1 + u) ((1 + u)^n - 1) + u`
    have hrec : (1 + u) ^ (n + 1) - 1 = (1 + u) * ((1 + u) ^ n - 1) + u := by ring
    rw [hrec]
    have hstep : (1 + u) * ((1 + u) ^ n - 1) + u ≤ (1 + u) * (n * u + (n * u) ^ 2) + u := by
      gcongr
    refine hstep.trans ?_
    -- the remaining gap is `u² (n + 1 - n² u) ≥ u²`
    have hgap : (n : K) * ((n : K) * u) ≤ n := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hu hu) (sub_nonneg.2 hgap)]

/-- **Lemma 2.7.1** of [golub2013matrix] (Wilkinson's constant). Let $u \ge 0$, and let
$\delta_1, \dots, \delta_n \in K$ with $|\delta_i| \le u$. If $nu \le 0.01$ and
$1 + \alpha = \prod_{i=1}^n (1 + \delta_i)$, then $$|\alpha| \le 1.01\,nu.$$

This does not follow from `FloatingPoint.abs_prod_one_add_sub_one_le_gamma`: at $nu = 0.01$,
$\gamma_n = nu/0.99 > 1.01\,nu$. The proof uses the sharp bound
`FloatingPoint.abs_prod_one_add_sub_one_le_one_add_pow_sub_one` and
`FloatingPoint.one_add_pow_sub_one_le_mul_add_sq`. The statement bounds
$|\prod_i (1 + \delta_i) - 1|$ directly, with the indices in `Fin n`. -/
theorem abs_prod_one_add_sub_one_le_of_mul_le {u : K} (hu : 0 ≤ u) {n : ℕ} {δ : Fin n → K}
    (hδ : ∀ i, |δ i| ≤ u) (h : (n : K) * u ≤ 1 / 100) :
    |∏ i, (1 + δ i) - 1| ≤ 101 / 100 * (n * u) := by
  have hnu0 : 0 ≤ (n : K) * u := mul_nonneg n.cast_nonneg hu
  refine (abs_prod_one_add_sub_one_le_one_add_pow_sub_one hδ).trans ?_
  refine (one_add_pow_sub_one_le_mul_add_sq hu (by linarith)).trans ?_
  nlinarith

/-! ### Relative perturbations -/

/-- A value $y \in K$ is a **relative perturbation of order $n$** of $x \in K$, for the unit
roundoff $u$, if $$y = x(1 + \theta) \quad \text{for some } |\theta| \le \gamma_n.$$

This is the notation $\theta_n$ of [higham2002accuracy], Lemma 3.1, made into a relation so that
it composes. -/
def IsRelPert (u : K) (n : ℕ) (x y : K) : Prop := ∃ θ : K, |θ| ≤ gamma u n ∧ y = x * (1 + θ)

/-- Every $x$ is a relative perturbation of order $0$ of itself. -/
theorem IsRelPert.refl (u : K) (x : K) : IsRelPert u 0 x x := ⟨0, by simp, by simp⟩

/-- A relative perturbation of order $m$ is one of every larger order $n$: if $u \ge 0$, $m \le n$,
$nu < 1$ and $y$ is a relative perturbation of order $m$ of $x$, then it is one of order $n$.
The reason is that $\gamma_n$ increases with $n$. -/
theorem IsRelPert.mono {u : K} (hu : 0 ≤ u) {m n : ℕ} (hmn : m ≤ n) (h : (n : K) * u < 1)
    {x y : K} (hxy : IsRelPert u m x y) : IsRelPert u n x y := by
  obtain ⟨θ, hθ, rfl⟩ := hxy
  exact ⟨θ, hθ.trans (gamma_mono hu hmn h), rfl⟩

/-- One rounding is a relative perturbation of order one: if the unit roundoff satisfies $u < 1$ and
$y$ is an admissible rounding of $x$, then $y$ is a relative perturbation of order $1$ of $x$. -/
theorem RoundingModel.Rounds.isRelPert {m : RoundingModel K} (hu : m.u < 1) {x y : K}
    (h : m.Rounds x y) : IsRelPert m.u 1 x y := by
  obtain ⟨δ, hδ, rfl⟩ := h.exists_delta
  exact ⟨δ, hδ.trans (le_gamma_one m.u_nonneg hu), rfl⟩

/-- The scalar inequality behind `FloatingPoint.IsRelPert.trans`, $\gamma_j + \gamma_k + \gamma_j
\gamma_k \le \gamma_{j+k}$, written with $x = ju$ and $y = ku$. -/
private theorem add_add_mul_div_le {x y : K} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y < 1) :
    x / (1 - x) + y / (1 - y) + x / (1 - x) * (y / (1 - y)) ≤ (x + y) / (1 - (x + y)) := by
  have h1 : (0 : K) < 1 - x := by linarith
  have h2 : (0 : K) < 1 - y := by linarith
  rw [← sub_nonneg]
  have heq : (x + y) / (1 - (x + y))
      - (x / (1 - x) + y / (1 - y) + x / (1 - x) * (y / (1 - y)))
      = x * y / ((1 - x) * (1 - y) * (1 - (x + y))) := by
    field_simp
    ring
  rw [heq]
  exact div_nonneg (mul_nonneg hx hy) (by positivity)

/-- **Lemma 3.3** of [higham2002accuracy]. If $u \ge 0$ and $(j + k)u < 1$, then $$\gamma_j +
\gamma_k + \gamma_j \gamma_k \le \gamma_{j+k},$$ that is, $(1 + \gamma_j)(1 + \gamma_k) \le 1 +
\gamma_{j+k}$. -/
theorem gamma_add_gamma_add_mul_le {u : K} (hu : 0 ≤ u) {j k : ℕ}
    (h : ((j + k : ℕ) : K) * u < 1) :
    gamma u j + gamma u k + gamma u j * gamma u k ≤ gamma u (j + k) := by
  have hcast : ((j + k : ℕ) : K) * u = (j : K) * u + (k : K) * u := by push_cast; ring
  rw [hcast] at h
  have hj : (0 : K) ≤ (j : K) * u := mul_nonneg (by positivity) hu
  have hk : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hmain := add_add_mul_div_le (x := (j : K) * u) (y := (k : K) * u) hj hk h
  rwa [gamma_def, gamma_def, gamma_def, hcast]

/-- If $u \ge 0$ and $3ku < 1$, then $$3\gamma_k + \gamma_k^2 \le \gamma_{3k}.$$ This is the
constant of Theorem 9.4 of [higham2002accuracy], and it follows from Lemma 3.3 of
[higham2002accuracy] applied twice. -/
theorem three_mul_gamma_add_sq_le {u : K} (hu : 0 ≤ u) {k : ℕ} (h : ((3 * k : ℕ) : K) * u < 1) :
    3 * gamma u k + gamma u k ^ 2 ≤ gamma u (3 * k) := by
  have h2 : ((k + k : ℕ) : K) * u < 1 := by
    have : ((k + k : ℕ) : K) * u ≤ ((3 * k : ℕ) : K) * u := by
      push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg (α := K) k) hu]
    linarith
  have h3 : ((k + k + k : ℕ) : K) * u < 1 := by
    have : ((k + k + k : ℕ) : K) = ((3 * k : ℕ) : K) := by push_cast; ring
    rwa [this]
  have hk : (k : K) * u < 1 := by
    have : (k : K) * u ≤ ((3 * k : ℕ) : K) * u := by
      push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg (α := K) k) hu]
    linarith
  have hg := gamma_nonneg hu hk
  have hA := gamma_add_gamma_add_mul_le hu (j := k) (k := k) h2
  have hB := gamma_add_gamma_add_mul_le hu (j := k + k) (k := k) h3
  have hg2 : 0 ≤ gamma u (k + k) := gamma_nonneg hu h2
  have h3k : k + k + k = 3 * k := by ring
  rw [h3k] at hB
  nlinarith [mul_nonneg hg2 hg]

/-- The scalar inequality behind `FloatingPoint.IsRelPert.div`, $\gamma_k + \gamma_j + \gamma_{k+2j}
\gamma_j \le \gamma_{k+2j}$, written with $x = ku$ and $y = ju$. -/
private theorem add_add_mul_div_le_div {x y : K} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + 2 * y < 1) :
    x / (1 - x) + y / (1 - y)
        + (x + 2 * y) / (1 - (x + 2 * y)) * (y / (1 - y))
      ≤ (x + 2 * y) / (1 - (x + 2 * y)) := by
  have h1 : (0 : K) < 1 - x := by linarith
  have h2 : (0 : K) < 1 - y := by linarith
  rw [← sub_nonneg]
  have heq : (x + 2 * y) / (1 - (x + 2 * y))
      - (x / (1 - x) + y / (1 - y) + (x + 2 * y) / (1 - (x + 2 * y)) * (y / (1 - y)))
      = y * (1 + x - 2 * y) / ((1 - x) * (1 - y) * (1 - (x + 2 * y))) := by
    field_simp
    ring
  rw [heq]
  exact div_nonneg (mul_nonneg hy (by linarith)) (by positivity)

/-- The form of Lemma 3.3 of [higham2002accuracy] that division needs: if $u \ge 0$ and
$(k + 2j)u < 1$, then $$\gamma_k + \gamma_j + \gamma_{k+2j} \gamma_j \le \gamma_{k+2j}.$$
-/
theorem gamma_add_gamma_add_mul_le_of_add_two_mul {u : K} (hu : 0 ≤ u) {k j : ℕ}
    (h : ((k + 2 * j : ℕ) : K) * u < 1) :
    gamma u k + gamma u j + gamma u (k + 2 * j) * gamma u j ≤ gamma u (k + 2 * j) := by
  have hcast : ((k + 2 * j : ℕ) : K) * u = (k : K) * u + 2 * ((j : K) * u) := by push_cast; ring
  rw [hcast] at h
  have hk : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hj : (0 : K) ≤ (j : K) * u := mul_nonneg (by positivity) hu
  have hmain := add_add_mul_div_le_div (x := (k : K) * u) (y := (j : K) * u) hk hj h
  rwa [gamma_def, gamma_def, gamma_def, hcast]

/-- **Relative perturbations compose** ([higham2002accuracy], Lemma 3.3). Let $u \ge 0$ and
$(k + j)u < 1$. If $y$ is a relative perturbation of order $k$ of $x$, and $z$ is a relative
perturbation of order $j$ of $y$, then $z$ is a relative perturbation of order $k + j$ of $x$.
In the notation of [higham2002accuracy], $(1 + \theta_k)(1 + \theta_j) = 1 + \theta_{k+j}$. -/
theorem IsRelPert.trans {u : K} (hu : 0 ≤ u) {k j : ℕ} (h : ((k + j : ℕ) : K) * u < 1)
    {x y z : K} (h₁ : IsRelPert u k x y) (h₂ : IsRelPert u j y z) : IsRelPert u (k + j) x z := by
  obtain ⟨θ₁, hθ₁, rfl⟩ := h₁
  obtain ⟨θ₂, hθ₂, rfl⟩ := h₂
  have hcast : ((k + j : ℕ) : K) * u = (k : K) * u + (j : K) * u := by push_cast; ring
  have hkn : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hjn : (0 : K) ≤ (j : K) * u := mul_nonneg (by positivity) hu
  have hk : (k : K) * u < 1 := by rw [hcast] at h; linarith
  have hgk : 0 ≤ gamma u k := gamma_nonneg hu hk
  refine ⟨θ₁ + θ₂ + θ₁ * θ₂, ?_, by ring⟩
  calc |θ₁ + θ₂ + θ₁ * θ₂| ≤ |θ₁ + θ₂| + |θ₁ * θ₂| := abs_add_le _ _
    _ ≤ |θ₁| + |θ₂| + |θ₁| * |θ₂| := by
        rw [abs_mul]
        exact add_le_add (abs_add_le θ₁ θ₂) le_rfl
    _ ≤ gamma u k + gamma u j + gamma u k * gamma u j :=
        add_le_add (add_le_add hθ₁ hθ₂) (mul_le_mul hθ₁ hθ₂ (abs_nonneg _) hgk)
    _ ≤ gamma u (k + j) := gamma_add_gamma_add_mul_le hu h

/-- **Products of relative perturbations** ([higham2002accuracy], Lemma 3.3). Let $u \ge 0$ and
$(k + j)u < 1$. If $y$ is a relative perturbation of order $k$ of $x$, and $w$ is a relative
perturbation of order $j$ of $z$, then $yw$ is a relative perturbation of order $k + j$ of $xz$. -/
theorem IsRelPert.mul {u : K} (hu : 0 ≤ u) {k j : ℕ} (h : ((k + j : ℕ) : K) * u < 1)
    {x y z w : K} (h₁ : IsRelPert u k x y) (h₂ : IsRelPert u j z w) :
    IsRelPert u (k + j) (x * z) (y * w) := by
  obtain ⟨θ₁, hθ₁, rfl⟩ := h₁
  obtain ⟨θ₂, hθ₂, rfl⟩ := h₂
  have hmid : IsRelPert u k (x * z) (x * (1 + θ₁) * z) := ⟨θ₁, hθ₁, by ring⟩
  have hlast : IsRelPert u j (x * (1 + θ₁) * z) (x * (1 + θ₁) * (z * (1 + θ₂))) :=
    ⟨θ₂, hθ₂, by ring⟩
  exact hmid.trans hu h hlast

/-- **Quotients of relative perturbations** ([higham2002accuracy], Lemma 3.3). Let $u \ge 0$ and
$(k + 2j)u < 1$. If $y$ is a relative perturbation of order $k$ of $x$, and $w$ is a relative
perturbation of order $j$ of $z$, then $y/w$ is a relative perturbation of order $k + 2j$ of
$x/z$.

The statement has no hypothesis $z \neq 0$: if $z = 0$, then $w = 0$, and both quotients are $0$
by the Lean convention $a / 0 = 0$. -/
theorem IsRelPert.div {u : K} (hu : 0 ≤ u) {k j : ℕ} (h : ((k + 2 * j : ℕ) : K) * u < 1)
    {x y z w : K} (h₁ : IsRelPert u k x y) (h₂ : IsRelPert u j z w) :
    IsRelPert u (k + 2 * j) (x / z) (y / w) := by
  obtain ⟨θ₁, hθ₁, rfl⟩ := h₁
  obtain ⟨θ₂, hθ₂, rfl⟩ := h₂
  have hcast : ((k + 2 * j : ℕ) : K) * u = (k : K) * u + 2 * ((j : K) * u) := by push_cast; ring
  have hkn : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
  have hgj : gamma u j < 1 := by
    rw [gamma_def, div_lt_one (by linarith)]
    linarith
  have hbound := abs_lt.1 (hθ₂.trans_lt hgj)
  have hden : (0 : K) < 1 + θ₂ := by linarith [hbound.1]
  have hgnn : 0 ≤ gamma u (k + 2 * j) := gamma_nonneg hu h
  have hstep := gamma_add_gamma_add_mul_le_of_add_two_mul hu h
  refine ⟨(1 + θ₁) / (1 + θ₂) - 1, ?_, ?_⟩
  · have hkey : (1 + θ₁) / (1 + θ₂) - 1 = (θ₁ - θ₂) / (1 + θ₂) := by
      field_simp
      ring
    rw [hkey, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have hnum : |θ₁ - θ₂| ≤ gamma u k + gamma u j := by
      calc |θ₁ - θ₂| = |θ₁ + -θ₂| := by rw [sub_eq_add_neg]
        _ ≤ |θ₁| + |-θ₂| := abs_add_le _ _
        _ = |θ₁| + |θ₂| := by rw [abs_neg]
        _ ≤ gamma u k + gamma u j := add_le_add hθ₁ hθ₂
    have hlow : 1 - gamma u j ≤ 1 + θ₂ := by
      linarith [neg_le_of_abs_le hθ₂]
    have hmul : gamma u (k + 2 * j) * (1 - gamma u j)
        ≤ gamma u (k + 2 * j) * (1 + θ₂) := mul_le_mul_of_nonneg_left hlow hgnn
    linarith
  · rw [show (1 : K) + ((1 + θ₁) / (1 + θ₂) - 1) = (1 + θ₁) / (1 + θ₂) by ring,
      div_mul_div_comm]

/-! ### One more rounding, multiplied or divided -/

/-- One more rounding raises the order of a relative perturbation by one: if $0 \le u < 1$ and
$(k + 1)u < 1$, then $$\gamma_k (1 + u) + u \le \gamma_{k+1}.$$ This is Lemma 3.3 of
[higham2002accuracy] together with $u \le \gamma_1$. -/
theorem gamma_mul_one_add_add_le {u : K} (hu : 0 ≤ u) (hu1 : u < 1) {k : ℕ}
    (h : ((k + 1 : ℕ) : K) * u < 1) : gamma u k * (1 + u) + u ≤ gamma u (k + 1) := by
  have hcast : ((k + 1 : ℕ) : K) * u = (k : K) * u + u := by push_cast; ring
  have hk : (k : K) * u < 1 := by rw [hcast] at h; linarith
  have hgk : 0 ≤ gamma u k := gamma_nonneg hu hk
  have hg1 : u ≤ gamma u 1 := le_gamma_one hu hu1
  have hmain := gamma_add_gamma_add_mul_le (u := u) hu (j := k) (k := 1) h
  have hmul : gamma u k * u ≤ gamma u k * gamma u 1 := mul_le_mul_of_nonneg_left hg1 hgk
  rw [mul_add, mul_one]
  linarith

/-- Multiplying by one rounding factor raises the order by one: if $0 \le u < 1$, $(k + 1)u < 1$,
$|\theta| \le \gamma_k$ and $|\delta| \le u$, then $$|(1 + \theta)(1 + \delta) - 1| \le
\gamma_{k+1}.$$ In the notation of [higham2002accuracy], Lemma 3.3,
$(1 + \theta_k)(1 + \delta) = 1 + \theta_{k+1}$. -/
theorem abs_one_add_mul_one_add_sub_one_le_gamma {u : K} (hu : 0 ≤ u) (hu1 : u < 1) {k : ℕ}
    (h : ((k + 1 : ℕ) : K) * u < 1) {θ δ : K} (hθ : |θ| ≤ gamma u k) (hδ : |δ| ≤ u) :
    |(1 + θ) * (1 + δ) - 1| ≤ gamma u (k + 1) := by
  have hk : (k : K) * u < 1 := by
    have : (k : K) * u ≤ ((k + 1 : ℕ) : K) * u := by push_cast; nlinarith
    linarith
  have hgk : 0 ≤ gamma u k := gamma_nonneg hu hk
  calc |(1 + θ) * (1 + δ) - 1| = |θ + δ + θ * δ| := by ring_nf
    _ ≤ |θ| + |δ| + |θ| * |δ| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ gamma u k + u + gamma u k * u :=
        add_le_add (add_le_add hθ hδ) (mul_le_mul hθ hδ (abs_nonneg _) hgk)
    _ = gamma u k * (1 + u) + u := by ring
    _ ≤ gamma u (k + 1) := gamma_mul_one_add_add_le hu hu1 h

/-- Dividing by one rounding factor raises the order by one: if $u \ge 0$, $(k + 1)u < 1$,
$|\theta| \le \gamma_k$ and $|\delta| \le u$, then $$\Bigl|\frac{1 + \theta}{1 + \delta} -
1\Bigr| \le \gamma_{k+1}.$$

The reason is that $(\gamma_k + u)/(1 - u) \le \gamma_{k+1}$. This is the case $\rho = -1$ of
Lemma 3.1 of [higham2002accuracy]. It is the reason that a division by one rounding factor costs
one order, and not the two of `FloatingPoint.IsRelPert.div`. -/
theorem abs_one_add_div_one_add_sub_one_le_gamma {u : K} (hu : 0 ≤ u) {k : ℕ}
    (h : ((k + 1 : ℕ) : K) * u < 1) {θ δ : K} (hθ : |θ| ≤ gamma u k) (hδ : |δ| ≤ u) :
    |(1 + θ) / (1 + δ) - 1| ≤ gamma u (k + 1) := by
  have hcast : ((k + 1 : ℕ) : K) * u = (k : K) * u + u := by push_cast; ring
  have hu1 : u < 1 := by
    have : (0 : K) ≤ (k : K) * u := mul_nonneg (by positivity) hu
    rw [hcast] at h
    linarith
  have hd : 0 < 1 + δ := by linarith [neg_le_of_abs_le hδ]
  have hkey : (1 + θ) / (1 + δ) - 1 = (θ - δ) / (1 + δ) := by
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  have hnum : |θ - δ| ≤ gamma u k + u :=
    (abs_sub _ _).trans (add_le_add hθ hδ)
  have hlow : 1 - u ≤ 1 + δ := by linarith [neg_le_of_abs_le hδ]
  have hg1 : 0 ≤ gamma u (k + 1) := gamma_nonneg hu h
  -- the scalar inequality `(γ_k + u) ≤ γ_{k+1} (1 - u)`
  have hscalar : gamma u k + u ≤ gamma u (k + 1) * (1 - u) := by
    rw [gamma_def, gamma_def, hcast]
    have h1 : (0 : K) < 1 - (k : K) * u := by linarith
    have h2 : (0 : K) < 1 - ((k : K) * u + u) := by linarith
    rw [div_add' _ _ _ h1.ne', div_mul_eq_mul_div, div_le_div_iff₀ h1 h2]
    have hk0 : (0 : K) ≤ k := by positivity
    nlinarith [mul_nonneg hk0 hu, mul_nonneg (mul_nonneg hk0 hu) hu]
  calc |θ - δ| ≤ gamma u k + u := hnum
    _ ≤ gamma u (k + 1) * (1 - u) := hscalar
    _ ≤ gamma u (k + 1) * (1 + δ) := mul_le_mul_of_nonneg_left hlow hg1

/-- A rounding read backwards costs $\gamma_1$: if $|\delta| \le u < 1$, then
$|\delta/(1 + \delta)| \le \gamma_1$. So $y = x(1 + \delta)$ gives
$x = y(1 - \delta/(1 + \delta))$, a relative perturbation of order $1$ in the other direction. -/
theorem abs_div_one_add_le_gamma_one {u δ : K} (hu : u < 1) (hδ : |δ| ≤ u) :
    |δ / (1 + δ)| ≤ gamma u 1 := by
  have hd : (0 : K) < 1 + δ := by linarith [neg_le_of_abs_le hδ]
  have hu1 : (0 : K) < 1 - u := by linarith
  rw [gamma_one_eq, abs_div, abs_of_pos hd, div_le_div_iff₀ hd hu1]
  nlinarith [neg_le_of_abs_le hδ, le_of_abs_le hδ, abs_nonneg δ]

/-! ### Relative perturbations, one operation at a time -/

section Steps

/-- In every rounding model, the only admissible rounding of $0$ is $0$. -/
theorem RoundingModel.Rounds.eq_zero_of_zero {m : RoundingModel K} {y : K} (h : m.Rounds 0 y) :
    y = 0 := by
  have := m.abs_sub_le h
  rw [sub_zero, abs_zero, mul_zero] at this
  exact abs_nonpos_iff.1 this

/-- An error bound gives a relative perturbation: if $\gamma_n \ge 0$ and
$|y - x| \le \gamma_n |x|$, then $y$ is a relative perturbation of order $n$ of $x$. -/
theorem isRelPert_of_abs_sub_le {u : K} {n : ℕ} (hγ : 0 ≤ gamma u n) {x y : K}
    (h : |y - x| ≤ gamma u n * |x|) : IsRelPert u n x y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [sub_zero, abs_zero, mul_zero] at h
    exact ⟨0, by simpa using hγ, by simp [abs_nonpos_iff.1 h]⟩
  · refine ⟨(y - x) / x, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.2 hx)]
      exact h
    · field_simp
      ring

/-- A relative perturbation gives an error bound: if $y$ is a relative perturbation of order $n$ of
$x$, then $|y - x| \le \gamma_n |x|$. -/
theorem IsRelPert.abs_sub_le {u : K} {n : ℕ} {x y : K} (h : IsRelPert u n x y) :
    |y - x| ≤ gamma u n * |x| := by
  obtain ⟨θ, hθ, rfl⟩ := h
  rw [show x * (1 + θ) - x = θ * x by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)

omit [IsStrictOrderedRing K] in
/-- A common factor keeps a relative perturbation: if $y$ is a relative perturbation of order $n$ of
$x$, then $cy$ is one of order $n$ of $cx$, for every $c \in K$. -/
theorem IsRelPert.const_mul {u : K} {n : ℕ} {x y : K} (h : IsRelPert u n x y) (c : K) :
    IsRelPert u n (c * x) (c * y) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  exact ⟨θ, hθ, by ring⟩

/-- If $\gamma_n \ge 0$, then $0$ is a relative perturbation of order $n$ of $0$. -/
theorem IsRelPert.zero {u : K} {n : ℕ} (hγ : 0 ≤ gamma u n) : IsRelPert u n (0 : K) 0 :=
  ⟨0, by simpa using hγ, by simp⟩

/-- Multiplying by one rounding factor: if $u \ge 0$, $(k + 1)u < 1$, $y$ is a relative perturbation
of order $k$ of $x$, and $|\delta| \le u$, then $y(1 + \delta)$ is a relative perturbation of
order $k + 1$ of $x$. -/
theorem IsRelPert.mul_one_add {u : K} (hu : 0 ≤ u) {k : ℕ}
    (hk : ((k + 1 : ℕ) : K) * u < 1) {x y δ : K} (h : IsRelPert u k x y) (hδ : |δ| ≤ u) :
    IsRelPert u (k + 1) x (y * (1 + δ)) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  have hu1 : u < 1 := by
    have : u ≤ ((k + 1 : ℕ) : K) * u := le_mul_of_one_le_left hu (by simp)
    linarith
  exact ⟨(1 + θ) * (1 + δ) - 1, abs_one_add_mul_one_add_sub_one_le_gamma hu hu1 hk hθ hδ,
    by ring⟩

/-- Dividing by one rounding factor: if $u \ge 0$, $(k + 1)u < 1$, $y$ is a relative perturbation of
order $k$ of $x$, and $|\delta| \le u$, then $y/(1 + \delta)$ is a relative perturbation of
order $k + 1$ of $x$. -/
theorem IsRelPert.div_one_add {u : K} (hu : 0 ≤ u) {k : ℕ}
    (hk : ((k + 1 : ℕ) : K) * u < 1) {x y δ : K} (h : IsRelPert u k x y) (hδ : |δ| ≤ u) :
    IsRelPert u (k + 1) x (y / (1 + δ)) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  refine ⟨(1 + θ) / (1 + δ) - 1, abs_one_add_div_one_add_sub_one_le_gamma hu hk hθ hδ, ?_⟩
  rw [show (1 : K) + ((1 + θ) / (1 + δ) - 1) = (1 + θ) / (1 + δ) by ring, mul_div_assoc]

/-- One more rounding raises the order of a relative perturbation by one. Let $m$ be a rounding
model with unit roundoff $u$ and $(k + 1)u < 1$. If $y$ is a relative perturbation of order $k$
of $x$, and $z$ is an admissible rounding of $y$, then $z$ is a relative perturbation of order
$k + 1$ of $x$. -/
theorem IsRelPert.rounds {m : RoundingModel K} {k : ℕ}
    (hk : ((k + 1 : ℕ) : K) * m.u < 1) {x y z : K} (h : IsRelPert m.u k x y)
    (hz : m.Rounds y z) : IsRelPert m.u (k + 1) x z := by
  obtain ⟨δ, hδ, rfl⟩ := hz.exists_delta
  exact h.mul_one_add m.u_nonneg hk hδ

/-- Sums of nonnegative values: let $x_1, x_2 \ge 0$. If $y_1$ and $y_2$ are relative perturbations
of order $k$ of $x_1$ and $x_2$, then $y_1 + y_2$ is a relative perturbation of order $k$ of
$x_1 + x_2$.

The perturbation of the sum is the convex combination
$(x_1 \theta_1 + x_2 \theta_2)/(x_1 + x_2)$ of the two perturbations. This is the step for
quantities such as $1 + \tau^2$ and $a^2 + b^2$ in the Givens and Householder analyses. -/
theorem IsRelPert.add_of_nonneg {u : K} {k : ℕ} {x₁ x₂ y₁ y₂ : K} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (h₁ : IsRelPert u k x₁ y₁) (h₂ : IsRelPert u k x₂ y₂) :
    IsRelPert u k (x₁ + x₂) (y₁ + y₂) := by
  obtain ⟨θ₁, hθ₁, rfl⟩ := h₁
  obtain ⟨θ₂, hθ₂, rfl⟩ := h₂
  rcases (add_nonneg hx₁ hx₂).eq_or_lt with h | h
  · obtain rfl : x₁ = 0 := by linarith
    obtain rfl : x₂ = 0 := by linarith
    exact ⟨0, by simpa using (abs_nonneg θ₁).trans hθ₁, by simp⟩
  · refine ⟨(x₁ * θ₁ + x₂ * θ₂) / (x₁ + x₂), ?_, ?_⟩
    · rw [abs_div, abs_of_pos h, div_le_iff₀ h]
      calc |x₁ * θ₁ + x₂ * θ₂| ≤ x₁ * |θ₁| + x₂ * |θ₂| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hx₁, abs_of_nonneg hx₂]
        _ ≤ x₁ * gamma u k + x₂ * gamma u k := by gcongr
        _ = gamma u k * (x₁ + x₂) := by ring
    · field_simp
      ring

/-- Finite sums of nonnegative values: let $s$ be a finite set and $\gamma_k \ge 0$. If $x_i \ge 0$
and $y_i$ is a relative perturbation of order $k$ of $x_i$ for every $i \in s$, then
$\sum_{i \in s} y_i$ is a relative perturbation of order $k$ of $\sum_{i \in s} x_i$.

This is `FloatingPoint.IsRelPert.add_of_nonneg` by induction, the step for a computed $x^T x$ or
$\|x\|_2^2$. -/
theorem IsRelPert.sum_of_nonneg {ι : Type*} (s : Finset ι) {u : K} {k : ℕ} (hγ : 0 ≤ gamma u k)
    {x y : ι → K} (hx : ∀ i ∈ s, 0 ≤ x i) (h : ∀ i ∈ s, IsRelPert u k (x i) (y i)) :
    IsRelPert u k (∑ i ∈ s, x i) (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsRelPert.zero hγ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact IsRelPert.add_of_nonneg (hx a (Finset.mem_insert_self a s))
      (Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
        fun i hi => h i (Finset.mem_insert_of_mem hi))

end Steps

/-! ### Square roots -/

/-- For real $\theta \ge -1$, $|\sqrt{1 + \theta} - 1| \le |\theta|$. -/
theorem abs_sqrt_one_add_sub_one_le {θ : ℝ} (h : -1 ≤ θ) : |√(1 + θ) - 1| ≤ |θ| := by
  have h0 : 0 ≤ 1 + θ := by linarith
  have hs : 0 ≤ √(1 + θ) := Real.sqrt_nonneg _
  have hsq : √(1 + θ) ^ 2 = 1 + θ := Real.sq_sqrt h0
  have key : (√(1 + θ) - 1) * (√(1 + θ) + 1) = θ := by nlinarith
  have hpos : 1 ≤ √(1 + θ) + 1 := by linarith
  calc |√(1 + θ) - 1| ≤ |√(1 + θ) - 1| * (√(1 + θ) + 1) :=
        le_mul_of_one_le_right (abs_nonneg _) hpos
    _ = |(√(1 + θ) - 1) * (√(1 + θ) + 1)| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < √(1 + θ) + 1)]
    _ = |θ| := by rw [key]

/-- Square roots of relative perturbations: let $u \in \mathbb{R}$ with $\gamma_n \le 1$, and let
$x \ge 0$. If $y$ is a relative perturbation of order $n$ of $x$, then $\sqrt{y}$ is a relative
perturbation of order $n$ of $\sqrt{x}$. -/
theorem IsRelPert.sqrt {u : ℝ} {n : ℕ} (hγ : gamma u n ≤ 1) {x y : ℝ} (hx : 0 ≤ x)
    (h : IsRelPert u n x y) : IsRelPert u n (√x) (√y) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  have hθ1 : -1 ≤ θ := by linarith [neg_le_of_abs_le hθ]
  refine ⟨√(1 + θ) - 1, (abs_sqrt_one_add_sub_one_le hθ1).trans hθ, ?_⟩
  rw [Real.sqrt_mul hx, add_sub_cancel]

end FloatingPoint
