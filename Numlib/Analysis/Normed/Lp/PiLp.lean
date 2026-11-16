/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Lp.PiLp`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Numlib.Data.ENNReal.Real

/-!
# Comparison of the $\ell^p$ norms on a finite product

Let $x = (x_i)_{i \in \iota}$ be an element of a finite product `PiLp p β` of seminormed groups,
with $n$ factors. Its $p$-norm is $\|x\|_p = (\sum_i \|x_i\|^p)^{1/p}$ for $1 \le p < \infty$ and
$\|x\|_\infty = \max_i \|x_i\|$. This module compares these norms: for $1 \le p \le q \le \infty$,
$$\|x\|_q \le \|x\|_p \le n^{1/p - 1/q} \|x\|_q,$$
and $\|x\|_p \to \|x\|_\infty$ as $p \to \infty$. The six cases with $p, q \in \{1, 2, \infty\}$ are
the equivalence constants $1$, $\sqrt{n}$ and $n$ of [quarteroni2000numerical], Table 1.1.

The module also proves that the $p$-norm is monotone in the norms of the coordinates, that dropping
coordinates does not increase it and extending by zero preserves it, and Hölder's inequality
$|x \cdot y| \le \|x\|_p \|y\|_q$ for conjugate exponents ([golub2013matrix], (2.2.2)). Finally it
identifies the dot products $x^T x$ and $x^H x$ with the squared Euclidean norm.

## Main results

* `NNReal.sum_rpow_le_rpow_sum`: $\sum_i f_i^p \le (\sum_i f_i)^p$ for $f_i \ge 0$ and $p \ge 1$.
* `PiLp.norm_le_norm_of_le`: $\|x\|_q \le \|x\|_p$ for $1 \le p \le q \le \infty$.
* `PiLp.norm_le_card_rpow_mul_norm`: $\|x\|_p \le n^{1/p - 1/q} \|x\|_q$ for
  $1 \le p \le q \le \infty$.
* `PiLp.tendsto_norm_toLp_atTop`: $\|x\|_p \to \|x\|_\infty$ as $p \to \infty$.
* `PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two` and the other five cases with
  $p, q \in \{1, 2, \infty\}$: the constants of [quarteroni2000numerical], Table 1.1.
* `PiLp.norm_toLp_comp_le`, `PiLp.norm_toLp_extend`: dropping coordinates does not increase the
  $p$-norm, and extending by zero preserves it.
* `PiLp.norm_dotProduct_le`: Hölder's inequality $|x \cdot y| \le \|x\|_p \|y\|_q$ for conjugate
  exponents, the endpoints included.
* `Matrix.dotProduct_self_eq_norm_sq`, `Matrix.star_dotProduct_self`: $x^T x$ and $x^H x$ are the
  squared Euclidean norm of $x$.

## Implementation notes

* Mathlib has the comparison of the $\infty$-norm with the $p$-norm only as the Lipschitz constants
  `PiLp.lipschitzWith_toLp` and `PiLp.antilipschitzWith_ofLp`.
* Mathlib has Hölder's inequality for the sequence space `lp` (`lp.norm_dualPairing`) and for finite
  sums of reals (`Real.inner_le_Lp_mul_Lq`), but not in the form of `PiLp.norm_dotProduct_le`.
* The consequences for matrices, such as the comparison of the induced matrix norms and the bound
  `Matrix.lpOpNorm_submatrix_le` for a submatrix, are in `Numlib.Analysis.Matrix.OperatorNorm`.
-/

open Filter Topology WithLp
open scoped ENNReal NNReal

/-- Let $s$ be a finite set, let $f_i \ge 0$ for $i \in s$, and let $p \ge 1$. Then
$$\sum_{i \in s} f_i^p \le \Big(\sum_{i \in s} f_i\Big)^p,$$
that is, $t \mapsto t^p$ is superadditive on $[0, \infty)$. This is the form for finite sums of
`NNReal.add_rpow_le_rpow_add`. -/
theorem NNReal.sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0) {p : ℝ}
    (hp : 1 ≤ p) : ∑ i ∈ s, f i ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    calc f j ^ p + ∑ i ∈ s, f i ^ p ≤ f j ^ p + (∑ i ∈ s, f i) ^ p := by gcongr
      _ ≤ (f j + ∑ i ∈ s, f i) ^ p := NNReal.add_rpow_le_rpow_add _ _ hp

namespace PiLp

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)]

/-- **The $p$-norms decrease in $p$.** Let $x$ be an element of a finite product of seminormed
groups, and let $1 \le p \le q \le \infty$. Then
$$\|x\|_q \le \|x\|_p.$$
These are the constants $c_{pq} = 1$ of [quarteroni2000numerical], Table 1.1.

For finite $q$ this is the superadditivity of $t \mapsto t^{q/p}$, which gives
$\sum_i \|x_i\|^q \le (\sum_i \|x_i\|^p)^{q/p}$; for $q = \infty$ it is `PiLp.norm_apply_le`.
Here $\|x\|_p$ is the norm of `toLp p x`. -/
theorem norm_le_norm_of_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q)
    (x : ∀ i, β i) : ‖toLp q x‖ ≤ ‖toLp p x‖ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [norm_toLp]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_apply_le (toLp p x) i
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := zero_lt_one.trans_le (ENNReal.one_le_toReal_of_ne_top hp)
  have hQ : 0 < q.toReal := zero_lt_one.trans_le (ENNReal.one_le_toReal_of_ne_top hq)
  have hr : 1 ≤ q.toReal / p.toReal := (one_le_div hP).2 (ENNReal.toReal_mono hq hpq)
  have key : ‖toLp q x‖₊ ≤ ‖toLp p x‖₊ := by
    rw [nnnorm_eq_sum hq, nnnorm_eq_sum hp]
    calc (∑ i, ‖x i‖₊ ^ q.toReal) ^ (1 / q.toReal)
        = (∑ i, (‖x i‖₊ ^ p.toReal) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← NNReal.rpow_mul, mul_div_cancel₀ _ hP.ne']
      _ ≤ ((∑ i, ‖x i‖₊ ^ p.toReal) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) :=
          NNReal.rpow_le_rpow (NNReal.sum_rpow_le_rpow_sum _ _ hr) (by positivity)
      _ = (∑ i, ‖x i‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [← NNReal.rpow_mul]
          congr 1
          field_simp
  exact_mod_cast key

/-- **The $p$-norms are equivalent.** Let $x$ be an element of a finite product of $n$ seminormed
groups, and let $1 \le p \le q \le \infty$. Then
$$\|x\|_p \le n^{1/p - 1/q} \|x\|_q,$$
with $1/\infty = 0$. These are the constants $C_{pq}$ of [quarteroni2000numerical], Table 1.1.

For finite $q$ this is the power-mean inequality `NNReal.rpow_sum_le_const_mul_sum_rpow` with
exponent $q/p$; for $q = \infty$ it is the Lipschitz constant `PiLp.lipschitzWith_toLp`. The
exponents are converted with `ENNReal.toReal`, which maps $\infty$ to $0$. -/
theorem norm_le_card_rpow_mul_norm {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q)
    (x : ∀ i, β i) :
    ‖toLp p x‖ ≤ (Fintype.card ι : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖toLp q x‖ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [norm_toLp, ENNReal.toReal_top, div_zero, sub_zero]
    have h := (lipschitzWith_toLp p β).norm_le_mul (toLp_zero p) x
    rwa [NNReal.coe_rpow, NNReal.coe_natCast, one_div, ENNReal.toReal_inv, ← one_div] at h
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := zero_lt_one.trans_le (ENNReal.one_le_toReal_of_ne_top hp)
  have hQ : 0 < q.toReal := zero_lt_one.trans_le (ENNReal.one_le_toReal_of_ne_top hq)
  have hr : 1 ≤ q.toReal / p.toReal := (one_le_div hP).2 (ENNReal.toReal_mono hq hpq)
  have key : ‖toLp p x‖₊ ≤
      (Fintype.card ι : ℝ≥0) ^ (1 / p.toReal - 1 / q.toReal) * ‖toLp q x‖₊ := by
    rw [nnnorm_eq_sum hq, nnnorm_eq_sum hp]
    have hmean := NNReal.rpow_sum_le_const_mul_sum_rpow Finset.univ
      (fun i => ‖x i‖₊ ^ p.toReal) hr
    simp only [Finset.card_univ, ← NNReal.rpow_mul, mul_div_cancel₀ _ hP.ne'] at hmean
    calc (∑ i, ‖x i‖₊ ^ p.toReal) ^ (1 / p.toReal)
        = ((∑ i, ‖x i‖₊ ^ p.toReal) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
          rw [← NNReal.rpow_mul]
          congr 1
          field_simp
      _ ≤ ((Fintype.card ι : ℝ≥0) ^ (q.toReal / p.toReal - 1) * ∑ i, ‖x i‖₊ ^ q.toReal) ^
            (1 / q.toReal) := NNReal.rpow_le_rpow hmean (by positivity)
      _ = (Fintype.card ι : ℝ≥0) ^ (1 / p.toReal - 1 / q.toReal) *
            (∑ i, ‖x i‖₊ ^ q.toReal) ^ (1 / q.toReal) := by
          rw [NNReal.mul_rpow, ← NNReal.rpow_mul]
          congr 2
          field_simp
  exact_mod_cast key

/-- Let $x$ be an element of a finite product of seminormed groups. Then
$$\|x\|_p \to \|x\|_\infty \qquad \text{as the real number } p \to \infty.$$
The maximum norm is thus the limit of the $p$-norms ([quarteroni2000numerical], §1.10).

The proof squeezes $\|x\|_p$ between $\|x\|_\infty \le \|x\|_p \le (n + 1)^{1/p} \|x\|_\infty$,
where $n$ is the number of coordinates. The $p$-norm in the statement is the norm of `PiLp` at
the exponent `ENNReal.ofReal p`, which is defined for every exponent; the bounds hold for
$p \ge 1$. -/
theorem tendsto_norm_toLp_atTop (x : ∀ i, β i) :
    Tendsto (fun p : ℝ => ‖toLp (ENNReal.ofReal p) x‖) atTop (𝓝 ‖toLp ∞ x‖) := by
  have hn : Tendsto (fun p : ℝ => ((Fintype.card ι : ℝ) + 1) ^ (1 / p)) atTop (𝓝 1) := by
    have h := (Real.continuousAt_const_rpow
      (by positivity : ((Fintype.card ι : ℝ) + 1) ≠ 0)).tendsto.comp tendsto_inv_atTop_zero
    simpa [Function.comp_def, one_div] using h
  have hfact : ∀ p : ℝ, 1 ≤ p → Fact (1 ≤ ENNReal.ofReal p) := fun p hp =>
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => ‖toLp ∞ x‖)
    (h := fun p => ((Fintype.card ι : ℝ) + 1) ^ (1 / p) * ‖toLp ∞ x‖) tendsto_const_nhds
    (by simpa only [one_mul] using hn.mul_const ‖toLp ∞ x‖) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with p hp
    have := hfact p hp
    exact norm_le_norm_of_le le_top x
  · filter_upwards [eventually_ge_atTop 1] with p hp
    have := hfact p hp
    have h := norm_le_card_rpow_mul_norm (p := ENNReal.ofReal p) (q := ∞) le_top x
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_top, div_zero, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by positivity)

/-!
### The constants of Table 1.1

The six comparisons between the $1$-, $2$- and $\infty$-norms in [quarteroni2000numerical], Table
1.1: $\|x\|_\infty \le \|x\|_2 \le \|x\|_1$ and $\|x\|_\infty \le \|x\|_1$ with constant $1$, and
$\|x\|_1 \le \sqrt{n} \|x\|_2$, $\|x\|_2 \le \sqrt{n} \|x\|_\infty$ and
$\|x\|_1 \le n \|x\|_\infty$, where $n$ is the number of coordinates.
-/

/-- For $x$ in a finite product of seminormed groups, $\|x\|_2 \le \|x\|_1$. This is a constant $1$
of [quarteroni2000numerical], Table 1.1. -/
theorem norm_toLp_two_le_norm_toLp_one (x : ∀ i, β i) : ‖toLp 2 x‖ ≤ ‖toLp 1 x‖ :=
  norm_le_norm_of_le (by norm_num) x

/-- For $x$ in a finite product of seminormed groups, $\|x\|_\infty \le \|x\|_2$. This is a constant
$1$ of [quarteroni2000numerical], Table 1.1. -/
theorem norm_toLp_top_le_norm_toLp_two (x : ∀ i, β i) : ‖toLp ∞ x‖ ≤ ‖toLp 2 x‖ :=
  norm_le_norm_of_le le_top x

/-- For $x$ in a finite product of seminormed groups, $\|x\|_\infty \le \|x\|_1$. This is a constant
$1$ of [quarteroni2000numerical], Table 1.1. -/
theorem norm_toLp_top_le_norm_toLp_one (x : ∀ i, β i) : ‖toLp ∞ x‖ ≤ ‖toLp 1 x‖ :=
  norm_le_norm_of_le le_top x

/-- For $x$ in a finite product of $n$ seminormed groups, $\|x\|_1 \le \sqrt{n}\, \|x\|_2$. This is
a constant of [quarteroni2000numerical], Table 1.1. -/
theorem norm_toLp_one_le_sqrt_card_mul_norm_toLp_two (x : ∀ i, β i) :
    ‖toLp 1 x‖ ≤ √(Fintype.card ι : ℝ) * ‖toLp 2 x‖ := by
  have h := norm_le_card_rpow_mul_norm (p := 1) (q := 2) (by norm_num) x
  rw [Real.sqrt_eq_rpow]
  convert h using 3
  norm_num

/-- For $x$ in a finite product of $n$ seminormed groups, $\|x\|_2 \le \sqrt{n}\, \|x\|_\infty$.
This is a constant of [quarteroni2000numerical], Table 1.1. -/
theorem norm_toLp_two_le_sqrt_card_mul_norm_toLp_top (x : ∀ i, β i) :
    ‖toLp 2 x‖ ≤ √(Fintype.card ι : ℝ) * ‖toLp ∞ x‖ := by
  have h := norm_le_card_rpow_mul_norm (p := 2) (q := ∞) le_top x
  rw [Real.sqrt_eq_rpow]
  convert h using 3
  norm_num

/-- For $x$ in a finite product of $n$ seminormed groups, $\|x\|_1 \le n \|x\|_\infty$. This is a
constant of [quarteroni2000numerical], Table 1.1. -/
theorem norm_toLp_one_le_card_mul_norm_toLp_top (x : ∀ i, β i) :
    ‖toLp 1 x‖ ≤ Fintype.card ι * ‖toLp ∞ x‖ := by
  have h := norm_le_card_rpow_mul_norm (p := 1) (q := ∞) le_top x
  simpa using h

/-! ### Monotonicity in the coordinates -/

section Mono

variable {γ : ι → Type*} [∀ i, SeminormedAddCommGroup (γ i)]

/-- Let $1 \le p \le \infty$, let $y$ and $z$ be elements of two finite products of seminormed
groups over the same index set, and let $c \ge 0$. If $\|y_i\| \le c \|z_i\|$ for every $i$,
then
$$\|y\|_p \le c \|z\|_p.$$
-/
theorem norm_toLp_le_mul_norm_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] {y : ∀ i, β i} {z : ∀ i, γ i}
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ‖y i‖ ≤ c * ‖z i‖) :
    ‖WithLp.toLp p y‖ ≤ c * ‖WithLp.toLp p z‖ := by
  rcases p.dichotomy with rfl | hp
  · rw [norm_eq_ciSup]
    exact Real.iSup_le (fun i => (h i).trans (mul_le_mul_of_nonneg_left
      (norm_apply_le (WithLp.toLp ⊤ z) i) hc)) (by positivity)
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [norm_eq_sum hp0, norm_eq_sum hp0]
    calc (∑ i, ‖y i‖ ^ p.toReal) ^ (1 / p.toReal)
        ≤ (∑ i, (c * ‖z i‖) ^ p.toReal) ^ (1 / p.toReal) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
            (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (h i) hp0.le)
            (by positivity)
      _ = c * (∑ i, ‖z i‖ ^ p.toReal) ^ (1 / p.toReal) := by
          simp_rw [Real.mul_rpow hc (norm_nonneg _)]
          rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg hc _)
            (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _),
            ← Real.rpow_mul hc, mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- **The $\ell^p$ norm is monotone in the coordinates.** Let $1 \le p \le \infty$, and let $x$ and
$y$ be elements of the $\ell^p$ products of two families of seminormed groups over the same
finite index set. If $\|x_i\| \le \|y_i\|$ for every $i$, then
$$\|x\|_p \le \|y\|_p.$$
-/
theorem norm_le_norm_of_forall_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {x : PiLp p β} {y : PiLp p γ}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    exact ciSup_mono (Finite.bddAbove_range _) h
  · have hP : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hP]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (h i) hP.le) (by positivity)

end Mono

/-! ### Subfamilies of coordinates, and extension by zero -/

section Reindex

variable {E : Type*} [SeminormedAddCommGroup E] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Let $E$ be a seminormed group, let $1 \le p \le \infty$, let $f : \iota \to \iota'$ be an
injection of finite index sets, and let $y \in E^{\iota'}$. Then the subfamily $y \circ f$ has
no larger $\ell^p$ norm:
$$\|y \circ f\|_p \le \|y\|_p.$$
-/
theorem norm_toLp_comp_le {ι ι' : Type*} [Fintype ι] [Fintype ι'] {f : ι → ι'}
    (hf : Function.Injective f) (y : ι' → E) :
    ‖(toLp p (y ∘ f) : PiLp p fun _ : ι => E)‖ ≤ ‖(toLp p y : PiLp p fun _ : ι' => E)‖ := by
  classical
  rcases p.dichotomy with rfl | hp
  · rw [norm_eq_ciSup]
    exact Real.iSup_le (fun i => norm_apply_le (toLp ⊤ y) (f i)) (norm_nonneg _)
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [norm_eq_sum hp0, norm_eq_sum hp0]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity) ?_ (by positivity)
    change ∑ i, ‖y (f i)‖ ^ p.toReal ≤ ∑ k, ‖y k‖ ^ p.toReal
    rw [← Finset.sum_image (f := fun k => ‖y k‖ ^ p.toReal) hf.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => by positivity

/-- Let $E$ be a seminormed group, let $1 \le p \le \infty$, let $g : \iota \to \iota'$ be an
injection of finite index sets, and let $x \in E^\iota$. Let $\tilde{x} \in E^{\iota'}$ be the
extension of $x$ by zero along $g$: $\tilde{x}_{g(i)} = x_i$, and $\tilde{x}_j = 0$ for $j$
outside the range of $g$. Then
$$\|\tilde{x}\|_p = \|x\|_p.$$

The extension is `Function.extend g x 0`. -/
theorem norm_toLp_extend {ι ι' : Type*} [Fintype ι] [Fintype ι'] {g : ι → ι'}
    (hg : Function.Injective g) (x : ι → E) :
    ‖(toLp p (Function.extend g x 0) : PiLp p fun _ : ι' => E)‖
      = ‖(toLp p x : PiLp p fun _ : ι => E)‖ := by
  classical
  refine le_antisymm ?_ ?_
  · rcases p.dichotomy with rfl | hp
    · rw [norm_eq_ciSup]
      refine Real.iSup_le (fun k => ?_) (norm_nonneg _)
      by_cases hk : ∃ i, g i = k
      · obtain ⟨i, rfl⟩ := hk
        rw [ofLp_toLp, hg.extend_apply]
        exact norm_apply_le (toLp ⊤ x) i
      · rw [ofLp_toLp, Function.extend_apply' _ _ _ hk, Pi.zero_apply, norm_zero]
        exact norm_nonneg _
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      rw [norm_eq_sum hp0, norm_eq_sum hp0]
      refine le_of_eq (congrArg (· ^ (1 / p.toReal)) ?_)
      change ∑ k, ‖Function.extend g x 0 k‖ ^ p.toReal = ∑ i, ‖x i‖ ^ p.toReal
      refine (Fintype.sum_of_injective g hg (fun i => ‖x i‖ ^ p.toReal) _ (fun k hk => ?_)
        fun i => ?_).symm
      · rw [Function.extend_apply' _ _ _ (by simpa using hk), Pi.zero_apply, norm_zero,
          Real.zero_rpow hp0.ne']
      · rw [hg.extend_apply]
  · simpa [Function.extend_comp hg] using norm_toLp_comp_le p hg (Function.extend g x 0)

end Reindex

/-! ### Hölder's inequality -/

section Holder

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem norm_dotProduct_le_sum (x y : ι → 𝕜) :
    ‖x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ :=
  (norm_sum_le _ _).trans_eq (by simp only [norm_mul])

/-- Hölder's inequality for the exponents $(\infty, 1)$: $|x \cdot y| \le \|x\|_\infty \|y\|_1$. -/
private theorem norm_dotProduct_le_top_one (x y : ι → 𝕜) :
    ‖x ⬝ᵥ y‖ ≤ ‖toLp ∞ x‖ * ‖toLp 1 y‖ := by
  refine (norm_dotProduct_le_sum x y).trans ?_
  rw [norm_eq_sum (p := 1) (by simp)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one, Finset.mul_sum]
  gcongr with i
  exact norm_apply_le (toLp ∞ x) i

/-- **Hölder's inequality** on $\mathbb{K}^\iota$ ([golub2013matrix], (2.2.2)). Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $\iota$ be finite, and let $p, q \in [1, \infty]$ be conjugate
exponents, $1/p + 1/q = 1$, the pairs $(1, \infty)$ and $(\infty, 1)$ included. For
$x, y \in \mathbb{K}^\iota$,
$$|x \cdot y| \le \|x\|_p \|y\|_q,$$
where $x \cdot y = \sum_i x_i y_i$ is the dot product without conjugation.

For finite exponents the proof applies `Real.inner_le_Lp_mul_Lq_of_nonneg` to the moduli of the
coordinates. -/
theorem norm_dotProduct_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (x y : ι → 𝕜) : ‖x ⬝ᵥ y‖ ≤ ‖toLp p x‖ * ‖toLp q y‖ := by
  obtain rfl | hp := eq_or_ne p ∞
  · obtain rfl := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).mp rfl
    exact norm_dotProduct_le_top_one x y
  obtain rfl | hq := eq_or_ne q ∞
  · obtain rfl := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
    rw [dotProduct_comm, mul_comm]
    exact norm_dotProduct_le_top_one y x
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  refine (norm_dotProduct_le_sum x y).trans ?_
  rw [norm_eq_sum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp),
    norm_eq_sum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q p) hq)]
  simpa only [toLp_apply] using Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq
    (fun i _ => norm_nonneg (x i)) (fun i _ => norm_nonneg (y i))

end Holder

end PiLp

/-- For $u \in \mathbb{K}^{m_1}$ and $w \in \mathbb{K}^{m_2}$, the vector $(u, w)$ on the disjoint
union $m_1 \sqcup m_2$ has the squared Euclidean norm $\|(u, w)\|^2 = \|u\|^2 + \|w\|^2$. -/
theorem EuclideanSpace.norm_toLp_sumElim_sq {𝕜 : Type*} [RCLike 𝕜] {m₁ m₂ : Type*} [Fintype m₁]
    [Fintype m₂] (u : m₁ → 𝕜) (w : m₂ → 𝕜) :
    ‖(toLp 2 (Sum.elim u w) : EuclideanSpace 𝕜 (m₁ ⊕ m₂))‖ ^ 2
      = ‖(toLp 2 u : EuclideanSpace 𝕜 m₁)‖ ^ 2 + ‖(toLp 2 w : EuclideanSpace 𝕜 m₂)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Let $v \in \mathbb{R}^n$ have Euclidean norm $\|v\| = 1$. Then some coordinate $v_i$ is nonzero.
-/
theorem EuclideanSpace.exists_apply_ne_zero_of_norm_eq_one {n : ℕ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) : ∃ i : Fin n, v i ≠ 0 := by
  by_contra hcon
  have : v = 0 := PiLp.ext fun i ↦ by_contra fun h ↦ hcon ⟨i, h⟩
  rw [this, norm_zero] at hv
  exact zero_ne_one hv

/-- Every $z \in \mathbb{R}^N$ is $z = \sum_k z_k e_k$, where $e_k$ are the standard basis vectors.
-/
theorem EuclideanSpace.eq_sum_single_smul {N : ℕ} (z : EuclideanSpace ℝ (Fin N)) :
    z = ∑ k, z k • EuclideanSpace.single k (1 : ℝ) := by
  have := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr z
  simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using this.symm

/-- A continuous linear functional $L$ on $\mathbb{R}^N$ satisfies $L(z) = \sum_k z_k L(e_k)$, where
$e_k$ are the standard basis vectors. -/
theorem ContinuousLinearMap.apply_eq_sum_single {N : ℕ} (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin N)) : L z = ∑ k, z k * L (EuclideanSpace.single k 1) := by
  conv_lhs => rw [EuclideanSpace.eq_sum_single_smul z, map_sum]
  simp only [map_smul, smul_eq_mul]

/-! ### The Euclidean norm as a dot product -/

namespace Matrix

/-- For $s \in \mathbb{R}^n$, the dot product $s^T s$ is the square of the Euclidean norm:
$$s^T s = \|s\|_2^2.$$

This connects the dot product `s ⬝ᵥ s` with the norm of `EuclideanSpace`. -/
theorem dotProduct_self_eq_norm_sq {n : Type*} [Fintype n] (s : n → ℝ) :
    s ⬝ᵥ s = ‖toLp 2 s‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]

/-- For $x \in \mathbb{K}^n$ with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, $x^H x = \|x\|_2^2$, as
an element of $\mathbb{K}$. -/
theorem star_dotProduct_self {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] (x : n → 𝕜) :
    star x ⬝ᵥ x = ((‖(toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ^ 2 := by
  rw [← inner_self_eq_norm_sq_to_K (𝕜 := 𝕜), EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

end Matrix
