/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Analysis.Calculus.SegmentAverage

/-!
# Roots of multiplicity $m$ of a real function

Let $f \colon \mathbb{R} \to \mathbb{R}$. A point $\alpha$ is a **root of multiplicity** $m$ of $f$
if $f(\alpha) = f'(\alpha) = \dots = f^{(m-1)}(\alpha) = 0$ and $f^{(m)}(\alpha) \neq 0$. The
central result is the **Taylor factorization** at such a root: if $f$ is $C^{m+n}$ at $\alpha$, then
$f(x) = (x - \alpha)^m h(x)$ for all $x$, where $h$ is $C^n$ at $\alpha$ and
$h(\alpha) = f^{(m)}(\alpha) / m!$. The rootfinding chapters of [quarteroni2000numerical] work with
this notion for functions that are only $C^m$.

The facts about multiple roots follow from this factorization. As $x \to \alpha$, the error and the
residual satisfy
$$\frac{|x - \alpha|}{|f(x)|^{1/m}} \to \left( \frac{m!}{|f^{(m)}(\alpha)|} \right)^{1/m}.$$
This limit is behind the conditioning estimates (6.4)–(6.7) of [quarteroni2000numerical], §6.1, and
the residual stopping test of §6.5. The factorization also gives the linear convergence of Newton's
method with factor $1 - 1/m$ in `Numlib.Nonlinear.ScalarNewton`, and the agreement with the
multiplicity of a polynomial root.

The factor $h$ is the $m$-fold iterate of the difference quotient $\operatorname{dslope}$, so the
factorization holds everywhere. Its regularity reduces to **Hadamard's lemma** in one variable: if
$f \colon \mathbb{K} \to \mathbb{K}$, with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, is $C^{n+1}$
at $a$, then the difference quotient $\operatorname{dslope} f a$ is $C^n$ at $a$, and its $n$-th
derivative at $a$ is $f^{(n+1)}(a) / (n + 1)$. On a ball about $a$, the difference quotient is the
segment average $b \mapsto \int_0^1 f'(a + t(b - a)) \, dt$ of
`Numlib.Analysis.Calculus.SegmentAverage`, whose $k$-th derivative is
$\int_0^1 t^k f^{(k+1)}(a + t(b - a)) \, dt$.

## Main definitions

* `IsRootOfMultiplicity`: $\alpha$ is a root of multiplicity $m$ of $f$.

## Main results

* `ContDiffAt.dslope_same`: Hadamard's lemma, the difference quotient of a $C^{n+1}$ function is
  $C^n$.
* `IsRootOfMultiplicity.exists_eq_pow_mul`: the Taylor factorization $f(x) = (x - \alpha)^m h(x)$.
* `IsRootOfMultiplicity.exists_eq_pow_mul_deriv`: the factorization with a $C^1$ factor and its
  derivative at $\alpha$.
* `IsRootOfMultiplicity.tendsto_abs_sub_div_abs_rpow`: the limit of $|x - \alpha| / |f(x)|^{1/m}$.
* `IsRootOfMultiplicity.eventually_abs_sub_le_mul_abs_rpow`: the residual bound
  $|x - \alpha| \le c |f(x)|^{1/m}$ near $\alpha$.
* `Polynomial.isRootOfMultiplicity_eval_iff`: for a nonzero polynomial, the multiplicity agrees with
  `Polynomial.rootMultiplicity`.

## Implementation notes

* Mathlib has the multiplicity of a root for polynomials (`Polynomial.rootMultiplicity`) and the
  order of a zero for analytic functions (`analyticOrderAt`), but not for functions that are only
  $C^m$.
* Derivatives are Mathlib's `iteratedDeriv`. The predicate `IsRootOfMultiplicity` does not include
  smoothness. The theorems that need the derivatives to be meaningful, such as the factorization,
  the limit and the residual bound, assume `ContDiffAt ℝ n f α` with $n \ge m$. The elementary
  consequences of the definition, such as `IsRootOfMultiplicity.eq_zero` and
  `IsRootOfMultiplicity.deriv`, do not.
* The factor $h$ is `(Function.swap dslope α)^[m] f`. The factorization identity is Mathlib's
  `pow_sub_smul_iterate_dslope_of_zero`.
* Hadamard's lemma and the pointwise $C^1$ facts `ContDiffAt.eventually_hasDerivAt` and
  `ContDiffAt.continuousAt_deriv` are general results with no numerical content. Their natural place
  is beside `Mathlib.Analysis.Calculus.DSlope`.
-/

open Filter Topology Set Nat
open scoped Interval

section Pointwise

/-- **A $C^N$ function is $N$ times differentiable on a ball.** Let
$f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^N$ at $a$. Then there is $\delta > 0$ such
that on the ball $B(a, \delta)$, for every $j < N$, the iterated derivative $f^{(j)}$ has the
derivative $f^{(j+1)}(x)$ at every $x$, and $f^{(N)}$ is continuous. -/
theorem ContDiffAt.exists_ball_hasDerivAt_iteratedDeriv {f : ℝ → ℝ} {a : ℝ} {N : ℕ}
    (hf : ContDiffAt ℝ N f a) :
    ∃ δ > 0, (∀ j < N, ∀ x ∈ Metric.ball a δ,
        HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x) ∧
      ContinuousOn (iteratedDeriv N f) (Metric.ball a δ) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  exact ⟨r, hr, fun j hj x hx =>
    (hfu.mono hru).hasDerivAt_iteratedDeriv_of_isOpen Metric.isOpen_ball hj hx,
    (hfu.mono hru).continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball le_rfl⟩

/-- Let $h \colon \mathbb{R} \to \mathbb{R}$ be of class $C^1$ at $a$. Then $h$ has the derivative
$h'(x)$ at every $x$ in a neighbourhood of $a$, where $h'$ is `deriv h`. -/
theorem ContDiffAt.eventually_hasDerivAt {h : ℝ → ℝ} {a : ℝ} (hh : ContDiffAt ℝ 1 h a) :
    ∀ᶠ x in 𝓝 a, HasDerivAt h (deriv h x) x := by
  obtain ⟨u, hu, hhu⟩ := hh.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  filter_upwards [Metric.ball_mem_nhds a hr] with x hx
  have := (hhu.mono hru).hasDerivAt_iteratedDeriv_of_isOpen (N := 1) Metric.isOpen_ball
    (j := 0) one_pos hx
  simpa using this

/-- Let $h \colon \mathbb{R} \to \mathbb{R}$ be of class $C^1$ at $a$. Then the derivative $h'$ is
continuous at $a$. -/
theorem ContDiffAt.continuousAt_deriv {h : ℝ → ℝ} {a : ℝ} (hh : ContDiffAt ℝ 1 h a) :
    ContinuousAt (deriv h) a := by
  obtain ⟨u, hu, hhu⟩ := hh.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  have := ((hhu.mono hru).continuousOn_iteratedDeriv_of_isOpen (N := 1) Metric.isOpen_ball
    (j := 1) le_rfl).continuousAt (Metric.ball_mem_nhds a hr)
  simpa using this

/-- Let $f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^2$ at $\alpha$. Then $f'$ has the
derivative $f''(\alpha)$ at $\alpha$. -/
theorem hasDerivAt_deriv_of_contDiffAt_two {f : ℝ → ℝ} {α : ℝ} (hf : ContDiffAt ℝ 2 f α) :
    HasDerivAt (deriv f) (iteratedDeriv 2 f α) α := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  have hfb : ContDiffOn ℝ (2 : ℕ) f (Metric.ball α r) := by exact_mod_cast hfu.mono hru
  have := hfb.hasDerivAt_iteratedDeriv_of_isOpen Metric.isOpen_ball (j := 1) one_lt_two
    (Metric.mem_ball_self hr)
  simpa using this

end Pointwise

section Hadamard

variable {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {a : 𝕜}

/-- Let $U \subseteq \mathbb{K}$ be open and convex, let $N \ge 1$, let
$f \colon \mathbb{K} \to \mathbb{K}$ be of class $C^N$ on $U$, and let $a \in U$. Then on $U$
the difference quotient $\operatorname{dslope} f a$ is the segment average
$$b \mapsto \int_0^1 f'(a + t(b - a)) \, dt.$$
-/
theorem eqOn_dslope_integral_deriv_comp_segment {U : Set 𝕜} (hU : IsOpen U)
    (hUc : Convex ℝ U) {N : ℕ} (hN : 1 ≤ N) (hf : ContDiffOn 𝕜 N f U) (ha : a ∈ U) :
    EqOn (dslope f a) (fun b => ∫ t in (0 : ℝ)..1, deriv f (a + t • (b - a))) U := by
  intro b hb
  have hf1 : ContDiffOn 𝕜 (1 : ℕ) f U := hf.of_le (by exact_mod_cast hN)
  have hf' : ∀ x ∈ U, HasDerivAt f (deriv f x) x := fun x hx => by
    simpa using hf1.hasDerivAt_iteratedDeriv_of_isOpen hU (j := 0) one_pos hx
  have hf'c : ContinuousOn (deriv f) U := by
    simpa using hf1.continuousOn_iteratedDeriv_of_isOpen hU le_rfl
  rcases eq_or_ne b a with rfl | hba
  · simp
  · rw [dslope_of_ne _ hba, slope_def_field, eq_add_mul_integral_comp_segment hUc hf' hf'c ha hb,
      add_sub_cancel_left, mul_div_cancel_left₀ _ (sub_ne_zero.2 hba)]

/-- On a ball about $a$ where $f$ is $C^{n+1}$, the difference quotient $\operatorname{dslope} f a$
is $C^n$ at $a$ and its $n$-th derivative at $a$ is $f^{(n+1)}(a) / (n + 1)$. -/
private theorem contDiffOn_dslope_ball {r : ℝ} (hr : 0 < r) {n : ℕ}
    (hf : ContDiffOn 𝕜 (n + 1 : ℕ) f (Metric.ball a r)) :
    ContDiffAt 𝕜 n (dslope f a) a ∧
      iteratedDeriv n (dslope f a) a = iteratedDeriv (n + 1) f a / (n + 1) := by
  have ha : a ∈ Metric.ball a r := Metric.mem_ball_self hr
  have hEq : dslope f a =ᶠ[𝓝 a] fun b => ∫ t in (0 : ℝ)..1, deriv f (a + t • (b - a)) :=
    (eqOn_dslope_integral_deriv_comp_segment Metric.isOpen_ball (convex_ball a r) (by omega) hf
      ha).eventuallyEq_of_mem (Metric.ball_mem_nhds a hr)
  refine ⟨?_, ?_⟩
  · have hg := contDiffOn_integral_deriv_comp_segment Metric.isOpen_ball (convex_ball a r)
      (n := n) (by exact_mod_cast hf) ha
    exact ((hg.contDiffAt (Metric.ball_mem_nhds a hr)).congr_of_eventuallyEq hEq).of_le
      (by exact_mod_cast le_rfl)
  · rw [hEq.iteratedDeriv_eq, iteratedDeriv_integral_deriv_comp_segment Metric.isOpen_ball
      (convex_ball a r) hf ha le_rfl ha]
    simp only [sub_self, smul_zero, add_zero]
    rw [intervalIntegral.integral_smul_const, integral_pow, one_pow,
      zero_pow (Nat.succ_ne_zero n), sub_zero, RCLike.real_smul_eq_coe_mul]
    push_cast
    ring

/-- **Hadamard's lemma** in one variable. Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$f \colon \mathbb{K} \to \mathbb{K}$ be of class $C^{n+1}$ at $a$. Then the difference quotient
$\operatorname{dslope} f a$ is of class $C^n$ at $a$.

The difference quotient $\operatorname{dslope} f a$ is Mathlib's `dslope f a`. Its value at
$x \neq a$ is $(f(x) - f(a)) / (x - a)$, and its value at $a$ is $f'(a)$. -/
theorem ContDiffAt.dslope_same {n : ℕ} (hf : ContDiffAt 𝕜 (n + 1 : ℕ) f a) :
    ContDiffAt 𝕜 n (dslope f a) a := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  exact (contDiffOn_dslope_ball hr (hfu.mono hru)).1

/-- Let $f \colon \mathbb{K} \to \mathbb{K}$ be of class $C^{n+1}$ at $a$. Then the $n$-th
derivative of $\operatorname{dslope} f a$ at $a$ is $f^{(n+1)}(a) / (n + 1)$. -/
theorem iteratedDeriv_dslope_same {n : ℕ} (hf : ContDiffAt 𝕜 (n + 1 : ℕ) f a) :
    iteratedDeriv n (dslope f a) a = iteratedDeriv (n + 1) f a / (n + 1) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  exact (contDiffOn_dslope_ball hr (hfu.mono hru)).2

/-- Let $f \colon \mathbb{K} \to \mathbb{K}$ be of class $C^{m+n}$ at $a$. Then the $m$-fold iterate
of the difference quotient at $a$, $h = \operatorname{dslope}(\cdots \operatorname{dslope}(f, a)
\cdots, a)$, is of class $C^n$ at $a$. -/
theorem ContDiffAt.iterate_dslope_same {m n : ℕ} (hf : ContDiffAt 𝕜 (m + n : ℕ) f a) :
    ContDiffAt 𝕜 n ((Function.swap dslope a)^[m] f) a := by
  induction m generalizing f with
  | zero => simpa using hf
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (f := dslope f a)
      (ContDiffAt.dslope_same (n := m + n) (by rwa [show m + n + 1 = m + 1 + n by omega]))

/-- Let $f \colon \mathbb{K} \to \mathbb{K}$ be of class $C^{m+n}$ at $a$, and let $h$ be the
$m$-fold iterate of the difference quotient at $a$. Then
$$h^{(n)}(a) = \frac{n!}{(m + n)!} f^{(m+n)}(a).$$
-/
theorem iteratedDeriv_iterate_dslope_same {m n : ℕ} (hf : ContDiffAt 𝕜 (m + n : ℕ) f a) :
    iteratedDeriv n ((Function.swap dslope a)^[m] f) a =
      (n ! : 𝕜) / (m + n)! * iteratedDeriv (m + n) f a := by
  induction m generalizing f with
  | zero => simp [Nat.factorial_ne_zero]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hf' : ContDiffAt 𝕜 (m + n + 1 : ℕ) f a := by
      rwa [show m + n + 1 = m + 1 + n by omega]
    rw [ih (f := dslope f a) (hf'.dslope_same), iteratedDeriv_dslope_same hf',
      show m + 1 + n = m + n + 1 by omega, Nat.factorial_succ]
    push_cast
    field_simp

/-- Let $f \colon \mathbb{K} \to \mathbb{K}$ be of class $C^m$ at $a$, and let $h$ be the $m$-fold
iterate of the difference quotient at $a$. Then $h(a) = f^{(m)}(a) / m!$. -/
theorem iterate_dslope_same_apply {m : ℕ} (hf : ContDiffAt 𝕜 m f a) :
    (Function.swap dslope a)^[m] f a = iteratedDeriv m f a / m ! := by
  have := iteratedDeriv_iterate_dslope_same (m := m) (n := 0) (by simpa using hf)
  simpa [div_eq_inv_mul] using this

/-- **Hadamard's lemma, global form.** Let $g \colon \mathbb{K} \to \mathbb{K}$ be of class
$C^{m+1}$, and let $c \in \mathbb{K}$. Then the difference quotient $\operatorname{dslope} g c$
is of class $C^m$.

At $c$ this is `ContDiffAt.dslope_same`. At other points $\operatorname{dslope} g c$ is the
quotient $(g(y) - g(c)) / (y - c)$. -/
theorem _root_.ContDiff.dslope {g : 𝕜 → 𝕜} {m : ℕ}
    (hg : ContDiff 𝕜 ((m + 1 : ℕ) : WithTop ℕ∞) g) (c : 𝕜) : ContDiff 𝕜 m (dslope g c) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  rcases eq_or_ne x c with rfl | hxc
  · exact hg.contDiffAt.dslope_same
  · refine ContDiffAt.congr_of_eventuallyEq ?_ (dslope_eventuallyEq_slope_of_ne g hxc)
    rw [slope_fun_def_field]
    have hg' : ContDiffAt 𝕜 m g x := hg.contDiffAt.of_le (by exact_mod_cast Nat.le_succ m)
    exact (hg'.sub contDiffAt_const).div (contDiffAt_id.sub contDiffAt_const)
      (sub_ne_zero.2 hxc)

end Hadamard

section Multiplicity

variable {f : ℝ → ℝ} {α : ℝ} {m : ℕ}

/-- Let $f \colon \mathbb{R} \to \mathbb{R}$, $\alpha \in \mathbb{R}$ and $m \in \mathbb{N}$. The
point $\alpha$ is a **root of multiplicity** $m$ of $f$ if
$$f^{(i)}(\alpha) = 0 \text{ for all } i < m \quad \text{and} \quad f^{(m)}(\alpha) \neq 0.$$

This is the notion of [quarteroni2000numerical], §6.1, and of [isaacson1994analysis], §3.2.
Multiplicity $1$ is a simple root: $f(\alpha) = 0$ and $f'(\alpha) \neq 0$. Multiplicity $0$
means $f(\alpha) \neq 0$. The derivatives are `iteratedDeriv`, which are $0$ where $f$ is not
differentiable. Therefore the theorems that need the derivatives to be meaningful also assume
that $f$ is $C^n$ at $\alpha$ for some $n \ge m$ (`ContDiffAt ℝ n f α`), as Mathlib does with
`iteratedDeriv`. -/
def IsRootOfMultiplicity (f : ℝ → ℝ) (α : ℝ) (m : ℕ) : Prop :=
  (∀ i < m, iteratedDeriv i f α = 0) ∧ iteratedDeriv m f α ≠ 0

/-- A root of multiplicity $m \ge 1$ of $f$ is a root: $f(\alpha) = 0$. -/
theorem IsRootOfMultiplicity.eq_zero (hα : IsRootOfMultiplicity f α m) (hm : 1 ≤ m) :
    f α = 0 := by
  simpa using hα.1 0 hm

/-- The point $\alpha$ is a root of multiplicity $1$ of $f$ if and only if $f(\alpha) = 0$ and
$f'(\alpha) \neq 0$. -/
theorem isRootOfMultiplicity_one_iff :
    IsRootOfMultiplicity f α 1 ↔ f α = 0 ∧ deriv f α ≠ 0 := by
  simp [IsRootOfMultiplicity]

/-- If $\alpha$ is a root of multiplicity $m + 1$ of $f$, then $\alpha$ is a root of multiplicity
$m$ of $f'$. -/
theorem IsRootOfMultiplicity.deriv (hα : IsRootOfMultiplicity f α (m + 1)) :
    IsRootOfMultiplicity (deriv f) α m := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [← iteratedDeriv_succ']
    exact hα.1 (i + 1) (by omega)
  · rw [← iteratedDeriv_succ']
    exact hα.2

/-- **Taylor factorization at a multiple root.** Let $f \colon \mathbb{R} \to \mathbb{R}$ be of
class $C^{m+n}$ at $\alpha$, and let $\alpha$ be a root of multiplicity $m$ of $f$. Then there
is $h \colon \mathbb{R} \to \mathbb{R}$, of class $C^n$ at $\alpha$, with
$h(\alpha) = f^{(m)}(\alpha) / m!$, such that
$$f(x) = (x - \alpha)^m h(x) \quad \text{for all } x \in \mathbb{R}.$$

In particular $h(\alpha) \neq 0$. The factor $h$ is the $m$-fold iterate of the difference
quotient at $\alpha$, which is $f(x) / (x - \alpha)^m$ for $x \neq \alpha$. Its regularity is
Hadamard's lemma `ContDiffAt.dslope_same`, applied $m$ times. Exercise 6.2 of
[quarteroni2000numerical] gives this factorization as its hint. -/
theorem IsRootOfMultiplicity.exists_eq_pow_mul {n : ℕ} (hf : ContDiffAt ℝ (m + n : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    ∃ h : ℝ → ℝ, ContDiffAt ℝ n h α ∧ h α = iteratedDeriv m f α / m ! ∧
      ∀ x, f x = (x - α) ^ m * h x := by
  refine ⟨(Function.swap dslope α)^[m] f, hf.iterate_dslope_same,
    iterate_dslope_same_apply (hf.of_le (by exact_mod_cast Nat.le_add_right m n)), fun x => ?_⟩
  rw [← smul_eq_mul, pow_sub_smul_iterate_dslope_of_zero m fun k hk => ?_]
  rw [iterate_dslope_same_apply (hf.of_le (by exact_mod_cast (by omega : k ≤ m + n))),
    hα.1 k hk, zero_div]

/-- **Taylor factorization with the derivative of the factor.** Let
$f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^{m+1}$ at $\alpha$, and let $\alpha$ be a
root of multiplicity $m$ of $f$. Then there is $h \colon \mathbb{R} \to \mathbb{R}$, of class
$C^1$ at $\alpha$, with
$$h(\alpha) = \frac{f^{(m)}(\alpha)}{m!}, \qquad h'(\alpha) = \frac{f^{(m+1)}(\alpha)}{(m +
  1)!},$$
such that $f(x) = (x - \alpha)^m h(x)$ for all $x \in \mathbb{R}$.

The analysis of Newton's method at a multiple root in `Numlib.Nonlinear.ScalarNewton` uses this
form. -/
theorem IsRootOfMultiplicity.exists_eq_pow_mul_deriv (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    ∃ h : ℝ → ℝ, ContDiffAt ℝ 1 h α ∧ h α = iteratedDeriv m f α / m ! ∧
      _root_.deriv h α = iteratedDeriv (m + 1) f α / (m + 1)! ∧ ∀ x, f x = (x - α) ^ m * h x := by
  refine ⟨(Function.swap dslope α)^[m] f, hf.iterate_dslope_same,
    iterate_dslope_same_apply (hf.of_le (by exact_mod_cast Nat.le_succ m)), ?_, fun x => ?_⟩
  · rw [← iteratedDeriv_one, iteratedDeriv_iterate_dslope_same hf, Nat.factorial_one,
      Nat.cast_one, one_div, inv_mul_eq_div]
  · rw [← smul_eq_mul, pow_sub_smul_iterate_dslope_of_zero m fun k hk => ?_]
    rw [iterate_dslope_same_apply (hf.of_le (by exact_mod_cast (by omega : k ≤ m + 1))),
      hα.1 k hk, zero_div]

/-- If $\alpha$ is a root of multiplicity $m$ of $f$, then $f^{(m)}(\alpha) / m! \neq 0$. -/
theorem IsRootOfMultiplicity.iteratedDeriv_div_factorial_ne_zero
    (hα : IsRootOfMultiplicity f α m) : iteratedDeriv m f α / m ! ≠ 0 :=
  div_ne_zero hα.2 (by exact_mod_cast Nat.factorial_ne_zero m)

/-- Let $f$ be of class $C^m$ at $\alpha$, and let $\alpha$ be a root of multiplicity $m$ of $f$,
for any $m$, including $m = 0$. Then $f(x) \neq 0$ for all $x \neq \alpha$ in a neighbourhood of
$\alpha$. -/
theorem IsRootOfMultiplicity.eventually_ne_zero (hf : ContDiffAt ℝ m f α)
    (hα : IsRootOfMultiplicity f α m) : ∀ᶠ x in 𝓝[≠] α, f x ≠ 0 := by
  obtain ⟨h, hh, hhα, hfh⟩ := hα.exists_eq_pow_mul (n := 0) (by simpa using hf)
  have hne : ∀ᶠ x in 𝓝 α, h x ≠ 0 :=
    hh.continuousAt.eventually_ne (hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero)
  filter_upwards [nhdsWithin_le_nhds hne, self_mem_nhdsWithin] with x hx hxα
  rw [hfh x]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hxα)) hx

/-- **Error versus residual at a root of multiplicity $m$.** Let $m \ge 1$, let
$f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^m$ at $\alpha$, and let $\alpha$ be a root
of multiplicity $m$ of $f$. Then as $x \to \alpha$ with $x \neq \alpha$,
$$\frac{|x - \alpha|}{|f(x)|^{1/m}} \to \left( \frac{m!}{|f^{(m)}(\alpha)|} \right)^{1/m}.$$

This is the rigorous content of (6.4) and (6.6) of [quarteroni2000numerical]. For $m = 1$ it is
$|x - \alpha| / |f(x)| \to 1 / |f'(\alpha)|$, the statement behind
$K_{abs} \simeq 1 / |f'(\alpha)|$ in (6.3) and the residual stopping test of §6.5. The power
$1/m$ is a real power. -/
theorem IsRootOfMultiplicity.tendsto_abs_sub_div_abs_rpow (hm : 1 ≤ m) (hf : ContDiffAt ℝ m f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => |x - α| / |f x| ^ (1 / (m : ℝ))) (𝓝[≠] α)
      (𝓝 ((m ! / |iteratedDeriv m f α|) ^ (1 / (m : ℝ)))) := by
  obtain ⟨h, hh, hhα, hfh⟩ := hα.exists_eq_pow_mul (n := 0) (by simpa using hf)
  have hc : (1 / |h α|) = m ! / |iteratedDeriv m f α| := by
    rw [hhα, abs_div, Nat.abs_cast, one_div_div]
  rw [← hc]
  have hlim : Tendsto (fun x => (1 / |h x|) ^ (1 / (m : ℝ))) (𝓝[≠] α)
      (𝓝 ((1 / |h α|) ^ (1 / (m : ℝ)))) := by
    refine Tendsto.rpow_const ?_ (Or.inr (by positivity))
    exact (tendsto_const_nhds.div (hh.continuousAt.abs.tendsto.mono_left nhdsWithin_le_nhds)
      (abs_ne_zero.2 (hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero)))
  refine hlim.congr' (eventually_mem_nhdsWithin.mono fun x hx => ?_)
  have hxα : |x - α| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 hx)
  change _ = |x - α| / |f x| ^ (1 / (m : ℝ))
  rw [hfh x, abs_mul, abs_pow, Real.mul_rpow (pow_nonneg (abs_nonneg _) _) (abs_nonneg _),
    one_div (m : ℝ), Real.pow_rpow_inv_natCast (abs_nonneg _) (by omega),
    div_mul_cancel_left₀ hxα, one_div, Real.inv_rpow (abs_nonneg _)]

/-- **The residual bound.** Let $m \ge 1$, let $f \colon \mathbb{R} \to \mathbb{R}$ be of class
$C^m$ at $\alpha$, and let $\alpha$ be a root of multiplicity $m$ of $f$. Let
$c > (m! / |f^{(m)}(\alpha)|)^{1/m}$. Then for all $x$ in a neighbourhood of $\alpha$,
$$|x - \alpha| \le c \, |f(x)|^{1/m}.$$

This is (6.5) and (6.6) of [quarteroni2000numerical] as an inequality: the source's $\lesssim$
is read in exactly this way. For $m = 1$: for every $c > 1 / |f'(\alpha)|$,
$|x - \alpha| \le c |f(x)|$ near $\alpha$. -/
theorem IsRootOfMultiplicity.eventually_abs_sub_le_mul_abs_rpow (hm : 1 ≤ m)
    (hf : ContDiffAt ℝ m f α) (hα : IsRootOfMultiplicity f α m) {c : ℝ}
    (hc : (m ! / |iteratedDeriv m f α|) ^ (1 / (m : ℝ)) < c) :
    ∀ᶠ x in 𝓝 α, |x - α| ≤ c * |f x| ^ (1 / (m : ℝ)) := by
  have h1 : ∀ᶠ x in 𝓝[≠] α, |x - α| ≤ c * |f x| ^ (1 / (m : ℝ)) := by
    filter_upwards [(hα.tendsto_abs_sub_div_abs_rpow hm hf).eventually_lt_const hc,
      hα.eventually_ne_zero hf] with x hx hfx
    have hpos : 0 < |f x| ^ (1 / (m : ℝ)) := Real.rpow_pos_of_pos (abs_pos.2 hfx) _
    exact (div_le_iff₀ hpos).1 hx.le
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with x hx
  by_cases hxα : x = α
  · subst hxα
    have hm0 : ((m : ℝ)⁻¹) ≠ 0 := by
      have : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      positivity
    simp [hα.eq_zero hm, Real.zero_rpow hm0]
  · exact hx hxα

end Multiplicity

namespace Polynomial

/-- For every real polynomial $P$ and every $N \in \mathbb{N} \cup \{\infty, \omega\}$, the function
$t \mapsto P(t)$ is of class $C^N$ on $\mathbb{R}$. -/
theorem contDiff_eval (P : ℝ[X]) (N : WithTop ℕ∞) :
    ContDiff ℝ N fun t : ℝ => P.eval t := by
  simpa only [coe_aeval_eq_eval] using P.contDiff_aeval (𝕜 := ℝ) N

/-- For every real polynomial $p$, every $k \in \mathbb{N} \cup \{\infty, \omega\}$ and every set
$s \subseteq \mathbb{R}$, the function $x \mapsto p(x)$ is of class $C^k$ on $s$. -/
theorem contDiffOn_eval (p : ℝ[X]) (k : WithTop ℕ∞) (s : Set ℝ) :
    ContDiffOn ℝ k (fun x => p.eval x) s :=
  (by simpa [Polynomial.coe_aeval_eq_eval] using p.contDiff_aeval (𝕜 := ℝ) k :
    ContDiff ℝ k fun x => p.eval x).contDiffOn

/-- Let $p$ be a nonzero real polynomial, let $\alpha \in \mathbb{R}$ and let $m \in \mathbb{N}$.
Then $\alpha$ is a root of multiplicity $m$ of the function $x \mapsto p(x)$ if and only if
`Polynomial.rootMultiplicity` of $p$ at $\alpha$ is $m$.

This lets (6.7) of [quarteroni2000numerical] speak of the multiplicity of a polynomial root in
the vocabulary of Mathlib. -/
theorem isRootOfMultiplicity_eval_iff {p : ℝ[X]} (hp : p ≠ 0) {α : ℝ} {m : ℕ} :
    IsRootOfMultiplicity (fun x => p.eval x) α m ↔ p.rootMultiplicity α = m := by
  simp only [IsRootOfMultiplicity, iteratedDeriv_eval]
  have hlt : ∀ n, n < p.rootMultiplicity α ↔ ∀ i ≤ n, (derivative^[i] p).eval α = 0 :=
    fun n => lt_rootMultiplicity_iff_isRoot_iterate_derivative hp
  constructor
  · rintro ⟨hz, hnz⟩
    refine le_antisymm ?_ ?_
    · by_contra hlt'
      exact hnz ((hlt m).1 (lt_of_not_ge hlt') m le_rfl)
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact Nat.zero_le _
      · have := (hlt (m - 1)).2 (fun i hi => hz i (by omega))
        omega
  · intro hm
    refine ⟨fun i hi => (hlt i).1 (hm ▸ hi) i le_rfl, ?_⟩
    rw [← hm, eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _)
      (eval_divByMonic_pow_rootMultiplicity_ne_zero α hp)

end Polynomial
