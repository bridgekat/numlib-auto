/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.RootMultiplicity
import Numlib.Nonlinear.Newton
import Numlib.Nonlinear.Order

/-!
# Newton's method for a real function of one real variable

For $f, f' \colon \mathbb{R} \to \mathbb{R}$, the scalar Newton step is
$\varphi_{\mathrm{Newt}}(x) = x - f(x)/f'(x)$, where $f'$ is usually the derivative of $f$
([quarteroni2000numerical], §6.2.2, §6.3.1, §6.6.2 and Exercise 6.2; [kress1998numerical], §6.2;
[han2009theoretical], §5.4). It is the Banach-space step `Newton.step` of `Numlib.Nonlinear.Newton`
for $E = \mathbb{R}$, so the local quadratic convergence theorem and the Kantorovich theorem apply.
This module proves what the scalar setting adds. At a simple root $\alpha$,
$\varphi_{\mathrm{Newt}}'(\alpha) = 0$ and $\varphi_{\mathrm{Newt}}''(\alpha) =
f''(\alpha)/f'(\alpha)$, and the method has order $2$ with the classical constant
$f''(\alpha)/(2 f'(\alpha))$. At a root of multiplicity $m$ the method is only linear, with factor
$1 - 1/m$ ((6.22) of [quarteroni2000numerical]). There are two repairs: the modified Newton method
$x - m f(x)/f'(x)$, which is quadratic again when $m$ is known (Exercise 6.2), and the adaptive
Newton method, which estimates $m$ from the increment ratios ((6.40)). Finally, for a decreasing
concave function started to the right of its root, the iterates decrease monotonically to the root;
this is the argument behind (4.7.10) of [golub2013matrix], the smallest eigenvalue of a Toeplitz
matrix.

Multiplicity is `IsRootOfMultiplicity f α m` of `Numlib.Analysis.Calculus.RootMultiplicity`:
$f^{(i)}(\alpha) = 0$ for $i < m$ and $f^{(m)}(\alpha) \neq 0$.

## Main definitions

* `Newton.scalarStep`: the scalar Newton step $x - f(x)/f'(x)$.
* `Newton.modifiedScalarStep`: the modified Newton step $x - m f(x)/f'(x)$.
* `Newton.multiplicityEstimate`: the estimate $1/(1 - \lambda_k)$ of the multiplicity from the
  increment ratios $\lambda_k$.
* `Newton.adaptiveStep`: one step of the adaptive Newton method.

## Main results

* `Newton.scalarStep_eq_step`: the scalar step is the Banach-space Newton step.
* `Newton.hasDerivAt_scalarStep`: $\varphi_{\mathrm{Newt}}'(x) = f(x) f''(x) / f'(x)^2$.
* `Newton.tendsto_scalarStep_sub_div_sq`: at a simple root, $(\varphi_{\mathrm{Newt}}(x) -
  \alpha)/(x - \alpha)^2 \to f''(\alpha)/(2 f'(\alpha))$.
* `Newton.hasIterationOrder_scalarStep_two`: Newton's method has order $2$ at a simple root.
* `Newton.deriv2_scalarStep_root`: $\varphi_{\mathrm{Newt}}''(\alpha) = f''(\alpha)/f'(\alpha)$ at a
  simple root.
* `Newton.tendsto_scalarStep_sub_div_of_isRootOfMultiplicity`: at a root of multiplicity $m$, the
  error ratio tends to $1 - 1/m$.
* `Newton.tendsto_modifiedScalarStep_sub_div_sq`: the modified method is quadratic at a root of
  multiplicity $m$, with its constant.
* `Newton.hasIterationOrder_modifiedScalarStep_two`: the modified method has order $2$.
* `Newton.tendsto_multiplicityEstimate`: the multiplicity estimate converges to $m$.
* `Newton.tendsto_iterate_scalarStep_of_antitoneOn_deriv`: monotone convergence for a decreasing
  concave function.

## Proof outline

At a root of multiplicity $m$, write $f(x) = (x - \alpha)^m h(x)$ with $h$ of class $C^1$ at
$\alpha$, $h(\alpha) = f^{(m)}(\alpha)/m!$ and $h'(\alpha) = f^{(m+1)}(\alpha)/(m+1)!$. Then
$f'(x) = (x - \alpha)^{m-1} (m h(x) + (x - \alpha) h'(x))$ near $\alpha$. The error of the modified
step is $(x - \alpha)^2 h'(x) / (m h(x) + (x - \alpha) h'(x))$, and its ratio limit gives Newton's
constant for $m = 1$.

## Implementation notes

* `Newton.scalarStep f f' x` agrees with `Newton.step` for the derivative
  `f' x • ContinuousLinearMap.id ℝ ℝ` everywhere, also where $f'(x) = 0$, since
  `ContinuousLinearMap.inverse 0 = 0` and $a/0 = 0$. Where $f'(x) = 0$ the step returns $x$.
* The factorization of $f$ at a multiple root is `IsRootOfMultiplicity.exists_eq_pow_mul_deriv`, and
  the formula for $f'$ is `Newton.deriv_eq_of_eq_pow_mul`.
* The theorems on multiplicity and order take `deriv f` as the derivative $f'$.
-/

open Filter Topology Set

namespace Newton

section Defs

/-- One **scalar Newton step** for $f, f' \colon \mathbb{R} \to \mathbb{R}$:
$x \mapsto x - f(x)/f'(x)$. Where $f'(x) = 0$, the step returns $x$.

This is (6.16) of [quarteroni2000numerical], and the iteration function
$\varphi_{\mathrm{Newt}}$ of §6.3.1 is `Newton.scalarStep f f'` itself. The value where
$f'(x) = 0$ comes from the convention $a/0 = 0$. -/
noncomputable def scalarStep (f f' : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / f' x

/-- If $f(x) = 0$, then $x$ is a fixed point of the scalar Newton step, for every $f'$. -/
theorem scalarStep_apply_of_eq_zero (f f' : ℝ → ℝ) {x : ℝ} (hx : f x = 0) :
    scalarStep f f' x = x := by
  simp [scalarStep, hx]

/-- For all $f, f' \colon \mathbb{R} \to \mathbb{R}$ and every $x \in \mathbb{R}$, the scalar Newton
step at $x$ equals the Banach-space Newton step `Newton.step` at $x$ for the derivative
$y \mapsto f'(y) \cdot \mathrm{id}$.

This holds also where $f'(x) = 0$: both sides are then $x$, since `ContinuousLinearMap.inverse`
of $0$ is $0$. Through this identity every theorem of `Numlib.Nonlinear.Newton` (local quadratic
convergence, the Kantorovich theorem) applies to the scalar setting without restatement. -/
theorem scalarStep_eq_step (f f' : ℝ → ℝ) (x : ℝ) :
    scalarStep f f' x = step f (fun x => f' x • ContinuousLinearMap.id ℝ ℝ) x := by
  unfold scalarStep step
  congr 1
  by_cases h : f' x = 0
  · simp [h]
  · have hinv : (f' x • ContinuousLinearMap.id ℝ ℝ).inverse =
        (f' x)⁻¹ • ContinuousLinearMap.id ℝ ℝ :=
      ContinuousLinearMap.inverse_eq
        (by rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
          mul_inv_cancel₀ h, one_smul, ContinuousLinearMap.id_comp])
        (by rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
          inv_mul_cancel₀ h, one_smul, ContinuousLinearMap.id_comp])
    rw [hinv]
    simp [div_eq_inv_mul]

/-- **The derivative of the Newton iteration function.** Let $x \in \mathbb{R}$, let $f$ have
derivative $f'(x)$ at $x$, let $f'$ have derivative $f''$ at $x$, and let $f'(x) \neq 0$. Then
the Newton iteration function $\varphi_{\mathrm{Newt}}$ has derivative
$$\varphi_{\mathrm{Newt}}'(x) = \frac{f(x) f''}{f'(x)^2}$$
at $x$.

The proof is the quotient rule. At a simple root $\alpha$, $f(\alpha) = 0$ gives
$\varphi_{\mathrm{Newt}}'(\alpha) = 0$, the first display of §6.3.1 of
[quarteroni2000numerical]. -/
theorem hasDerivAt_scalarStep {f f' : ℝ → ℝ} {x f'' : ℝ} (hf : HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' f'' x) (hx : f' x ≠ 0) :
    HasDerivAt (scalarStep f f') (f x * f'' / (f' x) ^ 2) x := by
  refine ((hasDerivAt_id x).sub (hf.div hf' hx)).congr_deriv ?_
  field_simp
  ring

end Defs

section Multiple

variable {f : ℝ → ℝ} {α : ℝ} {m : ℕ}

/-! ### Multiple roots and the modified Newton method -/

/-- **The derivative near a multiple root.** Let $h \colon \mathbb{R} \to \mathbb{R}$ be $C^1$ at
$\alpha$, and let $f(x) = (x - \alpha)^{m+1} h(x)$ for all $x$. Then for all $x$ in a
neighbourhood of $\alpha$,
$$f'(x) = (x - \alpha)^m \bigl((m + 1) h(x) + (x - \alpha) h'(x)\bigr).$$
-/
theorem deriv_eq_of_eq_pow_mul {h : ℝ → ℝ} (hh : ContDiffAt ℝ 1 h α)
    (hfh : ∀ x, f x = (x - α) ^ (m + 1) * h x) :
    ∀ᶠ x in 𝓝 α, deriv f x =
      (x - α) ^ m * (((m + 1 : ℕ) : ℝ) * h x + (x - α) * deriv h x) := by
  filter_upwards [hh.eventually_hasDerivAt] with x hx
  have hpow : HasDerivAt (fun x => (x - α) ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * (x - α) ^ (m + 1 - 1) * 1) x :=
    ((hasDerivAt_id' x).sub_const α).pow (m + 1)
  have hd : HasDerivAt f _ x :=
    (hpow.mul hx).congr_of_eventuallyEq (Eventually.of_forall fun y => hfh y)
  rw [hd.deriv]
  simp only [Nat.add_sub_cancel, mul_one]
  ring

/-- Let $h \colon \mathbb{R} \to \mathbb{R}$ be $C^1$ at $\alpha$ and $c \in \mathbb{R}$. Then
$c h(x) + (x - \alpha) h'(x) \to c h(\alpha)$ as $x \to \alpha$. This expression is the
denominator of the error formulas at multiple roots. -/
theorem tendsto_const_mul_add_sub_mul_deriv {h : ℝ → ℝ} (hh : ContDiffAt ℝ 1 h α) (c : ℝ) :
    Tendsto (fun x => c * h x + (x - α) * deriv h x) (𝓝 α) (𝓝 (c * h α)) := by
  have := (hh.continuousAt.tendsto.const_mul c).add
    (((continuous_id.sub (continuous_const (y := α))).tendsto α).mul hh.continuousAt_deriv.tendsto)
  simpa using this

/-- **At a root of multiplicity $m$, Newton's method is linear with factor $1 - 1/m$.** Let
$m \ge 1$, let $f \colon \mathbb{R} \to \mathbb{R}$ be $C^{m+1}$ at $\alpha$, and let $\alpha$
be a root of $f$ of multiplicity $m$. Then, with $\varphi_{\mathrm{Newt}}$ the Newton step for
$f$ and its derivative,
$$\frac{\varphi_{\mathrm{Newt}}(x) - \alpha}{x - \alpha} \to 1 - \frac{1}{m} \qquad \text{as } x
  \to \alpha,\ x \neq \alpha.$$

This is (6.22) of [quarteroni2000numerical]. With $e = x - \alpha$, $f(x) = e^m h(x)$ and
$f'(x) = e^{m-1}(m h(x) + e h'(x))$, the ratio is $1 - h(x)/(m h(x) + e h'(x))$. The theorem
states a limit and not a derivative of $\varphi_{\mathrm{Newt}}$ at $\alpha$, because for
$m \ge 2$ the value $\varphi_{\mathrm{Newt}}(\alpha) = \alpha - 0/0 = \alpha$ comes from the
convention $a/0 = 0$. The limit is the form that (6.22), §6.6.2 and Exercise 6.2 use. -/
theorem tendsto_scalarStep_sub_div_of_isRootOfMultiplicity (hm : 1 ≤ m)
    (hf : ContDiffAt ℝ (m + 1 : ℕ) f α) (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (scalarStep f (deriv f) x - α) / (x - α)) (𝓝[≠] α) (𝓝 (1 - 1 / m)) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  obtain ⟨h, hh, hhα, -, hfh⟩ := hα.exists_eq_pow_mul_deriv hf
  have hc0 : h α ≠ 0 := hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero
  have hDen := tendsto_const_mul_add_sub_mul_deriv hh ((q + 1 : ℕ) : ℝ)
  have hDen0 : ((q + 1 : ℕ) : ℝ) * h α ≠ 0 := mul_ne_zero (by positivity) hc0
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (hh.continuousAt.tendsto.div hDen hDen0)).mono_left (nhdsWithin_le_nhds (s := {α}ᶜ))
  rw [div_mul_cancel_right₀ hc0, ← one_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (deriv_eq_of_eq_pow_mul hh hfh),
    nhdsWithin_le_nhds (hDen.eventually (isOpen_ne.mem_nhds hDen0))] with x hx hdx hden
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  simp only [Pi.div_apply]
  rw [scalarStep, hdx, hfh x, sub_right_comm, sub_div, div_self he]
  congr 1
  generalize x - α = e at he hden ⊢
  field_simp
  ring

/-- At a root of multiplicity $m \ge 2$, Newton's method has order $1$. Precisely: let $m \ge 2$,
let $f$ be $C^{m+1}$ at $\alpha$, and let $\alpha$ be a root of $f$ of multiplicity $m$. Then
the iteration of the Newton step for $f$ and its derivative has order $1$ at $\alpha$, because
the convergence factor $1 - 1/m$ is less than $1$. -/
theorem hasIterationOrder_scalarStep_one_of_isRootOfMultiplicity (hm : 2 ≤ m)
    (hf : ContDiffAt ℝ (m + 1 : ℕ) f α) (hα : IsRootOfMultiplicity f α m) :
    HasIterationOrder (scalarStep f (deriv f)) α 1 := by
  refine hasIterationOrder_one_of_tendsto_sub_div
    (scalarStep_apply_of_eq_zero f (deriv f) (hα.eq_zero (by omega))) ?_
    (tendsto_scalarStep_sub_div_of_isRootOfMultiplicity (by omega) hf hα)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (0 : ℝ) < 1 / m := by positivity
  have h2 : (1 : ℝ) / m ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- The **modified Newton step** for a root of known multiplicity $m$: $x \mapsto x - m f(x)/f'(x)$.
Where $f'(x) = 0$, the step returns $x$.

This is (6.23) of [quarteroni2000numerical]. -/
noncomputable def modifiedScalarStep (f f' : ℝ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  x - m * (f x / f' x)

/-- For $m = 1$, the modified Newton step is the Newton step. -/
theorem modifiedScalarStep_one (f f' : ℝ → ℝ) : modifiedScalarStep f f' 1 = scalarStep f f' := by
  funext x
  simp [modifiedScalarStep, scalarStep]

/-- If $f(x) = 0$, then $x$ is a fixed point of the modified Newton step, for every $f'$ and every
$m$. -/
theorem modifiedScalarStep_apply_of_eq_zero (f f' : ℝ → ℝ) (m : ℕ) {x : ℝ} (hx : f x = 0) :
    modifiedScalarStep f f' m x = x := by
  simp [modifiedScalarStep, hx]

/-- **The modified Newton method is quadratic at a root of multiplicity $m$, with its constant.**
Let $m \ge 1$, let $f \colon \mathbb{R} \to \mathbb{R}$ be $C^{m+1}$ at $\alpha$, and let
$\alpha$ be a root of $f$ of multiplicity $m$. Then, with $\psi$ the modified Newton step for
$f$, its derivative and $m$,
$$\frac{\psi(x) - \alpha}{(x - \alpha)^2} \to \frac{f^{(m+1)}(\alpha)}{(m + 1) m
  f^{(m)}(\alpha)} \qquad \text{as } x \to \alpha,\ x \neq \alpha.$$

This is Exercise 6.2 of [quarteroni2000numerical]. With $e = x - \alpha$ and $f(x) = e^m h(x)$,
the error of the step is $e^2 h'(x)/(m h(x) + e h'(x))$, and the limit is
$h'(\alpha)/(m h(\alpha))$. For $m = 1$ this is Newton's constant $f''(\alpha)/(2 f'(\alpha))$. -/
theorem tendsto_modifiedScalarStep_sub_div_sq (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (modifiedScalarStep f (deriv f) m x - α) / (x - α) ^ 2) (𝓝[≠] α)
      (𝓝 (iteratedDeriv (m + 1) f α / ((m + 1) * m * iteratedDeriv m f α))) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  obtain ⟨h, hh, hhα, hhα', hfh⟩ := hα.exists_eq_pow_mul_deriv hf
  have hc0 : h α ≠ 0 := hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero
  have hDen := tendsto_const_mul_add_sub_mul_deriv hh ((q + 1 : ℕ) : ℝ)
  have hDen0 : ((q + 1 : ℕ) : ℝ) * h α ≠ 0 := mul_ne_zero (by positivity) hc0
  have hlim := (hh.continuousAt_deriv.tendsto.div hDen hDen0).mono_left
    (nhdsWithin_le_nhds (s := {α}ᶜ))
  have hD0 : iteratedDeriv (q + 1) f α ≠ 0 := hα.2
  rw [hhα', hhα, show iteratedDeriv (q + 1 + 1) f α / ((q + 1 + 1).factorial : ℝ) /
      (((q + 1 : ℕ) : ℝ) * (iteratedDeriv (q + 1) f α / (q + 1).factorial)) =
      iteratedDeriv (q + 1 + 1) f α /
        ((((q + 1 : ℕ) : ℝ) + 1) * ((q + 1 : ℕ) : ℝ) * iteratedDeriv (q + 1) f α) by
    rw [Nat.factorial_succ (q + 1)]
    push_cast
    field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (deriv_eq_of_eq_pow_mul hh hfh),
    nhdsWithin_le_nhds (hDen.eventually (isOpen_ne.mem_nhds hDen0))] with x hx hdx hden
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  simp only [Pi.div_apply]
  rw [modifiedScalarStep, hdx, hfh x, sub_right_comm]
  generalize x - α = e at he hden ⊢
  rw [show e ^ (q + 1) * h x / (e ^ q * (((q + 1 : ℕ) : ℝ) * h x + e * deriv h x)) =
      e * h x / (((q + 1 : ℕ) : ℝ) * h x + e * deriv h x) by
    rw [pow_succ, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero q he)],
    div_eq_div_iff hden (pow_ne_zero 2 he), sub_mul, mul_div_assoc', div_mul_cancel₀ _ hden]
  ring

/-- **The modified Newton method is quadratic at a root of multiplicity $m$.** Let $m \ge 1$, let
$f \colon \mathbb{R} \to \mathbb{R}$ be $C^{m+1}$ at $\alpha$, and let $\alpha$ be a root of $f$
of multiplicity $m$. Then there are $\varepsilon > 0$ and $C \in \mathbb{R}$ such that the
modified Newton step $\psi$ for $f$, its derivative and $m$ satisfies
$$|\psi(x) - \alpha| \le C |x - \alpha|^2 \qquad \text{for all } x \in B(\alpha, \varepsilon).$$

This is Exercise 6.2 of [quarteroni2000numerical]. -/
theorem exists_ball_abs_modifiedScalarStep_sub_le (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    ∃ ε > 0, ∃ C, ∀ x ∈ Metric.ball α ε,
      |modifiedScalarStep f (deriv f) m x - α| ≤ C * |x - α| ^ 2 := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (eventually_abs_sub_le_mul_abs_pow_of_tendsto
    (modifiedScalarStep_apply_of_eq_zero f (deriv f) m (hα.eq_zero hm))
    (tendsto_modifiedScalarStep_sub_div_sq hm hf hα))
  exact ⟨ε, hε, _, fun x hx => h (Metric.mem_ball.1 hx)⟩

/-- Let $m \ge 1$, let $f$ be $C^{m+1}$ at $\alpha$, and let $\alpha$ be a root of $f$ of
multiplicity $m$. Then the iteration of the modified Newton step for $f$, its derivative and $m$
has order $2$ at $\alpha$. -/
theorem hasIterationOrder_modifiedScalarStep_two (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    HasIterationOrder (modifiedScalarStep f (deriv f) m) α 2 := by
  have := hasIterationOrder_of_tendsto_sub_div_pow
    (modifiedScalarStep_apply_of_eq_zero f (deriv f) m (hα.eq_zero hm)) le_rfl
    (tendsto_modifiedScalarStep_sub_div_sq hm hf hα)
  simpa using this

end Multiple

section Simple

variable {f : ℝ → ℝ} {α : ℝ}

/-! ### Simple roots -/

/-- **Newton's method at a simple root, with the classical constant.** Let $f(\alpha) = 0$, let $f$
be $C^2$ at $\alpha$, and let $f'(\alpha) \neq 0$. Then
$$\frac{\varphi_{\mathrm{Newt}}(x) - \alpha}{(x - \alpha)^2} \to \frac{f''(\alpha)}{2
  f'(\alpha)} \qquad \text{as } x \to \alpha,\ x \neq \alpha.$$

This is the case $m = 1$ of `Newton.tendsto_modifiedScalarStep_sub_div_sq`. Only $C^2$ is
needed; to read the constant off $\varphi_{\mathrm{Newt}}''(\alpha) = f''(\alpha)/f'(\alpha)$
through Property 6.4 would require $C^3$. -/
theorem tendsto_scalarStep_sub_div_sq (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) :
    Tendsto (fun x => (scalarStep f (deriv f) x - α) / (x - α) ^ 2) (𝓝[≠] α)
      (𝓝 (iteratedDeriv 2 f α / (2 * deriv f α))) := by
  have hroot : IsRootOfMultiplicity f α 1 := isRootOfMultiplicity_one_iff.2 ⟨hα, hf'⟩
  have := tendsto_modifiedScalarStep_sub_div_sq le_rfl (by simpa using hf) hroot
  rw [modifiedScalarStep_one] at this
  simpa [one_add_one_eq_two] using this

/-- **Newton's method has order $2$ at a simple root.** Let $f(\alpha) = 0$, let $f$ be $C^2$ at
$\alpha$, and let $f'(\alpha) \neq 0$. Then the iteration of the Newton step for $f$ and its
derivative has order $2$ at $\alpha$ in the sense of Definition 6.1 of
[quarteroni2000numerical].

This is §6.3.1 of [quarteroni2000numerical], Theorem 6.20 of [kress1998numerical] and Theorem
5.4.1 of [han2009theoretical]. -/
theorem hasIterationOrder_scalarStep_two (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) : HasIterationOrder (scalarStep f (deriv f)) α 2 := by
  have := hasIterationOrder_of_tendsto_sub_div_pow (scalarStep_apply_of_eq_zero f (deriv f) hα)
    le_rfl (tendsto_scalarStep_sub_div_sq hα hf hf')
  simpa using this

/-- **The second derivative of the Newton iteration function at a simple root.** Let $f$ be $C^3$ at
$\alpha$, with $f(\alpha) = 0$ and $f'(\alpha) \neq 0$. Then
$$\varphi_{\mathrm{Newt}}''(\alpha) = \frac{f''(\alpha)}{f'(\alpha)}.$$

This is in §6.3.1 of [quarteroni2000numerical]. Near $\alpha$,
$\varphi_{\mathrm{Newt}}' = f f''/f'^2$, and its derivative at $\alpha$ reduces to
$f''(\alpha)/f'(\alpha)$ because $f(\alpha) = 0$. -/
theorem deriv2_scalarStep_root (hf : ContDiffAt ℝ 3 f α) (hα : f α = 0) (hf' : deriv f α ≠ 0) :
    iteratedDeriv 2 (scalarStep f (deriv f)) α = iteratedDeriv 2 f α / deriv f α := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  have hfb : ContDiffOn ℝ (3 : ℕ) f (Metric.ball α r) := by exact_mod_cast hfu.mono hru
  have hd : ∀ j < 3, ∀ x ∈ Metric.ball α r,
      HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := fun j hj x hx =>
    hfb.hasDerivAt_iteratedDeriv_of_isOpen Metric.isOpen_ball hj hx
  have hcont : ContinuousAt (deriv f) α := by
    have := (hfb.continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball (j := 1)
      (by norm_num)).continuousAt (Metric.ball_mem_nhds α hr)
    simpa using this
  -- `φ_Newt' = f f'' / f'²` near `α`
  have hφ' : deriv (scalarStep f (deriv f)) =ᶠ[𝓝 α]
      fun x => f x * iteratedDeriv 2 f x / (deriv f x) ^ 2 := by
    filter_upwards [Metric.ball_mem_nhds α hr, hcont.eventually_ne hf'] with x hx hx'
    have h1 : HasDerivAt f (deriv f x) x := by simpa using hd 0 (by norm_num) x hx
    have h2 : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
      simpa using hd 1 (by norm_num) x hx
    exact (hasDerivAt_scalarStep h1 h2 hx').deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hφ'.deriv_eq]
  -- differentiate `f f'' / f'²` at `α`
  have h1 : HasDerivAt f (deriv f α) α := by
    simpa using hd 0 (by norm_num) α (Metric.mem_ball_self hr)
  have h2 : HasDerivAt (deriv f) (iteratedDeriv 2 f α) α := by
    simpa using hd 1 (by norm_num) α (Metric.mem_ball_self hr)
  have h3 : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f α) α :=
    hd 2 (by norm_num) α (Metric.mem_ball_self hr)
  refine ((h1.mul h3).div (h2.pow 2) (pow_ne_zero 2 hf')).deriv.trans ?_
  simp only [Pi.mul_apply, Pi.pow_apply, hα]
  field_simp
  ring

end Simple

section Adaptive

/-! ### The adaptive Newton method -/

/-- The **multiplicity estimate** of a real sequence $(x_k)$: $m_k = 1/(1 - \lambda_k)$, where
$\lambda_k = (x_{k+2} - x_{k+1})/(x_{k+1} - x_k)$ is the increment ratio `aitkenRatio`.

This is $m^{(k+2)}$ of (6.40) of [quarteroni2000numerical]. The source also writes it as
$(x_{k+1} - x_k)/(2 x_{k+1} - x_{k+2} - x_k)$; see `Newton.multiplicityEstimate_eq`. -/
noncomputable def multiplicityEstimate (x : ℕ → ℝ) (k : ℕ) : ℝ := 1 / (1 - aitkenRatio x k)

/-- If $x_{k+1} - x_k \neq 0$, then the multiplicity estimate is
$$m_k = \frac{x_{k+1} - x_k}{2 x_{k+1} - x_{k+2} - x_k},$$
the second form in (6.40) of [quarteroni2000numerical]. Where $x_{k+1} = x_k$, the two forms are
$1$ and $0$ by the convention $a/0 = 0$. -/
theorem multiplicityEstimate_eq (x : ℕ → ℝ) (k : ℕ) (h : x (k + 1) - x k ≠ 0) :
    multiplicityEstimate x k = (x (k + 1) - x k) / (2 * x (k + 1) - x (k + 2) - x k) := by
  unfold multiplicityEstimate aitkenRatio
  rw [one_sub_div h, one_div_div]
  congr 1
  ring

/-- **The multiplicity estimate converges to the multiplicity.** Let $m \ge 1$, let
$f \colon \mathbb{R} \to \mathbb{R}$ be $C^{m+1}$ at $\alpha$, and let $\alpha$ be a root of $f$
of multiplicity $m$. Let $(x_k)$ be a Newton orbit, $x_{k+1} = x_k - f(x_k)/f'(x_k)$, with
$x_k \neq \alpha$ for all $k$ and $x_k \to \alpha$. Then the multiplicity estimates $m_k$ tend
to $m$.

This is in §6.6.2 of [quarteroni2000numerical]. The error ratios tend to $1 - 1/m \neq 1$ by
(6.22), so the increment ratios tend to $1 - 1/m$ by (6.34), and $1/(1 - (1 - 1/m)) = m$. -/
theorem tendsto_multiplicityEstimate {f : ℝ → ℝ} {α : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hf : ContDiffAt ℝ (m + 1 : ℕ) f α) (hα : IsRootOfMultiplicity f α m) {x : ℕ → ℝ}
    (hx : ∀ k, x (k + 1) = scalarStep f (deriv f) (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) : Tendsto (multiplicityEstimate x) atTop (𝓝 m) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hratio : Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 (1 - 1 / m)) := by
    have := (tendsto_scalarStep_sub_div_of_isRootOfMultiplicity hm hf hα).comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
    refine this.congr fun k => ?_
    simp [Function.comp, hx]
  have h1 : (1 : ℝ) - 1 / m ≠ 1 := by
    intro h
    have : (1 : ℝ) / m = 0 := by linarith
    exact hm0 (by simpa using this)
  have := (tendsto_const_nhds (x := (1 : ℝ))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_aitkenRatio hne hratio h1))
    (sub_ne_zero.2 h1.symm)
  rw [sub_sub_cancel, one_div_one_div] at this
  exact this

/-- **The adaptive Newton method** as a step on the last three iterates: $(x_{k-2}, x_{k-1}, x_k)
\mapsto (x_{k-1}, x_k, x_k - m_k f(x_k)/f'(x_k))$ with
$$m_k = \frac{x_{k-1} - x_{k-2}}{2 x_{k-1} - x_k - x_{k-2}},$$
the estimate (6.40). When the denominator of $m_k$ is zero, $m_k = 0$.

This is (6.39) of [quarteroni2000numerical]. Program 56 of the source keeps the previous
estimate instead, and updates it only when the ratios have settled; this safeguard belongs to
the implementation. The source proves nothing about the adaptive iteration, so this is a
definition only. -/
noncomputable def adaptiveStep (f f' : ℝ → ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (s.2.1, s.2.2, s.2.2 - (s.2.1 - s.1) / (2 * s.2.1 - s.2.2 - s.1) * (f s.2.2 / f' s.2.2))

end Adaptive

section Monotone

variable {f f' : ℝ → ℝ} {α x₀ : ℝ}

/-! ### Monotone convergence -/

/-- Let $f$ have derivative $f'$ on $[\alpha, x_0]$ with $f' < 0$ and $f'$ antitone there, and let
$f(\alpha) = 0$. Then for every $y \in [\alpha, x_0]$ the Newton step $y - f(y)/f'(y)$ lies in
$[\alpha, y]$. -/
private theorem scalarStep_mem_Icc (hf : ∀ x ∈ Icc α x₀, HasDerivAt f (f' x) x)
    (hneg : ∀ x ∈ Icc α x₀, f' x < 0) (hanti : AntitoneOn f' (Icc α x₀)) (hα : f α = 0)
    {y : ℝ} (hy : y ∈ Icc α x₀) : scalarStep f f' y ∈ Icc α y := by
  rcases hy.1.eq_or_lt with rfl | hlt
  · rw [scalarStep_apply_of_eq_zero f f' hα]
    exact ⟨le_rfl, le_rfl⟩
  have hsub : Icc α y ⊆ Icc α x₀ := Icc_subset_Icc le_rfl hy.2
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f f' hlt
    (fun x hx => (hf x (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx => hf x (hsub (Ioo_subset_Icc_self hx)))
  have hξmem : ξ ∈ Icc α x₀ := hsub (Ioo_subset_Icc_self hξ)
  have hfy : f y = f' ξ * (y - α) := by
    rw [hξeq, hα, sub_zero, div_mul_cancel₀ _ (sub_pos.mpr hlt).ne']
  have hy' := hneg y hy
  have hmono : f' y ≤ f' ξ := hanti hξmem hy hξ.2.le
  have hfy_nonpos : f y ≤ 0 := by
    rw [hfy]
    exact mul_nonpos_of_nonpos_of_nonneg (hneg ξ hξmem).le (sub_pos.mpr hlt).le
  rw [scalarStep]
  constructor
  · -- `f y / f' y ≤ y - α`, dividing `f y ≥ f' y (y - α)` by `f' y < 0`
    have h : f' y * (y - α) ≤ f y := by
      rw [hfy]
      exact mul_le_mul_of_nonneg_right hmono (sub_pos.mpr hlt).le
    have h' : f y / f' y ≤ y - α := by
      rw [div_le_iff_of_neg hy']
      linarith
    linarith
  · have : 0 ≤ f y / f' y := div_nonneg_of_nonpos hfy_nonpos hy'.le
    linarith

/-- **Monotone convergence of Newton's method.** Let $\alpha \le x_0$, let
$f \colon \mathbb{R} \to \mathbb{R}$ have derivative $f'(x)$ at every $x \in [\alpha, x_0]$,
with $f'(x) < 0$ on $[\alpha, x_0]$ and $f'$ antitone on $[\alpha, x_0]$, and let
$f(\alpha) = 0$. Then the Newton iterates $x_k$ from $x_0$ satisfy
$$\alpha \le x_{k+1} \le x_k \qquad \text{for all } k,$$
and $x_k \to \alpha$.

The hypotheses say that $f$ is decreasing and concave on $[\alpha, x_0]$ (Fourier's condition).
This is the argument behind (4.7.10) of [golub2013matrix], Newton's method for the smallest
eigenvalue of a symmetric positive definite Toeplitz matrix. Each step stays in $[\alpha, x_k]$
by the mean value theorem and concavity. The iterates decrease and are bounded below, so they
converge to some $\ell \in [\alpha, x_0]$. The identity $f(x_k) = f'(x_k)(x_k - x_{k+1})$, with
$|f'|$ bounded by $|f'(x_0)|$ because $f'$ is antitone, forces $f(\ell) = 0$, and $f$ has no
root in $(\alpha, x_0]$. -/
theorem tendsto_iterate_scalarStep_of_antitoneOn_deriv (hαx : α ≤ x₀)
    (hf : ∀ x ∈ Icc α x₀, HasDerivAt f (f' x) x) (hneg : ∀ x ∈ Icc α x₀, f' x < 0)
    (hanti : AntitoneOn f' (Icc α x₀)) (hα : f α = 0) :
    (∀ k, α ≤ (scalarStep f f')^[k + 1] x₀ ∧
      (scalarStep f f')^[k + 1] x₀ ≤ (scalarStep f f')^[k] x₀) ∧
      Tendsto (fun k => (scalarStep f f')^[k] x₀) atTop (𝓝 α) := by
  set x : ℕ → ℝ := fun k => (scalarStep f f')^[k] x₀ with hxdef
  have hxsucc : ∀ k, x (k + 1) = scalarStep f f' (x k) := fun k => by
    simp only [hxdef, Function.iterate_succ_apply']
  have hmem : ∀ k, x k ∈ Icc α x₀ := by
    intro k
    induction k with
    | zero => exact ⟨hαx, le_rfl⟩
    | succ k ih =>
      have h := scalarStep_mem_Icc hf hneg hanti hα ih
      rw [hxsucc]
      exact ⟨h.1, h.2.trans ih.2⟩
  have hstep : ∀ k, α ≤ x (k + 1) ∧ x (k + 1) ≤ x k := fun k => by
    rw [hxsucc]
    exact scalarStep_mem_Icc hf hneg hanti hα (hmem k)
  refine ⟨hstep, ?_⟩
  -- the iterates converge to their infimum `ℓ`
  have hanti_x : Antitone x := antitone_nat_of_succ_le fun k => (hstep k).2
  have hbdd : BddBelow (Set.range x) := ⟨α, by rintro _ ⟨k, rfl⟩; exact (hmem k).1⟩
  set ℓ := ⨅ k, x k with hℓ
  have hlim : Tendsto x atTop (𝓝 ℓ) := tendsto_atTop_ciInf hanti_x hbdd
  have hℓmem : ℓ ∈ Icc α x₀ :=
    ⟨le_ciInf fun k => (hmem k).1, (ciInf_le hbdd 0).trans (hmem 0).2⟩
  -- `f (x_k) → 0`
  have hfx : ∀ k, f (x k) = f' (x k) * (x k - x (k + 1)) := fun k => by
    rw [hxsucc, scalarStep, sub_sub_cancel, mul_div_cancel₀ _ (hneg _ (hmem k)).ne]
  have hdiff : Tendsto (fun k => x k - x (k + 1)) atTop (𝓝 0) := by
    simpa using hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
  have hf0 : Tendsto (fun k => f (x k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k => -f' x₀ * (x k - x (k + 1))) (fun k => ?_) ?_
    · rw [hfx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg (hneg _ (hmem k)),
        abs_of_nonneg (sub_nonneg.mpr (hstep k).2)]
      exact mul_le_mul_of_nonneg_right (neg_le_neg (hanti (hmem k) ⟨hαx, le_rfl⟩ (hmem k).2))
        (sub_nonneg.mpr (hstep k).2)
    · simpa using hdiff.const_mul (-f' x₀)
  have hfℓ : f ℓ = 0 :=
    tendsto_nhds_unique (((hf ℓ hℓmem).continuousAt.tendsto).comp hlim) hf0
  -- the only root in `[α, x₀]` is `α`
  suffices hℓα : ℓ = α by rwa [hℓα] at hlim
  by_contra hne
  have hlt : α < ℓ := lt_of_le_of_ne hℓmem.1 (Ne.symm hne)
  have hsub : Icc α ℓ ⊆ Icc α x₀ := Icc_subset_Icc le_rfl hℓmem.2
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f f' hlt
    (fun y hy => (hf y (hsub hy)).continuousAt.continuousWithinAt)
    (fun y hy => hf y (hsub (Ioo_subset_Icc_self hy)))
  rw [hfℓ, hα, sub_zero, zero_div] at hξeq
  exact (hneg ξ (hsub (Ioo_subset_Icc_self hξ))).ne hξeq

end Monotone

end Newton
