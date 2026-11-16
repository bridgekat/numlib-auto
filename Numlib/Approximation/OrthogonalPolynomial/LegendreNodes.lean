/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Numlib.Analysis.ODE.SturmComparison
import Numlib.Approximation.MarkovInequality
import Numlib.Approximation.OrthogonalPolynomial

/-!
# The location of the zeros of the Legendre polynomials and of the Gauss–Lobatto nodes

Let $L_N$ be the Legendre polynomial of degree $N$, normalized by $L_N(1) = 1$. In the variable
$\theta = \arccos x$, the function $u(\theta) = \sqrt{\sin\theta}\, L_N(\cos\theta)$ is the
**Liouville normal form** of the Legendre equation, and it satisfies
$$u'' + \Bigl(\bigl(N + \tfrac12\bigr)^2 + \frac{1}{4\sin^2\theta}\Bigr) u = 0 \quad \text{on } (0,
  \pi).$$
This module derives the equation and uses Sturm's comparison theorem to show that, in the variable
$\theta$, the zeros of $L_N$ are at most $\pi/(N + \frac12)$ apart, and the zeros of $L_N'$ are at
most $2\pi/(N + \frac12)$ apart. The zeros of $L_N'$ are the interior Gauss–Lobatto nodes
(`Quadrature.derivative_legendre_eq_family` in `Numlib.Approximation.GaussLobatto`). For $N \ge 2$
the node nearest to $1$ lies in $(1 - 81\pi^2/(32N^2), 1)$, and by the symmetry
$L_N(-x) = (-1)^N L_N(x)$ the same holds at $-1$. The presentation follows Szegő, *Orthogonal
Polynomials*, §4.7 and §6.3, and [quarteroni2000numerical], §10.4 and §13.3.1.

The spacing bound in $\theta$ is the ingredient of the Marcinkiewicz–Zygmund inequality at the
Gauss–Lobatto nodes. The lower bound $\lambda_{\max} \ge cN^4$ for the eigenvalues of the
pseudo-spectral stiffness matrix ([quarteroni2000numerical], §13.3.1) needs the location of the node
nearest to $1$, together with the bound $w_j \le 2048/N^2$ on the Gauss–Lobatto weight at that node,
which this module also proves.

## Main definitions

* `Polynomial.legendreLiouville`: the Liouville normal form $u(\theta) = \sqrt{\sin\theta}\,
  L_N(\cos\theta)$.
* `Polynomial.legendreLiouvilleDeriv`: the formula for its derivative $u'$.
* `Polynomial.legendreLiouvillePotential`: the potential $q(\theta) = (N + \frac12)^2 +
  1/(4\sin^2\theta)$.
* `Polynomial.legendreKernelOne`: the Christoffel–Darboux kernel $K_M(x, 1) = \sum_{k \le M}
  \frac{2k+1}{2} L_k(x)$.

## Main results

* `Polynomial.isSturmSolutionOn_legendreLiouville`: the Liouville normal form solves $u'' + qu = 0$
  on $(0, \pi)$.
* `Polynomial.exists_eval_legendre_cos_eq_zero`: every open interval of length at least
  $\pi/(N + \frac12)$ in $(0, \pi)$ contains a zero of $\theta \mapsto L_N(\cos\theta)$.
* `Polynomial.exists_eval_derivative_legendre_cos_eq_zero`: every open interval of length at least
  $2\pi/(N + \frac12)$ in $(0, \pi)$ contains a zero of $\theta \mapsto L_N'(\cos\theta)$.
* `Polynomial.exists_eval_derivative_legendre_eq_zero_near_one`: for $N \ge 2$ there is a zero $t$
  of $L_N'$ with $1 - 81\pi^2/(32N^2) < t < 1$.
* `Polynomial.abs_eval_derivative_legendre_le`: $|L_k'(x)| \le k^2$ on $[-1, 1]$.
* `Quadrature.weight_mul_eval_sq_le_of_isExactOnMeasure`: the Christoffel-function bound
  $w_j\, p(x_j)^2 \le \int p^2\,d\mu$ on the weights of a rule with nonnegative weights.
* `Quadrature.legendreLobattoWeight_le_of_near_one`: the Legendre–Gauss–Lobatto weight at a node
  within $81\pi^2/(32N^2)$ of $1$ is at most $2048/N^2$.

## Proof outline

The potential $q$ exceeds $(N + \frac12)^2$. Sturm comparison of $u$ with
$\sin((N + \frac12)(\theta - a))$ (`IsSturmSolutionOn.exists_zero_Ioo_of_sq_lt`) puts a zero of $u$
in every interval of length $\pi/(N + \frac12)$. Two zeros of $L_N$ in an interval of length
$2\pi/(N + \frac12)$ give, by Rolle's theorem, a zero of $L_N'$ between them. The bound on the
weight is the Christoffel-function bound with the test polynomial $K_M(\cdot, 1)$ of degree
$M = \lfloor N/16 \rfloor$.

## Implementation notes

* $L_N$ is `Polynomial.legendre N`, defined by Rodrigues' formula.
* The second-order equation is stated in first-order form by `IsSturmSolutionOn`, with
  `Polynomial.legendreLiouvilleDeriv` as the derivative of $u$.
* The functions of the Liouville normal form are defined on all of $\mathbb{R}$ but are used only on
  $(0, \pi)$. Where $\sin\theta \le 0$, Lean's conventions $\sqrt{s} = 0$ for $s \le 0$ and
  $1/0 = 0$ apply.
-/

open MeasureTheory Real Set

namespace Polynomial

variable (N : ℕ)

/-! ### The Liouville normal form of the Legendre equation -/

/-- The **Liouville normal form** of the Legendre polynomial $L_N$ is the function
$$u(\theta) = \sqrt{\sin\theta}\; L_N(\cos\theta).$$

It is used on $(0, \pi)$, where $\sin\theta > 0$. Where $\sin\theta \le 0$, the Lean square root
gives $\sqrt{\sin\theta} = 0$, so $u(\theta) = 0$. -/
noncomputable def legendreLiouville (θ : ℝ) : ℝ :=
  √(sin θ) * (legendre N).eval (cos θ)

/-- The derivative of the Liouville normal form $u$ of $L_N$, given by the formula
$$u'(\theta) = \frac{\cos\theta}{2\sqrt{\sin\theta}}\, L_N(\cos\theta) -
  \sqrt{\sin\theta}\,\sin\theta\, L_N'(\cos\theta).$$

The formula is the derivative of $u$ on $(0, \pi)$ (`Polynomial.hasDerivAt_legendreLiouville`).
Where $\sin\theta \le 0$, the Lean conventions $\sqrt{s} = 0$ for $s \le 0$ and $1/0 = 0$ give
the value $0$. -/
noncomputable def legendreLiouvilleDeriv (θ : ℝ) : ℝ :=
  cos θ / (2 * √(sin θ)) * (legendre N).eval (cos θ) -
    √(sin θ) * sin θ * (derivative (legendre N)).eval (cos θ)

/-- The potential of the Liouville normal form of $L_N$:
$$q(\theta) = \bigl(N + \tfrac12\bigr)^2 + \frac{1}{4\sin^2\theta}.$$

At the zeros of $\sin\theta$, the Lean convention $1/0 = 0$ gives $q(\theta) = (N + \frac12)^2$. -/
noncomputable def legendreLiouvillePotential (θ : ℝ) : ℝ :=
  ((N : ℝ) + 1 / 2) ^ 2 + 1 / (4 * sin θ ^ 2)

variable {N}

/-- The derivative of $\theta \mapsto \sqrt{\sin\theta}$ at $\theta \in (0, \pi)$ is
$\cos\theta / (2\sqrt{\sin\theta})$. -/
private theorem hasDerivAt_sqrt_sin {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (fun θ => √(sin θ)) (1 / (2 * √(sin θ)) * cos θ) θ :=
  (Real.hasDerivAt_sqrt (sin_pos_of_mem_Ioo hθ).ne').comp θ (Real.hasDerivAt_sin θ)

/-- The derivative of $\theta \mapsto p(\cos\theta)$ is $-p'(\cos\theta)\sin\theta$. -/
private theorem hasDerivAt_eval_cos (p : ℝ[X]) (θ : ℝ) :
    HasDerivAt (fun θ => p.eval (cos θ)) ((derivative p).eval (cos θ) * -sin θ) θ :=
  (p.hasDerivAt (cos θ)).comp θ (Real.hasDerivAt_cos θ)

/-- For $\theta \in (0, \pi)$, the Liouville normal form $u(\theta) = \sqrt{\sin\theta}\,
L_N(\cos\theta)$ has the derivative
$$u'(\theta) = \frac{\cos\theta}{2\sqrt{\sin\theta}}\, L_N(\cos\theta) -
  \sqrt{\sin\theta}\,\sin\theta\, L_N'(\cos\theta),$$
which is `Polynomial.legendreLiouvilleDeriv`. -/
theorem hasDerivAt_legendreLiouville {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (legendreLiouville N) (legendreLiouvilleDeriv N θ) θ := by
  refine ((hasDerivAt_sqrt_sin hθ).mul (hasDerivAt_eval_cos (legendre N) θ)).congr_deriv ?_
  unfold legendreLiouvilleDeriv
  ring

/-- The **Legendre equation in Liouville normal form**. For $\theta \in (0, \pi)$, the function $u'$
of `Polynomial.legendreLiouvilleDeriv` has the derivative
$$u''(\theta) = -\Bigl(\bigl(N + \tfrac12\bigr)^2 + \frac{1}{4\sin^2\theta}\Bigr)\, u(\theta),$$
where $u(\theta) = \sqrt{\sin\theta}\, L_N(\cos\theta)$.

Write $r = \sqrt{\sin\theta}$ and $c = \cos\theta$. The second derivative of $u = r L_N(c)$ is
$-(2r^4 + c^2) L_N(c)/(4r^3) - 2rc\, L_N'(c) + r^5 L_N''(c)$. The identity $c^2 = 1 - r^4$ and
the Legendre equation $(c^2 - 1) L_N''(c) + 2c L_N'(c) = N(N+1) L_N(c)$
(`Polynomial.legendre_ode`) turn this into $-((N + \frac12)^2 + 1/(4r^4))\, r L_N(c)$. -/
theorem hasDerivAt_legendreLiouvilleDeriv {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (legendreLiouvilleDeriv N)
      (-(legendreLiouvillePotential N θ * legendreLiouville N θ)) θ := by
  have hs : 0 < sin θ := sin_pos_of_mem_Ioo hθ
  have hr : 0 < √(sin θ) := Real.sqrt_pos.2 hs
  have hsq := hasDerivAt_sqrt_sin hθ
  have hA : HasDerivAt (fun θ => cos θ / (2 * √(sin θ)))
      ((-sin θ * (2 * √(sin θ)) - cos θ * (2 * (1 / (2 * √(sin θ)) * cos θ))) /
        (2 * √(sin θ)) ^ 2) θ :=
    (Real.hasDerivAt_cos θ).div (hsq.const_mul 2) (by positivity)
  have hC : HasDerivAt (fun θ => √(sin θ) * sin θ)
      (1 / (2 * √(sin θ)) * cos θ * sin θ + √(sin θ) * cos θ) θ :=
    hsq.mul (Real.hasDerivAt_sin θ)
  refine ((hA.mul (hasDerivAt_eval_cos (legendre N) θ)).sub
    (hC.mul (hasDerivAt_eval_cos (derivative (legendre N)) θ))).congr_deriv ?_
  -- the algebra: `r = √(sin θ)`, `c = cos θ`, `sin θ = r²`, `c² = 1 − r⁴`, and the ODE
  have hode := congrArg (eval (cos θ)) (legendre_ode N)
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_natCast,
    eval_ofNat] at hode
  have hcs : cos θ ^ 2 = 1 - sin θ ^ 2 := by rw [cos_sq']
  unfold legendreLiouvillePotential legendreLiouville
  set r := √(sin θ) with hr_def
  have hr2 : sin θ = r ^ 2 := (Real.sq_sqrt hs.le).symm
  rw [hr2] at hcs ⊢
  set c := cos θ
  set L := (legendre N).eval c
  set L' := (derivative (legendre N)).eval c
  set L'' := (derivative (derivative (legendre N))).eval c
  have hr0 : r ≠ 0 := hr.ne'
  field_simp
  linear_combination (-4 * L + 16 * r ^ 4 * L'') * hcs + (-16 * r ^ 4) * hode

/-- The Liouville normal form $u(\theta) = \sqrt{\sin\theta}\, L_N(\cos\theta)$ solves
$$u'' + \Bigl(\bigl(N + \tfrac12\bigr)^2 + \frac{1}{4\sin^2\theta}\Bigr) u = 0 \quad \text{on }
  (0, \pi).$$
This is equation (4.7.10) of Szegő, *Orthogonal Polynomials*.

The equation is stated in first-order form by `IsSturmSolutionOn`, with the potential
`Polynomial.legendreLiouvillePotential` and the derivative `Polynomial.legendreLiouvilleDeriv`. -/
theorem isSturmSolutionOn_legendreLiouville :
    IsSturmSolutionOn (legendreLiouvillePotential N) (legendreLiouville N)
      (legendreLiouvilleDeriv N) (Ioo 0 π) :=
  ⟨fun _ hθ => hasDerivAt_legendreLiouville hθ, fun _ hθ => hasDerivAt_legendreLiouvilleDeriv hθ⟩

/-- For $\theta \in (0, \pi)$, the potential of the Liouville normal form exceeds $(N + \frac12)^2$:
$(N + \frac12)^2 < (N + \frac12)^2 + 1/(4\sin^2\theta)$. -/
theorem sq_lt_legendreLiouvillePotential {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ((N : ℝ) + 1 / 2) ^ 2 < legendreLiouvillePotential N θ := by
  have hs : 0 < sin θ := sin_pos_of_mem_Ioo hθ
  unfold legendreLiouvillePotential
  have : 0 < 1 / (4 * sin θ ^ 2) := by positivity
  linarith

/-! ### The zeros of $L_N(\cos\theta)$ -/

/-- Let $0 < a$ and $b < \pi$ with $b - a \ge \pi/(N + \frac12)$. Then there is $\theta \in (a, b)$
with $L_N(\cos\theta) = 0$. So, in the variable $\theta$, the zeros of $L_N$ are at most
$\pi/(N + \frac12)$ apart. This is the Legendre case of Theorem 6.3.2 of Szegő, *Orthogonal
Polynomials*.

The proof is the Sturm comparison `IsSturmSolutionOn.exists_zero_Ioo_of_sq_lt` of the Liouville
normal form with $\sin((N + \frac12)(\theta - a))$. -/
theorem exists_eval_legendre_cos_eq_zero {a b : ℝ} (ha : 0 < a) (hb : b < π)
    (hab : π / ((N : ℝ) + 1 / 2) ≤ b - a) :
    ∃ θ ∈ Ioo a b, (legendre N).eval (cos θ) = 0 := by
  have hm : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hsub : Icc a b ⊆ Ioo 0 π := fun x hx => ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  obtain ⟨θ, hθ, hθ0⟩ := (isSturmSolutionOn_legendreLiouville (N := N)).mono hsub
    |>.exists_zero_Ioo_of_sq_lt hm hab
      fun x hx => sq_lt_legendreLiouvillePotential (hsub (Ioo_subset_Icc_self hx))
  refine ⟨θ, hθ, ?_⟩
  have hs : 0 < sin θ := sin_pos_of_mem_Ioo (hsub (Ioo_subset_Icc_self hθ))
  unfold legendreLiouville at hθ0
  exact (mul_eq_zero.1 hθ0).resolve_left (Real.sqrt_pos.2 hs).ne'

/-! ### The Gauss–Lobatto nodes -/

/-- Let $0 < a$ and $b < \pi$ with $b - a \ge 2\pi/(N + \frac12)$. Then there is $\theta \in (a, b)$
with $L_N'(\cos\theta) = 0$. The zeros of $L_N'$ are the interior Gauss–Lobatto nodes, so in the
variable $\theta$ these nodes are at most $2\pi/(N + \frac12)$ apart.

By `Polynomial.exists_eval_legendre_cos_eq_zero`, each half of $(a, b)$ contains a zero of
$\theta \mapsto L_N(\cos\theta)$, say $\theta_1 < \theta_2$. Rolle's theorem for $L_N$ on
$[\cos\theta_2, \cos\theta_1]$ gives the zero of $L_N'$. -/
theorem exists_eval_derivative_legendre_cos_eq_zero {a b : ℝ} (ha : 0 < a) (hb : b < π)
    (hab : 2 * (π / ((N : ℝ) + 1 / 2)) ≤ b - a) :
    ∃ θ ∈ Ioo a b, (derivative (legendre N)).eval (cos θ) = 0 := by
  have hm : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hπm : 0 < π / ((N : ℝ) + 1 / 2) := div_pos pi_pos hm
  obtain ⟨θ₁, hθ₁, h1⟩ := exists_eval_legendre_cos_eq_zero (N := N) (a := a)
    (b := a + π / ((N : ℝ) + 1 / 2)) ha (by linarith) (by linarith)
  obtain ⟨θ₂, hθ₂, h2⟩ := exists_eval_legendre_cos_eq_zero (N := N)
    (a := a + π / ((N : ℝ) + 1 / 2)) (b := b) (by linarith) hb (by linarith)
  have h12 : θ₁ < θ₂ := hθ₁.2.trans hθ₂.1
  have hθ₁0 : 0 ≤ θ₁ := by linarith [hθ₁.1]
  have hθ₂π : θ₂ ≤ π := by linarith [hθ₂.2]
  have hcos : cos θ₂ < cos θ₁ := cos_lt_cos_of_nonneg_of_le_pi hθ₁0 hθ₂π h12
  obtain ⟨t, ht, ht0⟩ := exists_hasDerivAt_eq_zero (f := fun x => (legendre N).eval x)
    (f' := fun x => (derivative (legendre N)).eval x) hcos
    (legendre N).continuous.continuousOn (by simp only [h1, h2])
    fun x _ => (legendre N).hasDerivAt x
  have ht1 : -1 ≤ t := (neg_one_le_cos θ₂).trans ht.1.le
  have ht2 : t ≤ 1 := ht.2.le.trans (cos_le_one θ₁)
  refine ⟨arccos t, ⟨?_, ?_⟩, by rwa [cos_arccos ht1 ht2]⟩
  · calc a < θ₁ := hθ₁.1
      _ = arccos (cos θ₁) := (arccos_cos hθ₁0 (by linarith)).symm
      _ < arccos t := strictAntiOn_arccos ⟨ht1, ht2⟩ ⟨neg_one_le_cos _, cos_le_one _⟩ ht.2
  · calc arccos t < arccos (cos θ₂) :=
          strictAntiOn_arccos ⟨neg_one_le_cos _, cos_le_one _⟩ ⟨ht1, ht2⟩ ht.1
      _ = θ₂ := arccos_cos (by linarith) hθ₂π
      _ < b := hθ₂.2

/-- For $N \ge 2$ there is $\theta$ with $0 < \theta < 9\pi/(4N + 2)$ and $L_N'(\cos\theta) = 0$.
This locates, in the variable $\theta$, the Gauss–Lobatto node nearest to $1$.

The proof applies `Polynomial.exists_eval_derivative_legendre_cos_eq_zero` on the interval
$(\pi/(4N + 2), 9\pi/(4N + 2))$. -/
theorem exists_eval_derivative_legendre_cos_eq_zero_lt (hN : 2 ≤ N) :
    ∃ θ, 0 < θ ∧ θ < 9 * π / (4 * (N : ℝ) + 2) ∧ (derivative (legendre N)).eval (cos θ) = 0 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  set m : ℝ := (N : ℝ) + 1 / 2 with hm_def
  have hπm : 0 < π / m := div_pos pi_pos hm
  have h9 : 9 * π / (4 * (N : ℝ) + 2) = 9 / 4 * (π / m) := by
    rw [hm_def]; field_simp; ring
  have hb : 9 / 4 * (π / m) < π := by
    rw [mul_div_assoc', div_lt_iff₀ hm, hm_def]
    nlinarith [pi_pos]
  obtain ⟨θ, hθ, h⟩ := exists_eval_derivative_legendre_cos_eq_zero (N := N)
    (a := 1 / 4 * (π / m)) (b := 9 / 4 * (π / m)) (by positivity) hb (by linarith)
  exact ⟨θ, by linarith [hθ.1], by rw [h9]; exact hθ.2, h⟩

/-- For $N \ge 2$ there is a zero $t$ of $L_N'$ with
$$1 - \frac{81\pi^2}{32N^2} < t < 1.$$
So the Gauss–Lobatto node nearest to $1$ lies within $81\pi^2/(32N^2)$ of $1$. The lower bound
$\lambda_{\max} \ge cN^4$ for the pseudo-spectral stiffness matrix ([quarteroni2000numerical],
§13.3.1) needs this location of the node.

The proof takes $t = \cos\theta$ with $\theta$ from
`Polynomial.exists_eval_derivative_legendre_cos_eq_zero_lt`, so that
$\theta < 9\pi/(4N + 2) < 9\pi/(4N)$, and uses $1 - \cos\theta \le \theta^2/2$
(`Real.one_sub_sq_div_two_le_cos`). -/
theorem exists_eval_derivative_legendre_eq_zero_near_one (hN : 2 ≤ N) :
    ∃ t, (derivative (legendre N)).eval t = 0 ∧
      1 - 81 * π ^ 2 / (32 * (N : ℝ) ^ 2) < t ∧ t < 1 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨θ, hθ0, hθ, h⟩ := exists_eval_derivative_legendre_cos_eq_zero_lt hN
  refine ⟨cos θ, h, ?_, ?_⟩
  · have hθ' : θ < 9 * π / (4 * (N : ℝ)) := by
      refine hθ.trans_le ?_
      gcongr
      linarith
    have hsq : θ ^ 2 < (9 * π / (4 * (N : ℝ))) ^ 2 := by gcongr
    have hcos := one_sub_sq_div_two_le_cos (x := θ)
    have h81 : (9 * π / (4 * (N : ℝ))) ^ 2 / 2 = 81 * π ^ 2 / (32 * (N : ℝ) ^ 2) := by
      field_simp; ring
    linarith
  · have hθπ : θ < π := by
      refine hθ.trans_le ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pi_pos]
    simpa using cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0

/-!
### The Gauss–Lobatto weights near the endpoints

Let a quadrature rule with nonnegative weights be exact on $\mathbb{P}_{2n-1}$. Its weight at a node
$x_j$ is at most $\int p^2 / p(x_j)^2$ for every $p \in \mathbb{P}_{n-1}$
(`Quadrature.weight_mul_eval_sq_le_of_isExactOnMeasure`). This is the Christoffel-function bound. At
a node within $81\pi^2/(32N^2)$ of $1$, take the test polynomial $K_M(x, 1) = \sum_{k \le M}
\frac{2k+1}{2} L_k(x)$ with $M = \lfloor N/16 \rfloor$. By Parseval's identity,
$\int_{-1}^1 K_M^2 = (M+1)^2/2$. The endpoint bound $|L_k'| \le k^2$ gives
$L_k(x_j) \ge 1 - k^2(1 - x_j) \ge 1/2$ for $k \le M$, so $K_M(x_j, 1) \ge (M+1)^2/4$. Hence
$w_j \le 8/(M+1)^2 < 2048/N^2$ (`Quadrature.legendreLobattoWeight_le_of_near_one`).
-/

/-- For every $k \in \mathbb{N}$ and $x \in [-1, 1]$,
$$|L_k'(x)| \le k^2.$$

The proof expands $L_k' = \sum_{j < k} c_j L_j$ in Legendre polynomials, with coefficients
$|c_j| \le 2j + 1$ (`Polynomial.abs_legendreCoeff_derivative_legendre_le`), and uses
$|L_j| \le 1$ on $[-1, 1]$. -/
theorem abs_eval_derivative_legendre_le (k : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(derivative (legendre k)).eval x| ≤ (k : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [legendre_zero]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hdeg : (derivative (legendre (m + 1))).natDegree ≤ m := by
    have := natDegree_derivative_le (legendre (m + 1))
    rw [natDegree_legendre] at this
    omega
  rw [eq_sum_legendreCoeff hdeg]
  simp only [eval_finsetSum, eval_mul, eval_C]
  calc |∑ j ∈ Finset.range (m + 1),
        legendreCoeff (derivative (legendre (m + 1))) j * (legendre j).eval x|
      ≤ ∑ j ∈ Finset.range (m + 1),
          |legendreCoeff (derivative (legendre (m + 1))) j * (legendre j).eval x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), (2 * (j : ℝ) + 1) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        calc |legendreCoeff (derivative (legendre (m + 1))) j| * |(legendre j).eval x|
            ≤ (2 * (j : ℝ) + 1) * 1 :=
              mul_le_mul (abs_legendreCoeff_derivative_legendre_le _ _)
                (abs_eval_legendre_le_one j hx) (abs_nonneg _) (by positivity)
          _ = 2 * (j : ℝ) + 1 := mul_one _
    _ = ((m : ℝ) + 1) ^ 2 := sum_range_two_mul_add_one m
    _ = ((m + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring

/-- For every $k \in \mathbb{N}$ and $t \in [-1, 1]$,
$$L_k(t) \ge 1 - k^2(1 - t).$$
This follows from $L_k(1) = 1$ and $|L_k'| \le k^2$ on $[-1, 1]$. -/
theorem one_sub_sq_mul_le_eval_legendre (k : ℕ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    1 - (k : ℝ) ^ 2 * (1 - t) ≤ (legendre k).eval t := by
  have hftc : ∫ x in t..1, (derivative (legendre k)).eval x =
      (legendre k).eval 1 - (legendre k).eval t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (legendre k).hasDerivAt x)
      ((derivative (legendre k)).continuous.intervalIntegrable _ _)
  have hle : ∫ x in t..1, (derivative (legendre k)).eval x ≤ ∫ x in t..1, (k : ℝ) ^ 2 := by
    refine intervalIntegral.integral_mono_on ht.2
      ((derivative (legendre k)).continuous.intervalIntegrable _ _)
      intervalIntegrable_const fun x hx => ?_
    exact (le_abs_self _).trans (abs_eval_derivative_legendre_le k ⟨by linarith [hx.1, ht.1], hx.2⟩)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  rw [legendre_eval_one] at hftc
  linarith

/-- The **Christoffel–Darboux kernel at $1$** of degree $M$ for the Legendre polynomials:
$$K_M(x, 1) = \sum_{k=0}^{M} \frac{2k+1}{2}\, L_k(x).$$
It is a polynomial of degree at most $M$ that is concentrated near $x = 1$, on a layer of width
of order $M^{-2}$. -/
noncomputable def legendreKernelOne (M : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (M + 1), C ((2 * (k : ℝ) + 1) / 2) * legendre k

/-- The kernel $K_M(\cdot, 1)$ has degree at most $M$. -/
theorem natDegree_legendreKernelOne_le (M : ℕ) : (legendreKernelOne M).natDegree ≤ M := by
  refine (natDegree_sum_le_of_forall_le _ _ fun k hk => ?_)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_legendre]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

/-- For $k \le M$, the $k$-th Legendre coefficient of $K_M(\cdot, 1)$ is $(2k+1)/2$. The coefficient
is `Polynomial.legendreCoeff`, that is, $\frac{2k+1}{2} \int_{-1}^1 K_M(x, 1)\, L_k(x)\,dx$. -/
theorem legendreCoeff_legendreKernelOne (M : ℕ) {k : ℕ} (hk : k ∈ Finset.range (M + 1)) :
    legendreCoeff (legendreKernelOne M) k = (2 * (k : ℝ) + 1) / 2 := by
  rw [legendreKernelOne, legendreCoeff_sum, Finset.sum_eq_single k]
  · rw [legendreCoeff_C_mul, legendreCoeff_legendre, ite_eq_left rfl, mul_one]
  · intro j _ hjk
    rw [legendreCoeff_C_mul, legendreCoeff_legendre, ite_eq_right hjk, mul_zero]
  · intro h; exact absurd hk h

/-- The kernel $K_M(\cdot, 1)$ satisfies
$$\int_{-1}^{1} K_M(x, 1)^2\,dx = \frac{(M+1)^2}{2}.$$
This is Parseval's identity: $\int_{-1}^1 L_k^2 = 2/(2k+1)$, and $\sum_{k \le M}
\bigl(\frac{2k+1}{2}\bigr)^2 \frac{2}{2k+1} = (M+1)^2/2$. -/
theorem integral_legendreKernelOne_sq (M : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendreKernelOne M).eval x ^ 2 = ((M : ℝ) + 1) ^ 2 / 2 := by
  rw [integral_sq_eq_sum_legendreCoeff (natDegree_legendreKernelOne_le M)]
  rw [← sum_range_two_mul_add_one M, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [legendreCoeff_legendreKernelOne M hk]
  have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- Let $t \in [-1, 1]$ with $k^2(1 - t) \le 1/2$ for every $k \le M$. Then
$$K_M(t, 1) \ge \frac{(M+1)^2}{4},$$
because $L_k(t) \ge 1/2$ for every $k \le M$ by `Polynomial.one_sub_sq_mul_le_eval_legendre`. -/
theorem le_eval_legendreKernelOne (M : ℕ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsmall : ∀ k ≤ M, (k : ℝ) ^ 2 * (1 - t) ≤ 1 / 2) :
    ((M : ℝ) + 1) ^ 2 / 4 ≤ (legendreKernelOne M).eval t := by
  rw [legendreKernelOne, eval_finsetSum]
  simp only [eval_mul, eval_C]
  calc ((M : ℝ) + 1) ^ 2 / 4 = ∑ k ∈ Finset.range (M + 1), (2 * (k : ℝ) + 1) / 2 * (1 / 2) := by
        rw [← Finset.sum_mul, ← Finset.sum_div, sum_range_two_mul_add_one]; ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h1 := one_sub_sq_mul_le_eval_legendre k ht
        have h2 := hsmall k hk'
        have : (0 : ℝ) ≤ (2 * (k : ℝ) + 1) / 2 := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) this

end Polynomial

namespace Quadrature

open OrthogonalPolynomial Polynomial

/-- The **Christoffel-function bound** on the weights of a rule with nonnegative weights. Let $\mu$
be a measure on $\mathbb{R}$, and let a rule with $n$ nodes $x_i$ and weights $w_i \ge 0$ be
exact to degree $d$ for $\mu$. If $p$ is a real polynomial with $\deg(p^2) \le d$, then for
every node $x_j$
$$w_j\, p(x_j)^2 \le \int p^2\,d\mu.$$

Exactness gives $\sum_i w_i\, p(x_i)^2 = \int p^2\,d\mu$, and $w_j\, p(x_j)^2$ is one term of
this sum of nonnegative terms. Exactness is `Quadrature.IsExactOnMeasure`. -/
theorem weight_mul_eval_sq_le_of_isExactOnMeasure {μ : MeasureTheory.Measure ℝ} {n d : ℕ}
    {w x : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (hexact : IsExactOnMeasure μ w x d) {p : ℝ[X]}
    (hp : (p * p).degree ≤ d) (j : Fin n) :
    w j * p.eval (x j) ^ 2 ≤ ∫ t, p.eval t ^ 2 ∂μ := by
  have h := hexact (p * p) hp
  simp only [eval_mul] at h
  have hsq : ∫ t, p.eval t ^ 2 ∂μ = ∫ t, p.eval t * p.eval t ∂μ := by simp only [sq]
  rw [hsq, ← h, sq]
  exact Finset.single_le_sum (f := fun i => w i * (p.eval (x i) * p.eval (x i)))
    (fun i _ => mul_nonneg (hw i) (mul_self_nonneg _)) (Finset.mem_univ j)

/-- Let $N \ge 1$, and let a rule with $N + 1$ nodes $x_i$ and weights $w_i \ge 0$ be exact to
degree $2N - 1$ for the Legendre weight, which is Lebesgue measure on $(-1, 1)$. If a node
$x_j \in [-1, 1]$ satisfies $1 - x_j \le 81\pi^2/(32N^2)$, then
$$w_j \le \frac{2048}{N^2}.$$
The Legendre–Gauss–Lobatto rule is such a rule, so this bounds its weight at the node nearest to
$1$ (`Polynomial.exists_eval_derivative_legendre_eq_zero_near_one`).

The proof is the Christoffel-function bound
`Quadrature.weight_mul_eval_sq_le_of_isExactOnMeasure` with the test polynomial $K_M(\cdot, 1)$,
$M = \lfloor N/16 \rfloor$:
$$w_j \le \frac{\int K_M^2}{K_M(x_j, 1)^2} \le \frac{(M+1)^2/2}{\bigl((M+1)^2/4\bigr)^2} =
  \frac{8}{(M+1)^2} < \frac{2048}{N^2}.$$
The hypothesis of `Polynomial.le_eval_legendreKernelOne` holds for every $k \le M$, because
$k^2(1 - x_j) \le (N/16)^2 \cdot 81\pi^2/(32N^2) \le 1/2$ by $\pi \le 4$. The Legendre weight is
`OrthogonalPolynomial.legendreMeasure`. -/
theorem legendreLobattoWeight_le_of_near_one {N : ℕ} (hN : 1 ≤ N) {x w : Fin (N + 1) → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hexact : IsExactOnMeasure legendreMeasure w x (2 * N - 1))
    (j : Fin (N + 1)) (hxj : x j ∈ Icc (-1 : ℝ) 1)
    (hnear : 1 - x j ≤ 81 * π ^ 2 / (32 * (N : ℝ) ^ 2)) :
    w j ≤ 2048 / (N : ℝ) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set M := N / 16 with hM
  have hM16 : 16 * M ≤ N := by omega
  have hNM : N < 16 * (M + 1) := by omega
  have hMR : 16 * (M : ℝ) ≤ N := by exact_mod_cast hM16
  have hNMR : (N : ℝ) < 16 * ((M : ℝ) + 1) := by exact_mod_cast hNM
  -- the smallness hypothesis
  have hsmall : ∀ k ≤ M, (k : ℝ) ^ 2 * (1 - x j) ≤ 1 / 2 := by
    intro k hk
    have hkR : (k : ℝ) ≤ M := by exact_mod_cast hk
    have hpi := pi_le_four
    have hpi2 : π ^ 2 ≤ 16 := by nlinarith [pi_pos]
    have h1 : (k : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 / 256 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    have h2 : 0 ≤ 1 - x j := by linarith [hxj.2]
    have h3 : 81 * π ^ 2 / (32 * (N : ℝ) ^ 2) ≤ 81 * 16 / (32 * (N : ℝ) ^ 2) := by gcongr
    calc (k : ℝ) ^ 2 * (1 - x j) ≤ (N : ℝ) ^ 2 / 256 * (81 * 16 / (32 * (N : ℝ) ^ 2)) :=
          mul_le_mul h1 (hnear.trans h3) h2 (by positivity)
      _ = 81 / 512 := by field_simp; ring
      _ ≤ 1 / 2 := by norm_num
  have hK := Polynomial.le_eval_legendreKernelOne M hxj hsmall
  have hdeg : (Polynomial.legendreKernelOne M * Polynomial.legendreKernelOne M).degree ≤
      ((2 * N - 1 : ℕ) : WithBot ℕ) := by
    refine (degree_mul_le _ _).trans ?_
    have h1 := degree_le_of_natDegree_le (Polynomial.natDegree_legendreKernelOne_le M)
    calc (Polynomial.legendreKernelOne M).degree + (Polynomial.legendreKernelOne M).degree
        ≤ (M : WithBot ℕ) + (M : WithBot ℕ) := add_le_add h1 h1
      _ = ((M + M : ℕ) : WithBot ℕ) := by push_cast; rfl
      _ ≤ ((2 * N - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : M + M ≤ 2 * N - 1)
  have hbound := weight_mul_eval_sq_le_of_isExactOnMeasure hw hexact hdeg j
  rw [integral_legendreMeasure, Polynomial.integral_legendreKernelOne_sq] at hbound
  -- `w_j ≤ ((M+1)²/2) / K(x_j)² ≤ 8/(M+1)²`
  have hw8 : w j ≤ 8 / ((M : ℝ) + 1) ^ 2 := by
    have hKsq : ((M : ℝ) + 1) ^ 4 / 16 ≤ (Polynomial.legendreKernelOne M).eval (x j) ^ 2 := by
      calc ((M : ℝ) + 1) ^ 4 / 16 = (((M : ℝ) + 1) ^ 2 / 4) ^ 2 := by ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hK 2
    have := mul_le_mul_of_nonneg_left hKsq (hw j)
    rw [le_div_iff₀ (by positivity)]
    calc w j * ((M : ℝ) + 1) ^ 2 = w j * (((M : ℝ) + 1) ^ 4 / 16) * (16 / ((M : ℝ) + 1) ^ 2) := by
          field_simp
      _ ≤ (((M : ℝ) + 1) ^ 2 / 2) * (16 / ((M : ℝ) + 1) ^ 2) := by
          exact mul_le_mul_of_nonneg_right (this.trans hbound) (by positivity)
      _ = 8 := by field_simp; ring
  refine hw8.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hNMR, hNR]

end Quadrature
