import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Numlib.Approximation.CompositeQuadrature
import Numlib.Conditioning.Method
import Numlib.FiniteDifference.LaxEquivalence
import NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section01

/-!
# Quarteroni–Sacco–Saleri §2.2: stability of numerical methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §2.2 and §2.2.1. A numerical method for the problem `F(x, d) = 0` is a
sequence of approximate problems `F_n(x_n, d_n) = 0`; the book's consistency (2.13), strong
consistency and its multistep form (2.14), the condition numbers `K_n`, `K_{abs,n}` of (2.17) and
the asymptotic ones `K^num`, and the convergence of Definition 2.2 are the backbone
`Numlib/Conditioning/Method` (on top of `Numlib/Conditioning/Problem`), read here over `ℝ` and on
the book's concrete methods. The datum is fixed and does not vary with `n`, as in the backbone:
the book's `d_n` is `d`.

## Definitions and their bridges

* `definition_2_2` — convergence of a numerical method, (2.20), verbatim; it is the backbone's
  `Conditioning.IsConvergent` by `Iff.rfl` (`definition_2_2_iff`).
* `equation_2_19`, `equation_2_19_abs` — the first-order formulas for `K_n` and `K_{abs,n}`, which
  are (2.7) applied to the resolvent `G_n` of the `n`-th approximate problem.

## The relations between stability and convergence (§2.2.1)

* `equation_2_21` — the sufficient criterion for convergence: (2.3) at `d` and uniform closeness
  of `x_n(d + δd)` to `x(d + δd)`.
* `equation_2_24` — a convergent method is stable, in the equicontinuity sense of
  `Conditioning.IsStable`: only that follows from (2.20), not the Lipschitz bound the book's
  text concludes (see the module `Numlib/Conditioning/Method` and `notes/book-errata.md`).
* `equation_2_25` — a consistent method with a uniform inverse bound on `∂F_n/∂x` has
  `x_n(d) → x(d)`; the uniform `AntilipschitzWith` hypothesis is the rigorous content of the
  book's mean-value argument, which is only scalar.
* `laxRichtmyerEquivalence` — "for a consistent numerical method, stability is equivalent to
  convergence", in the book's abstract setting; `laxRichtmyerEquivalence_ivp` is the theorem of
  Lax and Richtmyer for linear well-posed initial value problems that the book refers to, the
  backbone's `FiniteDifference.isStable_iff_isConvergent` over `ℝ`.

## The Examples

* `example_2_5_newton` — Newton's method (2.15), written in the two-step form (2.14) as
  `example_2_5_newtonResidual`, is strongly consistent.
* `example_2_5_midpoint_consistent`, `example_2_5_midpoint_stronglyConsistent` — the composite
  midpoint rule `example_2_5_midpointRule` is consistent for every continuous integrand and
  strongly consistent for the *affine* integrands. The book says "provided that `f` is a piecewise
  linear polynomial", which is false for a kink that is not a mesh point of every mesh (`|t|` on
  `[-1, 1]` with one panel); affine is the correct hypothesis. The book's rule is indexed by
  `n ≥ 1` panels; the method's `n`-th problem here uses `n + 1` panels, so that the family is
  indexed by `ℕ` as the backbone's methods are.
* `example_2_6`, `example_2_6_same_sign` — the condition number of the sum `f(a, b) = a + b` in the
  `1`-norm of (1.13) is `(|a| + |b|) / |a + b|`, exactly, and `1` when `a` and `b` have the same
  sign.
* `example_2_7_prod`, `example_2_7` — `x₋ = 1 / x₊` (the stable formula for the smaller root), and
  the asymptotic condition number of Newton's method on `x² - 2px + 1 = 0`: with the previous
  iterate frozen at a root, the Newton step `example_2_7_newtonStep` as a function of `p` has
  relative condition number `|p| / √(p² - 1)`, "in perfect agreement with the value (2.8)". This is
  the limit `K^num(p)` the book computes; its intermediate `K_n(p) ≃ |p| / |x_n - p|` is exact at
  a root and heuristic away from it, and is not a node.
-/

open Conditioning Filter Set Topology
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter02

/-! ### Example 2.5: Newton's method, and the composite midpoint rule -/

/-- Newton's method (2.15) written in the two-step form (2.14): the residual
`F_n(x_n, x_{n-1}, f) = x_n - x_{n-1} + f(x_{n-1}) / f'(x_{n-1})`, the datum being the function
`f` whose simple root is sought. `x 0` is `x_n` and `x 1` is `x_{n-1}`; the index `n` plays no
role. -/
noncomputable def example_2_5_newtonResidual (_n : ℕ) (x : Fin 2 → ℝ) (f : ℝ → ℝ) : ℝ :=
  x 0 - x 1 + f (x 1) / deriv f (x 1)

/-- **Example 2.5, Newton's method is strongly consistent**: for every root `α` of `f`,
`F_n(α, α, f) = 0` for all `n`, since `f(α) = 0`. -/
theorem example_2_5_newton :
    IsStronglyConsistentMultistep (q := 1) (fun x (f : ℝ → ℝ) => f x) example_2_5_newtonResidual
      univ := by
  intro f _ x hx n
  simp [example_2_5_newtonResidual, hx]

/-- The composite midpoint rule of Example 2.5 with `n` panels on `[a, b]`,
`x_n = H ∑_{k=1}^n f((t_k + t_{k+1}) / 2)` with `H = (b - a) / n` and `t_k = a + (k - 1) H`, on
the datum space `C([a, b], ℝ)`; the midpoints are placed in `[a, b]` by `Set.projIcc`, which is
the identity there. For `n = 0` the sum is empty. -/
noncomputable def example_2_5_midpointRule {a b : ℝ} (hab : a ≤ b) (n : ℕ) (f : C(Icc a b, ℝ)) :
    ℝ :=
  (b - a) / n * ∑ k ∈ Finset.range n, f (projIcc a b hab (a + (k + 1 / 2) * ((b - a) / n)))

/-- **Example 2.5, the composite midpoint rule is consistent**: for the problem
`x - ∫_a^b f = 0` on the continuous integrands, the residual `∫_a^b f - M_{n+1} f` of the
approximate problem `x - M_{n+1} f = 0` tends to zero, i.e. the midpoint sums converge to the
integral for every continuous `f`. This is the Riemann sum theorem
`Quadrature.tendsto_compositeSum` on the uniform mesh with one node per panel, the midpoint, of
weight `1`. -/
theorem example_2_5_midpoint_consistent {a b : ℝ} (hab : a ≤ b) :
    IsConsistent (fun (x : ℝ) (f : C(Icc a b, ℝ)) => x - ∫ t in a..b, f (projIcc a b hab t))
      (fun n x f => x - example_2_5_midpointRule hab (n + 1) f) univ := by
  intro f _ x hx
  rw [sub_eq_zero] at hx
  subst hx
  have hg : ContinuousOn (fun t => f (projIcc a b hab t)) (Icc a b) :=
    (f.continuous.comp continuous_projIcc).continuousOn
  have hH : ∀ n : ℕ, 0 ≤ (b - a) / ((n : ℝ) + 1) := fun n => by
    have : 0 ≤ b - a := by linarith
    positivity
  have hlim : Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp
  have hmain := Quadrature.tendsto_compositeSum (a := a) (b := b) hab hg (N := fun n => n + 1)
    (t := fun n j => a + j * ((b - a) / ((n : ℝ) + 1))) (hs := fun n => (b - a) / ((n : ℝ) + 1))
    (fun n => by simp)
    (fun n => by
      have : ((n : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring)
    (fun n j _ => by push_cast; nlinarith [hH n])
    (fun n j _ => by push_cast; nlinarith [hH n]) hlim (ω := fun _ : Fin 1 => 1)
    (fun _ => zero_le_one) (by simp)
    (y := fun n j _ => a + (j + 1 / 2) * ((b - a) / ((n : ℝ) + 1)))
    (fun n j _ i => by
      constructor
      · nlinarith [hH n]
      · push_cast
        nlinarith [hH n])
  have hM : Tendsto (fun n => example_2_5_midpointRule hab (n + 1) f) atTop
      (𝓝 (∫ t in a..b, f (projIcc a b hab t))) := by
    refine hmain.congr fun n => ?_
    rw [example_2_5_midpointRule, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.sum_univ_one, one_mul]
    push_cast
    ring_nf
  have := (tendsto_const_nhds (x := ∫ t in a..b, f (projIcc a b hab t))).sub hM
  rwa [sub_self] at this

/-- **Example 2.5, strong consistency of the midpoint rule for affine integrands**: on the
admissible data `{f | f t = c₀ + c₁ t}` the method `x - M_{n+1} f = 0` is strongly consistent,
because the midpoint rule integrates affine functions exactly on every panel:
`M_{n+1} f = ∫_a^b f` for every `n`. The book says "provided that `f` is a piecewise linear
polynomial", which is false when a kink of `f` is not a mesh point (`|t|` on `[-1, 1]` with one
panel gives `2 f(0) = 0 ≠ 1`); affine — equivalently, linear on every panel of every mesh — is the
correct hypothesis. -/
theorem example_2_5_midpoint_stronglyConsistent {a b : ℝ} (hab : a ≤ b) :
    IsStronglyConsistent
      (fun (x : ℝ) (f : C(Icc a b, ℝ)) => x - ∫ t in a..b, f (projIcc a b hab t))
      (fun n x f => x - example_2_5_midpointRule hab (n + 1) f)
      {f | ∃ c₀ c₁ : ℝ, ∀ t : Icc a b, f t = c₀ + c₁ * t} := by
  rintro f ⟨c₀, c₁, hf⟩ x hx n
  rw [sub_eq_zero] at hx
  subst hx
  rw [sub_eq_zero]
  have hint : ∫ t in a..b, f (projIcc a b hab t) = c₀ * (b - a) + c₁ * ((b ^ 2 - a ^ 2) / 2) := by
    rw [intervalIntegral.integral_congr (g := fun t => c₀ + c₁ * t) fun t ht => ?_]
    · rw [intervalIntegral.integral_add intervalIntegrable_const
        ((by fun_prop : Continuous fun x : ℝ => c₁ * x).intervalIntegrable _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
        smul_eq_mul, mul_comm (b - a)]
    · rw [uIcc_of_le hab] at ht
      simp only
      rw [projIcc_of_mem hab ht, hf]
  have key : ∀ m : ℕ, ∑ k ∈ Finset.range m, ((k : ℝ) + 1 / 2) = (m : ℝ) ^ 2 / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  set H : ℝ := (b - a) / ((n : ℝ) + 1) with hH
  have hH0 : 0 ≤ H := by
    have : 0 ≤ b - a := by linarith
    positivity
  have hmem : ∀ k ∈ Finset.range (n + 1), a + (k + 1 / 2) * H ∈ Icc a b := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have := Finset.mem_range.1 hk
      exact_mod_cast this
    have hHn : ((n : ℝ) + 1) * H = b - a := by
      rw [hH]; field_simp
    constructor
    · nlinarith
    · nlinarith
  rw [example_2_5_midpointRule, hint]
  push_cast
  rw [← hH, Finset.sum_congr rfl (g := fun k : ℕ => (c₀ + c₁ * a) + (c₁ * H) * ((k : ℝ) + 1 / 2))
    fun k hk => by rw [projIcc_of_mem hab (hmem k hk), hf]; simp only; ring,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum, key,
    nsmul_eq_mul]
  push_cast
  rw [hH]
  field_simp
  ring

/-! ### (2.19): the condition numbers of the approximate problems -/

section Equation219

variable {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup X]
  [NormedSpace ℝ X] {Gn : ℕ → D → X} {n : ℕ} {G' : D →L[ℝ] X} {d : D} {S : Set D}

/-- **(2.19), relative form.** For the resolvent `G_n` of the `n`-th approximate problem (2.18),
differentiable at the datum `d` interior to the admissible data, with `d ≠ 0` and `G_n(d) ≠ 0`,
`K_n(d) ≃ ‖G_n'(d)‖ ‖d‖ / ‖G_n(d)‖`: the first-order formula for the condition number (2.17) of
the approximate problem is (2.7) applied to `G_n`. -/
theorem equation_2_19 (hG : HasFDerivAt (Gn n) G' d) (hS : S ∈ 𝓝 d) (hd : d ≠ 0)
    (hx : Gn n d ≠ 0) : relCondNumber (Gn n) S d = ‖G'‖ₑ * (‖d‖ₑ / ‖Gn n d‖ₑ) :=
  equation_2_7_rel hG hS hd hx

/-- **(2.19), absolute form.** Under the same hypotheses, `K_{abs,n}(d) ≃ ‖G_n'(d)‖`. -/
theorem equation_2_19_abs (hG : HasFDerivAt (Gn n) G' d) (hS : S ∈ 𝓝 d) :
    absCondNumber (Gn n) S d = ‖G'‖ₑ :=
  equation_2_7_abs hG hS

end Equation219

/-! ### Example 2.6: sum and subtraction -/

/-- **Example 2.6 (sum and subtraction).** The sum `f(a, b) = a + b` is a linear map with gradient
`(1, 1)ᵀ`; in the vector norm `‖·‖₁` of (1.13) its condition number at `(a, b)` with `a + b ≠ 0`
is `K(a, b) ≃ (|a| + |b|) / |a + b|` — exactly, since the operator norm of `f` from `ℓ¹` to `ℝ` is
`1`. "Subtracting two numbers almost equal is ill conditioned, since `|a + b| ≪ |a| + |b|`." -/
theorem example_2_6 {a b : ℝ} (hab : a + b ≠ 0) :
    relCondNumber (fun x : WithLp 1 (ℝ × ℝ) => x.fst + x.snd) univ (WithLp.toLp 1 (a, b)) =
      ENNReal.ofReal ((|a| + |b|) / |a + b|) := by
  set L : WithLp 1 (ℝ × ℝ) →L[ℝ] ℝ := WithLp.fstL 1 ℝ ℝ ℝ + WithLp.sndL 1 ℝ ℝ ℝ with hL
  have hL1 : ‖L‖ = 1 := by
    refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_) ?_
    · rw [one_mul, WithLp.prod_norm_eq_of_L1]
      simpa [hL] using abs_add_le x.fst x.snd
    · have := L.le_opNorm (WithLp.toLp 1 ((1 : ℝ), (0 : ℝ)))
      simpa [hL, WithLp.prod_norm_eq_of_L1] using this
  have hd : WithLp.toLp 1 (a, b) ≠ (0 : WithLp 1 (ℝ × ℝ)) := by
    intro h
    apply hab
    have := congrArg (fun x : WithLp 1 (ℝ × ℝ) => x.fst + x.snd) h
    simpa using this
  have hx : (fun x : WithLp 1 (ℝ × ℝ) => x.fst + x.snd) (WithLp.toLp 1 (a, b)) ≠ 0 := by
    simpa using hab
  have hderiv : HasFDerivAt (fun x : WithLp 1 (ℝ × ℝ) => x.fst + x.snd) L
      (WithLp.toLp 1 (a, b)) :=
    L.hasFDerivAt
  rw [equation_2_7_rel hderiv univ_mem hd hx, ← ofReal_norm, hL1, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_div_of_pos (norm_pos_iff.2 hx), ← ENNReal.ofReal_mul zero_le_one, one_mul,
    WithLp.prod_norm_eq_of_L1]
  simp [Real.norm_eq_abs]

/-- **Example 2.6, same signs.** "Summing two numbers of the same sign is a well conditioned
operation, being `K(a, b) ≃ 1`": for `0 ≤ a b` and `(a, b) ≠ 0`, `|a + b| = |a| + |b|` and the
condition number is `1`. -/
theorem example_2_6_same_sign {a b : ℝ} (hab : 0 ≤ a * b) (h0 : (a, b) ≠ (0 : ℝ × ℝ)) :
    relCondNumber (fun x : WithLp 1 (ℝ × ℝ) => x.fst + x.snd) univ (WithLp.toLp 1 (a, b)) =
      1 := by
  have habs : |a + b| = |a| + |b| := (abs_add_eq_add_abs_iff a b).2 (mul_nonneg_iff.1 hab)
  have hne : a + b ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    have ha : a = 0 := abs_eq_zero.1 (by linarith [abs_nonneg a, abs_nonneg b])
    have hb : b = 0 := abs_eq_zero.1 (by linarith [abs_nonneg a, abs_nonneg b])
    exact h0 (by rw [ha, hb]; rfl)
  rw [example_2_6 hne, habs, div_self (by rw [← habs]; exact abs_ne_zero.2 hne),
    ENNReal.ofReal_one]

/-! ### Example 2.7: the roots of `x² - 2px + 1` by Newton's method -/

/-- **Example 2.7, the stable formula for `x₋`.** For `p ≥ 1`, `x₊ x₋ = 1`, so the smaller root
can be computed as `x₋ = 1 / x₊` from `x₊ = p + √(p² - 1)`, avoiding the cancellation in
`p - √(p² - 1)`. -/
theorem example_2_7_prod {p : ℝ} (hp : 1 ≤ p) :
    (p + √(p ^ 2 - 1)) * (p - √(p ^ 2 - 1)) = 1 := by
  have hs : √(p ^ 2 - 1) * √(p ^ 2 - 1) = p ^ 2 - 1 := Real.mul_self_sqrt (by nlinarith)
  linear_combination (-1 : ℝ) * hs

/-- One step of Newton's method for `x² - 2px + 1 = 0`, as a function of the datum `p` and the
previous iterate `x`: `x_n = x_{n-1} - (x_{n-1}² - 2p x_{n-1} + 1) / (2 x_{n-1} - 2p) = f_n(p)` of
Example 2.7, with `x_{n-1} = x` held fixed. -/
noncomputable def example_2_7_newtonStep (p x : ℝ) : ℝ :=
  x - (x ^ 2 - 2 * p * x + 1) / (2 * x - 2 * p)

/-- **Example 2.7, the asymptotic condition number of Newton's method on `x² - 2px + 1 = 0`.**
For `p > 1` and the previous iterate frozen at one of the roots `x = p ± √(p² - 1)` — the limit
the book's `K_n(p) → K^num(p)` computes, "since in the case when the algorithm converges the
solution `x_n` would converge to one of the roots" — the Newton step as a function of `p` has
relative condition number `|p| / √(p² - 1)`, "in perfect agreement with the value (2.8) of the
condition number of the exact problem". By (2.19): `∂f_n/∂p = (x² - 1) / (2 (x - p)²)`, and at a
root `x² - 1 = 2(px - 1)`, `(x - p)² = p² - 1` and `f_n(p) = x`. Newton's method for this
equation "is ill conditioned if `|p|` is very close to `1`, well conditioned in the other cases".
-/
theorem example_2_7 {p x : ℝ} (hp : 1 < p) (hx : x = p + √(p ^ 2 - 1) ∨ x = p - √(p ^ 2 - 1)) :
    relCondNumber (fun q => example_2_7_newtonStep q x) univ p =
      ENNReal.ofReal (|p| / √(p ^ 2 - 1)) := by
  have h1 : 0 < p ^ 2 - 1 := by nlinarith
  set s := √(p ^ 2 - 1) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 h1
  have hs2 : s ^ 2 = p ^ 2 - 1 := Real.sq_sqrt h1.le
  have hxp : (x - p) ^ 2 = s ^ 2 := by rcases hx with rfl | rfl <;> ring
  have hroot : x ^ 2 - 2 * p * x + 1 = 0 := by nlinarith
  have hxp0 : x - p ≠ 0 := by
    intro h; rw [h] at hxp; nlinarith
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at hroot; norm_num at hroot
  have hp0 : 0 < p := by linarith
  have hden0 : 2 * x - 2 * p ≠ 0 := by
    intro h; apply hxp0; linarith
  have hd : HasDerivAt (fun q => example_2_7_newtonStep q x) ((x ^ 2 - 1) / (2 * (x - p) ^ 2))
      p := by
    have hnum : HasDerivAt (fun q : ℝ => x ^ 2 - 2 * q * x + 1) (0 - 2 * 1 * x) p :=
      ((hasDerivAt_const p (x ^ 2)).sub (((hasDerivAt_id' p).const_mul 2).mul_const x)).add_const 1
    have hden : HasDerivAt (fun q : ℝ => 2 * x - 2 * q) (0 - 2 * 1) p :=
      (hasDerivAt_const p (2 * x)).sub ((hasDerivAt_id' p).const_mul 2)
    refine ((hasDerivAt_const p x).sub (hnum.div hden hden0)).congr_deriv ?_
    field_simp
    ring
  have hG : example_2_7_newtonStep p x ≠ 0 := by
    simp only [example_2_7_newtonStep, hroot, zero_div, sub_zero]; exact hx0
  rw [equation_2_7_rel_deriv hd hp0.ne' hG]
  congr 1
  have hGp : example_2_7_newtonStep p x = x := by simp [example_2_7_newtonStep, hroot]
  have hx21 : x ^ 2 - 1 = 2 * (p * x - 1) := by linarith
  have habs : |p * x - 1| = s * |x| := by
    rw [← abs_of_pos hs, ← abs_mul, ← sq_eq_sq_iff_abs_eq_abs]
    nlinarith
  rw [hGp, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, hx21, abs_mul, abs_two, habs, hxp,
    abs_of_pos (by positivity : 0 < 2 * s ^ 2)]
  field_simp

/-! ### Definition 2.2 and §2.2.1: stability and convergence -/

section Convergence

variable {D X : Type*} [NormedAddCommGroup D] [NormedAddCommGroup X] {G : D → X}
  {Gn : ℕ → D → X} {S : Set D} {d : D}

/-- **Definition 2.2, (2.20).** The numerical method (2.12) with resolvents `G_n` is *convergent*
at the admissible datum `d` of the problem with resolvent `G` iff for every `ε > 0` there are
`n₀(ε)` and `δ(n₀, ε) > 0` such that for every `n > n₀` and every admissible perturbation
`‖δd_n‖ < δ`, `‖x(d) - x_n(d + δd_n)‖ ≤ ε`, where `x(d) = G d` is the exact solution and
`x_n(d + δd_n) = G_n (d + δd_n)` the numerical solution with the perturbed datum. This is the
backbone's `Conditioning.IsConvergent` (`definition_2_2_iff`). -/
def definition_2_2 (G : D → X) (Gn : ℕ → D → X) (S : Set D) (d : D) : Prop :=
  ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∃ δ > (0 : ℝ), ∀ n > n₀, ∀ δd, ‖δd‖ < δ → d + δd ∈ S →
    ‖G d - Gn n (d + δd)‖ ≤ ε

/-- Definition 2.2 is the backbone's `Conditioning.IsConvergent`. -/
theorem definition_2_2_iff : definition_2_2 G Gn S d ↔ IsConvergent G Gn S d :=
  Iff.rfl

/-- **(2.21), the sufficient criterion for convergence.** If the problem satisfies (2.3) at `d`
(the absolute condition number over some radius is finite, `equation_2_3_iff`) and "under the
same assumptions" `‖x(d + δd_n) - x_n(d + δd_n)‖ ≤ ε / 2`, then the method is convergent:
`‖x(d) - x_n(d + δd_n)‖ ≤ K(δ, d) ‖δd_n‖ + ε / 2`, and `δd_n` can be chosen so that the first
term is `< ε / 2`. -/
theorem equation_2_21 (hK : ∃ η > (0 : ℝ), absCondNumberWithin G S d η ≠ ⊤)
    (h : ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∃ δ > (0 : ℝ), ∀ n > n₀, ∀ δd, ‖δd‖ < δ → d + δd ∈ S →
      ‖G (d + δd) - Gn n (d + δd)‖ ≤ ε / 2) :
    definition_2_2 G Gn S d := by
  obtain ⟨η, hη, hK⟩ := hK
  refine isConvergent_of_forall_norm_sub_le (continuousWithinAt_of_absCondNumberWithin_ne_top hη hK)
    fun ε hε => ?_
  obtain ⟨n₀, δ, hδ, h⟩ := h ε hε
  exact ⟨n₀, δ, hδ, fun n hn δd hδd hS => (h n hn δd hδd hS).trans (by linarith)⟩

/-- **§2.2.1, stability is necessary for convergence ((2.24)).** A convergent method is stable
at the admissible datum `d`: for `n` large the numerical solutions depend continuously on the
data, uniformly in `n`. From (2.24) with (2.20) applied twice,
`‖δx_n‖ ≤ ‖x_n(d) - x(d)‖ + ‖x(d) - x_n(d + δd_n)‖ ≤ 2ε`. The book concludes a Lipschitz
bound "of the order of `K(δ, d)`", which does not follow from (2.20); equicontinuity, the
backbone's `Conditioning.IsStable`, does. -/
theorem equation_2_24 (hd : d ∈ S) (h : definition_2_2 G Gn S d) : IsStable Gn S d :=
  ((definition_2_2_iff).1 h).isStable hd

end Convergence

section Consistency

variable {D X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {F : X → D → Y}
  {Fn : ℕ → X → D → Y} {G : D → X} {Gn : ℕ → D → X} {S : Set D} {d : D}

/-- **§2.2.1, consistency gives `x_n(d) → x(d)` ((2.25)).** If `x(d) = G d` solves the problem,
`x_n(d) = G_n d` solves the `n`-th approximate problem, the method is consistent, and the
approximate problems have a uniform inverse bound `‖x - y‖ ≤ M ‖F_n(x, d) - F_n(y, d)‖` — the
rigorous form of the book's "`∂F_n/∂x` invertible" with `‖(∂F_n/∂x)⁻¹‖ ≤ M`, whose mean-value
identity (2.25) holds only for scalar `F_n` — then
`‖x(d) - x_n(d)‖ ≤ M ‖F_n(x(d), d) - F(x(d), d)‖ → 0` by (2.13). -/
theorem equation_2_25 (hd : d ∈ S) (hF : F (G d) d = 0) (hFn : ∀ n, Fn n (Gn n d) d = 0)
    (hcons : IsConsistent F Fn S) {M : NNReal}
    (hanti : ∀ n, AntilipschitzWith M fun x => Fn n x d) :
    Tendsto (fun n => Gn n d) atTop (𝓝 (G d)) :=
  tendsto_of_isConsistent hd hF hFn hcons hanti

variable [NormedAddCommGroup D]

/-- **§2.2.1, the equivalence theorem in the book's abstract setting**: "for a consistent
numerical method, stability is equivalent to convergence". For a consistent method whose
approximate problems admit a uniform inverse bound at the admissible datum `d`, stability at `d`
(`Conditioning.IsStable`) and convergence at `d` (Definition 2.2) are the same. The two halves
are `equation_2_24` and the sufficient condition of §2.2.1, stability plus `equation_2_25`. -/
theorem laxRichtmyerEquivalence (hd : d ∈ S) (hF : F (G d) d = 0)
    (hFn : ∀ n, Fn n (Gn n d) d = 0) (hcons : IsConsistent F Fn S) {M : NNReal}
    (hanti : ∀ n, AntilipschitzWith M fun x => Fn n x d) :
    IsStable Gn S d ↔ definition_2_2 G Gn S d :=
  isStable_iff_isConvergent hd hF hFn hcons hanti

end Consistency

/-- **§2.2.1, the Lax–Richtmyer theorem for linear well-posed initial value problems** — the
"rigorous proof of this theorem … in [Lax65] and in [RM67]" the book refers to. For a real
Banach space `V`, an evolution family `S : ℝ → V →L[ℝ] V` with `S 0 = 1` and `t ↦ S t u`
continuous on `[0, T]`, and a one-step scheme `C : ℝ → V →L[ℝ] V` with `‖C Δt‖ ≤ c₁` for
`Δt ∈ (0, Δ₀]` that is consistent on a dense set of initial values, the scheme is stable
(`FiniteDifference.IsStable`: the powers `C Δt ^ m` with `m Δt ≤ T` are uniformly bounded) iff it
is convergent (`FiniteDifference.IsConvergent`). This is a different formal statement from
`laxRichtmyerEquivalence`, recorded under the same paragraph of the book; it is the backbone's
`FiniteDifference.isStable_iff_isConvergent` over `ℝ`. -/
theorem laxRichtmyerEquivalence_ivp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {S C : ℝ → V →L[ℝ] V} {T Δ₀ c₁ : ℝ} {D : Set V} (hT : 0 ≤ T)
    (hS0 : S 0 = 1) (hScont : ∀ u : V, ContinuousOn (fun t => S t u) (Icc 0 T))
    (hC : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖C Δt‖ ≤ c₁)
    (hcons : FiniteDifference.IsConsistent S C T Δ₀ D) :
    FiniteDifference.IsStable C T Δ₀ ↔ FiniteDifference.IsConvergent S C T Δ₀ :=
  FiniteDifference.isStable_iff_isConvergent hT hS0 hScont hC hcons

end QuarteroniSaccoSaleri.Chapter02
