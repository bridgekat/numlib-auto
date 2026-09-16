import Mathlib.LinearAlgebra.Lagrange
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Approximation.Quadrature

/-!
# Quarteroni–Sacco–Saleri §9.1: quadrature formulae

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §9.1.

The section sets up the vocabulary of the chapter: a quadrature formula `I_n(f) = ∫_a^b f_n`
obtained by integrating an approximant `f_n` of `f` (9.1), with the error bound
`|E_n(f)| ≤ ∫_a^b |f - f_n| ≤ (b - a) ‖f - f_n‖_∞`; the *Lagrange quadrature formula* (9.2),
`I_n(f) = ∑ᵢ f(xᵢ) ∫_a^b lᵢ`, obtained from the interpolating polynomial `Π_n f` at `n + 1` distinct
nodes; the general form (9.3), `I_n(f) = ∑ᵢ αᵢ f(xᵢ)`, with *nodes* `xᵢ` and *weights* `αᵢ`; the
*degree of exactness* of a formula, the largest `r` with `I_n(f) = I(f)` for every `f ∈ ℙ_r`; and
the two facts that an interpolatory formula on `n + 1` distinct nodes has degree of exactness at
least `n` and that, conversely, a formula on `n + 1` distinct nodes exact on `ℙ_n` is interpolatory
(the book cites [IK66], p. 316, for the converse).

The backbone has the whole story on `C([a, b], ℝ)`, in `Numlib/Approximation/Quadrature`: a rule
with weights `w` and nodes `x` is the functional `Quadrature.functional w x`, exactness on `ℙ_d` for
a target functional `L` is `Quadrature.IsExactOn L w x d`, "interpolatory" is
`Quadrature.IsInterpolatory L w x`, and the two facts are the two directions of
`Quadrature.isInterpolatory_iff_isExactOn`. The target functional here is the integral over
`[a, b]`, `ContinuousMap.integralIccCLM hab b` of `Numlib/Analysis/Calculus/ContDiffMapIcc`.

## Main definitions

* `lagrangeWeights x a b` — the weights `αᵢ = ∫_a^b lᵢ(x) dx` of (9.2)–(9.3).
* `lagrangeQuadrature x a b f` — the Lagrange quadrature formula (9.2), `∑ᵢ αᵢ f(xᵢ)`, for a real
  function `f` and real nodes `x : Fin (n + 1) → ℝ`.

## Main results

* `quadratureError_le_integral_abs`, `quadratureError_le` — the two halves of the unnumbered
  estimate `|E_n(f)| ≤ ∫_a^b |f - f_n| ≤ (b - a) ‖f - f_n‖_∞`, the second stated with any bound
  `M` on `|f - f_n|` over `[a, b]`, as the book uses it ("if `‖f - f_n‖_∞ < ε` then
  `|E_n(f)| ≤ ε (b - a)`").
* `lagrangeQuadrature_eq_integral_interpolate` — (9.1)–(9.2): the Lagrange quadrature formula is
  the integral of the interpolating polynomial.
* `isInterpolatory_lagrangeQuadrature`, `lagrangeQuadrature_eq_functional` — the formula read in
  the backbone's vocabulary: its weights are `∫ lᵢ`, so it is interpolatory for the integral on
  `C([a, b], ℝ)`, and its value at a continuous function is `Quadrature.functional` of it.
* `Quadrature.isExactOn_integralIccCLM_iff` (backbone) — "degree of exactness at least `d`" for a
  formula `∑ αᵢ f(xᵢ)` on `[a, b]`, stated on real polynomials, is `Quadrature.IsExactOn` for the
  integral functional.
* `degreeOfExactness_ge_of_interpolatory` — an interpolatory formula on `n + 1` distinct nodes is
  exact on `ℙ_n`.
* `isInterpolatory_of_degreeOfExactness` — a formula on `n + 1` distinct nodes exact on `ℙ_n` has
  the weights `∫ lᵢ`, i.e. is the Lagrange quadrature formula.

## Conventions

Nodes are real numbers `x : Fin (n + 1) → ℝ` in `[a, b]`, the book's `x₀, …, xₙ`, and "distinct"
is `Function.Injective x`; the characteristic Lagrange polynomial `lᵢ` of §8.1 is Mathlib's
`Lagrange.basis Finset.univ x i`, the interpolating polynomial `Π_n f` is
`Lagrange.interpolate Finset.univ x (fun i => f (x i))`, and `f ∈ ℙ_r` is `p.degree ≤ r` for a
real polynomial `p`. The bridge to the backbone reads the nodes as points of the subtype `Icc a b`
and a real function on `[a, b]` as the continuous map it restricts to; `Set.IccExtend` goes the
other way.
-/

open Set intervalIntegral
open scoped Polynomial

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {n : ℕ}

/-! ### The quadrature error of an approximant -/

/-- **§9.1, the unnumbered estimate, first half.** For `f ∈ C⁰([a, b])` and a continuous
approximant `f_n`, the quadrature error `E_n(f) = I(f) - I_n(f)` of the formula (9.1),
`I_n(f) = ∫_a^b f_n`, satisfies `|E_n(f)| ≤ ∫_a^b |f(x) - f_n(x)| dx`. -/
theorem quadratureError_le_integral_abs (hab : a ≤ b) {f fn : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfn : ContinuousOn fn (Icc a b)) :
    |(∫ x in a..b, f x) - ∫ x in a..b, fn x| ≤ ∫ x in a..b, |f x - fn x| := by
  rw [← integral_sub (hf.intervalIntegrable_of_Icc hab) (hfn.intervalIntegrable_of_Icc hab)]
  exact abs_integral_le_integral_abs hab

/-- **§9.1, the unnumbered estimate.** For `f ∈ C⁰([a, b])` and a continuous approximant `f_n`
with `|f - f_n| ≤ M` on `[a, b]` — in particular for `M = ‖f - f_n‖_∞` — the quadrature error of
(9.1) satisfies `|E_n(f)| ≤ (b - a) M`; so if `‖f - f_n‖_∞ < ε` for some `n`, then
`|E_n(f)| ≤ ε (b - a)`. -/
theorem quadratureError_le (hab : a ≤ b) {f fn : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hfn : ContinuousOn fn (Icc a b)) {M : ℝ} (hM : ∀ x ∈ Icc a b, |f x - fn x| ≤ M) :
    |(∫ x in a..b, f x) - ∫ x in a..b, fn x| ≤ (b - a) * M := by
  rw [← integral_sub (hf.intervalIntegrable_of_Icc hab) (hfn.intervalIntegrable_of_Icc hab)]
  have h := norm_integral_le_of_norm_le_const (a := a) (b := b) (f := fun x => f x - fn x)
    (C := M) fun x hx => by
      rw [uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      exact hM x (Ioc_subset_Icc_self hx)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab), mul_comm] at h
  exact h

/-! ### The Lagrange quadrature formula (9.2)–(9.3) -/

/-- The **weights of the Lagrange quadrature formula**, `αᵢ = ∫_a^b lᵢ(x) dx` in (9.2)–(9.3):
the integrals over `[a, b]` of the characteristic Lagrange polynomials `lᵢ` of the nodes
`x₀, …, xₙ` (§8.1). -/
noncomputable def lagrangeWeights (x : Fin (n + 1) → ℝ) (a b : ℝ) (i : Fin (n + 1)) : ℝ :=
  ∫ t in a..b, (Lagrange.basis Finset.univ x i).eval t

/-- **The Lagrange quadrature formula (9.2)**, `I_n(f) = ∑ᵢ₌₀ⁿ f(xᵢ) ∫_a^b lᵢ(x) dx`, an instance
of the general formula (9.3), `I_n(f) = ∑ᵢ αᵢ f(xᵢ)`, with the weights `αᵢ = ∫_a^b lᵢ` of
`lagrangeWeights`. -/
noncomputable def lagrangeQuadrature (x : Fin (n + 1) → ℝ) (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, lagrangeWeights x a b i * f (x i)

/-- The Lagrange quadrature formula written out as in (9.2). -/
theorem lagrangeQuadrature_def (x : Fin (n + 1) → ℝ) (a b : ℝ) (f : ℝ → ℝ) :
    lagrangeQuadrature x a b f
      = ∑ i, (∫ t in a..b, (Lagrange.basis Finset.univ x i).eval t) * f (x i) := rfl

/-- **(9.1)–(9.2).** The Lagrange quadrature formula is the formula (9.1) with `f_n = Π_n f`, the
interpolating Lagrange polynomial of `f` at the nodes: `I_n(f) = ∫_a^b Π_n f(x) dx`. This is the
linearity of the integral over the Lagrange form `Π_n f = ∑ᵢ f(xᵢ) lᵢ`. -/
theorem lagrangeQuadrature_eq_integral_interpolate (x : Fin (n + 1) → ℝ) (a b : ℝ) (f : ℝ → ℝ) :
    lagrangeQuadrature x a b f
      = ∫ t in a..b, (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t := by
  simp only [lagrangeQuadrature, lagrangeWeights, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  rw [integral_finsetSum fun i _ =>
    ((Polynomial.continuous _).const_mul (f (x i))).intervalIntegrable _ _]
  simp_rw [integral_const_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ### The formula in the backbone's vocabulary -/

/-- **The Lagrange quadrature formula is interpolatory**, in the sense of the backbone's
`Quadrature.IsInterpolatory` on `C([a, b], ℝ)` for the integral functional
`ContinuousMap.integralIccCLM hab b`: its weights `∫_a^b lᵢ` are the integrals of the Lagrange
basis functions `Lagrange.basisCM` of the nodes, read as points of `[a, b]`. -/
theorem isInterpolatory_lagrangeQuadrature (hab : a ≤ b) {x : Fin (n + 1) → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) :
    Quadrature.IsInterpolatory (ContinuousMap.integralIccCLM hab b) (lagrangeWeights x a b)
      fun i => (⟨x i, hx i⟩ : Icc a b) := by
  intro i
  rw [ContinuousMap.integralIccCLM_apply, lagrangeWeights]
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  rw [ContinuousMap.coe_IccExtend, IccExtend_of_mem hab _ ht, Lagrange.basisCM_apply]

/-- The value of the Lagrange quadrature formula at a continuous function on `[a, b]` is the
backbone rule `Quadrature.functional` with the weights `∫ lᵢ` at the nodes. -/
theorem lagrangeQuadrature_eq_functional (hab : a ≤ b) {x : Fin (n + 1) → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) (f : C(Icc a b, ℝ)) :
    lagrangeQuadrature x a b (IccExtend hab f)
      = Quadrature.functional (lagrangeWeights x a b) (fun i => (⟨x i, hx i⟩ : Icc a b)) f := by
  rw [Quadrature.functional_apply, lagrangeQuadrature]
  exact Finset.sum_congr rfl fun i _ => by rw [IccExtend_of_mem hab _ (hx i)]

/-! ### The degree of exactness of interpolatory formulae -/

/-- **§9.1: "Any interpolatory quadrature formula that makes use of `n + 1` distinct nodes has
degree of exactness equal to at least `n`."** For distinct nodes `x₀, …, xₙ` in `[a, b]` and
`p ∈ ℙ_n`, `I_n(p) = I(p)`: indeed `Π_n p = p`. The direction `mp` of the backbone's
`Quadrature.isInterpolatory_iff_isExactOn`, applied to `isInterpolatory_lagrangeQuadrature`. -/
theorem degreeOfExactness_ge_of_interpolatory (hab : a ≤ b) {x : Fin (n + 1) → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) (hinj : Function.Injective x) {p : ℝ[X]} (hp : p.degree ≤ n) :
    lagrangeQuadrature x a b (fun t => p.eval t) = ∫ t in a..b, p.eval t := by
  have hinj' : Function.Injective fun i => (⟨x i, hx i⟩ : Icc a b) := fun i j h =>
    hinj (congrArg Subtype.val h)
  exact (Quadrature.isExactOn_integralIccCLM_iff hab hx _ n).1
    ((Quadrature.isInterpolatory_iff_isExactOn hinj').1
      (isInterpolatory_lagrangeQuadrature hab hx)) p hp

/-- **§9.1, the converse ([IK66], p. 316): "a quadrature formula using `n + 1` distinct nodes and
having degree of exactness equal at least to `n` is necessarily of interpolatory type."** If
`∑ᵢ αᵢ p(xᵢ) = ∫_a^b p` for every `p ∈ ℙ_n`, then `αᵢ = ∫_a^b lᵢ` for every `i`, so the formula
is the Lagrange quadrature formula (9.2). The direction `mpr` of the backbone's
`Quadrature.isInterpolatory_iff_isExactOn`. -/
theorem isInterpolatory_of_degreeOfExactness (hab : a ≤ b) {x : Fin (n + 1) → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) (hinj : Function.Injective x) {α : Fin (n + 1) → ℝ}
    (hexact : ∀ p : ℝ[X], p.degree ≤ n → ∑ i, α i * p.eval (x i) = ∫ t in a..b, p.eval t) :
    α = lagrangeWeights x a b := by
  have hinj' : Function.Injective fun i => (⟨x i, hx i⟩ : Icc a b) := fun i j h =>
    hinj (congrArg Subtype.val h)
  funext i
  exact ((Quadrature.isInterpolatory_iff_isExactOn hinj').2
    ((Quadrature.isExactOn_integralIccCLM_iff hab hx α n).2 hexact) i).trans
    (isInterpolatory_lagrangeQuadrature hab hx i).symm

end QuarteroniSaccoSaleri.Chapter09
