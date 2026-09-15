import Numlib.FiniteDifference.Derivative
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section03

/-!
# Quarteroni–Sacco–Saleri §10.10: approximation of function derivatives

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.10.

On the uniform grid `x_k = a + k h`, `h = (b - a)/n`, the approximations `u_i` of `f'(x_i)` are
sought as solutions of the difference scheme (10.57), `h ∑_{k=-m}^m α_k u_{i-k} =
∑_{k=-m'}^{m'} β_k f(x_{i-k})`. §10.10.1 collects the classical explicit choices — the forward,
centred and backward differences (10.59), (10.61), (10.63) with their mean-value errors (10.60),
(10.62), (10.64), and the second centred difference (10.65)–(10.66) for `f''`. §10.10.2 is the
implicit ("compact") family (10.67), whose consistency error (10.68) has a Taylor expansion whose
coefficients give the order conditions `2α + 1 = β + γ`, `6α = β + 4γ`, `10α = β + 16γ` and the
unique sixth-order scheme (10.69). §10.10.3 is the pseudo-spectral derivative
`𝒟_n f = (Π^{GL}_{n,w} f)'` at the Chebyshev–Gauss–Lobatto nodes of (10.21), with the
differentiation matrix (10.72)–(10.73).

All of it is `Numlib/FiniteDifference/Derivative`: `FiniteDifference.forwardDiff`,
`backwardDiff`, `centredDiff`, `secondCentredDiff` with their mean-value errors,
`FiniteDifference.compactError` with `compactError_expansion` and the three order conditions, and
`Lagrange.derivMatrix` with `Lagrange.eval_derivative_interpolate_node` and
`Lagrange.chebyshevLobattoDerivMatrix_apply`.

## Main definitions

* `equation_10_57` — the difference scheme (10.57) as a relation between `u : ℤ → ℝ` and the nodal
  values of `f`, at one index `i`.
* `pseudoSpectralDerivative` — `𝒟_n f`, the derivative of the interpolant at the nodes (10.21).

## Main results

* `equation_10_60`, `equation_10_62`, `equation_10_64` — the forward, centred and backward
  differences: each is (10.57) for the coefficients the book lists, and each carries its
  mean-value error.
* `equation_10_66` — the second centred difference and its error.
* `equation_10_68`, `equation_10_69` — the consistency error of the compact scheme, its expansion,
  and the order conditions with the unique sixth-order scheme.
* `degree_pseudoSpectralDerivative_lt` — `𝒟_n f ∈ ℙ_{n-1}`.
* `equation_10_72` — `(𝒟_n f)(x̄_i) = ∑_j f(x̄_j) l̄_j'(x̄_i)`, i.e. `f' = D f`, and `f'' = D² f`.
* `equation_10_73` — the explicit entries of `D`.

## Not formalized

(10.71), `‖f' - 𝒟_n f‖_w ≤ C n^{1-m} ‖f‖_{m,w}`, is quoted from [CHQZ88] without proof and needs
the weighted-Sobolev machinery that (10.22) and (10.27) already wait on; its node is open. The
wave-number discussion of §10.10.2, the boundary closure of the compact scheme and Example 10.4
are prose or numerical runs and get no node.

## Conventions

As in §10.3 the Chebyshev–Gauss–Lobatto nodes are the book's `x̄_j = -cos(jπ/n)`
(`chebyshevLobattoNode`), which are the negatives of Mathlib's `Polynomial.Chebyshev.node`; the
differentiation matrix at the book's nodes is therefore the negative of the backbone's
(`Lagrange.derivMatrix_neg`). Errata: the printed expansion of §10.10.2 carries a spurious factor
`1/2` on both `h²` terms (the order conditions it derives are nevertheless right), the display
(10.68) prints `- α f_{i+1}^{(1)}` where (10.67) has `+ α u_{i+1}`, and (10.73) prints
`D_{nn} = (2n² + 1)/3` where the correct value is `(2n² + 1)/6` (`D` has zero trace).
-/

open Asymptotics Filter Matrix Polynomial Set Topology

namespace QuarteroniSaccoSaleri.Chapter10

variable {a h : ℝ} {f : ℝ → ℝ} {i : ℤ} {n : ℕ}

/-! ### The general difference scheme (10.57) -/

/-- **(10.57).** On the uniform grid `x_k = a + k h` the difference scheme with coefficients
`α_{-m}, …, α_m` and `β_{-m'}, …, β_{m'}` relates the approximations `u_k` of `f'(x_k)` to the
nodal values of `f` by

`h ∑_{k=-m}^{m} α_k u_{i-k} = ∑_{k=-m'}^{m'} β_k f(x_{i-k})`.

The predicate is stated at one index `i`, where the whole stencil is available; determining the
`u_i` requires solving a linear system as soon as `m ≠ 0`. -/
def equation_10_57 (m m' : ℕ) (α β : ℤ → ℝ) (f : ℝ → ℝ) (a h : ℝ) (u : ℤ → ℝ) (i : ℤ) : Prop :=
  h * ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), α k * u (i - k)
    = ∑ k ∈ Finset.Icc (-(m' : ℤ)) (m' : ℤ), β k * f (a + ((i - k : ℤ) : ℝ) * h)

/-- The one-point stencil `m = 0`. -/
private theorem sum_icc_zero (g : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ), g k = g 0 := by
  rw [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton]

/-- The three-point stencil `m' = 1`. -/
private theorem sum_icc_one (g : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ), g k = g (-1) + g 0 + g 1 := by
  rw [Nat.cast_one, show Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

/-! ### §10.10.1 Classical finite difference methods -/

/-- **(10.59)–(10.60), the forward difference.** The approximation
`u_i^{FD} = (f(x_{i+1}) - f(x_i))/h` is (10.57) with `m = 0`, `α_0 = 1`, `m' = 1`, `β_{-1} = 1`,
`β_0 = -1`, `β_1 = 0`, and for `f` of the required regularity

`f'(x_i) - u_i^{FD} = -(h/2) f''(ξ_i)` with `ξ_i ∈ (x_i, x_{i+1})`. -/
theorem equation_10_60 (hh : 0 < h) (hf : ContDiffOn ℝ 2 f (Icc (a + i * h) (a + i * h + h)))
    (hd : DifferentiableAt ℝ f (a + i * h)) :
    equation_10_57 0 1 (fun k => if k = 0 then 1 else 0)
        (fun k => if k = -1 then 1 else if k = 0 then -1 else 0) f a h
        (fun j => FiniteDifference.forwardDiff f h (a + j * h)) i ∧
      ∃ ξ ∈ Ioo (a + i * h) (a + i * h + h),
        deriv f (a + i * h) - FiniteDifference.forwardDiff f h (a + i * h)
          = -(h / 2) * iteratedDeriv 2 f ξ := by
  refine ⟨?_, FiniteDifference.deriv_sub_forwardDiff_eq hh hf hd⟩
  rw [equation_10_57, sum_icc_zero, sum_icc_one]
  simp only [FiniteDifference.forwardDiff_apply, sub_zero, sub_neg_eq_add]
  norm_num
  rw [show a + ((i : ℝ) + 1) * h = a + i * h + h by ring]
  field_simp
  ring

/-- **(10.61)–(10.62), the centred difference.** The approximation
`u_i^{CD} = (f(x_{i+1}) - f(x_{i-1}))/(2h)` is (10.57) with `m = 0`, `α_0 = 1`, `m' = 1`,
`β_{-1} = 1/2`, `β_0 = 0`, `β_1 = -1/2`, and for `f` of class `C³` on `[x_{i-1}, x_{i+1}]`

`f'(x_i) - u_i^{CD} = -(h²/6) f'''(ξ_i)` with `ξ_i ∈ (x_{i-1}, x_{i+1})`,

a second-order approximation to `f'(x_i)`. -/
theorem equation_10_62 (hh : 0 < h)
    (hf : ContDiffOn ℝ 3 f (Icc (a + i * h - h) (a + i * h + h))) :
    equation_10_57 0 1 (fun k => if k = 0 then 1 else 0)
        (fun k => if k = -1 then 1 / 2 else if k = 0 then 0 else -(1 / 2)) f a h
        (fun j => FiniteDifference.centredDiff f h (a + j * h)) i ∧
      ∃ ξ ∈ Ioo (a + i * h - h) (a + i * h + h),
        deriv f (a + i * h) - FiniteDifference.centredDiff f h (a + i * h)
          = -(h ^ 2 / 6) * iteratedDeriv 3 f ξ := by
  refine ⟨?_, FiniteDifference.deriv_sub_centredDiff_eq hh hf⟩
  rw [equation_10_57, sum_icc_zero, sum_icc_one]
  simp only [FiniteDifference.centredDiff_apply, sub_zero, sub_neg_eq_add]
  norm_num
  rw [show a + ((i : ℝ) + 1) * h = a + i * h + h by ring,
    show a + ((i : ℝ) - 1) * h = a + i * h - h by ring]
  field_simp
  ring

/-- **(10.63)–(10.64), the backward difference.** The approximation
`u_i^{BD} = (f(x_i) - f(x_{i-1}))/h` is (10.57) with `m = 0`, `α_0 = 1`, `m' = 1`, `β_{-1} = 0`,
`β_0 = 1`, `β_1 = -1`, and

`f'(x_i) - u_i^{BD} = (h/2) f''(ξ_i)` with `ξ_i ∈ (x_{i-1}, x_i)`. -/
theorem equation_10_64 (hh : 0 < h) (hf : ContDiffOn ℝ 2 f (Icc (a + i * h - h) (a + i * h)))
    (hd : DifferentiableAt ℝ f (a + i * h)) :
    equation_10_57 0 1 (fun k => if k = 0 then 1 else 0)
        (fun k => if k = -1 then 0 else if k = 0 then 1 else -1) f a h
        (fun j => FiniteDifference.backwardDiff f h (a + j * h)) i ∧
      ∃ ξ ∈ Ioo (a + i * h - h) (a + i * h),
        deriv f (a + i * h) - FiniteDifference.backwardDiff f h (a + i * h)
          = (h / 2) * iteratedDeriv 2 f ξ := by
  refine ⟨?_, FiniteDifference.deriv_sub_backwardDiff_eq hh hf hd⟩
  rw [equation_10_57, sum_icc_zero, sum_icc_one]
  simp only [FiniteDifference.backwardDiff_apply, sub_zero, sub_neg_eq_add]
  norm_num
  rw [show a + ((i : ℝ) - 1) * h = a + i * h - h by ring]
  field_simp
  ring

/-- **(10.65)–(10.66), the second centred difference.** For `f ∈ C⁴([a, b])` the approximation
`u_i'' = (f(x_{i+1}) - 2 f(x_i) + f(x_{i-1}))/h²` of `f''(x_i)` has the error

`f''(x_i) - u_i'' = -(h²/24)(f⁗(x_i + θ_i h) + f⁗(x_i - ω_i h))`, `0 < θ_i, ω_i < 1`,

a second-order approximation to `f''(x_i)`. -/
theorem equation_10_66 (hh : 0 < h)
    (hf : ContDiffOn ℝ 4 f (Icc (a + i * h - h) (a + i * h + h))) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, ∃ ω ∈ Ioo (0 : ℝ) 1,
      iteratedDeriv 2 f (a + i * h) - FiniteDifference.secondCentredDiff f h (a + i * h)
        = -(h ^ 2 / 24) * (iteratedDeriv 4 f (a + i * h + θ * h)
          + iteratedDeriv 4 f (a + i * h - ω * h)) :=
  FiniteDifference.iteratedDeriv_two_sub_secondCentredDiff_eq hh hf

/-! ### §10.10.2 Compact finite differences -/

/-- **(10.67)–(10.68) and the expansion of the consistency error.** The compact scheme

`α u_{i-1} + u_i + α u_{i+1} = (β/2h)(f_{i+1} - f_{i-1}) + (γ/4h)(f_{i+2} - f_{i-2})`

has, by "forcing" `f` to satisfy it, the consistency error

`σ_i(h) = α f_{i-1}^{(1)} + f_i^{(1)} + α f_{i+1}^{(1)}
  - ((β/2h)(f_{i+1} - f_{i-1}) + (γ/4h)(f_{i+2} - f_{i-2}))`,

and for `f` of class `C⁷` at `x_i` its Taylor expansion around `x_i` is

`σ_i(h) = (2α + 1 - β - γ) f_i^{(1)} + h²(α - β/6 - 2γ/3) f_i^{(3)}
  + h⁴(α/12 - β/120 - 2γ/15) f_i^{(5)} + O(h⁶)`.

Errata: the display (10.68) prints `- α f_{i+1}^{(1)}` for the `+ α u_{i+1}` of (10.67), and the
two `h²` terms of the printed expansion carry a spurious factor `1/2`; the order conditions the
book draws from it are nevertheless correct. -/
theorem equation_10_68 {α β γ x : ℝ} (hf : ContDiffAt ℝ 7 f x) :
    (∀ h : ℝ, FiniteDifference.compactError α β γ f x h
        = α * deriv f (x - h) + deriv f x + α * deriv f (x + h)
          - (β / (2 * h) * (f (x + h) - f (x - h))
            + γ / (4 * h) * (f (x + 2 * h) - f (x - 2 * h)))) ∧
      (fun h => FiniteDifference.compactError α β γ f x h
          - ((2 * α + 1 - β - γ) * deriv f x
            + h ^ 2 * (α - β / 6 - 2 * γ / 3) * iteratedDeriv 3 f x
            + h ^ 4 * (α / 12 - β / 120 - 2 * γ / 15) * iteratedDeriv 5 f x))
        =O[𝓝[≠] 0] fun h => h ^ 6 :=
  ⟨fun _ => rfl, FiniteDifference.compactError_expansion hf⟩

/-- **(10.69) and the order conditions of §10.10.2.** Equating to zero the coefficients of
`f_i^{(1)}`, `f_i^{(3)}` and `f_i^{(5)}` in the expansion of the consistency error gives the
conditions `2α + 1 = β + γ` (order 2), `6α = β + 4γ` (order 4) and `10α = β + 16γ` (order 6). The
three equations have a nonsingular matrix, so there is a unique scheme of order 6, namely
`α = 1/3`, `β = 14/9`, `γ = 1/9`; there are infinitely many of order 2 and 4, a popular
fourth-order one being `α = 1/4`, `β = 3/2`, `γ = 0`, and the traditional finite differences are
the case `α = 0`, of which `α = γ = 0`, `β = 1` is the centred difference (10.61). -/
theorem equation_10_69 {α β γ x : ℝ} (h₁ : 2 * α + 1 = β + γ) (h₂ : 6 * α = β + 4 * γ)
    (h₃ : 10 * α = β + 16 * γ) (hf : ContDiffAt ℝ 7 f x) :
    ((fun h => FiniteDifference.compactError α β γ f x h) =O[𝓝[≠] 0] fun h => h ^ 6) ∧
      (α = 1 / 3 ∧ β = 14 / 9 ∧ γ = 1 / 9) ∧
      ((fun h => FiniteDifference.compactError (1 / 4) (3 / 2) 0 f x h)
        =O[𝓝[≠] 0] fun h => h ^ 4) ∧
      ∀ h : ℝ, FiniteDifference.compactError 0 1 0 f x h
        = deriv f x - FiniteDifference.centredDiff f h x :=
  ⟨FiniteDifference.compactError_isBigO_pow_six h₁ h₂ h₃ hf,
    FiniteDifference.order_six_unique h₁ h₂ h₃,
    FiniteDifference.compactError_isBigO_pow_four (by norm_num) (by norm_num) hf,
    fun h => FiniteDifference.compactError_zero_one_zero h⟩

/-! ### §10.10.3 The pseudo-spectral derivative -/

/-- **The pseudo-spectral derivative** `𝒟_n f = (Π^{GL}_{n,w} f)'` of §10.10.3: the exact
derivative of the polynomial interpolating `f ∈ C⁰([-1, 1])` at the `n + 1`
Chebyshev–Gauss–Lobatto nodes (10.21). -/
noncomputable def pseudoSpectralDerivative (n : ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  derivative (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
    fun j => f (chebyshevLobattoNode n j))

/-- `𝒟_n f ∈ ℙ_{n-1}(I)`: the pseudo-spectral derivative has degree less than `n`. -/
theorem degree_pseudoSpectralDerivative_lt (hn : n ≠ 0) (f : ℝ → ℝ) :
    (pseudoSpectralDerivative n f).degree < (n : ℕ) := by
  have hdq : (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      fun j => f (chebyshevLobattoNode n j)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have hd := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (n + 1))))
      (v := fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      (r := fun j : Fin (n + 1) => f (chebyshevLobattoNode n j))
      (injective_chebyshevLobattoNode hn).injOn
    simpa using hd
  rw [pseudoSpectralDerivative]
  rcases eq_or_ne (Lagrange.interpolate Finset.univ
      (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      fun j => f (chebyshevLobattoNode n j)) 0 with h0 | h0
  · rw [h0, derivative_zero, degree_zero]
    simp
  · rw [degree_eq_natDegree h0] at hdq
    have h1 : (Lagrange.interpolate Finset.univ
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
        fun j => f (chebyshevLobattoNode n j)).natDegree < n + 1 := by exact_mod_cast hdq
    refine lt_of_lt_of_le (degree_derivative_lt h0) ?_
    rw [degree_eq_natDegree h0]
    exact_mod_cast Nat.lt_succ_iff.mp h1

/-- **(10.72), the pseudo-spectral differentiation matrix.** The nodal values of `𝒟_n f` are

`(𝒟_n f)(x̄_i) = ∑_{j=0}^n f(x̄_j) l̄_j'(x̄_i)`, `i = 0, …, n`,

so that, with `D_{ij} = l̄_j'(x̄_i)` (`Lagrange.derivMatrix`), `f' = D f`; the second-order
pseudo-spectral derivative is `D² f = D (D f)`. -/
theorem equation_10_72 (n : ℕ) (f : ℝ → ℝ) (i : Fin (n + 1)) :
    (pseudoSpectralDerivative n f).eval (chebyshevLobattoNode n i)
        = ∑ j : Fin (n + 1), f (chebyshevLobattoNode n j)
          * (derivative (Lagrange.basis Finset.univ
              (fun j : Fin (n + 1) => chebyshevLobattoNode n j) j)).eval
              (chebyshevLobattoNode n i) ∧
      (pseudoSpectralDerivative n f).eval (chebyshevLobattoNode n i)
        = (Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
            *ᵥ fun j => f (chebyshevLobattoNode n j)) i ∧
      ∀ v : Fin (n + 1) → ℝ,
        Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j) ^ 2 *ᵥ v
          = Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
            *ᵥ (Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j) *ᵥ v) := by
  have hmat : (pseudoSpectralDerivative n f).eval (chebyshevLobattoNode n i)
      = (Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
          *ᵥ fun j => f (chebyshevLobattoNode n j)) i :=
    by
      rw [pseudoSpectralDerivative]
      exact Lagrange.eval_derivative_interpolate_node
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
        (fun j => f (chebyshevLobattoNode n j)) i
  refine ⟨?_, hmat, fun v => ?_⟩
  · rw [hmat, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [Lagrange.derivMatrix_apply, mul_comm]
  · rw [sq, Matrix.mulVec_mulVec]

/-- **(10.73), the entries of `D`.** At the Chebyshev–Gauss–Lobatto nodes `x̄_j = -cos(jπ/n)`,
`n ≥ 1`, with the factors `d_0 = d_n = 2`, `d_j = 1` otherwise of §10.3,

`D_{lj} = (d_l/d_j) (-1)^{l+j}/(x̄_l - x̄_j)` for `l ≠ j`,
`D_{jj} = -x̄_j/(2(1 - x̄_j²))` for `1 ≤ j ≤ n - 1`,
`D_{00} = -(2n² + 1)/6` and `D_{nn} = (2n² + 1)/6`.

Erratum: the book prints `D_{nn} = (2n² + 1)/3`; since `D` has zero trace (its interior diagonal
is odd under `j ↦ n - j` and its only eigenvalue is `0`, Example 5.13) the value is
`(2n² + 1)/6`, the entry of [CHQZ88] p. 69 with the node order reversed. -/
theorem equation_10_73 (hn : n ≠ 0) (l j : Fin (n + 1)) :
    Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j) l j
      = if l = j then
          (if (j : ℕ) = 0 then -((2 * (n : ℝ) ^ 2 + 1) / 6)
            else if (j : ℕ) = n then (2 * (n : ℝ) ^ 2 + 1) / 6
            else -chebyshevLobattoNode n j / (2 * (1 - chebyshevLobattoNode n j ^ 2)))
        else Chebyshev.lobattoFactor n l / Chebyshev.lobattoFactor n j * (-1) ^ ((l : ℕ) + j)
          / (chebyshevLobattoNode n l - chebyshevLobattoNode n j) := by
  have hneg : (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      = -fun j : Fin (n + 1) => Chebyshev.node n j := by
    funext k
    simp [chebyshevLobattoNode, Chebyshev.node]
  have hval : ∀ k : Fin (n + 1), chebyshevLobattoNode n k = -Chebyshev.node n k := fun k => by
    simp [chebyshevLobattoNode, Chebyshev.node]
  rw [hneg, Lagrange.derivMatrix_neg, Matrix.neg_apply,
    Lagrange.chebyshevLobattoDerivMatrix_apply hn]
  simp only [hval, neg_sub_neg, neg_neg, neg_sq]
  split_ifs
  · ring
  · ring
  · ring
  · rw [← neg_sub (Chebyshev.node n l) (Chebyshev.node n j), div_neg]

end QuarteroniSaccoSaleri.Chapter10
