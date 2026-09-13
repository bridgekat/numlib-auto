import Numlib.Approximation.NewtonForm
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section01

/-!
# Quarteroni–Sacco–Saleri §8.2: the Newton form of the interpolating polynomial

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §8.2: the Newton form and the Newton divided differences — the defining
formula (8.14), the recursion in the degree (8.16), the Newton formula (8.17), the explicit
representation (8.18) and its four consequences (symmetry, linearity, the Leibniz formula, the
recursion (8.19) of Exercise 7), the vanishing on `𝒫_{n-1}`, and the interpolation error in
divided-difference form (8.20)–(8.21).

The divided difference `f[x₀, …, x_n]` is `DividedDifference.newton f x` of
`Numlib/Approximation/DividedDifference`, defined by the explicit formula (8.18); the book defines
it by (8.14), so `equation_8_14` is the equivalence of the two definitions. Everything else is
`Numlib/Approximation/NewtonForm`. Examples 8.3 and 8.4 are tables of computed divided differences
and are skipped.

## Main results

* `equation_8_14`, `equation_8_16`, `equation_8_17` — the Newton coefficient, the recursion in the
  degree and the Newton divided difference formula.
* `equation_8_18`, `dividedDifference_perm`, `dividedDifference_linear`,
  `dividedDifference_leibniz`, `equation_8_19` — the explicit representation and its consequences.
* `dividedDifference_eq_zero_of_mem_polyLT` — `f[x₀, …, x_n] = 0` for `f ∈ 𝒫_{n-1}`.
* `equation_8_20`, `equation_8_21` — the interpolation error `ω_{n+1}(x) f[x₀, …, x_n, x]` and the
  mean-value form `f[x₀, …, x_n, x] = f^{(n+1)}(ξ)/(n+1)!`.

## Conventions

As in §8.1: nodes are injective `x : Fin (n + 1) → ℝ`, the interpolant of `f` is
`Lagrange.interpolate Finset.univ x (fun i => f (x i))`, the nodal polynomial `ω_{n+1}` is
`Lagrange.nodal Finset.univ x`, and `ω_k` for `k ≤ n` is `DividedDifference.prefixNodal x k`. The
book's `n ≥ 1` in (8.14)–(8.16) is a family `x : Fin (n + 2) → ℝ`, with `Fin.init x` the first
`n + 1` nodes and `x (Fin.last _)` the last.
-/

open Polynomial Set DividedDifference

namespace QuarteroniSaccoSaleri.Chapter08

variable {n : ℕ} {f : ℝ → ℝ}

/-- **(8.14)–(8.15).** For distinct nodes `x₀, …, x_n` (`n ≥ 1`), the coefficient `a_n` of the
polynomial `q_n = a_n ω_n` added to `Π_{n-1} f` to obtain `Π_n f` is the `n`-th Newton divided
difference `f[x₀, …, x_n] = (f(x_n) - Π_{n-1} f(x_n)) / ω_n(x_n)`. The backbone's divided difference
is defined by the explicit formula (8.18), so this is `DividedDifference.eval_interpolate_snoc_sub`
at `x = Fin.snoc (Fin.init x) (x (Fin.last _))`. -/
theorem equation_8_14 (f : ℝ → ℝ) {x : Fin (n + 2) → ℝ} (hx : Function.Injective x) :
    DividedDifference.newton f x
      = (f (x (Fin.last (n + 1)))
          - (Lagrange.interpolate Finset.univ (Fin.init x) fun i => f (Fin.init x i)).eval
              (x (Fin.last (n + 1))))
        / ∏ i : Fin (n + 1), (x (Fin.last (n + 1)) - x i.castSucc) := by
  have h := DividedDifference.eval_interpolate_snoc_sub f (v := Fin.init x)
    (t := x (Fin.last (n + 1))) (by rwa [Fin.snoc_init_self])
  rwa [Fin.snoc_init_self] at h

/-- **(8.16).** `Π_n f = Π_{n-1} f + ω_n f[x₀, …, x_n]`, as polynomials:
`DividedDifference.interpolate_snoc_eq`. -/
theorem equation_8_16 (f : ℝ → ℝ) {x : Fin (n + 2) → ℝ} (hx : Function.Injective x) :
    (Lagrange.interpolate Finset.univ x fun i => f (x i))
      = (Lagrange.interpolate Finset.univ (Fin.init x) fun i => f (Fin.init x i))
        + C (DividedDifference.newton f x) * Lagrange.nodal Finset.univ (Fin.init x) := by
  have h := DividedDifference.interpolate_snoc_eq f (v := Fin.init x)
    (t := x (Fin.last (n + 1))) (by rwa [Fin.snoc_init_self])
  rwa [Fin.snoc_init_self] at h

/-- **(8.17), the Newton divided difference formula.** With `f[x₀] = f(x₀)` and `ω₀ = 1`,

`Π_n f(x) = ∑_{k=0}^n ω_k(x) f[x₀, …, x_k]`:

`DividedDifference.interpolate_eq_sum_newton_mul_prefixNodal`, where `f[x₀, …, x_k]` is the
divided difference at the first `k + 1` nodes `DividedDifference.prefixNodes x k` and `ω_k` is
`DividedDifference.prefixNodal x k`. -/
theorem equation_8_17 (f : ℝ → ℝ) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    (Lagrange.interpolate Finset.univ x fun i => f (x i))
      = ∑ k : Fin (n + 1),
          C (DividedDifference.newton f (DividedDifference.prefixNodes x k))
            * DividedDifference.prefixNodal x k :=
  DividedDifference.interpolate_eq_sum_newton_mul_prefixNodal f hx

/-! ### §8.2.1: properties of the Newton divided differences -/

/-- **(8.18), the explicit representation.** `f[x₀, …, x_n] = ∑_{i=0}^n f(x_i) / ω'_{n+1}(x_i)`;
this is the definition of `DividedDifference.newton` once the denominators are read as the values
of `ω'_{n+1}` at the nodes (Exercise 8.3). -/
theorem equation_8_18 (f : ℝ → ℝ) (x : Fin (n + 1) → ℝ) :
    DividedDifference.newton f x
      = ∑ i, f (x i) / (derivative (Lagrange.nodal Finset.univ x)).eval (x i) := by
  unfold DividedDifference.newton
  exact Finset.sum_congr rfl fun i _ => by rw [exercise_8_3]

/-- **§8.2.1, property 1.** The value of the divided difference is invariant with respect to
permutations of the indexes of the nodes: `DividedDifference.newton_comp_perm`. -/
theorem dividedDifference_perm (f : ℝ → ℝ) (x : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) :
    DividedDifference.newton f (x ∘ σ) = DividedDifference.newton f x :=
  DividedDifference.newton_comp_perm f x σ

/-- **§8.2.1, property 2.** If `f = α g + β h` for some `α, β ∈ ℝ`, then
`f[x₀, …, x_n] = α g[x₀, …, x_n] + β h[x₀, …, x_n]`: `DividedDifference.newton_add` and
`DividedDifference.newton_smul`. -/
theorem dividedDifference_linear (α β : ℝ) (g h : ℝ → ℝ) (x : Fin (n + 1) → ℝ) :
    DividedDifference.newton (fun t => α * g t + β * h t) x
      = α * DividedDifference.newton g x + β * DividedDifference.newton h x := by
  rw [show (fun t => α * g t + β * h t) = (fun t => α * g t) + fun t => β * h t from rfl,
    DividedDifference.newton_add, DividedDifference.newton_smul, DividedDifference.newton_smul]

/-- **§8.2.1, property 3, the Leibniz formula.** If `f = g h`, then

`f[x₀, …, x_n] = ∑_{j=0}^n g[x₀, …, x_j] h[x_j, …, x_n]`:

`DividedDifference.newton_mul`, with `g[x₀, …, x_j]` the divided difference at the prefix
`DividedDifference.prefixNodes x j` and `h[x_j, …, x_n]` the one at the suffix
`DividedDifference.suffixNodes x j`. -/
theorem dividedDifference_leibniz (g h : ℝ → ℝ) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) :
    DividedDifference.newton (fun t => g t * h t) x
      = ∑ j : Fin (n + 1), DividedDifference.newton g (DividedDifference.prefixNodes x j)
          * DividedDifference.newton h (DividedDifference.suffixNodes x j) :=
  DividedDifference.newton_mul g h hx

/-- **(8.19), the recursive formula** (§8.2.1, property 4; Exercise 8.7):

`f[x₀, …, x_n] = (f[x₁, …, x_n] - f[x₀, …, x_{n-1}]) / (x_n - x₀)`, `n ≥ 1`:

`DividedDifference.newton_succ`. -/
theorem equation_8_19 (f : ℝ → ℝ) {x : Fin (n + 2) → ℝ} (hx : Function.Injective x) :
    DividedDifference.newton f x
      = (DividedDifference.newton f (Fin.tail x) - DividedDifference.newton f (Fin.init x))
        / (x (Fin.last (n + 1)) - x 0) :=
  DividedDifference.newton_succ f hx

/-- **§8.2.1, after Example 8.3.** `f[x₀, …, x_n] = 0` for any `f ∈ 𝒫_{n-1}`:
`DividedDifference.newton_eq_zero_of_degree_lt`. -/
theorem dividedDifference_eq_zero_of_mem_polyLT {p : ℝ[X]} (hp : p.degree < n)
    {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    DividedDifference.newton (fun t => p.eval t) x = 0 :=
  DividedDifference.newton_eq_zero_of_degree_lt hp hx

/-! ### §8.2.2: the interpolation error using divided differences -/

/-- **(8.20).** For a point `x` distinct from the nodes `x₀, …, x_n`,

`E_n(x) = f(x) - Π_n f(x) = ω_{n+1}(x) f[x₀, …, x_n, x]`:

`DividedDifference.sub_eval_interpolate_eq_newton`. -/
theorem equation_8_20 (f : ℝ → ℝ) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {t : ℝ}
    (ht : ∀ i, x i ≠ t) :
    f t - (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t
      = (∏ i, (t - x i)) * DividedDifference.newton f (Fin.snoc x t) :=
  DividedDifference.sub_eval_interpolate_eq_newton f hx ht

/-- **(8.21).** Under the hypotheses of Theorem 8.2 (`f ∈ C^{n+1}` on an open set containing the
smallest interval `I_t` holding the nodes and `t`), for `t` distinct from the nodes,

`f[x₀, …, x_n, t] = f^{(n+1)}(ξ)/(n+1)!`

for a suitable `ξ ∈ I_t`. The book compares (8.20) with (8.7); the backbone
(`DividedDifference.exists_newton_eq_iteratedDeriv_div_of_contDiffOn`) proves it directly by the
generalized Rolle theorem at the `n + 2` nodes `x₀, …, x_n, t`. -/
theorem equation_8_21 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {t : ℝ}
    (ht : ∀ i, x i ≠ t) {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Icc (min t (⨅ i, x i)) (max t (⨆ i, x i)) ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Icc (min t (⨅ i, x i)) (max t (⨆ i, x i)),
      DividedDifference.newton f (Fin.snoc x t)
        = iteratedDeriv (n + 1) f ξ / (n + 1).factorial := by
  set a := min t (⨅ i, x i) with ha
  set b := max t (⨆ i, x i) with hb
  have hxmem : ∀ i, x i ∈ Icc a b := fun i =>
    ⟨(min_le_right _ _).trans (ciInf_le (Set.finite_range x).bddBelow i),
      (le_ciSup (Set.finite_range x).bddAbove i).trans (le_max_right _ _)⟩
  have htmem : t ∈ Icc a b := ⟨min_le_left _ _, le_max_left _ _⟩
  have hw : Function.Injective (Fin.snoc x t : Fin (n + 2) → ℝ) :=
    Fin.snoc_injective_iff.mpr ⟨hx, fun ⟨i, hi⟩ => ht i hi⟩
  have hwmem : ∀ i, (Fin.snoc x t : Fin (n + 2) → ℝ) i ∈ Icc a b := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa using htmem
    | cast i => simpa using hxmem i
  obtain ⟨ξ, hξ, h⟩ :=
    DividedDifference.exists_newton_eq_iteratedDeriv_div_of_contDiffOn hU hUsub hf hw hwmem
  exact ⟨ξ, Ioo_subset_Icc_self hξ, h⟩

end QuarteroniSaccoSaleri.Chapter08
