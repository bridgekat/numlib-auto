import Numlib.Approximation.BSpline
import Numlib.Approximation.Spline
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section03

/-!
# Quarteroni–Sacco–Saleri §8.6: approximation by splines

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §8.6: splines of degree `k` (Definition 8.1) and the dimension `n + k`
of their space, the periodic (8.44) and natural (8.45) end conditions, the truncated-power basis
of Exercise 10; interpolatory cubic splines (§8.6.1) — the panel representation (8.46), the
M-continuity system (8.47)–(8.48) and its unique solvability for the closures of type (8.48), the
natural, clamped, periodic and not-a-knot splines, the cardinal spline basis, the minimum-norm
Property 8.2 with its clamped version (Exercise 11) and the best-approximation property of the
clamped spline; B-splines (§8.6.2) — Definition 8.2, the explicit form (8.53), support and
positivity, the Cox–de Boor recursion (8.54), coincident knots (Remark 8.3), the uniform cubic
B-spline (Example 8.9), the B-spline basis (8.55)–(8.56) and the endpoint values (8.57).
Example 8.8 (a table) and Remark 8.2 (software) are skipped.

The backbone is `Numlib/Approximation/Spline` (`Spline.splineSpace`, `Spline.IsCubicInterp`,
`Spline.momentMatrix`, `Spline.cubicInterp`, `Spline.cardinalBasis`, the Holladay lemmas) and
`Numlib/Approximation/BSpline` (`BSpline.bspline` by the Cox–de Boor recursion, `BSpline.nform`
by divided differences, the B-spline basis).

## Main definitions

* `definition_8_1 a b n x k` — the space `𝒮_k` of splines of degree `k` on the nodes
  `a = x 0 < ⋯ < x n = b`, with `mem_definition_8_1_iff` ((8.41)–(8.42)) and
  `mem_definition_8_1_three_iff` (the cubic case as the backbone's `Spline.IsCubicSpline`).
* `equation_8_44`, `equation_8_45` — the periodic and the natural end conditions.
* `IsCubicInterpSpline a b n x f s` — the cubic spline interpolating the values `f_i` at the nodes.
* `definition_8_2 x k i` — the normalized B-spline `B_{i,k+1}` of Definition 8.2, as a scaled
  divided difference of a truncated power, with `definition_8_2_eq_bspline`: it is the Cox–de Boor
  B-spline `BSpline.bspline x k i`.
* `remark_8_3_confluent` — the confluent divided differences of Remark 8.3.

## Main results

* `definition_8_1_finrank` — `dim 𝒮_k = n + k`; `exercise_8_10` — the truncated-power basis.
* `equation_8_46`, `equation_8_46_integrated`, `equation_8_47`, `equation_8_48`,
  `equation_8_48_iff`, `equation_8_48_spline`, `equation_8_48_prolonged` — the construction of
  the interpolatory cubic spline from its moments.
* `naturalCubicSpline_existsUnique`, `clampedCubicSpline_existsUnique`,
  `periodicCubicSpline_existsUnique`, `notAKnotSpline_existsUnique` — the four closures.
* `cardinalSplineBasis` and its companions — the cardinal spline basis of `𝒮_3`.
* `property_8_2`, `property_8_2_eq_iff`, `exercise_8_11`, `exercise_8_11_eq_iff`,
  `clampedSpline_bestApprox_deriv2` — Holladay's minimum-norm property and the best
  approximation of `f''` by the clamped spline.
* `property_8_3_weak` — Property 8.3 with non-sharp constants, for the clamped spline.
* `remark_8_4` — Boehm's knot insertion.
* `equation_8_53`, `bSpline_support`, `bSpline_nonneg`, `equation_8_54`, `equation_8_54_zero`,
  `equation_8_54_definition_8_2`, `remark_8_3_left`, `remark_8_3_right`, `example_8_9`,
  `equation_8_56`, `equation_8_56_repr`, `equation_8_57`, `equation_8_57_right` — B-splines.

## Not formalized

Property 8.3 with the sharp Hall–Meyer constants (`property_8_3`) and the minimal-support
characterization of B-splines quoted from Schoenberg (`bSpline_minimalSupport`) are stated in the
plan and left open there; see the plan for the reasons. `property_8_3_weak` is Property 8.3 with
non-sharp constants.

## Conventions

The nodes are `x : ℕ → ℝ` with `Spline.IsPartition a b n x`: `a = x 0 < x 1 < ⋯ < x n = b`, `n`
panels `[x (i-1), x i]`, `1 ≤ i ≤ n`, of lengths `h_i = x i - x (i-1)`. A spline is a function
`s : ℝ → ℝ` considered on `[a, b]`; its derivatives at a point of `[a, b]` are the derivatives
within `[a, b]`, `derivWithin s (Icc a b)` and `iteratedDerivWithin 2 s (Icc a b)`, so that the
moments `M_i = s''(x_i)` are `iteratedDerivWithin 2 s (Icc a b) (x i)` (the backbone's
`Spline.moment a b x s i`). The space `𝒮_k` is a submodule of `C(Icc a b, ℝ)`, and
`mem_definition_8_1_three_iff` connects the two views. For B-splines the knots are `ℕ`-indexed;
the book's `B_{i,k+1}` (degree `k`) is `BSpline.bspline x k i`, and the fictitious knots
`x_{-k}, …, x_{-1}` of (8.55) are the knots `x 0, …, x (k - 1)` of a shifted sequence whose data
knots are `x k = a < ⋯ < x (n + k) = b`.
-/

open Filter MeasureTheory Polynomial Set
open scoped Topology

namespace QuarteroniSaccoSaleri.Chapter08

variable {a b : ℝ} {n k : ℕ} {x : ℕ → ℝ} {f : ℕ → ℝ} {s : ℝ → ℝ}

/-! ### Definition 8.1: splines of degree `k` -/

/-- **Definition 8.1, the space `𝒮_k`.** Let `x₀, …, x_n` be `n + 1` distinct nodes of `[a, b]`
with `a = x₀ < x₁ < ⋯ < x_n = b`. The function `s_k` on `[a, b]` is a *spline of degree `k`*
relative to the nodes `x_j` if `s_k|_{[x_j, x_{j+1}]} ∈ 𝒫_k` for `j = 0, …, n - 1` (8.41) and
`s_k ∈ C^{k-1}[a, b]` (8.42); `𝒮_k` is the space of such splines — the spline space
`Spline.splineSpace a b n x k (k - 1)` of `Numlib/Approximation/Spline`, a submodule of
`C(Icc a b, ℝ)`. -/
noncomputable def definition_8_1 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    Submodule ℝ C(Icc a b, ℝ) :=
  Spline.splineSpace a b n x k (k - 1)

/-- **Definition 8.1 unfolded, (8.41)–(8.42)**: a continuous function on `[a, b]` is a spline of
degree `k` when it is the restriction of a `C^{k-1}` function on `[a, b]` which agrees on every
panel `[x_j, x_{j+1}]`, `j < n`, with a polynomial of degree at most `k`. -/
theorem mem_definition_8_1_iff (v : C(Icc a b, ℝ)) :
    v ∈ definition_8_1 a b n x k ↔ ∃ g : ℝ → ℝ, ContDiffOn ℝ (k - 1 : ℕ) g (Icc a b) ∧
      (∀ t : Icc a b, v t = g t) ∧
      ∀ j < n, ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn g p.eval (Icc (x j) (x (j + 1))) :=
  Iff.rfl

/-- **Definition 8.1, `dim 𝒮_k = n + k`**: for `n ≥ 1` panels and `k ≥ 1`, the space of splines of
degree `k` has dimension `n + k` — the book's count (8.43), `(k + 1) n - k (n - 1)`.
`Spline.finrank_splineSpace` with `r = k - 1`: `n (k - (k - 1)) + (k - 1) + 1`. -/
theorem definition_8_1_finrank (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Module.finrank ℝ (definition_8_1 a b n x k) = n + k := by
  rw [definition_8_1, Spline.finrank_splineSpace hx hn (Nat.sub_le k 1)]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  ring

/-- **(8.44), periodic splines**: `s_k^{(m)}(a) = s_k^{(m)}(b)` for `m = 0, 1, …, k - 1`, the
derivatives being taken within `[a, b]`. -/
def equation_8_44 (a b : ℝ) (k : ℕ) (s : ℝ → ℝ) : Prop :=
  ∀ m ≤ k - 1, iteratedDerivWithin m s (Icc a b) a = iteratedDerivWithin m s (Icc a b) b

/-- **(8.44) for cubic splines** (`k = 3`): `s(a) = s(b)`, `s'(a) = s'(b)` and `s''(a) = s''(b)`,
the last two being the backbone's `Spline.IsPeriodicEnd a b s`. -/
theorem equation_8_44_three_iff :
    equation_8_44 a b 3 s ↔ s a = s b ∧ Spline.IsPeriodicEnd a b s := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by norm_num), by simpa using h 1 (by norm_num), h 2 le_rfl⟩
  · rintro ⟨h0, h1, h2⟩ m hm
    interval_cases m
    · simpa using h0
    · simpa using h1
    · exact h2

/-- **(8.45), natural splines** of odd degree `k = 2l - 1`, `l ≥ 2`:
`s_k^{(l+j)}(a) = s_k^{(l+j)}(b) = 0` for `j = 0, 1, …, l - 2`, the derivatives being taken within
`[a, b]`. -/
def equation_8_45 (a b : ℝ) (l : ℕ) (s : ℝ → ℝ) : Prop :=
  ∀ j ≤ l - 2, iteratedDerivWithin (l + j) s (Icc a b) a = 0 ∧
    iteratedDerivWithin (l + j) s (Icc a b) b = 0

/-- **(8.45) for cubic splines** (`l = 2`): `s''(a) = s''(b) = 0`. -/
theorem equation_8_45_two_iff :
    equation_8_45 a b 2 s ↔
      iteratedDerivWithin 2 s (Icc a b) a = 0 ∧ iteratedDerivWithin 2 s (Icc a b) b = 0 := by
  constructor
  · intro h
    simpa using h 0 le_rfl
  · rintro ⟨h0, h1⟩ j hj
    obtain rfl : j = 0 := by omega
    exact ⟨h0, h1⟩

/-- **The natural end conditions are the closure `λ₀ = μ_n = d₀ = d_n = 0` of (8.48)**: for a
partition of `[a, b]`, `s''(a) = s''(b) = 0` is `Spline.HasClosure a b n x 0 0 0 0 s`. -/
theorem equation_8_45_two_iff_hasClosure (hx : Spline.IsPartition a b n x) :
    equation_8_45 a b 2 s ↔ Spline.HasClosure a b n x 0 0 0 0 s := by
  rw [equation_8_45_two_iff, Spline.HasClosure]
  simp only [Spline.moment, hx.first, hx.last, zero_mul, add_zero, zero_add, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or]

/-- **Exercise 8.10.** The functions `1, x, x², …, x^k, (x - x₁)_+^k, …, (x - x_g)_+^k`, `g = n - 1`
the number of internal nodes, form a basis of `𝒮_k[a, b]`, so that every `s_k ∈ 𝒮_k` is
`∑_{i≤k} b_i x^i + ∑_{i=1}^{g} c_i (x - x_i)_+^k`: a basis indexed by `Fin (n + k)` whose first
`k + 1` vectors are the monomials and whose remaining `n - 1` vectors are the truncated powers
`(x - x_j)_+^k = Quadrature.truncPow k x (x j)`, `j = 1, …, n - 1`.
`Spline.exists_basis_truncPow`. -/
theorem exercise_8_10 (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ B : Module.Basis (Fin (n + k)) ℝ (definition_8_1 a b n x k),
      (∀ i : Fin (n + k), (i : ℕ) ≤ k → ∀ t : Icc a b,
        (B i : C(Icc a b, ℝ)) t = (t : ℝ) ^ (i : ℕ)) ∧
      ∀ i : Fin (n + k), k < i → ∀ t : Icc a b,
        (B i : C(Icc a b, ℝ)) t = Quadrature.truncPow k (t : ℝ) (x (i - k)) :=
  Spline.exists_basis_truncPow hx hn hk

/-! ### §8.6.1: interpolatory cubic splines -/

/-- **The cubic spline interpolating the values `f_i`** (§8.6.1): a function `s` on `[a, b]` of
class `C²`, a polynomial of degree at most `3` on every panel `[x_{i-1}, x_i]`, with
`s(x_i) = f_i` for `i = 0, …, n` — the backbone's `Spline.IsCubicInterp a b n x f s`. The book's
notation is `m_i = s'(x_i)` and `M_i = s''(x_i)`, the derivatives within `[a, b]`. -/
abbrev IsCubicInterpSpline (a b : ℝ) (n : ℕ) (x f : ℕ → ℝ) (s : ℝ → ℝ) : Prop :=
  Spline.IsCubicInterp a b n x f s

/-- The interpolating cubic spline unfolded: `C²` on `[a, b]`, a cubic on every panel,
interpolating the data. -/
theorem isCubicInterpSpline_iff :
    IsCubicInterpSpline a b n x f s ↔ ContDiffOn ℝ 2 s (Icc a b) ∧
      (∀ i, 1 ≤ i → i ≤ n → ∃ p : ℝ[X], p.degree ≤ 3 ∧ EqOn s p.eval (Icc (x (i - 1)) (x i))) ∧
      ∀ i ≤ n, s (x i) = f i :=
  ⟨fun h => ⟨h.contDiffOn, h.piecewise, h.interp⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- **The cubic splines of Definition 8.1 are the `C²` piecewise cubics of the backbone**: a
continuous function on `[a, b]` lies in `𝒮_3` exactly when it is the restriction of a function
`s : ℝ → ℝ` with `Spline.IsCubicSpline a b n x s`. -/
theorem mem_definition_8_1_three_iff (v : C(Icc a b, ℝ)) :
    v ∈ definition_8_1 a b n x 3 ↔
      ∃ s : ℝ → ℝ, Spline.IsCubicSpline a b n x s ∧ ∀ t : Icc a b, v t = s t := by
  have h2 : ((3 - 1 : ℕ) : WithTop ℕ∞) = 2 := by norm_num
  rw [mem_definition_8_1_iff, h2]
  constructor
  · rintro ⟨g, hg, hv, hp⟩
    refine ⟨g, ⟨hg, fun i hi1 hin => ?_⟩, hv⟩
    obtain ⟨p, hpd, hpe⟩ := hp (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at hpe
    exact ⟨p, hpd, hpe⟩
  · rintro ⟨g, hg, hv⟩
    refine ⟨g, hg.contDiffOn, hv, fun j hj => ?_⟩
    obtain ⟨p, hpd, hpe⟩ := hg.piecewise (j + 1) (by omega) hj
    rw [Nat.add_sub_cancel] at hpe
    exact ⟨p, hpd, hpe⟩

/-- A `C²` piecewise cubic on the partition, restricted to `[a, b]`, is an element of `𝒮_3`. -/
theorem mem_definition_8_1_three_of_isCubicSpline (hs : Spline.IsCubicSpline a b n x s) :
    (⟨(Icc a b).domRestrict s, hs.contDiffOn.continuousOn.domRestrict⟩ : C(Icc a b, ℝ)) ∈
      definition_8_1 a b n x 3 :=
  (mem_definition_8_1_three_iff _).mpr ⟨s, hs, fun _ => rfl⟩

section Cubic

variable (hx : Spline.IsPartition a b n x)
include hx

/-- **(8.46).** Let `s₃` be the cubic spline interpolating the values `f_i` at the nodes, and
`M_i = s₃''(x_i)`. Since `s_{3,i-1} ∈ 𝒫₃`, `s_{3,i-1}''` is linear and

`s_{3,i-1}''(x) = M_{i-1} (x_i - x)/h_i + M_i (x - x_{i-1})/h_i` for `x ∈ [x_{i-1}, x_i]`,

where `h_i = x_i - x_{i-1}`; `s₃''` is the second derivative within `[a, b]`. The spline is the
panel cubic of its moments (`Spline.IsCubicInterp.eqOn_panelCubic`), whose second derivative is
`Spline.panelCubicD2_apply`. -/
theorem equation_8_46 (hs : IsCubicInterpSpline a b n x f s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {t : ℝ} (ht : t ∈ Icc (x (i - 1)) (x i)) :
    iteratedDerivWithin 2 s (Icc a b) t
      = iteratedDerivWithin 2 s (Icc a b) (x (i - 1)) * (x i - t) / (x i - x (i - 1))
        + iteratedDerivWithin 2 s (Icc a b) (x i) * (t - x (i - 1)) / (x i - x (i - 1)) := by
  have hlt : x (i - 1) < x i := hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have heq := hs.eqOn_panelCubic hx hi1 hin
  rw [(Spline.derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn hlt hsub heq ht).2]
  exact Spline.panelCubicD2_apply x f (Spline.moment a b x s) hlt t

/-- **(8.46) integrated twice.** With `M_i = s₃''(x_i)` and `h_i = x_i - x_{i-1}`, on
`[x_{i-1}, x_i]`

`s₃(x) = M_{i-1} (x_i - x)³/(6 h_i) + M_i (x - x_{i-1})³/(6 h_i) + C_{i-1} (x - x_{i-1})
+ C̃_{i-1}`,

where the constants are determined by the end point values `s₃(x_{i-1}) = f_{i-1}` and
`s₃(x_i) = f_i`: `C̃_{i-1} = f_{i-1} - M_{i-1} h_i²/6` and
`C_{i-1} = (f_i - f_{i-1})/h_i - (h_i/6)(M_i - M_{i-1})`. The book states this for
`i = 1, …, n - 1`; it holds on every panel. -/
theorem equation_8_46_integrated (hs : IsCubicInterpSpline a b n x f s) {i : ℕ} (hi1 : 1 ≤ i)
    (hin : i ≤ n) {t : ℝ} (ht : t ∈ Icc (x (i - 1)) (x i)) :
    s t = iteratedDerivWithin 2 s (Icc a b) (x (i - 1)) * (x i - t) ^ 3 / (6 * (x i - x (i - 1)))
      + iteratedDerivWithin 2 s (Icc a b) (x i) * (t - x (i - 1)) ^ 3 / (6 * (x i - x (i - 1)))
      + ((f i - f (i - 1)) / (x i - x (i - 1)) - (x i - x (i - 1)) / 6
          * (iteratedDerivWithin 2 s (Icc a b) (x i)
            - iteratedDerivWithin 2 s (Icc a b) (x (i - 1)))) * (t - x (i - 1))
      + (f (i - 1)
          - iteratedDerivWithin 2 s (Icc a b) (x (i - 1)) * (x i - x (i - 1)) ^ 2 / 6) := by
  rw [hs.eqOn_panelCubic hx hi1 hin ht, Spline.panelCubic_apply]
  rfl

/-- **(8.47), the M-continuity system.** For the cubic spline `s₃` interpolating the values
`f_i`, with `M_i = s₃''(x_i)` and `h_i = x_i - x_{i-1}`, the continuity of `s₃'` at the internal
nodes gives, for `i = 1, …, n - 1`,

`μ_i M_{i-1} + 2 M_i + λ_i M_{i+1} = d_i`,

where `μ_i = h_i/(h_i + h_{i+1})`, `λ_i = h_{i+1}/(h_i + h_{i+1})` and
`d_i = (6/(h_i + h_{i+1})) ((f_{i+1} - f_i)/h_{i+1} - (f_i - f_{i-1})/h_i)`.
`Spline.IsCubicInterp.isMomentEq`. -/
theorem equation_8_47 (hs : IsCubicInterpSpline a b n x f s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    (x i - x (i - 1)) / ((x i - x (i - 1)) + (x (i + 1) - x i))
        * iteratedDerivWithin 2 s (Icc a b) (x (i - 1))
      + 2 * iteratedDerivWithin 2 s (Icc a b) (x i)
      + (x (i + 1) - x i) / ((x i - x (i - 1)) + (x (i + 1) - x i))
        * iteratedDerivWithin 2 s (Icc a b) (x (i + 1))
      = 6 / ((x i - x (i - 1)) + (x (i + 1) - x i))
        * ((f (i + 1) - f i) / (x (i + 1) - x i) - (f i - f (i - 1)) / (x i - x (i - 1))) := by
  have h := hs.isMomentEq hx hi1 hin
  simp only [Spline.IsMomentEq, Spline.panelLength, Spline.moment, Nat.add_sub_cancel] at h
  exact h

/-- **The system (8.48) is (8.47) together with the two closure rows**: for the moment vector
`M₀, …, M_n` and closure parameters `λ₀, μ_n, d₀, d_n`, the tridiagonal system

`[2 λ₀ ; μ₁ 2 λ₁ ; … ; μ_{n-1} 2 λ_{n-1} ; μ_n 2] [M₀; …; M_n] = [d₀; …; d_n]`

— `Spline.momentMatrix n h λ₀ μ_n *ᵥ M = Spline.momentRhs n h f d₀ d_n` with `h_i = x_i - x_{i-1}`
— holds exactly when the equations (8.47) hold at the internal nodes and
`2 M₀ + λ₀ M₁ = d₀`, `μ_n M_{n-1} + 2 M_n = d_n`. `Spline.momentMatrix_mulVec_eq_iff`. -/
theorem equation_8_48_iff (hn : 1 ≤ n) (lam0 mun d0 dn : ℝ) (M : ℕ → ℝ) :
    (Spline.momentMatrix n (Spline.panelLength x) lam0 mun).mulVec
        (fun i : Fin (n + 1) => M i) = Spline.momentRhs n (Spline.panelLength x) f d0 dn ↔
      (∀ i, 1 ≤ i → i < n →
        (x i - x (i - 1)) / ((x i - x (i - 1)) + (x (i + 1) - x i)) * M (i - 1) + 2 * M i
          + (x (i + 1) - x i) / ((x i - x (i - 1)) + (x (i + 1) - x i)) * M (i + 1)
          = 6 / ((x i - x (i - 1)) + (x (i + 1) - x i))
            * ((f (i + 1) - f i) / (x (i + 1) - x i) - (f i - f (i - 1)) / (x i - x (i - 1)))) ∧
      2 * M 0 + lam0 * M 1 = d0 ∧ mun * M (n - 1) + 2 * M n = dn := by
  rw [Spline.momentMatrix_mulVec_eq_iff hx hn]
  have he : ∀ i ≤ n, Spline.extendFin (fun i : Fin (n + 1) => M i) i = M i := fun i hi => by
    rw [Spline.extendFin_of_lt _ (by omega)]
  simp only [Spline.IsMomentEq, Spline.panelLength, Nat.add_sub_cancel]
  rw [he 0 (by omega), he 1 hn, he (n - 1) (by omega), he n le_rfl]
  refine and_congr (forall_congr' fun i => forall_congr' fun hi1 => forall_congr' fun hin => ?_)
    Iff.rfl
  rw [he (i - 1) (by omega), he i hin.le, he (i + 1) hin]

/-- **(8.48), unique solvability of the linear system.** For a partition with `n ≥ 1` panels and
closure parameters `0 ≤ λ₀ ≤ 1`, `0 ≤ μ_n ≤ 1` (any `d₀, d_n`), the tridiagonal system (8.48)
has exactly one solution `M = (M₀, …, M_n)`: the matrix is strictly diagonally dominant, hence
nonsingular (`Spline.isUnit_momentMatrix`). -/
theorem equation_8_48 {lam0 mun : ℝ} (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun)
    (hm1 : mun ≤ 1) (f : ℕ → ℝ) (d0 dn : ℝ) :
    ∃! M : Fin (n + 1) → ℝ, (Spline.momentMatrix n (Spline.panelLength x) lam0 mun).mulVec M
      = Spline.momentRhs n (Spline.panelLength x) f d0 dn := by
  have hA := Spline.isUnit_momentMatrix (h := Spline.panelLength x) (n := n)
    (fun i hi1 hin => hx.panelLength_pos hi1 hin) hl0 hl1 hm0 hm1
  obtain ⟨M, hM⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hA
    (Spline.momentRhs n (Spline.panelLength x) f d0 dn)
  exact ⟨M, hM, fun N hN => Matrix.mulVec_injective_iff_isUnit.mpr hA (hN.trans hM.symm)⟩

/-- **(8.48), the interpolatory cubic spline with a closure of type (8.48).** For a partition with
`n ≥ 1` panels, closure parameters `0 ≤ λ₀ ≤ 1`, `0 ≤ μ_n ≤ 1` and given values `d₀, d_n`, there
is exactly one cubic spline interpolating the values `f_i` whose moments `M_i = s''(x_i)` satisfy
the two closure conditions `2 M₀ + λ₀ M₁ = d₀` and `μ_n M_{n-1} + 2 M_n = d_n` (uniqueness on
`[a, b]`). `Spline.existsUnique_isCubicInterp_of_closure`. -/
theorem equation_8_48_spline (hn : 1 ≤ n) {lam0 mun : ℝ} (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1)
    (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) (f : ℕ → ℝ) (d0 dn : ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧
        2 * iteratedDerivWithin 2 s (Icc a b) (x 0) + lam0 * iteratedDerivWithin 2 s (Icc a b) (x 1)
          = d0 ∧
        mun * iteratedDerivWithin 2 s (Icc a b) (x (n - 1))
          + 2 * iteratedDerivWithin 2 s (Icc a b) (x n) = dn) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ →
        (2 * iteratedDerivWithin 2 s₁ (Icc a b) (x 0)
          + lam0 * iteratedDerivWithin 2 s₁ (Icc a b) (x 1) = d0 ∧
          mun * iteratedDerivWithin 2 s₁ (Icc a b) (x (n - 1))
            + 2 * iteratedDerivWithin 2 s₁ (Icc a b) (x n) = dn) →
        IsCubicInterpSpline a b n x f s₂ →
        (2 * iteratedDerivWithin 2 s₂ (Icc a b) (x 0)
          + lam0 * iteratedDerivWithin 2 s₂ (Icc a b) (x 1) = d0 ∧
          mun * iteratedDerivWithin 2 s₂ (Icc a b) (x (n - 1))
            + 2 * iteratedDerivWithin 2 s₂ (Icc a b) (x n) = dn) →
        EqOn s₁ s₂ (Icc a b) :=
  Spline.existsUnique_isCubicInterp_of_closure hx hn hl0 hl1 hm0 hm1 f d0 dn

/-- **(8.48), the "popular choice"** `λ₀ = μ_n = 1`, `d₀ = d₁`, `d_n = d_{n-1}`, which
"corresponds to prolongating the spline outside the end points of the interval `[a, b]` and
treating `a` and `b` as internal points": for `n ≥ 2` panels there is exactly one interpolatory
cubic spline with `2 M₀ + M₁ = d₁` and `M_{n-1} + 2 M_n = d_{n-1}`, the `d_i` being those of
(8.47). -/
theorem equation_8_48_prolonged (hn : 2 ≤ n) (f : ℕ → ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧
        2 * iteratedDerivWithin 2 s (Icc a b) (x 0) + 1 * iteratedDerivWithin 2 s (Icc a b) (x 1)
          = 6 / ((x 1 - x 0) + (x 2 - x 1))
            * ((f 2 - f 1) / (x 2 - x 1) - (f 1 - f 0) / (x 1 - x 0)) ∧
        1 * iteratedDerivWithin 2 s (Icc a b) (x (n - 1))
          + 2 * iteratedDerivWithin 2 s (Icc a b) (x n)
          = 6 / ((x (n - 1) - x (n - 1 - 1)) + (x n - x (n - 1)))
            * ((f n - f (n - 1)) / (x n - x (n - 1))
              - (f (n - 1) - f (n - 1 - 1)) / (x (n - 1) - x (n - 1 - 1)))) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ →
        (2 * iteratedDerivWithin 2 s₁ (Icc a b) (x 0)
          + 1 * iteratedDerivWithin 2 s₁ (Icc a b) (x 1)
          = 6 / ((x 1 - x 0) + (x 2 - x 1))
            * ((f 2 - f 1) / (x 2 - x 1) - (f 1 - f 0) / (x 1 - x 0)) ∧
          1 * iteratedDerivWithin 2 s₁ (Icc a b) (x (n - 1))
            + 2 * iteratedDerivWithin 2 s₁ (Icc a b) (x n)
            = 6 / ((x (n - 1) - x (n - 1 - 1)) + (x n - x (n - 1)))
              * ((f n - f (n - 1)) / (x n - x (n - 1))
                - (f (n - 1) - f (n - 1 - 1)) / (x (n - 1) - x (n - 1 - 1)))) →
        IsCubicInterpSpline a b n x f s₂ →
        (2 * iteratedDerivWithin 2 s₂ (Icc a b) (x 0)
          + 1 * iteratedDerivWithin 2 s₂ (Icc a b) (x 1)
          = 6 / ((x 1 - x 0) + (x 2 - x 1))
            * ((f 2 - f 1) / (x 2 - x 1) - (f 1 - f 0) / (x 1 - x 0)) ∧
          1 * iteratedDerivWithin 2 s₂ (Icc a b) (x (n - 1))
            + 2 * iteratedDerivWithin 2 s₂ (Icc a b) (x n)
            = 6 / ((x (n - 1) - x (n - 1 - 1)) + (x n - x (n - 1)))
              * ((f n - f (n - 1)) / (x n - x (n - 1))
                - (f (n - 1) - f (n - 1 - 1)) / (x (n - 1) - x (n - 1 - 1)))) →
        EqOn s₁ s₂ (Icc a b) :=
  equation_8_48_spline hx (by omega) zero_le_one le_rfl zero_le_one le_rfl f _ _

/-! #### The natural, clamped, periodic and not-a-knot splines -/

/-- **The natural cubic spline** (§8.6.1, "in order to obtain the natural splines, satisfying
`s₃''(a) = s₃''(b) = 0`, we must set the above coefficients equal to zero"): there is exactly
one cubic spline interpolating the values `f_i` with the natural end conditions (8.45), `l = 2`;
it is `Spline.naturalInterp n x f` on `[a, b]`. -/
theorem naturalCubicSpline_existsUnique (hn : 1 ≤ n) (f : ℕ → ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧ equation_8_45 a b 2 s) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ → equation_8_45 a b 2 s₁ →
        IsCubicInterpSpline a b n x f s₂ → equation_8_45 a b 2 s₂ → EqOn s₁ s₂ (Icc a b) := by
  have h := Spline.existsUnique_isCubicInterp_of_closure hx hn le_rfl zero_le_one le_rfl
    zero_le_one f 0 0
  simp only [← equation_8_45_two_iff_hasClosure hx] at h
  exact h

/-- **The natural cubic spline is `Spline.naturalInterp`** on `[a, b]`. -/
theorem IsCubicInterpSpline.eqOn_naturalInterp (hn : 1 ≤ n) (hs : IsCubicInterpSpline a b n x f s)
    (hnat : equation_8_45 a b 2 s) : EqOn s (Spline.naturalInterp n x f) (Icc a b) :=
  hs.eqOn_cubicInterp hx hn le_rfl zero_le_one le_rfl zero_le_one
    ((equation_8_45_two_iff_hasClosure hx).mp hnat)

/-- **The clamped end conditions are a closure of type (8.48)**: if the cubic spline `s`
interpolating the values `f_i` has `s'(a) = f'₀` and `s'(b) = f'_n` (derivatives within `[a, b]`),
its moments satisfy `2 M₀ + M₁ = (6/h₁)((f₁ - f₀)/h₁ - f'₀)` and
`M_{n-1} + 2 M_n = (6/h_n)(f'_n - (f_n - f_{n-1})/h_n)`, by the one-sided slope formulas displayed
before (8.47). -/
-- TODO(backbone): belongs to `Numlib/Approximation/Spline` beside `deriv_clampedInterp_endpoints`,
-- as the converse direction of the clamped closure.
theorem IsCubicInterpSpline.hasClosure_of_derivWithin (hn : 1 ≤ n)
    (hs : IsCubicInterpSpline a b n x f s) {f'0 f'n : ℝ} (h0 : derivWithin s (Icc a b) a = f'0)
    (h1 : derivWithin s (Icc a b) b = f'n) :
    Spline.HasClosure a b n x 1 1 (6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0))
      (6 / (x n - x (n - 1)) * (f'n - (f n - f (n - 1)) / (x n - x (n - 1)))) s := by
  have hA := hs.derivWithin_left hx hn
  have hB := hs.derivWithin_right hx hn
  have hl : x 0 < x 1 := hx.step 0 hn
  have hr : x (n - 1) < x n := hx.lt (Nat.sub_one_lt_of_le hn le_rfl) le_rfl
  rw [h0, Spline.panelCubicD1_left hl] at hA
  rw [h1, Spline.panelCubicD1_right hr] at hB
  have hl' : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr hl.ne'
  have hr' : x n - x (n - 1) ≠ 0 := sub_ne_zero.mpr hr.ne'
  refine ⟨?_, ?_⟩
  · rw [hA]; field_simp; ring
  · rw [hB]; field_simp; ring

/-- **The clamped (constrained) cubic spline** (§8.6.1, the closure "of the form" (8.48) with
`λ₀ = μ_n = 1` when the derivatives `f'(a)`, `f'(b)` are available; Exercise 11): for any
prescribed end slopes `f'₀, f'_n` there is exactly one cubic spline interpolating the values `f_i`
with `s'(a) = f'₀` and `s'(b) = f'_n` (derivatives within `[a, b]`); it is
`Spline.clampedInterp n x f f'₀ f'_n` on `[a, b]`. -/
theorem clampedCubicSpline_existsUnique (hn : 1 ≤ n) (f : ℕ → ℝ) (f'0 f'n : ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧ derivWithin s (Icc a b) a = f'0 ∧
        derivWithin s (Icc a b) b = f'n) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ →
        derivWithin s₁ (Icc a b) a = f'0 ∧ derivWithin s₁ (Icc a b) b = f'n →
        IsCubicInterpSpline a b n x f s₂ →
        derivWithin s₂ (Icc a b) a = f'0 ∧ derivWithin s₂ (Icc a b) b = f'n →
        EqOn s₁ s₂ (Icc a b) := by
  have hab := hx.lt_of_pos hn
  refine ⟨⟨Spline.clampedInterp n x f f'0 f'n,
    (Spline.isCubicInterp_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl).1, ?_, ?_⟩,
    fun s₁ s₂ h₁ hc₁ h₂ hc₂ => ?_⟩
  · rw [((Spline.contDiff_clampedInterp hx hn f'0 f'n).differentiable (by norm_num) a).derivWithin
      (uniqueDiffOn_Icc hab a (left_mem_Icc.mpr hab.le))]
    exact (Spline.deriv_clampedInterp_endpoints hx hn f'0 f'n).1
  · rw [((Spline.contDiff_clampedInterp hx hn f'0 f'n).differentiable (by norm_num) b).derivWithin
      (uniqueDiffOn_Icc hab b (right_mem_Icc.mpr hab.le))]
    exact (Spline.deriv_clampedInterp_endpoints hx hn f'0 f'n).2
  · exact h₁.eqOn_of_hasClosure hx hn zero_le_one le_rfl zero_le_one le_rfl
      (h₁.hasClosure_of_derivWithin hx hn hc₁.1 hc₁.2) h₂
      (h₂.hasClosure_of_derivWithin hx hn hc₂.1 hc₂.2)

/-- **The clamped cubic spline is `Spline.clampedInterp`** on `[a, b]`. -/
theorem IsCubicInterpSpline.eqOn_clampedInterp (hn : 1 ≤ n) (hs : IsCubicInterpSpline a b n x f s)
    {f'0 f'n : ℝ} (h0 : derivWithin s (Icc a b) a = f'0) (h1 : derivWithin s (Icc a b) b = f'n) :
    EqOn s (Spline.clampedInterp n x f f'0 f'n) (Icc a b) :=
  hs.eqOn_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl
    (hs.hasClosure_of_derivWithin hx hn h0 h1)

/-- **The periodic cubic spline** ((8.44) with `k = 3`): for data with `f₀ = f_n` and `n ≥ 2`
panels there is exactly one cubic spline interpolating the values `f_i` with the periodic end
conditions `s(a) = s(b)`, `s'(a) = s'(b)`, `s''(a) = s''(b)`; the uniqueness needs only the two
derivative conditions. `Spline.existsUnique_isCubicInterp_periodic`. -/
theorem periodicCubicSpline_existsUnique (hn : 2 ≤ n) (hf : f 0 = f n) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧ equation_8_44 a b 3 s) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ → equation_8_44 a b 3 s₁ →
        IsCubicInterpSpline a b n x f s₂ → equation_8_44 a b 3 s₂ → EqOn s₁ s₂ (Icc a b) := by
  obtain ⟨⟨s, hs, hp⟩, huniq⟩ := Spline.existsUnique_isCubicInterp_periodic hx hn f
  refine ⟨⟨s, hs, (equation_8_44_three_iff).mpr ⟨?_, hp⟩⟩, fun s₁ s₂ h₁ hp₁ h₂ hp₂ =>
    huniq s₁ s₂ h₁ ((equation_8_44_three_iff).mp hp₁).2 h₂ ((equation_8_44_three_iff).mp hp₂).2⟩
  rw [← hx.first, ← hx.last, hs.interp 0 (Nat.zero_le n), hs.interp n le_rfl, hf]

/-- **The not-a-knot spline** (§8.6.1): the closure enforcing the continuity of `s₃'''` at `x₁`
and at `x_{n-1}` — since `s₃'''` is constant on each panel, this says that the cubic pieces on
the first two and on the last two panels coincide, `Spline.IsNotAKnot n x s`, so that the "active"
knots are `x₀, x₂, …, x_{n-2}, x_n`. For `n ≥ 3` panels there is exactly one such cubic spline
interpolating the values `f_i` (`Spline.existsUnique_isCubicInterp_notAKnot`); the hypothesis
`n ≥ 3`, not in the book, is necessary: for `n = 2` the two conditions coincide. -/
theorem notAKnotSpline_existsUnique (hn : 3 ≤ n) (f : ℕ → ℝ) :
    (∃ s, IsCubicInterpSpline a b n x f s ∧ Spline.IsNotAKnot n x s) ∧
      ∀ s₁ s₂, IsCubicInterpSpline a b n x f s₁ → Spline.IsNotAKnot n x s₁ →
        IsCubicInterpSpline a b n x f s₂ → Spline.IsNotAKnot n x s₂ → EqOn s₁ s₂ (Icc a b) :=
  Spline.existsUnique_isCubicInterp_notAKnot hx hn f

/-! #### The cardinal spline basis -/

variable (hn : 1 ≤ n)
include hn

/-- The clamped spline is an interpolatory cubic spline of its data. -/
-- TODO(backbone): belongs to `Numlib/Approximation/Spline` beside `contDiff_clampedInterp`.
theorem isCubicInterp_clampedInterp (f : ℕ → ℝ) (f'0 f'n : ℝ) :
    Spline.IsCubicInterp a b n x f (Spline.clampedInterp n x f f'0 f'n) :=
  (Spline.isCubicInterp_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl).1

/-- Every cardinal function is a `C²` piecewise cubic on the partition. -/
theorem isCubicSpline_cardinalBasis (i : ℕ) :
    Spline.IsCubicSpline a b n x (Spline.cardinalBasis n x i) := by
  unfold Spline.cardinalBasis
  split_ifs <;> exact (isCubicInterp_clampedInterp hx hn _ _ _).toIsCubicSpline

/-- Every cardinal function is `C²` on `ℝ`. -/
theorem contDiff_cardinalBasis (i : ℕ) : ContDiff ℝ 2 (Spline.cardinalBasis n x i) := by
  unfold Spline.cardinalBasis
  split_ifs <;> exact Spline.contDiff_clampedInterp hx hn _ _

/-- **The cardinal spline basis, the interpolation constraints** (§8.6.1): the functions
`φ_i`, `i = 0, …, n + 2`, satisfy `φ_i(x_j) = δ_ij` for `i, j ≤ n`, and `φ_{n+1}`, `φ_{n+2}` vanish
at every node. `Spline.cardinalBasis_apply_node`. -/
theorem cardinalSplineBasis_apply_node (i : ℕ) {j : ℕ} (hj : j ≤ n) :
    Spline.cardinalBasis n x i (x j) = if i = j then 1 else 0 :=
  Spline.cardinalBasis_apply_node hx hn i hj

/-- **The cardinal spline basis, the slopes at `x₀ = a`**: `φ_i'(x₀) = 0` for `i ≤ n`,
`φ_{n+1}'(x₀) = 1` and `φ_{n+2}'(x₀) = 0`, as derivatives within `[a, b]`. -/
theorem derivWithin_cardinalSplineBasis_left (i : ℕ) :
    derivWithin (Spline.cardinalBasis n x i) (Icc a b) a = if i = n + 1 then 1 else 0 := by
  have hab := hx.lt_of_pos hn
  rw [((contDiff_cardinalBasis hx hn i).differentiable (by norm_num) a).derivWithin
    (uniqueDiffOn_Icc hab a (left_mem_Icc.mpr hab.le))]
  exact Spline.deriv_cardinalBasis_left hx hn i

/-- **The cardinal spline basis, the slopes at `x_n = b`**: `φ_i'(x_n) = 0` for `i ≤ n + 1` and
`φ_{n+2}'(x_n) = 1`, as derivatives within `[a, b]`. -/
theorem derivWithin_cardinalSplineBasis_right {i : ℕ} (hi : i ≤ n + 2) :
    derivWithin (Spline.cardinalBasis n x i) (Icc a b) b = if i = n + 2 then 1 else 0 := by
  have hab := hx.lt_of_pos hn
  rw [((contDiff_cardinalBasis hx hn i).differentiable (by norm_num) b).derivWithin
    (uniqueDiffOn_Icc hab b (right_mem_Icc.mpr hab.le))]
  exact Spline.deriv_cardinalBasis_right hx hn hi

/-- **The cardinal spline basis** (§8.6.1): the `n + 3` cubic splines `φ_0, …, φ_{n+2}` defined by
the interpolation constraints `φ_i(x_j) = δ_ij`, `φ_i'(x₀) = φ_i'(x_n) = 0` (`i ≤ n`),
`φ_{n+1}(x_j) = 0`, `φ_{n+1}'(x₀) = 1`, `φ_{n+1}'(x_n) = 0`, `φ_{n+2}(x_j) = 0`,
`φ_{n+2}'(x₀) = 0`, `φ_{n+2}'(x_n) = 1` — the functions `Spline.cardinalBasis n x i` — form a basis
of `𝒮_3`, "whose dimension is equal to `n + 3`": they are linearly independent, a vanishing
combination being evaluated at the nodes and differentiated at the endpoints, and there are
`n + 3 = dim 𝒮_3` of them. -/
theorem cardinalSplineBasis :
    ∃ B : Module.Basis (Fin (n + 3)) ℝ (definition_8_1 a b n x 3),
      ∀ (i : Fin (n + 3)) (t : Icc a b),
        (B i : C(Icc a b, ℝ)) t = Spline.cardinalBasis n x i t := by
  classical
  have hab := hx.lt_of_pos hn
  set v : Fin (n + 3) → definition_8_1 a b n x 3 := fun i =>
    ⟨_, mem_definition_8_1_three_of_isCubicSpline (isCubicSpline_cardinalBasis hx hn i)⟩ with hv
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    -- the vanishing combination, as a function on `ℝ`
    set Φ : ℝ → ℝ := fun t => ∑ i : Fin (n + 3), g i * Spline.cardinalBasis n x i t with hΦ
    have hΦ0 : EqOn Φ 0 (Icc a b) := by
      intro t ht
      have := congrArg (fun w : definition_8_1 a b n x 3 => (w : C(Icc a b, ℝ)) ⟨t, ht⟩) hg
      simpa [hv, hΦ, Submodule.coe_sum, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.coe_mk, Set.domRestrict_apply] using this
    have hΦd : ∀ t, HasDerivAt Φ (∑ i : Fin (n + 3), g i * deriv (Spline.cardinalBasis n x i) t)
        t := by
      intro t
      rw [hΦ]
      exact HasDerivAt.fun_sum fun (i : Fin (n + 3)) _ =>
        (((contDiff_cardinalBasis hx hn i).differentiable (by norm_num) t).hasDerivAt).const_mul
          (g i)
    have hderiv : ∀ t ∈ Icc a b, ∑ i : Fin (n + 3), g i * deriv (Spline.cardinalBasis n x i) t
        = 0 := by
      intro t ht
      rw [← HasDerivWithinAt.derivWithin (HasDerivAt.hasDerivWithinAt (hΦd t))
        (uniqueDiffOn_Icc hab t ht), derivWithin_congr hΦ0 (hΦ0 ht)]
      simp
    have hsingle : ∀ j : Fin (n + 3),
        ∑ i : Fin (n + 3), g i * (if (i : ℕ) = j then 1 else 0) = g j := by
      intro j
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        rw [ite_eq_right (fun h => hij (Fin.ext h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    -- the coefficients of `φ_0, …, φ_n`
    have hnode : ∀ j : Fin (n + 3), (j : ℕ) ≤ n → g j = 0 := by
      intro j hj
      have := hΦ0 ⟨hx.left_le hj, hx.le_right hj⟩
      simp only [hΦ, Pi.zero_apply, cardinalSplineBasis_apply_node hx hn _ hj] at this
      rwa [hsingle j] at this
    -- the coefficients of `φ_{n+1}` and `φ_{n+2}`
    have hleft := hderiv a (left_mem_Icc.mpr hab.le)
    have hright := hderiv b (right_mem_Icc.mpr hab.le)
    simp only [Spline.deriv_cardinalBasis_left hx hn] at hleft
    have hright' : ∑ i : Fin (n + 3), g i * (if (i : ℕ) = n + 2 then 1 else 0) = 0 := by
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hright
      rw [Spline.deriv_cardinalBasis_right hx hn (Nat.lt_succ_iff.mp i.2)]
    rw [hsingle ⟨n + 1, by omega⟩] at hleft
    rw [hsingle ⟨n + 2, by omega⟩] at hright'
    intro i
    rcases Nat.lt_or_ge (i : ℕ) (n + 1) with hi | hi
    · exact hnode i (by omega)
    · rcases Nat.lt_or_ge (i : ℕ) (n + 2) with hi' | hi'
      · have hi1 : i = ⟨n + 1, by omega⟩ := Fin.ext (show (i : ℕ) = n + 1 by omega)
        rw [hi1]
        exact hleft
      · have hi2 : i = ⟨n + 2, by omega⟩ := Fin.ext (show (i : ℕ) = n + 2 by omega)
        rw [hi2]
        exact hright'
  have hcard : Fintype.card (Fin (n + 3)) = Module.finrank ℝ (definition_8_1 a b n x 3) := by
    rw [Fintype.card_fin, definition_8_1_finrank hx hn (by norm_num)]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i t => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-- **The clamped spline in the cardinal basis** (§8.6.1): the cubic spline interpolating the
values `f_i` with `s'(x₀) = f'₀` and `s'(x_n) = f'_n` takes the form

`s₃(x) = ∑_{i=0}^{n} f_i φ_i(x) + f'₀ φ_{n+1}(x) + f'_n φ_{n+2}(x)` on `[a, b]`.

`Spline.clampedInterp_eq_sum_cardinalBasis`. -/
theorem cardinalSplineBasis_clampedInterp (hs : IsCubicInterpSpline a b n x f s) {f'0 f'n : ℝ}
    (h0 : derivWithin s (Icc a b) a = f'0) (h1 : derivWithin s (Icc a b) b = f'n) :
    EqOn s (∑ i ∈ Finset.range (n + 1), f i • Spline.cardinalBasis n x i
        + f'0 • Spline.cardinalBasis n x (n + 1) + f'n • Spline.cardinalBasis n x (n + 2))
      (Icc a b) :=
  (hs.eqOn_clampedInterp hx hn h0 h1).trans
    (Spline.clampedInterp_eq_sum_cardinalBasis hn f f'0 f'n ▸ fun _ _ => rfl)

/-! #### Property 8.2: the minimum norm property -/

variable {F : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Icc a b))
include hF

/-- **Property 8.2 (Holladay's minimum norm property).** Let `f ∈ C²([a, b])` and let `s₃` be the
natural cubic spline interpolating `f` at the nodes. Then

`∫_a^b [s₃''(x)]² dx ≤ ∫_a^b [f''(x)]² dx` (8.49),

the second derivatives being taken within `[a, b]`. `Spline.integral_sq_deriv2_le_of_end`, from
the orthogonality identity `∫ (f'' - s₃'') s₃'' = 0` obtained by integrating by parts on every
panel. -/
theorem property_8_2 (hs : IsCubicInterpSpline a b n x (fun i => F (x i)) s)
    (hnat : equation_8_45 a b 2 s) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 F (Icc a b) t ^ 2 :=
  Spline.integral_sq_deriv2_le_of_end hx hn hF hs (Or.inl ((equation_8_45_two_iff).mp hnat))

/-- **Property 8.2, the equality case**: equality holds in (8.49) if and only if `f = s₃` on
`[a, b]`. `Spline.eqOn_of_integral_sq_deriv2_eq` for the forward direction; the converse is the
congruence of the second derivatives within `[a, b]`. -/
theorem property_8_2_eq_iff (hs : IsCubicInterpSpline a b n x (fun i => F (x i)) s)
    (hnat : equation_8_45 a b 2 s) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      = ∫ t in a..b, iteratedDerivWithin 2 F (Icc a b) t ^ 2 ↔ EqOn F s (Icc a b) := by
  refine ⟨Spline.eqOn_of_integral_sq_deriv2_eq hx hn hF hs
    (Or.inl ((equation_8_45_two_iff).mp hnat)), fun heq => ?_⟩
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (hx.lt_of_pos hn).le] at ht
  rw [iteratedDerivWithin_congr heq ht]

/-- **Exercise 8.11.** Property 8.2 holds also for the constrained spline, the cubic spline
interpolating `f ∈ C²([a, b])` at the nodes with `s'(a) = f'(a)` and `s'(b) = f'(b)`:
`∫_a^b [s''(x)]² dx ≤ ∫_a^b [f''(x)]² dx`. The hint's integration by parts is the backbone's
`Spline.integral_sub_deriv2_mul_deriv2_eq`, whose boundary terms `[(f' - s') s'']_a^b` vanish
under the clamped conditions. -/
theorem exercise_8_11 (hs : IsCubicInterpSpline a b n x (fun i => F (x i)) s)
    (h0 : derivWithin s (Icc a b) a = derivWithin F (Icc a b) a)
    (h1 : derivWithin s (Icc a b) b = derivWithin F (Icc a b) b) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 F (Icc a b) t ^ 2 :=
  Spline.integral_sq_deriv2_le_of_end hx hn hF hs (Or.inr ⟨h0, h1⟩)

/-- **Exercise 8.11, the equality case**: for the constrained spline too, equality holds if and
only if `f = s` on `[a, b]`. -/
theorem exercise_8_11_eq_iff (hs : IsCubicInterpSpline a b n x (fun i => F (x i)) s)
    (h0 : derivWithin s (Icc a b) a = derivWithin F (Icc a b) a)
    (h1 : derivWithin s (Icc a b) b = derivWithin F (Icc a b) b) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      = ∫ t in a..b, iteratedDerivWithin 2 F (Icc a b) t ^ 2 ↔ EqOn F s (Icc a b) := by
  refine ⟨Spline.eqOn_of_integral_sq_deriv2_eq hx hn hF hs (Or.inr ⟨h0, h1⟩), fun heq => ?_⟩
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (hx.lt_of_pos hn).le] at ht
  rw [iteratedDerivWithin_congr heq ht]

/-- **The best approximation property of the clamped spline** (§8.6.1, the display after
Property 8.2). The cubic interpolating spline `s_f` of a function `f ∈ C²([a, b])` with
`s_f'(a) = f'(a)` and `s_f'(b) = f'(b)` satisfies

`∫_a^b [f''(x) - s_f''(x)]² dx ≤ ∫_a^b [f''(x) - s''(x)]² dx` for all `s ∈ 𝒮_3`,

`𝒮_3` being the `C²` piecewise cubics on the partition (`Spline.IsCubicSpline`, see
`mem_definition_8_1_three_iff`). `Spline.integral_sq_sub_deriv2_clampedInterp_le` for
`s_f = Spline.clampedInterp`, to which any such `s_f` is equal on `[a, b]`. -/
theorem clampedSpline_bestApprox_deriv2 {sf : ℝ → ℝ}
    (hsf : IsCubicInterpSpline a b n x (fun i => F (x i)) sf)
    (h0 : derivWithin sf (Icc a b) a = derivWithin F (Icc a b) a)
    (h1 : derivWithin sf (Icc a b) b = derivWithin F (Icc a b) b)
    (hs : Spline.IsCubicSpline a b n x s) :
    ∫ t in a..b, (iteratedDerivWithin 2 F (Icc a b) t - iteratedDerivWithin 2 sf (Icc a b) t) ^ 2
      ≤ ∫ t in a..b,
          (iteratedDerivWithin 2 F (Icc a b) t - iteratedDerivWithin 2 s (Icc a b) t) ^ 2 := by
  have heq := hsf.eqOn_clampedInterp hx hn h0 h1
  have hcongr : ∀ t ∈ uIcc a b, (iteratedDerivWithin 2 F (Icc a b) t
      - iteratedDerivWithin 2 sf (Icc a b) t) ^ 2
      = (iteratedDerivWithin 2 F (Icc a b) t - iteratedDerivWithin 2 (Spline.clampedInterp n x
          (fun i => F (x i)) (derivWithin F (Icc a b) a) (derivWithin F (Icc a b) b))
            (Icc a b) t) ^ 2 := by
    intro t ht
    rw [uIcc_of_le (hx.lt_of_pos hn).le] at ht
    rw [iteratedDerivWithin_congr heq ht]
  rw [intervalIntegral.integral_congr hcongr]
  exact Spline.integral_sq_sub_deriv2_clampedInterp_le hx hn hF hs

end Cubic

/-! #### Property 8.3: the error of the clamped interpolatory cubic spline -/

/-- **Property 8.3 with non-sharp constants.** Let `f ∈ C⁴([a, b])` with `|f⁗| ≤ K` on `[a, b]`,
let `a = x₀ < ⋯ < x_n = b` be a partition whose panels all have length at most `h`, and let `s₃` be
the **clamped** interpolatory cubic spline of `f` (`s₃'(a) = f'(a)`, `s₃'(b) = f'(b)`). Then

`‖f - s₃‖_∞ ≤ (7/8) h⁴ K`, `‖f' - s₃'‖_∞ ≤ (7/4) h³ K`, `|f''(x_i) - s₃''(x_i)| ≤ (3/4) h² K`.

This is Property 8.3 of [quarteroni2000numerical] for `r = 0, 1, 2` with the constants `7/8`, `7/4`
and `3/4` in place of the book's sharp `5/384`, `1/24` and `3/8`, and with the case `r = 2`
restricted to the nodes. The book states Property 8.3 without proof and without saying which end
conditions it means; the sharp constants are those of Hall and Meyer for the clamped spline (see
the plan node `property_8_3`), and for the natural spline the `O(h⁴)` rate fails altogether. The
backbone bounds are `Spline.norm_sub_clampedInterp_le`, `Spline.norm_deriv_sub_clampedInterp_le`
and `Spline.norm_deriv2_sub_clampedInterp_le`; `IsCubicInterpSpline.eqOn_clampedInterp` identifies
any clamped interpolatory cubic spline with `Spline.clampedInterp` on `[a, b]`. -/
theorem property_8_3_weak {f : ℝ → ℝ} {K hm : ℝ} (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (hf : ContDiff ℝ 4 f) (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    (hmesh : ∀ i, 1 ≤ i → i ≤ n → Spline.panelLength x i ≤ hm) :
    (∀ t ∈ Icc a b, |f t - Spline.clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) t|
        ≤ 7 / 8 * hm ^ 4 * K) ∧
      (∀ t ∈ Icc a b, |deriv f t
        - deriv (Spline.clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b)) t|
        ≤ 7 / 4 * hm ^ 3 * K) ∧
      (∀ i ≤ n, |iteratedDeriv 2 f (x i)
        - iteratedDeriv 2 (Spline.clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b))
            (x i)| ≤ 3 / 4 * hm ^ 2 * K) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun i hi => ?_⟩
  · rw [abs_sub_comm]
    exact Spline.norm_sub_clampedInterp_le hx hn hf hK hmesh ht
  · rw [abs_sub_comm]
    exact Spline.norm_deriv_sub_clampedInterp_le hx hn hf hK hmesh ht
  · rw [abs_sub_comm]
    exact Spline.norm_deriv2_sub_clampedInterp_le hx hn hf hK hmesh hi

/-! ### §8.6.2: B-splines -/

/-- **Definition 8.2, the normalized B-spline.** The normalized B-spline `B_{i,k+1}` of degree `k`
relative to the distinct nodes `x_i, …, x_{i+k+1}` is

`B_{i,k+1}(x) = (x_{i+k+1} - x_i) g[x_i, …, x_{i+k+1}]` (8.51), where `g(t) = (t - x)_+^k` (8.52),

`g[x_i, …, x_{i+k+1}]` being the Newton divided difference of §8.2 and `(t - x)_+^k` the truncated
power `Quadrature.truncPow k t x`. This is the backbone's divided-difference form `BSpline.nform`;
`definition_8_2_eq_bspline` identifies it with the Cox–de Boor B-spline `BSpline.bspline x k i`. -/
noncomputable def definition_8_2 (x : ℕ → ℝ) (k i : ℕ) : ℝ → ℝ :=
  BSpline.nform x k i

/-- **(8.51)–(8.52) unfolded.** -/
theorem definition_8_2_apply (x : ℕ → ℝ) (k i : ℕ) (t : ℝ) :
    definition_8_2 x k i t = (x (i + k + 1) - x i) *
      DividedDifference.newton (fun s => Quadrature.truncPow k s t)
        fun j : Fin (k + 2) => x (i + j) :=
  rfl

/-- **Definition 8.2 agrees with the recursive B-spline**: for strictly increasing knots and
`k ≥ 1`, the divided-difference B-spline of Definition 8.2 is `BSpline.bspline x k i`, the
B-spline of the Cox–de Boor recursion (8.54). (For `k = 0` the two differ at the knots: Definition
8.2 gives the indicator of `(x_i, x_{i+1}]`, the recursion that of `[x_i, x_{i+1})`.)
`BSpline.nform_eq_bspline`. -/
theorem definition_8_2_eq_bspline (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) :
    definition_8_2 x k i = BSpline.bspline x k i :=
  BSpline.nform_eq_bspline hx hk i

/-- **(8.53), the explicit representation.** Substituting (8.18) into (8.51),

`B_{i,k+1}(x) = (x_{i+k+1} - x_i) ∑_{j=0}^{k+1} (x_{i+j} - x)_+^k / ∏_{l ≠ j} (x_{i+j} - x_{i+l})`,

which is the definition of the divided difference unfolded. -/
theorem equation_8_53 (x : ℕ → ℝ) (k i : ℕ) (t : ℝ) :
    definition_8_2 x k i t = (x (i + k + 1) - x i) * ∑ j : Fin (k + 2),
      Quadrature.truncPow k (x (i + j)) t / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l)) :=
  rfl

/-- **Support** (§8.6.2): "`B_{i,k+1}(x)` is non null only within the interval `[x_i, x_{i+k+1}]`",
for nondecreasing knots. `BSpline.bspline_eq_zero_of_notMem` (which gives the sharper half-open
support `[x_i, x_{i+k+1})`). -/
theorem bSpline_support (hx : Monotone x) {i : ℕ} {t : ℝ} (ht : t ∉ Icc (x i) (x (i + k + 1))) :
    BSpline.bspline x k i t = 0 :=
  BSpline.bspline_eq_zero_of_notMem hx fun h => ht (Ico_subset_Icc_self h)

/-- **Positivity** (§8.6.2, quoted from de Boor): `B_{i,k+1}(x) ≥ 0` for nondecreasing knots.
`BSpline.bspline_nonneg`. -/
theorem bSpline_nonneg (hx : Monotone x) (i : ℕ) (t : ℝ) : 0 ≤ BSpline.bspline x k i t :=
  BSpline.bspline_nonneg hx

/-- **(8.54), the degree-zero B-spline**: `B_{i,1}` is `1` on `[x_i, x_{i+1})` and `0` otherwise.
The book prints the closed interval `[x_i, x_{i+1}]`, which cannot be right at the shared knots
(the partition of unity would fail); the half-open interval is the reading used. This is the
definition `BSpline.bspline_zero`. -/
theorem equation_8_54_zero (x : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    BSpline.bspline x 0 i t = if t ∈ Ico (x i) (x (i + 1)) then 1 else 0 :=
  BSpline.bspline_zero x i t

/-- **(8.54), the Cox–de Boor recursion**: for strictly increasing knots and `k ≥ 0`,

`B_{i,k+2}(x) = (x - x_i)/(x_{i+k+1} - x_i) B_{i,k+1}(x)
+ (x_{i+k+2} - x)/(x_{i+k+2} - x_{i+1}) B_{i+1,k+1}(x)`,

the book's second line of (8.54) written for the degree `k + 1` (its `k ≥ 1` is the order).
`BSpline.bspline_succ`, the weights `BSpline.weight` being the displayed quotients when the knots
are distinct. -/
theorem equation_8_54 (hx : StrictMono x) (k i : ℕ) (t : ℝ) :
    BSpline.bspline x (k + 1) i t
      = (t - x i) / (x (i + k + 1) - x i) * BSpline.bspline x k i t
        + (x (i + k + 2) - t) / (x (i + k + 2) - x (i + 1)) * BSpline.bspline x k (i + 1) t := by
  rw [BSpline.bspline_succ]
  simp only [BSpline.weight]
  have h1 : x (i + (k + 1)) ≠ x i := (hx (by omega : i < i + (k + 1))).ne'
  have h2 : x (i + 1 + (k + 1)) ≠ x (i + 1) := (hx (by omega : i + 1 < i + 1 + (k + 1))).ne'
  rw [ite_eq_right h1, ite_eq_right h2, show i + (k + 1) = i + k + 1 by omega,
    show i + 1 + (k + 1) = i + k + 2 by omega]
  have h2' : x (i + k + 2) - x (i + 1) ≠ 0 := by
    rw [show i + k + 2 = i + 1 + (k + 1) by omega]
    exact sub_ne_zero.mpr h2
  have h3 : 1 - (t - x (i + 1)) / (x (i + k + 2) - x (i + 1))
      = (x (i + k + 2) - t) / (x (i + k + 2) - x (i + 1)) := by
    field_simp
    ring
  rw [h3]

/-- **(8.54) for the B-splines of Definition 8.2**: the divided-difference B-splines satisfy the
Cox–de Boor recursion, for strictly increasing knots and degrees `k ≥ 1`; this is the book's claim
that the recursion "is usually preferred to (8.53) when evaluating a B-spline". -/
theorem equation_8_54_definition_8_2 (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) (t : ℝ) :
    definition_8_2 x (k + 1) i t
      = (t - x i) / (x (i + k + 1) - x i) * definition_8_2 x k i t
        + (x (i + k + 2) - t) / (x (i + k + 2) - x (i + 1)) * definition_8_2 x k (i + 1) t := by
  rw [definition_8_2_eq_bspline hx (by omega), definition_8_2_eq_bspline hx hk,
    definition_8_2_eq_bspline hx hk]
  exact equation_8_54 hx k i t

/-- **Remark 8.3, confluent divided differences**: the Newton divided differences extended to
partially coincident nodes by the recursion

`f[x₀, …, x_n] = (f[x₁, …, x_n] - f[x₀, …, x_{n-1}])/(x_n - x₀)` if `x₀ < x_n`, and
`f[x₀, …, x_n] = f^{(n)}(x₀)/n!` if `x₀ = x₁ = ⋯ = x_n`

(the book prints `f^{(n+1)}(x₀)/(n+1)!` in the second case, a misprint: `f[x₀, x₀] = f'(x₀)`).
The backbone's `DividedDifference.confluent`. -/
noncomputable def remark_8_3_confluent (f : ℝ → ℝ) {m : ℕ} (v : Fin (m + 1) → ℝ) : ℝ :=
  DividedDifference.confluent f v

/-- **Remark 8.3, the recursion at distinct end nodes**: when `x₀ < x_n`,
`f[x₀, …, x_n] = (f[x₁, …, x_n] - f[x₀, …, x_{n-1}])/(x_n - x₀)`. -/
theorem remark_8_3_confluent_of_lt (f : ℝ → ℝ) {m : ℕ} {v : Fin (m + 2) → ℝ}
    (h : v 0 < v (Fin.last (m + 1))) :
    remark_8_3_confluent f v
      = (remark_8_3_confluent f (Fin.tail v) - remark_8_3_confluent f (Fin.init v))
        / (v (Fin.last (m + 1)) - v 0) := by
  rw [remark_8_3_confluent, DividedDifference.confluent_succ, ite_eq_right h.ne]
  rfl

/-- **Remark 8.3, coincident nodes**: at `n + 1` copies of one node `x₀`,
`f[x₀, …, x₀] = f^{(n)}(x₀)/n!`. `DividedDifference.confluent_const`. -/
theorem remark_8_3_confluent_const (f : ℝ → ℝ) (m : ℕ) (x₀ : ℝ) :
    remark_8_3_confluent f (fun _ : Fin (m + 1) => x₀) = iteratedDeriv m f x₀ / m.factorial :=
  DividedDifference.confluent_const f x₀

/-- **Remark 8.3, distinct nodes**: at distinct nodes the confluent divided difference is the
Newton divided difference of §8.2. `DividedDifference.confluent_eq_newton`. -/
theorem remark_8_3_confluent_eq (f : ℝ → ℝ) {m : ℕ} {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) : remark_8_3_confluent f v = DividedDifference.newton f v :=
  DividedDifference.confluent_eq_newton f hv

/-- **Remark 8.3, `k + 1` coincident knots at the left**: if
`x_{i-1} < x_i = ⋯ = x_{i+k} < x_{i+k+1}`, then
`B_{i,k+1}(x) = ((x_{i+k+1} - x)/(x_{i+k+1} - x_i))^k` on `[x_i, x_{i+k+1})` and `0` otherwise;
the hypothesis `x_{i-1} < x_i` is not needed. (The book prints the closed interval, where the
formula gives `0` at the right end anyway.) `BSpline.bspline_apply_of_coincident_left`. -/
theorem remark_8_3_left {i : ℕ} (hcoin : ∀ j, i ≤ j → j ≤ i + k → x j = x i)
    (hlt : x i < x (i + k + 1)) (t : ℝ) :
    BSpline.bspline x k i t = if t ∈ Ico (x i) (x (i + k + 1)) then
      ((x (i + k + 1) - t) / (x (i + k + 1) - x i)) ^ k else 0 :=
  BSpline.bspline_apply_of_coincident_left hcoin hlt t

/-- **Remark 8.3, `k + 1` coincident knots at the right**: for nondecreasing knots with
`x_i < x_{i+1} = ⋯ = x_{i+k+1}` (`< x_{i+k+2}` is not needed),
`B_{i,k+1}(x) = ((x - x_i)/(x_{i+k+1} - x_i))^k` on `[x_i, x_{i+k+1})` and `0` otherwise.
`BSpline.bspline_apply_of_coincident_right`. -/
theorem remark_8_3_right (hx : Monotone x) {i : ℕ}
    (hcoin : ∀ j, i + 1 ≤ j → j ≤ i + k + 1 → x j = x (i + k + 1)) (hlt : x i < x (i + k + 1))
    (t : ℝ) :
    BSpline.bspline x k i t = if t ∈ Ico (x i) (x (i + k + 1)) then
      ((t - x i) / (x (i + k + 1) - x i)) ^ k else 0 :=
  BSpline.bspline_apply_of_coincident_right hx hcoin hlt t

/-- **Example 8.9, the cubic B-spline on equally spaced knots** `x_{i+1} = x_i + h`:

`6 h³ B_{i,4}(x)` is `(x - x_i)³` on `[x_i, x_{i+1})`,
`h³ + 3h²(x - x_{i+1}) + 3h(x - x_{i+1})² - 3(x - x_{i+1})³` on `[x_{i+1}, x_{i+2})`,
`h³ + 3h²(x_{i+3} - x) + 3h(x_{i+3} - x)² - 3(x_{i+3} - x)³` on `[x_{i+2}, x_{i+3})`,
`(x_{i+4} - x)³` on `[x_{i+3}, x_{i+4})`, and `0` otherwise.

`BSpline.bspline_uniform_cubic`. -/
theorem example_8_9 {x₀ h : ℝ} (hh : 0 < h) (hx : ∀ j, x j = x₀ + j * h) (i : ℕ) (t : ℝ) :
    6 * h ^ 3 * BSpline.bspline x 3 i t =
      if t ∈ Ico (x i) (x (i + 1)) then (t - x i) ^ 3
      else if t ∈ Ico (x (i + 1)) (x (i + 2)) then
        h ^ 3 + 3 * h ^ 2 * (t - x (i + 1)) + 3 * h * (t - x (i + 1)) ^ 2 - 3 * (t - x (i + 1)) ^ 3
      else if t ∈ Ico (x (i + 2)) (x (i + 3)) then
        h ^ 3 + 3 * h ^ 2 * (x (i + 3) - t) + 3 * h * (x (i + 3) - t) ^ 2 - 3 * (x (i + 3) - t) ^ 3
      else if t ∈ Ico (x (i + 3)) (x (i + 4)) then (x (i + 4) - t) ^ 3 else 0 :=
  BSpline.bspline_uniform_cubic hh hx i t

/-- **(8.55)–(8.56), the B-spline basis of `𝒮_k`.** With `2k` fictitious nodes
`x_{-k} ≤ ⋯ ≤ x_{-1} ≤ x₀ = a` and `b = x_n ≤ x_{n+1} ≤ ⋯ ≤ x_{n+k}` (8.55) — here strictly
increasing, and in the shifted indexing a sequence `x` with `x k = a < x (k+1) < ⋯ < x (n+k) = b` —
the `n + k` B-splines `B_{i,k+1}`, `i = -k, …, n - 1` (here `BSpline.bspline x k i`, `i < n + k`),
restricted to `[a, b]`, form a basis of `𝒮_k` on the nodes `a = x k < ⋯ < x (n+k) = b`, so that
"any spline `s_k ∈ 𝒮_k` can be uniquely written as `s_k = ∑_{i=-k}^{n-1} c_i B_{i,k+1}`" (8.56),
the `c_i` being its B-spline coefficients (`equation_8_56_repr`). `BSpline.exists_basis_bspline`.
-/
theorem equation_8_56 (hx : StrictMono x) (hn : 1 ≤ n) (hk : 1 ≤ k) (hxa : x k = a)
    (hxb : x (n + k) = b) :
    ∃ B : Module.Basis (Fin (n + k)) ℝ (definition_8_1 a b n (fun j => x (j + k)) k),
      ∀ (i : Fin (n + k)) (t : Icc a b), (B i : C(Icc a b, ℝ)) t = BSpline.bspline x k i t := by
  subst hxa hxb
  exact BSpline.exists_basis_bspline hx hn hk

/-- **(8.56), the B-spline coefficients**: under the hypotheses of `equation_8_56`, every
`s_k ∈ 𝒮_k` is uniquely `∑_{i<n+k} c_i B_{i,k+1}` on `[a, b]`. -/
theorem equation_8_56_repr (hx : StrictMono x) (hn : 1 ≤ n) (hk : 1 ≤ k) (hxa : x k = a)
    (hxb : x (n + k) = b) (v : C(Icc a b, ℝ))
    (hv : v ∈ definition_8_1 a b n (fun j => x (j + k)) k) :
    ∃! c : Fin (n + k) → ℝ, ∀ t : Icc a b, v t = ∑ i, c i * BSpline.bspline x k i t := by
  obtain ⟨B, hB⟩ := equation_8_56 hx hn hk hxa hxb
  have hval : ∀ (c : Fin (n + k) → ℝ) (t : Icc a b),
      ((∑ i, c i • B i : definition_8_1 a b n (fun j => x (j + k)) k) : C(Icc a b, ℝ)) t
        = ∑ i, c i * BSpline.bspline x k i t := by
    intro c t
    simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, hB]
  refine ⟨B.repr ⟨v, hv⟩, fun t => ?_, fun c hc => ?_⟩
  · have := hval (B.repr ⟨v, hv⟩) t
    rwa [B.sum_repr ⟨v, hv⟩] at this
  · have hsum : ∑ i, c i • B i = ⟨v, hv⟩ := by
      ext t
      rw [hval]
      exact (hc t).symm
    rw [← hsum, B.repr_sum_self]

/-- **(8.57), coincident fictitious knots, the left endpoint**: if `x_{-k} = ⋯ = x₀ = a` (in the
shifted indexing `x 0 = ⋯ = x k = a < x (k+1)`), then for `s_k = ∑_{i=-k}^{n-1} c_i B_{i,k+1}`,
`s_k(a) = c_{-k}` (here `c 0`). `BSpline.sum_smul_bspline_left`. -/
theorem equation_8_57 (hx : Monotone x) (hn : 1 ≤ n) (hcoin : ∀ j ≤ k, x j = x k)
    (hlt : x k < x (k + 1)) (c : ℕ → ℝ) :
    ∑ i ∈ Finset.range (n + k), c i * BSpline.bspline x k i (x k) = c 0 :=
  BSpline.sum_smul_bspline_left hx hn hcoin hlt c

/-- **(8.57), coincident fictitious knots, the right endpoint**: if `x_n = ⋯ = x_{n+k} = b` (in the
shifted indexing `x (n+k-1) < x (n+k) = ⋯ = x (n+2k) = b`), then for
`s_k = ∑_{i=-k}^{n-1} c_i B_{i,k+1}`, `s_k(b) = c_{n-1}` (here `c (n+k-1)`) — as the left limit at
`b`, every B-spline vanishing *at* `b` with the half-open convention of (8.54).
`BSpline.sum_smul_bspline_right`. -/
theorem equation_8_57_right (hx : Monotone x) (hn : 1 ≤ n)
    (hcoin : ∀ j, n + k ≤ j → j ≤ n + 2 * k → x j = x (n + k)) (hlt : x (n + k - 1) < x (n + k))
    (c : ℕ → ℝ) :
    Tendsto (fun t => ∑ i ∈ Finset.range (n + k), c i * BSpline.bspline x k i t)
      (𝓝[<] x (n + k)) (𝓝 (c (n + k - 1))) :=
  BSpline.sum_smul_bspline_right hx hn hcoin hlt c

/-- **Remark 8.4, Boehm's knot insertion.** Let `s_k = ∑_{i=-k}^{n-1} c_i B_{i,k+1}` be a spline of
degree `k` on the knots `x` (in the shifted indexing, `∑_{i < n + k} c_i B_{i,k}`) and let `x̃` be a
new knot in the panel `(x_j, x_{j+1})`, `k ≤ j < n + k`. Then `s_k` is also the spline
`∑_{i < n + k + 1} d_i B̃_{i,k}` on the refined knot sequence `BSpline.insertKnot x j x̃`, with

`d_i = ω_i c_i + (1 - ω_i) c_{i-1}`, `ω_i = 1` for `i + k ≤ j`,
`ω_i = (x̃ - x_i)/(x_{i+k} - x_i)` for `j - k < i ≤ j`, `ω_i = 0` for `i > j`

(the book prints `c_i` in both places; the second must be `c_{i-1}` — see the errata).
`BSpline.sum_smul_bspline_insertKnot`.

Two readings. The knots are taken strictly increasing and `x̃` strictly interior to its panel,
where the book writes `x̃ ∈ [x_j, x_{j+1})`: the endpoint case `x̃ = x_j` creates a double knot,
for which the divided-difference proof of `BSpline.bspline_eq_insert_comb` does not apply. And
`k ≤ j < n + k` says that the new knot falls in a panel of the data range, which is what makes the
two end coefficients come out right. -/
theorem remark_8_4 (hx : StrictMono x) (hk : 1 ≤ k) {j : ℕ} (hkj : k ≤ j) (hjn : j < n + k)
    {xt : ℝ} (hxt : xt ∈ Ioo (x j) (x (j + 1))) (c : ℕ → ℝ) (t : ℝ) :
    ∑ i ∈ Finset.range (n + k + 1),
        BSpline.insertKnotCoeff x k j xt c i * BSpline.bspline (BSpline.insertKnot x j xt) k i t
      = ∑ i ∈ Finset.range (n + k), c i * BSpline.bspline x k i t :=
  BSpline.sum_smul_bspline_insertKnot hx hk hxt hkj hjn c t

end QuarteroniSaccoSaleri.Chapter08
